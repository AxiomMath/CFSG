module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresTransport
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType

namespace LayerPDiv

open Matrix LayerCores

theorem eq_of_conj_mem_of_isQuasisimple {G : Type*} [Group G] {Q M : Subgroup G}
    (hQ : CFSG.IsQuasisimple Q) (hMQ : M ≤ Q) (hMn : ∀ q ∈ Q, ∀ m ∈ M, q * m * q⁻¹ ∈ M)
    (hM : ⁅M, M⁆ = M) (hM1 : M ≠ ⊥) : M = Q := by
  have hN : (M.subgroupOf Q).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hMn g g.2 n hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hN with h | h
  · refine le_antisymm hMQ fun q hq => ?_
    have : (⟨q, hq⟩ : Q) ∈ M.subgroupOf Q := h ▸ Subgroup.mem_top _
    exact this
  · refine absurd ?_ hM1
    have hab : ⁅M, M⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.mp
        (h (show (⟨x, hMQ hx⟩ : Q) ∈ M.subgroupOf Q from hx)) ⟨y, hMQ hy⟩
      exact congrArg Subtype.val this
    rw [← hM, hab]

theorem le_of_perfect_of_ggDer_le {G : Type*} [Group G] {H X S : Subgroup G} (hXH : X ≤ H)
    (hX : ⁅X, X⁆ = X) {k : ℕ} (hk : LayerFacts.ggDer H k ≤ S) : X ≤ S :=
  (LayerFacts.ggDer_of_perfect hX k).symm.le.trans ((LayerFacts.ggDer_mono hXH k).trans hk)

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
  {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}

theorem dvd_card_of_conj_mem_unitaryOf [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) (hcore : ∀ b, HasCore (factorGroup π hτ hπ b))
    {p : ℕ} (hX : ∀ b, b ≤ π b → Group.IsSolvable (factorGroup π hτ hπ b) ∨
      ∃ X : Subgroup (GL (Fin (d b)) (D b)), X ≤ factorGroup π hτ hπ b ∧ ⁅X, X⁆ = X ∧
        p ∣ Nat.card X)
    {S : Subgroup (PiMat D d)ˣ} (hSU : S ≤ unitaryOf hτ)
    (hSn : ∀ u ∈ unitaryOf hτ, ∀ s ∈ S, u * s * u⁻¹ ∈ S) (hSq : CFSG.IsQuasisimple S) :
    p ∣ Nat.card S := by
  classical
  obtain ⟨b, hb, hSb⟩ : ∃ b, b ≤ π b ∧ S.map (coordHom D d b) ≠ ⊥ := by
    by_contra hcon
    have hcon' : ∀ b, b ≤ π b → S.map (coordHom D d b) = ⊥ := fun b hb => by
      by_contra hne
      exact hcon ⟨b, hb, hne⟩
    have h1 : ∀ s ∈ S, s = 1 := fun s hs => eq_one_of_forall_le hτ hπ (hSU hs) fun b hb => by
      have hm : coordHom D d b s ∈ S.map (coordHom D d b) := Subgroup.mem_map_of_mem _ hs
      rw [hcon' b hb, Subgroup.mem_bot] at hm
      have h2 := congrArg (fun g : GL (Fin (d b)) (D b) =>
        (g : Matrix (Fin (d b)) (Fin (d b)) (D b))) hm
      simpa [coe_coordHom] using h2
    obtain ⟨a, a', haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hSq
    exact haa (Subtype.ext (by rw [h1 _ (a * a').2, h1 _ (a' * a).2]))
  set M := S.map (coordHom D d b) with hM
  have hMfg : M ≤ factorGroup π hτ hπ b := by
    rintro _ ⟨s, hs, rfl⟩
    exact coordHom_mem_factorGroup hτ hπ b (hSU hs)
  have hMn : ∀ g ∈ factorGroup π hτ hπ b, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    rintro g hg _ ⟨s, hs, rfl⟩
    obtain ⟨t, ht, rfl⟩ := exists_mem_orbitGroup hτ hπ b hg
    exact ⟨t * s * t⁻¹, hSn t (orbitGroup_le hτ b ht) s hs, by
      rw [map_mul, map_mul, map_inv]⟩
  have hMperf : ⁅M, M⁆ = M := by
    rw [hM, ← Subgroup.map_commutator, LayerFacts.ggCommutator_eq_of_isQuasisimple hSq]
  obtain ⟨S', hS'le, -, ⟨k, hk⟩, hS'⟩ := hcore b
  have hMS' : M ≤ S' := le_of_perfect_of_ggDer_le hMfg hMperf hk
  have hS'q : CFSG.IsQuasisimple S' := by
    rcases hS' with h | h
    · exact absurd (eq_bot_iff.mpr (h ▸ hMS')) hSb
    · exact h.1
  have hMeq : M = S' := eq_of_conj_mem_of_isQuasisimple hS'q hMS'
    (fun q hq m hm => hMn q (hS'le hq) m hm) hMperf hSb
  have hdvd : p ∣ Nat.card M := by
    rcases hX b hb with hsol | ⟨X, hXle, hXperf, hpX⟩
    · exfalso
      obtain ⟨j, hj⟩ := exists_ggDer_eq_bot hsol
      have hS'bot : S' = ⊥ := by
        rw [eq_bot_iff, ← hj]
        exact (LayerFacts.ggDer_of_perfect (LayerFacts.ggCommutator_eq_of_isQuasisimple hS'q)
          j).symm.le.trans (LayerFacts.ggDer_mono hS'le j)
      exact hSb (hMeq.trans hS'bot)
    · rw [hMeq]
      exact hpX.trans (Subgroup.card_dvd_of_le (le_of_perfect_of_ggDer_le hXle hXperf hk))
  exact hdvd.trans (Subgroup.card_map_dvd _ _)

theorem glFactor_pDiv {E : Type} [Field E] [Finite E] [CharP E 2] (m : ℕ) :
    Group.IsSolvable (⊤ : Subgroup (GL (Fin m) E)) ∨
      ∃ X : Subgroup (GL (Fin m) E), X ≤ ⊤ ∧ ⁅X, X⁆ = X ∧ Nat.card E ^ 2 - 1 ∣ Nat.card X := by
  by_cases hg : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset E, s.card = 4)
  · right
    refine ⟨(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* GL (Fin m) E).range,
      le_top, LayerFacts.ggCommutator_eq_of_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective)
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hg.1 hg.2)), ?_⟩
    rw [← Nat.card_congr (MonoidHom.ofInjective (SpecialLinearGroup.toGL_injective (n := Fin m)
      (R := E))).toEquiv]
    exact sq_sub_one_dvd_card_SL hg.1
  · left
    have : Group.IsSolvable (GL (Fin m) E) :=
      LayerFacts.isSolvable_of_not_goodBlock (E := fun _ : Unit => E) (m := fun _ => m)
        (b := ()) hg
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)

theorem sq_sub_one_dvd_card_sub_one_of_invol {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Finite E] (ρ : E →+* E) (hρ2 : ∀ c, ρ (ρ c) = c) (hρ1 : ∃ c, ρ c ≠ c)
    (hρF : ∀ a : F, ρ (algebraMap F E a) = algebraMap F E a) :
    Nat.card F ^ 2 - 1 ∣ Nat.card E - 1 := by
  have : Finite F := Finite.of_injective _ (algebraMap F E).injective
  have : FiniteDimensional F E := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hid : ρ.comp ρ = RingHom.id E := RingHom.ext hρ2
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom ρ ρ hid hid) hρF
  have hσ : ∀ c, σ c = ρ c := fun _ => rfl
  have hσ2 : σ ^ 2 = 1 := AlgEquiv.ext fun c => by
    rw [pow_two, AlgEquiv.mul_apply, hσ, hσ, hρ2, AlgEquiv.one_apply]
  have hσ1 : σ ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := hρ1
    exact hc (by rw [← hσ, h, AlgEquiv.one_apply])
  have h2 : 2 ∣ Module.finrank F E := by
    rw [← IsGalois.card_aut_eq_finrank F E, ← orderOf_eq_prime hσ2 hσ1]
    exact orderOf_dvd_natCard σ
  obtain ⟨j, hj⟩ := h2
  rw [Module.natCard_eq_pow_finrank (K := F) (V := E), hj, pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F ^ 2) 1 j

end LayerPDiv

end CFSG.StandardType
