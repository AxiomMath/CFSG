module

public import CFSG.Quasithin.MS93.S33SL

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

section Field

variable {F : Type} [Field F]

theorem eq_zero_or_eq_one_of_card_eq_two [Fintype F] (hF : Fintype.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  classical
  by_contra hc
  push Not at hc
  have hle : ({0, 1, c} : Finset F).card ≤ Fintype.card F := Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem, Finset.card_pair hc.2.symm] at hle
  · omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, hc.1.symm⟩

theorem ringHom_eq_of_involutive [Finite F] [CharP F 2] {σ τ : F →+* F}
    (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x) (hσ1 : ∃ x, σ x ≠ x)
    (hτ1 : ∃ x, τ x ≠ x) (x : F) : σ x = τ x := by
  classical
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hbij : ∀ ρ : F →+* F, Function.Bijective ρ := fun ρ =>
    ⟨ρ.injective, Finite.injective_iff_surjective.mp ρ.injective⟩
  have hmap : ∀ (ρ : F →+* F) (x : ZMod 2),
      ρ (algebraMap (ZMod 2) F x) = algebraMap (ZMod 2) F x := fun ρ x =>
    congrArg (fun f : ZMod 2 →+* F => f x)
      (Subsingleton.elim (ρ.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F))
  let σ' : F ≃ₐ[ZMod 2] F :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective σ (hbij σ)) (hmap σ)
  let τ' : F ≃ₐ[ZMod 2] F :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective τ (hbij τ)) (hmap τ)
  have hσ'x : ∀ y, σ' y = σ y := fun _ => rfl
  have hτ'x : ∀ y, τ' y = τ y := fun _ => rfl
  have : Fintype (F ≃ₐ[ZMod 2] F) := Fintype.ofFinite _
  have hsq : ∀ (ρ : F ≃ₐ[ZMod 2] F), (∀ y, ρ (ρ y) = y) → ρ ^ 2 = 1 := fun ρ hρ => by
    ext y
    rw [pow_two, AlgEquiv.mul_apply, hρ]
    rfl
  have hne : ∀ (ρ : F ≃ₐ[ZMod 2] F), (∃ y, ρ y ≠ y) → ρ ≠ 1 := fun ρ ⟨y, hy⟩ h => by
    rw [h] at hy
    exact hy rfl
  have hσ' := hsq σ' fun y => by rw [hσ'x, hσ'x, hσ]
  have hτ' := hsq τ' fun y => by rw [hτ'x, hτ'x, hτ]
  have hσne := hne σ' (by obtain ⟨y, hy⟩ := hσ1; exact ⟨y, by rw [hσ'x]; exact hy⟩)
  have hτne := hne τ' (by obtain ⟨y, hy⟩ := hτ1; exact ⟨y, by rw [hτ'x]; exact hy⟩)
  by_contra hστ
  have hστ' : σ' ≠ τ' := fun h => hστ (by
    rw [← hσ'x, ← hτ'x, h])
  have hle := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[ZMod 2] F) (n := 2) (by norm_num)
  have hsub : ({1, σ', τ'} : Finset (F ≃ₐ[ZMod 2] F)) ⊆
      ({a | a ^ 2 = 1} : Finset (F ≃ₐ[ZMod 2] F)) := by
    intro ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hρ with rfl | rfl | rfl
    · exact one_pow 2
    · exact hσ'
    · exact hτ'
  have hcard : ({1, σ', τ'} : Finset (F ≃ₐ[ZMod 2] F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hστ']
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσne h.symm, fun h => hτne h.symm⟩
  have := (Finset.card_le_card hsub).trans hle
  omega

end Field

section SL3

variable [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSL 3 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)}

omit [Finite G] [Fintype F] in
theorem coordSub_inf_centralizer (hβ : Function.Surjective β)
    (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L)) {m : G}
    (hm : m ∈ Subgroup.normalizer (Uq M T L : Set G)) {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : IsCoordAct β m f) :
    coordSub β (Subgroup.centralizer ({m} : Set G) ⊓ Uq M T L) = KGNat.fixAdd f := by
  ext x
  rw [KGNat.mem_fixAdd]
  constructor
  · rintro ⟨u, ⟨hu, -⟩, rfl⟩
    have hc : (u : G) = m * u * m⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hu m rfl
      rw [this, mul_inv_cancel_right]
    exact (hf u u hc).symm
  · intro hx
    obtain ⟨u, rfl⟩ := exists_coord_eq hβ x
    refine ⟨u, ⟨?_, u.2⟩, rfl⟩
    have hv := conj_mem_of_mem_normalizer hm u
    have he := hf u ⟨_, hv⟩ rfl
    rw [hx] at he
    have := crd_injective hβker (show crd β ⟨_, hv⟩ = crd β u from he)
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    have h2 := congrArg Subtype.val this
    simp only at h2
    calc m * (u : G) = m * u * m⁻¹ * m := by group
      _ = u * m := by rw [h2]

omit [Finite G] [Fintype F] in
theorem isCoordAct_id_of_le_centralizer {m : G} (hm : m ∈ Subgroup.centralizer (Uq M T L : Set G)) :
    IsCoordAct β m id := by
  intro u v huv
  have : v = u := by
    apply Subtype.ext
    rw [huv, ← Subgroup.mem_centralizer_iff.mp hm u u.2, mul_inv_cancel_right]
  rw [this]
  rfl

variable (h : PUHyp M T L) (ha : Function.Surjective a) (hβ : Function.Surjective β)
  (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
  (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
    Multiplicative.toAdd (β v) i =
      (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
include h ha hβ hβker hβα

theorem four_le_relIndex_centralizer (hF : 4 ≤ Fintype.card F) {m : G} (hm : m ∈ M)
    (hnt : ¬ Uq M T L ≤ Subgroup.centralizer ({m} : Set G)) :
    4 ≤ (Subgroup.centralizer ({m} : Set G)).relIndex (Uq M T L) := by
  have hmV := le_normalizer_Uq (T := T) h.le_normalizer hm
  obtain ⟨f, hf⟩ := exists_isCoordAct' hβ hβker hmV
  obtain ⟨σ, hσ⟩ := exists_semilinear_of_mem h ha hβ hβker hβα hm hf
  have hcoord := coordSub_inf_centralizer hβ hβker hmV hf
  have hne : ∃ x, f x ≠ x := by
    by_contra hall
    push Not at hall
    apply hnt
    intro u hu
    have : crd β ⟨u, hu⟩ ∈ KGNat.fixAdd f := hall _
    rw [← hcoord, crd_mem_coordSub_iff hβker] at this
    exact this.1
  have h4 := four_le_index hσ hF hne
  have hcU : Nat.card ↥(Uq M T L) = Fintype.card F ^ 3 := by
    rw [← card_coordSub hβker le_rfl, coordSub_self hβ, AddSubgroup.card_top, card_fin3]
  have hcC : Nat.card ↥(Subgroup.centralizer ({m} : Set G) ⊓ Uq M T L) =
      Nat.card (KGNat.fixAdd f) := by
    rw [← hcoord, card_coordSub hβker inf_le_right]
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({m} : Set G))
    (K := Uq M T L)
  rw [hcC, hcU] at hmul
  have hpos : 0 < Nat.card (KGNat.fixAdd f) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : (Subgroup.centralizer ({m} : Set G)).relIndex (Uq M T L) * Nat.card (KGNat.fixAdd f) <
      4 * Nat.card (KGNat.fixAdd f) := Nat.mul_lt_mul_of_pos_right hlt hpos
  omega

theorem relIndex_eq_two_of_nonlinear {n : ℕ} (hcard : Fintype.card F = 2 ^ n) {E : Subgroup G}
    (hE : E ≤ T) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hUE : ⁅Uq M T L, E⁆ ≤ E)
    (hnl : ∃ e ∈ E, ∃ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β e f ∧
      ¬ ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x) :
    (pCoreOf 2 M).relIndex E = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨e₀, he₀, f₀', hf₀', hnl₀⟩ := hnl
  obtain ⟨f₀, hf₀⟩ := exists_isCoordAct' hβ hβker (hTV (hE he₀))
  have hff₀ : f₀' = f₀ := IsCoordAct.unique hβ (hTV (hE he₀)) hf₀' hf₀
  obtain ⟨σ₀, hσ₀⟩ := exists_semilinear_of_mem h ha hβ hβker hβα (h.le (hE he₀)) hf₀
  have hne₀ : ∃ c, σ₀ c ≠ c := by
    by_contra hall
    push Not at hall
    apply hnl₀
    intro c x
    rw [hff₀, hσ₀, hall]
  have hA : ∀ e ∈ E, (∀ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β e f →
      ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x) → e ∈ pCoreOf 2 M := by
    intro e he hlin
    obtain ⟨g, hg⟩ := exists_isCoordAct' hβ hβker (hTV (hE he))
    have hfg : ∀ x, f₀ (g x - x) = g x - x := by
      intro x
      obtain ⟨u, rfl⟩ := exists_coord_eq hβ x
      have hc : ⁅e, (u : G)⁆ ∈ Uq M T L := by
        rw [commutatorElement_def]
        exact mul_mem (conj_mem_of_mem_normalizer (hTV (hE he)) u) (inv_mem u.2)
      have hcE : ⁅e, (u : G)⁆ ∈ E := hUE (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator he u.2)
      have hcrd := crd_commutator' (hTV (hE he)) hg u hc
      have he₀c : e₀ ∈ Subgroup.centralizer (E : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => hEab y hy e₀ he₀
      have hfix := fix_of_mem_centralizer he₀c hf₀
        (show crd β ⟨_, hc⟩ ∈ coordSub β E from ⟨⟨_, hc⟩, hcE, rfl⟩)
      rw [hcrd] at hfix
      exact hfix
    have hid := eq_id_of_quadratic hσ₀ hne₀ (hlin g hg) hfg
    have hcU : e ∈ Subgroup.centralizer (Uq M T L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have hv := conj_mem_of_mem_normalizer (hTV (hE he)) ⟨u, hu⟩
      have h1 := hg ⟨u, hu⟩ ⟨_, hv⟩ rfl
      rw [hid] at h1
      have h2 := crd_injective hβker (show crd β ⟨_, hv⟩ = crd β ⟨u, hu⟩ from h1)
      have h3 := congrArg Subtype.val h2
      simp only at h3
      calc u * e = e * u * e⁻¹ * e := by rw [h3]
        _ = e * u := by group
    rw [← inf_centralizer_Uq h]
    exact ⟨hE he, hcU⟩
  have hσinv : ∀ e ∈ E, ∀ g : (Fin 3 → F) →+ (Fin 3 → F), IsCoordAct β e g →
      ∀ σ : F →+* F, (∀ (c : F) (x : Fin 3 → F), g (c • x) = σ c • g x) → ∀ c, σ (σ c) = c := by
    intro e he g hg σ hσ c
    have hpow := iterate_eq_of_pow_eq_one hβ (hTV (hE he)) hg (hE2 e he)
    have hgg : ∀ x, g (g x) = x := fun x => by simpa using hpow x
    have hx₀ : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := fun h0 => by
      simpa using congrFun h0 0
    have h1 := hgg (c • Pi.single 0 1)
    rw [hσ, hσ, hgg] at h1
    exact smul_left_injective F hx₀ h1
  have hnt : ∀ e ∈ E, e ∉ pCoreOf 2 M → ∀ g : (Fin 3 → F) →+ (Fin 3 → F), IsCoordAct β e g →
      ∀ σ : F →+* F, (∀ (c : F) (x : Fin 3 → F), g (c • x) = σ c • g x) → ∃ c, σ c ≠ c := by
    intro e he hn g hg σ hσ
    by_contra hall
    push Not at hall
    exact hn (hA e he fun f hf c x => by
      rw [IsCoordAct.unique hβ (hTV (hE he)) hf hg, hσ, hall])
  have hC : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ∉ pCoreOf 2 M → e₂ ∉ pCoreOf 2 M →
      e₁ * e₂ ∈ pCoreOf 2 M := by
    intro e₁ he₁ e₂ he₂ hn₁ hn₂
    obtain ⟨g₁, hg₁⟩ := exists_isCoordAct' hβ hβker (hTV (hE he₁))
    obtain ⟨g₂, hg₂⟩ := exists_isCoordAct' hβ hβker (hTV (hE he₂))
    obtain ⟨σ₁, hσ₁⟩ := exists_semilinear_of_mem h ha hβ hβker hβα (h.le (hE he₁)) hg₁
    obtain ⟨σ₂, hσ₂⟩ := exists_semilinear_of_mem h ha hβ hβker hβα (h.le (hE he₂)) hg₂
    have heq := ringHom_eq_of_involutive (hσinv e₁ he₁ g₁ hg₁ σ₁ hσ₁)
      (hσinv e₂ he₂ g₂ hg₂ σ₂ hσ₂) (hnt e₁ he₁ hn₁ g₁ hg₁ σ₁ hσ₁) (hnt e₂ he₂ hn₂ g₂ hg₂ σ₂ hσ₂)
    apply hA _ (mul_mem he₁ he₂)
    intro f hf c x
    have hf12 := hg₁.mul (hTV (hE he₂)) hg₂
    rw [IsCoordAct.unique hβ (hTV (hE (mul_mem he₁ he₂))) hf hf12]
    simp only [Function.comp_apply]
    rw [hσ₂, hσ₁, heq, hσinv e₂ he₂ g₂ hg₂ σ₂ hσ₂]
  have he₀Q : e₀ ∉ pCoreOf 2 M := by
    intro hQ
    apply hnl₀
    have hcU : e₀ ∈ Subgroup.centralizer (Uq M T L : Set G) :=
      ((inf_centralizer_Uq h).ge hQ).2
    rw [IsCoordAct.unique hβ (hTV (hE he₀)) hf₀' (isCoordAct_id_of_le_centralizer hcU)]
    intro c x
    rfl
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨e₀, he₀⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ pCoreOf 2 M
  · refine Or.inr ⟨hb, fun h' => he₀Q ?_⟩
    have := mul_mem (inv_mem hb) h'
    simpa using this
  · exact Or.inl ⟨hC b b.2 e₀ he₀ hb he₀Q, hb⟩

end SL3

end CFSG.Quasithin.MS93.S33
