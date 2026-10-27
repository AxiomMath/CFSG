module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots
public import CFSG.Quasithin.Vol2.Ch11SecOE9L
public import CFSG.Quasithin.Vol2.Ch3E213MP6CA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin CFSG.Open
open CFSG.Quasithin.SteinbergBS (minorAut_sq_pow_uElt zero_pow_two_pow upper_of_mem_normalizer
  map_minorAut_pow_antiUnipotent)
open CFSG.Quasithin.Ch3E213M (IsUpper)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] in
theorem rootA_le_antiUnipotent (i : Axis) : rootA K i ≤ antiUnipotent K := by
  cases i
  · exact radA1_le_antiUnipotent
  · exact radA2_le_antiUnipotent

theorem exists_odd_of_swap (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {θ : MulAut (antiSp K)}
    (hU : (antiUnipotent K).map θ.toMonoidHom = antiUnipotent K)
    (hs : (radA1 K).map θ.toMonoidHom = radA2 K) :
    ∃ h : antiSp K, IsUpper h ∧ ∃ r : ℕ, θ = MulAut.conj h * minorAut K ^ (2 * r + 1) := by
  obtain ⟨g, j, -, rfl⟩ := aut_eq_conj_mul_pow hn hK θ
  have hg : g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
    rw [← A1b.conjSub_eq_iff_mem_normalizer, A1b.conjSub]
    have hcomp : (MulAut.conj g * minorAut K ^ j).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (minorAut K ^ j).toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [hcomp, ← Subgroup.map_map, map_minorAut_pow_antiUnipotent] at hU
    exact hU
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · exfalso
    have hle : radA2 K ≤ radA1 K := by
      rw [← hs]
      rintro _ ⟨x, ⟨b, c, d, rfl⟩, rfl⟩
      have h1 : (MulAut.conj g * minorAut K ^ (2 * k)) (uElt 0 b c d) =
          g * uElt 0 (b ^ 2 ^ k) (c ^ 2 ^ k) (d ^ 2 ^ k) * g⁻¹ := by
        rw [MulAut.mul_apply, pow_mul, minorAut_sq_pow_uElt, zero_pow_two_pow, MulAut.conj_apply]
      rw [MulEquiv.coe_toMonoidHom, h1]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.QuasithinUnique.Fin257.Sp4.normalizer_U_le_normalizer_radA1 hg) _).mp
        ⟨_, _, _, rfl⟩
    obtain ⟨b, c, d, h⟩ := hle (⟨1, 0, 0, rfl⟩ : (uElt 1 0 0 0 : antiSp K) ∈ radA2 K)
    exact one_ne_zero (uElt_inj h).1
  · exact ⟨g, upper_of_mem_normalizer hg, k, rfl⟩

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} [L.Normal] (ψ : antiSp K ≃* ↥L)

omit [Finite K] [Finite G] [L.Normal] in
theorem comap_le_antiUnipotent
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {A : Subgroup G}
    (hAT : A ≤ T) : A.comap (emb ψ) ≤ antiUnipotent K := by
  intro x hx
  have h : emb ψ x ∈ T ⊓ L := ⟨hAT hx, emb_mem ψ x⟩
  rw [inf_eq_map_emb ψ hψ] at h
  obtain ⟨y, hy, hyx⟩ := h
  rwa [← emb_injective ψ hyx]

omit [Finite K] [CharP K 2] [Finite G] [L.Normal] in
theorem mul_self_of_mem_comap {A : Subgroup G} (hA : IsElemAbelian 2 A) {x : antiSp K}
    (hx : x ∈ A.comap (emb ψ)) : x * x = 1 :=
  emb_injective ψ (by rw [map_mul, map_one, ← pow_two]; exact hA.2 _ hx)

omit [Finite K] [CharP K 2] in
theorem autHom_eq_of_mem_comap (hAS : AlmostSimple L) {A : Subgroup G} {t : G}
    (ht : t ∈ E1.tauOf ⊤ T A) {x : antiSp K} (hx : x ∈ A.comap (emb ψ)) :
    autHom ψ t x = x := by
  apply emb_injective ψ
  have h := tauOf_le_centralizer hAS hx ht
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  rw [emb_autHom, h, mul_inv_cancel_right]

theorem exists_member_of_not_le_center (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hAS : AlmostSimple L) (hT : IsSylowIn 2 T ⊤)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {A : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {i j : Axis}
    (hij : (i = .one ∧ j = .two) ∨ (i = .two ∧ j = .one)) (hA₀ : A.comap (emb ψ) ≤ rootA K i)
    (hZ : ¬ A.comap (emb ψ) ≤ antiUnipotentCenter K) :
    ∃ X : Subgroup G, E1.IsE n ⊤ T A X ∧ ¬ Group.IsSolvable ↥X := by
  have hinf : rootA K i ⊓ rootA K j = antiUnipotentCenter K := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact radA1_inf_radA2
    · exact (inf_comm _ _).trans radA1_inf_radA2
  have hfs : ∀ θ : MulAut (antiSp K), ((radA1 K).map θ.toMonoidHom = radA1 K ∧
      (radA2 K).map θ.toMonoidHom = radA2 K) ∨ ((radA1 K).map θ.toMonoidHom = radA2 K ∧
        (radA2 K).map θ.toMonoidHom = radA1 K) →
      (rootA K j).map θ.toMonoidHom = rootA K j ∨ (rootA K i).map θ.toMonoidHom = rootA K j := by
    intro θ h
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h2
    · exact Or.inr h1
    · exact Or.inl h1
    · exact Or.inr h2
  obtain ⟨z, hzA, hzZ⟩ := IsConcreteLE.not_le_iff_exists.mp hZ
  have hzi : z ∈ rootA K i := hA₀ hzA
  have hzj : z ∉ rootA K j := fun h => hzZ (by rw [← hinf]; exact ⟨hzi, h⟩)
  refine ⟨_, isE_parC ψ hK hn hψ hT hAT hA j (fun t ht => ?_) ?_,
    fun hs => not_le_of_isSolvable hK hn (emb_injective ψ) j hs le_sup_left⟩
  · have htN := SecE3.le_normalizer_inf (T := T) (L := L) (E1.tauOf_le _ _ _ ht)
    have hfix := autHom_eq_of_mem_comap ψ hAS ht hzA
    rcases hfs _ (fix_or_swap ψ hψ htN) with h | h
    · exact h
    · exfalso
      apply hzj
      rw [← hfix, ← h]
      exact ⟨z, hzi, rfl⟩
  · refine ⟨emb ψ z, hzA, ?_⟩
    obtain ⟨lev, hlev, hker⟩ := exists_leviHom hK hn j
    have hzC : z ∈ parC K j := antiUnipotent_le_parC j (rootA_le_antiUnipotent i hzi)
    set zc : ↥(parC K j) := ⟨z, hzC⟩ with hzc
    have hlz : lev zc ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [KGNat.center_SL2_eq_bot, Subgroup.mem_bot]
      intro h
      apply hzj
      have h1 : zc ∈ lev.ker := h
      rw [hker] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    rw [Subgroup.mem_center_iff] at hlz
    push Not at hlz
    obtain ⟨M, hM⟩ := hlz
    obtain ⟨x, rfl⟩ := hlev M
    refine ⟨x, x.2, fun hmem => hM ?_⟩
    rw [autHom_emb, MulAut.conj_apply] at hmem
    have hk : zc * x * zc⁻¹ * x⁻¹ ∈ lev.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      simpa [hzc] using hmem
    rw [MonoidHom.mem_ker, ← commutatorElement_def, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at hk
    exact hk.symm

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
