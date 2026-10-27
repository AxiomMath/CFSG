module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddShared
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddJ1Sylow
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddJ1Four
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Walter.J1Props CFSG.QuasithinUnique Subgroup

theorem normalizes_of_odd_prime_local {G : Type} [Group G] [Finite G] (h : JankoHyp₀ G)
    (hG : Nat.card G = 175560) {U B : Subgroup G} {y : G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hUB : U ≤ B)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) (hyB : y ∈ B)
    (hy : orderOf y = p) : y ∈ normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUc : Nat.card U = 8 := h.card_sylow (hU.toSylow hUi)
  have hBc := card_eq_eight_mul_of_card_eq hG hp hp5 hUc hUB hB hyB hy
  have hy' : orderOf (⟨y, hyB⟩ : B) = p := by rw [Subgroup.orderOf_mk, hy]
  have hU' : Nat.card (U.subgroupOf B) = 8 := by
    rw [← hUc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  rcases zpowers_normal_or_normal_of_card_eq_eight_mul hp hp5 hBc hy' hU' with hQ | hUn
  · exfalso
    refine not_normalizes_zpowers_of_sylow h hp hp5 hy hU hUi fun u hu => ?_
    have h1 := hQ.conj_mem ⟨y, hyB⟩ (mem_zpowers _) ⟨u, hUB hu⟩
    have h2 := Subgroup.mem_map_of_mem B.subtype h1
    rwa [MonoidHom.map_zpowers] at h2
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hUn hyB

theorem center_eq_bot_of_simple_of_not_prime {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    (hc : ¬ (Nat.card L).Prime) : Subgroup.center L = ⊥ := by
  open scoped IsMulCommutative in
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h0 | h0
  · exact h0
  · exfalso
    have : IsMulCommutative L := Subgroup.center_eq_top_iff.mp h0
    exact hc (IsSimpleGroup.prime_card (α := L))

theorem mem_map_subgroupOf_iff_of_equiv {A G : Type*} [Group A] [Group G] {L K : Subgroup A}
    (ψ : ↥L ≃* G) (m : ↥L) : ψ m ∈ (K.subgroupOf L).map ψ.toMonoidHom ↔ (m : A) ∈ K := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]

theorem j1_local_of_odd_prime
    (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (p : ℕ) (y g : A)
    (e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hUB : U ≤ B) (hBL : B ≤ L) (hU : IsSylowTwoOf U L)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) (hyB : y ∈ B)
    (hy : orderOf y = p) (hgL : g ∈ normalizer (L : Set A)) (hgU : g ∈ normalizer (U : Set A))
    (hgy : g ∈ normalizer ((zpowers y : Subgroup A) : Set A)) (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1) :
    g * y * g⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ε : ↥L ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hyL : y ∈ L := hBL hyB
  have hSimple : IsSimpleGroup CFSG.Open.walterJ1 := isSimpleGroup_walterJ1
  have hZ : Subgroup.center ↥L = ⊥ := by
    have : IsSimpleGroup ↥L := ε.isSimpleGroup
    refine center_eq_bot_of_simple_of_not_prime ?_
    rw [Nat.card_congr ε.toEquiv, card_walterJ1]
    norm_num
  have hyU : y ∈ normalizer (U : Set A) := by
    have hUw : IsPGroup 2 ((U.subgroupOf L).map ε.toMonoidHom) :=
      (hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm).map _
    have hUwi : ¬ 2 ∣ ((U.subgroupOf L).map ε.toMonoidHom).index := by
      have := Subgroup.index_map_equiv (U.subgroupOf L) ε
      erw [this]
      exact hU.2.2
    have hBw : ∀ q : ℕ, q.Prime → q ∣ Nat.card ((B.subgroupOf L).map ε.toMonoidHom) →
        q = 2 ∨ q = p := by
      intro q hq hqB
      refine hB q hq ?_
      rwa [← Nat.card_congr ((B.subgroupOf L).equivMapOfInjective _ ε.injective).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv] at hqB
    have hyw : orderOf (ε ⟨y, hyL⟩) = p := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
    have hN := normalizes_of_odd_prime_local jankoHyp₀ card_walterJ1 hp hp5 hUw hUwi
      (Subgroup.map_mono (Subgroup.subgroupOf_mono L hUB)) hBw
      ((mem_map_subgroupOf_iff_of_equiv ε ⟨y, hyL⟩).2 hyB) hyw
    have hsub : ∀ z : ↥L, ε z ∈ normalizer (((U.subgroupOf L).map ε.toMonoidHom : Subgroup _) :
        Set _) → ∀ u ∈ U, (z : A) * u * (z : A)⁻¹ ∈ U := by
      intro z hz u hu
      have huw : ε ⟨u, hU.1 hu⟩ ∈ (U.subgroupOf L).map ε.toMonoidHom :=
        (mem_map_subgroupOf_iff_of_equiv ε _).2 hu
      have h1 := (Subgroup.mem_normalizer_iff.mp hz _).1 huw
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      exact (mem_map_subgroupOf_iff_of_equiv ε _).1 h1
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hsub ⟨y, hyL⟩ hN u, fun hu => ?_⟩
    have := hsub ⟨y, hyL⟩⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hN) _ hu
    simpa [mul_assoc] using this
  let φ : MulAut ↥L := L.normalizerMonoidHom ⟨g, hgL⟩
  obtain ⟨s, hs⟩ := CFSG.Walter.J1Props.J3_aut (MulAut.congr ε φ)
  have hx : ∀ l : ↥L, g * (l : A) * g⁻¹ =
      ((ε.symm s : ↥L) : A) * l * ((ε.symm s : ↥L) : A)⁻¹ := by
    intro l
    have h1 := congrArg (fun ψ : MulAut CFSG.Open.walterJ1 => ψ (ε l)) hs
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply] at h1
    have h2 : φ l = ε.symm s * l * (ε.symm s)⁻¹ := by
      rw [← ε.symm_apply_apply (φ l), h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact congrArg (fun m : ↥L => (m : A)) h2
  exact fix_of_inner hZ hU hp (by omega) hyL hy hyU hgU hgy hg2 hx

end CFSG.Quasithin.H13.NQCore
