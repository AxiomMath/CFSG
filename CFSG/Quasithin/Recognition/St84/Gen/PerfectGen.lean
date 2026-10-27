module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RPerfect

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.H13.Ch9.F112Pf

theorem isPerfect_of_isL2Quot {X : Type*} [Group X] {f : ℕ} (hf : 2 ≤ f) (h : IsL2Quot f X) :
    Group.IsPerfect X := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    have := Fintype.ofFinite (GaloisField 2 f)
    have hc : 4 ≤ (Finset.univ : Finset (GaloisField 2 f)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) := e.trans (pslTwoGf2EquivSl f)
  exact Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective

variable {G : Type} [Group G]

theorem not_isSolvable_of_isL2Quot {L : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (h : IsL2Quot f (oTwoQuot ↥L)) : ¬ Group.IsSolvable ↥L := by
  intro hs
  have hX := isPerfect_of_isL2Quot hf h
  have hc : Nat.card (oTwoQuot ↥L) = 2 ^ f * (4 ^ f - 1) := IsL2Quot.card (by omega) h
  have h60 := two_pow_mul_four_pow_sub_one_ge f hf
  have : Finite (oTwoQuot ↥L) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (oTwoQuot ↥L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have : Group.IsSolvable (oTwoQuot ↥L) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥L))
  exact Group.IsPerfect.not_isSolvable (oTwoQuot ↥L) this

theorem le_commutator_sup_pCoreOf_of_isL2Quot {L : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (h : IsL2Quot f (oTwoQuot ↥L)) : L ≤ ⁅L, L⁆ ⊔ pCoreOf 2 L := by
  haveI := isPerfect_of_isL2Quot hf h
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hmap : (commutator ↥L).map π = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have hsup : commutator ↥L ⊔ pCore 2 ↥L = ⊤ := by
    have := Subgroup.comap_map_eq π (commutator ↥L)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm
  have := congrArg (Subgroup.map L.subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at this
  exact this.ge

theorem perfect_of_isL2Quot {L : Subgroup G} {f : ℕ} (hf : 2 ≤ f) (h : IsL2Quot f (oTwoQuot ↥L))
    (hO : pCoreOf 2 L ≤ ⁅L, L⁆) : ⁅L, L⁆ = L :=
  le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
      L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb))
    ((le_commutator_sup_pCoreOf_of_isL2Quot hf h).trans (sup_le le_rfl hO))

variable [Finite G]

theorem le_and_perfect_of_vFact_of_isL2Quot {L B S : Subgroup G} (hSB : S ≤ B)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hB : Group.IsSolvable ↥B) (hV : VFact (L ⊔ B))
    (hS : IsPGroup 2 S) {f : ℕ} (hf : 2 ≤ f) (h : IsL2Quot f (oTwoQuot ↥L)) :
    S ≤ L ∧ ⁅L, L⁆ = L := by
  have hLP : L ≤ L ⊔ B := le_sup_left
  have hn : (L.subgroupOf (L ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLP).2 (sup_le Subgroup.le_normalizer hBL)
  have hDL : perfectCore (L ⊔ B) ≤ L := perfectCore_le_of_sup_solvable hLP hn rfl hB
  have hSL : S ≤ L := (le_of_isPGroup_of_odd (perfectCore_normal (L ⊔ B)) hV.1
    (hSB.trans le_sup_right) hS).trans hDL
  refine ⟨hSL, perfect_of_isL2Quot hf h ?_⟩
  have hc := pCoreOf_sup_eq_commutator hSB hBL hB hV
  rw [sup_eq_left.mpr hSL] at hc
  rw [hc]
  exact Subgroup.commutator_mono (pCoreOf_le 2 L) le_rfl

theorem vFact_of_hasModelFacts_of_isL2Quot {L1 L2 S : Subgroup G} {f1 f2 : ℕ} (hf1 : 2 ≤ f1)
    (h1 : IsL2Quot f1 (oTwoQuot ↥L1)) (hf2 : 2 ≤ f2) (h2 : IsL2Quot f2 (oTwoQuot ↥L2))
    {Pr : ∀ (Y : Type) [Group Y], Prop} (hPr : HasModelFacts Pr)
    (hα : IsAmalgamOfGroup (f112Amalgam L1 L2 S) Pr) :
    Group.IsSolvable ↥(bigB L1 L2 S) ∧ VFact (L1 ⊔ bigB L1 L2 S) ∧ VFact (L2 ⊔ bigB L1 L2 S) := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hα
  obtain ⟨hfin, hmod⟩ := hPr Y hY
  obtain ⟨P, hR, hP⟩ := hmod T hpair.1
  have hns : ∀ (L : Subgroup G) (M : Subgroup Y) (f : ℕ), 2 ≤ f →
      (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) → IsL2Quot f (oTwoQuot ↥L) → ¬ Group.IsSolvable ↥M := by
    intro L M f hf e hq hs
    apply not_isSolvable_of_isL2Quot hf hq
    have : Group.IsSolvable ↥(L ⊔ bigB L1 L2 S) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_left : L ≤ L ⊔ bigB L1 L2 S))
  obtain ⟨hsolv, hV₁, hV₂⟩ := vFact_of_residual hR (fun j => (hP j).1) (fun j => (hP j).2) hpair
    (hns L1 M₁ f1 hf1 iso.φ1 h1) (hns L2 M₂ f2 hf2 iso.φ2 h2)
  refine ⟨?_, vFact_of_mulEquiv iso.φ1 hV₁, vFact_of_mulEquiv iso.φ2 hV₂⟩
  have : Group.IsSolvable (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 := hsolv
  have : Group.IsSolvable ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)) :=
    Group.isSolvable_of_isSolvable_injective (f := iso.φ12.toMonoidHom) iso.φ12.injective
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
    (le_inf le_sup_right le_sup_right :
      bigB L1 L2 S ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)))

theorem perfectOver_of_hasModelFacts_of_isL2Quot {L1 L2 S : Subgroup G} (hH : Hyp111 L1 L2 S)
    {f1 f2 : ℕ} (hf1 : 2 ≤ f1) (h1 : IsL2Quot f1 (oTwoQuot ↥L1)) (hf2 : 2 ≤ f2)
    (h2 : IsL2Quot f2 (oTwoQuot ↥L2)) {Pr : ∀ (Y : Type) [Group Y], Prop} (hPr : HasModelFacts Pr)
    (hα : IsAmalgamOfGroup (f112Amalgam L1 L2 S) Pr) : PerfectOver L1 L2 S := by
  obtain ⟨hB, hV₁, hV₂⟩ := vFact_of_hasModelFacts_of_isL2Quot hf1 h1 hf2 h2 hPr hα
  have hSB : S ≤ bigB L1 L2 S := (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S)
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hH
  obtain ⟨hS1, hp1⟩ := le_and_perfect_of_vFact_of_isL2Quot hSB hB1 hB hV₁ hH.h1.pgroup hf1 h1
  obtain ⟨hS2, hp2⟩ := le_and_perfect_of_vFact_of_isL2Quot hSB hB2 hB hV₂ hH.h1.pgroup hf2 h2
  exact ⟨perfectCore_eq_self_of_perfect hp1, perfectCore_eq_self_of_perfect hp2, hS1, hS2⟩

end CFSG.Quasithin.F112R
