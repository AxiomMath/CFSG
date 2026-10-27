module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag

theorem exists_corank_two_block_of_large_unitary_K_of_cfg_of_rank
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hnb : GGNbr p B x D J y K)
    {r f : ℕ} (hr : 4 ≤ r)
    (hr5 : r ≠ 5 ∨ f ≠ 1 ∧
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), p ^ 4 ≤ Nat.card (ggGamma K hN).range)
    (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* K) (S : Finset (Fin (r + 1))),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (K.subtype.comp φ) ∧
        S.card = r - 1 ∧
        (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t) := by
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hp : p.Prime := Fact.out
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side_of_cfg_of_rank hRig hcfg hIDA (Or.inr ⟨y, hnb⟩)
      hr hr5 hpq hpd hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hpJ : p ∣ Nat.card J :=
    (prime_dvd_card_of_hasLabel_unitary hp hp2 (by omega : 2 ≤ r - 2) hpq hJLab).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 hpJ hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hcfg.2.1.1 (hcfg.2.2.1.1 hxD)
  obtain ⟨S, hJblock, hS⟩ := exists_block_of_diagonal_unitary_component
    (by omega : 2 ≤ r) hΛ.1 hpq hcfg.tableB_facts.2.1 hN hF hM hdiag
      (Set.singleton_subset_iff.mpr hx) hcomp
  have hk : (K.subtype.comp φ).ker ≤ Subgroup.center ↥(unitarySU 2 f F (r + 1)) :=
    UnitTB.ker_comp_subtype_le_center hM
  have hΛJ : LargeEvenInLambda2 ⟨.twA, r - 2, f⟩ := by
    change 1 ≤ f ∧ 2 ≤ r - 2 ∧ (r - 2 = 2 → 2 ≤ f)
    refine ⟨hΛ.1, by omega, ?_⟩
    intro ha
    have hr4 : r = 4 := by omega
    have hp5 : p = 5 := by
      have hdvd : p ∣ 5 := by simpa only [hr4] using hpd
      exact ((Nat.dvd_prime Nat.prime_five).mp hdvd).resolve_left hp.ne_one
    by_contra hf2
    have hf1 : 1 ≤ f := hΛ.1
    have hlt : f < 2 := Nat.lt_of_not_ge hf2
    have hf : f = 1 := by omega
    have : 5 ∣ 3 := by simpa only [hp5, hf, pow_one] using hpq
    norm_num at this
  have hJq : Assembly.IsQuasisimple
      ((TableBUE.blockSU (K := F) (n := f) S).map (K.subtype.comp φ)) := by
    rw [← hJblock]
    exact hcomp.2.2
  have hc := card_eq_of_blockSU_label hRig hF hΛ.1 hk hS hJq hΛJ (hJblock ▸ hJLab)
  exact ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hJblock, hc, hdiag⟩

theorem exists_corank_two_block_of_large_unitary_K_of_cfg
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hnb : GGNbr p B x D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* K) (S : Finset (Fin (r + 1))),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (K.subtype.comp φ) ∧
        S.card = r - 1 ∧
        (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t) :=
  exists_corank_two_block_of_large_unitary_K_of_cfg_of_rank hRig hLB hcfg hIDA hnb hr (Or.inl hr5)
    hpq hpd hLab hΛ hJLab

theorem exists_corank_two_block_of_large_unitary_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : ↥(unitarySU 2 f F (r + 1)) →* K) (S : Finset (Fin (r + 1))),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (K.subtype.comp φ) ∧
        S.card = r - 1 ∧
        (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F,
          LineU.ActsDiagU φ a t) :=
  exists_corank_two_block_of_large_unitary_K_of_cfg hRig hLB hH.1 hH.2.2.1 hH.2.2.2.2.1 hr hr5 hpq
    hpd hLab hΛ hJLab

theorem ggResTwoNodeSideDatum_large_unitary_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    GGResTwoNodeSideDatum p Bs L J := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hJ, hS, hdiag⟩ :=
    exists_corank_two_block_of_large_unitary_L hRig hH hr hr5 hpq hpd hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggResTwoNodeSideDatum_of_diagonal_unitary_block hF hΛ.1
    hH.1.1.2.2.2.2.2.1.2.1 hpq (by omega : 4 ≤ r) hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2
    hN hM hdiag S hS hJ

theorem ggResTwoNodeSideDatum_large_unitary_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    GGResTwoNodeSideDatum p Bs K J := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hJ, hS, hdiag⟩ :=
    exists_corank_two_block_of_large_unitary_K hRig hLB hH hr hr5 hpq hpd hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggResTwoNodeSideDatum_of_diagonal_unitary_block hF hΛ.1
    hH.1.1.2.2.2.2.2.1.2.1 hpq (by omega : 4 ≤ r) hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2
    hN hM hdiag S hS hJ

end CFSG.StandardType

end
