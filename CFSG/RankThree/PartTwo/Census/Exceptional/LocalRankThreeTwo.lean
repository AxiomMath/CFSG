module

public import CFSG.RankThree.PartTwo.Census.Exceptional.E6Two
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open scoped MatrixGroups

section Five

open CFSG.RankThree.CentralCover

theorem four_le_localRank_three_of_five_commuting_SL2 {G : Type} [Group G] [Finite G]
    {K : Type*} [Field K] (h2 : ringChar K = 2) (φ : Fin 5 → SL(2, K) →* G)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 G := by
  have hu : orderOf (φ 4 (sl2Upper 1)) = 2 := by
    rw [orderOf_injective (φ 4) (hφ 4)]
    exact orderOf_sl2Upper_one h2
  have h4 := card_le_localRank_three_of_commuting_SL2 (ι := Fin 4)
    (fun i => φ (Fin.castSucc i)) (fun i => hφ _)
    (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 4 h)) A B) hu
    (fun i A => hcomm _ _ (Fin.castSucc_ne_last i) A _)
  rw [Fintype.card_fin] at h4
  exact h4

end Five

section E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti
open scoped commutatorElement

open CFSG.LieType.Chevalley.RootOps in
theorem four_le_localRank_three_e6Index_two
    (d : TypeE6LieIndex) (hq : d.1.fieldOrder = 2)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (FixedPointCandidate d.steinberg) := by
  obtain ⟨hr1, hr2, hso, hmod, hplus, hminus, h13⟩ := e6Two_check
  have hroot : ∀ {v}, isRootB .E6 v = true → IsRoot .E6 v := fun h => isRootB_iff.1 h
  have hnot : ∀ {v : Fin (Tag.rank .E6) → ℤ}, isRootB .E6 v = false → ¬ IsRoot .E6 v :=
    fun hv hr => by
      rw [← isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  have h2 : ringChar d.1.fixedField = 2 := ringChar_fixedField_eq_two hq
  have : CharP d.1.fixedField 2 := ringChar.of_eq h2
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  set θ := toQuot (e6Embed d) hC with hθ
  choose ρ hinj hmem hcen using fun i =>
    exists_rootSL2' e6Data_valid d.1.fixedField neighbour_cartan_E6 (hroot (hr1 i))
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, d.1.fixedField), ρ i A * ρ j B = ρ j B * ρ i A := by
    intro i j hij A B
    obtain ⟨h1, h2', h3, h4⟩ := hso i j hij
    exact (Subgroup.mem_centralizer_iff.1 (rankOne_le_centralizer e6Data_valid _ (hroot (hr1 i))
      (hroot (hr1 j)) h1 h2' (hnot h3) (hnot h4) (hmem i A)) (ρ j B) (hmem j B)).symm
  have hθρ : ∀ i, Function.Injective (θ.comp (ρ i)) := fun i =>
    toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i)
  set PC : Subgroup ↥(e6Data_valid.minGroup d.1.fixedField) :=
    ⨆ j, e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j) with hPC
  have hP2 : IsPGroup 2 PC := by
    refine isPGroup_iSup_rootGroup e6Data_valid _ e6ModuleRoots fun i j x hx y hy => ?_
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hx
    obtain ⟨e, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hy
    by_cases hij : i = j
    · subst hij
      rw [← e6Data_valid.xm_add, ← e6Data_valid.xm_add, add_comm]
    · exact commute_xm e6Data_valid _ (hroot (hr2 i)) (hroot (hr2 j)) (hmod i j hij).1
        (hnot (hmod i j hij).2) c e
  have hnorm : ∀ i A, ρ i A ∈ Subgroup.normalizer (PC : Set _) := by
    intro i A
    refine (sup_le ?_ ?_ : _ ≤ Subgroup.normalizer (PC : Set _)) (hmem i A)
    · exact rootGroup_le_normalizer_iSup e6Data_valid _ (hroot (hr1 i)) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hplus i j).1, fun h => (hplus i j).2 (isRootB_iff.2 h)⟩
    · exact rootGroup_le_normalizer_iSup e6Data_valid _
        (CFSG.LieType.Chevalley.IsRoot.neg (hroot (hr1 i))) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hminus i j).1, fun h => (hminus i j).2
          (isRootB_iff.2 h)⟩
  have hnc : e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1 ∉ Subgroup.center _ := by
    intro hc
    obtain ⟨σ, hσ, h⟩ := (e6Data_valid.commutator_xm d.1.fixedField (hroot (hr1 0))
      (hroot (hr2 0)) (hplus 0 0).1).1 (hroot h13)
    have h1 := h 1 1
    have h1' : ⁅e6Data_valid.xm d.1.fixedField (e6OrthoRoots 0) 1,
        e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1⁆ = 1 := by
      rw [commutatorElement_def, Subgroup.mem_center_iff.1 hc]
      group
    rw [h1', mul_one, mul_one] at h1
    have h0 := e6Data_valid.xm_injective d.1.fixedField (hroot h13)
      (h1.symm.trans (e6Data_valid.xm_zero _ _).symm)
    rcases hσ with rfl | rfl <;> simp at h0
  have hP : PC.map θ ≠ ⊥ := by
    intro hbot
    apply hnc
    refine mem_center_of_toQuot_eq_one (e6Embed_injective d) hC ?_
    have : θ (e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1) ∈ PC.map θ :=
      ⟨_, le_iSup (fun j => e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j)) 0
        (e6Data_valid.xm_mem_rootGroup _ _ _), rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h4 := card_le_localRank_three_of_commuting_SL2_of_le_normalizer (ι := Fin 4)
    (fun i => θ.comp (ρ i)) hθρ (fun i j hij A B => by
      simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]) hP (hP2.map θ)
    (fun i => Subgroup.le_normalizer_map θ ⟨_, hnorm i _, rfl⟩)
  rw [Fintype.card_fin] at h4
  exact h4

theorem four_le_localRank_three_E6_two
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hq : q.card = 2) [hfin : Finite (CFSGIndex.lie ⟨.E6 q, hv⟩).Group] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (CFSGIndex.lie ⟨.E6 q, hv⟩).Group :=
  @four_le_localRank_three_e6Index_two
    ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩
    (by change (LieTypeIndex.E6 q).fieldOrder = 2; rw [LieTypeIndex.fieldOrder_E6]; exact hq)
    hfin

end E6

section E7

open CFSG.LieType.Steinberg.Minuscule TauCeti

theorem four_le_localRank_three_e7Index_two
    (d : TypeE7LieIndex) (hq : d.1.fieldOrder = 2)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (FixedPointCandidate d.steinberg) := by
  have hC : commutator ↥(e7Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 d.1.fixedField).1.commutator_eq_top
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e7Data_valid d.1.fixedField
    neighbour_cartan_E7 ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1], ![2, 2, 3, 4, 3, 2, 1]]
    (by decide +kernel)
  refine four_le_localRank_three_of_five_commuting_SL2 (K := d.1.fixedField)
    (ringChar_fixedField_eq_two hq)
    (fun i => (toQuot (e7Embed d) hC).comp (ρ i))
    (fun i => toQuot_comp_injective (e7Embed_injective d) hC (ρ i) (hcen i))
    (fun i j hij A B => ?_)
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem four_le_localRank_three_E7_two
    (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    (hq : q.card = 2) [hfin : Finite (CFSGIndex.lie ⟨.E7 q, hv⟩).Group] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
  @four_le_localRank_three_e7Index_two
    ⟨⟨.E7 q, hv⟩, (LieTypeIndex.isTypeE7_iff _).2 trivial⟩
    (by change (LieTypeIndex.E7 q).fieldOrder = 2; rw [LieTypeIndex.fieldOrder_E7]; exact hq)
    hfin

end E7

section E8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

section Embedding

variable (d : ValidLieTypeIndex) {τ : Tag} (M : GeckMatch τ d.dynkinType d.dynkinType_valid)

include M

theorem four_le_localRank_three_geck_five
    [Finite (FixedPointCandidate d.geckFrobenius)]
    (hC : commutator ↥(adjointGroup τ d.fixedField) = ⊤) (h2 : ringChar d.fixedField = 2)
    (ι : Fin 5 → (SL2 d.fixedField →* adjointGroup τ d.fixedField))
    (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 d.fixedField, ι i A * ι j B = ι j B * ι i A) :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (FixedPointCandidate d.geckFrobenius) := by
  have hinj := toQuot_injective (geckEmbed_injective d M) hC center_adjointGroup_eq_bot
  refine four_le_localRank_three_of_five_commuting_SL2 (K := d.fixedField) h2
    (fun i => (toQuot (geckEmbed d M) hC).comp (ι i)) (fun i => hinj.comp (hι i))
    (fun i j hij A B => ?_)
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

end Embedding

theorem four_le_localRank_three_E8_two
    (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (hq : q.card = 2)
    [Finite (CFSGIndex.lie ⟨.E8 q, hv⟩).Group] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.E8 q, hv⟩ with hd
  have : Finite (FixedPointCandidate d.geckFrobenius) := ‹Finite (CFSGIndex.lie d).Group›
  change 4 ≤ CFSG.Open.twoLocalPrimeRank 3 (FixedPointCandidate d.geckFrobenius)
  have hq' : d.fieldOrder = 2 := by
    change (LieTypeIndex.E8 q).fieldOrder = 2
    rw [LieTypeIndex.fieldOrder_E8]
    exact hq
  have hC : commutator ↥(adjointGroup .E8 d.fixedField) = ⊤ :=
    single_edge_perfect .E8 d.fixedField (by simp)
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .E8
    ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0], ![2, 3, 4, 6, 5, 4, 3, 2]] (by decide +kernel)
  exact four_le_localRank_three_geck_five d geckMatchE8 hC (ringChar_fixedField_eq_two hq') ι hι
    hcomm

end E8

end CFSG.RankThree.PartTwo.Census.Exceptional

end
