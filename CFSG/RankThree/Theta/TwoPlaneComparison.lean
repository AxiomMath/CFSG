module

public import CFSG.RankThree.Theta.TwoPlaneSignalizer
public import CFSG.RankThree.GroupTheory.SteinbergBMAlphaHyperplaneIndependence

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThreeEvenClassification.Helpers Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem twoAlpha_le_of_local {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAcard : Nat.card A = 27) (hmix : TwoMixedBalance A) {B D : Subgroup X} (hBA : B ≤ A)
    (hB : Nat.card B = 9) (hDA : D ≤ A) (hD : Nat.card D = 9)
    (hstar : ∀ d ∈ D, d ∉ B → TwoStarConditionAt A d) :
    twoAlpha B ≤ twoAlpha D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hB' : Nat.card B = 3 ^ 2 := by rw [hB]; norm_num
  have hD' : Nat.card D = 3 ^ 2 := by rw [hD]; norm_num
  have hcop : ∀ S : Subgroup X, IsPGroup 2 S → ¬ 3 ∣ Nat.card S :=
    fun S hS => TwoPlane.not_three_dvd_card_of_isPGroup_two hS
  have hsolv : ∀ S : Subgroup X, IsPGroup 2 S → Group.IsSolvable S := fun S hS => by
    have := hS.isNilpotent
    infer_instance
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAR : ∀ a ∈ A, A ≤ normalizer
      (inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set X)) : Set X) := fun a ha x hx =>
    SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
      (mem_centralizer_singleton_iff.mpr (hAcomm x hx a ha))
  have hcentB : ∀ x ∈ A, x ∈ normalizer (B : Set X) := fun x hx =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => hAcomm b (hBA hb) x hx)
  have hDpow : ∀ x ∈ D, x ^ 3 = 1 := fun x hx => hA.2 x (hDA hx)
  have hDp : IsPGroup 3 D := IsPGroup.of_card hD'
  have hBp : IsPGroup 3 B := IsPGroup.of_card hB'
  have hDcomm : ∀ x y : D, x * y = y * x := fun x y =>
    Subtype.ext (hAcomm x (hDA x.2) y (hDA y.2))
  have hDpow' : ∀ x : D, x ^ 3 = 1 := fun x =>
    Subtype.ext ((D.coe_pow x 3).trans (hDpow x x.2))
  have hJD : ∀ d ∈ D, d ≠ 1 → ⁅inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)), D⁆ ≤
      twoCoreAlpha D := fun d hd hd1 =>
    (commutator_le_twoCoreJ hd hd1).trans (twoCoreJ_le_twoCoreAlpha D)
  have hB0 : B ≠ ⊥ := fun h => by
    rw [h, card_bot] at hB
    norm_num at hB
  have hloc : ∀ d ∈ D, d ≠ 1 →
      (twoAlpha (B.subgroupOf (centralizer ({d} : Set X)))).map
          (centralizer ({d} : Set X)).subtype ≤
        inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)) := by
    intro d hd hd1
    by_cases hdB : d ∈ B
    · exact TwoPlane.twoAlpha_local_le_of_mem hA hAcard hd1 hBA hB hdB
    · exact TwoPlane.twoAlpha_local_le_of_not_mem hA hAcard (hDA hd) hd1 (hstar d hd hdB) hBA hB
        hdB
  obtain ⟨hXO, -, -, -, hCX, -, -⟩ := SteinbergBM.alpha_product_structure hB0
  have hX2 : IsPGroup 2 (twoCoreX B) := (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hXO
  have hDX : D ≤ normalizer (twoCoreX B : Set X) := fun x hx =>
    hCX (mem_centralizer_iff.mpr fun b hb => hAcomm b (hBA hb) x (hDA hx))
  have hXd : ∀ d ∈ D, d ≠ 1 → twoCoreX B ⊓ centralizer ({d} : Set X) ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)) := by
    intro d hd hd1 y hy
    refine hloc d hd hd1 (mem_map_of_mem (centralizer ({d} : Set X)).subtype
      (x := ⟨y, hy.2⟩) (twoCoreX_le_twoCoreAlpha _ ?_))
    rw [mem_twoCoreX_iff]
    intro b' hb' hb'1
    have hb'1' : (b' : X) ≠ 1 := fun h => hb'1 (Subtype.ext h)
    rw [← mem_map_iff_mem (centralizer ({d} : Set X)).subtype_injective,
      SteinbergBY.map_subtype_inSubgroup_pCore_centralizer]
    have hyR := mem_twoCoreX_iff.mp hy.1 (b' : X) hb' hb'1'
    exact SteinbergBY.inf_inSubgroup_pCore_le inf_le_right
      ⟨⟨hy.2, SteinbergBY.inSubgroup_pCore_le 2 _ hyR⟩, hyR⟩
  have hX : twoCoreX B ≤ twoCoreAlpha D := by
    rw [coprime_commutator_centralizer_factorization 3 hp D (twoCoreX B) hDp (hcop _ hX2) hDX]
    refine sup_le ?_ ?_
    · rw [repeated_action_commutator_generation 3 hp D (twoCoreX B) hDcomm hDpow' hD'
        (hsolv _ hX2) (hcop _ hX2) hDX]
      refine iSup₂_le fun d hd1 => ?_
      have hd1' : (d : X) ≠ 1 := fun h => hd1 (Subtype.ext h)
      exact (commutator_mono (hXd d d.2 hd1') le_rfl).trans (hJD d d.2 hd1')
    · refine le_trans (fun y hy => mem_twoCoreX_iff.mpr fun d hd hd1 => hXd d hd hd1 ?_)
        (twoCoreX_le_twoCoreAlpha D)
      exact ⟨hy.1, centralizer_le (Set.singleton_subset_iff.mpr hd) hy.2⟩
  have hJ : twoCoreJ B ≤ twoCoreAlpha D := by
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    have hBR : B ≤ normalizer
        (inSubgroup (CFSG.pCore 2) (centralizer ({b} : Set X)) : Set X) :=
      hBA.trans (hAR b (hBA hb))
    have hYR := le_normalizer_iff_commutator_le_left.mp hBR
    refine SteinbergBM.le_twoCoreAlpha_of_commutator_le hp (by norm_num) hBA hDA hAcomm hDpow hD'
      ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hYR)
      (coprime_commutator_idempotent 3 hp B _ hBp
        (hcop _ (SteinbergBY.isPGroup_inSubgroup_pCore 2 _)) hBR)
      (normalizer_commutator_ge_right _ B)
      (fun x hx => SteinbergBY.mem_normalizer_commutator (hAR b (hBA hb) (hDA hx))
        (hcentB x (hDA hx))) fun d hd hd1 => ?_
    exact (commutator_mono (inf_le_inf_right _ hYR) le_rfl).trans
      (hmix d (hDA hd) hd1 b (hBA hb) hb1)
  exact sup_le hJ hX

theorem twoAlpha_hyperplane_independence {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hstar : ∀ a ∈ A, a ≠ 1 → TwoStarConditionAt A a) {B D : Subgroup X} (hBA : B ≤ A)
    (hB : Nat.card B = 9) (hDA : D ≤ A) (hD : Nat.card D = 9) :
    twoAlpha B = twoAlpha D := by
  have hmix := twoMixedBalance_of_twoStar hA hAcard hstar
  refine le_antisymm (twoAlpha_le_of_local hA hAcard hmix hBA hB hDA hD fun d hd hdB => ?_)
    (twoAlpha_le_of_local hA hAcard hmix hDA hD hBA hB fun b hb hbD => ?_)
  · exact hstar d (hDA hd) fun h => hdB (h ▸ one_mem B)
  · exact hstar b (hBA hb) fun h => hbD (h ▸ one_mem D)

end CFSG.RankThree.Theta
