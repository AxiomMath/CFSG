module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapGen
public import CFSG.RankThree.GF2n.Stroth80.Satz5Alg

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.AGLEmbeddingD2.SquareSpinMinus CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.CurtisTits CFSG.SeitzReduction.OmegaPilot

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

@[expose] def activeCoords (n : ℕ) (S : Finset (Fin (n - 1))) : Finset (Idx n) :=
  eCoords n S ∪ fCoords n S ∪ planeCoords n

abbrev anchoredSupport (F : Type) [Field F] (n : ℕ) (S : Finset (Fin (n - 1))) :
    Submodule F (Vm n F) :=
  supp F (activeCoords n S : Set (Idx n))

theorem mem_anchoredSupport_iff {S : Finset (Fin (n - 1))} {v : Vm n F} :
    v ∈ anchoredSupport F n S ↔ ∀ a ∉ (activeCoords n S : Set (Idx n)), v a = 0 :=
  Iff.rfl

theorem single_mem_anchoredSupport {S : Finset (Fin (n - 1))} {k : Fin (n - 1)} (hk : k ∈ S)
    (s : Bool) (x : F) :
    (Pi.single (minusPos n k s) x : Vm n F) ∈ anchoredSupport F n S := by
  refine single_mem_supp (F := F) ?_ x
  exact Finset.mem_coe.2 (Finset.mem_union_left _ (minusPos_mem_frame hk s))

theorem planeVec_mem_anchoredSupport (S : Finset (Fin (n - 1))) (p : Fin 2 → F) :
    planeVec n p ∈ anchoredSupport F n S := by
  intro a ha
  exact not_mem_planeCoords (F := F) (fun h => ha (Finset.mem_coe.2
    (Finset.mem_union_right _ h))) p

theorem polarNondegOn_anchoredSupport (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (S : Finset (Fin (n - 1))) :
    PolarNondegOn (quadMinus n F b c) (anchoredSupport F n S) := by
  have hb : b ≠ 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h4 : (4 : F) = 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num, h2, zero_mul]
    have h := discr_ne_zero_of_finite (K := F) hirr
    rw [h4, zero_mul, sub_zero] at h
    exact (pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
  intro x hx hxorth
  funext a
  simp only [Pi.zero_apply]
  rcases a with k | k | t
  ·
    by_cases hk : k ∈ S
    · have hmem : (Pi.single (Sum.inr (Sum.inl k)) (1 : F) : Vm n F) ∈
          anchoredSupport F n S := by
        exact single_mem_supp (F := F) (Finset.mem_coe.2 (Finset.mem_union_left _
          (Finset.mem_union_right _ (inr_inl_mem_fCoords.2 hk)))) 1
      have h0 := hxorth _ hmem
      rw [polar_quadMinus_single_inr_inl] at h0
      exact h0
    · refine hx _ ?_
      rw [activeCoords, Finset.mem_coe, Finset.mem_union, Finset.mem_union]
      rintro ((h1 | h2) | h3)
      · exact hk (inl_mem_eCoords.1 h1)
      · exact absurd h2 (inl_not_mem_fCoords S k)
      · exact absurd h3 (by simp [planeCoords])
  ·
    by_cases hk : k ∈ S
    · have hmem : (Pi.single (Sum.inl k) (1 : F) : Vm n F) ∈ anchoredSupport F n S := by
        exact single_mem_supp (F := F) (Finset.mem_coe.2 (Finset.mem_union_left _
          (Finset.mem_union_left _ (inl_mem_eCoords.2 hk)))) 1
      have h0 := hxorth _ hmem
      rw [polar_quadMinus_single_inl] at h0
      exact h0
    · refine hx _ ?_
      rw [activeCoords, Finset.mem_coe, Finset.mem_union, Finset.mem_union]
      rintro ((h1 | h2) | h3)
      · exact absurd h1 (inr_inl_not_mem_eCoords S k)
      · exact hk (inr_inl_mem_fCoords.1 h2)
      · exact absurd h3 (by simp [planeCoords])
  ·
    have hmem0 : (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : Vm n F) ∈
        anchoredSupport F n S := by
      exact single_mem_supp (F := F) (Finset.mem_coe.2 (Finset.mem_union_right _
        (by simp [planeCoords]))) 1
    have hmem1 : (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : Vm n F) ∈
        anchoredSupport F n S := by
      exact single_mem_supp (F := F) (Finset.mem_coe.2 (Finset.mem_union_right _
        (by simp [planeCoords]))) 1
    have h0 := hxorth _ hmem0
    have h1 := hxorth _ hmem1
    rw [polar_quadMinus_single_inr_inr_zero] at h0
    rw [polar_quadMinus_single_inr_inr_one] at h1
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [h2] at h0 h1
    simp only [zero_mul, zero_add, mul_zero, add_zero] at h0 h1
    have hx1 : x (.inr (.inr 1)) = 0 := (mul_eq_zero.mp h0).resolve_left hb
    have hx0 : x (.inr (.inr 0)) = 0 := (mul_eq_zero.mp h1).resolve_left hb
    fin_cases t
    · exact hx0
    · exact hx1

theorem spinAction_longRoot_mem_supportedDerived
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    (s t : Bool) (x : F) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longRoot hij s t (.ofAdd x)) ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n S) := by
  obtain ⟨ν, hν0, hν1⟩ :=
    CFSG.RankThree.GF2n.Stroth80.Satz5.exists_ne_zero_one (K := F) hcard
  have hreg := polarNondegOn_anchoredSupport (F := F) hirr S
  have hnd : (polarBilin ((quadMinus n F b c).comp (anchoredSupport F n S).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict hreg
  rw [HypFrame.spinAction_longRoot_eq_eichler (F := (minusFrame n b c).toHypFrame) hij s t x,
    minusFrame_vec]
  refine eichler_mem_supportedDerived ?_ ?_ (quadMinus_minusVec n b c j t) ?_ ?_
  · rw [minusVec_eq_single]
    exact single_mem_anchoredSupport hj t 1
  · rw [minusVec_eq_single]
    exact (anchoredSupport F n S).smul_mem x (single_mem_anchoredSupport hi s 1)
  · rw [polar_smul_right, polar_minusVec_minusVec,
      if_neg (by rintro ⟨hji, -⟩; exact hij hji.symm)]
    simp
  · exact eichler_mem_orthDerived_of_ne_zero_ne_one hnd hν0 hν1 _ _

theorem spinAction_twShortRoot_mem_supportedDerived
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (S : Finset (Fin (n - 1))) {i : Fin (n - 1)} (hi : i ∈ S) (s : Bool)
    (p : Fin 2 → F) :
    spinAction (quadMinus n F b c) (twShortRoot n hirr i s (.ofAdd p)) ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n S) := by
  obtain ⟨ν, hν0, hν1⟩ :=
    CFSG.RankThree.GF2n.Stroth80.Satz5.exists_ne_zero_one (K := F) hcard
  have hreg := polarNondegOn_anchoredSupport (F := F) hirr S
  have hnd : (polarBilin ((quadMinus n F b c).comp (anchoredSupport F n S).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict hreg
  rw [spinAction_twShortRoot_eq_eichler n hirr i s p]
  refine eichler_mem_supportedDerived ?_ (planeVec_mem_anchoredSupport S p)
    (quadMinus_minusVec n b c i s) (polar_minusVec_planeVec n b c i s p) ?_
  · rw [minusVec_eq_single]
    exact single_mem_anchoredSupport hi s 1
  · exact eichler_mem_orthDerived_of_ne_zero_ne_one hnd hν0 hν1 _ _

theorem leviM_map_spinAction_le_supportedDerived
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (I : Set (Fin (n - 1))) (S : Finset (Fin (n - 1)))
    (hI : ∀ k ∈ I, k ∈ S ∧ ∀ hk : k.val + 1 < n - 1, (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ S) :
    (leviM (minusDatum n hirr) I).map (spinAction (quadMinus n F b c)) ≤
      supportedDerived (quadMinus n F b c) (anchoredSupport F n S) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun (k : Fin (n - 1)) hk => ?_
  obtain ⟨hkS, hk'S⟩ := hI k hk
  by_cases hk1 : k.val + 1 < n - 1
  ·
    refine sup_le ?_ ?_
    · change minusRootGroup n hirr (Pi.single k 1) ≤
        (supportedDerived (quadMinus n F b c) (anchoredSupport F n S)).comap
          (spinAction (quadMinus n F b c))
      rw [minusRootGroup_single_of_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_comap.2 (spinAction_longRoot_mem_supportedDerived hirr hcard S
        (succ_ne_of_lt n hk1) hkS (hk'S hk1) true false x.toAdd)
    · change minusRootGroup n hirr (-Pi.single k 1) ≤
        (supportedDerived (quadMinus n F b c) (anchoredSupport F n S)).comap
          (spinAction (quadMinus n F b c))
      rw [minusRootGroup_neg_single_of_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_comap.2 (spinAction_longRoot_mem_supportedDerived hirr hcard S
        (succ_ne_of_lt n hk1).symm (hk'S hk1) hkS true false x.toAdd)
  ·
    refine sup_le ?_ ?_
    · change minusRootGroup n hirr (Pi.single k 1) ≤
        (supportedDerived (quadMinus n F b c) (anchoredSupport F n S)).comap
          (spinAction (quadMinus n F b c))
      rw [minusRootGroup_single_of_not_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_comap.2 (spinAction_twShortRoot_mem_supportedDerived hirr hcard S
        hkS true x.toAdd)
    · change minusRootGroup n hirr (-Pi.single k 1) ≤
        (supportedDerived (quadMinus n F b c) (anchoredSupport F n S)).comap
          (spinAction (quadMinus n F b c))
      rw [minusRootGroup_neg_single_of_not_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_comap.2 (spinAction_twShortRoot_mem_supportedDerived hirr hcard S
        hkS false x.toAdd)

@[expose] noncomputable def totalCoords (n : ℕ) (J : Finset (Fin (n - 1))) :
    Finset (Fin (n - 1)) :=
  J ∪ coordsF n (J : Set (Fin (n - 1)))

theorem totalCoords_mono {J K : Finset (Fin (n - 1))} (h : J ⊆ K) :
    totalCoords n J ⊆ totalCoords n K := by
  intro a ha
  rw [totalCoords, Finset.mem_union] at ha ⊢
  rcases ha with haJ | haC
  · exact Or.inl (h haJ)
  · right
    obtain ⟨i, hi, hk, h'⟩ := mem_coordsF.1 haC
    exact mem_coordsF.2 ⟨i, h hi, hk, h'⟩

theorem card_totalCoords_le (J : Finset (Fin (n - 1))) :
    (totalCoords n J).card ≤ 2 * J.card := by
  classical
  let succPlane : Fin (n - 1) → Fin (n - 1) := fun i =>
    if h : i.val + 1 < n - 1 then ⟨i.val + 1, h⟩ else i
  have hsub : totalCoords n J ⊆ J ∪ J.image succPlane := by
    intro a ha
    rw [totalCoords, Finset.mem_union] at ha
    rcases ha with haJ | haC
    · exact Finset.mem_union_left _ haJ
    · obtain ⟨i, hi, hk, rfl | hval⟩ := mem_coordsF.1 haC
      · exact Finset.mem_union_left _ hi
      · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, hi, ?_⟩)
        apply Fin.ext
        simp [succPlane, hk, hval]
  calc
    (totalCoords n J).card ≤ (J ∪ J.image succPlane).card := Finset.card_le_card hsub
    _ ≤ J.card + (J.image succPlane).card := Finset.card_union_le _ _
    _ ≤ J.card + J.card := add_le_add le_rfl Finset.card_image_le
    _ = 2 * J.card := by ring

theorem totalCoords_ne_univ {J : Finset (Fin (n - 1))} (hJ : J.card ≤ 2)
    (hn : 5 ≤ n - 1) : totalCoords n J ≠ Finset.univ := by
  intro h
  have hcard := card_totalCoords_le (n := n) J
  rw [h, Finset.card_univ, Fintype.card_fin] at hcard
  omega

end CFSG.RankThree.PartOne.KCOrthogonal
