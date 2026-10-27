module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2FixDim
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley CFSG.AGLEmbedding.KFactProofs.G2Q

private noncomputable def g2chi {L : Type} [Field L] (s t : Lˣ) : Label .G2 → Lˣ
  | .inl _ => 1
  | .inr a => s ^ (∑ j, Tag.G2.cartan ia j * a.1 j) * t ^ (∑ j, Tag.G2.cartan ir j * a.1 j)

private lemma g2chi_inl {L : Type} [Field L] (s t : Lˣ) (j : Fin Tag.G2.rank) :
    g2chi s t (.inl j) = 1 := rfl

private lemma g2chi_inr {L : Type} [Field L] (s t : Lˣ)
    (a : {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v}) :
    g2chi s t (.inr a) =
      s ^ (∑ j, Tag.G2.cartan ia j * a.1 j) * t ^ (∑ j, Tag.G2.cartan ir j * a.1 j) := rfl

private lemma fin_sum_two_eq (f : Fin Tag.G2.rank → ℤ) :
    (∑ j, f j) = f ia + f ir := by
  rw [show (Finset.univ : Finset (Fin Tag.G2.rank)) = {ia, ir} by decide,
    Finset.sum_pair (by decide)]

private lemma cartan_ia_sum
    (α : Fin Tag.G2.rank → ℤ) :
    (∑ j, Tag.G2.cartan ia j * α j) = 2 * α ia - α ir := by
  rw [fin_sum_two_eq, cartan_ia_ia, cartan_ia_ir]
  ring

private lemma cartan_ir_sum
    (α : Fin Tag.G2.rank → ℤ) :
    (∑ j, Tag.G2.cartan ir j * α j) = -3 * α ia + 2 * α ir := by
  rw [fin_sum_two_eq, cartan_ir_ia, cartan_ir_ir]

private lemma torusElt_rootVec_ia_apply
    {L : Type} [Field L] (s : Lˣ)
    (a : {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v}) :
    (torusElt .G2 L ia s : Module.End L (RootModule .G2 L)) (rootVec .G2 L a.1) =
      ((s ^ (2 * a.1 ia - a.1 ir) : Lˣ) : L) • rootVec .G2 L a.1 := by
  rw [torusElt_rootVec ia s a.2, cartan_ia_sum]

private lemma torusElt_rootVec_ir_apply
    {L : Type} [Field L] (t : Lˣ)
    (a : {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v}) :
    (torusElt .G2 L ir t : Module.End L (RootModule .G2 L)) (rootVec .G2 L a.1) =
      ((t ^ (-3 * a.1 ia + 2 * a.1 ir) : Lˣ) : L) • rootVec .G2 L a.1 := by
  rw [torusElt_rootVec ir t a.2, cartan_ir_sum]

private lemma tz_single
    {L : Type} [Field L] (s t : Lˣ) (b : Label .G2) :
    ((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) (Finsupp.single b 1) =
      ((g2chi s t b : Lˣ) : L) • Finsupp.single b 1 := by
  rcases b with j | a
  · rw [show Finsupp.single (Sum.inl j) 1 = hVec .G2 L j from rfl, g2chi_inl]
    rw [tz, Units.val_mul, Module.End.mul_apply, torusElt_hVec, torusElt_hVec]
    simp
  · rw [show Finsupp.single (Sum.inr a) 1 = rootVec .G2 L a.1 from
        (rootVec_eq_single_of_isRoot a.2).symm, g2chi_inr, cartan_ia_sum, cartan_ir_sum]
    rw [tz, Units.val_mul, Module.End.mul_apply, torusElt_rootVec_ir_apply,
      map_smul, torusElt_rootVec_ia_apply, smul_smul]
    congr 1
    rw [← Units.val_mul]
    exact congrArg Units.val (mul_comm _ _)

private noncomputable def diag {L : Type} [Field L] (χ : Label .G2 → Lˣ) :
    RootModule .G2 L →ₗ[L] RootModule .G2 L :=
  Finsupp.linearCombination L (fun b => ((χ b : Lˣ) : L) • Finsupp.single b 1)

private lemma diag_single {L : Type} [Field L] (χ : Label .G2 → Lˣ) (b : Label .G2) (c : L) :
    diag χ (Finsupp.single b c) = ((χ b : Lˣ) : L) • Finsupp.single b c := by
  rw [diag, Finsupp.linearCombination_single, Finsupp.smul_single_one,
    Finsupp.smul_single, Finsupp.smul_single]
  congr 1
  ring

private lemma diag_apply {L : Type} [Field L] (χ : Label .G2 → Lˣ) (u : RootModule .G2 L)
    (b : Label .G2) :
    diag χ u b = ((χ b : Lˣ) : L) * u b := by
  induction u using Finsupp.induction_linear with
  | zero => simp [diag]
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]; ring
  | single a c =>
      rw [diag_single, Finsupp.smul_apply]
      rcases eq_or_ne a b with rfl | hab
      · simp
      · simp [hab]

private lemma tz_eq_diag
    {L : Type} [Field L] (s t : Lˣ) :
    ((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) = diag (g2chi s t) := by
  apply Finsupp.lhom_ext
  intro b c
  rw [diag_single]
  rw [← Finsupp.smul_single_one b c, map_smul, tz_single, smul_comm]

private lemma tz_apply
    {L : Type} [Field L] (s t : Lˣ) (u : RootModule .G2 L) (b : Label .G2) :
    ((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) u b =
      ((g2chi s t b : Lˣ) : L) * u b := by
  rw [tz_eq_diag, diag_apply]

private lemma ker_le_supported
    {L : Type} [Field L] (s t : Lˣ) :
    LinearMap.ker (((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) - 1) ≤
      Finsupp.supported L L {b : Label .G2 | g2chi s t b = 1} := by
  intro u hu
  rw [LinearMap.mem_ker] at hu
  rw [Finsupp.mem_supported]
  intro b hb
  by_contra hne
  have hmem : u b ≠ 0 := Finsupp.mem_support_iff.1 hb
  have h1 : ((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) u b - u b = 0 := by
    have h := congrArg (fun w : RootModule .G2 L => w b) hu
    simpa using h
  rw [tz_apply] at h1
  have h2 : (((g2chi s t b : Lˣ) : L) - 1) * u b = 0 := by
    rw [sub_mul, one_mul]
    exact h1
  have hne' : ((g2chi s t b : Lˣ) : L) - 1 ≠ 0 := by
    intro h0
    apply hne
    exact Units.ext (by rw [sub_eq_zero.1 h0, Units.val_one])
  exact hmem ((mul_eq_zero.1 h2).resolve_left hne')

private lemma finrank_supported_eq_card
    {L : Type} [Field L] (S : Set (Label .G2)) :
    Module.finrank L (Finsupp.supported L L S) = Nat.card S := by
  classical
  have hS : Fintype S := Fintype.ofFinite S
  rw [(Finsupp.supportedEquivFinsupp (M := L) (R := L) S).finrank_eq,
    Module.finrank_finsupp_self]
  exact (Nat.card_eq_fintype_card).symm

private lemma g2AdjFixDim_le_ncard
    {L : Type} [Field L] (s t : Lˣ) :
    g2AdjFixDim (tz s t : ModGL .G2 L) ≤
      Nat.card {b : Label .G2 | g2chi s t b = 1} := by
  classical
  have hfin : FiniteDimensional L
      (Finsupp.supported L L {b : Label .G2 | g2chi s t b = 1}) :=
    LinearEquiv.finiteDimensional
      (Finsupp.supportedEquivFinsupp (M := L) (R := L) _).symm
  unfold g2AdjFixDim
  calc
    Module.finrank L (LinearMap.ker
        (((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) - 1))
        ≤ Module.finrank L (Finsupp.supported L L {b : Label .G2 | g2chi s t b = 1}) :=
          Submodule.finrank_mono (ker_le_supported s t)
    _ = Nat.card {b : Label .G2 | g2chi s t b = 1} := finrank_supported_eq_card _

private noncomputable def pc {L : Type} [Field L] (s t : Lˣ) : Fin 6 → Lˣ :=
  ![s ^ (2 : ℤ) * t ^ (-3 : ℤ), s ^ (-1 : ℤ) * t ^ (3 : ℤ), s,
    s ^ (-1 : ℤ) * t ^ (2 : ℤ), s * t ^ (-1 : ℤ), t]

private lemma pc0_mul_pc1 {L : Type} [Field L] (s t : Lˣ) :
    pc s t 0 * pc s t 1 = pc s t 2 := by
  simp [pc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

private lemma pc3_mul_pc4 {L : Type} [Field L] (s t : Lˣ) :
    pc s t 3 * pc s t 4 = pc s t 5 := by
  simp [pc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

private lemma pc4_mul_pc5 {L : Type} [Field L] (s t : Lˣ) :
    pc s t 4 * pc s t 5 = pc s t 2 := by
  simp [pc]

private lemma pc3_inv_mul_pc5_sq {L : Type} [Field L] (s t : Lˣ) :
    (pc s t 3)⁻¹ * (pc s t 5) ^ 2 = pc s t 2 := by
  simp [pc]

private def prootCoord : Fin 6 → Fin Tag.G2.rank → ℤ :=
  ![![1, 0], ![1, 3], ![2, 3], ![0, 1], ![1, 1], ![1, 2]]

private def firstCoord : Fin 6 → ℤ := ![1, 1, 2, 0, 1, 1]
private def secondCoord : Fin 6 → ℤ := ![0, 3, 3, 1, 1, 2]

private lemma prootCoord_ia (i : Fin 6) : prootCoord i ia = firstCoord i := by
  fin_cases i <;> decide

private lemma prootCoord_ir (i : Fin 6) : prootCoord i ir = secondCoord i := by
  fin_cases i <;> decide

private lemma prootCoord_mem (i : Fin 6) : prootCoord i ∈ CFSG.GH74.GLS.IVK.Proofs2.Ivk47.posRootList := by
  fin_cases i <;> decide

private noncomputable def proot :
    Fin 6 → {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v} :=
  fun i => ⟨prootCoord i, (CFSG.GH74.GLS.IVK.Proofs2.Ivk47.mem_posRootList_iff.1 (prootCoord_mem i)).1⟩

private lemma proot_val (i : Fin 6) :
    (proot i).1 = prootCoord i := rfl

private lemma exists_prootCoord_of_mem {α : Fin Tag.G2.rank → ℤ} (h : α ∈ CFSG.GH74.GLS.IVK.Proofs2.Ivk47.posRootList) :
    ∃ i : Fin 6, prootCoord i = α := by
  have hof : CFSG.GH74.GLS.IVK.Proofs2.Ivk47.posRootList.toFinset = (List.ofFn prootCoord).toFinset := by decide
  rw [← List.mem_toFinset, hof, List.mem_toFinset, List.mem_ofFn'] at h
  exact h

private lemma proot_surj_pos {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) (hpos : 0 < height α) : ∃ i : Fin 6, (proot i).1 = α := by
  obtain ⟨i, hi⟩ := exists_prootCoord_of_mem ((CFSG.GH74.GLS.IVK.Proofs2.Ivk47.mem_posRootList_iff).2 ⟨hα, hpos⟩)
  exact ⟨i, hi⟩

private lemma g2chi_proot
    {L : Type} [Field L] (s t : Lˣ) (i : Fin 6) :
    g2chi s t (.inr (proot i)) = pc s t i := by
  rw [g2chi_inr, cartan_ia_sum, cartan_ir_sum, proot_val, prootCoord_ia, prootCoord_ir]
  fin_cases i <;>
    simp only [pc, firstCoord, secondCoord] <;>
    norm_num

private lemma g2chi_neg {L : Type} [Field L] (s t : Lˣ)
    (a : {v : Fin Tag.G2.rank → ℤ // IsRoot .G2 v}) :
    g2chi s t (.inr (-a)) = (g2chi s t (.inr a))⁻¹ := by
  rw [g2chi_inr, g2chi_inr, CFSG.LieType.Chevalley.coe_neg_root]
  simp only [Pi.neg_apply]
  have hia : (∑ j, Tag.G2.cartan ia j * -a.1 j) =
      -(∑ j, Tag.G2.cartan ia j * a.1 j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hir : (∑ j, Tag.G2.cartan ir j * -a.1 j) =
      -(∑ j, Tag.G2.cartan ir j * a.1 j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hia, hir]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

private noncomputable def goodIdx {L : Type} [Field L] (s t : Lˣ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => pc s t i = 1)

private noncomputable def candidate {L : Type} [Field L]
    (s t : Lˣ) : Finset (Label .G2) :=
  ({Sum.inl ia, Sum.inl ir} : Finset (Label .G2)) ∪
    (goodIdx s t).image (fun i => Sum.inr (proot i)) ∪
    (goodIdx s t).image (fun i => Sum.inr (-(proot i)))

private lemma sset_subset_candidate
    {L : Type} [Field L] (s t : Lˣ) :
    {b : Label .G2 | g2chi s t b = 1} ⊆ (candidate s t : Set (Label .G2)) := by
  classical
  intro b hb
  rcases b with j | a
  · fin_cases j
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_insert_self (Sum.inl ia) {Sum.inl ir}))
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self (Sum.inl ir))))
  · rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg a.2 with hpos | hneg
    · obtain ⟨i, hi⟩ := proot_surj_pos a.2 hpos
      have hproot : proot i = a := Subtype.ext hi
      have hpc : pc s t i = 1 := by
        rw [← g2chi_proot s t i, hproot]
        exact hb
      rw [show (Sum.inr a : Label .G2) = Sum.inr (proot i) from by rw [hproot]]
      exact Finset.mem_union_left _
        (Finset.mem_union_right _
          (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpc⟩, rfl⟩))
    · have hpos' : 0 < height (-a).1 := by
        rw [CFSG.LieType.Chevalley.coe_neg_root, CFSG.LieType.Chevalley.height_neg]
        omega
      obtain ⟨i, hi⟩ := proot_surj_pos (CFSG.LieType.Chevalley.IsRoot.neg a.2) hpos'
      have hproot : proot i = -a := Subtype.ext hi
      have hpc : pc s t i = 1 := by
        rw [← g2chi_proot s t i, hproot, g2chi_neg, hb, inv_one]
      have ha : a = -(proot i) := by
        rw [hproot, neg_neg]
      rw [show (Sum.inr a : Label .G2) = Sum.inr (-(proot i)) from by rw [ha]]
      exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpc⟩, rfl⟩)

private lemma not_pc0_pc1 {L : Type} [Field L] {s t : Lˣ}
    (hnot : ¬ (s = 1 ∧ t ^ 3 = 1)) :
    ¬ (pc s t 0 = 1 ∧ pc s t 1 = 1) := by
  rintro ⟨h0, h1⟩
  apply hnot
  have hs : s = 1 := by
    have h2 : pc s t 2 = 1 := by rw [← pc0_mul_pc1 s t, h0, h1, one_mul]
    simpa [pc] using h2
  refine ⟨hs, ?_⟩
  simpa [pc, hs] using h1

private lemma not_pc3_pc4 {L : Type} [Field L] {s t : Lˣ}
    (hnot : ¬ (s = 1 ∧ t ^ 3 = 1)) :
    ¬ (pc s t 3 = 1 ∧ pc s t 4 = 1) := by
  rintro ⟨h3, h4⟩
  apply hnot
  have h5 : pc s t 5 = 1 := by rw [← pc3_mul_pc4 s t, h3, h4, one_mul]
  refine ⟨?_, ?_⟩
  · have h2 : pc s t 2 = 1 := by rw [← pc4_mul_pc5 s t, h4, h5, one_mul]
    simpa [pc] using h2
  · have ht : t = 1 := by simpa [pc] using h5
    rw [ht, one_pow]

private lemma not_pc3_pc5 {L : Type} [Field L] {s t : Lˣ}
    (hnot : ¬ (s = 1 ∧ t ^ 3 = 1)) :
    ¬ (pc s t 3 = 1 ∧ pc s t 5 = 1) := by
  rintro ⟨h3, h5⟩
  apply hnot
  refine ⟨?_, ?_⟩
  · have h2 : pc s t 2 = 1 := by rw [← pc3_inv_mul_pc5_sq s t, h3, h5]; simp
    simpa [pc] using h2
  · have ht : t = 1 := by simpa [pc] using h5
    rw [ht, one_pow]

private lemma not_pc4_pc5 {L : Type} [Field L] {s t : Lˣ}
    (hnot : ¬ (s = 1 ∧ t ^ 3 = 1)) :
    ¬ (pc s t 4 = 1 ∧ pc s t 5 = 1) := by
  rintro ⟨h4, h5⟩
  apply hnot
  refine ⟨?_, ?_⟩
  · have h2 : pc s t 2 = 1 := by rw [← pc4_mul_pc5 s t, h4, h5, one_mul]
    simpa [pc] using h2
  · have ht : t = 1 := by simpa [pc] using h5
    rw [ht, one_pow]

private lemma card_filter_pc_le_two {L : Type} [Field L] {s t : Lˣ}
    (hnot : ¬ (s = 1 ∧ t ^ 3 = 1)) :
    (goodIdx s t).card ≤ 2 := by
  classical
  have hmem : ∀ i, i ∈ goodIdx s t ↔ pc s t i = 1 := by intro i; simp [goodIdx]
  have hB : ((goodIdx s t).filter (fun i => i = 3 ∨ i = 4 ∨ i = 5)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have ha1 : pc s t a = 1 := (hmem a).1 ha.1
    have hb1 : pc s t b = 1 := (hmem b).1 hb.1
    have h34 : pc s t 3 = 1 → pc s t 4 = 1 → False := fun x y => not_pc3_pc4 hnot ⟨x, y⟩
    have h35 : pc s t 3 = 1 → pc s t 5 = 1 → False := fun x y => not_pc3_pc5 hnot ⟨x, y⟩
    have h45 : pc s t 4 = 1 → pc s t 5 = 1 → False := fun x y => not_pc4_pc5 hnot ⟨x, y⟩
    rcases ha.2 with rfl | rfl | rfl <;> rcases hb.2 with rfl | rfl | rfl <;>
      first
        | rfl
        | tauto
  by_cases h2 : pc s t 2 = 1
  · have hs : s = 1 := by simpa [pc] using h2
    have ht3 : t ^ (3 : ℤ) ≠ 1 := by
      intro h
      exact hnot ⟨hs, by simpa using h⟩
    have h0 : pc s t 0 ≠ 1 := by
      intro h
      apply ht3
      have h' : t ^ (-3 : ℤ) = 1 := by simpa [pc, hs] using h
      have h'' : t ^ (3 : ℤ) = 1 := by
        simpa [zpow_neg] using congrArg Inv.inv h'
      exact h''
    have h1 : pc s t 1 ≠ 1 := by
      intro h
      apply ht3
      simpa [pc, hs] using h
    have hA : ((goodIdx s t).filter (fun i => i = 2)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      rw [ha.2, hb.2]
    have hcover : goodIdx s t ⊆ (goodIdx s t).filter (fun i => i = 2) ∪
        (goodIdx s t).filter (fun i => i = 3 ∨ i = 4 ∨ i = 5) := by
      intro i hi
      have hi1 : pc s t i = 1 := (hmem i).1 hi
      fin_cases i <;> simp_all [Finset.mem_filter]
    calc (goodIdx s t).card
        ≤ ((goodIdx s t).filter (fun i => i = 2) ∪
            (goodIdx s t).filter (fun i => i = 3 ∨ i = 4 ∨ i = 5)).card :=
          Finset.card_le_card hcover
      _ ≤ ((goodIdx s t).filter (fun i => i = 2)).card +
            ((goodIdx s t).filter (fun i => i = 3 ∨ i = 4 ∨ i = 5)).card :=
          Finset.card_union_le _ _
      _ ≤ 2 := by omega
  · have hA : ((goodIdx s t).filter (fun i => i = 0 ∨ i = 1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      have ha1 : pc s t a = 1 := (hmem a).1 ha.1
      have hb1 : pc s t b = 1 := (hmem b).1 hb.1
      have h01 : pc s t 0 = 1 → pc s t 1 = 1 → False := fun x y => not_pc0_pc1 hnot ⟨x, y⟩
      rcases ha.2 with rfl | rfl <;> rcases hb.2 with rfl | rfl <;>
        first
          | rfl
          | tauto
    have hcover : goodIdx s t ⊆ (goodIdx s t).filter (fun i => i = 0 ∨ i = 1) ∪
        (goodIdx s t).filter (fun i => i = 3 ∨ i = 4 ∨ i = 5) := by
      intro i hi
      have hi1 : pc s t i = 1 := (hmem i).1 hi
      fin_cases i <;> simp_all [Finset.mem_filter]
    calc (goodIdx s t).card
        ≤ ((goodIdx s t).filter (fun i => i = 0 ∨ i = 1) ∪
            (goodIdx s t).filter (fun i => i = 3 ∨ i = 4 ∨ i = 5)).card :=
          Finset.card_le_card hcover
      _ ≤ ((goodIdx s t).filter (fun i => i = 0 ∨ i = 1)).card +
            ((goodIdx s t).filter (fun i => i = 3 ∨ i = 4 ∨ i = 5)).card :=
          Finset.card_union_le _ _
      _ ≤ 2 := by omega

private lemma ncard_sset_le_six
    {L : Type} [Field L] {s t : Lˣ} (hnot : ¬ (s = 1 ∧ t ^ 3 = 1)) :
    Nat.card {b : Label .G2 | g2chi s t b = 1} ≤ 6 := by
  classical
  have hsub := sset_subset_candidate s t
  have hcard : Nat.card {b : Label .G2 | g2chi s t b = 1} ≤ (candidate s t).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_le_of_injective
      (f := fun x : {b : Label .G2 // g2chi s t b = 1} =>
        (⟨x.1, hsub x.2⟩ : (candidate s t : Set (Label .G2)))) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.mk.inj hxy)
  have h1 : ((goodIdx s t).image fun i => (Sum.inr (proot i) : Label .G2)).card ≤
      (goodIdx s t).card := Finset.card_image_le
  have h2 : ((goodIdx s t).image fun i => (Sum.inr (-(proot i)) : Label .G2)).card ≤
      (goodIdx s t).card := Finset.card_image_le
  have hA : ({Sum.inl ia, Sum.inl ir} : Finset (Label .G2)).card ≤ 2 := Finset.card_le_two
  have hbound : (candidate s t).card ≤ 2 + 2 * (goodIdx s t).card := by
    calc (candidate s t).card
        ≤ (({Sum.inl ia, Sum.inl ir} : Finset (Label .G2)) ∪
            (goodIdx s t).image (fun i => (Sum.inr (proot i) : Label .G2))).card +
            ((goodIdx s t).image fun i => (Sum.inr (-(proot i)) : Label .G2)).card :=
          Finset.card_union_le _ _
      _ ≤ (({Sum.inl ia, Sum.inl ir} : Finset (Label .G2)).card +
            ((goodIdx s t).image fun i => (Sum.inr (proot i) : Label .G2)).card) +
            ((goodIdx s t).image fun i => (Sum.inr (-(proot i)) : Label .G2)).card :=
          add_le_add (Finset.card_union_le _ _) le_rfl
      _ ≤ 2 + 2 * (goodIdx s t).card := by omega
  have hg : (goodIdx s t).card ≤ 2 := card_filter_pc_le_two hnot
  omega

theorem eq_one_of_eight_le_g2AdjFixDim_tz
    {L : Type} [Field L] {s t : Lˣ} (h : 8 ≤ g2AdjFixDim (tz s t : ModGL .G2 L)) :
    s = 1 ∧ t ^ 3 = 1 := by
  by_contra hnot
  have h1 := g2AdjFixDim_le_ncard s t
  have h2 := ncard_sset_le_six hnot
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
