module

public import CFSG.Monster.B.TwoA.Unitary.LinThree
import all CFSG.Fischer.F4
public import Certificates.Certificate16015

public noncomputable section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.Monster.B.TwoA.Unitary.LinThree
open scoped Pointwise

@[expose] def planeLines : Set (Set PlanePoint) :=
  {S | ∃ f : Module.Dual F4 (Fin 3 → F4), f ≠ 0 ∧ S = {x | f x.rep = 0}}

theorem lineSet_mem_planeLines (b : Fin 21) : lineSet b ∈ planeLines :=
  ⟨dotForm (Ω b), dotForm_ne_zero (Ω_ne_zero b), lineSet_eq_kernel b⟩

theorem mem_planeLines_iff {S : Set PlanePoint} : S ∈ planeLines ↔ ∃ b, S = lineSet b := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, kernel_eq_lineSet f hf⟩
  · rintro ⟨b, rfl⟩
    exact lineSet_mem_planeLines b

theorem planeLines_eq_range : planeLines = Set.range lineSet := by
  ext S
  rw [mem_planeLines_iff]
  exact ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩

theorem Ωproj_mem_lineSet {i b : Fin 21} : Ωproj i ∈ lineSet b ↔ i ∈ projLine b := by
  rw [lineSet, Ωproj.injective.mem_set_image, Finset.mem_coe]

theorem Ω_five : Ω 5 = ![1, 0, 0] := by decide

theorem pPt_eq : pPt = Ωproj 5 := by
  rw [pPt, Ωproj_apply]
  exact mk_eq_mk_of_eq _ _ Ω_five.symm

theorem sum_Ω_zero (v : Fin 3 → F4) : ∑ k, Ω 0 k * v k = v 2 := by
  rw [Fin.sum_univ_three]
  have h0 : Ω 0 0 = 0 := rfl
  have h1 : Ω 0 1 = 0 := rfl
  have h2 : Ω 0 2 = 1 := rfl
  rw [h0, h1, h2, zero_mul, zero_mul, one_mul, zero_add, zero_add]

theorem vec_eq_of_two (v : Fin 3 → F4) (hv : v 2 = 0) : v = ![v 0, v 1, 0] := by
  funext k
  fin_cases k
  · rfl
  · rfl
  · exact hv

theorem ellLine_eq : ellLine = lineSet 0 := by
  rw [lineSet_eq_kernel]
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
    rw [Set.mem_ofPred_eq, form_rep_eq_zero_iff, dotForm_apply, sum_Ω_zero]
    constructor
    · rintro ⟨a, b, h, e⟩
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F4 v _ hv h).1 e
      rw [← hc]
      change c * 0 = 0
      exact mul_zero c
    · intro h2
      exact ⟨v 0, v 1, vec_eq_of_two v h2 ▸ hv, mk_eq_mk_of_eq _ _ (vec_eq_of_two v h2)⟩

theorem pPt_mem_ellLine : pPt ∈ ellLine := ⟨1, 0, vec100_ne_zero, rfl⟩

theorem ellLine_mem_planeLines : ellLine ∈ planeLines := by
  rw [ellLine_eq]
  exact lineSet_mem_planeLines 0

theorem genPt_eq : ∀ (k : Fin 6) (i : Fin 21), genPt k i =
    normIdx (CFSG.Monster.B.Classical.ThreePlane.pairVec (genMat k) (genFrob k) (Ω i)) :=
  Certificates.certificate16015.1

theorem genLn_spec : ∀ (k : Fin 6) (b : Fin 21),
    (projLine b).image (genPt k) = projLine (genLn k b) :=
  Certificates.certificate16015.2.1

theorem genLn_surjective : ∀ k : Fin 6, Function.Surjective (genLn k) := by
  decide

theorem genElt_smul_Ωproj
    (k : Fin 6) (i : Fin 21) : genElt k • Ωproj i = Ωproj (genPt k i) := by
  rw [genElt, Ωproj_apply, pairElt_smul_mk]
  apply Ωproj.symm.injective
  rw [Ωproj_symm_mk, Equiv.symm_apply_apply, genPt_eq]
  rfl

theorem genElt_smul_lineSet (k : Fin 6) (b : Fin 21) :
    genElt k • lineSet b = lineSet (genLn k b) := by
  rw [lineSet, lineSet, ← genLn_spec, Finset.coe_image, Set.image_image, ← Set.image_smul,
    Set.image_image]
  exact Set.image_congr fun i _ => genElt_smul_Ωproj k i

theorem wordElt_smul_Ωproj (w : List (Fin 6)) (i : Fin 21) :
    (w.map genElt).prod • Ωproj i = Ωproj (w.foldr genPt i) := by
  induction w with
  | nil => rw [List.map_nil, List.prod_nil, one_smul, List.foldr_nil]
  | cons k w ih => rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons,
      genElt_smul_Ωproj]

theorem wordElt_smul_lineSet (w : List (Fin 6)) (b : Fin 21) :
    (w.map genElt).prod • lineSet b = lineSet (w.foldr genLn b) := by
  induction w with
  | nil => rw [List.map_nil, List.prod_nil, one_smul, List.foldr_nil]
  | cons k w ih => rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons,
      genElt_smul_lineSet]

theorem flagCert_spec : ∀ i b : Fin 21, i ∈ projLine b →
    ∃ e ∈ flagCert, e.1 = i ∧ e.2.1 = b ∧ e.2.2.foldr genPt 5 = i ∧ e.2.2.foldr genLn 0 = b :=
  Certificates.certificate16015.2.2

theorem genElt_mem_stabilizer (k : Fin 6) :
    genElt k ∈ MulAction.stabilizer SigmaL3 (Set.range lineSet) := by
  rw [MulAction.mem_stabilizer_iff, ← Set.image_smul, ← Set.range_comp]
  ext S
  simp only [Set.mem_range, Function.comp_apply, genElt_smul_lineSet]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := genLn_surjective k b
    exact ⟨a, rfl⟩

theorem stabilizer_range_lineSet :
    MulAction.stabilizer SigmaL3 (Set.range lineSet) = ⊤ := by
  rw [eq_top_iff, ← closure_genElt, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact genElt_mem_stabilizer k

theorem smul_mem_planeLines
    (s : SigmaL3) {S : Set PlanePoint} (hS : S ∈ planeLines) :
    s • S ∈ planeLines := by
  rw [planeLines_eq_range] at hS ⊢
  have h : s • Set.range lineSet = Set.range lineSet :=
    MulAction.mem_stabilizer_iff.1 (stabilizer_range_lineSet ▸ Subgroup.mem_top s)
  rw [← h]
  exact Set.smul_mem_smul_set hS

theorem exists_smul_flag
    {x : PlanePoint} {S : Set PlanePoint} (hS : S ∈ planeLines)
    (hx : x ∈ S) : ∃ s : SigmaL3, s • pPt = x ∧ s • ellLine = S := by
  obtain ⟨b, rfl⟩ := mem_planeLines_iff.1 hS
  obtain ⟨i, rfl⟩ := Ωproj.surjective x
  obtain ⟨e, -, -, -, h1, h2⟩ := flagCert_spec i b (Ωproj_mem_lineSet.1 hx)
  refine ⟨(e.2.2.map genElt).prod, ?_, ?_⟩
  · rw [pPt_eq, wordElt_smul_Ωproj, h1]
  · rw [ellLine_eq, wordElt_smul_lineSet, h2]

theorem exists_mem_projLine : ∀ i : Fin 21, ∃ b, i ∈ projLine b := by decide

theorem exists_mem_projLine' : ∀ b : Fin 21, ∃ i, i ∈ projLine b := by decide

theorem exists_smul_pPt
    (x : PlanePoint) : ∃ s : SigmaL3, s • pPt = x := by
  obtain ⟨i, rfl⟩ := Ωproj.surjective x
  obtain ⟨b, hb⟩ := exists_mem_projLine i
  obtain ⟨s, hs, -⟩ := exists_smul_flag (lineSet_mem_planeLines b) (Ωproj_mem_lineSet.2 hb)
  exact ⟨s, hs⟩

theorem exists_smul_ellLine
    {S : Set PlanePoint} (hS : S ∈ planeLines) :
    ∃ s : SigmaL3, s • ellLine = S := by
  obtain ⟨b, rfl⟩ := mem_planeLines_iff.1 hS
  obtain ⟨i, hi⟩ := exists_mem_projLine' b
  obtain ⟨s, -, hs⟩ := exists_smul_flag (lineSet_mem_planeLines b) (Ωproj_mem_lineSet.2 hi)
  exact ⟨s, hs⟩

@[expose] def nc3 : NativeCoord := ⟨3, le_refl _⟩

theorem j_three : j nc3 = pPt := by
  rw [pPt_eq]
  rfl

theorem mem_nlMask_zero_iff : ∀ i : Fin 24, 3 ≤ (i : ℕ) →
    (i ∈ (ofMask (nlMask 0) : Finset (Fin 24)) ↔ (i : ℕ) < 8) := by
  decide

theorem image_j_lt_eight : j '' {i : NativeCoord | (i : ℕ) < 8} = ellLine := by
  rw [ellLine_eq, ← image_nlMask]
  congr 1
  ext i
  exact (mem_nlMask_zero_iff i i.2).symm

end CFSG.Monster.B.TwoA.Amalgam
