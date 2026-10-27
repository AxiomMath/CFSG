module

public import CFSG.Monster.B.TwoA.Census.MonoXi
public import CFSG.Monster.B.TwoA.Census.MonoClasses
public import CFSG.Monster.Visible.XiPair
public import CFSG.Monster.VisQuot.Image
public import CFSG.Monster.B.TwoA.Census.DenseMat
public meta import CFSG.Monster.B.TwoA.Census.DenseMat
public meta import CFSG.Monster.B.TwoA.Census.MonoXi
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.Xi.Defs
public import CFSG.Monster.B.TwoA.Census.XiFusionInputs
public import Certificates.Certificate3020
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.Xi Matrix

theorem diagonal_sgn_bvec (d : ℕ) : diagonal (fun k => sgn (bvec 24 d k)) = dsgn d := by
  rw [dsgn]
  congr 1
  funext k
  unfold sgn bvec
  by_cases h : d.testBit k <;> simp [h]

theorem Pmat_decode {a : Array ℕ} (h : PermArr a = true) : Pmat (decode a) = pmatA a := by
  ext i j
  have e : decode a i = j ↔ a[(i : ℕ)]! = (j : ℕ) := by
    rw [← decode_apply h i, Fin.val_inj]
  simp only [Pmat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, pmatA, Matrix.of_apply, e]

theorem letterArr_perm (l : ℕ) : PermArr (letterArr l) = true := by
  unfold letterArr
  split_ifs
  · exact centGenArr_perm 0 (by norm_num) _ (getD_mem_of_lt (by decide) _)
  · exact centGenArr_perm 0 (by norm_num) _ (getD_mem_of_lt (by decide) _)

theorem decode_letterArr (l : ℕ) : decode (letterArr l) = xiLetter l := by
  unfold letterArr xiLetter
  split_ifs
  · exact centGen_zero_zero
  · exact centGen_zero_one

theorem wordArr_perm (w : List ℕ) : PermArr (wordArr w) = true := by
  induction w with
  | nil => exact PermArr_idArr
  | cons a w ih => exact PermArr_amul ih (letterArr_perm a)

theorem decode_wordArr (w : List ℕ) : decode (wordArr w) = xiWordPerm w := by
  induction w with
  | nil => rw [wordArr, decode_idArr, xiWordPerm, List.map_nil, List.reverse_nil, List.prod_nil]
  | cons a w ih =>
    rw [wordArr, decode_amul (wordArr_perm w) (letterArr_perm a), ih, decode_letterArr]
    simp [xiWordPerm]

theorem xiEdge_arr_check : ∀ e ∈ xiEdges,
    mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) :=
  Certificates.certificate3020.1

theorem xiEdge_matrix_check {e : XiEdge} (he : e ∈ xiEdges) :
    (dsgn (monoSign.getD e.source 0) * pmatA (seedA (monoSeed.getD e.source 0))) *
      (dsgn e.conjSign * Pmat (xiWordPerm e.word) * gXi) =
    (dsgn e.conjSign * Pmat (xiWordPerm e.word) * gXi) *
      (dsgn e.afterSign * pmatA e.afterPerm) := by
  have := congrArg toMat (xiEdge_arr_check e he)
  rw [← decode_wordArr, Pmat_decode (wordArr_perm _)]
  simpa only [xiArrA, xiArrM, xiArrR, toMat_mulArr, toMat_ofMat] using this

theorem xiEdge_code_check :
    ∀ e ∈ xiEdges, bvec 24 e.conjSign ∈ C ∧ bvec 24 e.afterSign ∈ C :=
  Certificates.certificate3020.2.1

theorem xiEdge_aut_check :
    ∀ e ∈ xiEdges, AutArr e.afterPerm ∧ AutArr e.normalizer :=
  Certificates.certificate3020.2.2.1

theorem xiEdge_seed_check : ∀ e ∈ xiEdges, e.target < 7 ∧
    amul (amul e.normalizer e.afterPerm) (ainv e.normalizer) =
      seedA (monoSeed.getD e.target 0) :=
  Certificates.certificate3020.2.2.2.1

theorem xiEdge_spec_check : ∀ e ∈ xiEdges,
    bvec 24 (permI e.afterPerm e.afterSign) = bvec 24 e.afterSign ∘ arrFun (ainv e.afterPerm) ∧
    bvec 24 (permI e.normalizer (permI e.afterPerm e.afterSign)) =
      bvec 24 (permI e.afterPerm e.afterSign) ∘ arrFun (ainv e.normalizer) :=
  Certificates.certificate3020.2.2.2.2.1

theorem xiEdge_target_mem : ∀ e ∈ xiEdges,
    canI (permI e.normalizer (permI e.afterPerm e.afterSign)) ∈ (monoCert e.target).pts.toList :=
  Certificates.certificate3020.2.2.2.2.2

theorem xiEdges_eq : xiEdges.map (fun e => (e.source, e.target)) = [(1, 3), (2, 5), (2, 4)] := by
  rfl

open _root_.Classical in
@[expose] def codeO (d : ℕ) : latticeO := if h : bvec 24 d ∈ C then gO ⟨bvec 24 d, h⟩ else 1

theorem codeO_of_mem {d : ℕ} (h : bvec 24 d ∈ C) : codeO d = gO ⟨bvec 24 d, h⟩ := by
  unfold codeO
  simp only [h, ↓reduceDIte]

theorem mat_codeO {d : ℕ} (h : bvec 24 d ∈ C) : mat (codeO d) = dsgn d := by
  rw [codeO_of_mem h, mat_gO, gmat, diagonal_sgn_bvec]

open _root_.Classical in
@[expose] def permO (p : Equiv.Perm (Fin 24)) : latticeO :=
  if h : p ∈ AutPerm then PO ⟨p, h⟩ else 1

theorem permO_of_mem {p : Equiv.Perm (Fin 24)} (h : p ∈ AutPerm) : permO p = PO ⟨p, h⟩ := by
  unfold permO
  simp only [h, ↓reduceDIte]

theorem mat_permO {p : Equiv.Perm (Fin 24)} (h : p ∈ AutPerm) : mat (permO p) = Pmat p := by
  rw [permO_of_mem h, mat_PO]

theorem xiLetter_mem (l : ℕ) : xiLetter l ∈ AutPerm := by
  rw [← decode_letterArr]
  exact decode_centGenArrs_mem (by norm_num) (getD_mem_of_lt (by split_ifs <;> decide) _)

theorem xiWordPerm_mem (w : List ℕ) : xiWordPerm w ∈ AutPerm := by
  rw [← decode_wordArr]
  induction w with
  | nil =>
    rw [wordArr, decode_idArr]
    exact AutPerm.one_mem
  | cons a w ih =>
    rw [wordArr, decode_amul (wordArr_perm w) (letterArr_perm a), decode_letterArr]
    exact AutPerm.mul_mem ih (xiLetter_mem a)

@[expose] def xiConjO (e : XiEdge) : latticeO :=
  codeO e.conjSign * permO (xiWordPerm e.word) * xiO

@[expose] def xiAfterO (e : XiEdge) : latticeO := codeO e.afterSign * permO (decode e.afterPerm)

theorem mat_monoAO_eq
    (i : ℕ) :
    mat (monoAO i) = dsgn (monoSign.getD i 0) * pmatA (seedA (monoSeed.getD i 0)) := by
  rw [mat_monoAO, monoA, monoWord, diagonal_sgn_bvec, ← decode_seedA,
    Pmat_decode ((seedHyp (monoSeed_lt i)).perm)]

theorem afterPerm_mem {e : XiEdge} (he : e ∈ xiEdges) : decode
    e.afterPerm ∈ AutPerm :=
  mem_AutPerm_of_arr (xiEdges_perm e he).1 (xiEdge_aut_check e he).1

theorem normalizer_mem {e : XiEdge} (he : e ∈ xiEdges) : decode
    e.normalizer ∈ AutPerm :=
  mem_AutPerm_of_arr (xiEdges_perm e he).2 (xiEdge_aut_check e he).2

theorem xiConjO_conj
    {e : XiEdge} (he : e ∈ xiEdges) :
    (xiConjO e)⁻¹ * monoAO e.source * xiConjO e = xiAfterO e := by
  have hm : monoAO e.source * xiConjO e = xiConjO e * xiAfterO e := by
    apply mat_injective
    simp only [mat_mul, xiConjO, xiAfterO]
    rw [mat_codeO (xiEdge_code_check e he).1, mat_permO (xiWordPerm_mem _),
      mat_codeO (xiEdge_code_check e he).2, mat_permO (afterPerm_mem he), mat_monoAO_eq,
      Pmat_decode (xiEdges_perm e he).1]
    exact xiEdge_matrix_check he
  rw [mul_assoc, hm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem modTwoUnit_mem_OLvis (g : latticeO) : modTwoUnit g ∈ OLvis :=
  mem_OLvis.2 ⟨g, rfl⟩

theorem monoHom_mem_OLvis (y : MonoSD)
    : monoHom y ∈ OLvis := by
  rw [← Hvis_eq_OLvis]
  apply Nvis_le_Hvis
  rw [Nvis_eq_range_monoHom]
  exact ⟨y, rfl⟩

theorem xiEdge_fusion
    {e : XiEdge} (he : e ∈ xiEdges) :
    ∃ w ∈ OLvis, w * monoN e.source * w⁻¹ = monoN e.target := by
  obtain ⟨ht7, hseed⟩ := xiEdge_seed_check e he
  obtain ⟨hsp1, hsp2⟩ := xiEdge_spec_check e he
  have hpq := (xiEdges_perm e he).1
  have hpc := (xiEdges_perm e he).2
  set q : AutPerm := ⟨decode e.afterPerm, afterPerm_mem he⟩
  set c : AutPerm := ⟨decode e.normalizer, normalizer_mem he⟩
  have hsC := (xiEdge_code_check e he).2
  have h1C := mem_C_permI hpq (afterPerm_mem he) hsC hsp1
  have h2C := mem_C_permI hpc (normalizer_mem he) h1C hsp2
  have hR : modTwoUnit (xiAfterO e) =
      monoHom ⟨Multiplicative.ofAdd (codeCls (permI e.afterPerm e.afterSign)), q⟩ := by
    rw [xiAfterO, codeO_of_mem hsC, permO_of_mem (afterPerm_mem he), gO_mul_PO, ← monoHom_mk,
      codeCls_permQ (p := q) hpq rfl hsC hsp1, codeCls_of_mem hsC, permQ_mk]
  have hcq : c * q * c⁻¹ = seedAut (monoSeed.getD e.target 0) := by
    apply Subtype.ext
    have h := congrArg decode hseed
    rw [decode_amul (PermArr_amul hpc hpq) (PermArr_ainv hpc), decode_amul hpc hpq,
      decode_ainv hpc] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_seedAut_eq (monoSeed_lt _)]
    exact h
  have hc : (SemidirectProduct.inr c : MonoSD) *
      ⟨Multiplicative.ofAdd (codeCls (permI e.afterPerm e.afterSign)), q⟩ *
      (SemidirectProduct.inr c)⁻¹ =
      fibPt (monoSeed.getD e.target 0)
        (canI (permI e.normalizer (permI e.afterPerm e.afterSign))) := by
    rw [inr_conj, hcq, fibPt, codeCls_canI h2C, codeCls_permQ (p := c) hpc rfl h1C hsp2]
  obtain ⟨g, hg, hgt⟩ := (mem_conjOrbit_iff ht7).2 ⟨_, xiEdge_target_mem e he, rfl⟩
  have hfinal : monoHom g * monoN e.target * (monoHom g)⁻¹ =
      monoHom (SemidirectProduct.inr c) * (modTwoUnit (xiConjO e) * monoN e.source *
        (modTwoUnit (xiConjO e))⁻¹) * (monoHom (SemidirectProduct.inr c))⁻¹ := by
    have e1 : modTwoUnit (xiConjO e) * monoN e.source * (modTwoUnit (xiConjO e))⁻¹ =
        modTwoUnit (xiAfterO e) := by
      rw [← xiConjO_conj he, monoN, modTwoUnit_mul, modTwoUnit_mul, modTwoUnit_inv, mul_assoc]
    rw [e1, hR, monoN_eq ht7, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
      hc, hgt]
  refine ⟨(monoHom g)⁻¹ * monoHom (SemidirectProduct.inr c) * modTwoUnit (xiConjO e),
    OLvis.mul_mem (OLvis.mul_mem (OLvis.inv_mem (monoHom_mem_OLvis g)) (monoHom_mem_OLvis _))
      (modTwoUnit_mem_OLvis _), ?_⟩
  have : monoN e.target = (monoHom g)⁻¹ * (monoHom (SemidirectProduct.inr c) *
      (modTwoUnit (xiConjO e) * monoN e.source * (modTwoUnit (xiConjO e))⁻¹) *
      (monoHom (SemidirectProduct.inr c))⁻¹) * monoHom g := by
    rw [← hfinal]
    group
  rw [this]
  group

end CFSG.Monster.B.TwoA.Census
