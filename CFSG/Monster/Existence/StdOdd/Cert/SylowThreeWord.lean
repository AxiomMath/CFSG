module

public import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.LieType.Chevalley.C2E6StandardFixedTorus
public import CFSG.LieType.Chevalley.EvenDiagramRootParameters
public import CFSG.Monster.B.Classical.E6AdjointGroup
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
public import Certificates.Certificate16038

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Monster.B.Classical.E6Adjoint

@[expose] noncomputable def letterElt
    (l : Letter) : ModGL Tag.E6 K :=
  pinnedX Tag.E6 K (e6Certificate.root l.1) (ofBits l.2.1 l.2.2)

@[expose] noncomputable def wordElt
    (w : List Letter) : ModGL Tag.E6 K := (w.map letterElt).prod

theorem wordElt_nil :
    wordElt [] = 1 := rfl

theorem wordElt_cons
    (l : Letter) (w : List Letter) :
    wordElt (l :: w) = letterElt l * wordElt w := by
  simp [wordElt]

theorem wordElt_append
    (u v : List Letter) : wordElt (u ++ v) = wordElt u * wordElt v := by
  simp [wordElt]

theorem wordElt_singleton
    (l : Letter) : wordElt [l] = letterElt l := by
  simp [wordElt]

theorem letterElt_mul_self
    (l : Letter) : letterElt l * letterElt l = 1 := by
  unfold letterElt
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem letterElt_inv
    (l : Letter) : (letterElt l)⁻¹ = letterElt l :=
  inv_eq_of_mul_eq_one_right (letterElt_mul_self l)

theorem wordElt_reverse
    (w : List Letter) : wordElt w.reverse = (wordElt w)⁻¹ := by
  induction w with
  | nil => simp [wordElt_nil]
  | cons l w ih =>
    rw [List.reverse_cons, wordElt_append, ih, wordElt_singleton, wordElt_cons, mul_inv_rev,
      letterElt_inv]

theorem rootVec_cert (j : ℕ) (hj : j < 72) :
    rootVec Tag.E6 K (e6Certificate.root j) = Finsupp.single (lab ⟨6 + j, by omega⟩) 1 := by
  rw [CFSG.Monster.B.Classical.E6Adjoint.rootVec_eq_single (isRoot_certRoot hj),
    lab_of_ge (by simp only [not_lt]; omega)]
  congr 3
  simp

theorem glMat_letterElt
    (l : Letter) (hl : l.1 < 72) :
    glMat (letterElt l) = toMat (CFSG.Monster.Existence.StdOdd.CertNative.letterMat
      CFSG.Monster.B.Classical.E6Adjoint.bracketCodes CFSG.Monster.B.Classical.E6Adjoint.formBits
      l) := by
  obtain ⟨j, c0, c1⟩ := l
  have hj : j < 72 := hl
  rw [glMat_apply]
  show matOf ((pinnedX Tag.E6 K (e6Certificate.root j) (ofBits c0 c1) :
    ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) = _
  rw [pinnedX_eq (isRoot_certRoot hj), rootVec_cert j hj]
  exact matOf_rootOp ⟨6 + j, by omega⟩ c0 c1

theorem toMat_wordMat_foldl
    (w : List Letter) (hw : ∀ l ∈ w, l.1 < 72) (acc : Native.Mat) :
    toMat (w.foldl (fun acc l => Native.mul acc (CFSG.Monster.Existence.StdOdd.CertNative.letterMat
      bracketCodes formBits l)) acc) = toMat acc * glMat (wordElt w) := by
  induction w generalizing acc with
  | nil => simp [wordElt_nil]
  | cons l w ih =>
    rw [List.foldl_cons, ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')), toMat_mul,
      ← glMat_letterElt l (hw l List.mem_cons_self), wordElt_cons, map_mul, mul_assoc]

theorem glMat_wordElt
    (w : List Letter) (hw : ∀ l ∈ w, l.1 < 72) :
    glMat (wordElt w) = toMat (CFSG.Monster.Existence.StdOdd.CertNative.wordMat bracketCodes
      formBits w) := by
  rw [CFSG.Monster.Existence.StdOdd.CertNative.wordMat, toMat_wordMat_foldl w hw, toMat_one,
    one_mul]

theorem permLattice_cert_aux : ∀ j < 72,
    List.ofFn (permLattice TwistTag.E6.perm (e6Certificate.root j)) =
    List.ofFn (e6Certificate.root (gamTable.getD j 0)) :=
  Certificates.certificate16038.1

theorem permLattice_cert (j : ℕ) (hj : j < 72) :
    permLattice TwistTag.E6.perm (e6Certificate.root j) =
      e6Certificate.root (gamTable.getD j 0) :=
  List.ofFn_injective (permLattice_cert_aux j hj)

theorem gamTable_lt : ∀ j < 72, gamTable.getD j 0 < 72 :=
  Certificates.certificate16038.2

theorem barHom_ofBits (c0 c1 : Bool) : barHom (ofBits c0 c1) = ofBits (xor c0 c1) c1 := by
  rw [barHom_apply, bar, ofBits_sq]

@[expose] noncomputable def twistF : ModGL Tag.E6 K →* ModGL Tag.E6 K :=
  twistHom TwistTag.E6 K barHom

theorem twistF_letterElt
    (l : Letter) (hl : l.1 < 72) :
    twistF (letterElt l) =
      letterElt (CFSG.Monster.Existence.StdOdd.CertNative.twistLetter gamTable l) := by
  obtain ⟨j, c0, c1⟩ := l
  have hj : j < 72 := hl
  have h := even_diagram_root_parameters TwistTag.E6 barHom (isRoot_certRoot hj) (ofBits c0 c1)
  rw [permLattice_cert j hj, barHom_ofBits] at h
  exact h

theorem wordElt_mem_adjointGroup
    (w : List Letter) : wordElt w ∈ adjointGroup Tag.E6 K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
    exact pinnedX_mem_adjointGroup _ _

theorem twistF_wordElt
    (w : List Letter) (hw : ∀ l ∈ w, l.1 < 72) :
    twistF (wordElt w) =
      wordElt (w.map (CFSG.Monster.Existence.StdOdd.CertNative.twistLetter gamTable)) := by
  induction w with
  | nil => simp [wordElt_nil]
  | cons l w ih =>
    rw [wordElt_cons, map_mul, twistF_letterElt l (hw l List.mem_cons_self),
      ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')), List.map_cons, wordElt_cons]

theorem wordElt_mem_stdGroup
    (w : List Letter) (hw : ∀ l ∈ w, l.1 < 72)
    (hf : Native.eqM (CFSG.Monster.Existence.StdOdd.CertNative.wordMat bracketCodes formBits
      (w.map (CFSG.Monster.Existence.StdOdd.CertNative.twistLetter gamTable)))
      (CFSG.Monster.Existence.StdOdd.CertNative.wordMat bracketCodes formBits w) = true) :
    wordElt w ∈ stdGroup := by
  rw [← stdFixedGroup_eq_stdGroup]
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2
    ⟨wordElt_mem_adjointGroup w, ?_⟩
  show twistF (wordElt w) = wordElt w
  have hw' : ∀ l ∈ w.map (CFSG.Monster.Existence.StdOdd.CertNative.twistLetter gamTable),
      l.1 < 72 := by
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact gamTable_lt l'.1 (hw l' hl')
  rw [twistF_wordElt w hw]
  refine glMat_injective ?_
  rw [glMat_wordElt _ hw', glMat_wordElt w hw]
  exact toMat_eq_of_eqM hf

end CFSG.Monster.Existence.StdOdd.Cert
