module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSem

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pwk_foldl_range_map (p D : ℕ) (F : ℕ → ℕ) :
    ((((List.range D).map F).foldl (· + ·) 0 : ℕ) : ZMod p)
      = ∑ i : Fin D, (F i.val : ZMod p) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [Nat.cast_add, ih, Fin.sum_univ_castSucc]
      simp

private lemma pwk_dotv_cast (P : Pt) (f v : Vec) :
    ((P.dotv f v : ℕ) : ZMod P.p) = P.dot (P.vec f) (P.vec v) := by
  simp only [Pt.dotv]
  rw [ZMod.natCast_mod, pwk_foldl_range_map]
  simp only [Pt.dot, Pt.vec, Nat.cast_mul]

private lemma pwk_ent_cast (P : Pt) (v : Vec) (i : Fin P.D) :
    ((P.ent v i.val : ℕ) : ZMod P.p) = P.vec v i := by
  simp only [Pt.vec, Pt.ent, ZMod.natCast_mod]

private lemma pwk_ent_cast' (P : Pt) (v : Vec) (j : ℕ) (hj : j < P.D) :
    ((P.ent v j : ℕ) : ZMod P.p) = P.vec v ⟨j, hj⟩ :=
  pwk_ent_cast P v ⟨j, hj⟩

theorem wfCheck_sound {P : Pt} (h : wfCheck P = true) : P.WF := by
  have key : ∀ r ∈ P.gens, P.dot (P.vec r.f) (P.vec r.h) = 2 := by
    intro r hr
    have h1 : (P.gens.all (fun r => P.dotv r.f r.h == 2 % P.p)) = true := by
      simpa only [wfCheck] using h
    have h' : P.dotv r.f r.h = 2 % P.p := by
      have := (List.all_eq_true.mp h1) r hr
      simpa using this
    rw [← pwk_dotv_cast P r.f r.h, h']
    simp [ZMod.natCast_mod]
  exact key

theorem verifyK_sound {P : Pt} {w : Vec} (h : verifyK P w = true) : P.FrameViolation := by
  simp only [verifyK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [List.all_eq_true] at h1
  rw [List.any_eq_true] at h2
  obtain ⟨i, hi, h2⟩ := h2
  rw [List.any_eq_true] at h2
  obtain ⟨j, hj, h2⟩ := h2
  have h2ne : (P.ent w i * P.ent P.x j) % P.p ≠ (P.ent w j * P.ent P.x i) % P.p := by
    simpa using h2
  refine ⟨P.vec w, ?_, ?_⟩
  · intro r hr
    have h1r := h1 r hr
    rw [beq_iff_eq] at h1r
    rw [← pwk_dotv_cast P r.f w, h1r]
    simp
  · intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hi' : i < P.D := List.mem_range.mp hi
    have hj' : j < P.D := List.mem_range.mp hj
    apply h2ne
    have hZmod : ((P.ent w i * P.ent P.x j : ℕ) : ZMod P.p)
        = ((P.ent w j * P.ent P.x i : ℕ) : ZMod P.p) := by
      rw [Nat.cast_mul, Nat.cast_mul,
        pwk_ent_cast' P w i hi', pwk_ent_cast' P w j hj',
        pwk_ent_cast' P P.x i hi', pwk_ent_cast' P P.x j hj']
      rw [← ha]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hZmod

end CFSG.TwoNodeSmall
