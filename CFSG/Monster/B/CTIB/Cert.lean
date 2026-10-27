module

public import CFSG.Monster.B.TwoA.Census.NatCert
public import Certificates.Data.CFSGNative.CTIB.Arith

public section

namespace CFSG.Monster.B.CTIB

open CFSG.Monster.B.TwoA.Census

theorem chainLt_isChain : ∀ l : List ℕ, Native.chainLt l = true ↔ l.IsChain (· < ·)
  | [] => by simp [Native.chainLt]
  | [a] => by simp [Native.chainLt]
  | a :: b :: t => by
    rw [Native.chainLt, Bool.and_eq_true, decide_eq_true_iff, chainLt_isChain (b :: t),
      List.isChain_cons_cons]

theorem chainLt_iff (l : List ℕ) : Native.chainLt l = true ↔ l.Pairwise (· < ·) :=
  (chainLt_isChain l).trans List.isChain_iff_pairwise

theorem natCertOK_census {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root : ℕ}
    {pts : Array ℕ} {edges : Array (Array ℕ)} {par lab : Array ℕ}
    (h : Native.natCertOK act ngen valid root pts edges par lab = true) :
    natCertOK act ngen valid root ⟨pts, edges, par, lab⟩ = true := by
  simp only [Native.natCertOK, Bool.and_eq_true] at h
  simp only [natCertOK, Bool.and_eq_true]
  refine ⟨⟨h.1.1, ?_⟩, decide_eq_true ((chainLt_iff _).1 h.2)⟩
  rw [List.all_eq_true] at h ⊢
  intro i hi
  have := h.1.2 i hi
  simpa [natPointOK, Native.natPointOK] using this

section Action

variable {G X : Type*} [Group G] [MulAction G X] {act : ℕ → ℕ → ℕ} {ngen : ℕ}
  {valid : ℕ → Bool} {root size : ℕ} {dec : ℕ → X} {gens : ℕ → G}

theorem orbit_of_nativeCert {pts : Array ℕ} {edges : Array (Array ℕ)} {par lab : Array ℕ}
    (h : Native.natCertOK act ngen valid root pts edges par lab = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    (hinj : ∀ a b, valid a = true → valid b = true → dec a = dec b → a = b) :
    MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root) =
        (fun i => dec pts[i]!) '' {i | i < pts.size} ∧
      (MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root)).ncard =
        pts.size ∧
      valid root = true ∧ ∀ i < pts.size, valid pts[i]! = true := by
  have hc := natCertOK_census h
  refine ⟨orbit_of_natCertOK hc hact, ncard_orbit_of_natCertOK hc hact hinj, ?_,
    fun i hi => natCertOK_valid hc hi⟩
  have h0 := natCertOK_valid hc (natCertOK_pos hc)
  rwa [natCertOK_root hc] at h0

theorem orbitOK_parts (h : Native.orbitOK act ngen valid root size = true) :
    natCertOK act ngen valid root ⟨(Native.natBfs act ngen root (size + 1)).1,
      (Native.natBfs act ngen root (size + 1)).2.1,
      (Native.natBfs act ngen root (size + 1)).2.2.1,
      (Native.natBfs act ngen root (size + 1)).2.2.2⟩ = true ∧
    (Native.natBfs act ngen root (size + 1)).1.size = size ∧
    ∀ i < (Native.natBfs act ngen root (size + 1)).1.size,
      root ≤ (Native.natBfs act ngen root (size + 1)).1[i]! := by
  simp only [Native.orbitOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
    at h
  refine ⟨natCertOK_census h.1.1, h.1.2, fun i hi => ?_⟩
  rw [getElem!_pos _ i hi]
  exact h.2 i hi

theorem orbit_of_orbitOK (h : Native.orbitOK act ngen valid root size = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    (hinj : ∀ a b, valid a = true → valid b = true → dec a = dec b → a = b) :
    ∃ pts : Array ℕ, pts.size = size ∧ (∀ i < size, valid pts[i]! = true ∧ root ≤ pts[i]!) ∧
      MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root) =
        (fun i => dec pts[i]!) '' {i | i < size} ∧
      (MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root)).ncard = size ∧
      valid root = true := by
  obtain ⟨hc, hs, hr⟩ := orbitOK_parts h
  refine ⟨(Native.natBfs act ngen root (size + 1)).1, hs,
    fun i hi => ⟨?_, hr i (by rw [hs]; exact hi)⟩, ?_, ?_, ?_⟩
  · exact natCertOK_valid hc
      (by show i < (Native.natBfs act ngen root (size + 1)).1.size; rw [hs]; exact hi)
  · rw [orbit_of_natCertOK hc hact]
    show (fun i => dec (Native.natBfs act ngen root (size + 1)).1[i]!) ''
        {i | i < (Native.natBfs act ngen root (size + 1)).1.size} = _
    rw [hs]
  · rw [ncard_orbit_of_natCertOK hc hact hinj]
    exact hs
  · have h0 := natCertOK_valid hc (natCertOK_pos hc)
    rwa [natCertOK_root hc] at h0

end Action

end CFSG.Monster.B.CTIB
