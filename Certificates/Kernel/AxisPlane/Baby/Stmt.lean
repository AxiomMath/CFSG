module

public import Certificates.Kernel.AxisPlane.Baby.WordsOf
public import CFSG.Certificates.Kernel.AxisPlane.Glue

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.Monster.AxisCount.Baby CFSG.KC.AxisPlane

theorem planesOK_list {opss rls : List (List Nat)} {Ls Qs : List Nat} {Rss : List (List Nat)}
    {lams sizes : List Nat} (C : PlanesChk opss rls Ls Qs Rss lams sizes)
    (hm : opss.length = rls.length) :
    PlanesOK (rls.map List.toArray).toArray opss rls Ls Qs Rss lams sizes := by
  refine ⟨C, by simp [hm], fun g hg => ?_⟩
  have hg' : g < rls.length := by simpa using hg
  simp [getElem!_pos, hg', List.getD_eq_getElem?_getD]

theorem getElem!_eq_getD (a : Array ℕ) {r : ℕ} (hr : r < a.size) : a[r]! = a.toList.getD r 0 := by
  simp [getElem!_pos, hr, List.getD_eq_getElem?_getD]

theorem stmt_of {o : BabyOrbit} {rs : List (List Nat)} {opss Rss : List (List Nat)}
    {Ls Qs lams sizes : List Nat}
    (hw : rowsB o = (rs.map List.toArray).toArray ∧ wordsB o = true)
    (C : PlanesChk opss rs Ls Qs Rss lams sizes) (hm : opss.length = rs.length)
    (hl : o.lam.toList = lams) (hs : o.size.toList = sizes) : BabyStmt o := by
  have H := planesOK_list C hm
  rw [← hw.1] at H
  have hsz : o.lam.size = lams.length := by rw [← hl, Array.length_toList]
  have hsz' : o.lam.size = o.size.size := by
    have h := hw.2
    simp only [wordsB, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.2
  refine ⟨hw.2, fun r hr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := orbits_of_planesOK H (r := r) (by omega)
  rw [getElem!_eq_getD _ hr, hl]
  refine ⟨h1, ?_, fun r' hr' hne => ?_⟩
  · rw [h2, getElem!_eq_getD _ (by omega), hs]
  · rw [getElem!_eq_getD _ hr', hl]
    exact h3 r' (by omega) hne

end CertificateChecks.KernelAP.Baby

end
