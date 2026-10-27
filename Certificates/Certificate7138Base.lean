
module

public import CFSG.Certificates.Kernel.Sp4OvNodes
public import Certificates.Kernel.Sp4Ov.Checks
public import Certificates.Kernel.Sp4Ov.LinesChecks
public import Certificates.Kernel.Sp4Ov.SpecChecks

@[expose] public section

namespace CertificateChecks.Batch7138

open CFSG.Quasithin.H13 Sp4Cert CFSG.KD.Sp4Ov

theorem any_toNode {L : List NodeR} {g : List ℕ} (h : ((getN L 0).gens == g) = true)
    (hg : g ≠ []) : (L.map toNode).any (fun s => s.gens == g.map dec) = true := by
  cases L with
  | nil => exact absurd (beq_iff_eq.mp h).symm hg
  | cons s L =>
    have hs : s.gens = g := beq_iff_eq.mp h
    have : (toNode s).gens = g.map dec := by rw [← hs]; rfl
    simp only [List.map_cons, List.any_cons, this, beq_self_eq_true, Bool.true_or]

theorem p9C_mask : p9C.2 = D.p9M := by decide +kernel

theorem p9C_maskOf : p9C.2 = maskOf p9C.1 := by decide +kernel

theorem p9C_length : p9C.1.length = 9 := by decide +kernel

noncomputable instance sp4Data : Sp4Data where
  ov5K := D.ov5.map toNode
  ov9K := D.ov9.map toNode
  specK := specOf D.spec D.a36L D.b36L D.s36L D.s120L
  node5 hΔ hP := by
    have hg := any_toNode ch7138_g5 (by simp)
    have h5 : [58242].map dec = [x5C] := rfl
    rw [h5] at hg
    exact exists_node_eq_ofK ch7138_elems ch7138_ov5 hg hΔ (by simpa using hP)
  node9 hΔ hP hP' := by
    have hg := any_toNode ch7138_g9 (by simp)
    have h9 : [34369, 37928].map dec = [a9C, b9C] := rfl
    rw [h9] at hg
    refine exists_node_eq_ofK ch7138_elems ch7138_ov9 hg hΔ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hP
    · exact hP'
  facts s hs := by
    rcases hs with hs | hs
    all_goals
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    · obtain ⟨h1, h2, -⟩ := nodeK_sound ch7138_elems ch7138_ov5 hs'
      exact ⟨h1, (toNode_facts ch7138_elems ch7138_ov5 hs).2.1, h2⟩
    · obtain ⟨h1, h2, -⟩ := nodeK_sound ch7138_elems ch7138_ov9 hs'
      exact ⟨h1, (toNode_facts ch7138_elems ch7138_ov9 hs).2.1, h2⟩
  line5 := lineK_sound ch7138_elems ch7138_ov5 ch7138_lines rfl ch7138_line5
  line9 := lineK_sound ch7138_elems ch7138_ov9 ch7138_lines rfl ch7138_line9
  quad5 := quadK_sound ch7138_elems ch7138_ov5 ch7138_lines rfl ch7138_quad5
  quad9 := quadK_sound ch7138_elems ch7138_ov9 ch7138_lines rfl ch7138_quad9
  special := specialK_sound ch7138_elems ch7138_special p9C_mask p9C_maskOf p9C_length

end CertificateChecks.Batch7138

