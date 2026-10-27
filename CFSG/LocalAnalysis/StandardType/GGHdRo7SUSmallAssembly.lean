module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallAssemblyAux

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem smLin_of_leaves : SUNormalizerLeaf → SMRulesLeaf → SMClassSetLeaf → SMModelsBDLeaf → SMModelsALeaf → SMModelsELeaf → SMConjLeaf → (∀
    (m : ℕ), (m = 7 ∨ m = 8) → ∀ (H : Subgroup (SMGL m)), (∀ g, SMIsPerm g → g ∈ H) →
    QTwoLin.TransvectionFree H → (∀ g ∈ H, g (smOnes m) = smOnes m → ∀ s, SMIsPerm s → SMIsPerm (g *
    s * g⁻¹)) → (∃ S : Set (SMGL m), H = Subgroup.closure S ∧ (∀ r ∈ S, ∃ (u : SMV m) (φ :
    Module.Dual (ZMod 3) (SMV m)), SMRefl r u φ) ∧ ∀ r ∈ S, ∀ t ∈ S, Relation.ReflTransGen (fun a b
    => a ∈ S ∧ b ∈ S ∧ ¬ Commute a b) r t) → ZS.LinWeyl 3 H) := by
  intro hN hR hC hBD hA hE hCj
  intro m hm H hP hT hS hgen
  obtain ⟨S, hS_eq, hS_refl, hS_conn⟩ := hgen
  have hRcl : SMRCl (smRefSet H) := hR hN m hm H hP hT hS
  rcases hm with rfl | rfl
  · obtain ⟨X, hXmem, hXeq⟩ := hC.1 (smRefSet H) hRcl
    by_cases hcx : X = [sm7cx]
    · subst hcx
      exfalso
      have hXeq' : ∀ p : SMV 7 × SMV 7, p ∈ smRefSet H ↔ (SMTClass p ∨ SMClass p sm7cx) := by
        intro p
        rw [hXeq p]
        constructor
        · rintro (h | ⟨q, hq, hpq⟩)
          · exact Or.inl h
          · simp at hq; subst hq; exact Or.inr hpq
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨sm7cx, by simp, h⟩
      have hpart : ∀ s ∈ S, SMIsPerm s ∨ SMRefl s sm7cx.1 (smDual sm7cx.2) := by
        intro s hs
        obtain ⟨u, φ, hrefl⟩ := hS_refl s hs
        set w : SMV 7 := fun i => φ (Pi.single i (1 : ZMod 3)) with hw
        have hφ : smDual w = φ := hdRo7SmAsmAux_dual_eq φ
        have hrefl' : SMRefl s u (smDual w) := by rw [hφ]; exact hrefl
        have hsH : s ∈ H := by rw [hS_eq]; exact Subgroup.subset_closure hs
        have hpR : (u, w) ∈ smRefSet H := ⟨s, hsH, hrefl'⟩
        rcases (hXeq' (u, w)).mp hpR with hT' | hC'
        · exact Or.inl (hdRo7SmAsmAux_transp_isPerm hT' hrefl')
        · exact Or.inr (hdRo7SmAsmAux_cx7_class_refl hrefl' hC')
      have hcxR : ∃ r0 ∈ H, SMRefl r0 sm7cx.1 (smDual sm7cx.2) := by
        refine (hXeq' sm7cx).mpr (Or.inr ?_)
        exact ⟨1, 1, Or.inl rfl, by intro i; simp⟩
      exact hdRo7SmAsmAux_cx_contra hP hS_eq hS_conn hpart
        (fun s hrefl => hdRo7SmAsmAux_cx7_not_perm hrefl)
        (fun s hrefl g hg => by
          obtain ⟨σ, rfl⟩ := hdRo7SmAsmAux_isPerm_eq_permLin hg
          exact hdRo7SmAsmAux_cx7_comm_perm hrefl σ)
        hdRo7SmAsmAux_cx7_swap_perm
        hdRo7SmAsmAux_cx7_swap_ne_one
        (fun h => hdRo7SmAsmAux_cx7_not_perm h hdRo7SmAsmAux_cx7_swap_perm)
        hcxR
    · have hHX : H = smGroup 7 X := hdRo7SmAsmAux_eq_smGroup hP hXeq hS_eq hS_refl
      rw [hHX]
      exact (hCj hBD hA hE).1 X hXmem hcx
  · obtain ⟨X, hXmem, hXeq⟩ := hC.2 (smRefSet H) hRcl
    by_cases hcx : X = [sm8cx]
    · subst hcx
      exfalso
      have hXeq' : ∀ p : SMV 8 × SMV 8, p ∈ smRefSet H ↔ (SMTClass p ∨ SMClass p sm8cx) := by
        intro p
        rw [hXeq p]
        constructor
        · rintro (h | ⟨q, hq, hpq⟩)
          · exact Or.inl h
          · simp at hq; subst hq; exact Or.inr hpq
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨sm8cx, by simp, h⟩
      have hpart : ∀ s ∈ S, SMIsPerm s ∨ SMRefl s sm8cx.1 (smDual sm8cx.2) := by
        intro s hs
        obtain ⟨u, φ, hrefl⟩ := hS_refl s hs
        set w : SMV 8 := fun i => φ (Pi.single i (1 : ZMod 3)) with hw
        have hφ : smDual w = φ := hdRo7SmAsmAux_dual_eq φ
        have hrefl' : SMRefl s u (smDual w) := by rw [hφ]; exact hrefl
        have hsH : s ∈ H := by rw [hS_eq]; exact Subgroup.subset_closure hs
        have hpR : (u, w) ∈ smRefSet H := ⟨s, hsH, hrefl'⟩
        rcases (hXeq' (u, w)).mp hpR with hT' | hC'
        · exact Or.inl (hdRo7SmAsmAux_transp_isPerm hT' hrefl')
        · exact Or.inr (hdRo7SmAsmAux_cx8_class_refl hrefl' hC')
      have hcxR : ∃ r0 ∈ H, SMRefl r0 sm8cx.1 (smDual sm8cx.2) := by
        refine (hXeq' sm8cx).mpr (Or.inr ?_)
        exact ⟨1, 1, Or.inl rfl, by intro i; simp⟩
      exact hdRo7SmAsmAux_cx_contra hP hS_eq hS_conn hpart
        (fun s hrefl => hdRo7SmAsmAux_cx8_not_perm hrefl)
        (fun s hrefl g hg => by
          obtain ⟨σ, rfl⟩ := hdRo7SmAsmAux_isPerm_eq_permLin hg
          exact hdRo7SmAsmAux_cx8_comm_perm hrefl σ)
        hdRo7SmAsmAux_cx8_swap_perm
        hdRo7SmAsmAux_cx8_swap_ne_one
        (fun h => hdRo7SmAsmAux_cx8_not_perm h hdRo7SmAsmAux_cx8_swap_perm)
        hcxR
    · have hHX : H = smGroup 8 X := hdRo7SmAsmAux_eq_smGroup hP hXeq hS_eq hS_refl
      rw [hHX]
      exact (hCj hBD hA hE).2 X hXmem hcx

end CFSG.StandardType.HdRo7SU.Small
