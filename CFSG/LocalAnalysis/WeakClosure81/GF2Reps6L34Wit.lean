module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import CFSG.Quasithin.Background.KG82CoverModel
public import CFSG.Quasithin.Background.KG82CoverCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.PSL3Four.Native
open CFSG.Quasithin.H.L34Cov

theorem tabRep_invWord (w : List ℕ) :
    TabRep (wordTab (invW w)) (wordPerm w)⁻¹ := by
  rw [← wordPerm_invW w]
  exact tabRep_wordTab _

theorem g₁_eq_word : g₁ = wordPerm [0] := rfl

theorem g₂_eq_word : g₂ = wordPerm [1] := rfl

theorem g₃_eq_word : g₃ = wordPerm [2] := rfl

theorem orderOf_eq_four_of_tab {g : Equiv.Perm (Fin 42)} {t : Tab} (h : TabRep t g)
    (h2 : (powTab 42 t 2 == idTab 42) = false)
    (h4 : (powTab 42 t 4 == idTab 42) = true) : orderOf g = 4 := by
  have hne : g ^ 2 ≠ 1 := by
    intro h1
    rw [((h.pow 2).beq_iff TabRep.idTab).2 h1] at h2
    exact Bool.noConfusion h2
  have h4' : g ^ 4 = 1 := ((h.pow 4).beq_iff TabRep.idTab).1 h4
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) hne h4'
  simpa using this

@[expose] def x₂ : Equiv.Perm (Fin 42) := wordPerm [2, 0, 2]

@[expose] def k₂ : Equiv.Perm (Fin 42) := wordPerm [2, 0, 1, 0, 0, 2]

@[expose] def k₂' : Equiv.Perm (Fin 42) := wordPerm [2, 0, 0, 1, 0, 2]

@[expose] def x₃ : Equiv.Perm (Fin 42) := wordPerm [1, 0, 1, 0, 0, 1]

@[expose] def k₃ : Equiv.Perm (Fin 42) := wordPerm [0, 1, 0, 1, 0, 1]

@[expose] def h₃ : Equiv.Perm (Fin 42) := wordPerm [2, 0, 2, 1, 0, 2, 0, 2, 1, 0, 0, 1]

private theorem tabRep_r₂_inv : TabRep r₂T r₂⁻¹ :=
  tabRep_r₂.inv tabRep_r₂.1 (by decide +kernel)

private theorem tabRep_r₃_inv : TabRep r₃T r₃⁻¹ :=
  tabRep_r₃.inv tabRep_r₃.1 (by decide +kernel)

private theorem tabRep_x₂ : TabRep (wordTab [2, 0, 2]) x₂ := tabRep_wordTab _

private theorem tabRep_x₂_inv : TabRep (wordTab (invW [2, 0, 2])) x₂⁻¹ := tabRep_invWord _

private theorem tabRep_k₂ : TabRep (wordTab [2, 0, 1, 0, 0, 2]) k₂ := tabRep_wordTab _

private theorem tabRep_k₂_inv :
    TabRep (wordTab (invW [2, 0, 1, 0, 0, 2])) k₂⁻¹ := tabRep_invWord _

private theorem tabRep_k₂' : TabRep (wordTab [2, 0, 0, 1, 0, 2]) k₂' := tabRep_wordTab _

private theorem tabRep_k₂'_inv :
    TabRep (wordTab (invW [2, 0, 0, 1, 0, 2])) k₂'⁻¹ := tabRep_invWord _

theorem tabRep_x₃ : TabRep (wordTab [1, 0, 1, 0, 0, 1]) x₃ := tabRep_wordTab _

theorem tabRep_x₃_inv : TabRep (wordTab (invW [1, 0, 1, 0, 0, 1])) x₃⁻¹ := tabRep_invWord _

theorem tabRep_k₃ : TabRep (wordTab [0, 1, 0, 1, 0, 1]) k₃ := tabRep_wordTab _

theorem tabRep_k₃_inv : TabRep (wordTab (invW [0, 1, 0, 1, 0, 1])) k₃⁻¹ := tabRep_invWord _

private theorem tabRep_h₃ :
    TabRep (wordTab [2, 0, 2, 1, 0, 2, 0, 2, 1, 0, 0, 1]) h₃ := tabRep_wordTab _

private theorem tabRep_r₂_x₂ : TabRep
    (comp 42 (comp 42 (comp 42 r₂T (wordTab [2, 0, 2])) r₂T)
      (wordTab (invW [2, 0, 2]))) (r₂ * x₂ * r₂⁻¹ * x₂⁻¹) :=
  ((tabRep_r₂.comp tabRep_x₂).comp tabRep_r₂_inv).comp tabRep_x₂_inv

private theorem tabRep_r₂_x₂_inv : TabRep
    (comp 42 (comp 42 (comp 42 r₂T (wordTab (invW [2, 0, 2]))) r₂T)
      (wordTab [2, 0, 2])) (r₂ * x₂⁻¹ * r₂⁻¹ * x₂) :=
  ((tabRep_r₂.comp tabRep_x₂_inv).comp tabRep_r₂_inv).comp tabRep_x₂

private theorem tabRep_r₃_x₃ : TabRep
    (comp 42 (comp 42 (comp 42 r₃T (wordTab [1, 0, 1, 0, 0, 1])) r₃T)
      (wordTab (invW [1, 0, 1, 0, 0, 1]))) (r₃ * x₃ * r₃⁻¹ * x₃⁻¹) :=
  ((tabRep_r₃.comp tabRep_x₃).comp tabRep_r₃_inv).comp tabRep_x₃_inv

theorem orderOf_r₂_x₂ : orderOf (r₂ * x₂ * r₂⁻¹ * x₂⁻¹) = 4 :=
  orderOf_eq_four_of_tab tabRep_r₂_x₂ (by decide +kernel) (by decide +kernel)

theorem orderOf_r₂_x₂_inv : orderOf (r₂ * x₂⁻¹ * r₂⁻¹ * x₂) = 4 :=
  orderOf_eq_four_of_tab tabRep_r₂_x₂_inv (by decide +kernel) (by decide +kernel)

theorem k₂_mul_inv :
    k₂ * (r₂ * k₂ * r₂⁻¹)⁻¹ = r₂ * (r₂ * x₂ * r₂⁻¹ * x₂⁻¹) ^ 2 * r₂⁻¹ := by
  have hAi : TabRep (comp 42 (comp 42 r₂T (wordTab (invW [2, 0, 1, 0, 0, 2]))) r₂T)
      (r₂ * k₂ * r₂⁻¹)⁻¹ := by
    rw [show (r₂ * k₂ * r₂⁻¹)⁻¹ = r₂ * k₂⁻¹ * r₂⁻¹ by group]
    exact (tabRep_r₂.comp tabRep_k₂_inv).comp tabRep_r₂_inv
  exact ((tabRep_k₂.comp hAi).beq_iff
    ((tabRep_r₂.comp (tabRep_r₂_x₂.pow 2)).comp tabRep_r₂_inv)).mp (by decide +kernel)

theorem k₂'_mul_inv :
    k₂' * (r₂ * k₂' * r₂⁻¹)⁻¹ = r₂ * (r₂ * x₂⁻¹ * r₂⁻¹ * x₂) ^ 2 * r₂⁻¹ := by
  have hAi : TabRep (comp 42 (comp 42 r₂T (wordTab (invW [2, 0, 0, 1, 0, 2]))) r₂T)
      (r₂ * k₂' * r₂⁻¹)⁻¹ := by
    rw [show (r₂ * k₂' * r₂⁻¹)⁻¹ = r₂ * k₂'⁻¹ * r₂⁻¹ by group]
    exact (tabRep_r₂.comp tabRep_k₂'_inv).comp tabRep_r₂_inv
  exact ((tabRep_k₂'.comp hAi).beq_iff
    ((tabRep_r₂.comp (tabRep_r₂_x₂_inv.pow 2)).comp tabRep_r₂_inv)).mp (by decide +kernel)

theorem g₁_mul_r₂ : g₁ * r₂ = r₂ * g₁ :=
  ((tabRep_g₁.comp tabRep_r₂).beq_iff (tabRep_r₂.comp tabRep_g₁)).mp (by decide +kernel)

theorem g₂_mul_r₂ : g₂ * r₂ = r₂ * g₂ :=
  ((tabRep_g₂.comp tabRep_r₂).beq_iff (tabRep_r₂.comp tabRep_g₂)).mp (by decide +kernel)

theorem g₃_eq_of_k₂ :
    g₃ = k₂ * g₂ * k₂⁻¹ * g₁⁻¹ * (k₂ * g₁ * k₂⁻¹) * g₂ * (k₂ * g₁ * k₂⁻¹)⁻¹ * g₁ := by
  simp only [g₃_eq_word, g₂_eq_word, g₁_eq_word, k₂, ← wordPerm_invW, ← wordPerm_append]
  apply wordPerm_eq_of_tab
  decide +kernel

theorem g₃_eq_of_k₂' :
    g₃ = g₁ * (k₂' * g₁ * k₂'⁻¹)⁻¹ * g₂ * (k₂' * g₁ * k₂'⁻¹) * g₁⁻¹ * (k₂' * g₂ * k₂'⁻¹) := by
  simp only [g₃_eq_word, g₂_eq_word, g₁_eq_word, k₂', ← wordPerm_invW, ← wordPerm_append]
  apply wordPerm_eq_of_tab
  decide +kernel

theorem x₃_mul_self : x₃ * x₃ = 1 :=
  ((tabRep_x₃.comp tabRep_x₃).beq_iff TabRep.idTab).mp (by decide +kernel)

theorem orderOf_r₃_x₃ : orderOf (r₃ * x₃ * r₃⁻¹ * x₃⁻¹) = 4 :=
  orderOf_eq_four_of_tab tabRep_r₃_x₃ (by decide +kernel) (by decide +kernel)

theorem k₃_mul_inv :
    k₃ * (r₃ * k₃ * r₃⁻¹)⁻¹ = r₃ * (r₃ * x₃ * r₃⁻¹ * x₃⁻¹) ^ 2 * r₃⁻¹ := by
  have hAi : TabRep (comp 42 (comp 42 r₃T (wordTab (invW [0, 1, 0, 1, 0, 1]))) r₃T)
      (r₃ * k₃ * r₃⁻¹)⁻¹ := by
    rw [show (r₃ * k₃ * r₃⁻¹)⁻¹ = r₃ * k₃⁻¹ * r₃⁻¹ by group]
    exact (tabRep_r₃.comp tabRep_k₃_inv).comp tabRep_r₃_inv
  exact ((tabRep_k₃.comp hAi).beq_iff
    ((tabRep_r₃.comp (tabRep_r₃_x₃.pow 2)).comp tabRep_r₃_inv)).mp (by decide +kernel)

theorem g₁_mul_r₃ : g₁ * r₃ = r₃ * g₁ :=
  ((tabRep_g₁.comp tabRep_r₃).beq_iff (tabRep_r₃.comp tabRep_g₁)).mp (by decide +kernel)

theorem h₃_mul_r₃ : h₃ * r₃ = r₃ * h₃ :=
  ((tabRep_h₃.comp tabRep_r₃).beq_iff (tabRep_r₃.comp tabRep_h₃)).mp (by decide +kernel)

theorem g₂_eq_of_k₃ : g₂ = h₃ * g₁⁻¹ * h₃⁻¹ * g₁ * h₃ * (k₃ * g₁ * k₃⁻¹) := by
  simp only [g₂_eq_word, g₁_eq_word, h₃, k₃, ← wordPerm_invW, ← wordPerm_append]
  apply wordPerm_eq_of_tab
  decide +kernel

theorem g₃_eq_of_k₃ :
    g₃ = k₃ * g₁ * k₃⁻¹ * (k₃ * h₃ * k₃⁻¹)⁻¹ * (k₃ * h₃ * k₃⁻¹)⁻¹ * (k₃ * g₁ * k₃⁻¹) := by
  simp only [g₃_eq_word, g₁_eq_word, h₃, k₃, ← wordPerm_invW, ← wordPerm_append]
  apply wordPerm_eq_of_tab
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

end
