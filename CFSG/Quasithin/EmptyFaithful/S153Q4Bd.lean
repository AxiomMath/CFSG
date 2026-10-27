module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Bc

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4B

open Equiv

section Centres

variable {W : Type} [CommGroup W] {Ah : Subgroup (MulAut W)} {z : MulAut W}
  {lab : Fin 6 → Subgroup W}

theorem Ctx.centres [Finite W] (C : Ctx W Ah z lab) :
    ∃ P : Fin 3 → MulAut W,
      (∀ a, P a ∈ Ah ∧ P a * P a = 1 ∧ Ind lab (P a) (S3 a)) ∧
      (∀ a, IsPt z (cen (P a)) ∧ cen (P a) ≤ lab 4 ⊔ lab 5) ∧
      (∀ a, cen (P a) ≠ lab 4 ∧ cen (P a) ≠ lab 5) ∧
      (∀ a b, a ≠ b → cen (P a) ≠ cen (P b)) := by
  choose P hPA hPP hPI using fun a : Fin 3 => C.exists_inv_lift (S3_mem a) (S3_sq a)
  have h45 : lab 4 ≠ lab 5 := fun h => absurd (C.O.inj h) (by decide)
  have hV16 : Nat.card ↥(lab 4 ⊔ lab 5) = 16 := C.card_sup_pts (C.pt 4) (C.pt 5) h45
  have hne1 : ∀ a, P a ≠ 1 := fun a =>
    C.ne_one_of_ind (hPI a) (fun h => S3_zero_ne a (by rw [h]; rfl))
  have hspec : ∀ a, IsPt z (cen (P a)) ∧ cen (P a) ≤ lab 4 ⊔ lab 5 := fun a =>
    C.cen_spec (hPA a) (hne1 a) (hPP a) hV16
      (C.fix_sup (hPA a) (hPP a) (hPI a) (S3_four a) (S3_five a))
  have hsup : ∀ a k, lab (S3 a k) ≤ lab k ⊔ cen (P a) := fun a k =>
    lab_le_sup_cen (hPP a) (S3_sq a) (hPI a) k
  have hl0 : ∀ a, lab 0 ≠ lab (S3 a 0) := fun a h => S3_zero_ne a (C.O.inj h).symm
  have hn4 : ∀ a, cen (P a) ≠ lab 4 := by
    intro a h
    have h1 := hsup a 0
    rw [h] at h1
    exact C.O.arc 0 4 (S3 a 0) (by decide) (fun h' => S3_zero_ne a h'.symm)
      (fun h' => S3_zero_ne_four a h'.symm) h1
  have hn5 : ∀ a, cen (P a) ≠ lab 5 := by
    intro a h
    have h1 := hsup a 0
    rw [h] at h1
    exact C.O.arc 0 5 (S3 a 0) (by decide) (fun h' => S3_zero_ne a h'.symm)
      (fun h' => S3_zero_ne_five a h'.symm) h1
  have hdist : ∀ a b, a ≠ b → cen (P a) ≠ cen (P b) := by
    intro a b hab h
    have h0V : lab 0 ≠ cen (P a) := by
      intro h0
      have hle : lab 0 ≤ lab 4 ⊔ lab 5 := h0 ▸ (hspec a).2
      exact C.O.arc 4 5 0 (by decide) (by decide) (by decide) hle
    have hL : Nat.card ↥(lab 0 ⊔ cen (P a)) = 16 := C.card_sup_pts (C.pt 0) (hspec a).1 h0V
    have hle1 : lab 0 ⊔ lab (S3 a 0) ≤ lab 0 ⊔ cen (P a) := sup_le le_sup_left (hsup a 0)
    have hcard1 : Nat.card ↥(lab 0 ⊔ lab (S3 a 0)) = 16 :=
      C.card_sup_pts (C.pt 0) (C.pt _) (hl0 a)
    have heq : lab 0 ⊔ lab (S3 a 0) = lab 0 ⊔ cen (P a) :=
      Subgroup.eq_of_le_of_card_ge hle1 (by rw [hL, hcard1])
    have hb : lab (S3 b 0) ≤ lab 0 ⊔ lab (S3 a 0) := by
      rw [heq, h]
      exact hsup b 0
    exact C.O.arc 0 (S3 a 0) (S3 b 0) (fun h' => S3_zero_ne a h'.symm)
      (fun h' => S3_zero_ne b h'.symm) (fun h' => hab (S3_zero_inj h')) hb
  exact ⟨P, fun a => ⟨hPA a, hPP a, hPI a⟩, hspec, fun a => ⟨hn4 a, hn5 a⟩, hdist⟩

end Centres

end Q4B

end S153Q

end CFSG.Quasithin
