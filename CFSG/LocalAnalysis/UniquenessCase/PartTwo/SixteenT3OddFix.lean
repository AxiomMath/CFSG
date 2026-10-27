module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16t_fixV_eq_bot_of_indivisible {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {M A : Subgroup (MulAut T)} (hind : IsIndivisible M)
    (hnorm : ∀ g ∈ M, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hodd : Odd (Nat.card A)) (hA1 : A ≠ ⊥) :
    fixV A = ⊥ := by
  have hcop := coprime_decomp (P := A) hodd hT (W := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _)
  have hfix_stab : StableUnder M (fixV A) := by
    intro g hg u hu
    rw [mem_fixV] at hu ⊢
    intro a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      simpa only [inv_inv] using hnorm g⁻¹ (M.inv_mem hg) a ha
    calc a (g u) = g ((g⁻¹ * a * g) u) := by simp [MulAut.mul_apply]
      _ = g u := by rw [hu _ ha']
  have hcomm_stab : StableUnder M (commSub ⊤ A) := by
    intro g hg u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨θ, hθ, w, -, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨g * θ * g⁻¹, hnorm g hg θ hθ, g w,
        Subgroup.mem_top _, ?_⟩
      simp [MulAut.mul_apply]
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact (commSub ⊤ A).mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact (commSub ⊤ A).inv_mem hx
  have hsup : commSub ⊤ A ⊔ fixV A = ⊤ := by
    simpa [top_inf_eq] using hcop.1
  rcases hind (commSub ⊤ A) (fixV A) hcomm_stab hfix_stab hsup with h | h
  · have h2 := hcop.2
    simpa [h, top_inf_eq] using h2
  · exfalso
    apply hA1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    ext v
    have hv : v ∈ fixV A := by rw [h]; exact Subgroup.mem_top v
    simpa using (mem_fixV.mp hv) a ha

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
