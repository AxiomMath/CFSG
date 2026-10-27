module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeoD1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

variable {W : Type} [CommGroup W] {S : OmegaModel W} {E : Subgroup (MulAut W)}

theorem Geo2.comm_mem_fix_of_mem_perp (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) {h : W} (hh : h ∈ S.perp (fixV E)) {e₁ : MulAut W}
    (he₁ : e₁ ∈ E) : e₁ h * h⁻¹ ∈ fixV E := by
  classical
  haveI := S.finite_carrier
  by_contra hv
  have hvF₂ : e₁ h * h⁻¹ ∈ secondLayer E := hE.comm_mem_secondLayer hSK hF hh he₁
  have hinv : ∀ x : W, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (S.mul_self_eq_one x)
  have he2 : ∀ x : W, e₁ (e₁ x) = x := fun x => by
    have := congrArg (fun a : MulAut W => a x) (hE.elem.2 e₁ he₁)
    simpa [pow_two] using this
  have h16 : Nat.card (secondLayer E) = 16 := by
    rcases hE.card_secondLayer_cases hSK hF with h16 | h64
    · exact h16
    · exfalso
      have hEq : secondLayer E = S.perp (fixV E) :=
        Subgroup.eq_of_le_of_card_ge (hE.secondLayer_le_perp hSK hF)
          (by rw [h64, hE.card_perp_fix hSK hF])
      have hh2 : h ∈ secondLayer E := by rw [hEq]; exact hh
      exact hv (hh2 e₁ he₁)
  set v : W := e₁ h * h⁻¹ with hvdef
  have he1v : e₁ v = v := by
    have h1 : e₁ v = v⁻¹ := by
      rw [hvdef, map_mul, map_inv, he2, mul_inv_rev, inv_inv]
    rw [h1, hinv]
  set N : Subgroup W := fixV E ⊔ S.line v with hN
  have hNle : N ≤ secondLayer E := by
    refine sup_le fixV_le_secondLayer ?_
    rintro _ ⟨c, rfl⟩
    exact hE.isSub_secondLayer c v hvF₂
  have hv1 : v ∈ S.line v := ⟨1, (S.smul_one_eq v).symm⟩
  have hlt : fixV E < N := by
    refine lt_of_le_of_ne le_sup_left fun heq => hv ?_
    rw [heq]
    exact Subgroup.mem_sup_right hv1
  have hc1 : 4 < Nat.card N := by
    rw [← hF]; exact Subgroup.card_lt_of_lt hlt
  have hc2 : Nat.card N ≤ 16 := by
    rw [← h16]; exact Subgroup.card_le_of_le hNle
  have hsup : S.IsSub N := S.isSub_sup hE.isSub_fixV (S.isSub_line v)
  have hc3 : Nat.card N = 16 := by
    rcases S.card_isSub_cases hSK hsup with h | h | h | h | h <;> omega
  have hNeq : N = secondLayer E := Subgroup.eq_of_le_of_card_ge hNle (by rw [hc3, h16])
  have hfix₁ : ∀ x ∈ secondLayer E, e₁ x = x := by
    intro x hx
    rw [← hNeq] at hx
    obtain ⟨f, hf, l, ⟨c, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul, mem_fixV.1 hf e₁ he₁, hE.lin e₁ he₁ c v, he1v]
  apply hv
  rw [mem_fixV]
  intro e he
  have hx : e h * h⁻¹ ∈ secondLayer E := hE.comm_mem_secondLayer hSK hF hh he
  have h1 := hfix₁ _ hx
  rw [map_mul, map_inv] at h1
  have hcomm : e (e₁ h) = e₁ (e h) := by
    have := congrArg (fun a : MulAut W => a h) (hE.elem.1 e he e₁ he₁)
    simpa using this
  rw [hvdef, map_mul, map_inv, hcomm]
  have h2 : e₁ (e h) = e h * h⁻¹ * e₁ h := by
    have h3 : e₁ (e h) * (e₁ h)⁻¹ = e h * h⁻¹ := h1
    calc e₁ (e h) = e₁ (e h) * (e₁ h)⁻¹ * e₁ h := by group
      _ = e h * h⁻¹ * e₁ h := by rw [h3]
  rw [h2, mul_right_comm (e h * h⁻¹) (e₁ h) (e h)⁻¹, mul_right_comm (e h) h⁻¹ (e h)⁻¹,
    mul_inv_cancel, one_mul, mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
