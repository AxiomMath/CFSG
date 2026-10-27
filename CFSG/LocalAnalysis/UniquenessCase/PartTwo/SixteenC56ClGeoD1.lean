module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeoC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

variable {W : Type} [CommGroup W] {S : OmegaModel W} {E : Subgroup (MulAut W)}

@[expose] def secondLayer (E : Subgroup (MulAut W)) : Subgroup W where
  carrier := {w | ∀ e ∈ E, e w * w⁻¹ ∈ fixV E}
  one_mem' := fun e _ => by simpa using (fixV E).one_mem
  mul_mem' := fun {a b} ha hb e he => by
    have h : e (a * b) * (a * b)⁻¹ = (e a * a⁻¹) * (e b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [h]
    exact (fixV E).mul_mem (ha e he) (hb e he)
  inv_mem' := fun {a} ha e he => by
    have h : e a⁻¹ * (a⁻¹)⁻¹ = (e a * a⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
    rw [h]
    exact (fixV E).inv_mem (ha e he)

theorem fixV_le_secondLayer : fixV E ≤ secondLayer E := fun w hw e he => by
  rw [mem_fixV.1 hw e he, mul_inv_cancel]
  exact (fixV E).one_mem

theorem Geo2.isSub_secondLayer (hE : Geo2 S E) : S.IsSub (secondLayer E) := fun c w hw e he => by
  have h : e (S.smul c w) * (S.smul c w)⁻¹ = S.smul c (e w * w⁻¹) := by
    rw [hE.lin e he c w, S.smul_mul_eq]
    congr 1
    apply S.vec_injective
    rw [S.vec_inv, S.vec_smul, S.vec_smul, S.vec_inv, smul_neg]
  rw [h]
  exact hE.isSub_fixV c _ (hw e he)

theorem Geo2.secondLayer_le_perp (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) : secondLayer E ≤ S.perp (fixV E) := fun w hw =>
  (S.mem_perp).2 fun z hz => hE.pol_eq_zero_of_secondLayer hSK hF hw z hz

theorem Geo2.fixV_lt_secondLayer (hE : Geo2 S E) : fixV E < secondLayer E := by
  haveI := S.finite_carrier
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact S.mul_self_eq_one w
  obtain ⟨w, hwF, hw2⟩ :=
    exists_mem_secondLayer hW2 hE.elem (le_refl (fixV E)) (fixV_ne_top hE.ne_bot)
  refine lt_of_le_of_ne fixV_le_secondLayer fun h => hwF ?_
  have hw : w ∈ secondLayer E := hw2
  rwa [← h] at hw

theorem Geo2.card_perp_fix (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) : Nat.card (S.perp (fixV E)) = 64 := by
  have h := S.card_mul_card_perp hE.isSub_fixV
  rw [hF, hSK] at h
  omega

theorem Geo2.card_secondLayer_cases (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) :
    Nat.card (secondLayer E) = 16 ∨ Nat.card (secondLayer E) = 64 := by
  haveI := S.finite_carrier
  have h1 : Nat.card (fixV E) < Nat.card (secondLayer E) :=
    Subgroup.card_lt_of_lt hE.fixV_lt_secondLayer
  have h2 : Nat.card (secondLayer E) ≤ Nat.card (S.perp (fixV E)) :=
    Subgroup.card_le_of_le (hE.secondLayer_le_perp hSK hF)
  rw [hF] at h1
  rw [hE.card_perp_fix hSK hF] at h2
  rcases S.card_isSub_cases hSK hE.isSub_secondLayer with h | h | h | h | h <;> omega

theorem Geo2.comm_mem_secondLayer (hE : Geo2 S E) (hSK : Nat.card S.K = 4)
    (hF : Nat.card (fixV E) = 4) {h : W} (hh : h ∈ S.perp (fixV E)) {e : MulAut W}
    (he : e ∈ E) : e h * h⁻¹ ∈ secondLayer E := by
  classical
  haveI := S.finite_carrier
  have hδperp : e h * h⁻¹ ∈ S.perp (fixV E) := S.commutator_mem_perp_fixV hE.iso he h
  rcases hE.card_secondLayer_cases hSK hF with h16 | h64
  · by_contra hδ
    set δ : W := e h * h⁻¹ with hδdef
    have hδ1 : δ ∈ S.line δ := ⟨1, (S.smul_one_eq δ).symm⟩
    set T : Subgroup W := secondLayer E ⊔ S.line δ with hT
    have hlt : secondLayer E < T := by
      refine lt_of_le_of_ne le_sup_left fun heq => hδ ?_
      rw [heq]
      exact Subgroup.mem_sup_right hδ1
    have hle : T ≤ S.perp (fixV E) := by
      refine sup_le (hE.secondLayer_le_perp hSK hF) ?_
      rintro _ ⟨c, rfl⟩
      exact S.isSub_perp _ c δ hδperp
    have hc1 : 16 < Nat.card T := by
      rw [← h16]; exact Subgroup.card_lt_of_lt hlt
    have hc2 : Nat.card T ≤ 64 := by
      rw [← hE.card_perp_fix hSK hF]; exact Subgroup.card_le_of_le hle
    have hsup : S.IsSub T := S.isSub_sup hE.isSub_secondLayer (S.isSub_line δ)
    have hc3 : Nat.card T = 64 := by
      rcases S.card_isSub_cases hSK hsup with h | h | h | h | h <;> omega
    have hEq : T = S.perp (fixV E) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc3, hE.card_perp_fix hSK hF])
    have hhmem : h ∈ T := by rw [hEq]; exact hh
    obtain ⟨f, hf, l, ⟨c, rfl⟩, hfl⟩ := Subgroup.mem_sup.1 hhmem
    have hinv : ∀ x : W, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (S.mul_self_eq_one x)
    have he2 : ∀ x : W, e (e x) = x := fun x => by
      have := congrArg (fun a : MulAut W => a x) (hE.elem.2 e he)
      simpa [pow_two] using this
    have heδ : e δ = δ := by
      have h1 : e δ = δ⁻¹ := by
        rw [hδdef, map_mul, map_inv, he2, mul_inv_rev, inv_inv]
      rw [h1, hinv]
    have hδF : δ ∈ secondLayer E := by
      have h1 : e h = e f * S.smul c δ := by
        rw [← hfl, map_mul, hE.lin e he c δ, heδ]
      have hcalc : δ = e f * f⁻¹ := by
        rw [hδdef, h1, ← hfl]
        group
      rw [hcalc]
      exact fixV_le_secondLayer (hf e he)
    exact hδ hδF
  · have hEq : secondLayer E = S.perp (fixV E) :=
      Subgroup.eq_of_le_of_card_ge (hE.secondLayer_le_perp hSK hF)
        (by rw [h64, hE.card_perp_fix hSK hF])
    rw [hEq]
    exact hδperp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
