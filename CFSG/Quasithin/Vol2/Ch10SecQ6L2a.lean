module

public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix

variable {W : Type*} [CommGroup W] {K : Type} [Field K]

@[expose] def IsL2Coord (Λ : Subgroup (MulAut W)) (π : SpecialLinearGroup (Fin 2) K →* Λ)
    (Ψ : W → Fin 2 → K) : Prop :=
  Function.Surjective π ∧ (∀ w w', Ψ (w * w') = Ψ w + Ψ w') ∧ (∀ v, ∃ w, Ψ w = v) ∧
    (∀ w, Ψ w = 0 ↔ w ∈ fixV Λ) ∧
    ∀ (γ : SpecialLinearGroup (Fin 2) K) (w : W),
      Ψ ((π γ : MulAut W) w) = (γ : Matrix (Fin 2) (Fin 2) K).mulVec (Ψ w)

theorem exists_isL2Coord {Λ : Subgroup (MulAut W)}
    (h : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K)).Realizes Λ ⊤ (fixV Λ)) :
    ∃ (π : SpecialLinearGroup (Fin 2) K →* Λ) (Ψ : W → Fin 2 → K), IsL2Coord Λ π Ψ := by
  obtain ⟨π0, hπ0⟩ := h
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ0
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  let Ψ : W → Fin 2 → K := fun w =>
    Multiplicative.toAdd (β ⟨w, Subgroup.mem_top w⟩ : Multiplicative (Fin 2 → K))
  refine ⟨π0.comp e.toMonoidHom, Ψ, hπ0.1.comp e.surjective, fun w w' =>
    congrArg Multiplicative.toAdd (map_mul β ⟨w, Subgroup.mem_top w⟩ ⟨w', Subgroup.mem_top w'⟩),
    fun v => ?_, fun w => toAdd_eq_zero.trans (hβk ⟨w, Subgroup.mem_top w⟩), fun γ w =>
    congrArg Multiplicative.toAdd (hβe (e γ) ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _))⟩
  obtain ⟨⟨w, hw0⟩, hw⟩ := hβs (Multiplicative.ofAdd v)
  exact ⟨w, congrArg Multiplicative.toAdd hw⟩

theorem exists_sl2_mulVec_single {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ γ : SpecialLinearGroup (Fin 2) K,
      (γ : Matrix (Fin 2) (Fin 2) K).mulVec (Pi.single 0 1) = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec {v x : Fin 2 → K} (hv : v ≠ 0) (hx : x ≠ 0) :
    ∃ γ : SpecialLinearGroup (Fin 2) K, (γ : Matrix (Fin 2) (Fin 2) K).mulVec v = x := by
  obtain ⟨γv, hγv⟩ := exists_sl2_mulVec_single hv
  obtain ⟨γx, hγx⟩ := exists_sl2_mulVec_single hx
  refine ⟨γx * γv⁻¹, ?_⟩
  have h1 : ((γv⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (γv : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [← hγv, Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec, Matrix.mul_assoc, h1,
    Matrix.mul_one, hγx]

theorem neg_vec_char_two [CharP K 2] (x : Fin 2 → K) : -x = x :=
  funext fun i => CharTwo.neg_eq (x i)

theorem eq_one_of_centralizes [CharP K 2] {Λ : Subgroup (MulAut W)}
    {π : SpecialLinearGroup (Fin 2) K →* Λ} {Ψ : W → Fin 2 → K} (hc : IsL2Coord Λ π Ψ)
    (hcomm : commV Λ = ⊤) {e : MulAut W} (he2 : e * e = 1) (hec : ∀ l ∈ Λ, e * l = l * e) :
    e = 1 := by
  obtain ⟨-, hmul, -, hker, heq⟩ := hc
  have hee : ∀ w, e (e w) = w := fun w => by
    rw [← MulAut.mul_apply, he2]
    rfl
  have hZ : ∀ z ∈ fixV Λ, e z ∈ fixV Λ := fun z hz l hl => by
    rw [← MulAut.mul_apply, ← hec l hl, MulAut.mul_apply, hz l hl]
  have hΨ1 : Ψ 1 = 0 := (hker 1).mpr (one_mem _)
  have hΨinv : ∀ w, Ψ w⁻¹ = -Ψ w := fun w => by
    have h := hmul w w⁻¹
    rw [mul_inv_cancel, hΨ1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hdep : ∀ w w', Ψ w = Ψ w' → Ψ (e w) = Ψ (e w') := fun w w' h => by
    have h1 : w⁻¹ * w' ∈ fixV Λ := (hker _).mp (by rw [hmul, hΨinv, h, neg_add_cancel])
    have h2 := (hker _).mpr (hZ _ h1)
    rw [map_mul, map_inv, hmul, hΨinv] at h2
    exact neg_add_eq_zero.mp h2
  have hfix : ∀ w, Ψ (e w) = Ψ w := by
    by_contra hne
    push Not at hne
    obtain ⟨w0, hw0⟩ := hne
    have hv0 : Ψ (w0 * e w0) ≠ 0 := fun h => hw0 (by
      rw [hmul] at h
      rw [eq_neg_of_add_eq_zero_right h, neg_vec_char_two])
    have hw1 : e (w0 * e w0) = w0 * e w0 := by rw [map_mul, hee, mul_comm]
    by_cases hx0 : Ψ w0 = 0
    · apply hw0
      rw [hx0]
      exact (hker _).mpr (hZ _ ((hker _).mp hx0))
    · obtain ⟨γ, hγ⟩ := exists_sl2_mulVec hv0 hx0
      have hew : e ((π γ : MulAut W) (w0 * e w0)) = (π γ : MulAut W) (w0 * e w0) := by
        rw [← MulAut.mul_apply, hec _ (π γ).2, MulAut.mul_apply, hw1]
      have hΨw : Ψ ((π γ : MulAut W) (w0 * e w0)) = Ψ w0 := by rw [heq, hγ]
      apply hw0
      rw [hdep w0 _ hΨw.symm, hew, hΨw]
  have hφ : ∀ w, e w * w⁻¹ ∈ fixV Λ := fun w =>
    (hker _).mp (by rw [hmul, hΨinv, hfix, add_neg_cancel])
  let Fe : Subgroup W :=
    { carrier := {w | e w = w}
      one_mem' := map_one e
      mul_mem' := fun {a b} ha hb => by
        change e (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        change e a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hle : commV Λ ≤ Fe := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    change e (x v * v⁻¹) = x v * v⁻¹
    have h2 : x (e v * v⁻¹) = e v * v⁻¹ := hφ v x hx
    have h3 : e (x v) = (e v * v⁻¹) * x v :=
      calc e (x v) = x (e v) := by rw [← MulAut.mul_apply, hec x hx, MulAut.mul_apply]
        _ = x ((e v * v⁻¹) * v) := by rw [inv_mul_cancel_right]
        _ = (e v * v⁻¹) * x v := by rw [map_mul, h2]
    rw [map_mul, map_inv, h3]
    calc e v * v⁻¹ * x v * (e v)⁻¹ = x v * v⁻¹ * (e v * (e v)⁻¹) := by ac_rfl
      _ = x v * v⁻¹ := by rw [mul_inv_cancel, mul_one]
  rw [hcomm] at hle
  exact MulEquiv.ext fun w => hle (Subgroup.mem_top w)

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
