module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD.L3

open CFSG.Quasithin.L3

@[expose] def P0 : Subgroup Γ where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    simp [ha1, ha2, ha3, hb1, hb2, hb3]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [ha1, ha2, ha3]

instance : DecidablePred (· ∈ P0) := fun g =>
  inferInstanceAs (Decidable ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0))

theorem card_P0 : Nat.card P0 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Γ : Nat.card Γ = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem factorization_card_Γ : (Nat.card Γ).factorization 2 = 3 := by
  rw [card_Γ, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]

@[expose] noncomputable def sylowP0 : Sylow 2 Γ :=
  Sylow.ofCard P0 (by rw [card_P0, factorization_card_Γ]; norm_num)

theorem exists_conj_eq_P0 {P : Subgroup Γ} (hP : Nat.card P = 8) :
    ∃ g : Γ, P = P0.map (MulAut.conj g).toMonoidHom := by
  let SP : Sylow 2 Γ := Sylow.ofCard P (by rw [hP, factorization_card_Γ]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ sylowP0 SP
  refine ⟨g, ?_⟩
  have := congrArg (fun Q : Sylow 2 Γ => (Q : Subgroup Γ)) hg
  simp only [Sylow.coe_subgroup_smul, SP, Sylow.coe_ofCard] at this
  rw [← this]
  rfl

theorem fix_P0 (v : Vec) : (∀ g ∈ P0, act g v = v) ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro h
    have hx : (⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩ : Γ) ∈ P0 :=
      ⟨by decide, by decide, by decide⟩
    have hy : (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : Γ) ∈ P0 :=
      ⟨by decide, by decide, by decide⟩
    have h1 := congrFun (h _ hx) 0
    have h2 := congrFun (h _ hy) 1
    simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ g ⟨hg1, hg2, hg3⟩
    have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := g.2
    rw [Matrix.det_fin_three] at hdet
    simp only [hg1, hg2, hg3, mul_zero, zero_mul, add_zero] at hdet
    have hd : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 1 := by
      have key : ∀ a b c : ZMod 2, a * b * c - 0 - 0 - 0 = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by
        decide
      exact key _ _ _ hdet
    funext i
    fin_cases i <;>
      simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, hg1, hg2, hg3,
        hd.1, hd.2.1, hd.2.2]

theorem card_fix_P0 : Nat.card {v : Vec // ∀ g ∈ P0, act g v = v} = 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fix_P0), Nat.card_eq_fintype_card]
  decide

theorem card_fix_of_card_eq_eight {P : Subgroup Γ} (hP : Nat.card P = 8) :
    Nat.card {v : Vec // ∀ g ∈ P, act g v = v} = 2 := by
  obtain ⟨g, rfl⟩ := exists_conj_eq_P0 hP
  have key : ∀ v : Vec, (∀ h ∈ P0.map (MulAut.conj g).toMonoidHom, act h v = v) ↔
      (∀ h ∈ P0, act h (act g⁻¹ v) = act g⁻¹ v) := by
    intro v
    constructor
    · intro hv h hh
      have := hv (g * h * g⁻¹) ⟨h, hh, rfl⟩
      rw [act_mul, act_mul] at this
      have e' := congrArg (act g⁻¹) this
      rwa [act_inv_act] at e'
    · rintro hv _ ⟨h, hh, rfl⟩
      have e := hv h hh
      show act (g * h * g⁻¹) v = v
      rw [act_mul, act_mul, e, act_act_inv]
  have e : {x : Vec // ∀ h ∈ P0, act h (act g⁻¹ x) = act g⁻¹ x} ≃
      {v : Vec // ∀ g ∈ P0, act g v = v} :=
    { toFun := fun v => ⟨act g⁻¹ v.1, v.2⟩
      invFun := fun w => ⟨act g w.1, by simpa [act_inv_act] using w.2⟩
      left_inv := fun v => by simp [act_act_inv]
      right_inv := fun w => by simp [act_inv_act] }
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact (Nat.card_congr e).trans card_fix_P0

end CFSG.Quasithin.Vol2.Ch10.SecD.L3
