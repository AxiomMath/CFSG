module

public import CFSG.Quasithin.Background.SmithB42LnL5W5
public import CFSG.Quasithin.Background.SmithB42LnL5Ident

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

theorem upMat_R4_eq (c₃ c₆ c₈ c₉ : ZMod 2) :
    Curtis.upMat 0 0 0 c₃ 0 0 c₆ 0 c₈ c₉ = 1 + vecMulVec ![c₃, c₆, c₈, c₉, 0] (Pi.single 4 1) := by
  ext a b
  simp only [Matrix.add_apply, vecMulVec_apply, Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> simp [Curtis.upMat]

theorem mem_R4_iff {u : G5} : u ∈ R4 ↔
    ∃ w : Fin 5 → ZMod 2, w 4 = 0 ∧ ((u : G5) : 𝕄) = 1 + vecMulVec w (Pi.single 4 1) := by
  constructor
  · intro hu
    have h := eq_of_mem_R4 hu
    rw [upMat_R4_eq] at h
    exact ⟨_, rfl, h⟩
  · rintro ⟨w, hw4, hu⟩
    have hU : IsUpU ((u : G5) : 𝕄) := by
      intro a b
      rw [hu]
      fin_cases a <;> fin_cases b <;> simp [vecMulVec_apply, hw4]
    refine ⟨hU, ?_⟩
    ext a b
    simp only [topB, Matrix.of_apply, hu, Matrix.add_apply, vecMulVec_apply, Matrix.one_apply,
      Fin.castSucc_inj]
    have : (Pi.single (4 : Fin 5) (1 : ZMod 2) : Fin 5 → ZMod 2) b.castSucc = 0 := by
      revert b
      decide
    rw [this, mul_zero, add_zero]

theorem tvR_mul_self (w : Fin 5 → ZMod 2) (hw4 : w 4 = 0) :
    (1 + vecMulVec w (Pi.single 4 1)) * (1 + vecMulVec w (Pi.single 4 1)) = (1 : 𝕄) := by
  have hd : (Pi.single 4 1 : Fin 5 → ZMod 2) ⬝ᵥ w = 0 := by
    rw [dotProduct_comm, dotProduct_single, mul_one, hw4]
  rw [tv_mul_tv, hd, zero_smul, add_zero, add_assoc, add_self_mat, add_zero]

theorem card_R4 : Nat.card R4 = 16 := by
  refine le_antisymm card_R4_le ?_
  have hmem : ∀ w : Fin 4 → ZMod 2,
      ofMatInv (1 + vecMulVec (Fin.snoc w 0) (Pi.single 4 1))
        (1 + vecMulVec (Fin.snoc w 0) (Pi.single 4 1))
        (tvR_mul_self _ (Fin.snoc_last (α := fun _ => ZMod 2) _ _)) ∈ R4 := fun w =>
    mem_R4_iff.2 ⟨Fin.snoc w 0, Fin.snoc_last (α := fun _ => ZMod 2) _ _, rfl⟩
  have hentry : ∀ (w : Fin 4 → ZMod 2) (i : Fin 4),
      (1 + vecMulVec (Fin.snoc w 0) (Pi.single 4 1) : 𝕄) i.castSucc 4 = w i := by
    intro w i
    have hne : i.castSucc ≠ (4 : Fin 5) := (Fin.castSucc_lt_last i).ne
    simp [vecMulVec_apply, hne]
  let f : (Fin 4 → ZMod 2) → ↥R4 := fun w => ⟨_, hmem w⟩
  have hf : Function.Injective f := by
    intro w w' h
    have h1 : (1 + vecMulVec (Fin.snoc w 0) (Pi.single 4 1) : 𝕄) =
        1 + vecMulVec (Fin.snoc w' 0) (Pi.single 4 1) :=
      congrArg (fun u : ↥R4 => ((u : G5) : 𝕄)) h
    funext i
    have h2 := congrFun (congrFun h1 i.castSucc) 4
    rwa [hentry, hentry] at h2
  calc 16 = Nat.card (Fin 4 → ZMod 2) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]; rfl
    _ ≤ Nat.card R4 := Nat.card_le_card_of_injective f hf

theorem fix_R4_upMat (c₃ c₆ c₈ c₉ : ZMod 2) {x : Fin 10 → ZMod 2} (hx : crdE x = 0) :
    wedgeMat (Curtis.upMat 0 0 0 c₃ 0 0 c₆ 0 c₈ c₉) *ᵥ x = x := by
  have h3 : x 3 = 0 := congrFun hx 0
  have h6 : x 6 = 0 := congrFun hx 1
  have h8 : x 8 = 0 := congrFun hx 2
  have h9 : x 9 = 0 := congrFun hx 3
  funext k
  fin_cases k <;>
    simp [wedgeMat, pr5, Curtis.upMat, mulVec, dotProduct, Fin.sum_univ_succ, h3, h6, h8, h9] <;>
    ring

theorem card_crdE_zero :
    (Finset.univ.filter fun x : Fin 10 → ZMod 2 => crdE x = 0).card = 64 := by
  decide

theorem card_fixW_R4 : 64 ≤ Nat.card (FixW R4) := by
  classical
  rw [← card_crdE_zero, ← card_subtype_eq]
  refine card_subtype_mono fun x hx u hu => ?_
  rw [eq_of_mem_R4 hu]
  exact fix_R4_upMat _ _ _ _ hx

theorem mem_conj_R4_iff (h : G5) {u : G5} :
    u ∈ R4.map (MulAut.conj h).toMonoidHom ↔
      ∃ w : Fin 5 → ZMod 2, (Pi.single 4 1 ᵥ* ((h⁻¹ : G5) : 𝕄)) ⬝ᵥ w = 0 ∧
        ((u : G5) : 𝕄) = 1 + vecMulVec w (Pi.single 4 1 ᵥ* ((h⁻¹ : G5) : 𝕄)) := by
  have hhi : ((h : G5) : 𝕄) * ((h⁻¹ : G5) : 𝕄) = 1 := coe_mul_inv h
  have hih : ((h⁻¹ : G5) : 𝕄) * ((h : G5) : 𝕄) = 1 := coe_inv_mul h
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨w₀, hw₀, hr'⟩ := mem_R4_iff.1 hr
    refine ⟨(h : 𝕄) *ᵥ w₀, ?_, ?_⟩
    · rw [dotProduct_mulVec, vecMul_vecMul, hih, vecMul_one, dotProduct_comm,
        dotProduct_single, mul_one, hw₀]
    · show (h : 𝕄) * (r : 𝕄) * ((h⁻¹ : G5) : 𝕄) = _
      rw [hr', mul_add, mul_one, add_mul, hhi, mul_vecMulVec, vecMulVec_mul]
  · rintro ⟨w, hw, hu⟩
    refine ⟨h⁻¹ * u * h, mem_R4_iff.2 ⟨((h⁻¹ : G5) : 𝕄) *ᵥ w, ?_, ?_⟩, ?_⟩
    · calc (((h⁻¹ : G5) : 𝕄) *ᵥ w) 4 = Pi.single 4 1 ⬝ᵥ (((h⁻¹ : G5) : 𝕄) *ᵥ w) := by
            rw [single_dotProduct, one_mul]
        _ = 0 := by rw [dotProduct_mulVec]; exact hw
    · show ((h⁻¹ : G5) : 𝕄) * (u : 𝕄) * (h : 𝕄) = _
      rw [hu, mul_add, mul_one, add_mul, hih, mul_vecMulVec, vecMulVec_mul, vecMul_vecMul,
        hih, vecMul_one]
    · show h * (h⁻¹ * u * h) * h⁻¹ = u
      group

theorem card_fixW_conj (Y : Subgroup G5) (h : G5) :
    Nat.card (FixW (Y.map (MulAut.conj h).toMonoidHom)) = Nat.card (FixW Y) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨wedgeRep h⁻¹ x.1, fun u hu => ?_⟩
      invFun := fun x => ⟨wedgeRep h x.1, fun u hu => ?_⟩
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun x => Subtype.ext ?_ }
  · have h1 := x.2 (h * u * h⁻¹) ⟨u, hu, rfl⟩
    rw [← wedgeRep_apply'] at h1 ⊢
    calc wedgeRep u (wedgeRep h⁻¹ x.1) = wedgeRep h⁻¹ (wedgeRep (h * u * h⁻¹) x.1) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
            show h⁻¹ * (h * u * h⁻¹) = u * h⁻¹ by group]
      _ = wedgeRep h⁻¹ x.1 := by rw [h1]
  · obtain ⟨y, hy, rfl⟩ := hu
    have h1 := x.2 y hy
    rw [← wedgeRep_apply'] at h1 ⊢
    show wedgeRep (h * y * h⁻¹) (wedgeRep h x.1) = wedgeRep h x.1
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [show h * y * h⁻¹ * h = h * y by group, map_mul, Module.End.mul_apply, h1]
  · show wedgeRep h (wedgeRep h⁻¹ x.1) = x.1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · show wedgeRep h⁻¹ (wedgeRep h x.1) = x.1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem card_mul_fixW_le' {Y : Subgroup G5} (hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (h2 : ∀ a ∈ Y, a * a = 1) :
    Nat.card Y * Nat.card (FixW Y) ≤ 2 ^ 10 ∧
      (2 ^ 10 ≤ Nat.card Y * Nat.card (FixW Y) → Y ≠ ⊥ →
        ∃ h : G5, Y = R4.map (MulAut.conj h).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := exists_conj_le_Ugrp (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq Y h2)
  set Y' : Subgroup G5 := Y.map (MulAut.conj h).toMonoidHom with hY'
  have hcard : Nat.card Y' = Nat.card Y :=
    Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
  have hY'U : Y' ≤ Ugrp := by
    rintro _ ⟨a, ha, rfl⟩
    exact hh a ha
  have hc' : ∀ a ∈ Y', ∀ b ∈ Y', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hc a ha b hb
    calc h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
      _ = h * (b * a) * h⁻¹ := by rw [this]
      _ = h * b * h⁻¹ * (h * a * h⁻¹) := by group
  have h2' : ∀ a ∈ Y', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
      _ = 1 := by rw [h2 a ha]; group
  have key := card_mul_fixW_le hY'U hc' h2'
  rw [hcard, card_fixW_conj] at key
  refine ⟨key.1, fun hge hY1 => ⟨h⁻¹, ?_⟩⟩
  have hY'1 : Y' ≠ ⊥ := by
    intro h0
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have : (MulAut.conj h).toMonoidHom y ∈ Y' := ⟨y, hy, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact (MulAut.conj h).injective (this.trans (map_one _).symm)
  have hR := key.2 hge hY'1
  ext y
  constructor
  · intro hy
    refine ⟨h * y * h⁻¹, ?_, ?_⟩
    · rw [← hR]
      exact ⟨y, hy, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  · rintro ⟨r, hr, rfl⟩
    rw [← hR] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    have e1 : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom y) = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e1]
    exact hy

end CFSG.Quasithin.B42Ln
