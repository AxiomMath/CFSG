module

public import CFSG.LieType.Ree.SuzukiOvoidWeyl
public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiS_one_zero_fix [CharP K 2] {v : Fin 4 → K} (h : (suzukiS a 1 0).mulVec v = v) :
    v = Pi.single 3 (v 3) := by
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [suzukiS, suzukiN, mulVec, dotProduct, Fin.sum_univ_four] at h1 h2 h3
  rw [h1, h2, zero_add, zero_add] at h3
  ext i
  fin_cases i <;> simp [h1, h2, h3]

theorem suzukiS_e4 (u v c : K) : (suzukiS a u v).mulVec (Pi.single 3 c) = Pi.single 3 c := by
  ext i
  fin_cases i <;> simp [suzukiS, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiD_e4 (l : Kˣ) (c : K) : (suzukiD a l).mulVec (Pi.single 3 c) =
    Pi.single 3 (((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) * c) := by
  ext i
  fin_cases i <;> simp [suzukiD, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiW_e4 (c : K) : (suzukiW K).mulVec (Pi.single 3 c) = Pi.single 0 c := by
  rw [suzukiW_mulVec]
  ext i
  fin_cases i <;> simp

theorem suzukiS_e1 (u v c : K) : (suzukiS a u v).mulVec (Pi.single 0 c) =
    ![c, u * c, v * c, suzukiN a u v * c] := by
  ext i
  fin_cases i <;> simp [suzukiS, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiN_one_zero : suzukiN a (1 : K) 0 = 1 := by
  simp [suzukiN]

theorem suzukiN_zero_one : suzukiN a (0 : K) 1 = 1 := by
  simp [suzukiN]

@[expose] def sterm (g : suzukiGroup a K) (c : K) : Fin 4 → K :=
  ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec (Pi.single 3 c)

theorem sterm_W (c : K) :
    sterm (suzukiWElt a K) c = ![c, 0, 0, 0] := by
  rw [sterm, coe_suzukiWElt, suzukiW_e4]
  ext i
  fin_cases i <;> simp

theorem sterm_SW (u v c : K) :
    sterm (suzukiSElt a K u v * suzukiWElt a K) c = ![c, u * c, v * c, suzukiN a u v * c] := by
  rw [sterm, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, coe_suzukiSElt, coe_suzukiWElt,
    suzukiW_e4, suzukiS_e1]

theorem sterm_one (c : K) : sterm (1 : suzukiGroup a K) c = ![0, 0, 0, c] := by
  rw [sterm, Subgroup.coe_one, Units.val_one, one_mulVec]
  ext i
  fin_cases i <;> simp

theorem sz_induction [CharP K 2] {P : (Fin 4 → K) → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y)) (hT : ∀ (g : suzukiGroup a K) (c : K), P (sterm g c))
    (x : Fin 4 → K) : P x := by
  have hx : x = sterm (suzukiWElt a K) (x 0) +
      (sterm (suzukiSElt a K 1 0 * suzukiWElt a K) (x 1) + sterm (suzukiWElt a K) (x 1) +
        sterm (1 : suzukiGroup a K) (x 1)) +
      (sterm (suzukiSElt a K 0 1 * suzukiWElt a K) (x 2) + sterm (suzukiWElt a K) (x 2) +
        sterm (1 : suzukiGroup a K) (x 2)) + sterm (1 : suzukiGroup a K) (x 3) := by
    rw [sterm_W, sterm_W, sterm_W, sterm_SW, sterm_SW, sterm_one, sterm_one, sterm_one,
      suzukiN_one_zero, suzukiN_zero_one]
    ext i
    fin_cases i <;> simp [CharTwo.add_self_eq_zero]
  rw [hx]
  exact hadd _ _ (hadd _ _ (hadd _ _ (hT _ _) (hadd _ _ (hadd _ _ (hT _ _) (hT _ _)) (hT _ _)))
    (hadd _ _ (hadd _ _ (hT _ _) (hT _ _)) (hT _ _))) (hT _ _)

theorem coprime_two_pow (a : ℕ) : (2 ^ (2 * a + 1) - 1).Coprime (2 ^ a + 1) := by
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ a = y + 1 := ⟨2 ^ a - 1, by have := Nat.one_le_two_pow (n := a); omega⟩
  have h1 : 2 ^ (2 * a + 1) - 1 = 1 + (2 * y) * (2 ^ a + 1) := by
    rw [pow_succ, pow_mul', hy]
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h1, Nat.coprime_add_mul_right_left]
  exact Nat.coprime_one_left _

theorem exists_zpow_eq [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : Kˣ) :
    ∃ l : Kˣ, l ^ (-1 - (2 ^ a : ℤ)) = c := by
  classical
  have := Fintype.ofFinite K
  have hcop : (Nat.card Kˣ).Coprime (2 ^ a + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    exact coprime_two_pow a
  obtain ⟨l, hl⟩ := (Nat.Coprime.pow_left_bijective hcop).2 c⁻¹
  refine ⟨l, ?_⟩
  rw [show (-1 - (2 ^ a : ℤ)) = -((2 ^ a + 1 : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg,
    zpow_natCast]
  have hl' : l ^ (2 ^ a + 1) = c⁻¹ := hl
  rw [hl', inv_inv]

variable {W : Type*} [CommGroup W]

@[expose] def IsSzCoord (a : ℕ) (Λ : Subgroup (MulAut W)) (π : suzukiGroup a K →* Λ)
    (Ψ : W → Fin 4 → K) : Prop :=
  Function.Surjective π ∧ (∀ w w', Ψ (w * w') = Ψ w + Ψ w') ∧ Function.Bijective Ψ ∧
    ∀ (γ : suzukiGroup a K) (w : W), Ψ ((π γ : MulAut W) w) =
      ((γ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec (Ψ w)

theorem exists_isSzCoord {Λ : Subgroup (MulAut W)}
    (h : (FFModel.nat (suzukiGroup a K)).Realizes Λ ⊤ ⊥) :
    ∃ (π : suzukiGroup a K →* Λ) (Ψ : W → Fin 4 → K), IsSzCoord a Λ π Ψ := by
  obtain ⟨π0, hπ0⟩ := h
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ0
  let Ψ : W → Fin 4 → K := fun w =>
    Multiplicative.toAdd (β ⟨w, Subgroup.mem_top w⟩ : Multiplicative (Fin 4 → K))
  refine ⟨π0, Ψ, hπ0.1, fun w w' =>
    congrArg Multiplicative.toAdd (map_mul β ⟨w, Subgroup.mem_top w⟩ ⟨w', Subgroup.mem_top w'⟩),
    ⟨fun w w' hww => ?_, fun v => ?_⟩, fun γ w =>
    congrArg Multiplicative.toAdd (hβe γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _))⟩
  · have h1 : β (⟨w, Subgroup.mem_top w⟩ * (⟨w', Subgroup.mem_top w'⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, show β ⟨w, Subgroup.mem_top w⟩ = β ⟨w', Subgroup.mem_top w'⟩ from
        Multiplicative.toAdd.injective hww]
      exact mul_inv_cancel _
    have h2 := (hβk _).mp h1
    rw [Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  · obtain ⟨⟨w, hw0⟩, hw⟩ := hβs (Multiplicative.ofAdd v)
    exact ⟨w, congrArg Multiplicative.toAdd hw⟩

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
