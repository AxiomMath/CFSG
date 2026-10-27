module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WTwoRank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem false_of_comm_mem_card_le_B_of_I2a (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hI2a : I2aProp A B V)
    {u β : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) (huβ : (graph (A ⊔ B) A B).Adj u β)
    {y : D} (hyβ : y ∈ stab β) (hyu : y ∉ stab u) {P : Subgroup D} (hP : Nat.card P ≤ 4)
    (hcomm : ∀ w ∈ Vn V 2 u, w * y * w⁻¹ * y⁻¹ ∈ P) : False := by
  have hβt : vtype β = true := vtype_eq_true_of_adj huβ hu
  have hyG : y ∈ A ⊔ B := stab_le β hyβ
  lift y to ↥(A ⊔ B) using hyG with g
  have hgβ : g • β = β := smul_eq_of_mem_stab hyβ
  have hgu : g • u ≠ u := fun e => hyu (mem_stab_of_smul_eq e)
  have hgadj : (graph (A ⊔ B) A B).Adj β (g • u) := by
    have := (smul_adj g).mpr huβ.symm
    rwa [hgβ] at this
  obtain ⟨γ, -, hγ, -, n1, -, -⟩ := h.exists_other_nbrs huβ
  have hγt : vtype γ = true := vtype_eq_true_of_adj hγ hu
  have hgγ : (graph (A ⊔ B) A B).Adj (g • u) (g • γ) := (smul_adj g).mpr hγ
  have hgγβ : g • γ ≠ β := fun e => n1 (by
    have : g⁻¹ • (g • γ) = g⁻¹ • β := by rw [e]
    rwa [inv_smul_smul, inv_smul_eq_iff.mpr hgβ.symm] at this)
  have hint : Vv V γ ⊓ Vv V (g • γ) ≤ Vv V β :=
    hI2a β u (g • u) γ (g • γ) hβt huβ.symm hgadj (Ne.symm hgu) hγ hgγ n1 hgγβ
  have hI : Vv V γ ⊓ Vv V β ≤ Vv V u := hI1 u γ β hu hγ huβ n1
  set C : Subgroup D := Vv V γ ⊓ Subgroup.centralizer ({(g : D)} : Set D) with hC
  have hCle : C ≤ Vv V u ⊓ Vv V (g • u) := by
    intro w hw
    have hwy : (g : D) * w * (g : D)⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hw.2
      rw [← this]
      group
    have hwγ' : w ∈ Vv V (g • γ) := by
      rw [Vv_smul h.natural.reduced.2.1, mem_conjSub, inv_mul_mul_of_mul_mul_inv hwy]
      exact hw.1
    have hwβ : w ∈ Vv V β := hint ⟨hw.1, hwγ'⟩
    have hwu : w ∈ Vv V u := hI ⟨hw.1, hwβ⟩
    have hwu' : w ∈ Vv V (g • u) := by
      rw [Vv_smul h.natural.reduced.2.1, mem_conjSub, inv_mul_mul_of_mul_mul_inv hwy]
      exact hwu
    exact ⟨hwu, hwu'⟩
  have hVne : Vv V u ≠ Vv V (g • u) := fun e =>
    hgu (h.eq_of_Vv_eq hβt huβ.symm hgadj e).symm
  have hgut : vtype (g • u) = false := by
    rw [vtype_smul]
    exact hu
  have hc4 : Nat.card (Vv V u) = 4 := h.card_Vv_A hu
  have hc4' : Nat.card (Vv V (g • u)) = 4 := h.card_Vv_A hgut
  have hC2 : Nat.card C ≤ 2 := by
    have h1 : Nat.card C ≤ Nat.card (Vv V u ⊓ Vv V (g • u) : Subgroup D) :=
      Subgroup.card_le_of_le hCle
    have hle : Vv V u ⊓ Vv V (g • u) ≤ Vv V u := inf_le_left
    have hdvd : Nat.card (Vv V u ⊓ Vv V (g • u) : Subgroup D) ∣ 4 :=
      hc4 ▸ Subgroup.card_dvd_of_le hle
    have hne : Nat.card (Vv V u ⊓ Vv V (g • u) : Subgroup D) ≠ 4 := fun e =>
      hVne (by
        have e1 : Vv V u ⊓ Vv V (g • u) = Vv V u :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hc4, e])
        have e2 : Vv V u ⊓ Vv V (g • u) = Vv V (g • u) :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hc4', e])
        exact e1.symm.trans e2)
    have hle4 : Nat.card (Vv V u ⊓ Vv V (g • u) : Subgroup D) ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Vv V u ⊓ Vv V (g • u) : Subgroup D) = n at hdvd hne hle4 h1 ⊢
    interval_cases n <;> omega
  have hcount : Nat.card (Vv V γ) ≤ Nat.card P * Nat.card C :=
    card_le_mul_of_comm_mem fun w hw => hcomm w (Vv_B_le_Vn_two hu hγ hw)
  have hU16 : Nat.card (Vv V γ) = 16 := h.card_Vv_B_of_card hU hγt
  have h4 : Nat.card P * Nat.card C ≤ 4 * 2 := Nat.mul_le_mul hP hC2
  omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
