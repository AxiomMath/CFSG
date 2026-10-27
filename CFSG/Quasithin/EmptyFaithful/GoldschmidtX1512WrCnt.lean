module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrKer
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Card
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Syl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Lift
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaC
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace X1512

variable {G : Type} [Group G] {n : ℕ}

theorem ineq_perm (hn : n = 3 ∨ n = 5) {B : Subgroup (Equiv.Perm (Fin n))}
    (hB : IsElemAbelian 2 B) : Nat.card B * Nat.card (fixΔ n B) ≤ 2 ^ (n - 1) := by
  obtain ⟨D, hD, hBD⟩ :=
    A4.exists_isSylowTwoOf_ge (le_top : B ≤ ⊤) (B6.isPGroup_of_isElemAbelian hB)
  exact (fin_main hn (card_sylow_perm hn hD) hBD hB).1

theorem eq_of_le_of_le_mul {a b r s : ℕ} (ha : a ≤ r) (hb : b ≤ s) (h : r * s ≤ a * b)
    (hr : 0 < r) (hs : 0 < s) : a = r ∧ b = s := by
  have h1 : a * b ≤ r * b := Nat.mul_le_mul_right b ha
  have h2 : r * b ≤ r * s := Nat.mul_le_mul_left r hb
  have h3 : 0 < a * b := lt_of_lt_of_le (Nat.mul_pos hr hs) h
  have hb0 : 0 < b := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h3
  have e1 : a * b = r * b := by omega
  have e2 : r * b = r * s := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right hb0 e1, Nat.eq_of_mul_eq_mul_left hr e2⟩

variable [Finite G] {H U L N K F₁ F₂ X₁ X₂ : Subgroup G}

theorem WrStep.count_wr (P : WrStep H U L N K F₁ F₂ X₁ X₂) (hn : n = 3 ∨ n = 5)
    [(L.subgroupOf N).Normal] [(L.subgroupOf X₁).Normal] [(L.subgroupOf X₂).Normal]
    {Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n)} {β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁}
    {β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂} (M₁ : NatMod n K L X₁ Ψ₁ β₁)
    (M₂ : NatMod n K L X₂ Ψ₂ β₂) {A : Subgroup G} (hAK : A ≤ K) (hAe : IsElemAbelian 2 A)
    (hcount : Nat.card A * Nat.card (fixSecIn A L N) =
      Nat.card ↥(A ⊓ cSecIn H L N) * Nat.card N) :
    Nat.card ((A.subgroupOf K).map Ψ₁) * Nat.card (fixΔ n ((A.subgroupOf K).map Ψ₁)) =
        2 ^ (n - 1) ∧
      Nat.card ((A.subgroupOf K).map Ψ₂) * Nat.card (fixΔ n ((A.subgroupOf K).map Ψ₂)) =
        2 ^ (n - 1) ∧
      (A.subgroupOf K).map (Ψ₁.prod Ψ₂) =
        ((A.subgroupOf K).map Ψ₁).prod ((A.subgroupOf K).map Ψ₂) := by
  have hker := P.ker_prod hn M₁ M₂
  have h1 := card_eq_inf_mul_card_map hker hAK
  have hq : 0 < Nat.card ↥(A ⊓ cSecIn H L N) := Nat.card_pos
  have hf : 0 < Nat.card (fixSecIn A L N) := Nat.card_pos
  have h3 : Nat.card ((A.subgroupOf K).map (Ψ₁.prod Ψ₂)) * Nat.card (fixSecIn A L N) =
      Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_left hq
    calc Nat.card ↥(A ⊓ cSecIn H L N) * (Nat.card ((A.subgroupOf K).map (Ψ₁.prod Ψ₂)) *
          Nat.card (fixSecIn A L N))
        = (Nat.card ↥(A ⊓ cSecIn H L N) * Nat.card ((A.subgroupOf K).map (Ψ₁.prod Ψ₂))) *
          Nat.card (fixSecIn A L N) := by ring
      _ = Nat.card A * Nat.card (fixSecIn A L N) := by rw [← h1]
      _ = Nat.card ↥(A ⊓ cSecIn H L N) * Nat.card N := hcount
  have hfN : fixSecIn A L N ≤ N := (Subgroup.closure_le N).mpr fun x hx => hx.1
  have h4 := Subgroup.relIndex_mul_card (H := fixSecIn A L N) (K := N)
  rw [inf_eq_left.mpr hfN] at h4
  have h5 : (fixSecIn A L N).relIndex N = Nat.card ((A.subgroupOf K).map (Ψ₁.prod Ψ₂)) :=
    Nat.eq_of_mul_eq_mul_right hf (h4.trans h3.symm)
  have h6 := P.relIndex_fixSecIn hAK
  rw [relIndex_fixSecIn_eq M₁ P.L_le₁ hAK, relIndex_fixSecIn_eq M₂ P.L_le₂ hAK, h5] at h6
  have hle : (A.subgroupOf K).map (Ψ₁.prod Ψ₂) ≤
      ((A.subgroupOf K).map Ψ₁).prod ((A.subgroupOf K).map Ψ₂) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨a, ha, rfl⟩⟩
  have hprod : Nat.card ↥(((A.subgroupOf K).map Ψ₁).prod ((A.subgroupOf K).map Ψ₂)) =
      Nat.card ((A.subgroupOf K).map Ψ₁) * Nat.card ((A.subgroupOf K).map Ψ₂) := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  have hρle := Subgroup.card_le_of_le hle
  rw [hprod] at hρle
  have i₁ := ineq_perm hn (isElemAbelian_map_subgroupOf Ψ₁ hAe)
  have i₂ := ineq_perm hn (isElemAbelian_map_subgroupOf Ψ₂ hAe)
  have c₁ := Subgroup.card_mul_index (fixΔ n ((A.subgroupOf K).map Ψ₁))
  have c₂ := Subgroup.card_mul_index (fixΔ n ((A.subgroupOf K).map Ψ₂))
  rw [card_coreMod hn] at c₁ c₂
  have d₁ : 0 < Nat.card (fixΔ n ((A.subgroupOf K).map Ψ₁)) := Nat.card_pos
  have d₂ : 0 < Nat.card (fixΔ n ((A.subgroupOf K).map Ψ₂)) := Nat.card_pos
  have j₁ : Nat.card ((A.subgroupOf K).map Ψ₁) ≤ (fixΔ n ((A.subgroupOf K).map Ψ₁)).index := by
    apply Nat.le_of_mul_le_mul_left _ d₁
    calc _ = Nat.card ((A.subgroupOf K).map Ψ₁) * Nat.card (fixΔ n ((A.subgroupOf K).map Ψ₁)) :=
          mul_comm _ _
      _ ≤ 2 ^ (n - 1) := i₁
      _ = _ := c₁.symm
  have j₂ : Nat.card ((A.subgroupOf K).map Ψ₂) ≤ (fixΔ n ((A.subgroupOf K).map Ψ₂)).index := by
    apply Nat.le_of_mul_le_mul_left _ d₂
    calc _ = Nat.card ((A.subgroupOf K).map Ψ₂) * Nat.card (fixΔ n ((A.subgroupOf K).map Ψ₂)) :=
          mul_comm _ _
      _ ≤ 2 ^ (n - 1) := i₂
      _ = _ := c₂.symm
  have r₁ : 0 < (fixΔ n ((A.subgroupOf K).map Ψ₁)).index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0, mul_zero] at c₁
    exact (pow_pos (by norm_num : 0 < 2) (n - 1)).ne' c₁.symm)
  have r₂ : 0 < (fixΔ n ((A.subgroupOf K).map Ψ₂)).index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0, mul_zero] at c₂
    exact (pow_pos (by norm_num : 0 < 2) (n - 1)).ne' c₂.symm)
  obtain ⟨e₁, e₂⟩ := eq_of_le_of_le_mul j₁ j₂ (h6.symm.le.trans hρle) r₁ r₂
  refine ⟨?_, ?_, ?_⟩
  · rw [e₁, mul_comm]; exact c₁
  · rw [e₂, mul_comm]; exact c₂
  · refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hprod, h6, ← e₁, ← e₂]

end X1512

end CFSG.Quasithin
