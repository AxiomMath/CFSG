module

public import CFSG.RankThree.GF2n.Tim78S48EndForm
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

structure CSplit (B C L₀ : Subgroup G) : Prop where
  le_C : L₀ ≤ C
  inf_B : B ⊓ L₀ = ⊥
  C_le_sup : C ≤ B ⊔ L₀

theorem CSplit.unique {B C L₀ : Subgroup G} (S : CSplit B C L₀) {β β' l l' : G} (hβ : β ∈ B)
    (hβ' : β' ∈ B) (hl : l ∈ L₀) (hl' : l' ∈ L₀) (h : β * l = β' * l') : β = β' ∧ l = l' := by
  have h1 : β'⁻¹ * β = l' * l⁻¹ := by
    have : β'⁻¹ * (β * l) * l⁻¹ = β'⁻¹ * (β' * l') * l⁻¹ := by rw [h]
    simpa [mul_assoc] using this
  have h2 : β'⁻¹ * β ∈ B ⊓ L₀ :=
    ⟨B.mul_mem (B.inv_mem hβ') hβ, h1 ▸ L₀.mul_mem hl' (L₀.inv_mem hl)⟩
  rw [S.inf_B, Subgroup.mem_bot] at h2
  have h3 : β = β' := by
    have : β = β' * (β'⁻¹ * β) := by group
    rw [this, h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

namespace EndgameData

variable [Finite G] {M B Q P T : Subgroup G} {g : G}
  {C L : Subgroup G} (E : EndgameData M B Q P T g C L) (H : Hyp4 M B Q P T)
include E H

variable {b' : G} {L₀ : Subgroup G}

omit H in
theorem card_C_split (S : CSplit B C L₀) : Nat.card C = Nat.card B * Nat.card L₀ := by
  have hnorm : B ≤ Subgroup.normalizer (L₀ : Set G) := le_normalizer_of_comm fun x hx y hy =>
    E.comm_L (E.B_le_L hx) (E.C_le_L (S.le_C hy))
  have h := PartTwo.Sec6.card_sup_mul_card_inf hnorm
  rw [S.inf_B, Subgroup.card_bot, mul_one] at h
  have : B ⊔ L₀ = C := le_antisymm (sup_le E.B_le_C S.le_C) S.C_le_sup
  rwa [this] at h

theorem exists_dec (hb' : b' ∈ conjSubgroup g B) (S : CSplit B C L₀) :
    ∃ (Θ : ↥P →* ↥L₀) (kp : ↥P → ↥B),
      (∀ y : ↥P, ⁅b', (y : G)⁆ = (kp y : G) * (Θ y : G)) ∧
      ∀ y y' : ↥P, (kp (y * y') : G) = kp y * kp y' * ⁅(y : G), ⁅b', (y' : G)⁆⁆ := by
  classical
  have hLL : ∀ l ∈ L₀, l ∈ L := fun l hl => E.C_le_L (S.le_C hl)
  have hnorm : L₀ ≤ Subgroup.normalizer (B : Set G) := le_normalizer_of_comm fun x hx y hy =>
    E.comm_L (hLL x hx) (E.B_le_L hy)
  have hdec : ∀ y : ↥P, ∃ β : ↥B, ∃ l : ↥L₀, ⁅b', (y : G)⁆ = (β : G) * (l : G) := by
    intro y
    obtain ⟨β, hβ, l, hl, h⟩ :=
      exists_mul_of_mem_sup hnorm (S.C_le_sup (E.u_mem hb' (H.P_le_Q y.2)))
    exact ⟨⟨β, hβ⟩, ⟨l, hl⟩, h⟩
  choose kp l hkl using hdec
  have key : ∀ y y' : ↥P, (kp (y * y') : G) = kp y * ⁅(y : G), ⁅b', (y' : G)⁆⁆ * kp y' ∧
      (l (y * y') : G) = l y * l y' := by
    intro y y'
    have hD : ⁅(y : G), ⁅b', (y' : G)⁆⁆ ∈ B :=
      E.D_mem H hb' (H.P_le_Q y.2) (H.P_le_Q y'.2)
    have e1 : ⁅b', ((y * y' : ↥P) : G)⁆ = (kp y * ⁅(y : G), ⁅b', (y' : G)⁆⁆ * kp y' : G) *
        ((l y * l y' : ↥L₀) : G) := by
      have hlD : (l y : G) * ⁅(y : G), ⁅b', (y' : G)⁆⁆ = ⁅(y : G), ⁅b', (y' : G)⁆⁆ * l y :=
        E.comm_L (hLL _ (l y).2) (E.B_le_L hD)
      have hlk : (l y : G) * kp y' = kp y' * l y :=
        E.comm_L (hLL _ (l y).2) (E.B_le_L (kp y').2)
      have e0 : ⁅b', ((y * y' : ↥P) : G)⁆ =
          ⁅b', (y : G)⁆ * (⁅(y : G), ⁅b', (y' : G)⁆⁆ * ⁅b', (y' : G)⁆) := by
        simp only [Subgroup.coe_mul, commutatorElement_def]; group
      generalize ⁅(y : G), ⁅b', (y' : G)⁆⁆ = D at e0 hlD hD ⊢
      rw [e0, hkl y, hkl y']
      calc (kp y : G) * l y * (D * (kp y' * l y'))
          = kp y * ((l y : G) * D) * (kp y' * l y') := by group
        _ = kp y * (D * l y) * (kp y' * l y') := by rw [hlD]
        _ = kp y * D * ((l y : G) * kp y') * l y' := by group
        _ = kp y * D * (kp y' * l y) * l y' := by rw [hlk]
        _ = (kp y * D * kp y') * ((l y * l y' : ↥L₀) : G) := by
          simp only [Subgroup.coe_mul]; group
    have e2 := hkl (y * y')
    have hmem : (kp y : G) * ⁅(y : G), ⁅b', (y' : G)⁆⁆ * kp y' ∈ B :=
      B.mul_mem (B.mul_mem (kp y).2 hD) (kp y').2
    exact S.unique (kp (y * y')).2 hmem (l (y * y')).2 (l y * l y').2 (e2.symm.trans e1)
  refine ⟨{ toFun := l, map_one' := ?_, map_mul' := fun y y' => Subtype.ext (key y y').2 }, kp,
    hkl, fun y y' => ?_⟩
  · have h1 := hkl 1
    have h2 : (⁅b', (((1 : ↥P)) : G)⁆) = 1 * 1 := by simp
    have := S.unique (kp 1).2 B.one_mem (l 1).2 L₀.one_mem
      (by rw [← h1, h2] : (kp 1 : G) * (l 1 : G) = 1 * 1)
    exact Subtype.ext this.2
  · have hD : ⁅(y : G), ⁅b', (y' : G)⁆⁆ ∈ B :=
      E.D_mem H hb' (H.P_le_Q y.2) (H.P_le_Q y'.2)
    rw [(key y y').1]
    have := H.B_comm hD (kp y').2
    calc (kp y : G) * ⁅(y : G), ⁅b', (y' : G)⁆⁆ * kp y'
        = kp y * (⁅(y : G), ⁅b', (y' : G)⁆⁆ * kp y') := by group
      _ = kp y * (kp y' * ⁅(y : G), ⁅b', (y' : G)⁆⁆) := by rw [this]
      _ = kp y * kp y' * ⁅(y : G), ⁅b', (y' : G)⁆⁆ := by group

section Char

variable {Θ : ↥P →* ↥L₀} {kp : ↥P → ↥B}

theorem Theta_eq_one_iff (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1) (S : CSplit B C L₀)
    (hΘ : ∀ y : ↥P, ⁅b', (y : G)⁆ = (kp y : G) * (Θ y : G)) (y : ↥P) :
    Θ y = 1 ↔ (y : G) ∈ C := by
  constructor
  · intro h
    refine E.mem_C_of_comm_mem_B H hb' hb'1 y.2 ?_
    rw [hΘ y, h]
    simpa using (kp y).2
  · intro h
    have h1 : ⁅b', (y : G)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (E.C_cent _ h b' hb').symm
    have := S.unique (kp y).2 B.one_mem (Θ y).2 L₀.one_mem
      (by rw [← hΘ y, h1, mul_one] : (kp y : G) * (Θ y : G) = 1 * 1)
    exact Subtype.ext this.2

theorem Theta_surjective (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1) (S : CSplit B C L₀)
    (hΘ : ∀ y : ↥P, ⁅b', (y : G)⁆ = (kp y : G) * (Θ y : G)) : Function.Surjective Θ := by
  have hker : Θ.ker = C.subgroupOf P := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact E.Theta_eq_one_iff H hb' hb'1 S hΘ y
  have h2 : C.relIndex P = Nat.card L₀ := by
    have := E.card_C
    rw [E.card_C_split S] at this
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos this).symm
  have h3 := Subgroup.index_ker Θ
  rw [hker] at h3
  have h4 : Nat.card Θ.range = Nat.card L₀ := by rw [← h3]; exact h2
  have hr : Θ.range = ⊤ := Subgroup.eq_top_of_card_eq _ h4
  intro l
  have : l ∈ Θ.range := by rw [hr]; trivial
  exact this

theorem Theta_conj (hb' : b' ∈ conjSubgroup g B) (S : CSplit B C L₀)
    (hΘ : ∀ y : ↥P, ⁅b', (y : G)⁆ = (kp y : G) * (Θ y : G)) {x : G} (hxb' : x * b' = b' * x)
    (hxB : ∀ β ∈ B, x * β = β * x) (hxL₀ : x ∈ Subgroup.normalizer (L₀ : Set G))
    {y y₁ : ↥P} (hy₁ : (y₁ : G) = x * y * x⁻¹) :
    (Θ y₁ : G) = x * Θ y * x⁻¹ ∧ (kp y₁ : G) = kp y := by
  have e1 : ⁅b', (y₁ : G)⁆ = x * ⁅b', (y : G)⁆ * x⁻¹ := by
    rw [hy₁]; exact u_conj hxb' _
  have hxk : x * (kp y : G) * x⁻¹ = kp y := by rw [hxB _ (kp y).2]; group
  have hxΘ : x * (Θ y : G) * x⁻¹ ∈ L₀ :=
    (Subgroup.mem_normalizer_iff.mp hxL₀ _).mp (Θ y).2
  have e2 : ⁅b', (y₁ : G)⁆ = (kp y : G) * (x * Θ y * x⁻¹) := by
    rw [e1, hΘ y]
    calc x * ((kp y : G) * Θ y) * x⁻¹ = (x * kp y * x⁻¹) * (x * Θ y * x⁻¹) := by group
      _ = _ := by rw [hxk]
  have := S.unique (kp y₁).2 (kp y).2 (Θ y₁).2 hxΘ ((hΘ y₁).symm.trans e2)
  exact ⟨this.2, this.1⟩

theorem D_eq_of_Theta (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1) (S : CSplit B C L₀)
    (hΘ : ∀ y : ↥P, ⁅b', (y : G)⁆ = (kp y : G) * (Θ y : G)) {y y₁ y' y₁' : ↥P}
    (h : Θ y = Θ y₁) (h' : Θ y' = Θ y₁') :
    ⁅(y₁ : G), ⁅b', (y₁' : G)⁆⁆ = ⁅(y : G), ⁅b', (y' : G)⁆⁆ := by
  have hc : ∀ {z z₁ : ↥P}, Θ z = Θ z₁ → (z⁻¹ * z₁ : ↥P) ∈ C.subgroupOf P := by
    intro z z₁ hz
    have : Θ (z⁻¹ * z₁) = 1 := by rw [map_mul, map_inv, hz, inv_mul_cancel]
    rwa [Subgroup.mem_subgroupOf, ← E.Theta_eq_one_iff H hb' hb'1 S hΘ]
  have h1 : (y₁ : G) = y * ((y⁻¹ * y₁ : ↥P) : G) := by simp
  have h2 : (y₁' : G) = y' * ((y'⁻¹ * y₁' : ↥P) : G) := by simp
  rw [h2, E.D_mul_C_right hb' (Subgroup.mem_subgroupOf.mp (hc h')), h1,
    E.D_mul_C_left H hb' (H.P_le_Q y.2) (Subgroup.mem_subgroupOf.mp (hc h)) (H.P_le_Q y'.2)]

theorem kp_eq_of_Theta (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1) (S : CSplit B C L₀)
    (hΘ : ∀ y : ↥P, ⁅b', (y : G)⁆ = (kp y : G) * (Θ y : G)) {y y₁ : ↥P} (h : Θ y = Θ y₁) :
    kp y = kp y₁ := by
  have hc : (y⁻¹ * y₁ : ↥P) ∈ C.subgroupOf P := by
    have : Θ (y⁻¹ * y₁) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rwa [Subgroup.mem_subgroupOf, ← E.Theta_eq_one_iff H hb' hb'1 S hΘ]
  have h1 : (y₁ : G) = y * ((y⁻¹ * y₁ : ↥P) : G) := by simp
  have e : ⁅b', (y₁ : G)⁆ = ⁅b', (y : G)⁆ := by
    rw [h1, E.u_mul_C_right hb' (Subgroup.mem_subgroupOf.mp hc)]
  have := S.unique (kp y₁).2 (kp y).2 (Θ y₁).2 (Θ y).2 ((hΘ y₁).symm.trans (e.trans (hΘ y)))
  exact Subtype.ext this.1.symm

end Char

end EndgameData

end CFSG.RankThree.GF2n.Tim78
