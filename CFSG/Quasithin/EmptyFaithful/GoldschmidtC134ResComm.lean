module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC134ResAux
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC134ResBlk

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open CFSG.Quasithin.C134Res
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem yNode_commute_elemCenter [Finite G] (hn : n = 4 ∨ n = 5) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hST : S ≤ T) (hTQ : T ≤ Subgroup.normalizer (qNode L S n W : Set G))
    (hTY : T ≤ Subgroup.normalizer (yNode L S n W 2 : Set G))
    (hZ : ∀ x ∈ T, (∀ t ∈ T, t * x = x * t) → x ^ 2 = 1 →
      ∀ y ∈ yNode L S n W 2, y * x = x * y) :
    ∀ y ∈ yNode L S n W 2, ∀ e ∈ elemCenter (qNode L S n W), y * e = e * y := by
  obtain ⟨l₂, hl⟩ := D.exists_hasL2 hn
  set Q := qNode L S n W with hQdef
  set Y := yNode L S n W 2 with hYdef
  have hl₂P : (l₂ : G) ∈ parab (L ⊔ S) n W 2 := D.mem_parab_of_alpha l₂ hl.mem
  have hl₂Y : (l₂ : G) ∈ Y := mem_oTwoUpper_of_odd hl₂P hl.odd
  set B : Subgroup G := Subgroup.zpowers (l₂ : G) with hBdef
  have hBY : B ≤ Y := Subgroup.zpowers_le.2 hl₂Y
  have hYP : Y ≤ parab (L ⊔ S) n W 2 := yNode_le_parab L S n W 2
  have hPQ : parab (L ⊔ S) n W 2 ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 _
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) := hYP.trans hPQ
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBY.trans hYQ
  have hYE : Y ≤ Subgroup.normalizer (elemCenter Q : Set G) := le_normalizer_elemCenter hYQ
  have hTE : T ≤ Subgroup.normalizer (elemCenter Q : Set G) := le_normalizer_elemCenter hTQ
  have hBE : B ≤ Subgroup.normalizer (elemCenter Q : Set G) := hBY.trans hYE
  have hQ2 : IsPGroup 2 ↥Q := qNode_isPGroup
  have hE2 : IsPGroup 2 ↥(elemCenter Q) := hQ2.to_le (elemCenter_le Q)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2
  have hcop : Nat.Coprime (Nat.card B) (Nat.card (elemCenter Q)) := by
    rw [hk, hBdef, Nat.card_zpowers]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    obtain ⟨j, hj⟩ := hl.odd
    omega
  have hcb : ⁅B, elemCenter Q⁆ ⊓ Subgroup.centralizer (B : Set G) = ⊥ :=
    comm_inf_centralizer_eq_bot (fun x hx y hy => elemCenter_comm hx hy) hBE hcop
  have hYB : Y ≤ Q ⊔ B := D.yNode_le_sup_zpowers hn hl
  have hset : ((Q ⊔ B : Subgroup G) : Set G) = (Q : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q B hBQ
  have hle : ⁅Y, elemCenter Q⁆ ≤ ⁅B, elemCenter Q⁆ := by
    rw [Subgroup.commutator_le]
    intro y hy e he
    have hy' : y ∈ ((Q ⊔ B : Subgroup G) : Set G) := hYB hy
    rw [hset] at hy'
    obtain ⟨q, hq, b, hb, hqb⟩ := Set.mem_mul.1 hy'
    subst hqb
    have hbe : b * e * b⁻¹ ∈ elemCenter Q := conj_mem_elemCenter (hBQ hb) he
    have hqc : q * (b * e * b⁻¹) = (b * e * b⁻¹) * q := Subgroup.mem_centralizer_iff.1 hbe.2.1 q hq
    have h2 : q * (b * e * b⁻¹) * q⁻¹ = b * e * b⁻¹ := by rw [hqc]; group
    have h3 : ⁅q * b, e⁆ = ⁅b, e⁆ := by
      simp only [commutatorElement_def, _root_.mul_inv_rev]
      calc q * b * e * (b⁻¹ * q⁻¹) * e⁻¹ = (q * (b * e * b⁻¹) * q⁻¹) * e⁻¹ := by group
        _ = b * e * b⁻¹ * e⁻¹ := by rw [h2]
    rw [h3]
    exact Subgroup.commutator_mem_commutator hb he
  have hNE : ⁅Y, elemCenter Q⁆ ≤ elemCenter Q := by
    rw [Subgroup.commutator_le]
    intro y hy e he
    have : y * e * y⁻¹ ∈ elemCenter Q := (Subgroup.mem_normalizer_iff.1 (hYE hy) e).1 he
    exact (elemCenter Q).mul_mem this ((elemCenter Q).inv_mem he)
  have hNT : ⁅Y, elemCenter Q⁆ ≤ T :=
    hNE.trans ((elemCenter_le Q).trans (D.qNode_le_S.trans hST))
  have hTN : T ≤ Subgroup.normalizer ((⁅Y, elemCenter Q⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hTY hTE
  have hN : ⁅Y, elemCenter Q⁆ = ⊥ := by
    by_contra hne
    obtain ⟨x, hxN, hx1, hx2, hxT⟩ := exists_involution_central hT hNT hTN hne
    have hxc : x ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hZ x (hNT hxN) hxT hx2 b (hBY hb)
    have : x ∈ ⁅B, elemCenter Q⁆ ⊓ Subgroup.centralizer (B : Set G) := ⟨hle hxN, hxc⟩
    rw [hcb, Subgroup.mem_bot] at this
    exact hx1 this
  intro y hy e he
  have h1 : ⁅y, e⁆ ∈ ⁅Y, elemCenter Q⁆ := Subgroup.commutator_mem_commutator hy he
  rw [hN, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end P0Setup

end CFSG.Quasithin.FLc
