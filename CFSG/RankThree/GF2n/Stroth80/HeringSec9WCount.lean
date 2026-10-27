module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9WGeom

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem relIndex_X_LB {t : G} {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) : X.relIndex (LB M Q B) = Nat.card Z := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, -, -⟩ := hsplit
  obtain ⟨-, hrel, hLsplit⟩ := h4
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := normalizer_of_commutator_le hQX hcomm
  have hSN : LB M Q B ⊓ Y ≤ Subgroup.normalizer (X : Set G) := inf_le_right.trans hYX
  have hEN : LB M Q B ⊓ X ≤ Subgroup.normalizer (X : Set G) :=
    inf_le_right.trans Subgroup.le_normalizer
  have hLN : LB M Q B ≤ Subgroup.normalizer (X : Set G) :=
    hLsplit.le.trans (sup_le hEN hSN)
  have hLX : LB M Q B ⊔ X = (LB M Q B ⊓ Y) ⊔ X := by
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    · exact hLsplit.le.trans (sup_le (inf_le_right.trans le_sup_right) le_sup_left)
    · exact (inf_le_left.trans le_sup_left)
  have h1 : X.relIndex (LB M Q B ⊔ X) = X.relIndex (LB M Q B) :=
    relIndex_sup_right_of_le_normalizer hLN
  have h2 : X.relIndex ((LB M Q B ⊓ Y) ⊔ X) = X.relIndex (LB M Q B ⊓ Y) :=
    relIndex_sup_right_of_le_normalizer hSN
  have h3 : X.relIndex (LB M Q B ⊓ Y) = Q.relIndex (LB M Q B ⊓ Y) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have : (x : G) ∈ X ⊓ Y := ⟨hx, (Subgroup.mem_inf.mp x.2).2⟩
      rwa [hXYQ] at this
    · intro hx
      exact hQX hx
  rw [← h1, hLX, h2, h3, hrel]

theorem relIndex_centralizer_Q (hc : Ctx M Q Z B) {F : Subgroup G} (hF : IsConjB M B F) :
    (Subgroup.centralizer (F : Set G)).relIndex Q = Nat.card Z := by
  obtain ⟨m, hm, rfl⟩ := hF
  have hcF : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  obtain ⟨_, γ, M₀, _, hmodel⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨_, _, _, _, _, hcard⟩ := hcF.dictB hmodel
  have h1 := Subgroup.relIndex_mul_card
    (Subgroup.centralizer ((conjSubgroup m B : Subgroup G) : Set G)) Q
  rw [inf_comm] at h1
  have hpos : 0 < Nat.card ↥(Q ⊓ Subgroup.centralizer ((conjSubgroup m B : Subgroup G) : Set G)) :=
    Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, mul_comm]
  exact hcard

theorem card_inf_centralizer_ge (hc : Ctx M Q Z B) {F : Subgroup G} (hF : IsConjB M B F)
    {U₁ : Subgroup G} (hU₁Q : U₁ ≤ Q) (hU₁ : Nat.card Z ^ 4 ≤ Nat.card U₁) :
    Nat.card Z ^ 3 ≤ Nat.card ↥(U₁ ⊓ Subgroup.centralizer (F : Set G)) := by
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (F : Set G)) U₁
  have h2 : (Subgroup.centralizer (F : Set G)).relIndex U₁ ≤
      (Subgroup.centralizer (F : Set G)).relIndex Q :=
    Subgroup.relIndex_le_of_le_right hU₁Q Subgroup.index_ne_zero_of_finite
  rw [relIndex_centralizer_Q hc hF] at h2
  rw [inf_comm] at h1
  have hq : 0 < Nat.card Z := Nat.card_pos
  have h3 : Nat.card Z ^ 4 ≤ Nat.card Z * Nat.card ↥(U₁ ⊓ Subgroup.centralizer (F : Set G)) := by
    calc Nat.card Z ^ 4 ≤ Nat.card U₁ := hU₁
      _ = (Subgroup.centralizer (F : Set G)).relIndex U₁ *
          Nat.card ↥(U₁ ⊓ Subgroup.centralizer (F : Set G)) := h1.symm
      _ ≤ Nat.card Z * Nat.card ↥(U₁ ⊓ Subgroup.centralizer (F : Set G)) :=
        Nat.mul_le_mul_right _ h2
  have h4 : Nat.card Z * Nat.card Z ^ 3 ≤ Nat.card Z *
      Nat.card ↥(U₁ ⊓ Subgroup.centralizer (F : Set G)) := by
    rw [← pow_succ']
    exact h3
  exact Nat.le_of_mul_le_mul_left h4 hq

theorem exists_mem_not_mem_of_card {W A N L : Subgroup G} {q : ℕ} (hq : 1 < q)
    (hW : q ^ 3 ≤ Nat.card W) (hWL : W ≤ L) (hA : A.relIndex L ≤ q)
    (hN : Nat.card ↥(W ⊓ A ⊓ N) ≤ q) : ∃ x ∈ W ⊓ A, x ∉ N := by
  by_contra hno
  push Not at hno
  have hle : W ⊓ A ≤ N := fun x hx => hno x hx
  have hWAN : W ⊓ A ⊓ N = W ⊓ A := inf_eq_left.mpr hle
  rw [hWAN] at hN
  have h1 := Subgroup.relIndex_mul_card A W
  have h2 : A.relIndex W ≤ A.relIndex L :=
    Subgroup.relIndex_le_of_le_right hWL Subgroup.index_ne_zero_of_finite
  rw [inf_comm] at h1
  have h3 : Nat.card W ≤ q * q := by
    calc Nat.card W = A.relIndex W * Nat.card ↥(W ⊓ A) := h1.symm
      _ ≤ q * q := Nat.mul_le_mul (h2.trans hA) hN
  have h4 : q * q < q ^ 3 := by
    have : q ^ 3 = q * q * q := by ring
    rw [this]
    exact lt_mul_of_one_lt_right (by positivity) hq
  omega

theorem exists_swap_point (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {F : Subgroup G}
    (hF : IsConjB M B F) {U₁ : Subgroup G} (hU₁Q : U₁ ≤ Q)
    (hU₁ : Nat.card Z ^ 4 ≤ Nat.card U₁) {g : G} (hgZ : conjSubgroup g Z = F)
    (hgQB : conjSubgroup g (QB B) = Q) (hgQ : conjSubgroup g Q = QB F)
    (hcase : U₁ ⊓ QB F ≤ Z) :
    ∃ d ∈ U₁, d ∈ Subgroup.centralizer (F : Set G) ∧ d ∉ QB F ∧
      g⁻¹ * d * g ∈ LB M Q B ⊓ X := by
  set W : Subgroup G := U₁ ⊓ Subgroup.centralizer (F : Set G) with hW
  set W' : Subgroup G := conjSubgroup g⁻¹ W with hW'
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hWcard : Nat.card Z ^ 3 ≤ Nat.card W' := by
    rw [hW', card_conjSubgroup]
    exact card_inf_centralizer_ge hc hF hU₁Q hU₁
  have hW'mem : ∀ x ∈ W', g * x * g⁻¹ ∈ W := by
    intro x hx
    rw [hW', mem_conjSubgroup] at hx
    simpa using hx
  have hW'L : W' ≤ LB M Q B := by
    intro x hx
    have hxW := hW'mem x hx
    have := swap_conj_mem_LB hc hgZ hgQB (hU₁Q hxW.1) hxW.2
    simpa [mul_assoc] using this
  have hidx : (LB M Q B ⊓ X).relIndex (LB M Q B) ≤ Nat.card Z := by
    rw [Subgroup.inf_relIndex_left, relIndex_X_LB hsplit h4]
  have hcap : Nat.card ↥(W' ⊓ (LB M Q B ⊓ X) ⊓ Q) ≤ Nat.card Z := by
    have hle : W' ⊓ (LB M Q B ⊓ X) ⊓ Q ≤ conjSubgroup g⁻¹ Z := by
      intro x hx
      obtain ⟨⟨hxW', -⟩, hxQ⟩ := hx
      have hxW := hW'mem x hxW'
      have hdQF : g * x * g⁻¹ ∈ QB F := by
        have := (swap_conj_mem_Q_iff hgQ (g * x * g⁻¹)).mp
        apply this
        simpa [mul_assoc] using hxQ
      have hdZ : g * x * g⁻¹ ∈ Z := hcase ⟨hxW.1, hdQF⟩
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hdZ
    calc Nat.card ↥(W' ⊓ (LB M Q B ⊓ X) ⊓ Q) ≤ Nat.card ↥(conjSubgroup g⁻¹ Z) :=
        Subgroup.card_le_of_le hle
      _ = Nat.card Z := card_conjSubgroup _ _
  obtain ⟨x, ⟨hxW', hxLX⟩, hxQ⟩ := exists_mem_not_mem_of_card hq hWcard hW'L hidx hcap
  have hxW := hW'mem x hxW'
  refine ⟨g * x * g⁻¹, hxW.1, hxW.2, ?_, ?_⟩
  · intro hdQF
    exact hxQ (by simpa [mul_assoc] using (swap_conj_mem_Q_iff hgQ (g * x * g⁻¹)).mpr hdQF)
  · simpa [mul_assoc] using hxLX

end HS9

end CFSG.RankThree.GF2n.Stroth80
