module

public import CFSG.Quasithin.Background.F918C12
public import CFSG.Quasithin.Background.InternalSecAlt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem card_statedSL_two_eq {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem card_statedSL_three_eq {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 3 K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three K

theorem card_statedSL_three_ne_six {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 3 K) ≠ 6 := by
  rw [card_statedSL_three_eq]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 : 2 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 2 ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq 2
  have h3 : 2 ^ 3 * ((2 ^ 2 - 1) * (2 ^ 3 - 1)) ≤
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h1 1))
  intro h
  rw [h] at h3
  norm_num at h3

theorem card_eq_two_of_statedSL_two {K : Type} [Field K] [Finite K]
    (h : Nat.card ↥(StatedSL 2 K) = 6) : Nat.card K = 2 := by
  rw [card_statedSL_two_eq] at h
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases Nat.lt_or_ge (Nat.card K) 3 with h2 | h3
  · omega
  · exfalso
    have h1 : 3 ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left h3 2
    have h4 : 3 * (3 ^ 2 - 1) ≤ Nat.card K * (Nat.card K ^ 2 - 1) :=
      Nat.mul_le_mul h3 (Nat.sub_le_sub_right h1 1)
    norm_num at h4
    omega

section Piece

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_of_realizesVia_nat_two {K : Type} [Field K] [Finite K] {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : ↥(StatedSL 2 K) →* ↥H}
    (h : (FFModel.nat (StatedSL 2 K)).RealizesVia H U Z π) :
    Nat.card ↥U = Nat.card K ^ 2 * Nat.card ↥Z := by
  obtain ⟨-, hZU, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hker] at h1
  have h2 : Nat.card ↥(Z.subgroupOf U) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  have h3 : Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤) = Nat.card K ^ 2 := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤)
    have e2 : Nat.card ↥((⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤) = 1 := by
      rw [Subgroup.bot_subgroupOf, Subgroup.card_bot]
    have e3 : Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) = Nat.card K ^ 2 := by
      rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_fin]
    rw [e2, mul_one, e3] at e1
    exact e1.symm
  show Nat.card ↥U = _
  rw [h1, h2]
  exact congrArg (· * Nat.card ↥Z) h3

omit [Finite V] in
theorem piece_of_card_six {Gi : Subgroup (MulAut V)} {Wi C : Subgroup V}
    (h6 : Nat.card ↥Gi = 6) (hp : B56Piece Gi Wi C) :
    Wi = commV Gi ⊔ C ∧ Nat.card ↥Wi = 4 * Nat.card ↥C := by
  have hord : ∀ {Γ : Type} [Group Γ] (π : Γ →* ↥Gi), Function.Injective π →
      Function.Surjective π → Nat.card Γ = 6 := fun π hi hs => by
    rw [Nat.card_congr (Equiv.ofBijective π ⟨hi, hs⟩), h6]
  rcases hp with ⟨hW, ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩⟩ |
      ⟨hW, m, K, _, _, hK, I, π, -, -, -, hR⟩ | ⟨⟨e⟩, -⟩
  · refine ⟨hW, ?_⟩
    have hi := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    have hK2 := card_eq_two_of_statedSL_two (hord π hi hπ.1)
    rw [card_of_realizesVia_nat_two hπ, hK2]
    norm_num
  · exfalso
    have hi := realizesVia_injective_of_faithful (InternalSec.symDn_faithful (by norm_num)) hπ
    have h := hord π hi hπ.1
    simp only [FFModel.symDn, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
    norm_num [Nat.factorial] at h
  · exfalso
    have hi := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    exact card_statedSL_three_ne_six (hord π hi hπ.1)
  · exfalso
    have hi := realizesVia_injective_of_faithful (FFModel.nat_faithful _) (hR 0)
    exact card_statedSL_three_ne_six (hord π hi (hR 0).1)
  · exfalso
    have h1 := Nat.card_congr e.toEquiv
    rw [h6, card_statedSL_three_eq, Nat.card_zmod] at h1
    norm_num at h1

end Piece

end CFSG.Quasithin.H13.A5
