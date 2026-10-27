module

public import CFSG.RankThree.GF2n.Stroth80.Conj2
public import CFSG.RankThree.GF2n.Stroth80.QuadWitt
public import CFSG.RankThree.GF2n.Stroth80.Sec25a
public import CFSG.RankThree.GF2n.Stroth80.Swap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf_of_le_normalizer {L E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(L ⊔ E : Subgroup G) * Nat.card ↥(L ⊓ E : Subgroup G) =
      Nat.card L * Nat.card E := by
  rw [sup_comm, inf_comm, mul_comm (Nat.card L)]
  have := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hEN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient E L hEN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf E)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf (E ⊔ L))
  have h3 : Nat.card (L.subgroupOf E) = Nat.card (E ⊓ L : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (L.subgroupOf (E ⊔ L)) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

variable [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.card_L0 (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) :
    Nat.card ↥(QB B ⊓ Subgroup.centralizer (Z : Set G)) = Nat.card Z ^ (2 * w) := by
  obtain ⟨g, hg⟩ := hc.conj
  have h1 := hc.card_QB_eq
  have hQBcard : Nat.card (QB B) = Nat.card Q := by
    rw [(Ctx.QB_eq hc hg).2, card_conjSubgroup]
  rw [hQBcard] at h1
  unfold Width at hw
  rw [hw, pow_succ] at h1
  have hpos : 0 < Nat.card Z := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

theorem Ctx.card_LB_mul (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) :
    Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) = Nat.card Q * Nat.card Z ^ (2 * w) := by
  have hLM : QB B ⊓ M ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    hc.hyp.Q_normal.2 hx.2
  have h1 := card_sup_mul_card_inf_of_le_normalizer hLM
  have h2 : Q ⊓ (QB B ⊓ M) = Q ⊓ QB B := by
    refine le_antisymm (fun x hx => ⟨hx.1, hx.2.1⟩) fun x hx => ⟨hx.1, hx.2, ?_⟩
    exact hc.hyp.Q_normal.1 hx.1
  rw [h2] at h1
  have h3 : Nat.card ↥(QB B ⊓ M) = Nat.card Z ^ (2 * w) := by
    rw [hc.QB_inf_M_eq]; exact hc.card_L0 hw
  rw [h3] at h1
  exact h1

theorem Ctx.card_inf_QB_le (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) :
    Nat.card ↥(Q ⊓ QB B) ≤ Nat.card Z ^ (w + 1) := by
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  have hK : 1 < Nat.card (GaloisField 2 m) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hdim := h.finrank_E hw hK
  have hSQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hZS : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hsing : ∀ e ∈ M₀.img (Q ⊓ QB B), M₀.Qf e = 0 :=
    (M₀.isElemAbelian_iff h.reg hSQ).mp hc.inf_QB_elemAbelian
  have h1 := M₀.card_eq hSQ hZS
  have h2 := Tim79.QuadModel.card_le_of_totallySingular M₀ (U := M₀.img (Q ⊓ QB B)) hsing hdim
  rw [h.card] at h2
  calc Nat.card ↥(Q ⊓ QB B) = Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) := h1
    _ ≤ Nat.card Z * Nat.card Z ^ w := Nat.mul_le_mul_left _ h2
    _ = Nat.card Z ^ (w + 1) := by ring

theorem Ctx.card_LB_ge (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) (hw1 : 1 ≤ w) :
    Nat.card Q * Nat.card Z ^ (w - 1) ≤ Nat.card (LB M Q B) := by
  have h1 := hc.card_LB_mul hw
  have h2 := hc.card_inf_QB_le hw
  have hpos : 0 < Nat.card Z ^ (w + 1) := pow_pos Nat.card_pos _
  have h3 : Nat.card Q * Nat.card Z ^ (w - 1) * Nat.card Z ^ (w + 1) ≤
      Nat.card (LB M Q B) * Nat.card Z ^ (w + 1) := by
    calc Nat.card Q * Nat.card Z ^ (w - 1) * Nat.card Z ^ (w + 1)
        = Nat.card Q * Nat.card Z ^ (2 * w) := by
          rw [mul_assoc, ← pow_add]; congr 2; omega
      _ = Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) := h1.symm
      _ ≤ Nat.card (LB M Q B) * Nat.card Z ^ (w + 1) := Nat.mul_le_mul_left _ h2
  exact Nat.le_of_mul_le_mul_right h3 hpos

end CFSG.RankThree.GF2n.Stroth80
