module

public import CFSG.RankThree.GF2n.Smith81.S81BNLine
public import CFSG.RankThree.GF2n.Smith81.S81BCount

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube

variable {G : Type} [Group G]

@[expose] def ElemBoundE3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ [(Q.subgroupOf M).Normal], ∀ n : ℕ, Width Q Z n →
      ∀ A : Subgroup (↥M ⧸ Q.subgroupOf M), A ≤ bar M Q (Lgen M (LB M Q B)) →
        IsElemAbelian 2 A → Nat.card A ≤ Nat.card Z ^ (n - 1)

@[expose] def Smith28aE3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥

theorem le_QB_of_sum_mem_E3L [Finite G]
    (hFE1 : Smith24E3LUniformStatement) (hTacit : ETacitE3LStatement) (h34 : Stroth34Statement)
    {M Q Z B : Subgroup G} (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B)
    (h3L : InCaseE3L M Q Z B) {X Y D : Subgroup G} (hX : Ctx M Q Z X) (hY : Ctx M Q Z Y)
    (hD : Ctx M Q Z D) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y ∈ D) (hxy1 : x * y ≠ 1) (hne : Y ⊔ Z ≠ X ⊔ Z) : Y ≤ QB X := by
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3L K γ M₀ hg
  have hw : Width Q Z 10 := by
    obtain ⟨t, -, h⟩ := h3L
    exact h.1
  have hTac := hTacit G M Q Z B IH hc h3L X hX
  have hcard : Nat.card ↥(Q ⊓ QB X) = Nat.card Z ^ (10 + 1) :=
    (stroth_3_5 h34 hX hw (by norm_num) hTac.1 hTac.2).2.2.2
  exact d.le_QB_of_sum_mem hg a5MinuscGeom a5MinuscLine hX hY hD hcard hx hy hx1 hy1 hxy hxy1 hne

private theorem exists_sit_of_isConj {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z x : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hzx : IsConj z x) (hM : x ∈ M) (hQ : x ∉ Q) :
    ∃ X : Subgroup G, Sit M Q Z X x := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hzx
  exact ⟨_, Sit.of_conj H hz hz1 hM hQ⟩

end CFSG.RankThree.GF2n.Smith81
