module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Def
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public section

namespace CFSG.RankThree.GF2n.Smith81.D6X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X


abbrev b0 : Fin e7Data.d := ⟨8, by decide⟩

theorem pr_b0_theta : pr b0 theta = 0 := by
  decide +kernel

theorem phiP_card : ((rootFinset .E7).filter fun γ =>
    MinData.toWeight γ ⬝ᵥ theta = 0 ∧ pr b0 γ = 1).card = 15 := by
  decide +kernel

private def d6fin_NW (a b : Fin e7Data.d) : Prop :=
  ∀ k : Fin 126, pr a ((Tag.rootCertificate .E7).root k) = 1 →
    pr b ((Tag.rootCertificate .E7).root k) = -1 →
      e7Data.wt a = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k)

private instance d6fin_decNW (a b : Fin e7Data.d) : Decidable (d6fin_NW a b) := by
  unfold d6fin_NW; infer_instance

private theorem d6fin_NW_iff (a b : Fin e7Data.d) : NearW a b ↔ d6fin_NW a b :=
  nearW_iff a b

private theorem d6fin_key_unique : ∀ b : Fin e7Data.d, pr b theta = 0 → ¬ d6fin_NW b0 b →
    e7Data.wt b ≠ -e7Data.wt b0 →
    ∀ k k' : Fin 126, pr b0 ((Tag.rootCertificate .E7).root k) = 1 →
      pr b ((Tag.rootCertificate .E7).root k) = 1 →
      pr b0 ((Tag.rootCertificate .E7).root k') = 1 →
      pr b ((Tag.rootCertificate .E7).root k') = 1 →
      (Tag.rootCertificate .E7).root k = (Tag.rootCertificate .E7).root k' := by
  decide +kernel

theorem spec0_unique (b : Fin e7Data.d) (hb0 : pr b theta = 0) (hb : SpecW b0 b)
    (γ γ' : Fin (Tag.rank .E7) → ℤ) (hγ : IsRoot .E7 γ) (hγ' : IsRoot .E7 γ') (h1 : pr b0 γ = 1)
    (h2 : pr b γ = 1) (h3 : pr b0 γ' = 1) (h4 : pr b γ' = 1) : γ = γ' := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hb' : ¬ NearW b0 b ∧ b ≠ opp b0 := hb
  have hwt : e7Data.wt b ≠ -e7Data.wt b0 := fun h => hb'.2 (opp_eq h).symm
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
  obtain ⟨k', hk', rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ'
  exact d6fin_key_unique b hb0 (fun h => hb'.1 ((d6fin_NW_iff b0 b).2 h)) hwt ⟨k, by omega⟩
    ⟨k', by omega⟩ h1 h2 h3 h4

private def d6fin_t1 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 9, 0, 0, 9, 9, 0, 11, 9,
    0, 13, 11, 9, 0, 13, 11, 0, 13, 14, 0, 16, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def d6fin_t2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 23, 0, 0, 26, 27, 0, 26,
    30, 0, 26, 30, 33, 0, 30, 33, 0, 33, 33, 0, 33, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def d6fin_c1 (b : Fin e7Data.d) : Fin e7Data.d :=
  ⟨d6fin_t1.getD b.val 0 % e7Data.d, Nat.mod_lt _ (by decide)⟩

private def d6fin_c2 (b : Fin e7Data.d) : Fin e7Data.d :=
  ⟨d6fin_t2.getD b.val 0 % e7Data.d, Nat.mod_lt _ (by decide)⟩

private theorem d6fin_key_witness : ∀ b : Fin e7Data.d, pr b theta = 0 → ¬ d6fin_NW b0 b →
    e7Data.wt b ≠ -e7Data.wt b0 →
      pr (d6fin_c1 b) theta = 0 ∧ pr (d6fin_c2 b) theta = 0 ∧
        d6fin_NW b0 (d6fin_c1 b) ∧ d6fin_NW b0 (d6fin_c2 b) ∧
        d6fin_NW b (d6fin_c1 b) ∧ d6fin_NW b (d6fin_c2 b) ∧
        ¬ d6fin_NW (d6fin_c1 b) (d6fin_c2 b) ∧
        e7Data.wt (d6fin_c2 b) ≠ -e7Data.wt (d6fin_c1 b) := by
  decide +kernel

theorem spec0_witness (b : Fin e7Data.d) (hb0 : pr b theta = 0) (hb : SpecW b0 b) :
    ∃ c₁ c₂ : Fin e7Data.d, pr c₁ theta = 0 ∧ pr c₂ theta = 0 ∧ NearW b0 c₁ ∧ NearW b0 c₂ ∧
      NearW b c₁ ∧ NearW b c₂ ∧ ¬ NearW c₁ c₂ ∧ c₂ ≠ opp c₁ := by
  have hb' : ¬ NearW b0 b ∧ b ≠ opp b0 := hb
  have hwt : e7Data.wt b ≠ -e7Data.wt b0 := fun h => hb'.2 (opp_eq h).symm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
    d6fin_key_witness b hb0 (fun h => hb'.1 ((d6fin_NW_iff b0 b).2 h)) hwt
  refine ⟨d6fin_c1 b, d6fin_c2 b, g1, g2, (d6fin_NW_iff _ _).2 g3, (d6fin_NW_iff _ _).2 g4,
    (d6fin_NW_iff _ _).2 g5, (d6fin_NW_iff _ _).2 g6, fun h => g7 ((d6fin_NW_iff _ _).1 h), ?_⟩
  intro h
  apply g8
  rw [h, wt_opp]

private theorem d6fin_nearP_fin : ∀ b : Fin e7Data.d, pr b theta = 0 →
    (∀ k : Fin 126, MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 →
      pr b0 ((Tag.rootCertificate .E7).root k) = 1 →
      pr b ((Tag.rootCertificate .E7).root k) = -1 →
        e7Data.wt b0 = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k)) →
    ∀ k : Fin 126, pr b0 ((Tag.rootCertificate .E7).root k) = 1 →
      pr b ((Tag.rootCertificate .E7).root k) = -1 →
        e7Data.wt b0 = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k) := by
  decide +kernel

theorem nearP_iff (b : Fin e7Data.d) (hb0 : pr b theta = 0) :
    (∀ γ : Fin (Tag.rank .E7) → ℤ, γ ∈ Perp → pr b0 γ = 1 → pr b γ = -1 →
      e7Data.wt b0 = e7Data.wt b + MinData.toWeight γ) ↔ NearW b0 b := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  constructor
  · intro h
    rw [nearW_iff]
    refine d6fin_nearP_fin b hb0 (fun k hk h1 h2 => h _ ?_ h1 h2)
    exact (show IsRoot .E7 ((Tag.rootCertificate .E7).root k) ∧
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 from
        ⟨RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega), hk⟩)
  · intro h γ hγ h1 h2
    exact h γ (perp_iff.1 hγ).1 h1 h2

theorem dom0 : ∀ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ → MinData.toWeight γ ⬝ᵥ theta = 0 →
    0 < height γ → pr b0 γ ≠ -1 := by
  refine (forall_isRoot_iff fun γ => MinData.toWeight γ ⬝ᵥ theta = 0 → 0 < height γ →
    pr b0 γ ≠ -1).2 ?_
  decide +kernel

theorem exists_idx0_move : ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ →
    MinData.toWeight δ ⬝ᵥ theta = 0 → ∃ b : Fin e7Data.d, pr b theta = 0 ∧ pr b δ = -1 := by
  refine (forall_isRoot_iff fun δ => MinData.toWeight δ ⬝ᵥ theta = 0 →
    ∃ b : Fin e7Data.d, pr b theta = 0 ∧ pr b δ = -1).2 ?_
  decide +kernel

def weightWordsD6 : List (List ℕ) := [[], [], [], [], [], [], [], [], [], [1], [], [1, 3], [], [1, 3, 2], [1, 3, 4], [], [1, 3, 2, 4],
    [1, 3, 4, 5], [], [1, 3, 2, 4, 3], [1, 3, 2, 4, 5], [1, 3, 4, 5, 6], [1, 3, 2, 4, 3, 1],
    [1, 3, 2, 4, 3, 5], [1, 3, 2, 4, 5, 6], [1, 3, 2, 4, 3, 1, 5], [1, 3, 2, 4, 3, 5, 4],
    [1, 3, 2, 4, 3, 5, 6], [1, 3, 2, 4, 3, 1, 5, 4], [1, 3, 2, 4, 3, 1, 5, 6], [1, 3, 2, 4, 3, 5, 4, 6],
    [1, 3, 2, 4, 3, 1, 5, 4, 3], [1, 3, 2, 4, 3, 1, 5, 4, 6], [1, 3, 2, 4, 3, 5, 4, 6, 5],
    [1, 3, 2, 4, 3, 1, 5, 4, 3, 2], [1, 3, 2, 4, 3, 1, 5, 4, 3, 6], [1, 3, 2, 4, 3, 1, 5, 4, 6, 5], [],
    [1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6], [1, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5], [],
    [1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5], [1, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4], [],
    [1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4], [], [1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3], [],
    [1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1], [], [], [], [], [], [], []]

theorem weightWordsD6_correct : ∀ a : Fin e7Data.d, pr a theta = 0 →
    actWord (weightWordsD6.getD a []) 8 = a := by
  unfold actWord weightWordsD6 letter
  decide +kernel

theorem weightWordsD6_letters : ∀ a : Fin e7Data.d, ∀ i ∈ weightWordsD6.getD a [], 1 ≤ i % 7 := by
  unfold weightWordsD6
  decide +kernel

end CFSG.RankThree.GF2n.Smith81.D6X
