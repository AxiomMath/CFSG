module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 1(c)
-/

private theorem hypothesisA1_beta_ne
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t) :
    t⁻¹ • α ≠ α := by
  intro hβα
  apply hA1.t_not_mem_H
  change t • α = α
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  simpa [htinv] using hβα

private theorem hypothesisA1_D_eq_stabilizer_inf
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α β : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t)
    (hβ : β = t⁻¹ • α) :
    D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
  subst β
  simpa [rightConjugate_stabilizer] using hA1.D_eq

private theorem hypothesisA1_Q_subgroupOf_disjoint
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t) :
    Disjoint (Q.subgroupOf (MulAction.stabilizer G α))
      (D.subgroupOf (MulAction.stabilizer G α)) := by
  rw [Subgroup.disjoint_def]
  intro x hxQ hxD
  apply Subtype.ext
  have hxQD : (x : G) ∈ Q ⊓ D := ⟨hxQ, hxD⟩
  simpa using hA1.Q_disjoint_D.le_bot hxQD

private theorem hypothesisA1_Q_subgroupOf_sup_top
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t) :
    Q.subgroupOf (MulAction.stabilizer G α) ⊔
        D.subgroupOf (MulAction.stabilizer G α) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup hA1.Q_le_H hA1.D_le_H, hA1.Q_sup_D]
  simp

private theorem hypothesisA1_Q_subgroupOf_index_eq_card_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t) :
    (Q.subgroupOf (MulAction.stabilizer G α)).index = Nat.card D := by
  let QH : Subgroup (MulAction.stabilizer G α) :=
    Q.subgroupOf (MulAction.stabilizer G α)
  let DH : Subgroup (MulAction.stabilizer G α) :=
    D.subgroupOf (MulAction.stabilizer G α)
  have htop : DH ⊔ QH = ⊤ := by
    rw [sup_comm]
    exact hypothesisA1_Q_subgroupOf_sup_top hA1
  have hinf : QH ⊓ DH = ⊥ := by
    exact le_antisymm (hypothesisA1_Q_subgroupOf_disjoint hA1).le_bot bot_le
  letI : QH.Normal := hA1.Q_normal_in_H
  calc
    (Q.subgroupOf (MulAction.stabilizer G α)).index =
        QH.relIndex (⊤ : Subgroup (MulAction.stabilizer G α)) := by
      rw [Subgroup.relIndex_top_right]
    _ = QH.relIndex (DH ⊔ QH) := by rw [htop]
    _ = QH.relIndex DH := by rw [Subgroup.relIndex_sup_right]
    _ = (QH ⊓ DH).relIndex DH := by rw [Subgroup.inf_relIndex_right]
    _ = (⊥ : Subgroup (MulAction.stabilizer G α)).relIndex DH := by rw [hinf]
    _ = Nat.card DH := by rw [Subgroup.relIndex_bot_left]
    _ = Nat.card D := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA1.D_le_H).toEquiv

public theorem hypothesisA1_Q_regular_on_complement
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α β : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t)
    (hβ_ne : β ≠ α)
    (hD : D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    Set.BijOn (fun q : Q => (q : G) • β) Set.univ
      ({ω : Ω | ω ≠ α} : Set Ω) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q _hq hqβ
    have hqβ' : (q : G) • β = α := by
      simpa using hqβ
    exact hβ_ne
      (calc
        β = (q : G)⁻¹ • ((q : G) • β) := by simp [smul_smul]
        _ = (q : G)⁻¹ • α := by rw [hqβ']
        _ = α := by
          have hqH : (q : G) ∈ MulAction.stabilizer G α :=
            hA1.Q_le_H q.property
          exact (MulAction.stabilizer G α).inv_mem hqH)
  · intro q₁ _hq₁ q₂ _hq₂ hq
    have hq' : (q₁ : G) • β = (q₂ : G) • β := by
      simpa using hq
    have hrQ : (q₂ : G)⁻¹ * (q₁ : G) ∈ Q :=
      Q.mul_mem (Q.inv_mem q₂.property) q₁.property
    have hrα : ((q₂ : G)⁻¹ * (q₁ : G)) ∈ MulAction.stabilizer G α :=
      hA1.Q_le_H hrQ
    have hrβ : ((q₂ : G)⁻¹ * (q₁ : G)) ∈ MulAction.stabilizer G β := by
      change ((q₂ : G)⁻¹ * (q₁ : G)) • β = β
      calc
        ((q₂ : G)⁻¹ * (q₁ : G)) • β =
            (q₂ : G)⁻¹ • ((q₁ : G) • β) := by simp [smul_smul]
        _ = (q₂ : G)⁻¹ • ((q₂ : G) • β) := by rw [hq']
        _ = β := by simp [smul_smul]
    have hrD : (q₂ : G)⁻¹ * (q₁ : G) ∈ D := by
      rw [hD]
      exact ⟨hrα, hrβ⟩
    have hr_one : (q₂ : G)⁻¹ * (q₁ : G) = 1 := by
      have hrQD : (q₂ : G)⁻¹ * (q₁ : G) ∈ Q ⊓ D := ⟨hrQ, hrD⟩
      simpa using hA1.Q_disjoint_D.le_bot hrQD
    apply Subtype.ext
    exact (inv_mul_eq_one.mp hr_one).symm
  · intro γ hγα
    obtain ⟨h, hhα, hhβ⟩ :=
      (MulAction.is_two_pretransitive_iff.mp hA1.two_transitive)
        (Ne.symm hβ_ne) (Ne.symm hγα)
    have hhH : h ∈ MulAction.stabilizer G α := by
      change h • α = α
      exact hhα
    have hmem_sup :
        (⟨h, hhH⟩ : MulAction.stabilizer G α) ∈
          Q.subgroupOf (MulAction.stabilizer G α) ⊔
            D.subgroupOf (MulAction.stabilizer G α) := by
      rw [hypothesisA1_Q_subgroupOf_sup_top hA1]
      exact Subgroup.mem_top _
    letI : (Q.subgroupOf (MulAction.stabilizer G α)).Normal :=
      hA1.Q_normal_in_H
    rw [Subgroup.mem_sup_of_normal_left] at hmem_sup
    rcases hmem_sup with ⟨q, hqQ, d, hdD, hqd⟩
    refine ⟨⟨(q : G), hqQ⟩, by simp, ?_⟩
    have hdβ : (d : G) • β = β := by
      have hdD_G : (d : G) ∈ D := hdD
      have hd_stab : (d : G) ∈ MulAction.stabilizer G β := by
        rw [hD] at hdD_G
        exact hdD_G.2
      exact hd_stab
    have hqdG : (q : G) * (d : G) = h :=
      congrArg Subtype.val hqd
    calc
      (q : G) • β = (q : G) • ((d : G) • β) := by rw [hdβ]
      _ = ((q : G) * (d : G)) • β := by simp [smul_smul]
      _ = h • β := by rw [hqdG]
      _ = γ := hhβ

private theorem hypothesisA1_card_space_eq_card_Q_add_one
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α β : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t)
    (hβ_ne : β ≠ α)
    (hD : D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    Nat.card Ω = Nat.card Q + 1 := by
  have hcard := (hypothesisA1_Q_regular_on_complement hA1 hβ_ne hD).ncard_eq
  have hcardQ :
      Nat.card Q = ({ω : Ω | ω ≠ α} : Set Ω).ncard := by
    simpa using hcard
  have hsum := Set.ncard_add_ncard_compl ({α} : Set Ω)
  rw [Set.ncard_singleton] at hsum
  have hcompl :
      ({α} : Set Ω)ᶜ = ({ω : Ω | ω ≠ α} : Set Ω) := by
    ext ω
    simp
  rw [hcompl, ← hcardQ] at hsum
  simpa [Nat.add_comm] using hsum.symm

private theorem hypothesisA1_Q_index_odd
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {D Q : Subgroup G} {t : G} {α β : Ω}
    (hA1 : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t)
    (hβ_ne : β ≠ α)
    (hD : D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :
    Odd Q.index := by
  have hΩ_card : Nat.card Ω = Nat.card Q + 1 :=
    hypothesisA1_card_space_eq_card_Q_add_one hA1 hβ_ne hD
  have hH_index : (MulAction.stabilizer G α).index = Nat.card Ω := by
    letI : MulAction.IsMultiplyPretransitive G Ω 2 := hA1.two_transitive
    haveI : MulAction.IsPretransitive G Ω :=
      MulAction.isPretransitive_of_is_two_pretransitive
    exact MulAction.index_stabilizer_of_transitive (G := G) (x := α)
  have hQ_relIndex :
      Q.relIndex (MulAction.stabilizer G α) = Nat.card D := by
    change (Q.subgroupOf (MulAction.stabilizer G α)).index = Nat.card D
    exact hypothesisA1_Q_subgroupOf_index_eq_card_D hA1
  have hQ_index :
      Q.index = Nat.card D * (Nat.card Q + 1) := by
    calc
      Q.index =
          Q.relIndex (MulAction.stabilizer G α) *
            (MulAction.stabilizer G α).index :=
        (Subgroup.relIndex_mul_index hA1.Q_le_H).symm
      _ = Nat.card D * Nat.card Ω := by
        rw [hQ_relIndex, hH_index]
      _ = Nat.card D * (Nat.card Q + 1) := by rw [hΩ_card]
  rw [hQ_index]
  exact hA1.D_odd.mul hA1.Q_even.add_one

/-- The degree of the doubly transitive action in Hypothesis (A1). -/
public theorem hypothesisA1_card_space_eq_card_Q_add_one_of_hypothesis
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Nat.card Ω = Nat.card Q + 1 := by
  obtain ⟨α, hH⟩ := hA1.point_stabilizer
  subst H
  let β : Ω := t⁻¹ • α
  have hβ_ne : β ≠ α := hypothesisA1_beta_ne hA1
  have hD :
      D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    exact hypothesisA1_D_eq_stabilizer_inf hA1 rfl
  exact hypothesisA1_card_space_eq_card_Q_add_one hA1 hβ_ne hD

public theorem proposition_1_c
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hH⟩ := hA1.point_stabilizer
  subst H
  let β : Ω := t⁻¹ • α
  have hβ_ne : β ≠ α := hypothesisA1_beta_ne hA1
  have hD :
      D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    exact hypothesisA1_D_eq_stabilizer_inf hA1 rfl
  have hQ_index_odd : Odd Q.index :=
    hypothesisA1_Q_index_odd hA1 hβ_ne hD
  let P : Sylow 2 Q := default
  let Pmap : Subgroup G := (P : Subgroup Q).map Q.subtype
  have hPmap_isPGroup : IsPGroup 2 Pmap :=
    P.isPGroup'.map Q.subtype
  have hPmap_index_odd : ¬ 2 ∣ Pmap.index := by
    change ¬ 2 ∣ ((P : Subgroup Q).map Q.subtype).index
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two
      P.not_dvd_index hQ_index_odd.not_two_dvd_nat
  refine ⟨hPmap_isPGroup.toSylow hPmap_index_odd, ?_⟩
  change ((P : Subgroup Q).map Q.subtype) ≤ Q
  exact Subgroup.map_subtype_le (P : Subgroup Q)

end PFchapter1section1
end CFSG.BenderSuzuki
