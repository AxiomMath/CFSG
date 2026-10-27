module

public import CFSG.RankThree.GF2n.Tim79aTIPairing
public import CFSG.RankThree.GF2n.Tim79aSec33TI
public import CFSG.RankThree.GF2n.Tim79aSpPair
public import CFSG.RankThree.GF2n.Tim79aSec24CoreQuotient
public import CFSG.RankThree.GF2n.Tim79aSec34BetaSummand
public import CFSG.RankThree.GF2n.Tim79aSec24Tilde

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec3PairingStatement_of_parts
    (hBeta : Sec3BetaStatement) : Sec3PairingStatement := by
  have hP := CFSG.RankThree.GF2n.Tim79a.tiPairingStatement_holds
  have hBase := sec3BaseStatement_holds
  have hTIb := sec3TIStatement_holds
  have hEx := sec3ExistsStatement_holds
  intro G _ _ M V Q P H hs hF
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  obtain ⟨b1, b2, b3, b4, b5⟩ := hBase G M V Q P H hs
  have hQM : Q ≤ M := hc.hQ ▸ (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M := hc.P_le_Q.trans hQM
  have hdata : TIPairData M V P (V ⊓ wOf V H) (Eof V H P) (Ycomm V H) (Aof V H) :=
    { VleP := hc.V_le_P
      PleM := hPM
      normV := fun m hm => mem_normalizer_iff_conjSubgroup_eq.mp (hc.normalizer_eq ▸ hm)
      normP := fun m hm => mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_P hm)
      maxAb := hc.maxAb
      PcentV := fun x hx v hv => (hc.commute_of_mem_P hx hv).symm
      PcommV := fun x hx y hy => hc.commutator_mem_V_of_mem_P hx hy
      ti := hc.ti
      AleV := inf_le_left
      AjleV := fun y _ => inf_le_left
      AjleP := b1
      AjeqP := hTIb G M V Q P H hs hF
      Ajcard := b2
      Ajcomm := b3
      EleP := inf_le_left
      AjleE := b5
      abelL := b4
      moves := hEx G M V Q P H hs hF
      beta := hBeta G M V Q P H hs hF }
  obtain ⟨B, ⟨h, hh, y, hy, rfl⟩, hBP, hBL, hBV, hBTI, y', hy', hnv, hpair⟩ :=
    hP G M V P (V ⊓ wOf V H) (Eof V H P) (Ycomm V H) (Aof V H) hdata
  refine ⟨_, hBP, hBL, hBV, hBTI, ?_, y', hy', hnv, hpair⟩
  rw [← b2 y hy]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).symm.toEquiv

@[expose] def Sec34PairingStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H →
    ∃ B : Subgroup G, B ≤ P ∧ ¬ B ≤ V ⊔ Eof V H P ∧ B ⊓ V = ⊥ ∧
      (∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B) ∧
      Nat.card ↥B = Nat.card ↥(V ⊓ wOf V H) ∧
      ∃ y' ∈ Ycomm V H, ¬ Aof V H y' ≤ V ∧
        ∀ b ∈ B, b ≠ 1 → ∀ a ∈ V ⊓ wOf V H, ∃! α : G, α ∈ Aof V H y' ∧ ⁅b, α⁆ = a

theorem sec34PairingStatement_of_parts (hP : Sec3PairingStatement) :
    Sec34PairingStatement := by
  have hS := CFSG.RankThree.GF2n.Tim79a.spPairStatement_holds
  intro G _ _ M V Q P H hs h3
  have hSp : ClassicalRootSp (XbarZ V H) (VZ V H) := by
    obtain ⟨f, hf, -, hT⟩ := h3
    exact ⟨f, rootClassZ V H, hf, hT, VZ_mem_rootClassZ V H⟩
  exact hP G M V Q P H hs (hS _ _ hSp)

@[expose] def Sec34ModuleStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → CentreClause V H → Nat.card ↥(V ⊓ wOf V H) = qBar V H

@[expose] def Tim79a34TwoTildeEndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    qBar V H = 2 → Sec23Three V H → CentreClause V H → Sec24bTilde V H P → Sec25Concl V H P →
    Nat.card ↥(V ⊓ wOf V H) = qBar V H → False

@[expose] def Tim79a34TwoTwistedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    qBar V H = 2 → Sec23Three V H → ¬ CentreClause V H → Sec24bTilde V H P →
    Sec25Concl V H P → False

@[expose] def Tim79a34BigTildeEndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    4 ≤ qBar V H → Sec23Three V H → CentreClause V H → Sec24bTilde V H P → Sec25Concl V H P →
    Nat.card ↥(V ⊓ wOf V H) = qBar V H → False

theorem tim79a34TwoTildeNoCentreStatement_of_parts (hM : Sec34ModuleStatement)
    (hE : Tim79a34TwoTildeEndStatement) (hT : Tim79a34TwoTwistedStatement) :
    Tim79a34TwoTildeNoCentreStatement := by
  intro G _ _ M V Q P H hs hq h3 hb hS
  by_cases hc : CentreClause V H
  · exact hE G M V Q P H hs hq h3 hc hb hS (hM G M V Q P H ⟨hs, hb, hS⟩ h3 hc)
  · exact hT G M V Q P H hs hq h3 hc hb hS

theorem tim79a34BigTildeStatement_of_parts (hM : Sec34ModuleStatement)
    (hE : Tim79a34BigTildeEndStatement) : Tim79a34BigTildeStatement :=
  fun G _ _ M V Q P H hs hq h3 hc hb hS =>
    hE G M V Q P H hs hq h3 hc hb hS (hM G M V Q P H ⟨hs, hb, hS⟩ h3 hc)

@[expose] def Sec34SummandStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → CentreClause V H →
    ∃ W₁ : Subgroup G, W₁ ≤ wOf V H ∧ (∀ h ∈ H, conjSubgroup h W₁ = W₁) ∧
      Nat.card ↥(V ⊓ W₁) = qBar V H

theorem sec34ModuleStatement_of_summand (hSum : Sec34SummandStatement)
    (hBeta : Sec3BetaStatement)
    : Sec34ModuleStatement := by
  have hTI := CFSG.RankThree.GF2n.Tim79a.tiSummandStatement_holds
  have hBase := sec3BaseStatement_holds
  have hTIb := sec3TIStatement_holds
  have hEx := sec3ExistsStatement_holds
  have hBS := sec3BetaSummandStatement_holds
  have hSp := CFSG.RankThree.GF2n.Tim79a.spPairStatement_holds
  intro G _ _ M V Q P H hs h3 hcc
  have hSp' : ClassicalRootSp (XbarZ V H) (VZ V H) := by
    obtain ⟨f, hf, -, hT⟩ := h3
    exact ⟨f, rootClassZ V H, hf, hT, VZ_mem_rootClassZ V H⟩
  have hPF : PairFacts (XbarZ V H) (VZ V H) := hSp _ _ hSp'
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  obtain ⟨W₁, hW₁W, hW₁H, hW₁card⟩ := hSum G M V Q P H hs h3 hcc
  obtain ⟨b1, b2, b3, b4, b5⟩ := hBase G M V Q P H hs
  have hQM : Q ≤ M := hc.hQ ▸ (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M := hc.P_le_Q.trans hQM
  have hdata : TIPairData M V P (V ⊓ wOf V H) (Eof V H P) (Ycomm V H) (Aof V H) :=
    { VleP := hc.V_le_P
      PleM := hPM
      normV := fun m hm => mem_normalizer_iff_conjSubgroup_eq.mp (hc.normalizer_eq ▸ hm)
      normP := fun m hm => mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_P hm)
      maxAb := hc.maxAb
      PcentV := fun x hx v hv => (hc.commute_of_mem_P hx hv).symm
      PcommV := fun x hx y hy => hc.commutator_mem_V_of_mem_P hx hy
      ti := hc.ti
      AleV := inf_le_left
      AjleV := fun y _ => inf_le_left
      AjleP := b1
      AjeqP := hTIb G M V Q P H hs hPF
      Ajcard := b2
      Ajcomm := b3
      EleP := inf_le_left
      AjleE := b5
      abelL := b4
      moves := hEx G M V Q P H hs hPF
      beta := hBeta G M V Q P H hs hPF }
  have hbar : Nat.card ↥(barOf V H V) ≠ 1 := by
    intro h1
    have h2 : barOf V H V = ⊥ := Subgroup.card_eq_one.mp h1
    apply hc.not_V_le_wOf
    intro v hv
    have h3 : piBar V H ⟨v, hc.V_le_H hv⟩ ∈ barOf V H V :=
      mem_barOf_iff.mpr ⟨⟨v, hc.V_le_H hv⟩, hv, rfl⟩
    rw [h2, Subgroup.mem_bot] at h3
    exact (piBar_eq_one_iff _).mp h3
  have hVW₁ : V ⊓ W₁ ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(V ⊓ W₁) = 1 := by rw [h]; simp
    have hq : qBar V H = Nat.card ↥(barOf V H V) := rfl
    exact hbar (by rw [← hq, ← hW₁card, h1])
  have hle : Nat.card ↥(V ⊓ wOf V H) ≤ Nat.card ↥(V ⊓ W₁) := by
    refine hTI G M V P (V ⊓ wOf V H) (Eof V H P) (Ycomm V H) (Aof V H) (V ⊓ W₁) (W₁ ⊓ P)
      hdata inf_le_left inf_le_right ?_ ?_
    · intro x hx f hf
      refine Subgroup.mem_inf.mpr ⟨hc.commutator_mem_V_of_mem_P hx (Subgroup.mem_inf.mp hf).2, ?_⟩
      have hxH : x ∈ H := hc.PleH hx
      have h1 : x * f * x⁻¹ ∈ W₁ := by
        have hmem : x * f * x⁻¹ ∈ conjSubgroup x W₁ := by
          rw [mem_conjSubgroup]
          have e : x⁻¹ * (x * f * x⁻¹) * x = f := by group
          rw [e]
          exact (Subgroup.mem_inf.mp hf).1
        rwa [hW₁H x hxH] at hmem
      rw [commutatorElement_def]
      exact W₁.mul_mem h1 (W₁.inv_mem (Subgroup.mem_inf.mp hf).1)
    · intro x hx hcen
      refine hBS G M V Q P H W₁ hs hPF hW₁W hW₁H hVW₁ x hx ?_
      intro y hy α hα
      have hαA : α ∈ Aof V H y := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hα).1,
        hW₁W (Subgroup.mem_inf.mp hα).2⟩
      exact hcen α (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hα).2, b1 y hy hαA⟩)
  have hge : Nat.card ↥(V ⊓ W₁) ≤ Nat.card ↥(V ⊓ wOf V H) :=
    Subgroup.card_le_of_le (inf_le_inf_left V hW₁W)
  rw [← hW₁card]
  exact le_antisymm hle hge

theorem sec34ModuleStatement_of_summand_holds (hSum : Sec34SummandStatement) :
    Sec34ModuleStatement :=
  sec34ModuleStatement_of_summand hSum sec3BetaStatement_holds

theorem sec34PairingStatement_holds : Sec34PairingStatement :=
  sec34PairingStatement_of_parts (sec3PairingStatement_of_parts sec3BetaStatement_holds)

end CFSG.RankThree.GF2n.Tim79a
