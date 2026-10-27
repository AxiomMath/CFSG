module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinJNormGen
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPhanA5Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

namespace NSJoin

open CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

@[expose] def NSTypeAD {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  (∃ (m : ℕ) (e : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex e) ∨ GGIsWeylMatrixD M

theorem NSTypeAD.le_three {ι : Type} {M : CoxeterMatrix ι} (h : NSTypeAD M) (i j : ι)
    (hij : i ≠ j) : M.M i j ≤ 3 := by
  rcases h with ⟨m, e', hm, rfl⟩ | hD
  · rw [CoxeterMatrix.reindex_apply]
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    split_ifs <;> omega
  · exact GGIsWeylMatrixAD.le_three (Or.inr hD) i j hij

@[expose] def NSJoinGuardOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) (p : ℕ) (L Bs : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop :=
  ∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
    GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ T M ∧
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6

@[expose] def NSJoinGuard (p : ℕ) (L Bs : Subgroup G) (𝒦 : Finset (Subgroup G)) : Prop :=
  NSJoinGuardOf NSTypeAD p L Bs 𝒦

theorem NSJoinGuardOf.mono {T T' : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (h : ∀ {ι : Type} {M : CoxeterMatrix ι}, T' M → T M) {p : ℕ} {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hg : NSJoinGuardOf T' p L Bs 𝒦) : NSJoinGuardOf T p L Bs 𝒦 := by
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hg
  exact ⟨ι, M, e, hpres, h hT, hbig⟩

@[expose] def NSReflMaxInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦

@[expose] def NSReflMaxInput : Prop :=
  NSReflMaxInputOf NSTypeAD

@[expose] def NSNbrGenKNInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 →
        K ≤ ⨆ (n : G) (_ : n ∈ K) (_ : ∃ φ : MulAut ↥Bs,
            n ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
          J.map (MulAut.conj n).toMonoidHom

@[expose] def NSNbrGenKNInput : Prop :=
  NSNbrGenKNInputOf NSTypeAD

@[expose] def NSJNormInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      J ≤ L ∧ ∀ c ∈ Subgroup.centralizer (Bs : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J

@[expose] def NSJNormInput : Prop :=
  NSJNormInputOf NSTypeAD

theorem join_of_three_guard {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRM : NSReflMaxInputOf T) (hGen : NSNbrGenKNInputOf T) (hJ : NSJNormInputOf T) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
        NSJoinGuardOf T p L Bs 𝒦 → ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard
  obtain ⟨hJL, hcJ⟩ := hJ G p B Bs x L D J 𝒦 hcfg hns hguard
  refine le_antisymm ?_ (ggJoin_le_ggG0 (Bs := Bs) hcfg.2.2.2.1)
  exact ggG0_le_join_of_reflMax_genN hJL hcJ
    (hRM G p B Bs x L D J 𝒦 hcfg hns hguard)
    (hGen G p B Bs x L D J 𝒦 hcfg hns hguard)

theorem join_of_three (hRM : NSReflMaxInput) (hGen : NSNbrGenKNInput) (hJ : NSJNormInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
        NSJoinGuard p L Bs 𝒦 → ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K :=
  join_of_three_guard (T := NSTypeAD) hRM hGen hJ

theorem joinPhanD_of_three (hRM : NSReflMaxInput) (hGen : NSNbrGenKNInput)
    (hJ : NSJNormInput) : GGSecFiveJoinPhanInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard
  obtain ⟨ι, M, e, hpres, hD, hbig⟩ := hguard
  exact join_of_three hRM hGen hJ G p B Bs x L D J 𝒦 hcfg hns
    ⟨ι, M, e, hpres, Or.inr hD, hbig⟩

theorem joinPhanA5_of_three (hRM : NSReflMaxInput) (hGen : NSNbrGenKNInput)
    (hJ : NSJNormInput) : GGSecFiveJoinPhanA5Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard
  obtain ⟨ι, M, e, hpres, hA, hbig⟩ := hguard
  exact join_of_three hRM hGen hJ G p B Bs x L D J 𝒦 hcfg hns
    ⟨ι, M, e, hpres, Or.inl hA, hbig⟩

theorem jnormInputOf_of_phan_gen_pair {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput) : NSJNormInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hJL : J ≤ L := (hC.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
  have hDB : D ≤ Bs := (hC.2.2.1.1).trans hC.2.1.1
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  have hnorm := jnormD_of_phan_gen_pair hGen hPair hcfg hns hpres (hT3 hT) hbig
  refine ⟨hJL, ?_⟩
  intro c hc j hj
  exact hnorm c (Subgroup.centralizer_le hDB hc) j hj

theorem jnormInput_of_phan_gen_pair (hGen : GGSecFiveGenPhanInput)
    (hPair : GGSecFivePhanPairInput) : NSJNormInput :=
  jnormInputOf_of_phan_gen_pair (T := NSTypeAD) NSTypeAD.le_three hGen hPair

theorem joinPhanD_of_reflMax_genN (hRM : NSReflMaxInput) (hGenN : NSNbrGenKNInput)
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput) : GGSecFiveJoinPhanInput :=
  joinPhanD_of_three hRM hGenN (jnormInput_of_phan_gen_pair hGen hPair)

theorem joinPhanA5_of_reflMax_genN (hRM : NSReflMaxInput) (hGenN : NSNbrGenKNInput)
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput) : GGSecFiveJoinPhanA5Input :=
  joinPhanA5_of_three hRM hGenN (jnormInput_of_phan_gen_pair hGen hPair)

end NSJoin

end CFSG.StandardType

end

