module

public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Defs
public import CFSG.LocalAnalysis.StandardType.GGTWHLTorRow
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nTA_odd {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f + 1) := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  rw [pow_succ]
  exact ⟨2 ^ g, by omega⟩

private theorem l05nTA_L
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hW : GGTBWNormLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hp3 : p = 3) {labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labX)
    (hl : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L))
    (htag : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) : GGTWHLAt p Bs L x := by
  obtain ⟨f, hN, hf, hpq, hTor⟩ :=
    ggTwA5Three_torDataAt hRig hLB hPJ hH (Or.inl ⟨rfl, rfl⟩) hp3 hΛ hl htag
  subst hp3
  obtain ⟨htw, -, hdvd⟩ := htag
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hsplit : LargeEvenSplit 3 labX :=
    Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htw], by simp [htw], hdvd⟩)
  have hexcl : ¬ GGTBWExcl labX := by simp [GGTBWExcl, htw]
  let S : ℕ → LargeEvenLabel → Prop := fun p lab => p ≠ 2 ∧ lab.tag = .twA ∧ ¬ GGTBWExcl lab
  have hM : GGInnerDiagOnLab S 3 Bs L := by
    refine largeEvenMarking_mono (fun lab' _ _ _ _ _ hP => ?_)
      (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hΛ hl)
    obtain ⟨rfl, hN', hind⟩ := hP
    exact ⟨⟨by norm_num, htw, hexcl⟩, hsplit, hN', hind⟩
  have hWn : GGTBWNormInputOn S :=
    ggTBWNormInputOn_of_labels fun p lab hpp hlab hSlab => hW p hpp hSlab.1 lab hlab hSlab.2.2
      (by rw [hSlab.2.1]; decide)
  have hnc : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 3 T ∧ ¬ IsCyclic T :=
    ggLNoncyclicInputOn_not_twisted G 3 B x L hH.1.1
      (largeEvenMarking_mono (fun lab' _ _ _ _ _ hP =>
        ⟨by simp [GGOutdiagTwistedLabel, hP.1.2.1], hP.2.1, hBBs.trans hP.2.2.1,
          fun b hb => hP.2.2.2 b (hBBs hb)⟩) hM)
  exact ggTWHL_of_torData hWn hcfg hM hnc hN (l05nTA_odd hf) hpq hTor

private theorem l05nTA_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hW : GGTBWNormLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hp3 : p = 3) {labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labX)
    (hl : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K))
    (htag : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y) :
    GGTWHLAt p Bs K y := by
  obtain ⟨f, hN, hf, hpq, hTor⟩ :=
    ggTwA5Three_torDataAt hRig hLB hPJ hH (Or.inr ⟨rfl, rfl⟩) hp3 hΛ hl htag
  subst hp3
  obtain ⟨htw, -, hdvd⟩ := htag
  have hsplit : LargeEvenSplit 3 labX :=
    Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htw], by simp [htw], hdvd⟩)
  have hexcl : ¬ GGTBWExcl labX := by simp [GGTBWExcl, htw]
  let S : ℕ → LargeEvenLabel → Prop := fun p lab => p ≠ 2 ∧ lab.tag = .twA ∧ ¬ GGTBWExcl lab
  have hM : GGInnerDiagOnLab S 3 Bs K := by
    refine largeEvenMarking_mono (fun lab' _ _ _ _ _ hP => ?_)
      (ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ hl)
    obtain ⟨rfl, hN', hind⟩ := hP
    exact ⟨⟨by norm_num, htw, hexcl⟩, hsplit, hN', hind⟩
  have hW' : GGTBWNormInputNbr S :=
    ggTBWNormInputNbr_of_labels fun p lab hpp hlab hSlab => hW p hpp hSlab.1 lab hlab hSlab.2.2
      (by rw [hSlab.2.1]; decide)
  exact ggHL58Nbr_of_torData hW' hH hCent hM hN (l05nTA_odd hf) hpq hTor

theorem ggTWTwA5Open_of_frame
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hW : GGTBWNormLabelInput) : GGTWTwA5Open := by
  intro G _ _ p B Bs x L D J y K hH _ X z hXz hp3 labX hΛ hl htag
  refine ⟨(ggTwA5Three_frame hRig hLB hPJ hH hXz hp3 hΛ hl htag).2.2, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    exact l05nTA_L hRig hLB hPJ hW hH hp3 hΛ hl htag
  · rintro ⟨rfl, rfl⟩ _ hCent
    exact l05nTA_K hRig hLB hPJ hW hH hp3 hΛ hl htag hCent

end CFSG.StandardType

end
