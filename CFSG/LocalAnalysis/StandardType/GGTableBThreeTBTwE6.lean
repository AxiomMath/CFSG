module

public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwE6Field
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBTwE6ThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def GGTwE6ThreeTorusNbrInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → U63TB.GGTorusNbrSCrK 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6ThreeModuleInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → GGTableBModuleSCr 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6ThreeTvInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → GGNoTransvectionSCr 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6ThreeBstarRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L →
      ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G), 3 ^ 5 ≤ Nat.card (ggGamma L hN).range

section Certs

theorem ggTorusLift_twE6Three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ∣ 2 ^ n + 1) :
    GGTorusLift 3 4 (TwE6Delta.RecipeR K n) := by
  have h := ggTorusLift_twE6Add_holds hn hK Nat.prime_three hd
  rwa [TwE6Delta.liftRank_three] at h

theorem largeEvenLabelAll_twE6Three_of {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBTwE6ThreeLabel p lab)
    {P : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (hP : ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
      3 ∣ 2 ^ n + 1 → P (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ P R I := by
  obtain ⟨ht, -, hd⟩ := h
  exact TwE6Delta.labelAll ht fun K _ _ hK =>
    ⟨ggTorusLift_twE6Three hlab.1 hK hd, hP K lab.n hlab.1 hK hd⟩

theorem largeEvenLabelAll_twE6Three_nbr {p : ℕ} {lab : LargeEvenLabel}
    (hK : GGTwE6ThreeTorusNbrInput) (hlab : LargeEvenInLambda2 lab)
    (h : GGTableBTwE6ThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ U63TB.GGTorusNbrSCrK 3 5 R I :=
  largeEvenLabelAll_twE6Three_of hlab h (P := fun R _ I => U63TB.GGTorusNbrSCrK 3 5 R I)
    (fun K _ _ n hn hK' h' => hK K n hn hK' h')

theorem largeEvenLabelAll_twE6Three_mod {p : ℕ} {lab : LargeEvenLabel}
    (hK : GGTwE6ThreeModuleInput) (hlab : LargeEvenInLambda2 lab)
    (h : GGTableBTwE6ThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ GGTableBModuleSCr 3 5 R I :=
  largeEvenLabelAll_twE6Three_of hlab h (P := fun R _ I => GGTableBModuleSCr 3 5 R I)
    (fun K _ _ n hn hK' h' => hK K n hn hK' h')

theorem largeEvenLabelAll_twE6Three_tv {p : ℕ} {lab : LargeEvenLabel}
    (hK : GGTwE6ThreeTvInput) (hlab : LargeEvenInLambda2 lab)
    (h : GGTableBTwE6ThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ GGNoTransvectionSCr 3 5 R I :=
  largeEvenLabelAll_twE6Three_of hlab h (P := fun R _ I => GGNoTransvectionSCr 3 5 R I)
    (fun K _ _ n hn hK' h' => hK K n hn hK' h')

theorem largeEvenLabelAll_twE6Three_line {p : ℕ} {lab : LargeEvenLabel}
    (hK : GGTwE6ThreeModuleInput) (hlab : LargeEvenInLambda2 lab)
    (h : GGTableBTwE6ThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ GGNoInvariantLineSCr 3 5 R I :=
  largeEvenLabelAll_twE6Three_of hlab h (P := fun R _ I => GGNoInvariantLineSCr 3 5 R I)
    (fun K _ _ n hn hK' h' => ggNoInvariantLineSCr_of_ggTableBModuleSCr (by norm_num)
      (hK K n hn hK' h'))

theorem ggBstarInnerDiagLInputOn_twE6Three (hX : GGTwE6InnerDiagBound2LInput) :
    GGBstarInnerDiagLInputOn GGTableBTwE6ThreeLabel := by
  have hF := ggBstarInnerDiagLInputOn_of_le_twE6Field hX
    (S := fun p lab => GGTableBTwE6ThreeLabel p lab ∧ p ∣ lab.n) (fun p lab h => by
      obtain ⟨⟨ht, rfl, hd⟩, hn⟩ := h
      exact ⟨ht, hd, hn⟩)
  have hC := CorFourTwoOpen.ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds
    (S := fun p lab => GGTableBTwE6ThreeLabel p lab ∧ ¬ p ∣ lab.n) (fun p lab hp hlab hs => by
      obtain ⟨⟨ht, rfl, -⟩, hn⟩ := hs
      exact TwE6TB.largeEvenLabelAll_pow_mem hp (by norm_num) hlab ht hn)
  have h := hF.or hC
  have e : (fun p lab => (GGTableBTwE6ThreeLabel p lab ∧ p ∣ lab.n) ∨
      (GGTableBTwE6ThreeLabel p lab ∧ ¬ p ∣ lab.n)) = GGTableBTwE6ThreeLabel := by
    funext p lab
    apply propext
    by_cases hpn : p ∣ lab.n <;> simp [hpn]
  rwa [e] at h

theorem ggTableBCxInputOn_twE6Three (hX : GGTwE6InnerDiagBound2LInput)
    (hB : GGTwE6ThreeBstarRankInput) (hK : GGTwE6ThreeTorusNbrInput) :
    GGTableBCxInputOn GGTableBTwE6ThreeLabel := by
  intro G _ _ p B Bs x L D J hcfg hM Y hYx hYN _ hYn hYp
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hMB := ggBstarInnerDiagLInputOn_twE6Three hX G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ U63TB.GGTorusNbrSCrK 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6Three_nbr hK hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hMB
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  have h5 := hB G _ B Bs x L D J hcfg hMB hBsN
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  exact U63TB.ggTableBCx_of_card hcfg
    (UnitTB.exists_noncyclic_of_torusLift hp (by norm_num) hL θ hlift) hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT hYx hYN hYn hYp

theorem ggTableBModuleInputOn_twE6Three (hX : GGTwE6InnerDiagBound2LInput)
    (hB : GGTwE6ThreeBstarRankInput) (hK : GGTwE6ThreeModuleInput) :
    GGTableBModuleInputOn GGTableBTwE6ThreeLabel := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hMB := ggBstarInnerDiagLInputOn_twE6Three hX G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGTableBModuleSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6Three_mod hK hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hMB
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, -, hT⟩ :=
    largeEvenRawDatum_exists hraw
  have h5 := hB G _ B Bs x L D J hcfg hMB hBsN
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  exact U63TB.ggTableBModule_of_card hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT

theorem ggLTransvectionCenterInputOn_twE6Three (hB : GGTwE6ThreeBstarRankInput)
    (hK : GGTwE6ThreeTvInput) : GGLTransvectionCenterInputOn GGTableBTwE6ThreeLabel := by
  intro G _ _ p B Bs x L D J hC hM φ hφ hφt b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGNoTransvectionSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6Three_tv hK hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, hlift, htv⟩ :=
    largeEvenRawDatum_exists hraw
  have h5 := hB G _ B Bs x L D J hC hM hBsN
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  exact UnitTv.mem_zpowers_of_noTransvectionSCr_card hC
    (UnitTB.exists_noncyclic_of_torusLift hp (by norm_num) hL θ hlift) hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' htv hφ hφt b

theorem ggLNoInvariantLineInputOn_twE6Three (hB : GGTwE6ThreeBstarRankInput)
    (hK : GGTwE6ThreeModuleInput) : GGLNoInvariantLineInputOn GGTableBTwE6ThreeLabel := by
  intro G _ _ p B Bs x L D J hC hM E hEBs hxE hE
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ GGNoInvariantLineSCr 3 5 R I)
    (fun lab hlab hs => largeEvenLabelAll_twE6Three_line hK hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, rfl, -⟩, -, hBsN, h3⟩, -, hT⟩ :=
    largeEvenRawDatum_exists hraw
  have h5 := hB G _ B Bs x L D J hC hM hBsN
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  exact Line63.not_normalizer_le_of_noInvariantLineSCr_card hC hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT hEBs hxE hE

theorem ggTableBCxInputOn_of_not_twE6Three (hX : GGTwE6InnerDiagBound2LInput)
    (hB : GGTwE6ThreeBstarRankInput) (hK : GGTwE6ThreeTorusNbrInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGTableBTwE6ThreeLabel p lab) :
    GGTableBCxInputOn S := by
  have h' := (ggTableBCxInputOn_twE6Three hX hB hK).or h
  intro G _ _ p B Bs x L D J hcfg hM
  refine h' G p B Bs x L D J hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBTwE6ThreeLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_twE6Three (hX : GGTwE6InnerDiagBound2LInput)
    (hB : GGTwE6ThreeBstarRankInput) (hK : GGTwE6ThreeModuleInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGTableBTwE6ThreeLabel p lab) :
    GGTableBModuleInputOn S := by
  have h' := (ggTableBModuleInputOn_twE6Three hX hB hK).or h
  intro G _ _ p B Bs x L D J hcfg hM
  refine h' G p B Bs x L D J hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBTwE6ThreeLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggLTransvectionCenterInputOn_of_not_twE6Three (hB : GGTwE6ThreeBstarRankInput)
    (hK : GGTwE6ThreeTvInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGTableBTwE6ThreeLabel p lab) :
    GGLTransvectionCenterInputOn S := by
  have h' := (ggLTransvectionCenterInputOn_twE6Three hB hK).or h
  intro G _ _ p B Bs x L D J hC hM
  refine h' G p B Bs x L D J hC (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBTwE6ThreeLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggLNoInvariantLineInputOn_of_not_twE6Three (hB : GGTwE6ThreeBstarRankInput)
    (hK : GGTwE6ThreeModuleInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGTableBTwE6ThreeLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := (ggLNoInvariantLineInputOn_twE6Three hB hK).or h
  intro G _ _ p B Bs x L D J hC hM
  refine h' G p B Bs x L D J hC (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTableBTwE6ThreeLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

end Certs

end CFSG.StandardType

end
