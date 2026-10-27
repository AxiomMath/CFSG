module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeTransfer
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeInstance
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeKer
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviIso
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwE6Three_tbGroup_of_label
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs)
    (hInn : GGInnerDiagOn Bs X) (hXc : commutator ↥X = ⊤) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hXl : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 5 ≤ Nat.card (ggGamma X hN).range) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (K : Type) (_ : Field K) (_ : Finite K)
      (_ : Nat.card K = (2 ^ n) ^ 2) (ψ₀ : ↥X →* TwE6Delta.RecipeR K n),
      GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ↥X ψ₀
        (ggGamma X hN).range := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInn
  obtain ⟨R, _, θ, I, F, hBsI, K, i1, i2, hK, e, hIe⟩ :=
    exists_innerDiagDatum_of_labelAll hRig hInn hΛ hXl
      (P := fun R _ I _ => ∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = (2 ^ n) ^ 2 ∧ ∃ e : R ≃* TwE6Delta.RecipeR K n,
          ∀ φ, φ ∈ I ↔ MulAut.congr e φ ∈ TwE6Delta.RecipeI K n)
      (TwE6Delta.labelAll (lab := (⟨.twE6, 0, n⟩ : LargeEvenLabel)) rfl
        (Q := fun R _ I => ∃ (K : Type) (_ : Field K) (_ : Finite K),
          Nat.card K = (2 ^ n) ^ 2 ∧ ∃ e : R ≃* TwE6Delta.RecipeR K n,
            ∀ φ, φ ∈ I ↔ MulAut.congr e φ ∈ TwE6Delta.RecipeI K n)
        fun K _ _ hK => ⟨K, inferInstance, inferInstance, hK, MulEquiv.refl _,
          fun φ => Iff.rfl⟩) hN
  let θ' : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K n := θ.trans e
  have hBsI' : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut X θ' ⟨b, hN hb⟩ ∈ TwE6Delta.RecipeI K n := by
    intro b hb
    have h1 : ggLAut X θ' ⟨b, hN hb⟩ = MulAut.congr e (ggLAut X θ ⟨b, hN hb⟩) := by
      ext r
      obtain ⟨q, rfl⟩ := θ'.surjective r
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [ggLAut_apply, MulAut.congr_apply]
        simp only [θ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        rw [ggLAut_apply]
    rw [h1]
    exact (hIe _).1 (hBsI b hb)
  have h5 := hrk hN
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  exact ⟨hN, K, i1, i2, hK, ggQuotHom θ',
    ggTorusTBGroup_of_marking (r := 5) Nat.prime_three hBs hSC hXc θ' hN hBsI' h5 h3⟩

theorem ggE6ThreeCoordData_mono {G : Type} [Group G] [Finite G] {Bs X J : Subgroup G} {g : G}
    {hgBs : g ∈ Bs} {P P' : Prop} (hPP : P → P') (hC : GGE6ThreeCoordData Bs X J g hgBs P) :
    GGE6ThreeCoordData Bs X J g hgBs P' := by
  obtain ⟨V, i1, i2, ι, φ, h, α, f, κW, cd, F, iF, ζ, hζ, hord, c1, c2, c3, c4, c5, c6, c7, c8,
    c9, c10, c11, c12, i, k1, k2, k3⟩ := hC
  exact ⟨V, i1, i2, ι, φ, h, α, f, κW, cd, F, iF, ζ, hζ, hord, c1, c2, c3, c4, c5, c6, c7, c8,
    c9, c10, c11, c12, i, k1, k2, fun hD => hPP (k3 hD)⟩

theorem ggTwE6Three_label_of_subgroupOf {G : Type} [Group G] {X J : Subgroup G} (hJX : J ≤ X)
    (hJp : Group.IsPerfect ↥J)
    (h : ∃ m : ℕ, 1 ≤ m ∧ GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel)
      (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X))) :
    ∃ m : ℕ, 1 ≤ m ∧ GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
  let f : ↥J →* ↥(J.subgroupOf X) := (Subgroup.subgroupOfEquivOfLe hJX).symm.toMonoidHom
  have hf : Function.Surjective f := (Subgroup.subgroupOfEquivOfLe hJX).symm.surjective
  have hk : f.ker ≤ Subgroup.center ↥J := fun x hx => by
    have : x = 1 := (Subgroup.subgroupOfEquivOfLe hJX).symm.injective (by simpa [f] using hx)
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨m, hm, hl⟩ := h
  exact ⟨m, hm, ggHasLabel_quotCenter_of_central_cover hJp f hf hk hl⟩


theorem ggTwE6Three_coordData
    {G : Type} [Group G] [Finite G] {Bs J X : Subgroup G} {g : G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hgBs : g ∈ Bs)
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) {ψ₀ : ↥X →* TwE6Delta.RecipeR K n}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ↥X ψ₀
      (ggGamma X hN).range) :
    GGE6ThreeCoordData Bs X J g hgBs (∃ m : ℕ, 1 ≤ m ∧
      GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) := by
  obtain ⟨κ, hF, hCall⟩ := ggTwE6Three_frameClass_of_tb hn hK h3 hTB
  have hJX : J ≤ X := hcomp.1.trans inf_le_left
  have hJp : Group.IsPerfect ↥J := ⟨hcomp.2.2.1⟩
  exact ggE6ThreeCoordData_mono (ggTwE6Three_label_of_subgroupOf hJX hJp)
    (ggE6Three_coordData_of_frameA hBs hSC hN hgBs hJX hgX hcomp
      (ggTwE6Three_hKer hBs hN hn h3 hK hTB) hF
      (P := fun J' => ∃ m : ℕ, 1 ≤ m ∧
        GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J' ⧸ Subgroup.center ↥J')) hCall)


theorem ggTBJTwE6Levi_threeP_of_label
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {Bs J X : Subgroup G} {g : G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs)
    (hJX : J ≤ X) (hgBs : g ∈ Bs) (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (bX : ↥Bs) (hbX1 : bX ≠ 1) (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 3)
    (hInn : GGInnerDiagOn Bs X) (hXc : commutator ↥X = ⊤)
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 5 ≤ Nat.card (ggGamma X hN).range) {n : ℕ} (hn : 2 ≤ n)
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hXl : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (h3 : 3 ∣ 2 ^ n + 1) {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4)) :
    GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J := by
  obtain ⟨hN, K, _, _, hK, ψ₀, hTB⟩ :=
    ggTwE6Three_tbGroup_of_label hRig hBs hSC hInn hXc hΛ hXl hrk
  have hC := ggTwE6Three_coordData hBs hSC hN hgBs hgX hcomp hn hK h3 hTB
  have hP : ¬ ∃ m : ℕ, 1 ≤ m ∧
      GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨m, hm, hlab⟩
    have hiso : GGLabelIso labJ ⟨.D, 4, m⟩ :=
      hRig labJ ⟨.D, 4, m⟩ _ hΛJ ⟨hm, by norm_num⟩ hJlab hlab
    apply hD4
    obtain ⟨t, r, n'⟩ := labJ
    unfold GGLabelIso at hiso
    rcases hiso with h | h | h | h | h | h | h | h
    · simp only [LargeEvenLabel.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl⟩
    all_goals simp at h
  exact ggTBJE6Levi_of_threeCoordData hgBs hJX hJg hC hP bX hbX1 hbXc hcardJ

theorem ggTBJTwE6LeviL_threeP
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 2 ≤ n) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ n hΛ hL _ labJ hΛJ hJlab _ hnc
  have hP : p = 3 ∧ 2 ≤ n := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, hn2⟩ := hP
  subst hp3
  have hst : LargeEvenStandardType 3 B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  have heq : labs = (⟨.twE6, 0, n⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (hRig ⟨.twE6, 0, n⟩ labs _ hΛ hlabs hL hhass)
  have hs : LargeEvenSplit 3 (⟨.twE6, 0, n⟩ : LargeEvenLabel) := heq ▸ hPs.1
  have h3 : 3 ∣ 2 ^ n + 1 := by
    rcases hs with ⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | ⟨hn1, -⟩
    · exact absurd hu (by simp [LargeEvenUntwisted])
    · exact h
    · simp at ht
    · have hn1' : n = 1 := hn1
      omega
  have hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4) := fun h =>
    hnc (Or.inl (Or.inl ⟨h.1, h.2, rfl, h3⟩))
  refine ggTBJE6LeviL_of_cellFn hH fun hBs hSC hJX hyBs hJg hgX hcomp bX hbX1 hbXc hcardJ => ?_
  obtain ⟨-, -, -, hperf⟩ := GGConfig.data_L hH.1
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hlabL : GGTableBTwE6ThreeLabel 3 (⟨.twE6, 0, n⟩ : LargeEvenLabel) := by
    unfold GGTableBTwE6ThreeLabel
    exact ⟨rfl, rfl, h3⟩
  have hM : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    ggInnerDiagOnLab_of_hasLabel hRig hInn hΛ hL hlabL hs
  exact ggTBJTwE6Levi_threeP_of_label hRig hBs hSC hJX hyBs hJg hgX hcomp bX hbX1 hbXc hcardJ
    hInn hperf (fun hN => ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hH.1 hM hN) hn2
    hΛ hL h3 hΛJ hJlab hD4

theorem ggTBJTwE6LeviK_threeP
    (hRig : GGLabelRigidInput) (hRK : GGTwE6ThreeNbrRankInput) :
    GGTBJETypeLeviK .twE6 fun p n labJ =>
      ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 2 ≤ n ∧ 3 ∣ 2 ^ n + 1) := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ _ n hΛ hK _ labJ hΛJ hJlab _ hnc
  have hP : p = 3 ∧ 2 ≤ n ∧ 3 ∣ 2 ^ n + 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, hn2, h3⟩ := hP
  subst hp3
  have hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4) := fun h =>
    hnc (Or.inl (Or.inl ⟨h.1, h.2, rfl, h3⟩))
  refine ggTBJE6LeviK_of_cellFn hH hJK fun hBs hSC hJK' hxBs hJg hgX hcomp bX hbX1 hbXc hcardJ => ?_
  obtain ⟨-, -, -, hperf⟩ := hH.data_K
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hInn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hbad : GGTwE6BadLabel 3 (⟨.twE6, 0, n⟩ : LargeEvenLabel) := by
    unfold GGTwE6BadLabel
    exact ⟨rfl, rfl, h3⟩
  have hM : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    ggInnerDiagOnLab_of_hasLabel hRig hInn hΛ hK hbad (largeEvenSplit_of_twE6BadLabel hbad)
  exact ggTBJTwE6Levi_threeP_of_label hRig hBs hSC hJK' hxBs hJg hgX hcomp bX hbX1 hbXc hcardJ
    hInn hperf (fun hN => hRK G 3 B Bs x L D J hH.1 rfl y K hnb hM hN
      (ggTorusSelfCent_ggGamma hN hSC)) hn2 hΛ hK h3 hΛJ hJlab hD4

end CFSG.StandardType

end
