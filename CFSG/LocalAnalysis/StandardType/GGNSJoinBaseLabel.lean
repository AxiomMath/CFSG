module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMChain
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGSecFiveJA2PhanDOfEsu
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapter
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
import CFSG.LocalAnalysis.StandardType.GGNSJoinToralA
import CFSG.LocalAnalysis.StandardType.GGNSJoinFrameA
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Parity
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrInputs
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2TBJ

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

@[expose] def NSRestEnnolaLab (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggRowP_EOmM p lab ∨ (ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨
    (lab.n = 1 ∧ p = 3 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab))

@[expose] def NSF4TwoLab (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.n = 1 ∧ p = 3 ∧ ggRowP_NF4 p lab

@[expose] def NSJA2RestLab (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (GGTwE6BadLabel p lab ∧ ¬ GGLabQFour p lab) ∨ (NSRestEnnolaLab p lab ∧ ¬ GGLabQFour p lab)

theorem nsJA2RestLab_tag {p : ℕ} {lab : LargeEvenLabel} (h : NSJA2RestLab p lab) :
    lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
  rcases h with ⟨⟨ht, -⟩, -⟩ | ⟨h, -⟩
  · exact ⟨by simp [ht], by simp [ht]⟩
  rcases h with ⟨ht, hr, -⟩ | ⟨⟨⟨ht, -⟩ | ⟨ht, hr⟩, -⟩, -⟩ | ⟨-, -, ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩⟩
  · exact ⟨by simp [ht], fun _ => by omega⟩
  · exact ⟨by simp [ht], by simp [ht]⟩
  · exact ⟨by simp [ht], fun _ => by omega⟩
  all_goals exact ⟨by simp [ht], by simp [ht]⟩

theorem ggLabelIso_n_eq {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (hA : lab.tag ≠ .A) (hD : lab.tag = .twD → lab.rank ≠ 2) : lab.n = lab'.n := by
  rcases h with rfl | ⟨-, -, -, hn⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨h₁, -⟩ | ⟨-, h₁⟩
  · rfl
  · exact hn
  · rw [h']
  · rw [h']
  · rw [h']
  · rw [h']
  · exact absurd (congrArg LargeEvenLabel.rank h₁) (hD (congrArg LargeEvenLabel.tag h₁))
  · exact absurd (congrArg LargeEvenLabel.tag h₁) hA

theorem largeEvenSplit_untwisted_of_dvd_add {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hu : LargeEvenUntwisted lab.tag) (hs : LargeEvenSplit p lab)
    (hd : p ∣ 2 ^ lab.n + 1) : lab.n = 1 ∧ p = 3 := by
  rcases hs with ⟨-, h1⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | h
  · exact (not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 h1 hd).elim
  · exact (hnu hu).elim
  · rcases ht with ht | ht <;> rw [ht] at hu <;> simp [LargeEvenUntwisted] at hu
  · exact h

theorem ggLabelIso_eq_of_untwisted {lab' lab : LargeEvenLabel} (hiso : GGLabelIso lab' lab)
    (ht : (lab'.tag = .D ∧ 4 ≤ lab'.rank) ∨ lab'.tag = .E7 ∨ lab'.tag = .E8 ∨ lab'.tag = .F4) :
    lab' = lab := by
  obtain ⟨t, r, n⟩ := lab'
  rcases hiso with h | ⟨hBC, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact h
  · simp only at hBC ht
    rcases hBC with rfl | rfl <;> simp at ht
  all_goals
    simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    simp at ht

theorem ggCoxeterMatrixD_three :
    ggCoxeterMatrixD 3 = (CoxeterMatrix.A 3).reindex (Equiv.swap 0 1) := by
  apply CoxeterMatrix.ext
  ext i j
  fin_cases i <;> fin_cases j <;> (rw [CoxeterMatrix.reindex_apply]; decide)

theorem nsRestEnnolaLab_cases {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : NSRestEnnolaLab p lab) :
    (∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      GGTBTorRowAt p lab r m N C M ∧ ((GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) ∧ 3 ≤ N)) ∨
    (lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨t, r, n⟩ := lab
  rcases h with ⟨ht, hr, hodd, hpn⟩ | ⟨⟨⟨ht, hr3⟩ | ⟨ht, hr3⟩, hpn⟩, hn, hr⟩ | ⟨hn, hp3, hE⟩
  ·
    exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inr ⟨ht, hpn, hodd⟩),
      Or.inl (Or.inr ⟨r, Equiv.refl _, by simp only at hr; omega,
        (ggCoxeterMatrix_reindex_refl _).symm⟩), by simp only at hr ⊢; omega⟩
  ·
    simp only at ht hr3 hpn hn hr
    subst hn
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpn)
    subst hp3
    rcases hr with rfl | rfl
    · refine Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.aInd (Or.inr ht) (by decide : ¬ 3 ∣ 3 + 1) ?_,
        Or.inl (Or.inl ⟨3, Equiv.refl _, le_rfl, (ggCoxeterMatrix_reindex_refl _).symm⟩), le_rfl⟩
      simpa [ggTorM, ht] using hpn
    · exact Or.inr ⟨ht, rfl, rfl, hpn⟩
  ·
    simp only at ht hr3 hpn hn hr
    subst hr3
    exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inr ⟨ht, hpn, (by decide : Odd 3)⟩),
      Or.inl (Or.inl ⟨3, Equiv.swap 0 1, le_rfl, ggCoxeterMatrixD_three⟩), le_rfl⟩
  · rcases hE with ⟨ht, hr, hev, hpn⟩ | ⟨ht, hpn⟩ | ⟨ht, -⟩
    ·
      exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inl ⟨ht, Or.inr ⟨hpn, hev⟩⟩),
        Or.inl (Or.inr ⟨r, Equiv.refl _, hr, (ggCoxeterMatrix_reindex_refl _).symm⟩),
        by simp only at hr ⊢; omega⟩
    ·
      exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.e7 ht (dvd_mul_of_dvd_right hpn _),
        Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩)),
        by norm_num⟩
    ·
      exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.e8Three ht hp3,
        Or.inr (Or.inr (Or.inr ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩)),
        by norm_num⟩

theorem weylOfType_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hMC : GGIntCartan M C) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range) :
    GGWeylOfType p M (ggAutomizer X Bs) := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨e, fun i => ?_⟩
  rw [he i]
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem nsBaseFrame_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} {Bs X : Subgroup G}
    {x : G} (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hm : Odd m) (hpm : p ∣ m)
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} (hMC : GGIntCartan M C)
    (hM : GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) (hN3 : 3 ≤ N)
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range) (hx : orderOf x = p)
    (hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x) :
    ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
      (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer X Bs) ∧
        Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hW := weylOfType_of_torData hp2 hm hpm hMC hBs hS hN hTor
  refine ⟨Fin N, inferInstance, M, hM, hW, ?_, by rw [Fintype.card_fin]; exact hN3⟩
  have hle := card_le_pow_mul_card_of_weylOfType hW ((Subgroup.zpowers x).subgroupOf Bs)
    fun b hb => Subgroup.mem_subgroupOf.mpr (hFix b hb)
  have hF : Nat.card ((Subgroup.zpowers x).subgroupOf Bs) ≤ p := by
    rw [← hx, ← Nat.card_zpowers]
    exact Nat.card_le_card_of_injective
      (fun b => (⟨((b : ↥Bs) : G), Subgroup.mem_subgroupOf.mp b.2⟩ : Subgroup.zpowers x))
      fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
  rw [Fintype.card_fin] at hle ⊢
  rw [pow_succ]
  exact hle.trans (Nat.mul_le_mul_left _ hF)

theorem nsBaseFrame_of_tbTorLab (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hL : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        ((GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) ∧ 3 ≤ N)) p Bs L) :
    ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
      (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer L Bs) ∧
        Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL := by
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨_lab, _r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, ⟨hM, hN3⟩, hBsI, hlift,
    hT, -⟩ := l05nPlQ_marking_with hW hLift hp2
      (fun _ _ N _ M => (GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) ∧ 3 ≤ N) hL
  have hTor := hT ↥L (ggQuotHom θ) (ggGamma L hN).range
    (ggTorusTBGroup_of_L hcfg hperf θ hN hBsI hlift)
  obtain ⟨hom, hpm, -, hMC⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  exact nsBaseFrame_of_torData hp hp2 hBs hcfg.2.1.2.2.2 hN hom hpm hMC hM hN3 hTor
    (orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1) hFix

theorem nsBaseFrame_twA5Three
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧
      3 ∣ 2 ^ lab.n + 1) p Bs L) :
    ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
      (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer L Bs) ∧
        Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL := by
  have hp3 : p = 3 := by
    obtain ⟨-, lab, -, hraw⟩ := hL
    obtain ⟨_, _, _, _, -, -, _, ⟨⟨-, -, hp3, -⟩, -, -⟩⟩ := largeEvenRawDatum_exists hraw
    exact hp3
  subst hp3
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨⟨htw, hr5, -, hdvd⟩, hN', hBsI⟩ := hP
    exact ⟨⟨⟨htw, by omega, hdvd, by omega⟩, hr5, rfl⟩,
      Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htw], by simp [htw], hdvd⟩), hN', hBsI⟩
  have hr : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma L hN).range := by
    intro hN
    have hcard := Line63.H5.ggUnitDvd63BstarRankInput_holds G 3 B Bs x L D J hcfg hM
    have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp.pos
  have hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
      3 ∣ ggTorM lab) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨⟨htw, hr5, -, hdvd⟩, hN', hBsI⟩ := hP
    exact ⟨⟨htw, hr5, by simpa [ggTorM, htw] using hdvd⟩, hN', hBsI⟩
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hMark hr
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  exact nsBaseFrame_of_torData hp (by norm_num) hBs hcfg.2.1.2.2.2 hN hodd hpq (ggIntCartan_A 5)
    (Or.inl (Or.inl ⟨5, Equiv.refl _, by norm_num, (ggCoxeterMatrix_reindex_refl _).symm⟩))
    (by norm_num) hTor (orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1) hFix

section Inputs


@[expose] def NSJA2LabInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop)
    (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 → GGInnerDiagOnLabel S p Bs L →
      ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs, GGIsReflection p r ∧ GGIsReflection p r' ∧
        orderOf (r * r') = 3

theorem nsJA2LabInputOf_rest_of_qFour {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRig : GGLabelRigidInput) (hQ4 : NSQFourInputOf T) : NSJA2LabInputOf T NSJA2RestLab := by
  intro G _ _ p B Bs x L D J 𝒦 hreg hlab
  exfalso
  obtain ⟨lab₁, hΛ₁, hhas₁, R₁, _, I₁, F₁, θ₁, hS, -⟩ := largeEvenMarking_exists_hasLabel hlab
  obtain ⟨lab₂, hΛ₂, hhas₂, R₂, _, I₂, F₂, θ₂, hQ, -⟩ :=
    largeEvenMarking_exists_hasLabel (hQ4 G p B Bs x L D J 𝒦 hreg)
  have hn : lab₁.n = lab₂.n := ggLabelIso_n_eq (hRig lab₁ lab₂ _ hΛ₁ hΛ₂ hhas₁ hhas₂)
    (nsJA2RestLab_tag hS).1 (nsJA2RestLab_tag hS).2
  have h4 : ¬ GGLabQFour p lab₁ := by
    rcases hS with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h
  exact h4 (by unfold GGLabQFour at hQ ⊢; omega)

end Inputs

end NSJoin


theorem ggL_baseLabel_of_nonSplit
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie p L) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∨ ggRowP_EOmM p lab ∨ ggRowP_ETwE6 p lab ∨
      (lab.n = 1 ∧ p = 3 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨
        ggRowP_NF4 p lab))) p Bs L := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hST : LargeEvenStandardType p B x L := hcfg.1.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hST.1
  refine GGInnerDiagOnLabel.mono_label_of_hasLabel ?_
    (ggX_ennola_of_nonSplit hcfg hpres hle3 (Or.inl rfl) hns)
  intro lab' hlab' hhas' hE
  have hiso : GGLabelIso lab' lab := ggLabelRigidInput_holds lab' lab _ hlab' hlab hhas' hhas
  have hsplit : ∀ (hu : LargeEvenUntwisted lab'.tag),
      ((lab'.tag = .D ∧ 4 ≤ lab'.rank) ∨ lab'.tag = .E7 ∨ lab'.tag = .E8 ∨ lab'.tag = .F4) →
      p ∣ 2 ^ lab'.n + 1 → lab'.n = 1 ∧ p = 3 := fun hu ht hd => by
    have heq := NSJoin.ggLabelIso_eq_of_untwisted hiso ht
    subst heq
    exact NSJoin.largeEvenSplit_untwisted_of_dvd_add hp hp2 hu hP.1 hd
  rcases hE with (hE | hE | hE | hE | hE | hE) | ⟨hF, hp3, hd⟩
  · exact Or.inl hE
  · obtain ⟨hn, hp3⟩ := hsplit (by rw [hE.1]; trivial) (Or.inl ⟨hE.1, hE.2.1⟩) hE.2.2.2
    exact Or.inr (Or.inr (Or.inr ⟨hn, hp3, Or.inl hE⟩))
  · exact Or.inr (Or.inl hE)
  · exact Or.inr (Or.inr (Or.inl hE))
  · obtain ⟨hn, hp3⟩ := hsplit (by rw [hE.1]; trivial) (Or.inr (Or.inl hE.1)) hE.2
    exact Or.inr (Or.inr (Or.inr ⟨hn, hp3, Or.inr (Or.inl hE)⟩))
  · obtain ⟨hn, hp3⟩ := hsplit (by rw [hE.1]; trivial) (Or.inr (Or.inr (Or.inl hE.1))) hE.2
    exact Or.inr (Or.inr (Or.inr ⟨hn, hp3, Or.inr (Or.inr (Or.inl hE))⟩))
  · obtain ⟨hn, -⟩ := hsplit (by rw [hF.1]; trivial) (Or.inr (Or.inr (Or.inr hF.1))) hd
    exact Or.inr (Or.inr (Or.inr ⟨hn, hp3, Or.inr (Or.inr (Or.inr hF))⟩))

namespace NSJoin

theorem not_f4Three_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hL : GGInnerDiagOnLabel GGF4ThreeLabel p Bs L) :
    False := by
  have hp3 : p = 3 := by
    obtain ⟨-, lab, -, hraw⟩ := hL
    obtain ⟨_, _, _, _, -, -, _, ⟨⟨-, hp3, -⟩, -, -⟩⟩ := largeEvenRawDatum_exists hraw
    exact hp3
  subst hp3
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hM : GGF4ThreeMarking Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP) hL
  have hR : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G), 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    fun hN => ggF4Three_rank_of_marking
      (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds) hconf
      (ggRouteCfg_noTransvection hcfg) hM hN
  obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ := ggF4Three_framePair_of_rank hconf hM hR
  have hle : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
  have hx₁ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₁) hr₁
  have hx₂ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₂) hr₂
  rcases ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hx₁ hx₂ with h | h
  · exact absurd (h4.trans (orderOf_dvd_of_pow_eq_one h)) (by decide)
  · exact absurd (h4.trans (orderOf_dvd_of_pow_eq_one h)) (by decide)

theorem nsBaseFrameInputOf_of_lab {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hTBF : GGTBFixInput) (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) :
    NSBaseFrameInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0
  obtain ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ := hcfg0
  have hlab := ggL_baseLabel_of_nonSplit hcfg hpres (hT3 hTM) hns
  have h' : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
        ((GGTwE6BadLabel p lab ∨ GGTBTwE6PlusLabel p lab) ∨
          (NSF4TwoLab p lab ∨ NSRestEnnolaLab p lab))) p Bs L :=
    hlab.mono' fun lab hl => by
      rcases hl with hl | hl | hl | ⟨hn, hp3, hl | hl | hl | hl⟩
      · by_cases hq : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, hq⟩))))
        · exact Or.inl ⟨hl, hq⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
      · by_cases h3 : p = 3
        · exact Or.inr (Or.inl (Or.inl ⟨hl.1, h3, h3 ▸ hl.2⟩))
        · exact Or.inr (Or.inl (Or.inr ⟨hl.1, hl.2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn, hp3, Or.inl hl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn, hp3, Or.inr (Or.inl hl)⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn, hp3, Or.inr (Or.inr hl)⟩))))
      · exact Or.inr (Or.inr (Or.inl ⟨hn, hp3, hl⟩))
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  ·
    obtain ⟨K, hKf, hKfin, hKchar, f, n, ψ, hcard, hn4, hker, hrange, hdvd, hacts, -⟩ :=
      ggNSLie_cover_of_esu (X := L) h
    letI : Field K := hKf
    letI : Finite K := hKfin
    letI : CharP K 2 := hKchar
    have hh : GGNSLocalHyp p B Bs K f n ψ :=
      ggNSLocalHyp_of_routeCfg hcfg (Or.inl rfl) hcard hn4 hker hrange hdvd hacts
    obtain ⟨c, hc⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds hh
    have hh' := hh.comp_conj c
    have hr : (ψ.comp (MulAut.conj c).toMonoidHom).range = L := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
        Subgroup.map_top, hrange]
    have hpos := ggNSDiag_position hh' hc
    rw [hr] at hpos
    have htor := ggNSDiag_toral_bound hh' hc
    rw [hr] at htor
    have hFix := nsFixInput_of_tbFix (T := T) hTBF G p B Bs x L D J 𝒦
      ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩
    have hconf : GGConfig p B Bs x L D J := hcfg.1.1
    obtain ⟨hp, hBs_ea, hxBs, -, -⟩ := hconf.tableB_facts
    haveI : Fact p.Prime := ⟨hp⟩
    have hS : LargeEvenSStar p B x L := hconf.1.2.2.2.2.2.2.1
    have hx : orderOf x = p := orderOf_eq_prime (hBs_ea.2 x hxBs) hS.2.2.1
    exact nsBaseFrame_of_posSU hn4 hpos htor hx hFix
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact nsBaseFrame_twE6_of_cfg ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩
      (GGInnerDiagOnLabel.elim_or h)
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact (not_f4Three_of_cfg hcfg hpres (hT3 hTM) (h.mono' fun lab hl => by
      obtain ⟨hn, hp3, htag, -⟩ := hl
      exact ⟨htag, hp3, by rw [hn]; norm_num⟩)).elim
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  have hFix := nsFixInput_of_tbFix (T := T) hTBF G p B Bs x L D J 𝒦
    ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have h' : GGInnerDiagOnLabel (fun p lab => (∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        ((GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) ∧ 3 ≤ N)) ∨
      (lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)) p Bs L :=
    h.mono' fun lab hl => nsRestEnnolaLab_cases hp hl
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  · exact nsBaseFrame_of_tbTorLab hW hLift hconf hFix h
  · exact nsBaseFrame_twA5Three hconf hFix h


theorem nsJA2InputOf_of_lab {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRest : NSJA2LabInputOf T NSJA2RestLab) : NSJA2InputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0
  obtain ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ := hcfg0
  have hlab := ggL_baseLabel_of_nonSplit hcfg hpres (hT3 hTM) hns
  have h' : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
        (((GGTwE6BadLabel p lab ∧ ¬ GGLabQFour p lab) ∨
          ((GGLabQFour p lab ∧ GGTwE6BadLabel p lab) ∨ GGTBTwE6PlusLabel p lab)) ∨
          (NSF4TwoLab p lab ∨ ((GGLabQFour p lab ∧ GGTBRowR5O2 p lab) ∨
            (NSRestEnnolaLab p lab ∧ ¬ GGLabQFour p lab))))) p Bs L :=
    hlab.mono' fun lab hl => by
      rcases hl with hl | hl | hl | ⟨hn, hp3, hl | hl | hl | hl⟩
      · by_cases hq : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl ⟨hl, hq⟩),
            fun h4 => by simp only [GGLabQFour] at h4; have := hq.1; omega⟩)))
        · exact Or.inl ⟨hl, hq⟩
      · by_cases h4 : GGLabQFour p lab
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, hl.1, by have := hl.2.1; omega, hl.2.2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl hl, h4⟩)))
      · by_cases h3 : p = 3
        · by_cases h4 : GGLabQFour p lab
          · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨h4, hl.1, h3, h3 ▸ hl.2⟩)))
          · exact Or.inr (Or.inl (Or.inl ⟨⟨hl.1, h3, h3 ▸ hl.2⟩, h4⟩))
        · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hl.1, hl.2, h3⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr ⟨hn, hp3, Or.inl hl⟩),
          fun h4 => by simp only [GGLabQFour] at h4; omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr ⟨hn, hp3, Or.inr (Or.inl hl)⟩),
          fun h4 => by simp only [GGLabQFour] at h4; omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr ⟨hn, hp3, Or.inr (Or.inr hl)⟩),
          fun h4 => by simp only [GGLabQFour] at h4; omega⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hn, hp3, hl⟩))
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  · exact nsJA2_of_esuLabel ggSecFiveNSCornerInput_holds hcfg h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · rcases GGInnerDiagOnLabel.elim_or h with h | h
    · exact hRest G p B Bs x L D J 𝒦 ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩
        (h.mono' fun lab hl => Or.inl hl)
    rcases GGInnerDiagOnLabel.elim_or h with h | h
    · exact nsJA2_of_twE6Bad hT3 ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ h
    · exact nsJA2_of_twE6Plus hT3 ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ h
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact (not_f4Three_of_cfg hcfg hpres (hT3 hTM) (h.mono' fun lab hl => by
      obtain ⟨hn, hp3, htag, -⟩ := hl
      exact ⟨htag, hp3, by rw [hn]; norm_num⟩)).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact nsJA2_of_rowR5O2 hT3 ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ h
  · exact hRest G p B Bs x L D J 𝒦 ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩
      (h.mono' fun lab hl => Or.inr hl)

end NSJoin

end CFSG.StandardType

end
