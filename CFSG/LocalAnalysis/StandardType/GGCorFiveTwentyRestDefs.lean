module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTorusWeylElt (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) (n : L') :
    Prop :=
  ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹

section Congr

variable {G : Type} [Group G] {M : Type} [Group M]

theorem GGIsPseudoReflection.congr {p : ℕ} {A : Subgroup M} {Bs : Subgroup G} (e : ↥A ≃* ↥Bs)
    {φ : MulAut ↥A} (h : GGIsPseudoReflection p φ) : GGIsPseudoReflection p (MulAut.congr e φ) := by
  refine ⟨by rw [← map_pow, h.1, map_one], ?_⟩
  have hfix : Nat.card {b : ↥Bs // MulAut.congr e φ b = b} = Nat.card {a : ↥A // φ a = a} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun b => ?_)
    rw [MulAut.congr_apply]
    show e (φ (e.symm b)) = b ↔ φ (e.symm b) = e.symm b
    constructor
    · intro hb
      have h1 := congrArg e.symm hb
      rwa [MulEquiv.symm_apply_apply] at h1
    · intro hb
      rw [hb, MulEquiv.apply_symm_apply]
  rw [hfix, h.2]
  exact Nat.card_congr e.toEquiv

end Congr

section Gamma

variable {G : Type} [Group G] {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))

theorem ggGamma_injective_of_inf_eq_bot (h : Bs ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    Function.Injective (ggGamma X hBsN) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro b hb
  rw [MonoidHom.mem_ker, ggGamma_eq_one_iff] at hb
  have hb' : (b : G) ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := ⟨b.2, hb⟩
  rw [h, Subgroup.mem_bot] at hb'
  exact Subgroup.mem_bot.mpr (Subtype.ext hb')

theorem conj_mem_normalizer_range_ggGamma {g : G} (hgX : g ∈ X)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    MulAut.conj (⟨g, hgX⟩ : X) ∈
      Subgroup.normalizer ((ggGamma X hBsN).range : Set (MulAut X)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : g * b * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hg b).mp b.2
    exact ⟨⟨g * b * g⁻¹, hb⟩, ggGamma_conj X hBsN ⟨g, hgX⟩ b hb⟩
  · rintro ⟨b, hb⟩
    have hb' : g⁻¹ * b * g⁻¹⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) b).mp b.2
    refine ⟨⟨g⁻¹ * b * g⁻¹⁻¹, hb'⟩, (ggGamma_conj X hBsN (⟨g, hgX⟩ : X)⁻¹ b hb').trans ?_⟩
    rw [hb, map_inv]
    group

theorem congr_ggConjAut_ggGamma (hinj : Function.Injective (ggGamma X hBsN)) {g : G}
    (hgX : g ∈ X) (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hn : MulAut.conj (⟨g, hgX⟩ : X) ∈
      Subgroup.normalizer ((ggGamma X hBsN).range : Set (MulAut X))) :
    MulAut.congr (MonoidHom.ofInjective hinj).symm
      (ggConjAut (ggGamma X hBsN).range hn) = ggConjAut Bs hg := by
  refine MulEquiv.ext fun b => ?_
  show (MonoidHom.ofInjective hinj).symm
    (ggConjAut (ggGamma X hBsN).range hn (MonoidHom.ofInjective hinj b)) = ggConjAut Bs hg b
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [ggConjAut_apply, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply]
  exact (ggGamma_conj X hBsN ⟨g, hgX⟩ b _).symm

theorem mem_normalizer_of_ggTorusWeylElt [Finite G] {p : ℕ}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {n : X}
    (hn : GGTorusWeylElt p (ggGamma X hBsN).range n) :
    (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  set γ := ggGamma X hBsN with hγ
  have hWB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨htp, htA⟩ := hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
    simpa using hWB w hw)
  simpa using Subgroup.inv_mem _ h

end Gamma

section Config

variable {G : Type} [Group G] [Finite G]

theorem bstar_inf_centralizer_ggG0_eq_bot {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    Bs ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ := by
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hxG0 : x ∉ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
    obtain ⟨⟨y, K, hK⟩, -⟩ := hst.2.2.2 D J hDJ
    intro hx
    apply hK.2.2.2
    have hxK : x ∈ Subgroup.centralizer (K : Set G) :=
      Subgroup.centralizer_le (fun k hk => le_ggG0_of_ggNbr hK hk) hx
    have hbot : ⁅K, Subgroup.zpowers x⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.zpowers_le.mpr hxK
    rw [hbot]
    exact bot_le
  have hCL := inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1 hLx hS.2.2.2.2
  refine (Subgroup.eq_bot_iff_forall _).mpr fun b hb => ?_
  by_contra hb1
  have hbL : b ∈ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hb.1, Subgroup.centralizer_le (le_ggG0_left p B x L D J) hb.2⟩
  rw [hCL] at hbL
  have hxp : orderOf x = p := orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1
  have hbp : orderOf b = p := orderOf_eq_prime (hBs.2 b hb.1) hb1
  have heq : Subgroup.zpowers b = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbL)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hxp, hbp])
  have hxb : x ∈ Subgroup.zpowers b := heq ▸ Subgroup.mem_zpowers x
  exact hxG0 ((Subgroup.zpowers_le.mpr hb.2) hxb)

theorem le_twoLocalRank_of_torusLift {p r : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    (hlift : GGTorusLift p r R) : r ≤ LargeEvenTwoLocalRank p G := by
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, -⟩ := hlift X (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX
  have hEG : IsElemAbelian p (E.map X.subtype) := isElemAbelian_map hE X.subtype
  have hcard : Nat.card (E.map X.subtype) = p ^ r := by
    rw [← Nat.card_congr (E.equivMapOfInjective _ X.subtype_injective).toEquiv, hEcard]
  have hUne : U.map X.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map X.subtype : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  exact le_twoLocalRank hp.one_lt hTL (le_pRank_of_le hp.one_lt
    ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)) hEG hcard)

theorem pow_le_card_bstar_of_torusLift {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    (hlift : GGTorusLift p r R) : p ^ r ≤ Nat.card Bs := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  calc p ^ r ≤ p ^ LargeEvenTwoLocalRank p G :=
        Nat.pow_le_pow_right hp.pos (le_twoLocalRank_of_torusLift hp hX θ hlift)
    _ = Nat.card B := hBc.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1

end Config

@[expose] def GGWeylPseudoReflGenInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs (ggG0 p B x L D J) →
      GGPseudoReflGenerated p (ggAutomizer (ggG0 p B x L D J) Bs)

@[expose] def GGWeylCentralizerScalarInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs (ggG0 p B x L D J) →
      ∀ ψ ∈ ggAutomizer ⊤ Bs, (∀ w ∈ ggAutomizer (ggG0 p B x L D J) Bs, ψ * w = w * ψ) →
        GGIsScalar ψ

@[expose] def GGCorFiveTwentyOuterInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs (ggG0 p B x L D J) →
      ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
        ggConjAut Bs hg ∈ Subgroup.normalizer
          (ggAutomizer (ggG0 p B x L D J) Bs : Set (MulAut ↥Bs)) →
        (¬ ∃ w ∈ ggAutomizer (ggG0 p B x L D J) Bs, ∀ v ∈ ggAutomizer (ggG0 p B x L D J) Bs,
          ggConjAut Bs hg * v * (ggConjAut Bs hg)⁻¹ = w * v * w⁻¹) →
        g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGInnerOnWeylInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs (ggG0 p B x L D J) →
      ∀ φ ∈ ggAutomizer ⊤ Bs,
        φ ∈ Subgroup.normalizer (ggAutomizer (ggG0 p B x L D J) Bs : Set (MulAut ↥Bs)) →
        ∃ w ∈ ggAutomizer (ggG0 p B x L D J) Bs, ∀ v ∈ ggAutomizer (ggG0 p B x L D J) Bs,
          φ * v * φ⁻¹ = w * v * w⁻¹

theorem ggCorFiveTwentyOuterInputOn_of_inner {S : ℕ → LargeEvenLabel → Prop}
    (h : GGInnerOnWeylInputOn S) : GGCorFiveTwentyOuterInputOn S := by
  intro G _ _ p B Bs x L D J hH hM g hg hN hout
  exact absurd (h G p B Bs x L D J hH hM _
    (ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg) hN) hout

section Cover

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem GGCorFiveTwentyHyp.label_or (hH : GGCorFiveTwentyHyp p B Bs x L D J)
    (S : ℕ → LargeEvenLabel → Prop) :
    GGInnerDiagOnLabel S p Bs (ggG0 p B x L D J) ∨
      GGInnerDiagOnLabel (fun p lab => ¬ S p lab) p Bs (ggG0 p B x L D J) :=
  (hH.2.2.2.2.label S p).elim_or

end Cover

theorem ggWeylPseudoReflGenInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGWeylPseudoReflGenInputOn S) (h₂ : GGWeylPseudoReflGenInputOn fun p lab => ¬ S p lab) :
    GGWeylPseudoReflGenInput := by
  intro G _ _ p B Bs x L D J hH
  rcases hH.label_or S with hM | hM
  · exact h₁ G p B Bs x L D J hH hM
  · exact h₂ G p B Bs x L D J hH hM

theorem ggWeylCentralizerScalarInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGWeylCentralizerScalarInputOn S)
    (h₂ : GGWeylCentralizerScalarInputOn fun p lab => ¬ S p lab) :
    GGWeylCentralizerScalarInput := by
  intro G _ _ p B Bs x L D J hH
  rcases hH.label_or S with hM | hM
  · exact h₁ G p B Bs x L D J hH hM
  · exact h₂ G p B Bs x L D J hH hM

theorem ggCorFiveTwentyOuterInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGCorFiveTwentyOuterInputOn S)
    (h₂ : GGCorFiveTwentyOuterInputOn fun p lab => ¬ S p lab) :
    GGCorFiveTwentyOuterInput := by
  intro G _ _ p B Bs x L D J hH
  rcases hH.label_or S with hM | hM
  · exact h₁ G p B Bs x L D J hH hM
  · exact h₂ G p B Bs x L D J hH hM

end CFSG.StandardType

end
