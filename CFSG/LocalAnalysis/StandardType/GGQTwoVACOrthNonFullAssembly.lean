module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthNonFullGuard
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalMovingAutomizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalFrame
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXA5
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightBasic
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Quasithin.Background.GoldschmidtTDE68Qs
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.StandardType

open Module Polynomial QuadraticMap CFSG.Assembly
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.StandardType.OmNsRootGen

theorem exists_torus_data_of_selfCentralizing
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {ℓ : ℕ} (hdim : Module.finrank K V = 2 * ℓ) (h4 : 4 ≤ ℓ)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q)
    (hE : IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ (ℓ - 1))
    (hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A) :
    ∃ r : ℕ, Nonempty (OrthTorus.TBJOmData Q 3 A r) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.exists_threeSingular hQ hdim (by
      by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · exact Or.inl ⟨hplus, by omega⟩
      · exact Or.inr ⟨hplus, h4⟩)
  have hne : ∃ b ∈ A, b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr h
    rw [hbot, Subgroup.card_bot] at hcard
    have hp : 1 < 3 ^ (ℓ - 1) := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hc : ∀ e ∈ A, ∀ e' ∈ A, e * e' = e' * e := by
    intro e he e' he'
    exact congrArg (fun z : ↥A => (z : V ≃ₗ[K] V)) (hE.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
  obtain ⟨r, τ, F, D, i₁, i₂, i₃, c, θ, hτF, hinj, hrange, hdimD, hcp, hfix, hT',
      hroots, hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsign, hnoFix, hexFix⟩ :=
    OrthTorus.exists_torus_blocks (p := 3) (by decide : (3 : ℕ) ≠ 2)
      (Or.inr (by norm_num [hK])) hQ hT hAΩ hE.2 hc hmax hne
  let Δ : OrthTorus.TBJOmData Q 3 A r :=
    { τ := τ, F := F, D := D, c := c, θ := θ, τ_eq := hτF, τ_inj := hinj, τ_range := hrange,
      finrank_D := hdimD, c_pow := hcp, c_fix := hfix, c_twist := hT', c_roots := hroots,
      θ_inj := hθinj, θ_range := hθrange, θ_act := hθact, normalizer := hnorm, swapMove := hswap,
      dinvMove := hdinv, signMove := hsign, noFixed := hnoFix, exFixed := hexFix }
  exact ⟨r, ⟨Δ⟩⟩


theorem four_dvd_of_specialBlock
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup ↥(orthDerived Q)}
    (hAΩ : E.map (orthDerived Q).subtype ≤ orthDerived Q)
    {r : ℕ} (Δ : OrthTorus.TBJOmData Q 3 (E.map (orthDerived Q).subtype) r)
    {f₀ : Fin r → Multiplicative (ZMod 3)} {t : V ≃ₗ[K] V} (hτ : Δ.τ f₀ = t)
    (hh : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (Δ.τ f₀).toLinearMap)
    {Jbar : Subgroup ↥(orthDerived Q)}
    (hsp : Jbar = (specialBlock Q t (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))
    (hJns : ¬ Group.IsSolvable ↥Jbar) :
    4 ∣ Nat.card (ggAutomizer Jbar E) := by
  have hsp' : Jbar = (specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1)).subgroupOf
      (orthDerived Q) := by
    rw [hτ]
    exact hsp
  have hns : ¬ Group.IsSolvable
      ↥((specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)) := by
    rw [← hsp']
    exact hJns
  have h4dvd := QTwoOrthogonalCav.four_dvd_moving_of_data hK hQ hAΩ Δ f₀ hh hns
  have hcardAut : Nat.card (ggAutomizer
        (specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1) ⊓ orthDerived Q)
        (E.map (orthDerived Q).subtype)) =
      Nat.card (ggAutomizer
        ((specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)) E) := by
    rw [← Subgroup.subgroupOf_map_subtype]
    rw [F4AutWeyl.ggAutomizer_map_eq (orthDerived Q).subtype_injective
      ((specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)) E rfl,
      Subgroup.card_map_of_injective (MulAut.congr _).injective]
  rw [hsp', ← hcardAut]
  exact h4dvd

theorem four_dvd_of_supportedFixedDerived_large
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {ℓ : ℕ} (hdim : Module.finrank K V = 2 * ℓ) (h4 : 4 ≤ ℓ)
    (htype : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Odd ℓ)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E)
    {t : ↥(orthDerived Q)} (htE : t ∈ E) (ht3 : orderOf t = 3)
    {Jbar : Subgroup ↥(orthDerived Q)}
    (hfix : Jbar = (supportedFixedDerived Q (t : V ≃ₗ[K] V)).subgroupOf (orthDerived Q))
    (h6 : 6 ≤ Module.finrank K (fixedSpace (t : V ≃ₗ[K] V))) :
    4 ∣ Nat.card (ggAutomizer Jbar E) := by
  obtain ⟨k, U, e, u, c, tK, f, f', hF, hkℓ, hf, hf', hQf, hQf', hff'⟩ :=
    ggQ2OrthNonFull_frame hQ hK hdim h4 htype hE hsc
  have h4dvd := four_dvd_ggAutomizer_of_supportedFixedDerived hQ hF hdim hkℓ hf hf'
    hQf hQf' hff' htE ht3 h6
  rwa [hfix]

theorem four_dvd_ggAutomizer_or_minusFour_of_nonFull
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {ℓ : ℕ} (hdim : Module.finrank K V = 2 * ℓ) (h4 : 4 ≤ ℓ)
    (htype : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Odd ℓ)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ (ℓ - 1))
    (hsc : ∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E)
    {t : ↥(orthDerived Q)} (htE : t ∈ E) (ht3 : orderOf t = 3)
    {Jbar : Subgroup ↥(orthDerived Q)}
    (hJ : IsComponentOf Jbar (Subgroup.centralizer ({t} : Set ↥(orthDerived Q)))) :
    4 ∣ Nat.card (ggAutomizer Jbar E) ∨
      (Jbar = (supportedFixedDerived Q (t : V ≃ₗ[K] V)).subgroupOf (orthDerived Q) ∧
        Module.finrank K (fixedSpace (t : V ≃ₗ[K] V)) = 4 ∧
        ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
          (Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype)) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A := E.map (orthDerived Q).subtype
  have hAΩ : A ≤ orthDerived Q := Subgroup.map_subtype_le E
  have hAE : IsElemAbelian 3 A := hE.map (orthDerived Q).subtype
  have hcardA : Nat.card A = 3 ^ (ℓ - 1) := by
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective, hcard]
  have hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A := by
    intro g hg hg3 hcomm
    refine Subgroup.mem_map_of_mem _ (hsc ⟨g, hg⟩ (fun z hz => ?_) (Subtype.ext ?_))
    · exact Subtype.ext (hcomm (z : V ≃ₗ[K] V) (Subgroup.mem_map_of_mem _ hz))
    · simpa using hg3
  obtain ⟨r, ⟨Δ⟩⟩ := exists_torus_data_of_selfCentralizing hK hQ hdim h4 hAΩ hAE hcardA hmax
  have htA : (t : V ≃ₗ[K] V) ∈ A := Subgroup.mem_map_of_mem _ htE
  obtain ⟨f₀, hτ⟩ : ∃ f₀, Δ.τ f₀ = (t : V ≃ₗ[K] V) := by
    rw [← Δ.τ_range] at htA
    exact htA
  have ht1 : Δ.τ f₀ ≠ 1 := by
    intro h
    have h1 : t = 1 := Subtype.ext (hτ.symm.trans h)
    rw [h1, orderOf_one] at ht3
    omega
  have hx := Δ.oddOrderIsometry (by decide) hQ hAΩ f₀
  have hh : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (Δ.τ f₀).toLinearMap :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_mem hx (by norm_num [hK]) ht1
  let : Group.IsPerfect ↥Jbar := ⟨hJ.2.2.1⟩
  let : IsSimpleGroup (↥Jbar ⧸ Subgroup.center ↥Jbar) := hJ.2.2.2
  let : Nontrivial ↥Jbar := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (Subgroup.center ↥Jbar))
  have hJns : ¬ Group.IsSolvable ↥Jbar := Group.IsPerfect.not_isSolvable (G := ↥Jbar)
  rcases ggQ2OrthNonFull_comp_cases hK hQ hdim ht3 hJ with hsp | ⟨hfix, hcond⟩
  · exact Or.inl (four_dvd_of_specialBlock hK hQ hAΩ Δ hτ hh hsp hJns)
  · rcases hcond with h6 | ⟨h4fix, hminus⟩
    · exact Or.inl (four_dvd_of_supportedFixedDerived_large hK hQ hdim h4 htype hE hsc
        htE ht3 hfix h6)
    · exact Or.inr ⟨hfix, h4fix, hminus⟩

theorem card_supportedFixedDerived_eq_sixty_of_minusFour
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (hdim : Module.finrank K (fixedSpace x) = 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace x).subtype)) :
    Nat.card ↥(supportedFixedDerived Q x) = 60 := by
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hts : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro U hU
    by_contra h
    push Not at h
    exact hminus ⟨U, by rw [hU, hdim], h⟩
  obtain ⟨-, -, hcard⟩ :=
    CFSG.SeitzReduction.OmegaPilot.isQuasisimple_orthDerived_of_four hR hdim hts
  rw [Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv, hcard, hK]
  norm_num

theorem card_quotient_center_eq_sixty_of_minusFour
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {ψ : ↥L →* ↥(orthDerived Q)} (hker : ψ.ker = Subgroup.center ↥L)
    (hJbar : Nat.card ↥((J.subgroupOf L).map ψ) = 60) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = 60 := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hJle : J ≤ L := (hDJ.1.2.2.2.2.2.1).1.trans inf_le_left
  have hJq_asm : CFSG.Assembly.IsQuasisimple ↥J := hDJ.1.2.2.2.2.2.1.2.2
  have hJq : CFSG.IsQuasisimple ↥J :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hJq_asm
  let κ : ↥J →* ↥(orthDerived Q) := ψ.comp (Subgroup.inclusion hJle)
  have hrange : κ.range = (J.subgroupOf L).map ψ := by
    rw [MonoidHom.range_eq_map]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr j.2)
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
  have hker_le : κ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    refine Subgroup.mem_center_iff.mpr fun j' => ?_
    have hjL : Subgroup.inclusion hJle j ∈ ψ.ker := hj
    have hZ : Subgroup.inclusion hJle j ∈ Subgroup.center ↥L := by rwa [hker] at hjL
    have hcommL := Subgroup.mem_center_iff.mp hZ (Subgroup.inclusion hJle j' : ↥L)
    exact Subtype.ext (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inclusion] using
        congrArg (fun z : ↥L => (z : G)) hcommL)
  have hker_index : κ.ker.index = 60 := by
    rw [Subgroup.index_ker, hrange, hJbar]
  have hcenter : (Subgroup.center ↥J).index = 60 :=
    le_antisymm (hker_index ▸ Subgroup.index_antitone hker_le)
      (CFSG.Quasithin.E6.Qs.sixty_le_index_center hJq)
  rw [← Subgroup.index_eq_card]
  exact hcenter

theorem index_centralizer_subgroupOf_le_three_of_minusFour
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) :
    ((Subgroup.centralizer (J : Set G)).subgroupOf B).index ≤ 3 := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hJq : CFSG.Open.IsQuasisimple ↥J := hcfg.2.2.1.2.2.2.2.2.1.2.2
  have hB : IsElemAbelian 3 B := hcfg.2.1.2.1.mono hcfg.2.1.1
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_stdSub hcfg.1.2.2.2.2.2.2.1 hcfg.1.2.2.2.2.2.2.2 hcfg.2.2.1
  have hcardle := CFSG.LocalAnalysis.GLTheoremA.T263.DX.card_le_three_mul_of_a5
    hJq h60 hB hBJ
  have hmul := Subgroup.index_mul_card
    (H := (Subgroup.centralizer (J : Set G)).subgroupOf B)
  have hcardsub : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf B) =
      Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hle : ((Subgroup.centralizer (J : Set G)).subgroupOf B).index *
      Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf B) ≤
      3 * Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf B) := by
    rw [hmul, hcardsub]
    exact hcardle
  exact Nat.le_of_mul_le_mul_right hle Nat.card_pos

theorem false_of_minusFour_component
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E)
    {ψ : ↥L →* ↥(orthDerived Q)} (hker : ψ.ker = Subgroup.center ↥L)
    {t : ↥(orthDerived Q)} (htE : t ∈ E)
    (hfix : ((J.subgroupOf L).map ψ) =
      (supportedFixedDerived Q (t : V ≃ₗ[K] V)).subgroupOf (orthDerived Q))
    (hdim4 : Module.finrank K (fixedSpace (t : V ≃ₗ[K] V)) = 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype)) :
    False := by
  have hx : OddOrderIsometry Q 3 (t : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived_pow_eq_one hQ Nat.prime_three (by norm_num) (hE.2 t htE)
  have hcardSFD : Nat.card ↥(supportedFixedDerived Q (t : V ≃ₗ[K] V)) = 60 :=
    card_supportedFixedDerived_eq_sixty_of_minusFour hK hx hdim4 hminus
  have hJbar : Nat.card ↥((J.subgroupOf L).map ψ) = 60 := by
    rw [hfix, natCard_subgroupOf_eq _ _ hx.supportedFixedDerived_le_orthDerived, hcardSFD]
  have h60 := card_quotient_center_eq_sixty_of_minusFour hS hker hJbar
  have hidx := index_centralizer_subgroupOf_le_three_of_minusFour hS h60
  exact ggQ2OrthNonFull_A5_case_impossible hS hidx

theorem ggQTwoGuardFailsOn_orthNonFull :
    GGQTwoGuardFailsOn GGQ2VACLabOrthNonFull := by
  intro G _ _ p B Bs x L D J hS hp hL
  subst hp
  obtain ⟨K, hfield, hfin, hK, V, hV, hM, hFd, Q, ℓ, E, ψ, hQ, hdim, h4, htype,
    hψ, hker, hE, hcard, hsc, haut, t, htE, ht3, hcomp⟩ :=
    ggQ2OrthNonFull_model hS hL
  let : Field K := hfield
  let : Finite K := hfin
  let : AddCommGroup V := hV
  let : Module K V := hM
  let : FiniteDimensional K V := hFd
  let : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  rcases four_dvd_ggAutomizer_or_minusFour_of_nonFull hK hQ hdim h4 htype hE hcard hsc htE ht3
    hcomp with hdvd | ⟨hfix, hdim4, hminus⟩
  · rw [haut] at hdvd
    exact hdvd
  · exact False.elim
      (false_of_minusFour_component hK hQ hS hE hker htE hfix hdim4 hminus)

end CFSG.StandardType

end
