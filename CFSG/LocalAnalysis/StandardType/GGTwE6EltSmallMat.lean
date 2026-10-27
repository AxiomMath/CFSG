module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallCount
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsToral
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernel
public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import Certificates.Certificate10050
public import Certificates.Certificate8117

public section

namespace CFSG.StandardType.TwE6EltSmall

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.LangRat

set_option linter.unusedSectionVars false


theorem false_of_isComponentOf_fixSubgroup {K : Type} [Field K] [Finite K] {n : ℕ}
    {σ : K ≃+* K} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    {B : Subgroup (twistedE6RootGroup K σ)} (hB : IsElemAbelian p B) (h5 : p ^ 5 ≤ Nat.card B)
    (hU : TwE6RootKill.TwNormTwo K σ (B.map (twistedE6RootGroup K σ).subtype))
    {a : twistedE6RootGroup K σ} (ha : a ∈ B) (ha1 : a ≠ 1)
    {Q : Subgroup (twistedE6RootGroup K σ)}
    (hQ : IsComponentOf Q (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a)))
    (hcomm : ∀ b ∈ B, (∀ d ∈ Q, b * d = d * b) → b ∈ Subgroup.zpowers a)
    (hsmall : Nat.card ↥(B ⊓ Q) < p ^ 3) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).1 h)
    omega
  haveI : NeZero ((p : ℕ) : AlgebraicClosure K) := ⟨hpL⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ p :=
    ⟨_, IsPrimitiveRoot.isUnit_unit hp.ne_zero hζ0⟩
  have hcard : Nat.card (B.map (twistedE6RootGroup K σ).subtype) = Nat.card B :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hAI : B.map (twistedE6RootGroup K σ).subtype ≤ twistedE6InndiagGL K σ :=
    (Subgroup.map_subtype_le B).trans le_sup_left
  have hA := hB.map (twistedE6RootGroup K σ).subtype
  obtain ⟨D, hc, hv⟩ := TwE6RootAs.exists_twLangData_of_dvd_add_one σ hK hσ hp hp5 hpq hAI hA
    (by rw [hcard]; exact (Nat.pow_le_pow_right hp.pos (by norm_num)).trans h5)
  obtain ⟨β, hβ, hi, -, hiii⟩ := TwE6RootKill.rootKernel_of_rootKill
      (TwE6RootKill.rootKill_of_ennolaKill_weylKill
          (TwE6RootKill.ennolaKill_of_steps TwE6RootKill.leviSplitStep_holds
              TwE6RootKill.ennolaSplitStep_holds) TwE6RootKill.weylKill_holds)
    hK hσ (ringChar.eq K 2) hp hpq hAI hA (by rw [hcard]; exact h5) hU D
  obtain ⟨S, hSD⟩ := exists_ennolaSetup hn hK hσ D hp hp5 hpq
  obtain ⟨ι, hιdef⟩ : ∃ ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K),
      ι = (MulAut.conj D.g0⁻¹).toMonoidHom.comp ((baseChangeGL
        (algebraMap K (AlgebraicClosure K))).comp (twistedE6RootGroup K σ).subtype) := ⟨_, rfl⟩
  have hιx : ∀ x : twistedE6RootGroup K σ, ι x = D.g0⁻¹ * baseChangeGL
      (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 :=
    fun x => by rw [hιdef, hc]; simp
  have hι : Function.Injective ι := by
    rw [hιdef]
    exact (MulAut.conj D.g0⁻¹).injective.comp
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))
  have hrange : ι.range = S.Γ := by rw [hιdef]; exact ennola_range_eq_Γ D S hSD hn hK hσ
  have hi' : ∀ c, (∃ y ∈ B, rootDiagUnit TwistTag.E6.tag c = ι y) ↔
      (∀ k, c k ^ p = 1) ∧ rootChar c β = 1 := fun c => by
    rw [← hi c]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, ⟨y, hy, rfl⟩, h.trans (hιx y)⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
      exact ⟨y, hy, h.trans (hιx y).symm⟩
  have hiii' : ∀ γ, iform γ β = 0 → ∀ ζ : (AlgebraicClosure K)ˣ, ζ ^ p = 1 →
      ∃ y ∈ B, rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) = ι y :=
    fun γ hγ ζ hζ => by
      obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := hiii γ hγ ζ hζ
      exact ⟨y, hy, h.trans (hιx y).symm⟩
  obtain ⟨t, ht, hta⟩ := D.hc (a : ModGL TwistTag.E6.tag K) ⟨a, ha, rfl⟩
  have hιa : ι a = t := by
    rw [hιx, ← hta, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨aT, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 ht).1
  have hT : rootDiagUnit TwistTag.E6.tag aT ∈ S.D.torus := by rw [hSD]; exact ht
  obtain ⟨hap, hβa⟩ := (hi' aT).1 ⟨a, ha, hιa.symm⟩
  have h1 : rootDiagUnit TwistTag.E6.tag aT ≠ 1 := fun h =>
    ha1 ((map_eq_one_iff ι hι).1 (hιa.trans h))
  have hβc : ∀ c, ι (MulAut.conj a c) =
      rootDiagUnit TwistTag.E6.tag aT * ι c * (rootDiagUnit TwistTag.E6.tag aT)⁻¹ := fun c => by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hιa]
  obtain ⟨i, -, hQi⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S
    hp ι hι hrange (MulAut.conj a) hβc hT hap h1
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S hp hpL
      (fun h => absurd h (by decide)) hT hap h1) hQ
  have hQR : ∀ {y}, ι y ∈ rationalComponent S.ρ S.Γ (rootCharHom aT) i → y ∈ Q := fun hy => by
    rw [← hQi] at hy
    obtain ⟨d, hd, hdy⟩ := hy
    exact hι hdy ▸ hd
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom aT) i
  have hβk : β ∈ kernelRoots (rootCharHom aT) := ⟨hβ, hβa⟩
  have hβΨ : β ∈ componentRoots (rootCharHom aT) i ∨
      ∀ α ∈ componentRoots (rootCharHom aT) i, iform α β = 0 := by
    by_cases hβi : (⟦⟨β, hβk⟩⟧ : KernelComponent (rootCharHom aT)) = i
    · exact Or.inl ⟨hβk, hβi⟩
    · refine Or.inr fun α ⟨hαk, hαi⟩ => iform_eq_zero_of_mk_ne (α := ⟨α, hαk⟩) (β := ⟨β, hβk⟩) ?_
      rw [hαi]
      exact Ne.symm hβi
  refine false_of_rank_count (by omega) hζ (f := ι) hβ hΨ hβΨ
    (Z := B ⊓ Subgroup.centralizer (Q : Set (twistedE6RootGroup K σ))) (Y := B ⊓ Q) ?_ ?_ ?_ hsmall
  · intro c hcp hcβ hcΨ
    obtain ⟨y, hy, hyc⟩ := (hi' c).2 ⟨hcp, hcβ⟩
    refine ⟨y, ⟨hy, Subgroup.mem_centralizer_iff.2 fun d hd => hι ?_⟩, hyc⟩
    have hle := rationalComponent_le_centralizer S i (b := c)
      (by rwa [rationalRoots_eq_of_rho_neg S (fun γ hγ => ennola_rho_eq_neg D hv S hSD hγ) i])
    have hdQ : ι d ∈ rationalComponent S.ρ S.Γ (rootCharHom aT) i := by
      rw [← hQi]
      exact Subgroup.mem_map_of_mem ι hd
    have hdc := Subgroup.mem_centralizer_iff.1 (hle hdQ) _ (Set.mem_singleton _)
    rw [hyc] at hdc
    rw [map_mul, map_mul]
    exact hdc.symm
  · intro γ hγ hγβ
    have hγr : IsRoot TwistTag.E6.tag γ := hΨ.isRoot γ hγ
    obtain ⟨y, hy, hyc⟩ := hiii' γ hγβ ζ hζ.pow_eq_one
    refine ⟨y, ⟨hy, hQR ?_⟩, hyc⟩
    obtain ⟨s, hs⟩ : ∃ s : (AlgebraicClosure K)ˣ, s = ζ ^ ((p + 1) / 2) := ⟨_, rfl⟩
    have hs2 : s ^ 2 = ζ := by
      rw [hs, ← pow_mul, show (p + 1) / 2 * 2 = p + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
    obtain ⟨y', -, hy'⟩ := hiii' γ hγβ s
      (by rw [hs, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    have hmem := rootSL2_HSL_sq_mem_rationalComponent S i hγ (t := s)
      (by rw [rootSL2_HSL_eq_rootDiagUnit_corootTuple hγr, hy', ← hrange]; exact ⟨y', rfl⟩)
      (ennola_rootSL2_WSL_mem_Γ D hv S hSD hn hK hσ hγr)
    rwa [hs2, rootSL2_HSL_eq_rootDiagUnit_corootTuple hγr, hyc] at hmem
  · calc Nat.card ↥(B ⊓ Subgroup.centralizer (Q : Set (twistedE6RootGroup K σ)))
        ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le fun z hz =>
          hcomm z hz.1 fun d hd => (Subgroup.mem_centralizer_iff.1 hz.2 d hd).symm
      _ = orderOf a := Nat.card_zpowers a
      _ ≤ p := orderOf_le_of_pow_eq_one hp.pos (hB.2 a ha)

end CFSG.StandardType.TwE6EltSmall

end
