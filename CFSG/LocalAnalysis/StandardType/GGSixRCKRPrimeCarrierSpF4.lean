module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpModel
public import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpF4Cover
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart2
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.F4KernelOne
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag StatedSp)

theorem rckFrameCover_sp_of_hom
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (h : ℕ) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Finite K]
    (hK : Nat.card K = 2 ^ (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hnK : 3 ≤ n ∨ 4 ≤ Nat.card K) (f : StatedSp n K →* ModGL τ GGL)
    (hrange : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hker : f.ker ≤ Subgroup.center (StatedSp n K))
    (hconj : ∀ b ∈ S.D.torus, ∃ C : StatedSp n K, ∀ X, b⁻¹ * f X * b = f (C * X * C⁻¹)) :
    RCKFrameCover S a i h (fun M g => M = ggU .PSp n g) := by
  set g := h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hg
  have hpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0, pow_zero] at hK
      exact absurd hK (Finite.one_lt_card (α := K)).ne'
    · exact h0
  have hng : 3 ≤ n ∨ 2 ≤ g := hnK.imp_right fun h4 => by
    by_contra hlt
    have : 2 ^ g ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E⟩ :=
    rckSp_nonempty_equiv n (CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 g hpos hK)
  refine ⟨ggU .PSp n g, f.comp E.symm.toMonoidHom, rfl, rckSp_standardReturnAt hn hpos hng, ?_,
    ?_, rckSp_finite n g, rckSp_isPerfect hpos hng, rckSp_oddCentralSplit n g,
    rckSp_exists_longRoot (by omega) g, ?_⟩
  · rw [← hrange]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨E.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨E x, by simp⟩
  · intro x hx
    have hx' : E.symm x ∈ Subgroup.center (StatedSp n K) := hker hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply E.symm.injective
    simpa using hx' (E.symm y)
  · intro b hb
    obtain ⟨C, hC⟩ := hconj b hb
    refine RootDetect.ggPsiInnerDiag_of_centralizes _ (a := E C) fun y => ?_
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    calc (b * f C)⁻¹ * f (E.symm y) * (b * f C) = (f C)⁻¹ * (b⁻¹ * f (E.symm y) * b) * f C := by
          group
      _ = f (C⁻¹ * (C * E.symm y * C⁻¹) * C) := by rw [hC]; simp only [map_mul, map_inv]
      _ = f (E.symm y) := by group

theorem rckCarrierSpF4_holds :
    RCKCarrierSpF4 := by
  intro p₀ S a hT p hp hp2 hTp i h hq hk hrank hcard _
  have hpL : ((p : ℕ) : GGL) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff GGL 2]
    exact fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  obtain ⟨v, J, hJ, hroots, -, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4_rank_ge_three_component_is_levi_odd hp.pos
      (Nat.odd_iff.1 (hp.odd_of_ne_two hp2)) hpL hTp
      (CFSG.HardMathSupport.Timmesfeld.Steinberg.rootDiagUnit_ne_one_of_ncard_ne_F4 i
        (by rw [hcard]; decide)) i hrank.ge
  obtain ⟨σQ, hfin, hcardF, f, hrange, hinj, hconj⟩ :=
    sp3_exists_cover_torusConj S hT i v hJ hroots hk hq
  refine rckFrameCover_sp_of_hom S a i h (n := 3) (by norm_num) (K := ↥(fixSubfield σQ)) ?_
    (Or.inl le_rfl) f hrange ?_ hconj
  · rw [hcardF, hq, ← pow_mul]
  · rw [(MonoidHom.ker_eq_bot_iff f).2 hinj]
    exact bot_le

end CFSG.StandardType.RCKRP

end
