module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpF4Cover
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpB2Shape
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpB2Frame
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpF4

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.SeitzReduction.F4Pilot


theorem sp2_exists_cover_torusConj
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra (ZMod 2) L]
    [Algebra.IsAlgebraic (ZMod 2) L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {v : WeylGroup Tag.F4}
    (hv : componentRoots (rootCharHom a) i = (fun α => v • α) '' b2LeviRoots)
    {h : ℕ} (hq : S.D.q = 2 ^ h)
    (hQ : 4 ≤ 2 ^ (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) :
    ∃ σQ : L ≃+* L, Finite ↥(fixSubfield σQ) ∧
      Nat.card ↥(fixSubfield σQ) =
        S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      ∃ f : ↥(StatedSp 2 ↥(fixSubfield σQ)) →* ModGL Tag.F4 L,
        f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧ Function.Injective f ∧
        ∀ b ∈ S.D.torus, ∃ C : ↥(StatedSp 2 ↥(fixSubfield σQ)),
          ∀ X, b⁻¹ * f X * b = f (C * X * C⁻¹) := by
  obtain ⟨ψ, hψinj, hψrange, hψfrob, hψtorus⟩ := exists_sp2Frame (L := L) v
  rw [← hv] at hψrange
  exact sp_exists_cover_torusConj_of_frame S hT i (rckSpB2_twistInner S hT i hv) hψinj hψrange
    hψfrob hψtorus hq (Or.inr hQ)

theorem rckCarrierSpB2_holds : RCKCarrierSpB2 := by
  intro p₀ S a hT p hp hp2 hTp i h hq hrank hcard hQ _hQS
  obtain ⟨v, hv⟩ := rckSpB2_componentRoots_eq hp hp2 hTp i hrank hcard
  obtain ⟨σQ, hfin, hcardQ, f, hfrange, hfinj, hfconj⟩ :=
    sp2_exists_cover_torusConj S hT i hv hq hQ
  have hK : Nat.card ↥(fixSubfield σQ) =
      2 ^ (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    rw [hcardQ, hq, ← pow_mul]
  haveI := hfin
  exact rckFrameCover_sp_of_hom S a i h le_rfl hK (Or.inr (by rw [hK]; exact hQ)) f hfrange
    (by rw [(MonoidHom.ker_eq_bot_iff f).2 hfinj]; exact bot_le) hfconj

end CFSG.StandardType.RCKRP

end
