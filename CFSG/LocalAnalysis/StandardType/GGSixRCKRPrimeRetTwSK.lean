module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIota
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.Timmesfeld
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckRet_SK_tw
    {h : ℕ} (hh : 0 < h) {w' : WeylGroup Tag.E6} {zh : ModGL Tag.E6 GGL}
    (hzh : zh ∈ adjointGroup Tag.E6 GGL)
    (hlang : twistHom TwistTag.E6 GGL (ggFrobT h) zh⁻¹ =
      zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w') :
    ∃ SK : LangSetup Tag.E6 GGL 5, SK.D.q = 2 ^ h ∧ SK.D.g0 = zh⁻¹ ∧
      SK.D.n = canonicalRep (coxeterSystem Tag.E6) GGL w' ∧
      SK.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h) ∧
      (∀ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ' →
        SK.ρ γ' = w' • permLattice (τ := Tag.E6) TwistTag.E6.perm γ') ∧
      SK.Γ = (show Subgroup (ModGL Tag.E6 GGL) from (rckTw6_iota h).range).map
        (MulAut.conj zh).toMonoidHom := by
  classical
  have hPinnedEq : ∀ (γ' : Fin TwistTag.E6.tag.rank → ℤ) (c : GGL),
      pinnedX TwistTag.E6.tag GGL γ' c = pinnedX Tag.E6 GGL γ' c := by
    intro γ' c
    rfl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP GGL 2 := inferInstance
  let K := GaloisField 2 (2 * h)
  letI : Algebra K GGL := (ggRatEmb (2 * h)).toAlgebra
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  have hK : Nat.card K = (2 ^ h) ^ 2 := by
    dsimp only [K]
    rw [GaloisField.card 2 (2 * h) (by omega), ← pow_mul, mul_comm]
  let σE : K ≃+* K := iterateFrobeniusEquiv K 2 h
  have hσ : ∀ c : K, σE c = c ^ 2 ^ h := fun c =>
    iterateFrobeniusEquiv_def (R := K) (p := 2) (n := h) c
  let D : LangDatum Tag.E6 GGL :=
    { Φ := twistHom TwistTag.E6 GGL (ggFrobT h)
      q := 2 ^ h
      n := canonicalRep (coxeterSystem Tag.E6) GGL w'
      g0 := zh⁻¹
      steinberg := ⟨ggFrobT h, fun c => ggFrobT_apply h c, diagramMap TwistTag.E6 GGL,
        Or.inr ⟨TwistTag.E6, rfl, rfl⟩, fun g => rfl⟩
      n_weyl := ⟨w', rfl⟩
      g0_mem := inv_mem hzh
      lang := hlang }
  have hΦ : D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h) := rfl
  have hfin : Finite D.model :=
    finite_model_twistedE6 Nat.prime_two hh hK hσ (ggFrobT_apply h) D hΦ
  have hqpow : IsPrimePow D.q ∧ (((D.q : ℕ) : GGL) = 0) := by
    refine ⟨?_, ?_⟩
    · dsimp only [D]
      exact Nat.prime_two.isPrimePow.pow hh.ne'
    · dsimp only [D]
      rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hh.ne']
  have hpq : ¬ 5 ∣ D.q := by
    dsimp only [D]
    intro hd
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hd
    norm_num at h52
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 GGL D
  let S : LangSetup Tag.E6 GGL 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hfin
  have hSD : S.D = D := rfl
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSD]
  · rw [hSD]
  · rw [hSD]
  · rw [hSD]
  · intro γ' hγ'
    have hγπ : IsRoot Tag.E6 (permLattice (τ := Tag.E6) TwistTag.E6.perm γ') :=
      hγ'.permLattice TwistTag.E6.cartan_perm
    have h1 := rckRet_step_pinnedX S hγ' 1
    have h2 : S.D.step (pinnedX Tag.E6 GGL γ' 1) =
        pinnedX Tag.E6 GGL (w' • permLattice (τ := Tag.E6) TwistTag.E6.perm γ') 1 := by
      have hs : S.D.step (pinnedX Tag.E6 GGL γ' 1) =
          S.D.n * S.D.Φ (pinnedX Tag.E6 GGL γ' 1) * S.D.n⁻¹ := by
        simp [LangDatum.step, MulAut.conj_apply]
      rw [hs, hSD]
      have hPinnedEqL : pinnedX TwistTag.E6.tag GGL γ' 1 = pinnedX Tag.E6 GGL γ' 1 := rfl
      have htw : (twistHom TwistTag.E6 GGL (ggFrobT h) (pinnedX Tag.E6 GGL γ' 1) : ModGL Tag.E6 GGL) =
          (pinnedX Tag.E6 GGL (permLattice (τ := Tag.E6) TwistTag.E6.perm γ') 1 : ModGL Tag.E6 GGL) := by
        have h := E6GraphRadical.twistHom_pinnedX_of_two
          (CharTwo.two_eq_zero : (2 : GGL) = 0) (ggFrobT h) hγ' (1 : GGL)
        rw [hPinnedEqL, hPinnedEq] at h
        rw [map_one] at h
        exact h
      have hΦpin : D.Φ (pinnedX Tag.E6 GGL γ' 1) =
          pinnedX Tag.E6 GGL (permLattice (τ := Tag.E6) TwistTag.E6.perm γ') 1 := by
        rw [hΦ]
        convert htw using 2 <;> exact Iff.rfl
      rw [hΦpin]
      rw [canonicalRep_conj_pinnedX_two w' hγπ]
    have h3 : pinnedX Tag.E6 GGL (w' • permLattice (τ := Tag.E6) TwistTag.E6.perm γ') 1 ∈
        rootSubgroup Tag.E6 GGL (S.ρ γ') := by
      rw [← h2, h1, one_pow]
      exact mem_rootSubgroup.2 ⟨1, rfl⟩
    have h4 : IsRoot Tag.E6 (w' • permLattice (τ := Tag.E6) TwistTag.E6.perm γ') := by
      rw [isRoot_smul_iff]
      exact hγπ
    have h5 : IsRoot Tag.E6 (S.ρ γ') := (S.frob.isRoot_iff γ').2 hγ'
    exact (eq_of_pinnedX_one_mem_rootSubgroup h4 h5 h3).symm
  · have hΓ := rckTw6_Gamma S h hΦ (rckTw6_langPkg S h hh hΦ)
    exact hΓ

end CFSG.StandardType.RCKRP

end
