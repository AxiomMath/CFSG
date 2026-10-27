module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.KGroups.L3EpsInvLin
import CFSG.GH74.KGroups.L3EpsUniInv
import CFSG.GH74.Generic.S3.L3Class
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.GH74.KGroups.L3EpsUniBlock

public section

namespace CFSG.RankThree.PartTwo.Sec20.L3OddInv

open CFSG.GH74.KGroups.L3Eps CFSG.GH74.Generic.S3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem exists_invData_sl2_L3 {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hq : p % 3 = 2)
    (e : K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p 1))
    {t : K} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ S : Subgroup K, CFSG.GH74.KGroups.L3Eps.InvData p K t S ∧
      Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) := by
  have hp : p.Prime := Fact.out
  have hFc : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have h2 : (2 : GaloisField p 1) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p 1) p]; exact hp2)
  have h4 : 4 ≤ Nat.card (GaloisField p 1) := by
    have := hp.two_le
    rw [hFc, pow_one]
    omega
  let e₁ : K ≃* projectiveSL 3 (GaloisField p 1) :=
    e.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField p 1))
  have hS : SingleInv K :=
    SingleInv.of_mulEquiv (e.trans (CFSG.PGLModel.projSLEquivStatedProj 3 _)).symm
      (singleInv_psl h2)
  have ht₀ : e₁.symm tInv * e₁.symm tInv = 1 := by rw [← map_mul, tInv_mul_self, map_one]
  have ht₀1 : e₁.symm tInv ≠ 1 := fun h => tInv_ne_one h2 (by simpa using congrArg e₁ h)
  obtain ⟨g, hg⟩ := hS t (e₁.symm tInv) ht ht1 ht₀ ht₀1
  obtain ⟨e', he'⟩ : ∃ e' : K ≃* projectiveSL 3 (GaloisField p 1), e' t = tInv :=
    ⟨(MulAut.conj g).trans e₁, by simp [MulAut.conj_apply, hg]⟩
  have hSeq : subgroupOfEquiv e' blockSub =
      blockSub.map (e'.symm : projectiveSL 3 (GaloisField p 1) →* K) := by
    ext x
    rw [mem_subgroupOfEquiv]
    constructor
    · intro hx
      exact ⟨e' x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  refine ⟨subgroupOfEquiv e' blockSub, ?_, ⟨?_⟩⟩
  · have h := invData_of_equiv hp hFc odd_one h2 h4 e' he'
    rwa [pow_one] at h
  · exact (MulEquiv.subgroupCongr hSeq).trans ((MulEquiv.subgroupMap e'.symm blockSub).symm.trans
      (MonoidHom.ofInjective (blockEmb_injective (F := GaloisField p 1))).symm)

open CFSG.GH74.KGroups.L3Eps.Uni in
theorem exists_invData_sl2_U3 {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hq : p % 3 = 1)
    (e : K ≃* CFSG.Assembly.RankThreeEven.projSU 3 p 1)
    {t : K} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ S : Subgroup K, CFSG.GH74.KGroups.L3Eps.InvData p K t S ∧
      Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) := by
  have hp : p.Prime := Fact.out
  have hU : UnitaryFieldData p 1 (GaloisField p (2 * 1)) :=
    ⟨hp, le_rfl, GaloisField.card p (2 * 1) (by norm_num)⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (p ^ 1) := by rw [pow_one]; exact hpodd
  have h5 : 5 ≤ p ^ 1 := by
    obtain ⟨k, hk⟩ := hpodd
    have := hp.two_le
    rw [pow_one]
    omega
  let e₀ := e.trans (CFSG.PGLModel.projSUEquivStatedProj 3 p 1)
  have hS : SingleInv K := SingleInv.of_mulEquiv e₀.symm (singleInv_psu hU hp2)
  obtain ⟨θ₀, hθ₀⟩ := exists_cover_of_equiv hU e₀
  obtain ⟨g, hg⟩ := hS (θ₀ (dU hodd)) t (theta_dU_sq hodd θ₀) (theta_dU_ne_one hU hodd hθ₀) ht ht1
  obtain ⟨θ, hθ, hθt⟩ : ∃ θ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU p 1
      (GaloisField p (2 * 1)) 3) →* K, IsCover hU θ ∧ θ (dU hodd) = t :=
    ⟨_, hθ₀.comp_equiv (MulAut.conj g), by simpa [MulAut.conj_apply] using hg⟩
  refine ⟨levS hodd θ, ?_, ?_⟩
  · have h := invData_of_cover hU hp2 h5 hodd hθ
    rw [hθt, pow_one] at h
    exact h
  ·
    obtain ⟨σ⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := GaloisField p (2 * 1)) (r := p) (f := 1) hU.card_eq_sq
    let ι : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU p 1 (GaloisField p (2 * 1)) 2) ≃*
        ↥(levS hodd θ) :=
      MonoidHom.ofInjective (hθ.injective_comp hU hodd.pos)
    have := Fintype.ofFinite
      (CFSG.LieType.Steinberg.fixedSubfield (GaloisField p (2 * 1)) p 1)
    have := Fintype.ofFinite (GaloisField p 1)
    have hc : Fintype.card (CFSG.LieType.Steinberg.fixedSubfield (GaloisField p (2 * 1)) p 1) =
        Fintype.card (GaloisField p 1) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
        CFSG.LieType.Steinberg.card_fixedSubfield hU.card_eq_sq, GaloisField.card p 1 one_ne_zero]
    let ρ := FiniteField.ringEquivOfCardEq hc
    let μ : SL(2, CFSG.LieType.Steinberg.fixedSubfield (GaloisField p (2 * 1)) p 1) ≃*
        SL(2, GaloisField p 1) :=
      MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map ρ.toRingHom)
        (Matrix.SpecialLinearGroup.map ρ.symm.toRingHom)
        (by ext A i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
        (by ext A i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    exact ⟨ι.symm.trans (σ.symm.trans μ)⟩

end CFSG.RankThree.PartTwo.Sec20.L3OddInv
