module

public import CFSG.RankThree.PartOne.AUTSL.FourBridge
public import CFSG.RankThree.PartOne.AUTSL.FourIota
public import CFSG.RankThree.PartOne.KF1514B.Main
public import CFSG.RankThree.PartOne.S15K.OrthLifts
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.KF1514B
  CFSG.Assembly.RankThreeEven CFSG.RankThree.Classical2 CFSG.ComponentClassification Module
open CFSG.LieType.Universal.Spin (quadMinus)


theorem projOrth_conj_injective {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hTcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a)
  exact KCOrthogonalD4.conj_injective_of_trivial_center hTcenter

theorem fourModel_holds : FourModel := by
  intro G _ _ p A c L E h15 hF h13 hout
  have h := h15.h12
  obtain ⟨f, hf, hpf, ⟨b, c', hbc, ⟨φ₀⟩⟩, -, hEA, -⟩ := hout
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have : AnisoPair b c' := ⟨hbc⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hpf
  have hq : 3 < Nat.card (GaloisField 2 f) := by
    rw [hK]
    have := Nat.le_of_dvd (by positivity) hpf
    omega
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  let φ : ↥(lieGenerated p E) ≃* ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c') :=
    φ₀.trans (projOmegaMinusEquivOrth (GaloisField 2 f) b c')
  have hOut := outPNice_of_projOmegaMinus
    (X := ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c')) hp (by omega) hf hbc
    (projOmegaMinusEquivOrth (GaloisField 2 f) b c').symm
  have hpI : p ∣ Nat.card (lieGenerated p E) :=
    dvd_card_of_projOmegaMinus hf hbc φ₀ (Or.inr hpf)
  have hQ := polar_nondegenerate_quadMinus hbc
  have hT := exists_three_totSing_quadMinus (GaloisField 2 f) b c'
  obtain ⟨a, hap, hac, hacomm, hao, hmul⟩ := orth_lifts h h13 hEA hQ hT hOut hpI φ
  have hTinj := projOrth_conj_injective hQ hT
  have hEN : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
    E_le_normalizer_lieGenerated hp
  have hirr := hbc
  let Ψ : ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c') ≃* ↥(G0 b c') :=
    (projOmegaMinusEquivOrth (GaloisField 2 f) b c').symm.trans (modelEquiv hirr)
  let ψ : ↥(lieGenerated p E) →* (Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)) :=
    (G0 b c').subtype.comp (Ψ.toMonoidHom.comp φ.toMonoidHom)
  let aH : ↥E →* ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c') := MonoidHom.mk' a hmul
  let abar : ↥E →* (Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)) :=
    (G0 b c').subtype.comp (Ψ.toMonoidHom.comp aH)
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp (Ψ.injective.comp φ.injective)
  have hψO : ∀ x, ψ x ∈ G0 b c' := fun x => (Ψ (φ x)).2
  have hainj : Function.Injective abar := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have h1 : aH e = 1 := by
      have h0 : Ψ (aH e) = 1 := Subtype.ext he
      exact Ψ.injective (h0.trans (map_one Ψ).symm)
    have h2 : a e = 1 := h1
    have h3 := hao e hne
    rw [h2, orderOf_one] at h3
    exact hp.one_lt.ne h3
  have hcompatT : ∀ (e : ↥E) (x : ↥(lieGenerated p E))
      (hx : (e : G) * x * (e : G)⁻¹ ∈ lieGenerated p E),
      φ ⟨(e : G) * x * (e : G)⁻¹, hx⟩ = a e * φ x * (a e)⁻¹ := by
    intro e x hx
    have h1 := congrArg (fun m : MulAut _ => m (φ x)) (hac e)
    simp only [MulAut.conj_apply] at h1
    rw [h1, actP_apply]
    rfl
  have hactP : ∀ (y : G) (hy : y ∈ lieGenerated p E),
      actP φ ⟨y, Subgroup.le_normalizer hy⟩ = MulAut.conj (φ ⟨y, hy⟩) := by
    intro y hy
    refine MulEquiv.ext fun t => ?_
    obtain ⟨x, rfl⟩ := φ.surjective t
    rw [actP_apply]
    have : ((lieGenerated p E).normalizerMonoidHom ⟨y, Subgroup.le_normalizer hy⟩) x =
        ⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, MulAut.conj_apply]
  have hψ : ∀ x, ψ x = ((Ψ (φ x) : ↥(G0 b c')) :
      Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)) := fun x => rfl
  have habar : ∀ e, abar e = ((Ψ (a e) : ↥(G0 b c')) :
      Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)) := fun e => rfl
  have hcompat : ∀ (e : ↥E) (x : ↥(lieGenerated p E))
      (hx : (e : G) * x * (e : G)⁻¹ ∈ lieGenerated p E),
      ψ ⟨(e : G) * x * (e : G)⁻¹, hx⟩ = abar e * ψ x * (abar e)⁻¹ := by
    intro e x hx
    simp only [hψ, habar, hcompatT e x hx, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hEI : ∀ (e : ↥E) (he : (e : G) ∈ lieGenerated p E), abar e = ψ ⟨e, he⟩ := by
    intro e he
    have h1 : a e = φ ⟨e, he⟩ := by
      apply hTinj
      rw [hac e]
      exact hactP e he
    rw [habar, hψ, h1]
  have hnorm : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)) (hyI : y ∈ lieGenerated p E)
      (e : ↥E), abar (conjAut E y hy e) = ψ ⟨y, hyI⟩ * abar e * (ψ ⟨y, hyI⟩)⁻¹ := by
    intro y hy hyI e
    have h1 : a (conjAut E y hy e) = φ ⟨y, hyI⟩ * a e * (φ ⟨y, hyI⟩)⁻¹ := by
      apply hTinj
      have h2 : actP φ ⟨((conjAut E y hy e : ↥E) : G), hEN (conjAut E y hy e).2⟩ =
          actP φ ⟨y, Subgroup.le_normalizer hyI⟩ * actP φ ⟨(e : G), hEN e.2⟩ *
            (actP φ ⟨y, Subgroup.le_normalizer hyI⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
      rw [hac, h2, hactP y hyI, ← hac e]
      simp only [map_mul, map_inv]
    simp only [habar, hψ, h1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hĒ : abar.range ≤ G0 b c' := by
    rintro _ ⟨e, rfl⟩
    exact (Ψ (aH e)).2
  have hexp : ∀ x ∈ abar.range, x ^ p = 1 := by
    rintro _ ⟨e, rfl⟩
    have hEpow : e ^ p = 1 :=
      Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h e.2)
    rw [← map_pow, hEpow, map_one]
  have hcardE : Nat.card abar.range = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hainj).toEquiv.symm).trans hEcard
  have hcardG : Nat.card ↥(G0 b c') = (Nat.card (GaloisField 2 f)) ^ 12 *
      ((Nat.card (GaloisField 2 f)) ^ 4 + 1) * (((Nat.card (GaloisField 2 f)) ^ 2 - 1) *
        ((Nat.card (GaloisField 2 f)) ^ 4 - 1) * ((Nat.card (GaloisField 2 f)) ^ 6 - 1)) := by
    rw [hK]
    exact card_G0 hf hbc
  obtain ⟨lam, hL⟩ := lineStr_G0 hp h5 hpq hcardG hĒ hexp hcardE
  exact fourFacts_of_lineStr hL hEN ψ hψinj hψO abar hainj rfl hcompat hEI hnorm

open CFSG.Assembly (InCatalog)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf158FourShort_holds (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hKF156 : KF156') : S15K.KF158FourShort :=
  kf158FourShort_of_model hS h82 hKF156 fourModel_holds

end CFSG.RankThree.PartOne.AUTSL.Four
