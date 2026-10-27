module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec15.NoModNine

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1519CentAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → (∀ X ∈ scriptY2 A, ¬ L ≤ X) →
      IsSimpleGroup ↥L →
      ∀ m p : ℕ, Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m →
        (1 ≤ m → ¬ 3 ∣ m) → IsChoice1519 m p → 3 < p →
        ∀ Y₀ ∈ scriptY0 A (lB A), p ∣ Nat.card (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) →
          ∀ R ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y₀ : Set G)) (piOf p),
            (R : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
              (CFSG.Open.pCoreOf 2 Y₀)

namespace Proof1517

@[expose] noncomputable def quotAut {X : Type*} [Group X] (N : Subgroup X) [N.Characteristic] :
    MulAut X →* MulAut (X ⧸ N) where
  toFun σ := QuotientGroup.congr N N σ (Subgroup.characteristic_iff_map_eq.mp ‹_› σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable {G : Type} [Group G]

theorem subset_sectionCentralizer_of_not_dvd {p : ℕ} [Fact p.Prime] {Y₀ R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (Y₀ : Set G)) (hRp : IsPGroup p R)
    (hcop : ¬ p ∣ Nat.card (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) :
    (R : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀) := by
  intro r hr
  refine ⟨hRN hr, fun y hy => ?_⟩
  set N := CFSG.pCore 2 ↥Y₀ with hN
  set ρ : ↥R →* MulAut (↥Y₀ ⧸ N) :=
    (quotAut N).comp (Y₀.normalizerMonoidHom.comp (Subgroup.inclusion hRN)) with hρ
  have h1 : ρ ⟨r, hr⟩ = 1 := by
    obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
    have ho1 : orderOf (ρ ⟨r, hr⟩) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
    have ho2 : orderOf (ρ ⟨r, hr⟩) ∣ Nat.card (MulAut (↥Y₀ ⧸ N)) := orderOf_dvd_natCard _
    have hcop' : Nat.Coprime (p ^ k) (Nat.card (MulAut (↥Y₀ ⧸ N))) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hcop)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' ho1 ho2)
  have h2 := congrArg (fun φ : MulAut (↥Y₀ ⧸ N) => φ ((⟨y, hy⟩ : ↥Y₀) : ↥Y₀ ⧸ N)) h1
  simp only [MulAut.one_apply] at h2
  set z : ↥Y₀ := Y₀.normalizerMonoidHom ⟨r, hRN hr⟩ ⟨y, hy⟩ with hz
  have hzv : (z : G) = r * y * r⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have h3 : ((z : ↥Y₀) : ↥Y₀ ⧸ N) = ((⟨y, hy⟩ : ↥Y₀) : ↥Y₀ ⧸ N) := h2
  have h4 : z⁻¹ * ⟨y, hy⟩ ∈ N := QuotientGroup.eq.mp h3
  have h5 : z * (⟨y, hy⟩ : ↥Y₀)⁻¹ ∈ N := by
    have hnorm : N.Normal := inferInstance
    have := hnorm.conj_mem _ (N.inv_mem h4) ⟨y, hy⟩
    simpa [mul_assoc] using this
  have h6 : ((z * (⟨y, hy⟩ : ↥Y₀)⁻¹ : ↥Y₀) : G) ∈ CFSG.Open.pCoreOf 2 Y₀ := by
    refine ⟨z * (⟨y, hy⟩ : ↥Y₀)⁻¹, ?_, rfl⟩
    exact h5
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv] at h6
  exact h6

end Proof1517

open Proof1517

theorem step1519Cent_of (h1517 : Step1517R) (h138 : Item138N) (hcent : Step1519CentAut) :
    Step1519Cent := by
  intro G _ _ A c L h Y hctx m p hiso hp hp3 Y₀ hY₀ R hR
  have hpp : p.Prime := hp.1
  have : Fact p.Prime := ⟨hpp⟩
  by_cases hdvd : p ∣ Nat.card (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))
  · obtain ⟨hno, hsimp, -⟩ := h1517 G A c L h Y hctx
    have h3m : 1 ≤ m → ¬ 3 ∣ m := fun hm1 =>
      (not_three_dvd_of_concl1515 h h138 KFacts.kSL3PiOrder3TypeC hctx.concl1515 hm1 hiso).1
    exact hcent G A c L h Y hctx hno hsimp m p hiso h3m hp hp3 Y₀ hY₀ hdvd R hR
  · exact subset_sectionCentralizer_of_not_dvd hR.1.2 ((isPiSubgroup_piOf_iff hpp R).mp hR.2)
      hdvd

end CFSG.RankThree.PartTwo.Sec15
