module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSevenSL3
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
public import CFSG.Quasithin.EmptyFaithful.S153E59C
public import CFSG.Quasithin.H13.KG14726COrd
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Chevalley
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Linear
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Symplectic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.H13.KG14726Corr
public import CFSG.Quasithin.H13.KG14726Elim

public section

namespace CFSG.StandardType.LieKnownR2.PSL

open Matrix

theorem one_le_of_not_isSolvable_psl {k g : ℕ} {X : Type} [Group X]
    (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g) →* X)
    (hns : ¬ Group.IsSolvable ↥φ.range) : 1 ≤ k := by
  by_contra h
  have hk : k = 0 := by omega
  subst hk
  haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin (0 + 1)) (GaloisField 2 g)) :=
    CFSG.StandardType.subsingleton_specialLinear_of_card_le_one (Q := GaloisField 2 g) (by simp)
  haveI : Subsingleton ↥φ.range := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    exact Subtype.ext (by rw [← hx, ← hy, Subsingleton.elim x y])
  exact hns inferInstance

theorem sq_dvd_card_mulAut_of_normalizing {X : Type} [Group X] [Finite X] {J B₁ D : Subgroup X}
    {p : ℕ} (hp : p.Prime) (hB₁p : IsPGroup p B₁)
    (hB₁ : B₁ ≤ Subgroup.normalizer (J : Set X))
    (hBD : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hcard : p ^ 4 ≤ Nat.card B₁)
    (hD : Nat.card D = p ^ 2) : p ^ 2 ∣ Nat.card (MulAut ↥J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let ψ : B₁ →* MulAut J := (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom J).comp
    (Subgroup.inclusion hB₁)
  have hmap : ψ.ker.map B₁.subtype = B₁ ⊓ Subgroup.centralizer (J : Set X) := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
      have hx1 : ψ x = 1 := MonoidHom.mem_ker.1 hx
      have hxker : Subgroup.inclusion hB₁ x ∈
          (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom J).ker := by
        rw [MonoidHom.mem_ker]
        exact hx1
      rw [CFSG.LocalAnalysis.ComponentInitial.ker_normalizerConjHom J] at hxker
      exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_subgroupOf.1 hxker⟩
    · intro hg
      obtain ⟨hgB, hgC⟩ := Subgroup.mem_inf.1 hg
      refine Subgroup.mem_map.2 ⟨⟨g, hgB⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      have h : Subgroup.inclusion hB₁ ⟨g, hgB⟩ ∈
          (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom J).ker := by
        rw [CFSG.LocalAnalysis.ComponentInitial.ker_normalizerConjHom J]
        exact Subgroup.mem_subgroupOf.2 hgC
      exact MonoidHom.mem_ker.1 h
  have hkerCard : Nat.card ψ.ker = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective B₁.subtype_injective, hmap, hBD, hD]
  have hsplit : Nat.card B₁ = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  obtain ⟨m, hm⟩ := hB₁p.exists_card_eq
  have hdvdR : Nat.card ψ.range ∣ p ^ m := by
    rw [← hm, hsplit]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvdR
  have hcpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hcard' : p ^ 2 * p ^ 2 ≤ Nat.card B₁ := by
    rw [show p ^ 2 * p ^ 2 = p ^ 4 by ring]
    exact hcard
  have hRge : p ^ 2 ≤ Nat.card ψ.range := by
    refine Nat.le_of_mul_le_mul_right ?_ hcpos
    rw [← hsplit, hkerCard]
    exact hcard'
  have hj2 : 2 ≤ j := by
    rw [hj] at hRge
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hRge
  have hp2r : p ^ 2 ∣ Nat.card ψ.range := by
    rw [hj]
    exact pow_dvd_pow p hj2
  exact hp2r.trans (Subgroup.card_subgroup_dvd_card ψ.range)

private theorem lr2d1_not_sq_336 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 336) :
    False := by
  have hle : p ≤ 18 := by
    have : p ^ 2 ≤ 336 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;>
    first | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

theorem three_le_of_not_isSolvable_psl_two {k : ℕ} {X : Type} [Group X] [Finite X]
    (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1) →* X)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)))
    (hns : ¬ Group.IsSolvable ↥φ.range) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D : Subgroup X} (hB₁p : IsPGroup p B₁)
    (hB₁ : B₁ ≤ Subgroup.normalizer (φ.range : Set X))
    (hBD : B₁ ⊓ Subgroup.centralizer (φ.range : Set X) = D)
    (hcard : p ^ 4 ≤ Nat.card B₁) (hD : Nat.card D = p ^ 2) : 3 ≤ k := by
  by_contra h
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact absurd (one_le_of_not_isSolvable_psl φ hns) (by omega)
  · haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 1)) :=
      CFSG.StandardType.isSolvable_specialLinear_of_card_eq_two (ι := Fin (1 + 1))
        (Q := GaloisField 2 1) (by simp) (by simpa using GaloisField.card 2 1 one_ne_zero)
    exact hns (Group.isSolvable_of_surjective φ.rangeRestrict_surjective)
  · have hcenter : Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 1)) = ⊥ :=
      CFSG.StandardType.sl3CenterEqBotOfCardTwo (GaloisField 2 1)
        (by simpa using GaloisField.card 2 1 one_ne_zero)
    have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hkerbot
    let e : Matrix.SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 1) ≃* φ.range :=
      MonoidHom.ofInjective hinj
    have hcardAut : Nat.card (MulAut ↥φ.range) = 336 := by
      let efield : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
        (CFSG.ClassicalModels.specialLinearFieldEquiv
          (CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod 2) 2 1 one_pos (by simp))
          (Fin 3)).symm
      let eStated : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1) ≃*
          CFSG.Open.StatedSL 3 (ZMod 2) :=
        efield.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2))
      calc
        Nat.card (MulAut ↥φ.range)
            = Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin (2 + 1))
                (GaloisField 2 1))) :=
              Nat.card_congr (MulAut.congr e).toEquiv.symm
        _ = Nat.card (MulAut (CFSG.Open.StatedSL 3 (ZMod 2))) :=
              Nat.card_congr (MulAut.congr eStated).toEquiv
        _ = 336 := CFSG.Quasithin.S153E59.card_mulAut_statedSL_three_two
    have hp2dvd : p ^ 2 ∣ Nat.card (MulAut ↥φ.range) :=
      sq_dvd_card_mulAut_of_normalizing (J := φ.range) (B₁ := B₁) (D := D)
        hp hB₁p hB₁ hBD hcard hD
    rw [hcardAut] at hp2dvd
    exact lr2d1_not_sq_336 hp hp2 hp2dvd

private theorem lr2d2_small_not_sq_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ 120) : False := by
  have hle : p ≤ 11 := by
    have : p ^ 2 ≤ 120 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;>
    first | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

theorem two_le_of_not_isSolvable_psl_four {k : ℕ} {X : Type} [Group X] [Finite X]
    (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 2) →* X)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 2)))
    (hns : ¬ Group.IsSolvable ↥φ.range) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D : Subgroup X} (hB₁p : IsPGroup p B₁)
    (hB₁ : B₁ ≤ Subgroup.normalizer (φ.range : Set X))
    (hBD : B₁ ⊓ Subgroup.centralizer (φ.range : Set X) = D)
    (hcard : p ^ 4 ≤ Nat.card B₁) (hD : Nat.card D = p ^ 2) : 2 ≤ k := by
  by_contra hk
  push Not at hk
  have hk1 : 1 ≤ k := one_le_of_not_isSolvable_psl φ hns
  have hk_eq : k = 1 := le_antisymm (by omega) hk1
  subst hk_eq
  simp only [Nat.reduceAdd] at hker
  have hp2dvd : p ^ 2 ∣ Nat.card (MulAut ↥φ.range) :=
    sq_dvd_card_mulAut_of_normalizing hp hB₁p hB₁ hBD hcard hD
  have h120 : Nat.card (MulAut ↥φ.range) ∣ 120 := by
    have hF : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hcenter :
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = ⊥ := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2
          (GaloisField 2 2),
        CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot (GaloisField 2 2)]
    have hkerbot : φ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' := hker hx
      rwa [hcenter] at hx'
    have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
    have hSLq : CFSG.IsQuasisimple
        (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
      CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le (K := GaloisField 2 2)
        (by rw [hF])
    have hqs : CFSG.IsQuasisimple ↥φ.range :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hφinj) hSLq
    exact CFSG.Quasithin.H13.KG14726.card_mulAut_dvd_of_mulEquiv_sl2_four hqs hF
      (MonoidHom.ofInjective hφinj).symm
  exact lr2d2_small_not_sq_120 hp hp2 (hp2dvd.trans h120)

theorem jDim_psl {f k : ℕ} (hf : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f) →* X)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)))
    (hns : ¬ Group.IsSolvable ↥φ.range) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D : Subgroup X} (hB₁p : IsPGroup p B₁)
    (hB₁ : B₁ ≤ Subgroup.normalizer (φ.range : Set X))
    (hBD : B₁ ⊓ Subgroup.centralizer (φ.range : Set X) = D)
    (hcard : p ^ 4 ≤ Nat.card B₁) (hD : Nat.card D = p ^ 2) :
    (f = 1 ∧ 3 ≤ k) ∨ (f = 2 ∧ 2 ≤ k) ∨ (3 ≤ f ∧ 1 ≤ k) := by
  by_cases h1 : f = 1
  · subst h1
    exact Or.inl ⟨rfl, three_le_of_not_isSolvable_psl_two φ hker hns hp hp2 hB₁p hB₁ hBD hcard hD⟩
  · by_cases h2 : f = 2
    · subst h2
      exact Or.inr (Or.inl ⟨rfl,
        two_le_of_not_isSolvable_psl_four φ hker hns hp hp2 hB₁p hB₁ hBD hcard hD⟩)
    · exact Or.inr (Or.inr ⟨by omega, one_le_of_not_isSolvable_psl φ hns⟩)

end CFSG.StandardType.LieKnownR2.PSL
