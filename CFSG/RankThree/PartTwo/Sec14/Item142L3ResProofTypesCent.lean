module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofRigid
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofListBar
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

theorem orderPoly_le (π : Bool) (q : ℕ) :
    q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1) ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  refine Nat.mul_le_mul_left _ ?_
  cases π
  · exact le_rfl
  · exact (Nat.sub_le _ _).trans (Nat.le_add_right _ _)

theorem le_orderPoly (π : Bool) (q : ℕ) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≤ q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1) := by
  refine Nat.mul_le_mul_left _ ?_
  cases π
  · exact (Nat.sub_le _ _).trans (Nat.le_add_right _ _)
  · exact le_rfl

theorem orderPoly_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 3 * (a ^ 2 - 1) * (a ^ 3 - 1) ≤ b ^ 3 * (b ^ 2 - 1) * (b ^ 3 - 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h 3)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 3) 1)

theorem orderPoly_step {a : ℕ} (ha : 2 ≤ a) :
    a ^ 3 * (a ^ 2 - 1) * (a ^ 3 + 1) < (a + 1) ^ 3 * ((a + 1) ^ 2 - 1) * ((a + 1) ^ 3 - 1) := by
  have h4 : 4 ≤ (a + 1) ^ 2 := by nlinarith
  have h1 : a ^ 3 * (a ^ 2 - 1) < (a + 1) ^ 3 * ((a + 1) ^ 2 - 1) :=
    Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_left (Nat.lt_succ_self a) (by norm_num))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left (Nat.le_succ a) 2) 1) (by omega)
  have e : (a + 1) ^ 3 = a ^ 3 + (3 * a ^ 2 + 3 * a) + 1 := by ring
  have h2 : a ^ 3 + 1 ≤ (a + 1) ^ 3 - 1 := by
    rw [e, Nat.add_sub_cancel]
    exact Nat.add_le_add_left (by nlinarith) _
  exact Nat.mul_lt_mul_of_lt_of_le h1 h2 (by rw [e, Nat.add_sub_cancel]; positivity)

theorem orderPoly_lt (π₁ π₂ : Bool) {q₁ q₂ : ℕ} (h1 : 2 ≤ q₁) (h : q₁ < q₂) :
    q₁ ^ 3 * (q₁ ^ 2 - 1) * cond π₁ (q₁ ^ 3 - 1) (q₁ ^ 3 + 1) <
      q₂ ^ 3 * (q₂ ^ 2 - 1) * cond π₂ (q₂ ^ 3 - 1) (q₂ ^ 3 + 1) :=
  (orderPoly_le π₁ q₁).trans_lt ((orderPoly_step h1).trans_le
    ((orderPoly_mono h).trans (le_orderPoly π₂ q₂)))

theorem eq_of_orderPoly_eq {π₁ π₂ : Bool} {q₁ q₂ : ℕ} (h1 : 2 ≤ q₁) (h2 : 2 ≤ q₂)
    (h : q₁ ^ 3 * (q₁ ^ 2 - 1) * cond π₁ (q₁ ^ 3 - 1) (q₁ ^ 3 + 1) =
      q₂ ^ 3 * (q₂ ^ 2 - 1) * cond π₂ (q₂ ^ 3 - 1) (q₂ ^ 3 + 1)) : q₁ = q₂ := by
  rcases lt_trichotomy q₁ q₂ with hlt | heq | hgt
  · exact absurd h (orderPoly_lt π₁ π₂ h1 hlt).ne
  · exact heq
  · exact absurd h.symm (orderPoly_lt π₂ π₁ h2 hgt).ne

variable {G : Type} [Group G] [Finite G]

theorem two_lt_of_model {L : Subgroup G}
    (hqs : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K)) : 2 < p ^ f := by
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hqs.1
  have : IsSimpleGroup ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := hqs.2.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (QuotientGroup.mk_surjective
      (s := Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L))).nontrivial
  by_contra h2
  have hp := hK.prime
  have hf := hK.one_le
  have h2' : p ^ f = 2 := by
    have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
    omega
  cases π
  · have := Sec13.isSolvable_projImage_slPi_two hK h2'
    have : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.IsPerfect.not_isSolvable _ this
  · change p ^ f % 3 = 1 at hq
    omega

theorem cent_of_prime_model {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hPGLA : Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A)) {x : G} (hxA : x ∈ A)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) {π : Bool} {p : ℕ} {K : Type} [Field K]
    (hK : PiField π p 1 K) (hq : ModThree π (p ^ 1))
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ 1) K))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ 1) K) (hy3 : Type123 π (p ^ 1) K y 3)
    (hact : ∀ z : ↥L ⧸ aschbacherSolvableCore 3 ↥L,
      ((e (sigmaOf L hxN z) : projImage (slPi π 3 (p ^ 1) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hπ : π = false → UnitaryFieldData p 1 K := fun h => by subst h; exact hK.unitary
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hq2 := two_lt_of_model hqs hK hq e
  obtain ⟨s, hs, hsZ, hs3, hysZ, -, hσ'⟩ := plane_model h hPGLA hxA hxN hK hq e hyH hy3 hact
  have hsH : s ∈ glPi π 3 (p ^ 1) K := slPi_le_glPi hπ hs
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hconj : ∀ (g : GL (Fin 3) K) (hg : g ∈ glPi π 3 (p ^ 1) K) (i j : ℤ),
      ProjGenLinGroup.mk g = ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j →
      ∃ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        MulAut.congr e (sigmaOf L haN) = Res8Hess.conjM' hπ hg := by
    intro g hg i j hgij
    obtain ⟨a, haA, haN, hz⟩ := hσ' i j
    refine ⟨a, haA, haN, ?_⟩
    ext m
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, Res8Hess.coe_conjM',
      hz, hgij, MulEquiv.apply_symm_apply]
  obtain ⟨a₁, ha₁A, ha₁N, h₁⟩ := hconj s hsH 1 0 (by simp)
  obtain ⟨a₂, ha₂A, ha₂N, h₂⟩ := hconj y hyH 0 1 (by simp)
  intro r hr l hl
  have hrA : r ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr
  have hrc : r ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A) hrA
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hrN : r ∈ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h h3L hrc
  set σ := sigmaOf L hrN with hσ
  have hcomm : ∀ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
      σ * sigmaOf L haN = sigmaOf L haN * σ := by
    intro a haA haN
    rw [hσ, sigmaOf, sigmaOf, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hrA a haA).symm)
  set n := orderOf r with hn
  have hn3 : ¬ 3 ∣ n := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Subgroup.orderOf_dvd_natCard _ hr))
  have hσn : σ ^ n = 1 := by
    have h1 : (⟨r, hrN⟩ : Subgroup.normalizer (L : Set G)) ^ n = 1 :=
      Subtype.ext (by simp [hn, pow_orderOf_eq_one])
    rw [hσ, sigmaOf, ← map_pow, ← map_pow, h1, map_one, map_one]
  set τ := MulAut.congr e σ with hτ
  have hτs : τ * Res8Hess.conjM' hπ hsH = Res8Hess.conjM' hπ hsH * τ := by
    rw [← h₁, hτ, ← map_mul, ← map_mul, hcomm a₁ ha₁A ha₁N]
  have hτy : τ * Res8Hess.conjM' hπ hyH = Res8Hess.conjM' hπ hyH * τ := by
    rw [← h₂, hτ, ← map_mul, ← map_mul, hcomm a₂ ha₂A ha₂N]
  have hτn : τ ^ n = 1 := by rw [hτ, ← map_pow, hσn, map_one]
  have hτ1 := rigid_prime hπ hK hq hq2 hyH hy3 hs hsH hsZ hs3 hysZ τ hτs hτy hn3 hτn
  have hσ1 : σ = 1 := (MulAut.congr e).injective (hτ1.trans (map_one _).symm)
  have h1 := congrArg (fun φ : MulAut (↥L ⧸ θ) => φ (QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩))
    hσ1
  change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨r, hrN⟩ ⟨l⁻¹, inv_mem hl⟩) =
    QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩ at h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  refine ⟨_, h1, ?_⟩
  simp [commutatorElement_def, mul_assoc]

theorem cent_of_isoPrime {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hPGLA : Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A)) (hx : ∃ x ∈ A, Sec4.InducesTypeOn L x 3)
    {p : ℕ} [Fact p.Prime] (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p 1) :
    ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  obtain ⟨x, hxA, hx⟩ := hx
  obtain ⟨hxN, π, p₁, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  obtain ⟨π₂, K₂, _, hK₂, hq₂, ⟨e₂⟩⟩ := Sec13.exists_projImage_model le_rfl hiso
  have := hK.finite
  have := hK₂.finite
  have hcard : Nat.card (projImage (slPi π 3 (p₁ ^ f) K)) =
      Nat.card (projImage (slPi π₂ 3 (p ^ 1) K₂)) :=
    Nat.card_congr (e.symm.trans e₂).toEquiv
  have h1 := Sec13.card_projImage_slPi_mul_three hK hq
  have h2 := Sec13.card_projImage_slPi_mul_three hK₂ hq₂
  rw [hcard, h2] at h1
  have hp₁ := hK.prime
  have hf := hK.one_le
  have hq1 : 2 ≤ p₁ ^ f := le_trans hp₁.two_le (Nat.le_self_pow (by omega) _)
  have hq2 : 2 ≤ p ^ 1 := by rw [pow_one]; exact (Fact.out : p.Prime).two_le
  have heq := eq_of_orderPoly_eq hq2 hq1 h1
  rw [pow_one] at heq
  obtain ⟨-, rfl⟩ := ((Fact.out : p.Prime).pow_eq_iff).mp heq.symm
  exact cent_of_prime_model h hPGLA hxA hxN hK hq e hyH hy3 hact

end CFSG.RankThree.PartTwo.Sec14.L3PGL
