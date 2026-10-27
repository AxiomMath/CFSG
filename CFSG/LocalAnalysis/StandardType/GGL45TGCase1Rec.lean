module

public import CFSG.LocalAnalysis.StandardType.GGL45TGCase1Core
public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecLin
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecUni

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

private noncomputable def c15StatedProjEquiv (d : ℕ) (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* StatedProj (StatedSL d K) :=
  (TypeA.recipeEquiv d K).trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL d K).symm.trans
      (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d K))

private theorem c15LieModel (d : ℕ) (K : Type) [Field K] [Finite K]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hadm : StatedLieAdmissible .PSL d 2 f) :
    CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) .PSL d 2 f :=
  Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨c15StatedProjEquiv d K⟩⟩⟩

private theorem c15CardHopfMultiplierCongr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) =
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) :=
  ((Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv).symm.trans
    ((Nat.card_congr
        (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv).trans
      (Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess Y).toEquiv)))

private theorem c15CenterEqBotOfMulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [h, Subgroup.mem_bot] at hz'
  exact e.injective (by rw [hz', map_one])

private theorem c15CenterPrimeOfHopf {R L' : Type} [Group R] [Group L']
    (hZR : Subgroup.center R = ⊥) {p : ℕ}
    (hM : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier R))
    (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    ¬ p ∣ Nat.card (Subgroup.center L') := by
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hcen : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    have h1 : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZR, Subgroup.mem_bot] at h1
    exact h1
  have heq : Subgroup.center L' = ψ.ker := le_antisymm hcen hker
  have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective ψ hψ hker
  have hdvd : Nat.card ψ.ker ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier R) :=
    ⟨Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplierToKer ψ hψ hker).ker,
      CFSG.RankThree.PerfectCover.card_eq_card_mul_card_ker _ hsurj⟩
  rw [heq]
  exact fun hp => hM (hp.trans hdvd)

theorem ggCenterPrime_three_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) := by
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) = ⊥ :=
    c15CenterEqBotOfMulEquiv (TypeA.recipeEquiv 3 K)
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := K) (by norm_num))
  have hLie3 : CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) .PSL 3 2 1 :=
    c15LieModel 3 K (by simpa using hK)
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hLie2 : CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) .PSL 2 7 1 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hLie3
  obtain ⟨-, K', _, _, hK'card, ⟨eK'⟩⟩ :=
    (CFSG.Blueprint.LieModel.statedClassicalModel hLie2 (by decide) :
      StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) .PSL 2 7 1)
  haveI : Fintype K' := Fintype.ofFinite K'
  have hcard7 : Fintype.card K' = 7 := by
    rw [Fintype.card_eq_nat_card, hK'card]; norm_num
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
      (k := K') (by rw [hcard7]; norm_num) (by rw [hcard7]; norm_num)
  have hgcd : Nat.gcd 2 (Fintype.card K' - 1) = 2 := by rw [hcard7]; norm_num
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K')) = 2 := by
    rw [Nat.card_congr eM.toEquiv, hgcd]
    change Nat.card (ZMod 2) = 2
    rw [Nat.card_zmod]
  have eR2 : LargeEvenProj (LargeEvenSLGroup (Fin 3) K) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K' :=
    eK'.trans (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K').symm
  have hcongr := c15CardHopfMultiplierCongr eR2
  have hcardH : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K')) = 2 :=
    ((Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K')).toEquiv).symm.trans hcardM)
  have hcardR : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) = 2 := hcongr.trans hcardH
  have hM : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) := by
    intro hpdiv
    rw [hcardR] at hpdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv)
  intro L' _ _ ψ hψ hker hperf
  exact c15CenterPrimeOfHopf hZR hM ψ hψ hker hperf

private theorem c15IsPEltCongr {p : ℕ} {G H : Type*} [Monoid G] [Monoid H] (e : G ≃* H) {u : G}
    (h : GGL45IsPElt p u) : GGL45IsPElt p (e u) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

private theorem c15InnerOfIsPElt {n : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ} (hn : 3 ≤ n)
    (hpg : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)))
    {a : MulAut (projectiveSL n K)} (haD : a ∈ linearAutGroup n K) (hap : GGL45IsPElt p a) :
    a ∈ CFSG.RankThree.PartOne.innSL n K := by
  obtain ⟨k, hk⟩ := hap
  obtain ⟨g, rfl⟩ := mem_linearAutGroup_iff.mp haD
  have hcop : Nat.Coprime (p ^ k) (Nat.gcd n (Nat.card K - 1)) := hpg.pow_left k
  have h1 : conjAut n K (g ^ p ^ k) = 1 := by rw [map_pow, hk]
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn (g ^ p ^ k) |>.mp h1
  have hdet : (Matrix.GeneralLinearGroup.det g) ^ (p ^ k) = c ^ n := by
    rw [← map_pow, ← hc, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units]
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartOne.KCLinPlane.exists_pow_eq_of_pow_eq
    (m := Nat.card K - 1) (fun x : Kˣ => by rw [← Nat.card_units]; exact pow_card_eq_one') hcop hdet
  have hdet' : Matrix.GeneralLinearGroup.det
      (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) = 1 := by
    rw [map_mul, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units, ← hu, inv_pow,
      inv_mul_cancel]
  have hrange : GeneralLinearGroup.scalar (Fin n) u⁻¹ * g ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet'
  have h2 : conjAut n K g = conjAut n K (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) := by
    rw [map_mul, conjAut_scalar, one_mul]
  rw [h2]
  show conjAut n K (GeneralLinearGroup.scalar (Fin n) u⁻¹ * g) ∈
    (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
  rw [← CFSG.RankThree.PartOne.KCLinComm.map_toGL_range_eq_conj_range]
  exact ⟨_, hrange, rfl⟩

private theorem c15CenterCoprimePsl {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpq : Nat.Coprime p (Nat.card K - 1)) (hsec : TypeA.SLHasSections d K) :
    GGCenterCoprime p (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf hdvd
  have := Fact.mk hp
  obtain ⟨φ, hφs, hφ⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ψ.ker) p hdvd
  obtain ⟨s, hs⟩ := hφs (z : L')
  have hs1 : proj d K s = 1 := by
    rw [← hφ, hs]
    exact z.2
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hs1)
  have hcq : c ^ (Nat.card K - 1) = 1 := by rw [← Nat.card_units]; exact pow_card_eq_one'
  have hsq : s ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow, ← Units.val_pow_eq_pow_val, hcq,
      Units.val_one, map_one]
    rfl
  have hzq : z ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hs, ← map_pow, hsq, map_one]
    rfl
  have h1 := orderOf_dvd_of_pow_eq_one hzq
  rw [hz] at h1
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hpq h1)

private theorem c15CenterPrimeOfCenterCoprime {p : ℕ} {R : Type} [Group R]
    (h : GGCenterCoprime p R) (hZ : Subgroup.center R = ⊥) : GGCenterPrime p R := by
  intro L' _ _ ψ hψ hker hperf hdvd
  have hZle : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  exact h L' ψ hψ hker hperf (hdvd.trans (Subgroup.card_dvd_of_le hZle))

private theorem c15CoprimeCardSubOne {n p : ℕ} {K : Type} [Finite K] (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) (hpq : ¬ (p : ℤ) ∣ 2 ^ n - 1) : Nat.Coprime p (Nat.card K - 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpq ?_
  rw [hK] at h
  have h1 : ((2 ^ n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [← h1]
  exact Int.natCast_dvd_natCast.mpr h

theorem ggL45NtRec_linear_case1
    {d n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d)
    (hpq : ¬ (p : ℤ) ∣ 2 ^ n - 1) :
    GGL45NtRec p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  have hcop := c15CoprimeCardSubOne hK hp hpq
  have hcopg : Nat.Coprime p (Nat.gcd d (Nat.card K - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) hcop
  have hcen : GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hn1 : 1 ≤ n := by
      by_contra h0
      have h1 := Finite.one_lt_card (α := K)
      rw [hK, show n = 0 by omega, pow_zero] at h1
      exact lt_irrefl _ h1
    have hgen : (d = 3 ∧ n = 1) ∨ 5 ≤ d ∨ (d = 3 ∧ 3 ≤ n) := by
      rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h3 | h4 | h5
      · subst h3
        have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd
        rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
        · exact Or.inl ⟨rfl, h1⟩
        · exfalso
          subst h2 hp3'
          exact hpq (by norm_num)
        · exact Or.inr (Or.inr ⟨rfl, h3⟩)
      · exfalso
        subst h4
        have h2 : p ∣ 2 ^ 2 := by simpa using hpd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl h5)
    rcases hgen with ⟨rfl, rfl⟩ | h5 | ⟨rfl, hn3⟩
    · exact ggCenterPrime_three_two (by rw [hK, pow_one]) hp hp2
    · exact ggCenterPrime_of_mulEquiv (TypeA.recipeEquiv d K)
        (c15CenterPrimeOfCenterCoprime (c15CenterCoprimePsl hp hcop
          (TypeA.slHasSections_of_five_le h5))
          (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := d) (k := K) hd))
    · have hle : 2 ^ 3 ≤ Nat.card K := by
        rw [hK]; exact Nat.pow_le_pow_right (by norm_num) hn3
      have hsec : TypeA.SLHasSections 3 K := by
        refine TypeA.slHasSections_of_card (by norm_num) ?_ ?_ ?_
        · intro hc; rw [hc] at hle; norm_num at hle
        · rintro ⟨-, hc⟩; rw [hc] at hle; norm_num at hle
        · rintro ⟨h, -⟩; norm_num at h
      exact ggCenterPrime_of_mulEquiv (TypeA.recipeEquiv 3 K)
        (c15CenterPrimeOfCenterCoprime (c15CenterCoprimePsl hp hcop hsec)
          (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := K)
            (by norm_num)))
  intro _ _
  refine ⟨?_, ?_, hcen⟩
  · intro r
    exact (RecipeFieldLinear.coe_recI (d := d) (K := K)) ▸ RecipeFieldLinear.conj_mem_recI r
  · intro u hu hup
    have hlin : MulAut.congr (TypeA.recipeEquiv d K) u ∈ linearAutGroup d K := by
      rw [← RecipeFieldLinear.mem_recI_iff (d := d) (K := K)]
      exact show u ∈ (RecipeFieldLinear.recI d K : Set _) from
        (RecipeFieldLinear.coe_recI (d := d) (K := K)).symm ▸ hu
    have hinner := c15InnerOfIsPElt hd hcopg hlin
      (c15IsPEltCongr (MulAut.congr (TypeA.recipeEquiv d K)) hup)
    obtain ⟨r', hr'⟩ := hinner
    refine ⟨(TypeA.recipeEquiv d K).symm r', (MulAut.congr (TypeA.recipeEquiv d K)).injective ?_⟩
    rw [mulAut_congr_conj, MulEquiv.apply_symm_apply]
    exact hr'.symm

section Unitary

variable {n d : ℕ} {K : Type} [Field K]

private theorem c15BarMap (h : UnitaryFieldData 2 n K) (M : Matrix (Fin d) (Fin d) K) :
    M.map (· ^ 2 ^ n) = M.map h.bar := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]

private theorem c15SuSubsetGu (h : UnitaryFieldData 2 n K) :
    (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) ⊆
      LargeEvenGUSet (Fin d) K (2 ^ n) := by
  intro A hA
  obtain ⟨h1, -⟩ := (SU.mem_su_iff h).mp hA
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul, c15BarMap h]
  exact h1

private theorem c15PowQAddOneMem [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hN : LargeEvenGUSet (Fin d) K (2 ^ n) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)))
    {A : GL (Fin d) K} (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) ⟨A, hN hA⟩ ^ (2 ^ n + 1) ∈
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  classical
  have h := TableBU.unitaryFieldData_of_card hK hn
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hAmem : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := ⟨μ, hμ0, hμq, hAμ⟩
  have hAμσ : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) =
      μ • 1 := by
    rw [← c15BarMap h]
    exact hAμ
  set x : Kˣ := Matrix.GeneralLinearGroup.det A with hx
  have hxval : (x : K) = (A : Matrix (Fin d) (Fin d) K).det :=
    Matrix.GeneralLinearGroup.val_det_apply A
  have hxq : (x : K) ^ (2 ^ n) * (x : K) = μ ^ d := by
    have hdet := congrArg Matrix.det hAμσ
    rw [Matrix.det_mul, Matrix.det_transpose] at hdet
    rw [show (A : Matrix (Fin d) (Fin d) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin d) (Fin d) K) from rfl] at hdet
    rw [← RingHom.map_det] at hdet
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, UnitaryFieldData.bar_apply,
      ← hxval] at hdet
    exact hdet
  set m : Kˣ := Units.mk0 μ hμ0 with hm
  set B : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) m⁻¹ * A ^ (2 ^ n + 1) with hB
  have hcoeb : (B : Matrix (Fin d) (Fin d) K) =
      μ⁻¹ • ((A : Matrix (Fin d) (Fin d) K) ^ (2 ^ n + 1)) := by
    rw [hB, TableB.coe_scalar_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hm,
      Units.val_mk0]
  have hBdet : (B : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [hcoeb, Matrix.det_smul, Matrix.det_pow, Fintype.card_fin, ← hxval, pow_succ, hxq,
      ← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
  have hAinv : (A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcomm : Commute ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ
      (A : Matrix (Fin d) (Fin d) K) := by
    show ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) K) * ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ
    have hM : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
        μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      calc ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
            ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
              ((A : Matrix (Fin d) (Fin d) K) *
                ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
              rw [hAinv, Matrix.mul_one]
        _ = (((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K)) *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [Matrix.mul_assoc]
        _ = (μ • 1) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hAμσ]
        _ = μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              rw [Matrix.smul_mul, Matrix.one_mul]
    have hAM : (A : Matrix (Fin d) (Fin d) K) * ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
        μ • 1 := by
      calc (A : Matrix (Fin d) (Fin d) K) * ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ =
            (A : Matrix (Fin d) (Fin d) K) *
              (μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by rw [hM]
        _ = μ • ((A : Matrix (Fin d) (Fin d) K) *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by rw [Matrix.mul_smul]
        _ = μ • 1 := by rw [hAinv]
    rw [hAμσ]
    exact hAM.symm
  have hμq1 : μ ^ (2 ^ n - 1) = 1 := by
    have h2 : μ ^ (2 ^ n - 1) * μ = 1 * μ := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul, hμq]
    exact mul_right_cancel₀ hμ0 h2
  have hBuniσ :
      ((B : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (B : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hcoeb, TableB.transpose_map_smul, Matrix.map_pow, Matrix.transpose_pow, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    have hpow : (((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ) ^ (2 ^ n + 1) *
        (A : Matrix (Fin d) (Fin d) K) ^ (2 ^ n + 1) = μ ^ (2 ^ n + 1) • 1 := by
      rw [← hcomm.mul_pow, hAμσ, Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow]
      have hfun : ((fun _ : Fin d => μ) ^ (2 ^ n + 1)) = fun _ : Fin d => μ ^ (2 ^ n + 1) := by
        funext i
        simp
      rw [hfun, ← Matrix.smul_one_eq_diagonal]
    rw [hpow, smul_smul]
    have hsc : h.bar μ⁻¹ * μ⁻¹ * μ ^ (2 ^ n + 1) = 1 := by
      rw [UnitaryFieldData.bar_apply, inv_pow, hμq, pow_succ, ← mul_assoc,
        show μ⁻¹ * μ⁻¹ * μ ^ 2 ^ n * μ = μ ^ (2 ^ n - 1) * (μ⁻¹ * μ) * (μ⁻¹ * μ) by
          rw [show μ ^ 2 ^ n = μ ^ (2 ^ n - 1) * μ by
            rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]]
          ring,
        inv_mul_cancel₀ hμ0, hμq1, mul_one, mul_one]
    rw [hsc, one_smul]
  have hBmem : B ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) :=
    (SU.mem_su_iff h).mpr ⟨hBuniσ, hBdet⟩
  have hAeq : (⟨A, hN hAmem⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) ^ (2 ^ n + 1) =
      ⟨Matrix.GeneralLinearGroup.scalar (Fin d) m,
        TableB.scalar_mem_normalizer _ ⟨m, rfl⟩⟩ *
        ⟨B, Subgroup.le_normalizer hBmem⟩ := by
    apply Subtype.ext
    show (A : GL (Fin d) K) ^ (2 ^ n + 1) = Matrix.GeneralLinearGroup.scalar (Fin d) m * B
    rw [hB, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hinner : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      (⟨A, hN hAmem⟩ ^ (2 ^ n + 1)) ∈
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
    rw [hAeq, map_mul, TableB.projConj_of_scalar _ ⟨m, rfl⟩, one_mul,
      TableB.projConj_of_mem _ B hBmem]
    exact ⟨((⟨B, hBmem⟩ : LargeEvenSUGroup (Fin d) K (2 ^ n)) :
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))), rfl⟩
  rw [← map_pow]
  exact hinner

private theorem c15EqOneOfMemScalars (h : UnitaryFieldData 2 n K) (hd : 1 ≤ d) {p : ℕ}
    (hp : p.Prime) (hpq : Nat.Coprime p (2 ^ n + 1)) {z : LargeEvenSUGroup (Fin d) K (2 ^ n)}
    (hz : z ∈ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))).ker) (hzp : z ^ p = 1) :
    z = 1 := by
  rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hz
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
  let i : Fin d := ⟨0, hd⟩
  have hu := ((SU.mem_su_iff h).mp z.2).1
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at hu
  have hu' := congrFun (congrFun hu i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.one_apply_eq] at hu'
  have hcq : c ^ (2 ^ n + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at hu'
    simpa [UnitaryFieldData.bar_apply] using hu'
  have hcp : c ^ p = 1 := by
    have h1 : ((z ^ p : LargeEvenSUGroup (Fin d) K (2 ^ n)) : GL (Fin d) K) = 1 := by
      rw [hzp]; rfl
    rw [Subgroup.coe_pow, ← hc, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K) i i) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h2)
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hcp, hcq⟩
    rwa [Nat.Coprime.gcd_eq_one hpq, pow_one] at this
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

private theorem c15CenterPrimeUnitary
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : Nat.Coprime p (2 ^ n + 1)) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  have := Fact.mk hp
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* LargeEvenSUGroup (Fin d) K (2 ^ n)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSUGroup (Fin d) K (2 ^ n) →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen hC
    by_cases he : Even d
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
        (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn hd he hdq hπ hcen
  have : Finite (LargeEvenSUGroup (Fin d) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin d) K (2 ^ n) =>
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnp := StdSubRestU.noTorsion_ker_of_section
    (q := LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (QuotientGroup.mk'_surjective _) hsplit hp hp2
    (fun z hz hzp => c15EqOneOfMemScalars h (by omega) hp hpq hz hzp) hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [TableBUE.center_proj_eq_bot hK hd hdq, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : z = 1 := Subtype.ext (hnp _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

end Unitary

theorem ggL45NtRec_unitary_case1
    {d n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ (p : ℤ) ∣ 2 ^ n + 1) :
    GGL45NtRec p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  have hcop : Nat.Coprime p (2 ^ n + 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpq ?_
    exact_mod_cast Int.natCast_dvd_natCast.mpr h
  intro _ _
  have h := TableBU.unitaryFieldData_of_card hK hn
  set H := LargeEvenSUGroup (Fin d) K (2 ^ n) with hH
  have hN : LargeEvenGUSet (Fin d) K (2 ^ n) ⊆ Subgroup.normalizer (H : Set (GL (Fin d) K)) :=
    TableBUE.gu_subset_normalizer h
  have hSUgu : (H : Set (GL (Fin d) K)) ⊆ LargeEvenGUSet (Fin d) K (2 ^ n) := c15SuSubsetGu h
  refine ⟨?_, ?_, c15CenterPrimeUnitary hK hn hd hdq hp hp2 hcop⟩
  · intro r
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin d) K).subgroupOf H) r
    refine ⟨a, hSUgu a.2, ?_⟩
    intro x y hxy
    rw [MulAut.conj_apply]
    have h1 : (LargeEvenProjMk H a) * (LargeEvenProjMk H x) * (LargeEvenProjMk H a)⁻¹ =
        LargeEvenProjMk H (a * x * a⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    congr 1
    exact Subtype.ext hxy.symm
  · intro u hu hup
    obtain ⟨k, hk⟩ := hup
    obtain ⟨A, hA, rfl⟩ := TableB.exists_eq_projConj hN hu
    have hqmem : TableB.projConj H ⟨A, hN hA⟩ ^ (2 ^ n + 1) ∈
        (MulAut.conj : LargeEvenProj H →* MulAut (LargeEvenProj H)).range :=
      c15PowQAddOneMem hK hn hN hA
    have hmem : TableB.projConj H ⟨A, hN hA⟩ ∈
        (MulAut.conj : LargeEvenProj H →* MulAut (LargeEvenProj H)).range := by
      set N := (MulAut.conj : LargeEvenProj H →* MulAut (LargeEvenProj H)).range
      have h1 : (QuotientGroup.mk' N (TableB.projConj H ⟨A, hN hA⟩)) ^ (2 ^ n + 1) = 1 := by
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff (N := N) _).mpr hqmem
      have h2 : (QuotientGroup.mk' N (TableB.projConj H ⟨A, hN hA⟩)) ^ (p ^ k) = 1 := by
        rw [← map_pow, hk, map_one]
      have hgcd : Nat.gcd (2 ^ n + 1) (p ^ k) = 1 := (Nat.Coprime.pow_left k hcop).symm
      have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rw [hgcd, pow_one] at h3
      exact (QuotientGroup.eq_one_iff _).mp h3
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, hr.symm⟩

theorem ggL45NtRecOn_famTypeACase1 :
    GGL45NtRecOn GGL45FamTypeACase1 := by
  intro p hp hp2 lab hlab _ hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hd : 3 ≤ rank + 1 := ggL45FamTypeA_three_le hp hp2 hS.1
  obtain ⟨⟨htag, hpd⟩, hq⟩ := hS
  dsimp only at hpd
  rcases htag with ht | ht <;> dsimp only at ht <;> subst ht
  · dsimp only [GGL45Eps] at hq
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    haveI : Finite K := hfin
    exact ⟨K, hf, hfin, hK, hQ', ggL45NtRec_linear_case1 hK hd hp hp2 hpd hq⟩
  · dsimp only [GGL45Eps] at hq
    have hq' : ¬ (p : ℤ) ∣ 2 ^ n + 1 := by simpa using hq
    have hdq : (rank + 1, 2 ^ n) ≠ (3, 2) := by
      intro he
      have h1 : rank = 2 := by
        have := congrArg Prod.fst he
        simpa using this
      have h2 : 2 ^ n = 2 := congrArg Prod.snd he
      have hn2 : 2 ≤ n := hlab.2.2 h1
      have hle : 2 ^ (2 : ℕ) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      rw [h2] at hle
      norm_num at hle
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    haveI : Finite K := hfin
    exact ⟨K, hf, hfin, hK, hQ', ggL45NtRec_unitary_case1 hK hlab.1 hd hdq hp hp2 hq'⟩

end CFSG.StandardType.GGL45TG
