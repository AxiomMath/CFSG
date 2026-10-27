module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FField
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3F
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.UnitaryCover
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GroupTheory.SteinbergBK

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r4f_exists_field {Y : Type} [Group Y] {m f : ℕ} (hm : 4 ≤ m)
    (hX : LieModel Y .PSU m 2 f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : ¬ r ∣ 2 ^ f + 1)
    {θ : MulAut Y} (hθr : θ ^ r = 1) (hθ : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K)
      (e : Y ≃* primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) (σ : K ≃+* K)
      (M₀ : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)),
      r ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = (2 ^ (f / r)) ^ 2 ∧
      (∀ x : K, σ x = x → h.bar x = x ^ 2 ^ (f / r)) ∧
      (primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) M₀)⁻¹ *
          MulAut.congr e θ * primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) M₀ =
        primeFormFieldHom h CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
          σ := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨K, _, h, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel'
      (LieModel.admissible hX) hX
  have hm3 : 3 ≤ m := by omega
  have hq : ¬(m = 3 ∧ 2 ^ f = 2) := by omega
  have ha : MulAut.congr e θ ^ r = 1 := by rw [← map_pow, hθr, map_one]
  have ha1 : MulAut.congr e θ ≠ 1 := fun h1 => hθ (MonoidHom.mem_range.2 ⟨1, by
    rw [map_one]
    exact ((MulAut.congr e).injective (h1.trans (map_one _).symm)).symm⟩)
  obtain ⟨σ, hσ⟩ : ∃ σ, primeFormFieldFactor h
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one hm3 hq
        (MulAut.congr e θ) = σ := ⟨_, rfl⟩
  have hσr : σ ^ r = 1 := by rw [← hσ, ← map_pow, ha, map_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have hD : MulAut.congr e θ ∈ primeFormD h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
      rw [← ker_primeFormFieldFactor h
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one hm3 hq]
      exact MonoidHom.mem_ker.2 hσ
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1
      (CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.mem_inner_of_pow_eq_one_primeFormD h hm3
        hq hr hrq hD ha)
    refine hθ (MonoidHom.mem_range.2 ⟨e.symm z, (MulAut.congr e).injective ?_⟩)
    rw [← hz]
    ext w
    simp
  obtain ⟨hrf, hcard, hbar, -, -, M₀, hM₀⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hm3 hq hr hr2
      (MulAut.congr e θ) (orderOf_eq_prime ha ha1) σ hσ (orderOf_eq_prime hσr hσ1)
  exact ⟨K, inferInstance, h, e, σ, M₀, hrf, hcard, hbar, hM₀⟩

theorem uc22s2114r4f_exists_fixed_noncyclic {Y : Type} [Group Y] {m f : ℕ}
    (hm : 4 ≤ m) (hX : LieModel Y .PSU m 2 f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : ¬ r ∣ 2 ^ f + 1) {θ : MulAut Y} (hθr : θ ^ r = 1)
    (hθ : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ f + 1 ∧
      ∃ X : Subgroup Y, IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧ ∀ x ∈ X, θ x = x := by
  obtain ⟨K, _, h, e, σ, M₀, hrf, hcard, hbar, hM₀⟩ :=
    uc22s2114r4f_exists_field hm hX hr hr2 hrq hθr hθ
  have := h.finite
  have hfr : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by have := h.one_le; omega) hrf) hr.pos
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ (f / r) + 1 ≠ 1 by have := Nat.one_le_two_pow (n := f / r); omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ (f / r) := dvd_pow_self 2 (by omega)
    omega
  have hpf : p ∣ 2 ^ f + 1 := by
    have h' := (hr.odd_of_ne_two hr2).nat_add_dvd_pow_add_pow (2 ^ (f / r)) 1
    rw [one_pow, ← pow_mul, Nat.div_mul_cancel hrf] at h'
    exact hpd.trans h'
  obtain ⟨ζ, hζ, hσζ⟩ := uc22s2114r3f_exists_fixed_unit hcard hp hpd
  have hσμ : ∀ s ∈ zpowers ζ, σ (s : K) = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hσζ]
  have hpμ : ∀ s ∈ zpowers ζ, (s : K) ^ p = 1 := by
    intro s hs
    rw [← Units.val_pow_eq_pow_val, ← hζ,
      orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_of_mem_zpowers hs), Units.val_one]
  have hμ : ∀ s ∈ zpowers ζ, h.norm (s : K) = 1 := by
    intro s hs
    obtain ⟨t, ht⟩ := hpd
    rw [UnitaryFieldData.norm, hbar _ (hσμ s hs), ← pow_succ', ht, pow_mul, hpμ s hs, one_pow]
  obtain ⟨ι, hι, hθι⟩ := uc22s2114r3f_exists_diag h (by omega) e θ σ M₀ hM₀ (zpowers ζ) hμ
    (MonoidHom.id _) fun s => (hσμ s s.2).symm
  obtain ⟨hPp, hPc⟩ := uc22s2114r3f_isPGroup_pi (μ := zpowers ζ) hp
    (by rw [Nat.card_zpowers, hζ])
  refine ⟨p, hp, hp2, hpf, ι.range, hPp.of_equiv (MonoidHom.ofInjective hι),
    fun hc => hPc ((MonoidHom.ofInjective hι).isCyclic.2 hc), ?_⟩
  rintro _ ⟨s, rfl⟩
  exact hθι s

theorem uc22s2114r4f_exists_fpf {Y : Type} [Group Y] {m f : ℕ} (hm : 4 ≤ m)
    (hX : LieModel Y .PSU m 2 f) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : ¬ r ∣ 2 ^ f + 1) {θ : MulAut Y} (hθr : θ ^ r = 1)
    (hθ : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ∣ 2 ^ f + 1 ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a) := by
  obtain ⟨K, _, h, e, σ, M₀, hrf, hcard, -, hM₀⟩ :=
    uc22s2114r4f_exists_field hm hX hr (by omega) hrq hθr hθ
  have := h.finite
  have hf1 := h.one_le
  have hf5 : 5 ≤ f := hr5.trans (Nat.le_of_dvd (by omega) hrf)
  have hfr : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos
  have hfr' : f / r < f := Nat.div_lt_self (by omega) hr.one_lt
  obtain ⟨q, hq, hqd, hqprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * f) (by omega) (by omega)
  have hfac : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [show 2 * f = f * 2 by ring, pow_mul, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
  have hqf : q ∣ 2 ^ f + 1 :=
    (hq.dvd_mul.1 (hfac ▸ hqd)).resolve_right (hqprim f (by omega) (by omega))
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hqprim 2 (by norm_num) (by omega) (by norm_num)
  have hq5 : q ≠ 5 := by
    rintro rfl
    exact hqprim 4 (by norm_num) (by omega) (by norm_num)
  have hq4 : q ≠ 4 := by
    rintro rfl
    exact absurd hq (by decide)
  have hq6 : q ≠ 6 := by
    rintro rfl
    exact absurd hq (by decide)
  have hq7 : 7 ≤ q := by
    have := hq.two_le
    omega
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) q
    (by rw [Nat.card_units, h.card]; exact hqd)
  have hζp : IsPrimitiveRoot ζ q := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  have hμq : Nat.card (rootsOfUnity q K) = q := hζp.card_rootsOfUnity'
  have hμ : ∀ s ∈ rootsOfUnity q K, h.norm (s : K) = 1 := by
    intro s hs
    obtain ⟨t, ht⟩ := hqf
    have hs' : (s : K) ^ q = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity q s).1 hs, Units.val_one]
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ', ht, pow_mul, hs',
      one_pow]
  obtain ⟨ι, hι, hθι⟩ := uc22s2114r3f_exists_diag h (by omega) e θ σ M₀ hM₀ (rootsOfUnity q K)
    hμ (restrictRootsOfUnity σ q) fun s => restrictRootsOfUnity_coe_apply σ s
  obtain ⟨hAp, hAc⟩ := uc22s2114r3f_isPGroup_pi (μ := rootsOfUnity q K) hq hμq
  have : Finite (rootsOfUnity q K) := Nat.finite_of_card_ne_zero (by rw [hμq]; exact hq.ne_zero)
  have hqq0 : ¬ q ∣ (2 ^ (f / r)) ^ 2 - 1 := by
    rw [← pow_mul, mul_comm]
    exact hqprim (2 * (f / r)) (by omega) (by omega)
  refine ⟨q, hq, hq7, hqf, Fin 2 → rootsOfUnity q K, inferInstance, inferInstance, hAp, hAc,
    (restrictRootsOfUnity σ q).compLeft (Fin 2), fun s hs => ?_, ι, hι, hθι⟩
  funext i
  have hsi : restrictRootsOfUnity σ q (s i) = s i := congrFun hs i
  refine Subtype.ext
    (uc22s2114r3f_eq_one_of_fixed hcard hq hqq0 ((mem_rootsOfUnity q _).1 (s i).2) ?_)
  rw [← restrictRootsOfUnity_coe_apply σ (s i), hsi]


theorem uc22s2114r4f_fieldSubgroups_of_psu {Y : Type} [Group Y] {m f r : ℕ} (hm : 4 ≤ m)
    (hX : LieModel Y .PSU m 2 f) (hr : r.Prime) (hr5 : 5 ≤ r) (hrq : ¬ r ∣ 2 ^ f + 1)
    {θ : MulAut Y} (hθr : θ ^ r = 1)
    (hθ : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ f + 1 ∧
      ∃ X : Subgroup Y, IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧ q ∣ 2 ^ f + 1 ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  have hqr : ∀ {q : ℕ}, q.Prime → q ∣ 2 ^ f + 1 → q ≠ r := fun hq hqf hqr => by
    subst hqr
    exact hrq hqf
  exact ⟨uc22s2114r4f_exists_fixed_noncyclic hm hX hr (by omega) hrq hθr hθ,
    (by
      obtain ⟨q, hq, hq7, hqf, A, hAcomm, hAfin, hAq, hAcyc, κ, hκ, ι, hι, hθι⟩ :=
        uc22s2114r4f_exists_fpf hm hX hr hr5 hrq hθr hθ
      exact ⟨q, hq, hq7, hqr hq hqf, hqf, A, hAcomm, hAfin, hAq, hAcyc, κ, hκ, ι, hι, hθι⟩)⟩

theorem uc22s2114r4f_fieldSubgroups_of_psu_odd
    {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G}
    {m f : ℕ} (hm : 4 ≤ m) (hX : LieModel (BarInf L) .PSU m 2 f)
    {b : G} (hbL : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hrn : r ∣ 2 ^ c.n - 1) (hodd : Odd c.n)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ f + 1 ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧ q ∣ 2 ^ f + 1 ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have hr2 : r ≠ 2 := by omega
  have hrq : ¬ r ∣ 2 ^ f + 1 := uc22s2114r3f_not_dvd_two_pow_add_one hodd hr hr2 hrn
  have hbr' : b ^ r = 1 := hbr ▸ pow_orderOf_eq_one b
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := Subtype.ext (by simpa using hbr')
    rw [this, map_one]
  exact uc22s2114r4f_fieldSubgroups_of_psu hm hX hr hr5 hrq hθr hin



end CFSG.LocalAnalysis.UniquenessCase.UC22
