module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusSp6
public import CFSG.GroupTheory.SylowAutConj
public import CFSG.LocalAnalysis.StandardType.GGCoverRkFieldFix
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank (StatedSp)

private theorem fieldSp_torusHom_three {K : Type} [Field K]
    (σ : K ≃+* K) (t : Fin 3 → Kˣ) :
    fieldSp 3 K σ (torusHom t) =
      torusHom (fun i => Units.map (σ : K →* K) (t i)) := by
  apply statedSp_ext
  rw [coe_fieldSp, coe_torusHom, coe_torusHom]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => by_cases h : i = j <;> simp [h]
    | inr j => simp
  | inr i =>
    cases j with
    | inl j => simp
    | inr j => by_cases h : i = j <;> simp [h]

theorem sylow_torsion_fixed_statedSp_three
    {K : Type} [Field K] [Finite K] [CharP K 2] {f r : ℕ}
    (hK : Nat.card K = 2 ^ f) (hr : r.Prime) (hr7 : 7 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) (R : Sylow r (StatedSp 3 K))
    (α : MulAut (StatedSp 3 K)) (hα : ∃ k : ℕ, α ^ (r ^ k) = 1)
    (hαR : ∀ x ∈ (R : Subgroup (StatedSp 3 K)),
      α x ∈ (R : Subgroup (StatedSp 3 K))) :
    ∀ x ∈ (R : Subgroup (StatedSp 3 K)), x ^ r = 1 → α x = x := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (K ≃+* K) := Finite.of_injective
    (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hrqK : r ∣ Nat.card K - 1 := by rwa [hK]
  let a := (Nat.card K - 1).factorization r
  have hra : r ^ a ∣ Nat.card K - 1 :=
    (hr.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  have huord : orderOf u = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]
  let ζ : Kˣ := u ^ (orderOf u / r ^ a)
  have hζ : orderOf ζ = r ^ a :=
    orderOf_pow_orderOf_div (orderOf_pos u).ne' (by rw [huord]; exact hra)
  have : NeZero (r ^ a) := ⟨pow_ne_zero _ hr.ne_zero⟩
  have hζprim : IsPrimitiveRoot ζ (r ^ a) := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  let H : Subgroup (Fin 3 → Kˣ) :=
    Subgroup.pi Set.univ (fun _ => zpowers ζ)
  let S₀ : Subgroup (StatedSp 3 K) := H.map (torusHom (r := 3) (k := K))
  have hS₀card : Nat.card S₀ = r ^ (3 * a) := by
    change Nat.card ((Subgroup.pi Set.univ (fun _ : Fin 3 => zpowers ζ)).map
      (torusHom (r := 3) (k := K))) = _
    rw [map_pi_zpowers_torusHom, card_closure_single_torusHom, hζ, ← pow_mul, mul_comm]
  have hS₀ : IsPGroup r S₀ := IsPGroup.of_card hS₀card
  have hS₀i : ¬ r ∣ S₀.index := by
    apply CFSG.HardMathSupport.Timmesfeld.LinearRank.not_dvd_index_of_card_eq hr
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.factorization_card_statedSp_three
      hr (by omega) (by omega) hrqK, hS₀card, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul, hr.factorization_self, mul_one]
  have hS₀c : ∀ s ∈ S₀, ∀ t ∈ S₀, s * t = t * s := by
    rintro _ ⟨s, -, rfl⟩ _ ⟨t, -, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hHσ : ∀ (σ : K ≃+* K) (t : Fin 3 → Kˣ), t ∈ H →
      (fun i => Units.map (σ : K →* K) (t i)) ∈ H := by
    intro σ t ht
    apply (Subgroup.mem_pi Set.univ).mpr
    intro i _
    have hti := (Subgroup.mem_pi Set.univ).mp ht i (Set.mem_univ i)
    rw [hζprim.zpowers_eq, mem_rootsOfUnity] at hti ⊢
    simpa only [map_pow, map_one] using congrArg (Units.map (σ : K →* K)) hti
  have hS₀σ : ∀ (σ : K ≃+* K) s, s ∈ S₀ → fieldSp 3 K σ s ∈ S₀ := by
    rintro σ _ ⟨t, ht, rfl⟩
    rw [fieldSp_torusHom_three]
    exact mem_map_of_mem _ (hHσ σ t ht)
  obtain ⟨-, hcyc⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : IsCyclic (K ≃+* K) := hcyc
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := K ≃+* K)
  let Φ : MulAut (StatedSp 3 K) := fieldSp 3 K σ₀
  let eP : StatedSp 3 K ≃* CFSG.Assembly.LowTwoRank.StatedProj (StatedSp 3 K) :=
    MulEquiv.ofBijective (proj 3 K) UnitaryHigher.proj_bijective_of_charTwo
  have hconjP : ∀ y : StatedSp 3 K,
      MulAut.congr eP (MulAut.conj y) = MulAut.conj (proj 3 K y) := by
    intro y
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply, eP]
  have hfieldP : ∀ σ : K ≃+* K,
      MulAut.congr eP (fieldSp 3 K σ) = fieldAut 3 K σ := by
    intro σ
    ext x
    obtain ⟨s, rfl⟩ := proj_surjective x
    have hs : proj 3 K s = eP s := rfl
    rw [hs, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change proj 3 K (fieldSp 3 K σ s) = fieldAut 3 K σ (proj 3 K s)
    exact (fieldAut_proj σ s).symm
  have hΦ : ∀ β : MulAut (StatedSp 3 K),
      ∃ y : StatedSp 3 K, ∃ j : ℕ, β = MulAut.conj y * Φ ^ j := by
    intro β
    obtain ⟨A, σ, hβ⟩ := (automorphism_generation (K := K) (r := 3) (by norm_num)).2
      (MulAut.congr eP β)
    obtain ⟨y, hy⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
    have hβ' : β = MulAut.conj y * fieldSp 3 K σ := by
      apply (MulAut.congr eP).injective
      rw [hβ, hy, map_mul, hconjP, hfieldP, conjAut_statedSp]
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff σ σ₀).mp
      (mem_powers_iff_mem_zpowers.mpr (hσ₀ σ))
    refine ⟨y, j, ?_⟩
    rw [hβ', ← hj, map_pow]
  obtain ⟨e, m, hm, hσorder⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos σ₀).ne' r hr.ne_one
  have hσpow : (σ₀ ^ m) ^ (r ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hσorder, pow_orderOf_eq_one]
  have hφ : ∃ k : ℕ, (Φ ^ m) ^ (r ^ k) = 1 := by
    refine ⟨e, ?_⟩
    change (fieldSp 3 K σ₀ ^ m) ^ (r ^ e) = 1
    rw [← map_pow, ← map_pow, hσpow, map_one]
  have hφi : ¬ r ∣ ((MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)).range ⊔
      zpowers (Φ ^ m)).index :=
    fun h => hm (h.trans (CFSG.index_range_conj_sup_zpowers_pow_dvd hΦ m))
  have hφfix : ∀ x ∈ S₀, x ^ r = 1 → (Φ ^ m) x = x := by
    rintro _ ⟨t, -, rfl⟩ htr
    have ht : t ^ r = 1 := torusHom_injective (by rwa [map_pow, map_one])
    change (fieldSp 3 K σ₀ ^ m) (torusHom t) = _
    rw [← map_pow, fieldSp_torusHom_three]
    congr 1
    funext i
    apply Units.ext
    exact CFSG.StandardType.fieldAut_fixes_pow_eq_one hr hσpow (by
      simpa using congrArg (fun s : Fin 3 → Kˣ => ((s i : Kˣ) : K)) ht)
  have hφS : ∀ s ∈ S₀, (Φ ^ m) s ∈ S₀ := by
    simpa only [Φ, ← map_pow] using hS₀σ (σ₀ ^ m)
  exact CFSG.apply_eq_self_of_pow_eq_one hS₀ hS₀i hS₀c hφ hφS
    hφi hφfix R.isPGroup' R.not_dvd_index hα hαR

theorem sylow_torsion_fixed_of_lieModel_psp_three
    {X : Type} [Group X] [Finite X] {f r : ℕ}
    (hX : LieModel X .PSp 3 2 f) (hr : r.Prime) (hr7 : 7 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) (R : Sylow r X) (α : MulAut X)
    (hα : ∃ k : ℕ, α ^ (r ^ k) = 1)
    (hαR : ∀ x ∈ (R : Subgroup X), α x ∈ (R : Subgroup X)) :
    ∀ x ∈ (R : Subgroup X), x ^ r = 1 → α x = x := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel hX
  let R' : Sylow r (StatedSp 3 K) := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : (R' : Subgroup (StatedSp 3 K)) = (R : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R
  have hα' : ∃ k : ℕ, (MulAut.congr e α) ^ (r ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hαR' : ∀ y ∈ (R' : Subgroup (StatedSp 3 K)),
      MulAut.congr e α y ∈ (R' : Subgroup (StatedSp 3 K)) := by
    intro y hy
    rw [hR] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using mem_map_of_mem e.toMonoidHom (hαR x hx)
  intro x hx hxr
  apply e.injective
  simpa using sylow_torsion_fixed_statedSp_three hK hr hr7 hrq R' (MulAut.congr e α) hα' hαR'
    (e x) (by rw [hR]; exact mem_map_of_mem _ hx) (by rw [← map_pow, hxr, map_one])

end CFSG.LocalAnalysis.UniquenessCase.UC22
