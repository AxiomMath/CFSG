module

public import CFSG.RankThree.PartOne.SLBN.LocalBasic
public import CFSG.RankThree.PartOne.SRC.RankOne
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup Matrix CFSG
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K]

section SmallFacts

omit [Finite K] in
theorem neg_one_sq_sl2 : (-1 : SL(2, K)) ^ 2 = 1 := by simp

omit [Finite K] in
theorem neg_one_ne_one_sl2 (h : (2 : K) ≠ 0) : (-1 : SL(2, K)) ≠ 1 := by
  intro h1
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  simp at this
  apply h
  linear_combination -this

omit [Finite K] in
theorem neg_one_mem_center_sl2 : (-1 : SL(2, K)) ∈ Subgroup.center (SL(2, K)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp

omit [Finite K] in
theorem eq_one_or_neg_one_of_mem_center {c : SL(2, K)} (hc : c ∈ Subgroup.center (SL(2, K))) :
    c = 1 ∨ c = -1 := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr2 : r * r = 1 := by simpa [pow_two] using hr
  rcases mul_self_eq_one_iff.mp hr2 with h | h
  · left
    ext i j
    rw [← hrc, h]; simp
  · right
    apply Subtype.ext
    rw [← hrc, h]
    simp only [map_neg, map_one, SpecialLinearGroup.coe_neg]
    rfl

end SmallFacts

section Normal

variable (hK : Nat.card K = 9)
include hK

theorem card_sl2_nine : Nat.card (SL(2, K)) = 720 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
  norm_num

theorem sl2_quasisimple_nine : CFSG.IsQuasisimple (SL(2, K)) :=
  CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))

end Normal

section Cover

variable {W : Type*} [Group W] [Finite W] (ρ : W →* SL(2, K))

omit [Finite K] [Finite W] in
theorem mem_center_of_map_mem_center [Group.IsPerfect W] (hcen : ρ.ker ≤ Subgroup.center W)
    {x : W} (hx : ρ x ∈ Subgroup.center (SL(2, K))) : x ∈ Subgroup.center W := by
  have hperf : ⁅(⊤ : Subgroup W), (⊤ : Subgroup W)⁆ = (⊤ : Subgroup W) := by
    have := Group.IsPerfect.commutator_eq_top (G := W)
    rwa [_root_.commutator_def] at this
  have hc : ⁅(⊤ : Subgroup W), Subgroup.zpowers x⁆ ≤ Subgroup.center W := by
    rw [Subgroup.commutator_le]
    intro g _ k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    apply hcen
    rw [MonoidHom.mem_ker, map_commutatorElement, map_zpow]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hx m)) (ρ g))
  rw [Subgroup.mem_center_iff]
  intro w
  exact (commute_of_commutator_le_center hperf hc w (Subgroup.mem_top w) x
    (Subgroup.mem_zpowers x))

theorem normal_le_center_or_top_nine (hK : Nat.card K = 9) [Group.IsPerfect W]
    (hρ : Function.Surjective ρ) (hker : IsPGroup 3 ρ.ker) (hcen : ρ.ker ≤ Subgroup.center W)
    (N : Subgroup W) [N.Normal] : N ≤ Subgroup.center W ∨ N = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hρN : (N.map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρ
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (sl2_quasisimple_nine hK) hρN with
    htop | hle
  · right
    have hpg : IsPGroup 3 (W ⧸ N) :=
      CFSG.RankThree.PartOne.SRC.isPGroup_quotient_of_map_eq_top ρ hker N htop
    exact CFSG.RankThree.PartOne.SRC.eq_top_of_perfect_pgroup_quotient N hpg
  · left
    intro x hx
    exact mem_center_of_map_mem_center ρ hcen (hle (Subgroup.mem_map_of_mem ρ hx))

theorem exists_five_noncentral_nine (hK : Nat.card K = 9) [Group.IsPerfect W]
    (hρ : Function.Surjective ρ) (hker : IsPGroup 3 ρ.ker) :
    ∃ h : W, orderOf h = 5 ∧ h ∉ Subgroup.center W := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card W := by
    have h1 : Nat.card (SL(2, K)) ∣ Nat.card W := Subgroup.card_dvd_of_surjective hρ
    exact (by rw [card_sl2_nine hK]; norm_num : 5 ∣ Nat.card (SL(2, K))).trans h1
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 5 h5
  refine ⟨h, hh, fun hc => ?_⟩
  have hρc : ρ h ∈ Subgroup.center (SL(2, K)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := hρ q
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc w).symm]
  have hord : orderOf (ρ h) ∣ 5 := by
    rw [← hh]; exact orderOf_map_dvd ρ h
  have hd2 : orderOf (ρ h) ∣ Nat.card (Subgroup.center (SL(2, K))) :=
    Subgroup.orderOf_dvd_natCard _ hρc
  have hcop := CFSG.RankThree.PartOne.SRC.coprime_card_center_SL2 (p := 5) (F := K)
    (by norm_num) (by norm_num)
  have h1 : orderOf (ρ h) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord hd2
  have hh1 : ρ h = 1 := orderOf_eq_one_iff.mp h1
  have hmem : h ∈ ρ.ker := hh1
  obtain ⟨k, hk⟩ := hker ⟨h, hmem⟩
  have hk' : h ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  have hdvd : 5 ∣ 3 ^ k := by rw [← hh]; exact orderOf_dvd_of_pow_eq_one hk'
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd)
  omega

theorem card_ker_le_three (hK : Nat.card K = 9) [CharP K 3] [Group.IsPerfect W]
    (hρ : Function.Surjective ρ) (hker : IsPGroup 3 ρ.ker) (hcen : ρ.ker ≤ Subgroup.center W) :
    Nat.card ρ.ker ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K 3 2).1 this
    omega
  obtain ⟨z, hz⟩ := hρ (-1)
  have hz2 : z ^ 2 ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, hz, neg_one_sq_sl2]
  obtain ⟨m, hm⟩ := hker ⟨z ^ 2, hz2⟩
  have hm' : (z ^ 2) ^ (3 ^ m) = 1 := congrArg Subtype.val hm
  set t : W := z ^ (3 ^ m) with ht
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← pow_mul, mul_comm, pow_mul, hm']
  have hρt : ρ t = -1 := by
    rw [ht, map_pow, hz]
    exact Odd.neg_one_pow ((Nat.odd_iff.2 (by simp [Nat.pow_mod])) : Odd (3 ^ m))
  have htc : t ∈ Subgroup.center W :=
    mem_center_of_map_mem_center ρ hcen (hρt ▸ neg_one_mem_center_sl2)
  have hnorm : (Subgroup.zpowers t).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hgt : g * t * g⁻¹ = t := by
      rw [Subgroup.mem_center_iff.mp htc g, mul_inv_cancel_right]
    rw [← conj_zpow, hgt]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
  have hle : Subgroup.zpowers t ≤
      ((CFSG.SectionRank.OddCover.pslMk (K := K)).comp ρ).ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker, MonoidHom.comp_apply, hρt,
      CFSG.SectionRank.OddCover.pslMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact neg_one_mem_center_sl2
  let π : W ⧸ Subgroup.zpowers t →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.lift (Subgroup.zpowers t) ((CFSG.SectionRank.OddCover.pslMk (K := K)).comp ρ) hle
  have hπ : ∀ w : W, π (w : W ⧸ Subgroup.zpowers t) = CFSG.SectionRank.OddCover.pslMk (ρ w) :=
    fun w => rfl
  have hπs : Function.Surjective π := by
    intro q
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨w, rfl⟩ := hρ A
    exact ⟨w, rfl⟩
  have hkerπ : ∀ x : W ⧸ Subgroup.zpowers t, x ∈ π.ker →
      ∃ k ∈ ρ.ker, x = (k : W ⧸ Subgroup.zpowers t) := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hxy : π (y : W ⧸ Subgroup.zpowers t) = 1 := hx
    rw [hπ, CFSG.SectionRank.OddCover.pslMk, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hxy
    rcases eq_one_or_neg_one_of_mem_center hxy with h1 | h1
    · exact ⟨y, h1, rfl⟩
    · refine ⟨y * t, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, h1, hρt]
        simp
      · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).2 (Subgroup.mem_zpowers t),
          mul_one]
  have hker3 : IsPGroup 3 π.ker := by
    intro x
    obtain ⟨k, hk, hkx⟩ := hkerπ x x.2
    obtain ⟨a, ha⟩ := hker ⟨k, hk⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have : k ^ 3 ^ a = 1 := congrArg Subtype.val ha
    change (x : W ⧸ Subgroup.zpowers t) ^ 3 ^ a = 1
    rw [hkx, ← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hkerc : π.ker ≤ Subgroup.center (W ⧸ Subgroup.zpowers t) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hkerπ x hx
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hcen hk) w]
  obtain ⟨n, hn⟩ := hker3.exists_card_eq
  have hodd : Odd (Nat.card π.ker) := by rw [hn]; exact Odd.pow (by decide)
  obtain ⟨-, h9⟩ := CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel (p := 3) (f := 2)
    (by norm_num) (by rw [hK]; norm_num) π hπs hkerc hodd
  have hle3 : Nat.card π.ker ≤ 3 := (h9 (by norm_num)).2
  have hmem : ∀ k : ρ.ker, ((k : W) : W ⧸ Subgroup.zpowers t) ∈ π.ker := by
    intro k
    show π _ = 1
    rw [hπ, MonoidHom.mem_ker.mp k.2, map_one]
  have hinj : Function.Injective
      (fun k : ρ.ker => (⟨((k : W) : W ⧸ Subgroup.zpowers t), hmem k⟩ : π.ker)) := by
    intro k k' h
    have h1 : ((k : W) : W ⧸ Subgroup.zpowers t) = ((k' : W) : W ⧸ Subgroup.zpowers t) :=
      congrArg Subtype.val h
    rw [QuotientGroup.eq] at h1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hk1 : ρ ((k : W)⁻¹ * k') = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp k.2, MonoidHom.mem_ker.mp k'.2]; simp
    obtain ⟨r, hr | hr⟩ := Int.even_or_odd' j
    · have : t ^ j = 1 := by rw [hr, _root_.zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2,
        _root_.one_zpow]
      rw [this] at hj
      apply Subtype.ext
      have : (k : W)⁻¹ * k' = 1 := hj.symm
      exact inv_mul_eq_one.mp this
    · exfalso
      have : t ^ j = t := by
        rw [hr, _root_.zpow_add, _root_.zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2,
          _root_.one_zpow, one_mul, zpow_one]
      rw [this] at hj
      rw [← hj, hρt] at hk1
      exact neg_one_ne_one_sl2 h2 hk1
  have := Nat.card_le_card_of_injective _ hinj
  omega

section Three

open CFSG.SectionRank.OddCover

omit [Finite K] in
theorem slU_injective' {s t : K} (h : slU s = slU t) : s = t := by
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [coe_slU] using this

omit [Finite K] in
theorem slU_pow (t : K) (n : ℕ) : slU t ^ n = slU (n • t) := by
  induction n with
  | zero => simp [slU_zero]
  | succ n ih => rw [pow_succ, ih, ← slU_add, succ_nsmul]

omit [Finite K] in
theorem eq_of_add_mul_eq_of_charP {ω : K} (hω : ω ^ 2 = -1) (ι : ZMod 3 →+* K)
    {a b a' b' : ZMod 3} (h : ι a + ι b * ω = ι a' + ι b' * ω) : a = a' ∧ b = b' := by
  by_cases hb : b = b'
  · subst hb
    exact ⟨ι.injective (by linear_combination h), rfl⟩
  · exfalso
    have hβ : b - b' ≠ 0 := sub_ne_zero.mpr hb
    have h1 : ι (b - b') * ω = ι (a' - a) := by
      rw [map_sub, map_sub]; linear_combination h
    have h2 : ι ((b - b') * (b - b') + (a' - a) * (a' - a)) = 0 := by
      rw [map_add, map_mul, map_mul]
      have : ι (b - b') * ι (b - b') * (ω ^ 2) = ι (a' - a) * ι (a' - a) := by
        calc ι (b - b') * ι (b - b') * (ω ^ 2) = (ι (b - b') * ω) * (ι (b - b') * ω) := by ring
          _ = _ := by rw [h1]
      rw [hω] at this
      linear_combination -this
    have h3 : (b - b') * (b - b') + (a' - a) * (a' - a) = 0 :=
      ι.injective (by rw [h2, map_zero])
    revert hβ h3
    generalize b - b' = β
    generalize a' - a = α
    revert α β
    decide

theorem exists_pow_three_eq_one_nine (hK : Nat.card K = 9) [CharP K 3] [Group.IsPerfect W]
    (hρ : Function.Surjective ρ) (hker : IsPGroup 3 ρ.ker) (hcen : ρ.ker ≤ Subgroup.center W) :
    ∃ e : W, e ^ 3 = 1 ∧ ρ e ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := card_ker_le_three ρ hK hρ hker hcen
  have hC3 : ∀ c ∈ ρ.ker, c ^ 3 = 1 := by
    intro c hc
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    have hn1 : n ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ n := by omega
      have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      omega
    have hpow : (⟨c, hc⟩ : ρ.ker) ^ Nat.card ρ.ker = 1 := pow_card_eq_one'
    rw [hn] at hpow
    interval_cases n
    · have h1 : c = 1 := by simpa using congrArg Subtype.val hpow
      rw [h1, one_pow]
    · simpa using congrArg Subtype.val hpow
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω ^ 2 = -1 := by
    have := Fintype.ofFinite K
    obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).mpr
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
    exact ⟨r, by rw [sq, ← hr]⟩
  let ι : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  obtain ⟨x, hx⟩ := hρ (CFSG.SectionRank.OddCover.slU (1 : K))
  obtain ⟨y, hy⟩ := hρ (CFSG.SectionRank.OddCover.slU ω)
  have hnat : ∀ a : ZMod 3, (a.val : K) = ι a := fun a => by
    rw [← map_natCast ι, ZMod.natCast_zmod_val]
  have himg : ∀ a b : ZMod 3, ρ (x ^ a.val * y ^ b.val) =
      CFSG.SectionRank.OddCover.slU (ι a + ι b * ω) := by
    intro a b
    rw [map_mul, map_pow, map_pow, hx, hy, slU_pow, slU_pow, ← CFSG.SectionRank.OddCover.slU_add,
      nsmul_eq_mul, nsmul_eq_mul, hnat, hnat, mul_one]
  have hcube : ∀ a b : ZMod 3, (x ^ a.val * y ^ b.val) ^ 3 ∈ ρ.ker := by
    intro a b
    rw [MonoidHom.mem_ker, map_pow, himg, slU_pow]
    have : (3 : ℕ) • (ι a + ι b * ω) = 0 := by
      rw [nsmul_eq_mul]
      have : ((3 : ℕ) : K) = 0 := CharP.cast_eq_zero K 3
      rw [this, zero_mul]
    rw [this, CFSG.SectionRank.OddCover.slU_zero]
  let f : ZMod 3 × ZMod 3 → ρ.ker := fun ab => ⟨(x ^ ab.1.val * y ^ ab.2.val) ^ 3, hcube _ _⟩
  let _ : Fintype ρ.ker := Fintype.ofFinite _
  have hlt : Fintype.card ρ.ker < Fintype.card (ZMod 3 × ZMod 3) := by
    rw [Fintype.card_prod, ZMod.card, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨⟨a, b⟩, ⟨a', b'⟩, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  have hfeq' : (x ^ a.val * y ^ b.val) ^ 3 = (x ^ a'.val * y ^ b'.val) ^ 3 :=
    congrArg Subtype.val hfeq
  set g := x ^ a.val * y ^ b.val with hg
  set g' := x ^ a'.val * y ^ b'.val with hg'
  have hcomm : ρ g * ρ g' = ρ g' * ρ g := by
    rw [hg, hg', himg, himg, ← CFSG.SectionRank.OddCover.slU_add,
      ← CFSG.SectionRank.OddCover.slU_add, add_comm]
  refine ⟨g * g'⁻¹, ?_, ?_⟩
  · have hcm : ⁅g, g'⁻¹⁆ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, map_inv]
      exact commutatorElement_eq_one_iff_mul_comm.mpr ((Commute.inv_right (show Commute (ρ g) (ρ g')
        from hcomm)).eq)
    rw [cube_mul_eq hcen hC3 hcm, inv_pow, hfeq', mul_inv_cancel]
  · intro h1
    have h2 : ρ g = ρ g' := by
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    rw [hg, hg', himg, himg] at h2
    have h3 := slU_injective' h2
    obtain ⟨ha, hb⟩ := eq_of_add_mul_eq_of_charP hω ι h3
    exact hne (Prod.ext ha hb)

end Three

end Cover

end CFSG.RankThree.PartOne.SLBN
