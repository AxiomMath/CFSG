module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.StandardType.SuDvdRootGen

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.LineU CFSG.StandardType.TypeA

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'} {A : Subgroup (MulAut L')}

theorem commute_conj_permSU_swap_iff (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hφs : Function.Surjective φ) {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t)
    (i j : Fin d) :
    MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a =
        a * MulAut.conj (φ (permSU hK (Equiv.swap i j))) ↔ t i = t j := by
  classical
  constructor
  · intro hcomm
    have h1 : MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a *
        (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹ = a := by
      rw [hcomm]
      group
    have h2 : ActsDiagU φ (MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a *
        (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹)
        (fun k => t ((Equiv.swap i j)⁻¹ k)) :=
      ActsDiagU.conj_perm hK ha (Equiv.swap i j)
    rw [h1] at h2
    obtain ⟨m, hmi, hmj⟩ := exists_not_mem_two hd i j
    have h3 := ActsDiagU.ratio_eq hK hd hφker ha h2 m i
    rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hmi hmj,
      Equiv.swap_apply_left] at h3
    exact inv_inj.mp (mul_left_cancel₀ (ha.ne_zero m) h3)
  · intro htij
    have hdiag : (fun k => t ((Equiv.swap i j)⁻¹ k)) = t := by
      funext k
      by_cases hki : k = i
      · rw [hki, Equiv.swap_inv, Equiv.swap_apply_left, htij]
      · by_cases hkj : k = j
        · rw [hkj, Equiv.swap_inv, Equiv.swap_apply_right]
          exact htij
        · rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hki hkj]
    have h2 : ActsDiagU φ (MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a *
        (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹)
        (fun k => t ((Equiv.swap i j)⁻¹ k)) :=
      ActsDiagU.conj_perm hK ha (Equiv.swap i j)
    rw [hdiag] at h2
    have h1 : MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a *
        (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹ = a :=
      ActsDiagU.unique hφs h2 ha
    calc MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a
        = (MulAut.conj (φ (permSU hK (Equiv.swap i j))) * a *
            (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹) *
            MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by group
      _ = a * MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by rw [h1]

theorem conj_permSU_mem_normalizer (hK : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1)
    (hd : 3 ≤ d) (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hsc : GGTorusSelfCent p A) (σ : Equiv.Perm (Fin d)) :
    MulAut.conj (φ (permSU hK σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  classical
  have hcinv : MulAut.conj (φ (permSU hK σ⁻¹)) =
      (MulAut.conj (φ (permSU hK σ)))⁻¹ := by
    have hP : permSU hK σ⁻¹ = (permSU hK σ)⁻¹ := by
      apply Subtype.ext
      rw [coe_permSU, Subgroup.coe_inv, coe_permSU]
      exact map_inv (CFSG.RankThree.Classical.permGL (K := K)) σ
    rw [hP, map_inv, map_inv]
  have hkey : ∀ τ : Equiv.Perm (Fin d), ∀ b ∈ A,
      MulAut.conj (φ (permSU hK τ)) * b * (MulAut.conj (φ (permSU hK τ)))⁻¹ ∈ A := by
    intro τ b hb
    obtain ⟨t, ht⟩ := hdiag b hb
    have hup : ∀ k, (t (τ⁻¹ k) * (t k)⁻¹) ^ p = 1 := fun k =>
      ActsDiagU.ratio_pow hK hd hφker ht (hAp b hb) (τ⁻¹ k) k
    have huq : ∀ k, (t (τ⁻¹ k) * (t k)⁻¹) ^ (2 ^ n + 1) = 1 := fun k => by
      obtain ⟨m, hm⟩ := hpq
      rw [hm, pow_mul, hup k, one_pow]
    have hprod : ∏ k, t (τ⁻¹ k) * (t k)⁻¹ = 1 := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp τ⁻¹ t]
      exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => ht.ne_zero k)
    obtain ⟨D, hD⟩ := exists_diagSU hK huq hprod
    have hDA : MulAut.conj (φ D) ∈ A := conj_mem_of_selfCent_U hsc hdiag hD hup
    have hmul : ActsDiagU φ (MulAut.conj (φ D) * b) (fun k => t (τ⁻¹ k)) := by
      have h := (actsDiagU_conj hD).mul ht
      have hfe : (fun k => (t (τ⁻¹ k) * (t k)⁻¹) * t k) = fun k => t (τ⁻¹ k) := by
        funext k
        rw [mul_assoc, inv_mul_cancel₀ (ht.ne_zero k), mul_one]
      rwa [hfe] at h
    have hconj : ActsDiagU φ (MulAut.conj (φ (permSU hK τ)) * b *
        (MulAut.conj (φ (permSU hK τ)))⁻¹) (fun k => t (τ⁻¹ k)) :=
      ActsDiagU.conj_perm hK ht τ
    rw [ActsDiagU.unique hφs hconj hmul]
    exact A.mul_mem hDA hb
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hkey σ b hb
  · intro hb
    have h1 := hkey σ⁻¹ _ hb
    rw [hcinv] at h1
    have h2 : (MulAut.conj (φ (permSU hK σ)))⁻¹ *
        (MulAut.conj (φ (permSU hK σ)) * b * (MulAut.conj (φ (permSU hK σ)))⁻¹) *
        ((MulAut.conj (φ (permSU hK σ)))⁻¹)⁻¹ = b := by
      group
    rwa [h2] at h1

theorem ggTorusWeylElt_permSU (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (hAp : ∀ a ∈ A, a ^ p = 1)
    (σ : Equiv.Perm (Fin d)) :
    GGTorusWeylElt p A (φ (permSU hK σ)) :=
  weyl_W_prop hK hd hφker hAp hdiag (φ (permSU hK σ)) ⟨σ, rfl⟩

theorem isReflection_permSU_swap [Finite L'] (hK : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d) (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hsc : GGTorusSelfCent p A) {i j : Fin d} (hij : i ≠ j)
    (hn : MulAut.conj (φ (permSU hK (Equiv.swap i j))) ∈
      Subgroup.normalizer (A : Set (MulAut L'))) :
    GGIsReflection p (ggConjAut A hn) := by
  classical
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  haveI : Finite ↥A := Subtype.finite
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hK.one_le hpq
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let σ : Equiv.Perm (Fin d) := Equiv.swap i j
  let g : MulAut L' := MulAut.conj (φ (permSU hK σ))
  let f : MulAut ↥A := ggConjAut A hn
  have hf_apply : ∀ b : ↥A, ((f b : ↥A) : MulAut L') = g * (b : MulAut L') * g⁻¹ :=
    fun b => ggConjAut_apply A hn b
  have hPP : permSU hK σ * permSU hK σ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_permSU, ← map_mul, Equiv.swap_mul_self, map_one,
      Subgroup.coe_one]
  have hgg : g * g = 1 := by
    rw [← map_mul, ← map_mul, hPP, map_one, map_one]
  have hf2 : f ^ 2 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_pow_apply A hn 2 b]
    rw [show g ^ 2 = 1 by rw [pow_two]; exact hgg]
    simp
  have hAc : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    obtain ⟨ta, hta⟩ := hdiag (a : MulAut L') a.2
    obtain ⟨tb, htb⟩ := hdiag (b : MulAut L') b.2
    refine Subtype.ext ?_
    have h1 : ActsDiagU φ ((a : MulAut L') * (b : MulAut L')) (fun k => ta k * tb k) :=
      hta.mul htb
    have h2 : ActsDiagU φ ((b : MulAut L') * (a : MulAut L')) (fun k => tb k * ta k) :=
      htb.mul hta
    have h3 : (fun k => ta k * tb k) = fun k => tb k * ta k :=
      funext fun k => mul_comm _ _
    rw [h3] at h1
    exact ActsDiagU.unique hφs h1 h2
  obtain ⟨η, hηord, hηq⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) hK hp hpq
  have hηp : η ^ p = 1 := hηord ▸ pow_orderOf_eq_one η
  have hηpK : (η : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hηp, Units.val_one]
  have hηprim : IsPrimitiveRoot (η : K) p := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]
    exact hηord
  have hηq' : (η : K) ^ (2 ^ n + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hηq, Units.val_one]
  obtain ⟨D₁, hD₁⟩ := exists_diagSU hK (u := ggPairVec i j (η : K))
    (ggPairVec_norm_one hηq' i j) (prod_ggPairVec (η : K) η.ne_zero)
  have hD₁p : ∀ k, ggPairVec i j (η : K) k ^ p = 1 := fun k => pow_ggPairVec hηpK k
  have hD₁mem : MulAut.conj (φ D₁) ∈ A := conj_mem_of_selfCent_U hsc hdiag hD₁ hD₁p
  let a₁ : ↥A := ⟨MulAut.conj (φ D₁), hD₁mem⟩
  have ha₁coe : (a₁ : MulAut L') = MulAut.conj (φ D₁) := rfl
  have ha₁p : a₁ ^ p = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ha₁coe, ← map_pow, ← map_pow,
      pow_eq_one_of_diagSU hD₁ hD₁p, map_one, map_one]
  have hδ : ∀ a : ↥A, ∃ e : ℕ, a * (f a)⁻¹ = a₁ ^ e := by
    intro a
    obtain ⟨t, hta⟩ := hdiag (a : MulAut L') a.2
    have hfa : ActsDiagU φ ((f a : ↥A) : MulAut L') (fun k => t (σ⁻¹ k)) := by
      rw [hf_apply a]
      exact ActsDiagU.conj_perm hK hta σ
    have hfinv : ActsDiagU φ (((f a)⁻¹ : ↥A) : MulAut L') (fun k => (t (σ⁻¹ k))⁻¹) := by
      rw [Subgroup.coe_inv]
      exact hfa.inv
    have hmul : ActsDiagU φ ((a : MulAut L') * (((f a)⁻¹ : ↥A) : MulAut L'))
        (fun k => t k * (t (σ⁻¹ k))⁻¹) := hta.mul hfinv
    have hratp : (t i * (t j)⁻¹) ^ p = 1 :=
      ActsDiagU.ratio_pow hK hd hφker hta (hAp (a : MulAut L') a.2) i j
    obtain ⟨e, -, he⟩ := hηprim.eq_pow_of_pow_eq_one hratp
    have he' : t i * (t j)⁻¹ = (η : K) ^ e := he.symm
    refine ⟨e, Subtype.ext ?_⟩
    have hfun : (fun k => t k * (t (σ⁻¹ k))⁻¹) = ggPairVec i j ((η : K) ^ e) := by
      rw [← he']
      exact TypeA.mul_inv_comp_swap (fun k => hta.ne_zero k) hij
    rw [hfun] at hmul
    have hpow : ActsDiagU φ ((MulAut.conj (φ D₁)) ^ e) (ggPairVec i j ((η : K) ^ e)) := by
      have h : ActsDiagU φ ((MulAut.conj (φ D₁)) ^ e)
          (fun k => ggPairVec i j (η : K) k ^ e) :=
        (actsDiagU_conj (φ := φ) hD₁).pow e
      rwa [ggPairVec_pow] at h
    have h1 := ActsDiagU.unique hφs hmul hpow
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, ha₁coe] using h1
  have h₁ : a₁ * (f a₁)⁻¹ ≠ 1 := by
    intro hcontra
    have hfa₁ : (f a₁ : ↥A) = a₁ := (mul_inv_eq_one.mp hcontra).symm
    have hcomm : g * (a₁ : MulAut L') = (a₁ : MulAut L') * g := by
      have h1 : g * (a₁ : MulAut L') * g⁻¹ = (a₁ : MulAut L') := by
        rw [← hf_apply a₁]
        exact congrArg (fun x : ↥A => (x : MulAut L')) hfa₁
      calc g * (a₁ : MulAut L')
          = (g * (a₁ : MulAut L') * g⁻¹) * g := by group
        _ = (a₁ : MulAut L') * g := by rw [h1]
    have htij := (commute_conj_permSU_swap_iff hK hd hφker hφs
      (actsDiagU_conj hD₁) i j).mp hcomm
    rw [ggPairVec_apply, ggPairVec_apply, if_pos rfl, if_neg hij, mul_one,
      if_neg hij.symm, if_pos rfl, one_mul] at htij
    have h2 : (η : K) * (η : K) = 1 := by
      nth_rewrite 2 [htij]
      exact mul_inv_cancel₀ η.ne_zero
    have hη2 : η ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_two, Units.val_one]
      exact h2
    have hdvd : p ∣ 2 := by
      have h := orderOf_dvd_of_pow_eq_one hη2
      rwa [hηord] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  exact ⟨hf2, card_fix_mul_of_le_zpowers hp hAc f ha₁p hδ h₁⟩

private theorem exists_diag_eq_of_not_mem (hK : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) {a b c e : Fin d} (hab : a ≠ b)
    (hac : a ∉ ({c, e} : Finset (Fin d))) :
    ∃ t : Fin d → K, (∀ x, t x ^ p = 1) ∧ ∏ x, t x = 1 ∧ t a ≠ t b ∧ t c = t e := by
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hK.one_le hpq
  obtain ⟨η, hηord, -⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) hK hp hpq
  have hηpow : η ^ p = 1 := hηord ▸ pow_orderOf_eq_one η
  have hηp : (η : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hηpow, Units.val_one]
  have hη1 : (η : K) ≠ 1 := by
    intro h
    have h1 : orderOf (η : K) = 1 := orderOf_eq_one_iff.mpr h
    rw [orderOf_units, hηord] at h1
    exact hp.one_lt.ne' h1
  have hηinv : (η : K) ≠ (η : K)⁻¹ := by
    intro h
    have h2 : (η : K) * (η : K) = 1 := by
      nth_rewrite 2 [h]
      exact mul_inv_cancel₀ η.ne_zero
    have hdvd : p ∣ 2 := by
      have h3 : (η : K) ^ 2 = 1 := by rw [pow_two]; exact h2
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rwa [orderOf_units, hηord] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  obtain ⟨m, hma, hmc, hme⟩ := exists_not_mem_three hd a c e
  have ham : a ≠ m := Ne.symm hma
  have hcm : c ≠ m := Ne.symm hmc
  have hem : e ≠ m := Ne.symm hme
  have hca : c ≠ a := by
    intro h
    exact hac (by rw [← h]; exact Finset.mem_insert_self c {e})
  have hea : e ≠ a := by
    intro h
    exact hac (by rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e))
  have haa : ggPairVec a m (η : K) a = (η : K) := by
    rw [ggPairVec_apply, if_pos rfl, if_neg ham, mul_one]
  have hmm : ggPairVec a m (η : K) m = (η : K)⁻¹ := by
    rw [ggPairVec_apply, if_neg (Ne.symm ham), if_pos rfl, one_mul]
  have hone : ∀ x : Fin d, x ≠ a → x ≠ m → ggPairVec a m (η : K) x = 1 := by
    intro x hxa hxm
    rw [ggPairVec_apply, if_neg hxa, if_neg hxm, one_mul]
  refine ⟨ggPairVec a m (η : K), fun x => pow_ggPairVec hηp x,
    prod_ggPairVec (η : K) η.ne_zero, ?_, ?_⟩
  · rw [haa]
    by_cases hbm : b = m
    · subst hbm
      rw [hmm]
      exact hηinv
    · rw [hone b (fun h => hab h.symm) hbm]
      exact hη1
  · rw [hone c hca hcm, hone e hea hem]

theorem pair_eq_of_ggConjAut_eq_permSU (hK : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (hsc : GGTorusSelfCent p A)
    {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l)
    (hn₁ : MulAut.conj (φ (permSU hK (Equiv.swap i j))) ∈
      Subgroup.normalizer (A : Set (MulAut L')))
    (hn₂ : MulAut.conj (φ (permSU hK (Equiv.swap k l))) ∈
      Subgroup.normalizer (A : Set (MulAut L')))
    (h : ggConjAut A hn₁ = ggConjAut A hn₂) :
    ({i, j} : Finset (Fin d)) = {k, l} := by
  classical
  have hkey : ∀ t : Fin d → K, (∀ x, t x ^ p = 1) → ∏ x, t x = 1 →
      (t i = t j ↔ t k = t l) := by
    intro t ht hprod
    have hnorm : ∀ x, t x ^ (2 ^ n + 1) = 1 := fun x => by
      obtain ⟨m, hm⟩ := hpq
      rw [hm, pow_mul, ht x, one_pow]
    obtain ⟨D, hD⟩ := exists_diagSU hK hnorm hprod
    have hmem : MulAut.conj (φ D) ∈ A := conj_mem_of_selfCent_U hsc hdiag hD ht
    let b : ↥A := ⟨MulAut.conj (φ D), hmem⟩
    have hbact : ActsDiagU φ (b : MulAut L') t := actsDiagU_conj (φ := φ) hD
    have hfix₁ : ggConjAut A hn₁ b = b ↔ t i = t j := by
      have h1 : ggConjAut A hn₁ b = b ↔
          MulAut.conj (φ (permSU hK (Equiv.swap i j))) * (b : MulAut L') *
            (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹ = (b : MulAut L') := by
        rw [← ggConjAut_apply A hn₁ b]
        exact ⟨fun hh => congrArg (fun x : ↥A => (x : MulAut L')) hh,
          fun hh => Subtype.ext hh⟩
      have h2 : MulAut.conj (φ (permSU hK (Equiv.swap i j))) * (b : MulAut L') *
            (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹ = (b : MulAut L') ↔
          MulAut.conj (φ (permSU hK (Equiv.swap i j))) * (b : MulAut L') =
            (b : MulAut L') * MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by
        constructor
        · intro hh
          calc MulAut.conj (φ (permSU hK (Equiv.swap i j))) * (b : MulAut L')
              = (MulAut.conj (φ (permSU hK (Equiv.swap i j))) * (b : MulAut L') *
                  (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹) *
                  MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by group
            _ = (b : MulAut L') * MulAut.conj (φ (permSU hK (Equiv.swap i j))) := by
                rw [hh]
        · intro hh
          calc MulAut.conj (φ (permSU hK (Equiv.swap i j))) * (b : MulAut L') *
                (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹
              = ((b : MulAut L') * MulAut.conj (φ (permSU hK (Equiv.swap i j)))) *
                  (MulAut.conj (φ (permSU hK (Equiv.swap i j))))⁻¹ := by rw [hh]
            _ = (b : MulAut L') := by group
      exact h1.trans (h2.trans
        (commute_conj_permSU_swap_iff hK (by omega) hφker hφs hbact i j))
    have hfix₂ : ggConjAut A hn₂ b = b ↔ t k = t l := by
      have h1 : ggConjAut A hn₂ b = b ↔
          MulAut.conj (φ (permSU hK (Equiv.swap k l))) * (b : MulAut L') *
            (MulAut.conj (φ (permSU hK (Equiv.swap k l))))⁻¹ = (b : MulAut L') := by
        rw [← ggConjAut_apply A hn₂ b]
        exact ⟨fun hh => congrArg (fun x : ↥A => (x : MulAut L')) hh,
          fun hh => Subtype.ext hh⟩
      have h2 : MulAut.conj (φ (permSU hK (Equiv.swap k l))) * (b : MulAut L') *
            (MulAut.conj (φ (permSU hK (Equiv.swap k l))))⁻¹ = (b : MulAut L') ↔
          MulAut.conj (φ (permSU hK (Equiv.swap k l))) * (b : MulAut L') =
            (b : MulAut L') * MulAut.conj (φ (permSU hK (Equiv.swap k l))) := by
        constructor
        · intro hh
          calc MulAut.conj (φ (permSU hK (Equiv.swap k l))) * (b : MulAut L')
              = (MulAut.conj (φ (permSU hK (Equiv.swap k l))) * (b : MulAut L') *
                  (MulAut.conj (φ (permSU hK (Equiv.swap k l))))⁻¹) *
                  MulAut.conj (φ (permSU hK (Equiv.swap k l))) := by group
            _ = (b : MulAut L') * MulAut.conj (φ (permSU hK (Equiv.swap k l))) := by
                rw [hh]
        · intro hh
          calc MulAut.conj (φ (permSU hK (Equiv.swap k l))) * (b : MulAut L') *
                (MulAut.conj (φ (permSU hK (Equiv.swap k l))))⁻¹
              = ((b : MulAut L') * MulAut.conj (φ (permSU hK (Equiv.swap k l)))) *
                  (MulAut.conj (φ (permSU hK (Equiv.swap k l))))⁻¹ := by rw [hh]
            _ = (b : MulAut L') := by group
      exact h1.trans (h2.trans
        (commute_conj_permSU_swap_iff hK (by omega) hφker hφs hbact k l))
    have hiff : ggConjAut A hn₁ b = b ↔ ggConjAut A hn₂ b = b := by
      rw [DFunLike.congr_fun h b]
    exact hfix₁.symm.trans (hiff.trans hfix₂)
  by_contra hne
  have hsub : ¬ ({i, j} : Finset (Fin d)) ⊆ {k, l} := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_pair hkl, Finset.card_pair hij]))
  obtain ⟨a, ha_mem, ha_not⟩ := Set.not_subset.mp hsub
  have haij : a = i ∨ a = j := by
    simpa using ha_mem
  rcases haij with h | h
  · have hi_not : i ∉ ({k, l} : Finset (Fin d)) := by rwa [h] at ha_not
    obtain ⟨t, ht, hprod, hta, htc⟩ :=
      exists_diag_eq_of_not_mem (a := i) (b := j) (c := k) (e := l) hK hp hpq hd hij hi_not
    exact hta ((hkey t ht hprod).mpr htc)
  · have hj_not : j ∉ ({k, l} : Finset (Fin d)) := by rwa [h] at ha_not
    obtain ⟨t, ht, hprod, hta, htc⟩ :=
      exists_diag_eq_of_not_mem (a := j) (b := i) (c := k) (e := l) hK hp hpq hd
        (Ne.symm hij) hj_not
    exact hta ((hkey t ht hprod).mpr htc).symm

end CFSG.StandardType.SuDvdRootGen

end
