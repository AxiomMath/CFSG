module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

private theorem r1gen_isPGroup {G : Type} [Group G] {V : Subgroup G}
    (hV2 : CFSG.Open.IsElemAbelian 2 V) : IsPGroup 2 V :=
  fun x => ⟨1, Subtype.ext (by simpa using hV2.2 x x.2)⟩

private theorem r1gen_card_le_two_of_isCyclic {G : Type} [Group G] {V : Subgroup G}
    (hV2 : CFSG.Open.IsElemAbelian 2 V) (hcyc : IsCyclic V) : Nat.card V ≤ 2 := by
  have hexp : Monoid.exponent V ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hV2.2 x x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

private theorem r1gen_eq_one_of_sq_eq_one {G : Type} [Group G] {C : Subgroup G}
    (hC : Odd (Nat.card C)) {k : G} (hk : k ∈ C) (hk2 : k ^ 2 = 1) : k = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (even_iff_two_dvd.mpr (h ▸ C.orderOf_dvd_natCard hk))
      (Nat.not_even_iff_odd.mpr hC)

private theorem r1gen_conj_injective {K : Type} [Group K] (hKZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  refine (injective_iff_map_eq_one _).mpr fun k hk => ?_
  have hkZ : k ∈ center K := mem_center_iff.mpr fun g => by
    have h := DFunLike.congr_fun hk g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * k = k * g * k⁻¹ * k := by rw [h]
      _ = k * g := by group
  rwa [hKZ, mem_bot] at hkZ

private theorem r1gen_mem_centralizer_of_conj {Y : Type} [Group Y] {K : Subgroup Y} {e : Y}
    (heK : e ∈ K) {k : K} (hk : MulAut.conj k (⟨e, heK⟩ : K) = ⟨e, heK⟩) :
    k ∈ centralizer ({(⟨e, heK⟩ : K)} : Set K) := by
  rw [mem_centralizer_iff]
  rintro h rfl
  rw [MulAut.conj_apply] at hk
  calc (⟨e, heK⟩ : K) * k = k * ⟨e, heK⟩ * k⁻¹ * k := by rw [hk]
    _ = k * ⟨e, heK⟩ := by group

private def r1gen_rho {Y : Type} [Group Y] {K V : Subgroup Y}
    (hVN : V ≤ normalizer (K : Set Y)) : V →* MulAut K :=
  K.normalizerMonoidHom.comp (inclusion hVN)

private theorem r1gen_rho_coe {Y : Type} [Group Y] {K V : Subgroup Y}
    (hVN : V ≤ normalizer (K : Set Y)) (v : V) (k : K) :
    ((r1gen_rho hVN v k : K) : Y) = (v : Y) * k * (v : Y)⁻¹ :=
  rfl

private theorem r1gen_rho_injective {Y : Type} [Group Y] {K V : Subgroup Y}
    (hVN : V ≤ normalizer (K : Set Y)) (hVf : V ⊓ centralizer (K : Set Y) = ⊥) :
    Function.Injective (r1gen_rho hVN) := by
  refine (injective_iff_map_eq_one _).mpr fun v hv => ?_
  have hvC : (v : Y) ∈ V ⊓ centralizer (K : Set Y) := by
    refine ⟨v.2, mem_centralizer_iff.mpr fun k hk => ?_⟩
    have h : (v : Y) * k * (v : Y)⁻¹ = k := by
      have h := congrArg Subtype.val (DFunLike.congr_fun hv (⟨k, hk⟩ : K))
      rw [r1gen_rho_coe, MulAut.one_apply] at h
      exact h
    calc k * v = (v : Y) * k * (v : Y)⁻¹ * v := by rw [h]
      _ = v * k := by group
  rw [hVf, mem_bot] at hvC
  exact Subtype.ext hvC

private theorem r1gen_rho_fix {Y : Type} [Group Y] {K V : Subgroup Y} {e : Y} (heK : e ∈ K)
    (hVN : V ≤ normalizer (K : Set Y)) (hVe : V ≤ centralizer ({e} : Set Y)) (v : V) :
    r1gen_rho hVN v ⟨e, heK⟩ = ⟨e, heK⟩ := by
  apply Subtype.ext
  rw [r1gen_rho_coe, ← mem_centralizer_iff.mp (hVe v.2) e rfl, mul_inv_cancel_right]

private theorem r1gen_rho_sq {Y : Type} [Group Y] {K V : Subgroup Y}
    (hV2 : CFSG.Open.IsElemAbelian 2 V) (hVN : V ≤ normalizer (K : Set Y)) (v : V) :
    r1gen_rho hVN v ^ 2 = 1 := by
  rw [← map_pow, show v ^ 2 = 1 from Subtype.ext (by simpa using hV2.2 v v.2), map_one]

theorem card_le_two_of_odd_centralizer {Y : Type} [Group Y] [Finite Y] {K V : Subgroup Y} {e : Y}
    (hKZ : Subgroup.center ↥K = ⊥) (heK : e ∈ K) (hV2 : CFSG.Open.IsElemAbelian 2 V)
    (hVN : V ≤ normalizer (K : Set Y)) (hVf : V ⊓ centralizer (K : Set Y) = ⊥)
    (hVe : V ≤ centralizer ({e} : Set Y))
    (hodd : Odd (Nat.card (centralizer ({(⟨e, heK⟩ : ↥K)} : Set ↥K))))
    (hOut : ∀ W : Subgroup (MulAut ↥K), IsPGroup 2 W →
      W ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range = ⊥ → IsCyclic W) :
    Nat.card V ≤ 2 := by
  have hW2 : IsPGroup 2 (r1gen_rho hVN).range := (r1gen_isPGroup hV2).of_surjective
    (r1gen_rho hVN).rangeRestrict (r1gen_rho hVN).rangeRestrict_surjective
  have hWI : (r1gen_rho hVN).range ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨v, rfl⟩, ⟨k, hk⟩⟩
    have hkC := r1gen_mem_centralizer_of_conj heK (k := k)
      (by rw [hk]; exact r1gen_rho_fix heK hVN hVe v)
    have hk2 : k ^ 2 = 1 := r1gen_conj_injective hKZ
      (by rw [map_pow, hk, map_one]; exact r1gen_rho_sq hV2 hVN v)
    rw [mem_bot, ← hk, r1gen_eq_one_of_sq_eq_one hodd hkC hk2, map_one]
  have := hOut _ hW2 hWI
  exact r1gen_card_le_two_of_isCyclic hV2 (isCyclic_of_injective (r1gen_rho hVN).rangeRestrict
    (MonoidHom.rangeRestrict_injective_iff.mpr (r1gen_rho_injective hVN hVf)))

theorem card_le_two_of_isCyclic_sylow_centralizer {Y : Type} [Group Y] [Finite Y]
    {K V : Subgroup Y} {e : Y} (hKZ : Subgroup.center ↥K = ⊥) (heK : e ∈ K)
    (hV2 : CFSG.Open.IsElemAbelian 2 V) (hVN : V ≤ normalizer (K : Set Y))
    (hVf : V ⊓ centralizer (K : Set Y) = ⊥) (hVe : V ≤ centralizer ({e} : Set Y))
    (hinn : ∀ α : MulAut ↥K, (∃ k : ℕ, α ^ 2 ^ k = 1) →
      α ∈ (MulAut.conj : ↥K →* MulAut ↥K).range)
    (hcyc : ∀ P : Subgroup ↥K, P ≤ centralizer ({(⟨e, heK⟩ : ↥K)} : Set ↥K) → IsPGroup 2 P →
      IsCyclic P) :
    Nat.card V ≤ 2 := by
  have hc := r1gen_conj_injective hKZ
  have hρc : ∀ v, r1gen_rho hVN v ∈ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    fun v => hinn _ ⟨1, by rw [pow_one]; exact r1gen_rho_sq hV2 hVN v⟩
  let φ : V →* K :=
    (MonoidHom.ofInjective hc).symm.toMonoidHom.comp ((r1gen_rho hVN).codRestrict _ hρc)
  have hφ : ∀ v, MulAut.conj (φ v) = r1gen_rho hVN v := fun v =>
    MonoidHom.apply_ofInjective_symm hc _
  have hφinj : Function.Injective φ := fun a b hab =>
    r1gen_rho_injective hVN hVf (by rw [← hφ, ← hφ, hab])
  have hP : φ.range ≤ centralizer ({(⟨e, heK⟩ : ↥K)} : Set ↥K) := by
    rintro _ ⟨v, rfl⟩
    exact r1gen_mem_centralizer_of_conj heK (by rw [hφ]; exact r1gen_rho_fix heK hVN hVe v)
  have := hcyc _ hP
    ((r1gen_isPGroup hV2).of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
  exact r1gen_card_le_two_of_isCyclic hV2 (isCyclic_of_injective φ.rangeRestrict
    (MonoidHom.rangeRestrict_injective_iff.mpr hφinj))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
