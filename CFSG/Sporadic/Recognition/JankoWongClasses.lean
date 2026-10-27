module

public import CFSG.Sporadic.Recognition.JankoWongCover

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup

theorem cycleType_cube_aux {σ : Perm (Fin 8)} (h3 : σ ^ 3 = 1) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 ∧
      σ.support.card = 3 * Multiset.card σ.cycleType := by
  have hall : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have hd := dvd_of_mem_cycleType hn
    have hd3 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h1 := (Nat.dvd_prime Nat.prime_three).mp (hd.trans hd3)
    have := two_le_of_mem_cycleType hn
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  refine ⟨hrep, ?_⟩
  rw [← sum_cycleType]
  conv_lhs => rw [hrep]
  rw [Multiset.sum_replicate]; simp [mul_comm]

theorem cycleType_of_cube_eq_one {σ : Perm (Fin 8)} (h3 : σ ^ 3 = 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 3) 3 := by
  obtain ⟨hrep, hsum⟩ := cycleType_cube_aux h3
  rw [hsum, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  exact hrep

theorem cycleType_type3_of_card {σ : Perm (Fin 8)} (h3 : σ ^ 3 = 1)
    (hs : (Finset.univ.filter fun i => σ i ≠ i).card = 3) : σ.cycleType = {3} := by
  rw [cycleType_of_cube_eq_one h3]
  have : σ.support.card = 3 := hs
  rw [this]; rfl

theorem cycleType_type33_of_card {σ : Perm (Fin 8)} (h3 : σ ^ 3 = 1)
    (hs : (Finset.univ.filter fun i => σ i ≠ i).card = 6) : σ.cycleType = {3, 3} := by
  rw [cycleType_of_cube_eq_one h3]
  have : σ.support.card = 6 := hs
  rw [this]; rfl

theorem cycleType_of_cube_eq_one_ne_one {σ : Perm (Fin 8)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  obtain ⟨hrep, hsum⟩ := cycleType_cube_aux h3
  have hle : σ.support.card ≤ 8 := by
    have := Finset.card_le_univ σ.support
    simpa using this
  have hne : Multiset.card σ.cycleType ≠ 0 := fun h => h1 (cycleType_eq_zero.mp
    (Multiset.card_eq_zero.mp h))
  have h2 : Multiset.card σ.cycleType = 1 ∨ Multiset.card σ.cycleType = 2 := by omega
  rcases h2 with h2 | h2
  · left; rw [hrep, h2]; rfl
  · right; rw [hrep, h2]; rfl

namespace IsCover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem eq_of_cube_one (h : IsCover8 ρ z) {y y' : E} (hy : y ^ 3 = 1) (hy' : y' ^ 3 = 1)
    (hρ : ρ y = ρ y') : y = y' := by
  rcases h.eq_or_eq_mul_z hρ with h1 | h1
  · exact h1.symm
  · exfalso
    rw [h1, Commute.mul_pow (h.mul_z_comm y), hy] at hy'
    have : z ^ 3 = z := by rw [pow_succ, h.sq_eq_one, one_mul]
    rw [this, one_mul] at hy'
    exact h.ne_one hy'

end IsCover8


theorem card_alt_type3 : (Finset.univ.filter fun g : alternatingGroup (Fin 8) =>
    (g : Perm (Fin 8)).cycleType = {3}).card = 112 := by
  have := AlternatingGroup.card_of_cycleType (Fin 8) ({3} : Multiset ℕ)
  simp only [Fintype.card_fin] at this
  norm_num [Nat.factorial] at this
  exact this

theorem card_alt_type33 : (Finset.univ.filter fun g : alternatingGroup (Fin 8) =>
    (g : Perm (Fin 8)).cycleType = {3, 3}).card = 1120 := by
  have := AlternatingGroup.card_of_cycleType (Fin 8) ({3, 3} : Multiset ℕ)
  simp only [Fintype.card_fin] at this
  norm_num [Nat.factorial] at this
  exact this

theorem card_alt_type2222 : (Finset.univ.filter fun g : alternatingGroup (Fin 8) =>
    (g : Perm (Fin 8)).cycleType = {2, 2, 2, 2}).card = 105 := by
  have := AlternatingGroup.card_of_cycleType (Fin 8) ({2, 2, 2, 2} : Multiset ℕ)
  simp only [Fintype.card_fin] at this
  norm_num [Nat.factorial] at this
  exact this

theorem card_alt_type22 : (Finset.univ.filter fun g : alternatingGroup (Fin 8) =>
    (g : Perm (Fin 8)).cycleType = {2, 2}).card = 210 := by
  have := AlternatingGroup.card_of_cycleType (Fin 8) ({2, 2} : Multiset ℕ)
  simp only [Fintype.card_fin] at this
  norm_num [Nat.factorial] at this
  exact this

theorem card_centralizer_mul_ncard_orbit {E : Type*} [Group E] [Finite E] (y : E) :
    Nat.card (centralizer ({y} : Set E)) * (MulAction.orbit (ConjAct E) y).ncard =
      Nat.card E := by
  rw [← index_centralizer_eq_ncard]; exact Subgroup.card_mul_index _

namespace IsCover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem orbit_eq_cube_class (h : IsCover8 ρ z) {x : E} (hx : x ^ 3 = 1)
    (hsupp : (ρ x).support.card + 2 ≤ 8) :
    MulAction.orbit (ConjAct E) x = {y | y ^ 3 = 1 ∧ (ρ y).cycleType = (ρ x).cycleType} := by
  ext y
  rw [ConjAct.mem_orbit_conjAct]
  constructor
  · intro hc
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    have hy : y = c⁻¹ * x * c := by rw [← hc]; group
    refine ⟨?_, ?_⟩
    · have : y ^ 3 = c⁻¹ * x ^ 3 * c := by
        rw [hy]; simp [pow_succ, mul_assoc]
      rw [this, hx]; simp
    · rw [hy, map_mul, map_mul, map_inv]
      have := cycleType_conj (σ := ρ x) (τ := (ρ c)⁻¹)
      simpa using this
  · rintro ⟨hy3, hty⟩
    have hconj : IsConj (ρ y) (ρ x) := isConj_iff_cycleType_eq.mpr hty
    have hsy : (ρ y).support.card + 2 ≤ Fintype.card (Fin 8) := by
      rw [← sum_cycleType, hty, sum_cycleType]; simpa using hsupp
    obtain ⟨c, hc⟩ := isConj_iff.mp (alternatingGroup.isConj_of
      (σ := ⟨ρ y, (mem_alternatingGroup).mpr (h.sign_rho y)⟩)
      (τ := ⟨ρ x, (mem_alternatingGroup).mpr (h.sign_rho x)⟩) hconj hsy)
    obtain ⟨c', hc'⟩ := h.exists_lift ((mem_alternatingGroup).mp c.2)
    have h1 : ρ (c' * y * c'⁻¹) = ρ x := by
      rw [map_mul, map_mul, map_inv, hc']
      have := congrArg Subtype.val hc
      simpa using this
    have h2 : (c' * y * c'⁻¹) ^ 3 = 1 := by
      have : (c' * y * c'⁻¹) ^ 3 = c' * y ^ 3 * c'⁻¹ := by simp [pow_succ, mul_assoc]
      rw [this, hy3]; simp
    exact isConj_iff.mpr ⟨c', h.eq_of_cube_one h2 hx h1⟩


theorem orderOf_z (h : IsCover8 ρ z) : orderOf z = 2 :=
  orderOf_eq_prime h.sq_eq_one h.ne_one

theorem nat_card_ker (h : IsCover8 ρ z) : Nat.card ρ.ker = 2 := by
  rw [h.ker_eq, Nat.card_zpowers, h.orderOf_z]

theorem nat_card_eq (h : IsCover8 ρ z) [Finite E] : Nat.card E = 40320 := by
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker, h.nat_card_ker, h.range_eq] at h1
  rw [← h1, nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem ncard_cube_class (h : IsCover8 ρ z) (m : Multiset ℕ) (hm3 : ∀ n ∈ m, n = 3) :
    {y : E | y ^ 3 = 1 ∧ (ρ y).cycleType = m}.ncard =
      (Finset.univ.filter fun g : alternatingGroup (Fin 8) =>
        (g : Perm (Fin 8)).cycleType = m).card := by
  classical
  rw [← Nat.card_coe_set_eq]
  have hcube : ∀ g : alternatingGroup (Fin 8), (g : Perm (Fin 8)).cycleType = m →
      (g : Perm (Fin 8)) ^ 3 = 1 := by
    intro g hg
    rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType, hg]
    exact Multiset.lcm_dvd.mpr fun n hn => (hm3 n hn).symm ▸ dvd_rfl
  have hbij : Nat.card ↥{y : E | y ^ 3 = 1 ∧ (ρ y).cycleType = m} =
      Nat.card {g : alternatingGroup (Fin 8) // (g : Perm (Fin 8)).cycleType = m} := by
    refine Nat.card_eq_of_bijective
      (fun y => ⟨⟨ρ y.1, (mem_alternatingGroup).mpr (h.sign_rho y.1)⟩, y.2.2⟩) ⟨?_, ?_⟩
    · intro y y' hyy'
      apply Subtype.ext
      apply h.eq_of_cube_one y.2.1 y'.2.1
      have := congrArg (fun g => (g.1 : Perm (Fin 8))) hyy'
      simpa using this
    · rintro ⟨g, hg⟩
      obtain ⟨c, hc, hc3⟩ := h.exists_lift_cube_one ((mem_alternatingGroup).mp g.2) (hcube g hg)
      refine ⟨⟨c, hc3, by rw [hc]; exact hg⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa using hc
  rw [hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_centralizer_mul_of_cube (h : IsCover8 ρ z) [Finite E] {x : E} (hx : x ^ 3 = 1)
    (hsupp : (ρ x).support.card + 2 ≤ 8) (hm3 : ∀ n ∈ (ρ x).cycleType, n = 3) :
    Nat.card (centralizer ({x} : Set E)) *
      (Finset.univ.filter fun g : alternatingGroup (Fin 8) =>
        (g : Perm (Fin 8)).cycleType = (ρ x).cycleType).card = 40320 := by
  have h1 := card_centralizer_mul_ncard_orbit x
  rw [h.orbit_eq_cube_class hx hsupp, h.ncard_cube_class _ hm3, h.nat_card_eq] at h1
  exact h1


theorem card_centralizer_type3 (h : IsCover8 ρ z) [Finite E] {x : E} (hx : x ^ 3 = 1)
    (ht : (ρ x).cycleType = {3}) : Nat.card (centralizer ({x} : Set E)) = 360 := by
  have hsupp : (ρ x).support.card + 2 ≤ 8 := by
    rw [← sum_cycleType, ht]; simp
  have := h.card_centralizer_mul_of_cube hx hsupp (by rw [ht]; simp)
  rw [ht, card_alt_type3] at this
  omega

theorem card_centralizer_type33 (h : IsCover8 ρ z) [Finite E] {x : E} (hx : x ^ 3 = 1)
    (ht : (ρ x).cycleType = {3, 3}) : Nat.card (centralizer ({x} : Set E)) = 36 := by
  have hsupp : (ρ x).support.card + 2 ≤ 8 := by
    rw [← sum_cycleType, ht]; simp
  have := h.card_centralizer_mul_of_cube hx hsupp (by rw [ht]; simp)
  rw [ht, card_alt_type33] at this
  omega

theorem commute_of_cube (h : IsCover8 ρ z) {x g : E} (hx : x ^ 3 = 1)
    (hg : ρ g * ρ x = ρ x * ρ g) : g * x = x * g := by
  have h1 : ρ (g * x * g⁻¹) = ρ x := by
    rw [map_mul, map_mul, map_inv, hg]; group
  have h2 : (g * x * g⁻¹) ^ 3 = 1 := by
    have : (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ := by simp [pow_succ, mul_assoc]
    rw [this, hx]; simp
  have h3 := h.eq_of_cube_one h2 hx h1
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h3]

end IsCover8

theorem even_card_support_of_commute {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Perm α}
    (hτ2 : τ ^ 2 = 1) (hfpf : ∀ a, τ a ≠ a) (hcomm : τ * σ = σ * τ) :
    Even σ.support.card := by
  have hτinv : ∀ a, τ (τ a) = a := by
    intro a
    have := congrArg (fun p : Perm α => p a) hτ2
    simpa [pow_two] using this
  have hmem : ∀ a, a ∈ σ.support ↔ τ a ∈ σ.support := by
    have key : ∀ a, a ∈ σ.support → τ a ∈ σ.support := by
      intro a ha
      rw [mem_support] at ha ⊢
      intro h1
      apply ha
      have h2 : τ (σ a) = σ (τ a) := by
        have := congrArg (fun p : Perm α => p a) hcomm
        simpa using this
      rw [h1] at h2
      exact τ.injective h2
    intro a
    exact ⟨key a, fun h => by simpa [hτinv] using key _ h⟩
  let f : Function.End ↥σ.support := fun a => ⟨τ a.1, (hmem a.1).mp a.2⟩
  have hf2 : f ^ 2 ^ 1 = 1 := by
    funext a
    apply Subtype.ext
    simp only [pow_one, pow_two]
    exact hτinv a.1
  have hfix : Function.fixedPoints f = ∅ := by
    ext a
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ha
    apply hfpf a.1
    exact congrArg Subtype.val ha
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf2
  have : IsEmpty ↑(Function.fixedPoints f) := Set.isEmpty_coe_sort.mpr hfix
  have hz0 : Fintype.card ↑(Function.fixedPoints f) = 0 := Fintype.card_eq_zero
  rw [hz0] at hmod
  rw [Fintype.card_coe] at hmod
  exact Nat.even_iff.mpr hmod




theorem sign_of_type33 {σ : Perm (Fin 8)} (h : σ.cycleType = {3, 3}) : sign σ = 1 := by
  rw [sign_of_cycleType, h]; decide

theorem sign_of_type3 {σ : Perm (Fin 8)} (h : σ.cycleType = {3}) : sign σ = 1 := by
  rw [sign_of_cycleType, h]; decide

theorem fpf_of_type2222 {σ : Perm (Fin 8)} (h : σ.cycleType = {2, 2, 2, 2}) : ∀ a, σ a ≠ a := by
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← sum_cycleType, h]; simp
  intro a
  have : a ∈ σ.support := by rw [hsupp]; exact Finset.mem_univ _
  exact mem_support.mp this

theorem exists_even_conj_of_support {σ τ : Perm (Fin 8)} (hc : IsConj σ τ)
    (hs : σ.support.card + 2 ≤ 8) (hσ : sign σ = 1) (hτ : sign τ = 1) :
    ∃ g : Perm (Fin 8), sign g = 1 ∧ g * σ * g⁻¹ = τ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (alternatingGroup.isConj_of
    (σ := ⟨σ, (mem_alternatingGroup).mpr hσ⟩) (τ := ⟨τ, (mem_alternatingGroup).mpr hτ⟩) hc
    (by simpa using hs))
  refine ⟨c, (mem_alternatingGroup).mp c.2, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

private def permS33 : Perm (Fin 8) := (swap 0 1 * swap 1 2) * (swap 3 4 * swap 4 5)
private def permT33 : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7

private theorem cycleType_permS33 : permS33.cycleType = {3, 3} := by
  unfold permS33
  exact cycleType_type33_of_card (by decide) (by decide)

private theorem cycleType_permT33 : permT33.cycleType = {2, 2, 2, 2} := by
  unfold permT33
  exact cycleType_type2222_of_card (by decide) (by decide)

private theorem commute_permT33_S33 : permT33 * permS33 = permS33 * permT33 := by
  unfold permT33 permS33; decide

namespace IsCover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem eq_z_of_involution_centralizer_type3 (h : IsCover8 ρ z) {x y : E}
    (ht : (ρ x).cycleType = {3}) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hc : y * x = x * y) :
    y = z := by
  by_contra hyz
  have hty := h.type2222_of_involution hy2 hy1 hyz
  have hρ2 : ρ y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hcomm : ρ y * ρ x = ρ x * ρ y := by rw [← map_mul, ← map_mul, hc]
  have := even_card_support_of_commute hρ2 (fpf_of_type2222 hty) hcomm
  rw [← sum_cycleType, ht] at this
  simp at this
  exact absurd this (by decide)

theorem exists_involution_centralizer_type33 (h : IsCover8 ρ z) {x : E} (hx : x ^ 3 = 1)
    (ht : (ρ x).cycleType = {3, 3}) :
    ∃ t : E, t ^ 2 = 1 ∧ t ≠ 1 ∧ t ≠ z ∧ t * x = x * t := by
  have hsupp : permS33.support.card + 2 ≤ 8 := by
    rw [← sum_cycleType, cycleType_permS33]; simp
  obtain ⟨g, hg, hgc⟩ := exists_even_conj_of_support
    (isConj_iff_cycleType_eq.mpr (cycleType_permS33.trans ht.symm)) hsupp
    (sign_of_type33 cycleType_permS33) (h.sign_rho x)
  obtain ⟨t, ht'⟩ := h.exists_lift (p := g * permT33 * g⁻¹) (by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, sign_inv, hg, sign_of_type2222 cycleType_permT33]
    simp)
  have htype : (ρ t).cycleType = {2, 2, 2, 2} := by
    rw [ht', cycleType_conj]; exact cycleType_permT33
  obtain ⟨h2, h1, hz⟩ := h.isInvolution_of_type2222 htype
  refine ⟨t, h2, h1, hz, h.commute_of_cube hx ?_⟩
  rw [ht', ← hgc]
  calc g * permT33 * g⁻¹ * (g * permS33 * g⁻¹) = g * (permT33 * permS33) * g⁻¹ := by group
    _ = g * (permS33 * permT33) * g⁻¹ := by rw [commute_permT33_S33]
    _ = g * permS33 * g⁻¹ * (g * permT33 * g⁻¹) := by group

end IsCover8

end CFSG.Sporadic.Recognition.JankoWong
