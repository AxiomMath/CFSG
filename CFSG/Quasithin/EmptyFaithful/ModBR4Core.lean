module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.ModB


section Tv

variable {W : Type*} [CommGroup W]

@[expose] def IsTvOf (z : W) (s : MulAut W) : Prop := ∀ w : W, s w = w ∨ s w = w * z

theorem IsTvOf.fix_center {z : W} (hz1 : z ≠ 1) (hz2 : z * z = 1) {s : MulAut W} (h : IsTvOf z s) :
    s z = z := by
  rcases h z with h | h
  · exact h
  · exfalso
    apply hz1
    have : s z = s 1 := by rw [h, hz2, map_one]
    exact s.injective this

theorem IsTvOf.mul_self {z : W} (hz1 : z ≠ 1) (hz2 : z * z = 1) {s : MulAut W} (h : IsTvOf z s) :
    s * s = 1 := by
  ext w
  have hsz := h.fix_center hz1 hz2
  rcases h w with hw | hw
  · show s (s w) = w
    rw [hw, hw]
  · show s (s w) = w
    rw [hw, map_mul, hsz, hw, mul_assoc, hz2, mul_one]

theorem IsTvOf.conj {z : W} {s : MulAut W} (h : IsTvOf z s) (g : MulAut W) :
    IsTvOf (g z) (g * s * g⁻¹) := by
  intro w
  have e : (g * s * g⁻¹) w = g (s (g⁻¹ w)) := rfl
  have e2 : g (g⁻¹ w) = w := by
    show (g * g⁻¹) w = w
    rw [mul_inv_cancel]
    rfl
  rcases h (g⁻¹ w) with h1 | h1
  · left
    rw [e, h1, e2]
  · right
    rw [e, h1, map_mul, e2]


theorem IsTvOf.mul_eq_one_of_pow_five [Finite W] (hcard : Nat.card W = 2 ^ 4) {z z' : W}
    {s s' : MulAut W} (hs : IsTvOf z s) (hs' : IsTvOf z' s') (h5 : (s * s') ^ 5 = 1) :
    s * s' = 1 := by
  classical
  set g : MulAut W := s * s' with hg
  let δ : W →* W := MonoidHom.mk' (fun w => g w * w⁻¹) (fun a b => by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hδ : ∀ w, δ w ∈ ({1, z, z', z' * z} : Finset W) := by
    intro w
    have hgw : g w = s (s' w) := rfl
    have e : δ w = g w * w⁻¹ := rfl
    rw [e, hgw]
    rcases hs' w with h1 | h1 <;> rcases hs (s' w) with h2 | h2
    · rw [h2, h1]; simp
    · rw [h2, h1]; simp
    · rw [h2, h1]; simp
    · rw [h2, h1]; simp [mul_comm, mul_assoc]
  have hsub : (δ.range : Set W) ⊆ ↑({1, z, z', z' * z} : Finset W) := by
    rintro _ ⟨w, rfl⟩
    exact_mod_cast hδ w
  have hr : Nat.card δ.range ≤ 4 := by
    have h1 : Nat.card δ.range = (δ.range : Set W).ncard := Nat.card_coe_set_eq _
    rw [h1]
    calc (δ.range : Set W).ncard ≤ (↑({1, z, z', z' * z} : Finset W) : Set W).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({1, z, z', z' * z} : Finset W).card := Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers g) := by
    intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]
  have hfix : MulAction.fixedPoints (Subgroup.zpowers g) W = (δ.ker : Set W) := by
    ext w
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, MonoidHom.mem_ker]
    constructor
    · intro hw
      have h1 : g w = w := hw ⟨g, Subgroup.mem_zpowers g⟩
      show g w * w⁻¹ = 1
      rw [h1, mul_inv_cancel]
    · intro hw h
      have h1 : g w = w := by
        have : g w * w⁻¹ = 1 := hw
        exact mul_inv_eq_one.mp this
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h.2
      show (h : MulAut W) w = w
      rw [← hm]
      have hn : ∀ n : ℕ, (g ^ n) w = w := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ]
          show (g ^ n) (g w) = w
          rw [h1, ih]
      have hinv : ∀ n : ℕ, (g ^ n)⁻¹ w = w := by
        intro n
        have := hn n
        calc (g ^ n)⁻¹ w = (g ^ n)⁻¹ ((g ^ n) w) := by rw [this]
          _ = w := by
            show ((g ^ n)⁻¹ * (g ^ n)) w = w
            rw [inv_mul_cancel]
            rfl
      rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast]; exact hn n
      · rw [zpow_neg, zpow_natCast]; exact hinv n
  have hmod := hP.card_modEq_card_fixedPoints W
  rw [hfix] at hmod
  have hk := Subgroup.card_ker_mul_card_range δ
  have hpos : 0 < Nat.card δ.range := Nat.card_pos
  rw [hcard] at hmod hk
  have hker : Nat.card δ.ker = Nat.card (↥(δ.ker : Set W)) := rfl
  rw [← hker] at hmod
  have hr1 : Nat.card δ.range = 1 := by
    unfold Nat.ModEq at hmod
    generalize Nat.card δ.range = r at hr hpos hk ⊢
    generalize Nat.card δ.ker = f at hk hmod
    interval_cases r <;> omega
  have hbot : δ.range = ⊥ := Subgroup.eq_bot_of_card_eq _ hr1
  ext w
  have : δ w = 1 := by
    have hw : δ w ∈ δ.range := ⟨w, rfl⟩
    rw [hbot] at hw
    exact hw
  have h2 : g w * w⁻¹ = 1 := this
  exact mul_inv_eq_one.mp h2

end Tv



section Alt

open Equiv Equiv.Perm

theorem cycleType_involution {n : ℕ} (hn : n ≤ 7) {g : Perm (Fin n)} (hg1 : g ≠ 1) (hg2 : g * g = 1)
    (hs : g ∈ alternatingGroup (Fin n)) : g.cycleType = Multiset.replicate 2 2 := by
  have h2 : ∀ k ∈ g.cycleType, k = 2 := by
    intro k hk
    have hdvd : k ∣ orderOf g := Equiv.Perm.dvd_of_mem_cycleType hk
    have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    have hk2 : 2 ≤ k := Equiv.Perm.two_le_of_mem_cycleType hk
    have := Nat.le_of_dvd (by norm_num) (hdvd.trans hord)
    omega
  have hsupp : g.support.card ≤ n := by simpa using g.support.card_le_univ
  rw [← Multiset.eq_replicate_card] at h2
  rw [← sum_cycleType, h2, Multiset.sum_replicate, smul_eq_mul] at hsupp
  have hcard : Multiset.card g.cycleType ≤ 3 := by omega
  rw [mem_alternatingGroup, sign_of_cycleType, h2, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul, pow_add, pow_mul, Int.units_pow_two, one_mul, neg_one_pow_eq_one_iff_even
      (by decide)] at hs
  interval_cases hk : Multiset.card g.cycleType
  · exact (hg1 (card_cycleType_eq_zero.1 hk)).elim
  · exact absurd hs (by decide)
  · exact h2
  · exact absurd hs (by decide)

theorem alt_involution_isConj {n : ℕ} (h6 : 6 ≤ n) (h7 : n ≤ 7) {a b : alternatingGroup (Fin n)}
    (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb1 : b ≠ 1) (hb2 : b * b = 1) : IsConj a b := by
  have hne : ∀ c : alternatingGroup (Fin n), c ≠ 1 → (c : Perm (Fin n)) ≠ 1 := fun c hc h =>
    hc (Subtype.ext h)
  have hsq : ∀ c : alternatingGroup (Fin n), c * c = 1 → (c : Perm (Fin n)) * c = 1 := fun c h => by
    simpa using congrArg Subtype.val h
  have hca := cycleType_involution h7 (hne a ha1) (hsq a ha2) a.2
  have hcb := cycleType_involution h7 (hne b hb1) (hsq b hb2) b.2
  have hc : IsConj (a : Perm (Fin n)) (b : Perm (Fin n)) :=
    isConj_iff_cycleType_eq.2 (hca.trans hcb.symm)
  refine alternatingGroup.isConj_of hc ?_
  have : (a : Perm (Fin n)).support.card = 4 := by
    rw [← sum_cycleType, hca]
    simp
  rw [this, Fintype.card_fin]
  omega

theorem alt6_pair : ∃ r r' : alternatingGroup (Fin 6), r ≠ 1 ∧ r * r = 1 ∧ r' ≠ 1 ∧ r' * r' = 1 ∧
    (r * r') ^ 5 = 1 ∧ r * r' ≠ 1 := by
  refine ⟨⟨swap 1 4 * swap 2 3, ?_⟩, ⟨swap 0 2 * swap 3 4, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup]; decide
  · rw [mem_alternatingGroup]; decide
  · decide +kernel

theorem alt7_pair : ∃ r r' : alternatingGroup (Fin 7), r ≠ 1 ∧ r * r = 1 ∧ r' ≠ 1 ∧ r' * r' = 1 ∧
    (r * r') ^ 5 = 1 ∧ r * r' ≠ 1 := by
  refine ⟨⟨swap 1 4 * swap 2 3, ?_⟩, ⟨swap 0 2 * swap 3 4, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup]; decide
  · rw [mem_alternatingGroup]; decide
  · decide +kernel


end Alt

section NoTv

variable {W : Type} [CommGroup W] [Finite W]

open Equiv.Perm in
theorem IsTvOf.eq_one_of_mem (hcard : Nat.card W = 2 ^ 4) {z : W} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    {A : Type*} [Group A] (Kb : Subgroup (MulAut W)) (e : Kb ≃* A)
    (hconj : ∀ a b : A, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → IsConj a b)
    (hpair : ∃ r r' : A, r ≠ 1 ∧ r * r = 1 ∧ r' ≠ 1 ∧ r' * r' = 1 ∧ (r * r') ^ 5 = 1 ∧ r * r' ≠ 1)
    {s : MulAut W} (hsK : s ∈ Kb) (hs : IsTvOf z s) : s = 1 := by
  by_contra hs1
  obtain ⟨r, r', hr1, hr2, hr1', hr2', hr5, hrr⟩ := hpair
  set σ : Kb := ⟨s, hsK⟩ with hσ
  have hσ1 : σ ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hσ2 : σ * σ = 1 := Subtype.ext (hs.mul_self hz1 hz2)
  have heσ1 : e σ ≠ 1 := fun h => hσ1 (e.injective (by rw [h, map_one]))
  have heσ2 : e σ * e σ = 1 := by rw [← map_mul, hσ2, map_one]
  obtain ⟨c₁, hc₁⟩ := isConj_iff.mp (hconj _ _ heσ1 heσ2 hr1 hr2)
  obtain ⟨c₂, hc₂⟩ := isConj_iff.mp (hconj _ _ heσ1 heσ2 hr1' hr2')
  have hk : ∀ (c t : A), c * e σ * c⁻¹ = t →
      ((e.symm t : Kb) : MulAut W) = ((e.symm c : Kb) : MulAut W) * s * ((e.symm c : Kb) : MulAut W)⁻¹ := by
    intro c t hct
    have : e.symm t = e.symm c * σ * (e.symm c)⁻¹ := by
      rw [← hct]
      simp
    rw [this]
    rfl
  have hT : (((e.symm r : Kb) : MulAut W) * ((e.symm r' : Kb) : MulAut W)) = 1 := by
    apply IsTvOf.mul_eq_one_of_pow_five hcard (z := (e.symm c₁ : Kb) • z) (z' := (e.symm c₂ : Kb) • z)
    · rw [hk c₁ r hc₁]
      exact hs.conj _
    · rw [hk c₂ r' hc₂]
      exact hs.conj _
    · have : (((e.symm r : Kb) : MulAut W) * ((e.symm r' : Kb) : MulAut W)) ^ 5 =
          ((e.symm ((r * r') ^ 5) : Kb) : MulAut W) := by
        rw [map_pow, map_mul]
        rfl
      rw [this, hr5, map_one]
      rfl
  apply hrr
  have : e.symm (r * r') = 1 := by
    apply Subtype.ext
    rw [map_mul]
    exact hT
  have := congrArg e this
  simpa using this

end NoTv

section Core

open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem tv_on_plane {X : Subgroup W} (hsq : ∀ w : W, w ^ 2 = 1) (hX : Nat.card X = 4) {z : W} (hz1 : z ≠ 1)
    (hzX : z ∈ X) {s : MulAut W} (hsz : s z = z) (hsX : ∀ x ∈ X, s x ∈ X) {x : W} (hx : x ∈ X) :
    s x = x ∨ s x = x * z := by
  classical
  have hz2 : z * z = 1 := by rw [← sq]; exact hsq z
  by_cases hx1 : x = 1
  · left; rw [hx1, map_one]
  by_cases hxz : x = z
  · left; rw [hxz, hsz]
  have hxz1 : x * z ≠ 1 := fun h => hxz (by
    have : x = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hz2))
  have hcov : ∀ y ∈ X, y = 1 ∨ y = z ∨ y = x ∨ y = x * z := by
    intro y hy
    by_contra hcon
    push Not at hcon
    obtain ⟨hy1, hyz, hyx, hyxz⟩ := hcon
    have hxz' : x * z ≠ z := fun h => hx1 (by simpa using h)
    have hxxz : x ≠ x * z := fun h => hz1 (by simpa using h)
    have h1z : (1 : W) ≠ z := hz1.symm
    have h1x : (1 : W) ≠ x := fun h => hx1 h.symm
    have h1xz : (1 : W) ≠ x * z := hxz1.symm
    have h1y : (1 : W) ≠ y := hy1.symm
    have hzx : z ≠ x := fun h => hxz h.symm
    have hzxz : z ≠ x * z := hxz'.symm
    have hzy : z ≠ y := hyz.symm
    have hxy : x ≠ y := hyx.symm
    have hxzy : x * z ≠ y := hyxz.symm
    have hF : ({1, z, x, x * z, y} : Finset W).card = 5 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton] <;>
      simp [h1z, h1x, h1xz, h1y, hzx, hzxz, hzy, hxxz, hxy, hxzy]
    have hsub : (↑({1, z, x, x * z, y} : Finset W) : Set W) ⊆ (X : Set W) := by
      intro t ht
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact X.one_mem
      · exact hzX
      · exact hx
      · exact X.mul_mem hx hzX
      · exact hy
    have h1 : (({1, z, x, x * z, y} : Finset W) : Set W).ncard ≤ (X : Set W).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hF, ← Nat.card_coe_set_eq (X : Set W)] at h1
    have : Nat.card (X : Set W) = 4 := hX
    omega
  rcases hcov (s x) (hsX x hx) with h | h | h | h
  · exfalso
    exact hx1 (s.injective (by rw [h, map_one]))
  · exfalso
    exact hxz (s.injective (by rw [h, hsz]))
  · left; exact h
  · right; exact h

open Equiv.Perm in
theorem rank4_core (hsq : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    (Kb S : Subgroup (MulAut W)) (hSK : S ≤ Kb)
    (hn : Nonempty (Kb ≃* alternatingGroup (Fin 6)) ∨ Nonempty (Kb ≃* alternatingGroup (Fin 7)))
    (hS : 7 ≤ Nat.card S) {z : W} (hz1 : z ≠ 1) (hSz : ∀ s ∈ S, s z = z)
    (𝒪 : Set (Subgroup W)) (h𝒪 : 𝒪.ncard ≤ 3)
    (hzX : ∀ X ∈ 𝒪, z ∈ X) (hX4 : ∀ X ∈ 𝒪, Nat.card X = 4)
    (hOS : ∀ s ∈ S, ∀ X ∈ 𝒪, s • X ∈ 𝒪) :
    Nat.card ↥(⨆ X ∈ 𝒪, X) ≤ 8 := by
  classical
  by_contra hlt
  push Not at hlt
  have hz2 : z * z = 1 := by rw [← sq]; exact hsq z
  have htop : (⨆ X ∈ 𝒪, X) = ⊤ := by
    have hdvd : Nat.card ↥(⨆ X ∈ 𝒪, X) ∣ Nat.card W := Subgroup.card_subgroup_dvd_card _
    rw [hcard] at hdvd
    have h16 : Nat.card ↥(⨆ X ∈ 𝒪, X) = 2 ^ 4 := by
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [hk']
      rw [hk'] at hlt
      have : k = 4 := by
        by_contra hne
        have : k ≤ 3 := by omega
        have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
        omega
      rw [this]
    exact Subgroup.eq_top_of_card_eq _ (by rw [h16, hcard])
  let act : MulAction ↥S ↥𝒪 :=
    { smul := fun s X => ⟨(s : MulAut W) • (X : Subgroup W), hOS s s.2 X X.2⟩
      one_smul := fun X => Subtype.ext (one_smul (MulAut W) (X : Subgroup W))
      mul_smul := fun a b X =>
        Subtype.ext (mul_smul (a : MulAut W) (b : MulAut W) (X : Subgroup W)) }
  have hfin : Finite ↥𝒪 := Set.toFinite 𝒪
  have hperm : Nat.card (Equiv.Perm ↥𝒪) ≤ 6 := by
    rw [Nat.card_perm]
    have h3 : Nat.card ↥𝒪 ≤ 3 := by rw [Nat.card_coe_set_eq]; exact h𝒪
    calc (Nat.card ↥𝒪).factorial ≤ (3 : ℕ).factorial := Nat.factorial_le h3
      _ = 6 := by decide
  have hnotinj : ¬ Function.Injective (MulAction.toPermHom ↥S ↥𝒪) := by
    intro hinj
    have := Nat.card_le_card_of_injective _ hinj
    omega
  obtain ⟨a, b, hmap, hab⟩ : ∃ a b : ↥S, MulAction.toPermHom ↥S ↥𝒪 a = MulAction.toPermHom ↥S ↥𝒪 b ∧
      a ≠ b := by
    unfold Function.Injective at hnotinj
    push Not at hnotinj
    obtain ⟨a, b, h1, h2⟩ := hnotinj
    exact ⟨a, b, h1, h2⟩
  obtain ⟨s, hsS, hs1, hsX⟩ : ∃ s ∈ S, s ≠ 1 ∧ ∀ X ∈ 𝒪, s • X = X := by
    refine ⟨((a⁻¹ * b : ↥S) : MulAut W), (a⁻¹ * b).2, ?_, ?_⟩
    · intro h
      apply hab
      have : a⁻¹ * b = 1 := Subtype.ext h
      exact inv_mul_eq_one.mp this
    · intro X hX
      have h1 : a • (⟨X, hX⟩ : ↥𝒪) = b • (⟨X, hX⟩ : ↥𝒪) := by
        have := congrArg (fun p : Equiv.Perm ↥𝒪 => p ⟨X, hX⟩) hmap
        simpa using this
      have h2 : (a⁻¹ * b) • (⟨X, hX⟩ : ↥𝒪) = ⟨X, hX⟩ := by
        rw [mul_smul, ← h1, inv_smul_smul]
      exact congrArg Subtype.val h2
  have hsz : s z = z := hSz s hsS
  have hTv : IsTvOf z s := by
    let δ : W →* W := MonoidHom.mk' (fun w => s w * w⁻¹) (fun a b => by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
    let R : Subgroup W := (Subgroup.zpowers z).comap δ
    have hX_le : ∀ X ∈ 𝒪, X ≤ R := by
      intro X hX x hx
      have hsx : ∀ y ∈ X, s y ∈ X := by
        intro y hy
        have h1 : s • X = X := hsX X hX
        rw [← h1]
        exact Subgroup.smul_mem_pointwise_smul y s X hy
      show δ x ∈ Subgroup.zpowers z
      have e : δ x = s x * x⁻¹ := rfl
      rw [e]
      rcases tv_on_plane hsq (hX4 X hX) hz1 (hzX X hX) hsz hsx hx with h | h
      · rw [h, mul_inv_cancel]; exact Subgroup.one_mem _
      · have : x * z * x⁻¹ = z := by rw [mul_comm x z, mul_assoc, mul_inv_cancel, mul_one]
        rw [h, this]; exact Subgroup.mem_zpowers z
    have hle : (⨆ X ∈ 𝒪, X) ≤ R := iSup₂_le hX_le
    rw [htop] at hle
    intro w
    have hw : δ w ∈ Subgroup.zpowers z := hle (Subgroup.mem_top w)
    have e : δ w = s w * w⁻¹ := rfl
    rw [e] at hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      have : z ^ (2 * m) = 1 := by rw [zpow_mul, zpow_ofNat, hsq z, one_zpow]
      rw [this] at hk
      exact mul_inv_eq_one.mp hk.symm
    · right
      have : z ^ (2 * m + 1) = z := by
        rw [zpow_add, zpow_mul, zpow_ofNat, hsq z, one_zpow, one_mul, zpow_one]
      rw [this] at hk
      rw [mul_comm]
      exact (mul_inv_eq_iff_eq_mul.mp hk.symm)
  rcases hn with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact hs1 (IsTvOf.eq_one_of_mem hcard hz1 hz2 Kb e
      (fun _ _ ha1 ha2 hb1 hb2 => alt_involution_isConj (n := 6) (by norm_num) (by norm_num) ha1 ha2 hb1 hb2)
      alt6_pair (hSK hsS) hTv)
  · exact hs1 (IsTvOf.eq_one_of_mem hcard hz1 hz2 Kb e
      (fun _ _ ha1 ha2 hb1 hb2 => alt_involution_isConj (n := 7) (by norm_num) (by norm_num) ha1 ha2 hb1 hb2)
      alt7_pair (hSK hsS) hTv)

end Core

end CFSG.Quasithin.ModB
