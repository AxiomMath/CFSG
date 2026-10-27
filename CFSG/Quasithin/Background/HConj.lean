module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem natAut_injective (Γ : Subgroup (GL ι K)) : Function.Injective (natAut Γ) :=
  fun _ _ h => Subtype.ext (matHom_injective h)

@[expose] noncomputable def natEquiv (Γ : Subgroup (GL ι K)) : ↥Γ ≃* ↥(natImage Γ) :=
  MonoidHom.ofInjective (natAut_injective Γ)

theorem coe_natEquiv (Γ : Subgroup (GL ι K)) (γ : ↥Γ) :
    ((natEquiv Γ γ : ↥(natImage Γ)) : MulAut (StdMod ι K)) = natAut Γ γ :=
  MonoidHom.ofInjective_apply _

@[expose] noncomputable def conjHom (Γ : Subgroup (GL ι K)) : ↥(natNorm Γ) →* MulAut ↥Γ :=
  (MulAut.congr (natEquiv Γ).symm).toMonoidHom.comp (natImage Γ).normalizerMonoidHom

theorem natAut_conjHom (Γ : Subgroup (GL ι K)) (g : ↥(natNorm Γ)) (γ : ↥Γ) :
    natAut Γ (conjHom Γ g γ) =
      (g : MulAut (StdMod ι K)) * natAut Γ γ * (g : MulAut (StdMod ι K))⁻¹ := by
  rw [← coe_natEquiv]
  change ((natEquiv Γ ((natEquiv Γ).symm ((natImage Γ).normalizerMonoidHom g
    ((natEquiv Γ).symm.symm γ))) : ↥(natImage Γ)) : MulAut (StdMod ι K)) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
  change (g : MulAut (StdMod ι K)) * ((natEquiv Γ γ : ↥(natImage Γ)) : MulAut (StdMod ι K)) *
    (g : MulAut (StdMod ι K))⁻¹ = _
  rw [coe_natEquiv]

theorem conjHom_natAut (Γ : Subgroup (GL ι K)) (s : ↥Γ) (hs : natAut Γ s ∈ natNorm Γ) :
    conjHom Γ ⟨natAut Γ s, hs⟩ = MulAut.conj s := by
  refine MulEquiv.ext fun γ => ?_
  apply natAut_injective Γ
  rw [natAut_conjHom, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem exists_smul_of_conjHom_eq {Γ : Subgroup (GL ι K)} (hΓ : HasScalarCommutant Γ)
    (g : ↥(natNorm Γ)) (s : ↥Γ) (h : conjHom Γ g = MulAut.conj s) :
    ∃ c : K, ∀ v, toAddMap (g : MulAut (StdMod ι K)) v =
      c • (((s : GL ι K) : Matrix ι ι K) *ᵥ v) := by
  set h' : MulAut (StdMod ι K) := (natAut Γ s)⁻¹ * g with hh'
  have hcomm : ∀ γ : ↥Γ, h' * natAut Γ γ = natAut Γ γ * h' := by
    intro γ
    have h1 := natAut_conjHom Γ g γ
    rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    rw [hh']
    have h2 : (g : MulAut (StdMod ι K)) * natAut Γ γ =
        natAut Γ s * natAut Γ γ * (natAut Γ s)⁻¹ * g := by
      rw [h1]; group
    calc (natAut Γ s)⁻¹ * (g : MulAut (StdMod ι K)) * natAut Γ γ
        = (natAut Γ s)⁻¹ * ((g : MulAut (StdMod ι K)) * natAut Γ γ) := by group
      _ = natAut Γ γ * ((natAut Γ s)⁻¹ * g) := by rw [h2]; group
  let F : (ι → K) →+ (ι → K) := AddMonoidHom.mk' (toAddMap h') (toAddMap_add h')
  obtain ⟨c, hc⟩ := hΓ F fun γ hγ v => by
    have := congrArg (fun y => toAddMap y v) (hcomm ⟨γ, hγ⟩)
    simp only [toAddMap_mul, toAddMap_natAut] at this
    exact this
  refine ⟨c, fun v => ?_⟩
  have hg : (g : MulAut (StdMod ι K)) = natAut Γ s * h' := by rw [hh']; group
  rw [hg, toAddMap_mul, toAddMap_natAut]
  have := hc v
  change toAddMap h' v = c • v at this
  rw [this, Matrix.mulVec_smul]

theorem mem_inner_of_pow_eq_one {G : Type*} [Group G] [Finite G] {x : MulAut G} {k : ℕ}
    (hx : x ^ k = 1) (hk : Nat.Coprime k (Nat.card (Outer G))) : x ∈ inner G := by
  have : Finite (MulAut G) := MulEquiv.finite_left
  let π : MulAut G →* Outer G := QuotientGroup.mk' (inner G)
  have h1 : orderOf (π x) ∣ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (π x) ∣ Nat.card (Outer G) := orderOf_dvd_natCard _
  have h3 : orderOf (π x) = 1 := Nat.eq_one_of_dvd_coprimes hk h1 h2
  have h4 : π x = 1 := orderOf_eq_one_iff.mp h3
  exact (QuotientGroup.eq_one_iff x).mp h4

@[expose] def fieldMap (σ : K ≃+* K) : MulAut (StdMod ι K) where
  toFun x := Multiplicative.ofAdd (fun i => σ (Multiplicative.toAdd x i))
  invFun x := Multiplicative.ofAdd (fun i => σ.symm (Multiplicative.toAdd x i))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Pi.add_apply, map_add]
    rfl

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_fieldMap (σ : K ≃+* K) (v : ι → K) :
    toAddMap (fieldMap (ι := ι) σ) v = fun i => σ (v i) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem toAddMap_fieldMap_inv (σ : K ≃+* K) (v : ι → K) :
    toAddMap (fieldMap (ι := ι) σ)⁻¹ v = fun i => σ.symm (v i) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem isSemilinear_fieldMap (σ : K ≃+* K) : IsSemilinear (fieldMap (ι := ι) σ) σ := by
  intro c v
  ext i
  simp [toAddMap_fieldMap]

theorem toAddMap_fieldMap_conj (σ : K ≃+* K) (A : GL ι K) (v : ι → K) :
    toAddMap (fieldMap σ * matAut A * (fieldMap σ)⁻¹) v =
      ((A : Matrix ι ι K).map σ) *ᵥ v := by
  rw [toAddMap_mul, toAddMap_mul, toAddMap_matAut, toAddMap_fieldMap, toAddMap_fieldMap_inv]
  ext i
  have := RingHom.map_mulVec (σ : K →+* K) (A : Matrix ι ι K) (fun j => σ.symm (v j)) i
  simp only [RingEquiv.coe_toRingHom] at this
  rw [this]
  congr 1
  ext j
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem fieldMap_symm (σ : K ≃+* K) : fieldMap (ι := ι) σ.symm = (fieldMap σ)⁻¹ :=
  toAddMap_injective fun _ => rfl

section Counting

theorem card_fix_diag_le [Finite K] {κ : Type} (d : κ → K) (hd : ∀ i j, d i = d j → i = j)
    (c : K) : Nat.card {w : κ → K // ∀ i, c * (d i * w i) = w i} ≤ Nat.card K := by
  by_cases h : ∃ i, c * d i = 1
  · obtain ⟨i₀, hi₀⟩ := h
    have hc : c ≠ 0 := by
      rintro rfl
      simp at hi₀
    have hz : ∀ w : {w : κ → K // ∀ i, c * (d i * w i) = w i}, ∀ j, j ≠ i₀ → w.1 j = 0 := by
      intro w j hj
      have h1 := w.2 j
      have h2 : c * d j ≠ 1 := by
        intro h3
        apply hj
        apply hd
        have := h3.trans hi₀.symm
        exact mul_left_cancel₀ hc this
      have h4 : (c * d j - 1) * w.1 j = 0 := by rw [sub_mul, one_mul, mul_assoc, h1, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr h2)
    refine Nat.card_le_card_of_injective (fun w => w.1 i₀) fun w w' hww' => ?_
    apply Subtype.ext
    funext j
    by_cases hj : j = i₀
    · subst hj
      exact hww'
    · rw [hz w j hj, hz w' j hj]
  · push Not at h
    have hz : ∀ w : {w : κ → K // ∀ i, c * (d i * w i) = w i}, w.1 = 0 := by
      intro w
      funext j
      have h1 := w.2 j
      have h4 : (c * d j - 1) * w.1 j = 0 := by rw [sub_mul, one_mul, mul_assoc, h1, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr (h j))
    have : Subsingleton {w : κ → K // ∀ i, c * (d i * w i) = w i} :=
      ⟨fun w w' => Subtype.ext ((hz w).trans (hz w').symm)⟩
    calc Nat.card {w : κ → K // ∀ i, c * (d i * w i) = w i} ≤ 1 :=
          Finite.card_le_one_iff_subsingleton.mpr this
      _ ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'

theorem le_rkIdx_of_card_le {V : Type*} [Group V] [Finite V] {m j : ℕ}
    (hV : Nat.card V = 2 ^ m) {U : Subgroup V} (hU : Nat.card U ≤ 2 ^ j) : m - j ≤ rkIdx U := by
  obtain ⟨k, hk, hUk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hV ▸ U.card_subgroup_dvd_card)
  have hkj : k ≤ j := by
    rw [hUk] at hU
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hU
  have h1 := U.card_mul_index
  rw [hUk, hV] at h1
  have h2 : U.index = 2 ^ (m - k) := by
    have h3 : 2 ^ m = 2 ^ k * 2 ^ (m - k) := by rw [← pow_add]; congr 1; omega
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  unfold rkIdx
  rw [h2, padicValNat.prime_pow]
  omega

theorem zpow_apply_eq_of_apply_eq {V : Type*} [Group V] {y : MulAut V} {v : V} (hv : y v = v)
    (k : ℤ) : (y ^ k) v = v := by
  induction k using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [_root_.zpow_add_one, MulAut.mul_apply, hv, ih]
  | pred k ih =>
    rw [_root_.zpow_sub_one, MulAut.mul_apply]
    have : y⁻¹ v = v := by
      conv_lhs => rw [← hv]
      simp
    rw [this, ih]

theorem card_modEq_fix {V : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime] {y : MulAut V}
    (hy : orderOf y = p) :
    Nat.card V ≡ Nat.card {v : V // y v = v} [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have h := hP.card_modEq_card_fixedPoints V
  have h2 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) V) =
      Nat.card {v : V // y v = v} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro hv
      exact hv ⟨y, Subgroup.mem_zpowers y⟩
    · intro hv g
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_apply_eq_of_apply_eq hv k
  rw [h2] at h
  exact h

theorem eq_zero_of_modEq_of_dvd_sq_add_one {p q w : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q ^ 2 + 1) (hw : w < 4) (h : q ^ 4 ≡ q ^ w [MOD p]) : w = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hx2 : (q : ZMod p) ^ 2 = -1 := by
    have : ((q ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    push_cast at this
    linear_combination this
  have h' : (q : ZMod p) ^ 4 = (q : ZMod p) ^ w := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    push_cast at this
    exact this
  have h1 : (q : ZMod p) ^ w = 1 := by
    rw [← h']
    linear_combination ((q : ZMod p) ^ 2 - 1) * hx2
  by_contra hw0
  apply h2
  interval_cases w
  · exact absurd rfl hw0
  · have h1' : (q : ZMod p) = 1 := by simpa using h1
    linear_combination hx2 - ((q : ZMod p) + 1) * h1'
  · linear_combination hx2 - h1
  · linear_combination (1 + (q : ZMod p) - (q : ZMod p) ^ 2) * hx2 + ((q : ZMod p) - 1) * h1

end Counting

end H

end CFSG.Quasithin
