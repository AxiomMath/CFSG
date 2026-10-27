module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitaryDiag
public import CFSG.LocalAnalysis.StandardType.GGStdPosTorusNorm
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.LieType.Steinberg.CentralExt.SUBruhatExtras
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType.KGPosSU

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem Matrix

section Basic

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem commute_of_mem_diagSubgroup {x y : SU σ n} (hx : x ∈ diagSubgroup σ n)
    (hy : y ∈ diagSubgroup σ n) : x * y = y * x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  apply mat_injective
  rw [map_mul, map_mul, mat_apply, mat_apply, ha, hb, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem mem_diagSubgroup_iff_isDiag {x : SU σ n} :
    x ∈ diagSubgroup σ n ↔ (mat σ n x).IsDiag := by
  constructor
  · rintro ⟨d, hd⟩
    rw [mat_apply, hd]
    exact isDiag_diagonal d
  · intro h
    exact ⟨_, ((isDiag_iff_diagonal_diag _).mp h).symm⟩

theorem mat_apply_eq_zero_of_commute {x y : SU σ n} {d : Fin n → F}
    (hx : mat σ n x = diagonal d) (hxy : x * y = y * x) {a b : Fin n} (hab : d a ≠ d b) :
    mat σ n y a b = 0 := by
  have h := congrFun (congrFun (congrArg (mat σ n) hxy) a) b
  rw [map_mul, map_mul, hx, diagonal_mul, mul_diagonal] at h
  have h2 : (d a - d b) * mat σ n y a b = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hab
  · exact h3

theorem pow_apply_self_of_col {M : Matrix (Fin n) (Fin n) F} {c : Fin n}
    (hM : ∀ r, r ≠ c → M r c = 0) (N : ℕ) : (M ^ N) c c = M c c ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Finset.sum_eq_single c, ih]
    · intro r _ hr
      rw [hM r hr, mul_zero]
    · simp

end Basic

section Field

variable {F : Type} [Field F]

theorem zpow_ne_one_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F}
    (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) {k : ℤ} (hk : k ≠ 0) (hk1 : -2 ≤ k) (hk2 : k ≤ 2) :
    ζ ^ k ≠ 1 := by
  have hsq : ζ ^ 2 ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    apply hζ1
    rw [hm, pow_succ, pow_mul, h, one_pow, one_mul] at hζ
    exact hζ
  interval_cases k
  · rw [_root_.zpow_neg, inv_ne_one, zpow_ofNat]
    exact hsq
  · rw [_root_.zpow_neg, inv_ne_one, zpow_one]
    exact hζ1
  · exact absurd rfl hk
  · rw [zpow_one]
    exact hζ1
  · rw [zpow_ofNat]
    exact hsq

theorem exists_pow_eq_one_ne_one [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) : ∃ ζ : F, ζ ^ p = 1 ∧ ζ ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    refine hpq.trans ⟨2 ^ f + 1, ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.one_le_two_pow (n := f))
    rw [hk, Nat.add_sub_cancel_left]
    ring_nf
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hcard
  refine ⟨u, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · intro h
    have h1 : u = 1 := Units.ext h
    rw [h1, orderOf_one] at hu
    exact hp.one_lt.ne hu

variable [Finite F] [CharP F 2] {f : ℕ}

theorem unitaryInvolution_eq_self_of_pow_eq_one {p : ℕ} (hpq : p ∣ 2 ^ f - 1) {x : F}
    (hx : x ^ p = 1) : unitaryInvolution F 2 f x = x := by
  rw [unitaryInvolution_apply]
  obtain ⟨m, hm⟩ := hpq
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  calc x ^ 2 ^ f = x ^ (2 ^ f - 1) * x := by rw [← pow_succ, Nat.sub_add_cancel h1]
    _ = x := by rw [hm, pow_mul, hx, one_pow, one_mul]

omit [Finite F] [CharP F 2] in
theorem longTorusFun_lowIdx_eq_zpow {n : ℕ} (c : Fin (n / 2)) (ζ : F) (s : Fin n) :
    longTorusFun (lowIdx c) ζ s = ζ ^ weight n s c := by
  rw [longTorusFun, weight_apply']
  have hc := c.isLt
  have hs := s.isLt
  by_cases h1 : s.val = c.val
  · rw [if_pos (Fin.ext (by rw [val_lowIdx]; exact h1)), if_pos h1, zpow_one]
  · rw [if_neg (fun h => h1 (by rw [h, val_lowIdx])), if_neg h1]
    by_cases h2 : s.val + c.val + 1 = n
    · rw [if_pos (Fin.ext (by rw [Fin.val_rev, val_lowIdx]; omega)), if_pos h2, _root_.zpow_neg_one]
    · rw [if_neg (fun h => h2 (by rw [h, Fin.val_rev, val_lowIdx]; omega)), if_neg h2,
        zpow_zero]

end Field

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

variable (F f) in
@[expose] def diagP (p : ℕ) : Subgroup (SU (unitaryInvolution F 2 f) 6) where
  carrier := {x | x ∈ diagSubgroup (unitaryInvolution F 2 f) 6 ∧ x ^ p = 1}
  mul_mem' := by
    rintro x y ⟨hx, hxp⟩ ⟨hy, hyp⟩
    refine ⟨mul_mem hx hy, ?_⟩
    rw [Commute.mul_pow (commute_of_mem_diagSubgroup hx hy) p, hxp, hyp, one_mul]
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' := by
    rintro x ⟨hx, hxp⟩
    exact ⟨inv_mem hx, by rw [inv_pow, hxp, inv_one]⟩

theorem mem_diagP {p : ℕ} {x : SU (unitaryInvolution F 2 f) 6} :
    x ∈ diagP F f p ↔ x ∈ diagSubgroup (unitaryInvolution F 2 f) 6 ∧ x ^ p = 1 :=
  Iff.rfl

theorem diagP_entries {p : ℕ} (hpq : p ∣ 2 ^ f - 1) {x : SU (unitaryInvolution F 2 f) 6}
    (hx : x ∈ diagP F f p) {d : Fin 6 → F} (hd : mat _ 6 x = diagonal d) (s : Fin 6) :
    d s ^ p = 1 ∧ d (Fin.rev s) = (d s)⁻¹ := by
  have hp : d s ^ p = 1 := by
    have h := congrFun (congrFun (congrArg (mat _ 6) hx.2) s) s
    rw [map_pow, hd, diagonal_pow, map_one, diagonal_apply_eq, one_apply_eq] at h
    exact h
  refine ⟨hp, ?_⟩
  have hu := unitary_of_coe_eq_diagonal (σ := unitaryInvolution F 2 f) hd s
  rw [unitaryInvolution_eq_self_of_pow_eq_one hpq hp] at hu
  exact eq_inv_of_mul_eq_one_right hu

theorem exists_mem_diagP_longTorusFun (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : 0 < p)
    (hpq : p ∣ 2 ^ f - 1) {ζ : F} (hζ : ζ ^ p = 1) {b : Fin 6} (hb : b ≠ Fin.rev b) :
    ∃ x ∈ diagP F f p, mat _ 6 x = diagonal (longTorusFun b ζ) := by
  obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hζ
    exact zero_ne_one hζ
  have he := unitaryInvolution_eq_self_of_pow_eq_one hpq hζ
  let x := longTorus (unitaryInvolution F 2 f) hb ζ' he
  have hx : mat _ 6 x = diagonal (longTorusFun b ζ) :=
    coe_longTorus (unitaryInvolution F 2 f) hb hζ' he hζ0
  refine ⟨x, ⟨⟨_, hx⟩, ?_⟩, hx⟩
  apply mat_injective
  rw [map_pow, hx, diagonal_pow, map_one, ← diagonal_one]
  congr 1
  funext s
  simp only [Pi.pow_apply, longTorusFun]
  split_ifs <;> simp [hζ, inv_pow]

theorem mem_diagSubgroup_of_commute (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) {y : SU (unitaryInvolution F 2 f) 6}
    (hy : ∀ x ∈ diagP F f p, x * y = y * x) : y ∈ diagSubgroup (unitaryInvolution F 2 f) 6 := by
  obtain ⟨ζ, hζ, hζ1⟩ := exists_pow_eq_one_ne_one hF hp hpq
  rw [mem_diagSubgroup_iff_isDiag]
  intro a b hab
  obtain ⟨c, hc⟩ : ∃ c : Fin (6 / 2), weight 6 a c ≠ weight 6 b c := by
    by_contra h
    push Not at h
    exact hab (weight_injective (funext h))
  obtain ⟨x, hx, hxd⟩ := exists_mem_diagP_longTorusFun hF hp.pos hpq hζ (lowIdx_ne_rev c c)
  refine mat_apply_eq_zero_of_commute hxd (hy x hx) ?_
  rw [longTorusFun_lowIdx_eq_zpow, longTorusFun_lowIdx_eq_zpow]
  intro h
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have h' : ζ ^ (weight 6 a c - weight 6 b c) = 1 := by
    rw [zpow_sub₀ hζ0, h, div_self (zpow_ne_zero _ hζ0)]
  obtain ⟨ha1, ha2⟩ := weight_apply_bounds a c
  obtain ⟨hb1, hb2⟩ := weight_apply_bounds b c
  exact zpow_ne_one_of_pow_eq_one hp hp2 hζ hζ1 (sub_ne_zero.mpr hc) (by omega) (by omega) h'

theorem eq_one_of_mem_center_of_pow_eq_one (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) {z : SU (unitaryInvolution F 2 f) 6}
    (hz : z ∈ Subgroup.center _) (hzp : z ^ p = 1) : z = 1 := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
  have hzd := mem_diagSubgroup_of_commute hF hp hp2 hpq fun x _ =>
    (Subgroup.mem_center_iff.mp hz x)
  obtain ⟨d, hd⟩ := hzd
  have hzP : z ∈ diagP F f p := ⟨⟨d, hd⟩, hzp⟩
  have hperm : ∀ k : Fin (6 / 2), ∀ s, d ((levelPerm k).symm s) = d s := by
    intro k s
    have hc := Subgroup.mem_center_iff.mp hz (levelWeyl hσ ζ' k)
    have h1 : levelWeyl hσ ζ' k * z * (levelWeyl hσ ζ' k)⁻¹ = z := by
      rw [hc, mul_inv_cancel_right]
    have h2 := coe_conj_diagonal (coe_levelWeyl hσ hζ' k) hd
    rw [h1, hd] at h2
    exact congrFun (diagonal_injective h2.symm) s
  have hent := fun s => diagP_entries hpq hzP hd s
  have h23 : d 2 = d 3 := hperm 2 3
  have h12 : d 1 = d 2 := hperm 1 2
  have h01 : d 0 = d 1 := hperm 0 1
  have h2 : d 2 = 1 := by
    have h := (hent 2).2
    rw [show Fin.rev (2 : Fin 6) = 3 from rfl, ← h23] at h
    have hsq : d 2 ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h]
      exact mul_inv_cancel₀ (fun h0 => by
        have := (hent 2).1
        rw [h0, zero_pow hp.ne_zero] at this
        exact zero_ne_one this)
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have h' := (hent 2).1
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at h'
    exact h'
  have hall : ∀ s, d s = 1 := by
    intro s
    fin_cases s
    · exact h01.trans (h12.trans h2)
    · exact h12.trans h2
    · exact h2
    · exact h23.symm.trans h2
    · have h := (hent 1).2
      rw [show Fin.rev (1 : Fin 6) = 4 from rfl, h12, h2, inv_one] at h
      exact h
    · have h := (hent 0).2
      rw [show Fin.rev (0 : Fin 6) = 5 from rfl, h01, h12, h2, inv_one] at h
      exact h
  apply mat_injective
  rw [mat_apply, hd, map_one, ← diagonal_one]
  exact congrArg diagonal (funext hall)

theorem pow_eq_one_of_mem_center (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) {z : SU (unitaryInvolution F 2 f) 6}
    (hz : z ∈ Subgroup.center _) : z ^ (Nat.card F - 1) = 1 := by
  obtain ⟨d, hd⟩ := mem_diagSubgroup_of_commute hF hp hp2 hpq fun x _ =>
    (Subgroup.mem_center_iff.mp hz x)
  have h0 := ne_zero_of_unitary (unitary_of_coe_eq_diagonal (σ := unitaryInvolution F 2 f) hd)
  apply mat_injective
  rw [map_pow, mat_apply, hd, diagonal_pow, map_one, ← diagonal_one]
  congr 1
  funext s
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ (h0 s)

end Torus

section Weyl

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem ggTorus_eq_diagSubgroup :
    ggTorus (Unitary.rootDatum hF 6) = diagSubgroup (unitaryInvolution F 2 f) 6 := by
  obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
  refine le_antisymm ?_ fun x hx => ?_
  · rw [ggStdPos_ggTorus_eq (Unitary.isCTGroupDatum hF 6 (by norm_num) ζ' hζ')
      (Unitary.steinbergExtras hF 6 (by norm_num) ζ' hζ')
      (CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ' hζ')]
    exact iSup_le fun k => levelTorus_le_diagSubgroup k
  · exact MpStdSU.mem_ggTorus_of_isDiag hF (mem_diagSubgroup_iff_isDiag.mp hx)

theorem mem_ggTorus_of_actsAs_one {K : Type} [Group K] {D : UniversalRootDatum K} {x : K}
    (hx : ActsAs D x 1) : x ∈ ggTorus D :=
  Subgroup.mem_iInf.mpr fun γ => Subgroup.mem_iInf.mpr fun hγ => by
    rw [mem_normalizer_iff_map_conj, hx γ hγ, map_one, Module.End.one_apply]

variable {ν : GGWeyl (Unitary.rootDatum hF 6) →* SU (unitaryInvolution F 2 f) 6}

include hF in
theorem conj_mem_diagSubgroup (hν : GGWeylLift (Unitary.rootDatum hF 6) ν)
    (w : GGWeyl (Unitary.rootDatum hF 6)) {x : SU (unitaryInvolution F 2 f) 6}
    (hx : x ∈ diagSubgroup (unitaryInvolution F 2 f) 6) :
    ν w * x * (ν w)⁻¹ ∈ diagSubgroup (unitaryInvolution F 2 f) 6 := by
  rw [← ggTorus_eq_diagSubgroup hF] at hx ⊢
  exact ggStdPos_conj_mem_ggTorus_of_actsAs hx (ggStdPos_actsAs_weylLift hν w)

include hF in
theorem conj_mem_diagP (hν : GGWeylLift (Unitary.rootDatum hF 6) ν)
    (w : GGWeyl (Unitary.rootDatum hF 6)) {p : ℕ} {x : SU (unitaryInvolution F 2 f) 6}
    (hx : x ∈ diagP F f p) : ν w * x * (ν w)⁻¹ ∈ diagP F f p :=
  ⟨conj_mem_diagSubgroup hF hν w hx.1, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩

include hF in
theorem mat_conj_simple (hν : GGWeylLift (Unitary.rootDatum hF 6) ν) (k : Fin (6 / 2))
    {x : SU (unitaryInvolution F 2 f) 6} {d : Fin 6 → F} (hx : mat _ 6 x = diagonal d) :
    mat _ 6 (ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k) * x *
        (ν ((coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k))⁻¹) =
      diagonal fun r => d ((levelPerm k).symm r) := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
  have hct := Unitary.isCTGroupDatum hF 6 (by norm_num) ζ' hζ'
  set s := (coxeterMatrix (Unitary.rootDatum hF 6).isFiniteType).simple k
  have h1 : ActsAs (Unitary.rootDatum hF 6) ((levelWeyl hσ ζ' k)⁻¹ * ν s) 1 := by
    have h := (actsAs_n hct k).inv.mul (ggStdPos_actsAs_weylLift hν s)
    rwa [CoxeterMatrix.toCoxeterSystem_simple, inv_mul_cancel] at h
  have hh := mem_ggTorus_of_actsAs_one h1
  rw [ggTorus_eq_diagSubgroup hF] at hh
  have hx' : x ∈ diagSubgroup (unitaryInvolution F 2 f) 6 := ⟨d, hx⟩
  have hc := commute_of_mem_diagSubgroup hh hx'
  have e : ν s * x * (ν s)⁻¹ = levelWeyl hσ ζ' k * x * (levelWeyl hσ ζ' k)⁻¹ := by
    have e1 : ν s = levelWeyl hσ ζ' k * ((levelWeyl hσ ζ' k)⁻¹ * ν s) := by group
    rw [e1, _root_.mul_inv_rev, mul_assoc (levelWeyl hσ ζ' k), mul_assoc (levelWeyl hσ ζ' k), hc]
    group
  rw [e]
  exact coe_conj_diagonal (coe_levelWeyl hσ hζ' k) hx

include hF in
theorem exists_fixFree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) :
    ∀ γ ∈ (Unitary.rootDatum hF 6).roots, ∃ t ∈ diagP F f p,
      ∀ y ∈ (Unitary.rootDatum hF 6).rootGroup γ, t * y * t⁻¹ = y → y = 1 := by
  intro γ hγ
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ, hζ1⟩ := exists_pow_eq_one_ne_one hF hp hpq
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have he : toStd 6 γ ≠ 0 := toStd_ne_zero_of_mem_roots hγ
  obtain ⟨c, hc⟩ : ∃ c, toStd 6 γ c ≠ 0 := by
    by_contra h
    push Not at h
    exact he (funext h)
  obtain ⟨t, ht, htd⟩ := exists_mem_diagP_longTorusFun hF hp.pos hpq hζ (lowIdx_ne_rev c c)
  refine ⟨t, ht, fun y hy hfix => ?_⟩
  have hty : t * y = y * t := by
    calc t * y = t * y * t⁻¹ * t := by group
      _ = y * t := by rw [hfix]
  apply mat_injective
  rw [map_one]
  ext a b
  by_cases hab : weight 6 a - weight 6 b = toStd 6 γ ∨ weight 6 a - weight 6 b = 2 • toStd 6 γ
  · have hne : a ≠ b := by
      rintro rfl
      rw [sub_self] at hab
      rcases hab with h | h
      · exact he h.symm
      · exact he (eq_zero_of_two_nsmul_eq_zero h)
    rw [one_apply_ne hne]
    refine mat_apply_eq_zero_of_commute htd hty ?_
    rw [longTorusFun_lowIdx_eq_zpow, longTorusFun_lowIdx_eq_zpow]
    intro h
    have h' : ζ ^ (weight 6 a c - weight 6 b c) = 1 := by
      rw [zpow_sub₀ hζ0, h, div_self (zpow_ne_zero _ hζ0)]
    obtain ⟨ha1, ha2⟩ := weight_apply_bounds a c
    obtain ⟨hb1, hb2⟩ := weight_apply_bounds b c
    have hk : weight 6 a c - weight 6 b c ≠ 0 := by
      rcases hab with h3 | h3
      · have := congrFun h3 c
        simp only [Pi.sub_apply] at this
        rw [this]
        exact hc
      · have := congrFun h3 c
        simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
        rw [this]
        exact mul_ne_zero two_ne_zero hc
    exact zpow_ne_one_of_pow_eq_one hp hp2 hζ hζ1 hk (by omega) (by omega) h'
  · rw [not_or] at hab
    exact mat_apply_of_mem_rootGroup hσ hy hab.1 hab.2

include hF in
theorem exists_eq_mul_of_normalizes (hν : GGWeylLift (Unitary.rootDatum hF 6) ν) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) {u : SU (unitaryInvolution F 2 f) 6}
    (hu : ∀ x ∈ diagP F f p, u * x * u⁻¹ ∈ diagP F f p)
    (hu' : ∀ x ∈ diagP F f p, u⁻¹ * x * u ∈ diagP F f p) :
    ∃ h ∈ diagSubgroup (unitaryInvolution F 2 f) 6, ∃ w, u = h * ν w := by
  obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
  have hct := Unitary.isCTGroupDatum hF 6 (by norm_num) ζ' hζ'
  have hext := Unitary.steinbergExtras hF 6 (by norm_num) ζ' hζ'
  have hBU := CentralExt.SUBruhat.bruhatExtras hF (n := 6) (by norm_num) ζ' hζ'
  have hT : (⨆ i, levelTorus (unitaryInvolution F 2 f) i) =
      diagSubgroup (unitaryInvolution F 2 f) 6 := by
    rw [← ggTorus_eq_diagSubgroup hF]
    exact (ggStdPos_ggTorus_eq hct hext hBU).symm
  have hN : ∀ t ∈ ⨆ i, levelTorus (unitaryInvolution F 2 f) i,
      u * t * u⁻¹ ∈ ⨆ i, levelTorus (unitaryInvolution F 2 f) i := by
    intro t ht
    rw [hT] at ht ⊢
    refine mem_diagSubgroup_of_commute hF hp hp2 hpq fun x hx => ?_
    have hc := commute_of_mem_diagSubgroup ht (hu' x hx).1
    calc x * (u * t * u⁻¹) = u * ((u⁻¹ * x * u) * t) * u⁻¹ := by group
      _ = u * (t * (u⁻¹ * x * u)) * u⁻¹ := by rw [hc]
      _ = u * t * u⁻¹ * x := by group
  have hno : ∀ γ ∈ (Unitary.rootDatum hF 6).roots,
      ∃ t ∈ ⨆ i, levelTorus (unitaryInvolution F 2 f) i,
        ∀ y ∈ (Unitary.rootDatum hF 6).rootGroup γ, t * y * t⁻¹ = y → y = 1 := by
    intro γ hγ
    obtain ⟨t, ht, hfix⟩ := exists_fixFree hF hp hp2 hpq γ hγ
    exact ⟨t, hT ▸ ht.1, hfix⟩
  obtain ⟨h, hh, w, rfl⟩ :=
    ClassicalInvolution.ModelFacts.ChevAut.exists_mem_iSup_mul_nrep_of_forall_conj_mem hct hext
      hBU hno hN
  have h1 : ActsAs (Unitary.rootDatum hF 6) (nrep hct w * (ν w)⁻¹) 1 := by
    have h := (actsAs_nrep hct w).mul (ggStdPos_actsAs_weylLift hν w).inv
    rwa [mul_inv_cancel] at h
  have hh' := mem_ggTorus_of_actsAs_one h1
  rw [ggTorus_eq_diagSubgroup hF] at hh'
  refine ⟨h * (nrep hct w * (ν w)⁻¹), mul_mem (hT ▸ hh) hh', w, by group⟩

include hF in
theorem eq_one_of_mem_diagSubgroup (hν : GGWeylLift (Unitary.rootDatum hF 6) ν)
    {w : GGWeyl (Unitary.rootDatum hF 6)}
    (hw : ν w ∈ diagSubgroup (unitaryInvolution F 2 f) 6) : w = 1 := by
  obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero hF
  have hext := Unitary.steinbergExtras hF 6 (by norm_num) ζ' hζ'
  rw [← ggTorus_eq_diagSubgroup hF] at hw
  refine eq_one_of_forall_rootGroup_eq hext fun γ hγ => ?_
  rw [← ggStdPos_actsAs_weylLift hν w γ hγ]
  exact mem_normalizer_iff_map_conj.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hw γ) hγ)

end Weyl

end CFSG.StandardType.KGPosSU

end
