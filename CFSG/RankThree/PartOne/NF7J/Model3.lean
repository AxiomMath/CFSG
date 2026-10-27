module

public import CFSG.RankThree.PartOne.NF7J.Model2

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS
open scoped commutatorElement

section Iota

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] {F : RFrame G p c L E f K} {D : Datum p E}

@[expose] noncomputable def rhoU (F : RFrame G p c L E f K) (D : Datum p E) : GL (Fin 3) (ZMod 2) :=
  D.e ⟨F.r₀ * F.r₁, rho_mem F D⟩

structure Norm (F : RFrame G p c L E f K) (D : Datum p E) : Prop where
  h1 : ((D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ : GL (Fin 3) (ZMod 2)) : M32) = mk32 84
  h2 : ((D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ : GL (Fin 3) (ZMod 2)) : M32) = mk32 167

theorem Norm.rho (N : Norm F D) : ((rhoU F D : GL (Fin 3) (ZMod 2)) : M32) = mk32 482 := by
  have h : (⟨F.r₀ * F.r₁, rho_mem F D⟩ : ↥D.H) =
      ⟨D.ν * F.r₀, a₁_mem F D⟩ * ⟨D.ν * F.r₁, a₂_mem F D⟩ :=
    Subtype.ext (D.νmul_νmul F.r₀ F.r₁).symm
  unfold rhoU
  rw [h, map_mul, Units.val_mul, N.h1, N.h2, mk32_84_mul_167]

theorem rho_comm_zp (j : ℕ) :
    (F.r₀ * F.r₁) ^ j * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) =
      (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * (F.r₀ * F.r₁) ^ j := by
  have h1 : (F.r₀ * F.r₁) ^ j * D.ν = D.ν * (F.r₀ * F.r₁) ^ j := D.ν_comm _
  have h2 : (F.r₀ * F.r₁) ^ j * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) =
      ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) * (F.r₀ * F.r₁) ^ j := by
    have := (Commute.refl (F.r₀ * F.r₁)).pow_left j
    exact (this.mul_right this).eq
  calc (F.r₀ * F.r₁) ^ j * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)))
      = ((F.r₀ * F.r₁) ^ j * D.ν) * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) := by simp only [mul_assoc]
    _ = D.ν * ((F.r₀ * F.r₁) ^ j * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) := by
        rw [h1]; simp only [mul_assoc]
    _ = D.ν * (((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) * (F.r₀ * F.r₁) ^ j) := by rw [h2]
    _ = (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * (F.r₀ * F.r₁) ^ j := by simp only [mul_assoc]

omit [Finite G] in
theorem comm_sq_of_pow_four {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (h4 : (a * b) ^ 4 = 1) : a * ((a * b) * (a * b)) = ((a * b) * (a * b)) * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h5 : a * b * a * b * a * (b * a * b) = 1 := by
    have : (a * b) ^ 4 = a * b * a * b * a * (b * a * b) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← this]
    exact h4
  have h6 : a * b * a * b * a = b * a * b := by
    have := eq_inv_of_mul_eq_one_left h5
    rw [this]
    simp [_root_.mul_inv_rev, ha', hb', mul_assoc]
  calc a * (a * b * (a * b)) = (a * a) * b * (a * b) := by simp only [mul_assoc]
    _ = b * (a * b) := by rw [ha, one_mul]
    _ = b * a * b := by simp only [mul_assoc]
    _ = a * b * a * b * a := h6.symm
    _ = a * b * (a * b) * a := by simp only [mul_assoc]

theorem r₀_comm_zz : F.r₀ * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) =
    ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) * F.r₀ :=
  comm_sq_of_pow_four (RFrame.r₀_sq F) (RFrame.r₁_sq F) (rho_pow_four F)

variable (X : EFacts G p c E)

theorem rho_pow_fix_c (j : ℕ) : ((F.r₀ * F.r₁) ^ j) X.cE = X.cE := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, MulAut.mul_apply, rho_fix_c F X, ih]

theorem a₁_c : (D.ν * F.r₀) X.cE = X.cE⁻¹ := by
  rw [MulAut.mul_apply, torusImage_fix_c F X F.r₀_L, D.hν]

theorem a₁_comm_zp : (D.ν * F.r₀) * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) =
    (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * (D.ν * F.r₀) := by
  rw [D.νmul_νmul, D.νmul_νmul]
  exact r₀_comm_zz (F := F)

theorem a₁_rho : (D.ν * F.r₀) * (F.r₀ * F.r₁) * (D.ν * F.r₀) = F.r₁ * F.r₀ := by
  have h0 := RFrame.r₀_sq F
  calc (D.ν * F.r₀) * (F.r₀ * F.r₁) * (D.ν * F.r₀)
      = D.ν * (F.r₀ * (F.r₀ * F.r₁) * D.ν) * F.r₀ := by simp only [mul_assoc]
    _ = D.ν * (D.ν * (F.r₀ * (F.r₀ * F.r₁))) * F.r₀ := by rw [D.ν_comm (F.r₀ * (F.r₀ * F.r₁))]
    _ = (D.ν * D.ν) * (F.r₀ * (F.r₀ * F.r₁) * F.r₀) := by simp only [mul_assoc]
    _ = F.r₁ * F.r₀ := by
        rw [D.ν_sq, one_mul]
        calc F.r₀ * (F.r₀ * F.r₁) * F.r₀ = (F.r₀ * F.r₀) * F.r₁ * F.r₀ := by simp only [mul_assoc]
          _ = F.r₁ * F.r₀ := by rw [h0, one_mul]

omit [Field K] [Finite K] [CharP K 2] [Finite G] in
theorem coe_conj_cE {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    ((conjAut E w hw X.cE : E) : G) = w * c * w⁻¹ := Equivariance.coe_conjAut hw X.cE

include X in
theorem Base.fix_of (B : Base F D) (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hcomm : conjAut E w hw * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) =
      (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * conjAut E w hw)
    (hc : conjAut E w hw X.cE = X.cE) :
    conjBy w B.R = B.R ∧ conjBy w B.R' = B.R' := by
  have hfix : conjAut E w hw * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * (conjAut E w hw)⁻¹ =
      D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) := by
    rw [hcomm]
    group
  have hn : w * c * w⁻¹ = c ^ 1 := by
    have := congrArg Subtype.val hc
    rw [coe_conj_cE X hw] at this
    rw [pow_one]
    exact this
  have h5 := X.five_le
  exact (B.rule X hdvd hodd hw hfix hn).1 (Nat.mod_eq_of_lt (by omega))

include X in
theorem Base.swap_of (B : Base F D) (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hcomm : conjAut E w hw * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) =
      (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * conjAut E w hw)
    (hc : conjAut E w hw X.cE = X.cE⁻¹) :
    conjBy w B.R = B.R' ∧ conjBy w B.R' = B.R := by
  have hfix : conjAut E w hw * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * (conjAut E w hw)⁻¹ =
      D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) := by
    rw [hcomm]
    group
  have h5 := X.five_le
  have hpow : c ^ (p - 1) = c⁻¹ := by
    have : c ^ (p - 1) * c = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact X.c_pow
    exact eq_inv_of_mul_eq_one_left this
  have hn : w * c * w⁻¹ = c ^ (p - 1) := by
    have := congrArg Subtype.val hc
    rw [coe_conj_cE X hw] at this
    rw [hpow]
    exact this
  exact (B.rule X hdvd hodd hw hfix hn).2 (by rw [Nat.sub_add_cancel (by omega)]; exact Nat.mod_self p)

include F in
theorem exists_y : ∃ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)), conjAut E y hy = D.ν := by
  obtain ⟨u, hu, hue⟩ := D.exists_lift (a₁_mem F D)
  obtain ⟨x, hxL, hxE, hxr⟩ := KF132.exists_conjAut_of_mem_torusImage F.r₀_L
  refine ⟨u * x, (Subgroup.normalizer (E : Set G)).mul_mem hu hxE, ?_⟩
  rw [conjAut_mul' hu hxE, hue, ← hxr, mul_assoc, RFrame.r₀_sq F, mul_one]

variable (B : Base F D) (N : Norm F D)

@[expose] def IsIota (x : GL (Fin 3) (ZMod 2)) (S : Subgroup G) : Prop :=
  ∃ (k : GL (Fin 3) (ZMod 2)) (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
    k * rhoU F D * k⁻¹ = x ∧ conjAut E w hw = ((D.e.symm k : ↥D.H) : MulAut E) ∧ S = conjBy w B.R

include N in
theorem isIota_exists {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32)) : ∃ S, IsIota B x S := by
  obtain ⟨Km, hKd, hK⟩ := exists_conj_rho (x : M32) hx
  have hkr : matUnit' Km hKd * rhoU F D * (matUnit' Km hKd)⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, matUnit'_val, N.rho]
    exact hK
  obtain ⟨w, hw, hwe⟩ := D.exists_lift (D.e.symm (matUnit' Km hKd)).2
  exact ⟨conjBy w B.R, matUnit' Km hKd, w, hw, hkr, hwe, rfl⟩

omit [Field K] [Finite K] [CharP K 2] [Finite G] in
theorem conjAut_commutator {u v : G} (hu : u ∈ Subgroup.normalizer (E : Set G))
    (hv : v ∈ Subgroup.normalizer (E : Set G))
    (h : conjAut E u hu * conjAut E v hv = conjAut E v hv * conjAut E u hu) :
    ∃ hd : u⁻¹ * v⁻¹ * u * v ∈ Subgroup.normalizer (E : Set G),
      conjAut E (u⁻¹ * v⁻¹ * u * v) hd = 1 := by
  have hN := Subgroup.normalizer (E : Set G)
  have hd : u⁻¹ * v⁻¹ * u * v ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem
        ((Subgroup.normalizer (E : Set G)).mul_mem ((Subgroup.normalizer (E : Set G)).inv_mem hu)
          ((Subgroup.normalizer (E : Set G)).inv_mem hv)) hu) hv
  refine ⟨hd, ?_⟩
  have e1 := conjAut_mul' ((Subgroup.normalizer (E : Set G)).mul_mem
    ((Subgroup.normalizer (E : Set G)).mul_mem ((Subgroup.normalizer (E : Set G)).inv_mem hu)
      ((Subgroup.normalizer (E : Set G)).inv_mem hv)) hu) hv
  have e2 := conjAut_mul' ((Subgroup.normalizer (E : Set G)).mul_mem
    ((Subgroup.normalizer (E : Set G)).inv_mem hu) ((Subgroup.normalizer (E : Set G)).inv_mem hv)) hu
  have e3 := conjAut_mul' ((Subgroup.normalizer (E : Set G)).inv_mem hu)
    ((Subgroup.normalizer (E : Set G)).inv_mem hv)
  rw [e1, e2, e3, Equivariance.conjAut_inv hu, Equivariance.conjAut_inv hv]
  calc (conjAut E u hu)⁻¹ * (conjAut E v hv)⁻¹ * conjAut E u hu * conjAut E v hv
      = (conjAut E u hu)⁻¹ * (conjAut E v hv)⁻¹ * (conjAut E u hu * conjAut E v hv) := by
        simp only [mul_assoc]
    _ = (conjAut E u hu)⁻¹ * (conjAut E v hv)⁻¹ * (conjAut E v hv * conjAut E u hu) := by rw [h]
    _ = 1 := by group

theorem rho_inv_eq (F : RFrame G p c L E f K) : (F.r₀ * F.r₁)⁻¹ = F.r₁ * F.r₀ := by
  have h0 := RFrame.r₀_sq F
  have h1 := RFrame.r₁_sq F
  apply inv_eq_of_mul_eq_one_right
  calc (F.r₀ * F.r₁) * (F.r₁ * F.r₀) = F.r₀ * (F.r₁ * F.r₁) * F.r₀ := by simp only [mul_assoc]
    _ = 1 := by rw [h1, mul_one, h0]

include X N in
theorem isIota_unique (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {x : GL (Fin 3) (ZMod 2)}
    {S S' : Subgroup G} (h : IsIota B x S) (h' : IsIota B x S') : S = S' := by
  obtain ⟨k, w, hw, hk, hwe, hS⟩ := h
  obtain ⟨k', w', hw', hk', hwe', hS'⟩ := h'
  have hmc : (k⁻¹ * k') * rhoU F D = rhoU F D * (k⁻¹ * k') := by
    have h1 : k * rhoU F D * k⁻¹ = k' * rhoU F D * k'⁻¹ := hk.trans hk'.symm
    calc k⁻¹ * k' * rhoU F D = k⁻¹ * (k' * rhoU F D * k'⁻¹) * k' := by group
      _ = k⁻¹ * (k * rhoU F D * k⁻¹) * k' := by rw [h1]
      _ = rhoU F D * (k⁻¹ * k') := by group
  have hmat : ((k⁻¹ * k' : GL (Fin 3) (ZMod 2)) : M32) * mk32 482 =
      mk32 482 * ((k⁻¹ * k' : GL (Fin 3) (ZMod 2)) : M32) := by
    have := congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : M32)) hmc
    simpa only [Units.val_mul, N.rho] using this
  have hcases := cent_rho_fin _ (det3_GL (k⁻¹ * k')) hmat
  have hrho : ((D.e.symm (rhoU F D) : ↥D.H) : MulAut E) = F.r₀ * F.r₁ := by
    unfold rhoU
    rw [MulEquiv.symm_apply_apply]
  have hj : ∃ j : ℕ, ((D.e.symm (k⁻¹ * k') : ↥D.H) : MulAut E) = (F.r₀ * F.r₁) ^ j := by
    rcases hcases with h1 | h1 | h1 | h1
    · refine ⟨0, ?_⟩
      have : k⁻¹ * k' = 1 := Units.ext h1
      rw [this, map_one]
      rfl
    · refine ⟨1, ?_⟩
      have : k⁻¹ * k' = rhoU F D := Units.ext (h1.trans N.rho.symm)
      rw [this, hrho, pow_one]
    · refine ⟨2, ?_⟩
      have : k⁻¹ * k' = rhoU F D * rhoU F D := Units.ext (by simpa only [Units.val_mul, N.rho] using h1)
      rw [this, map_mul, Subgroup.coe_mul, hrho, pow_two]
    · refine ⟨3, ?_⟩
      have : k⁻¹ * k' = rhoU F D * rhoU F D * rhoU F D :=
        Units.ext (by simpa only [Units.val_mul, N.rho] using h1)
      rw [this, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hrho, pow_three']
  obtain ⟨j, hj⟩ := hj
  have hw'' : w⁻¹ * w' ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer (E : Set G)).mul_mem ((Subgroup.normalizer (E : Set G)).inv_mem hw) hw'
  have hlift : conjAut E (w⁻¹ * w') hw'' = (F.r₀ * F.r₁) ^ j := by
    rw [conjAut_mul' ((Subgroup.normalizer (E : Set G)).inv_mem hw) hw',
      Equivariance.conjAut_inv hw, hwe, hwe', ← hj, map_mul, map_inv]
    rfl
  have hfix := B.fix_of X hdvd hodd hw'' (by rw [hlift]; exact rho_comm_zp j)
    (by rw [hlift]; exact rho_pow_fix_c X j)
  rw [hS, hS']
  calc conjBy w B.R = conjBy w (conjBy (w⁻¹ * w') B.R) := by rw [hfix.1]
    _ = conjBy w' B.R := by rw [← conjBy_mul']; congr 1; group

theorem isIota_conj {x : GL (Fin 3) (ZMod 2)} {S : Subgroup G} (h : IsIota B x S)
    (hh : GL (Fin 3) (ZMod 2)) {w₂ : G} (hw₂ : w₂ ∈ Subgroup.normalizer (E : Set G))
    (hw₂e : conjAut E w₂ hw₂ = ((D.e.symm hh : ↥D.H) : MulAut E)) :
    IsIota B (hh * x * hh⁻¹) (conjBy w₂ S) := by
  obtain ⟨k, w, hw, hk, hwe, hS⟩ := h
  refine ⟨hh * k, w₂ * w, (Subgroup.normalizer (E : Set G)).mul_mem hw₂ hw, ?_, ?_, ?_⟩
  · rw [← hk]
    group
  · rw [conjAut_mul' hw₂ hw, hw₂e, hwe, map_mul]
    rfl
  · rw [hS, conjBy_mul']

include X in
theorem conjBy_y_R (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {y : G}
    (hy : y ∈ Subgroup.normalizer (E : Set G)) (hye : conjAut E y hy = D.ν) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) : conjBy y (conjBy w B.R) = conjBy w B.R' := by
  have hcomm_y : conjAut E y hy * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) =
      (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * conjAut E y hy := by
    rw [hye]
    exact (D.ν_comm _).symm
  have hc_y : conjAut E y hy X.cE = X.cE⁻¹ := by
    rw [hye]
    exact D.hν _
  have hRy : conjBy y B.R = B.R' := (B.swap_of X hdvd hodd hy hcomm_y hc_y).1
  obtain ⟨hd, hd1⟩ := conjAut_commutator hy hw (by
    rw [hye]
    exact (D.ν_comm _).symm)
  have hfd := (B.fix_of X hdvd hodd hd (by rw [hd1]; simp) (by rw [hd1]; rfl)).1
  have e1 : y * w = w * y * (y⁻¹ * w⁻¹ * y * w) := by group
  rw [← conjBy_mul', e1, conjBy_mul', conjBy_mul', hfd, hRy]

include X in
theorem isIota_inv (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {x : GL (Fin 3) (ZMod 2)}
    {S : Subgroup G} (h : IsIota B x S) {y : G} (hy : y ∈ Subgroup.normalizer (E : Set G))
    (hye : conjAut E y hy = D.ν) : IsIota B x⁻¹ (conjBy y S) ∧ conjBy y S ≠ S := by
  obtain ⟨k, w, hw, hk, hwe, hS⟩ := h
  obtain ⟨ua, hua, huae⟩ := D.exists_lift (a₁_mem F D)
  have hā : D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ * rhoU F D * (D.e ⟨D.ν * F.r₀, a₁_mem F D⟩)⁻¹ =
      (rhoU F D)⁻¹ := by
    have h1 : (⟨D.ν * F.r₀, a₁_mem F D⟩ : ↥D.H) * ⟨F.r₀ * F.r₁, rho_mem F D⟩ *
        (⟨D.ν * F.r₀, a₁_mem F D⟩ : ↥D.H)⁻¹ = (⟨F.r₀ * F.r₁, rho_mem F D⟩ : ↥D.H)⁻¹ := by
      apply Subtype.ext
      have hinv : (D.ν * F.r₀)⁻¹ = D.ν * F.r₀ := inv_eq_of_mul_eq_one_right (a₁_sq F D)
      show (D.ν * F.r₀) * (F.r₀ * F.r₁) * (D.ν * F.r₀)⁻¹ = (F.r₀ * F.r₁)⁻¹
      rw [hinv, a₁_rho, rho_inv_eq]
    unfold rhoU
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_inv]
  have hcomm_ua : conjAut E ua hua * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) =
      (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * conjAut E ua hua := by
    rw [huae]
    exact a₁_comm_zp
  have hc_ua : conjAut E ua hua X.cE = X.cE⁻¹ := by
    rw [huae]
    exact a₁_c X
  have hR1 : conjBy ua B.R = B.R' := (B.swap_of X hdvd hodd hua hcomm_ua hc_ua).1
  have hyS : conjBy y S = conjBy w B.R' := by rw [hS]; exact conjBy_y_R X B hdvd hodd hy hye hw
  refine ⟨⟨k * D.e ⟨D.ν * F.r₀, a₁_mem F D⟩, w * ua,
    (Subgroup.normalizer (E : Set G)).mul_mem hw hua, ?_, ?_, ?_⟩, ?_⟩
  · calc k * D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ * rhoU F D * (k * D.e ⟨D.ν * F.r₀, a₁_mem F D⟩)⁻¹
        = k * (D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ * rhoU F D * (D.e ⟨D.ν * F.r₀, a₁_mem F D⟩)⁻¹) *
          k⁻¹ := by group
      _ = k * (rhoU F D)⁻¹ * k⁻¹ := by rw [hā]
      _ = x⁻¹ := by rw [← hk]; group
  · rw [conjAut_mul' hw hua, hwe, huae, map_mul, MulEquiv.symm_apply_apply]
    rfl
  · rw [hyS, conjBy_mul', hR1]
  · rw [hyS, hS]
    intro heq
    have hinj : Function.Injective (conjBy w : Subgroup G → Subgroup G) :=
      Subgroup.map_injective (MulAut.conj w).injective
    exact B.R_ne (hinj heq).symm

theorem isIota_witness {x : GL (Fin 3) (ZMod 2)} {S : Subgroup G} (h : IsIota B x S) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), S = conjBy w B.R ∧
      D.ν * ((D.e.symm (x * x) : ↥D.H) : MulAut E) =
        conjAut E w hw * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) * (conjAut E w hw)⁻¹ := by
  obtain ⟨k, w, hw, hk, hwe, hS⟩ := h
  refine ⟨w, hw, hS, ?_⟩
  have hrho : ((D.e.symm (rhoU F D) : ↥D.H) : MulAut E) = F.r₀ * F.r₁ := by
    unfold rhoU
    rw [MulEquiv.symm_apply_apply]
  have hxx : x * x = k * (rhoU F D * rhoU F D) * k⁻¹ := by rw [← hk]; group
  have hxe : ((D.e.symm (x * x) : ↥D.H) : MulAut E) =
      ((D.e.symm k : ↥D.H) : MulAut E) * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) *
        ((D.e.symm k : ↥D.H) : MulAut E)⁻¹ := by
    rw [hxx]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hrho]
  rw [hxe, hwe]
  have hν := D.ν_comm ((D.e.symm k : ↥D.H) : MulAut E)
  calc D.ν * (((D.e.symm k : ↥D.H) : MulAut E) * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) *
          ((D.e.symm k : ↥D.H) : MulAut E)⁻¹)
      = (D.ν * ((D.e.symm k : ↥D.H) : MulAut E)) * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) *
          ((D.e.symm k : ↥D.H) : MulAut E)⁻¹ := by simp only [mul_assoc]
    _ = (((D.e.symm k : ↥D.H) : MulAut E) * D.ν) * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁)) *
          ((D.e.symm k : ↥D.H) : MulAut E)⁻¹ := by rw [hν]
    _ = ((D.e.symm k : ↥D.H) : MulAut E) * (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) *
          ((D.e.symm k : ↥D.H) : MulAut E)⁻¹ := by simp only [mul_assoc]

include X in
theorem Base.R_mem : B.R ∈ RootGp p E f (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) := by
  have h5 := X.five_le
  have h0 : F.rg 0 ∈ RootGp p E f F.r₀ := by
    rw [F.rootGp_r₀ h5]
    exact Set.mem_insert _ _
  have := conjBy_mem_rootGp (f := f) B.hu h0
  rwa [B.hconj] at this

include X in
theorem Base.rootGp_zp : RootGp p E f (D.ν * ((F.r₀ * F.r₁) * (F.r₀ * F.r₁))) = {B.R, B.R'} := by
  have h5 := X.five_le
  ext S
  rw [← B.hconj, RFrame.mem_rootGp_conj_iff B.hu, F.rootGp_r₀ h5]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hinj : Function.Injective (conjBy B.u : Subgroup G → Subgroup G) :=
    Subgroup.map_injective (MulAut.conj B.u).injective
  constructor
  · rintro (h | h)
    · left
      have := congrArg (conjBy B.u) h
      rw [Equivariance.conjBy_conjBy_inv] at this
      rw [this]
      rfl
    · right
      have := congrArg (conjBy B.u) h
      rw [Equivariance.conjBy_conjBy_inv] at this
      rw [this]
      rfl
  · rintro (h | h)
    · left
      have e' : conjBy B.u (F.rg 0) = B.R := rfl
      rw [h, ← e', Equivariance.conjBy_inv_conjBy]
    · right
      have e' : conjBy B.u (F.rg 4) = B.R' := rfl
      rw [h, ← e', Equivariance.conjBy_inv_conjBy]

include X in
theorem isIota_node {x : GL (Fin 3) (ZMod 2)} {S : Subgroup G} (h : IsIota B x S) :
    S ∈ RootGp p E f (D.ν * ((D.e.symm (x * x) : ↥D.H) : MulAut E)) := by
  obtain ⟨w, hw, hS, hn⟩ := isIota_witness B h
  rw [hS, hn]
  exact conjBy_mem_rootGp hw (B.R_mem X)

end Iota

end CFSG.RankThree.PartOne.NF7J
