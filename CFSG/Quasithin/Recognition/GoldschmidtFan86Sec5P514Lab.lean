module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PConj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def lab (T : Track Γ G) (z : G) (j : ℤ) : G := T.τ ^ j * z * T.τ ^ (-j)

theorem lab_lab (T : Track Γ G) (z : G) (j k : ℤ) : lab T (lab T z j) k = lab T z (j + k) := by
  simp only [lab]
  rw [zpow_add, neg_add, zpow_add]
  group

theorem lab_mul (T : Track Γ G) (z w : G) (j : ℤ) :
    lab T (z * w) j = lab T z j * lab T w j := by
  simp only [lab]
  group

theorem lab_mul_self (T : Track Γ G) {z : G} (hz : z * z = 1) (j : ℤ) :
    lab T z j * lab T z j = 1 := by
  rw [← lab_mul, hz]
  simp [lab]

theorem lab_ne_one (T : Track Γ G) {z : G} (hz : z ≠ 1) (j : ℤ) : lab T z j ≠ 1 := by
  intro h
  apply hz
  have : T.τ ^ (-j) * (T.τ ^ j * z * T.τ ^ (-j)) * T.τ ^ j = z := by group
  rw [lab] at h
  rw [h] at this
  simpa using this.symm

theorem inv_tau_zpow_smul_vert (T : Track Γ G) (j i : ℤ) :
    T.τ ^ (-j) • T.line.vert i = T.line.vert (i - 2 * j) := by
  rw [T.zpow_smul_vert]
  congr 1
  omega

theorem lab_smul_iff (T : Track Γ G) (z : G) (j i : ℤ) :
    lab T z j • T.line.vert i = T.line.vert i ↔
      z • T.line.vert (i - 2 * j) = T.line.vert (i - 2 * j) := by
  have h1 : T.τ ^ j • T.line.vert (i - 2 * j) = T.line.vert i := by
    rw [T.zpow_smul_vert]
    congr 1
    omega
  constructor
  · intro h
    have h2 : T.τ ^ j • (z • T.line.vert (i - 2 * j)) = T.τ ^ j • T.line.vert (i - 2 * j) := by
      rw [h1]
      have : lab T z j • T.line.vert i = T.τ ^ j • (z • T.line.vert (i - 2 * j)) := by
        simp only [lab, mul_smul]
        rw [← inv_tau_zpow_smul_vert T j i]
      rw [← this, h]
    exact MulAction.injective _ h2
  · intro h
    rw [← inv_tau_zpow_smul_vert T j i] at h
    simp only [lab, mul_smul]
    rw [h, ← mul_smul]
    simp

theorem mem_fixIdx_lab (T : Track Γ G) (z : G) (j i : ℤ) :
    i ∈ T.line.fixIdx (lab T z j) ↔ i - 2 * j ∈ T.line.fixIdx z :=
  lab_smul_iff T z j i

theorem conj_mem_Cen {S S' : Set G} (k : G) (hS : ∀ g, g ∈ S' ↔ k⁻¹ * g * k ∈ S) (z : G) :
    k * z * k⁻¹ ∈ Cen S' ↔ z ∈ Cen S := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h hh => ?_⟩
    · have := (hS _).1 h1
      simpa [mul_assoc] using this
    · have h3 := h2 (k * h * k⁻¹) ((hS _).2 (by simpa [mul_assoc] using hh))
      have h4 : k * (h * z) * k⁻¹ = k * (z * h) * k⁻¹ := by
        simpa [mul_assoc] using h3
      simpa using h4
  · rintro ⟨h1, h2⟩
    refine ⟨(hS _).2 (by simpa [mul_assoc] using h1), fun h hh => ?_⟩
    have hh' := (hS _).1 hh
    have h3 := h2 _ hh'
    have h4 : k * (k⁻¹ * h * k * z) * k⁻¹ = k * (z * (k⁻¹ * h * k)) * k⁻¹ := by rw [h3]
    simpa [mul_assoc] using h4

theorem conj_smul_iff (k g : G) (u : V) : g • k • u = k • u ↔ (k⁻¹ * g * k) • u = u := by
  constructor
  · intro h
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · intro h
    rw [show g • k • u = k • (k⁻¹ * g * k) • u by simp [mul_smul], h]

theorem mem_nbrStab_smul_iff (F : FanTree Γ G) (k : G) (u : V) (z : G) :
    z ∈ nbrStab Γ G (k • u) ↔ k⁻¹ * z * k ∈ nbrStab Γ G u := by
  constructor
  · intro h
    have := F.conj_mem_nbrStab_smul k⁻¹ h
    rwa [inv_smul_smul, inv_inv] at this
  · intro h
    have := F.conj_mem_nbrStab_smul k h
    simpa [mul_assoc] using this

theorem mem_Gcirc_smul_iff (F : FanTree Γ G) (k : G) (u v : V) (g : G) :
    g ∈ Gcirc Γ G (k • u) (k • v) ↔ k⁻¹ * g * k ∈ Gcirc Γ G u v := by
  simp only [mem_Gcirc, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rw [conj_smul_iff, conj_smul_iff, mem_nbrStab_smul_iff F]
  have : k⁻¹ * (g * g) * k = (k⁻¹ * g * k) * (k⁻¹ * g * k) := by group
  rw [this]

theorem valence_vert_add_two_mul (F : FanTree Γ G) (ℓ : Line Γ) (i j : ℤ) :
    valence Γ (ℓ.vert (i + 2 * j)) = valence Γ (ℓ.vert i) := by
  induction j using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show i + 2 * ((n : ℤ) + 1) = (i + 2 * n) + 2 by omega, ℓ.valence_add_two F, ih]
  | pred n ih =>
    have := ℓ.valence_add_two F (i + 2 * (-(n : ℤ) - 1))
    rw [show i + 2 * (-(n : ℤ) - 1) + 2 = i + 2 * (-(n : ℤ)) by omega] at this
    exact this.symm.trans ih

theorem mem_edgeStab_lab_iff (T : Track Γ G) (j i : ℤ) (g : G) :
    g ∈ T.line.edgeStab (G := G) (i + 2 * j) ↔
      T.τ ^ (-j) * g * T.τ ^ j ∈ T.line.edgeStab (G := G) i := by
  have e0 : T.line.vert (i + 2 * j) = T.τ ^ j • T.line.vert i := by
    rw [T.zpow_smul_vert]
  have e1 : T.line.vert (i + 2 * j + 1) = T.τ ^ j • T.line.vert (i + 1) := by
    rw [T.zpow_smul_vert]
    congr 1
    omega
  have hk : (T.τ ^ j)⁻¹ = T.τ ^ (-j) := (zpow_neg _ _).symm
  simp only [Line.edgeStab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rw [e0, e1, conj_smul_iff, conj_smul_iff, hk]

theorem mem_edgeCirc_lab_iff (F : FanTree Γ G) (T : Track Γ G) (j i : ℤ) (g : G) :
    g ∈ T.line.edgeCirc (G := G) (i + 2 * j) ↔
      T.τ ^ (-j) * g * T.τ ^ j ∈ T.line.edgeCirc (G := G) i := by
  have e0 : T.line.vert (i + 2 * j) = T.τ ^ j • T.line.vert i := by
    rw [T.zpow_smul_vert]
  have e1 : T.line.vert (i + 2 * j + 1) = T.τ ^ j • T.line.vert (i + 1) := by
    rw [T.zpow_smul_vert]
    congr 1
    omega
  have hk : (T.τ ^ j)⁻¹ = T.τ ^ (-j) := (zpow_neg _ _).symm
  have hv := valence_vert_add_two_mul F T.line i j
  by_cases h5 : valence Γ (T.line.vert i) = 5
  · rw [T.line.edgeCirc_of_five (hv.trans h5), T.line.edgeCirc_of_five h5, e0, e1,
      mem_Gcirc_smul_iff F, hk]
  · rw [T.line.edgeCirc_of_ne_five (fun h => h5 (hv.symm.trans h)),
      T.line.edgeCirc_of_ne_five h5, e0, e1, mem_Gcirc_smul_iff F, hk]

theorem lab_mem_Cen_edgeStab (T : Track Γ G) (z : G) (j i : ℤ) :
    lab T z j ∈ Cen (T.line.edgeStab (G := G) (i + 2 * j) : Set G) ↔
      z ∈ Cen (T.line.edgeStab (G := G) i : Set G) := by
  have hk : (T.τ ^ j)⁻¹ = T.τ ^ (-j) := (zpow_neg _ _).symm
  have := conj_mem_Cen (S := (T.line.edgeStab (G := G) i : Set G))
    (S' := (T.line.edgeStab (G := G) (i + 2 * j) : Set G)) (T.τ ^ j) (fun g => by
      rw [SetLike.mem_coe, SetLike.mem_coe, mem_edgeStab_lab_iff, hk]) z
  rwa [hk] at this

theorem lab_mem_Cen_edgeCirc (F : FanTree Γ G) (T : Track Γ G) (z : G) (j i : ℤ) :
    lab T z j ∈ Cen (T.line.edgeCirc (G := G) (i + 2 * j)) ↔
      z ∈ Cen (T.line.edgeCirc (G := G) i) := by
  have hk : (T.τ ^ j)⁻¹ = T.τ ^ (-j) := (zpow_neg _ _).symm
  have := conj_mem_Cen (S := T.line.edgeCirc (G := G) i)
    (S' := T.line.edgeCirc (G := G) (i + 2 * j)) (T.τ ^ j) (fun g => by
      rw [mem_edgeCirc_lab_iff F, hk]) z
  rwa [hk] at this

theorem lab_mem_ZZ (T : Track Γ G) {z : G} (hz : z ∈ T.line.ZZ) (j : ℤ) :
    lab T z j ∈ T.line.ZZ := by
  obtain ⟨h1, i, hi⟩ := hz
  exact ⟨lab_mul_self T h1 j, i + 2 * j, (lab_mem_Cen_edgeStab T z j i).2 hi⟩

theorem lab_mem_Zc (F : FanTree Γ G) (T : Track Γ G) {z : G} (hz : z ∈ T.line.Zc) (j : ℤ) :
    lab T z j ∈ T.line.Zc := by
  obtain ⟨h1, i, hi⟩ := hz
  exact ⟨lab_mul_self T h1 j, i + 2 * j, (lab_mem_Cen_edgeCirc F T z j i).2 hi⟩

theorem isCoreWith_lab (T : Track Γ G) {P P' : ℤ → Prop} (j : ℤ)
    (hP : ∀ i, P' (i + 2 * j) ↔ P i) {z : G} {a b : ℤ} (h : T.line.IsCoreWith P z a b) :
    T.line.IsCoreWith P' (lab T z j) (a + 2 * j) (b + 2 * j) := by
  obtain ⟨hab, hfix, hP1, hn1, hn2⟩ := h
  refine ⟨by omega, fun i h1 h2 => ?_, fun i h1 h2 => ?_, ?_, ?_⟩
  · rw [mem_fixIdx_lab]
    exact hfix _ (by omega) (by omega)
  · have h3 := (hP (i - 2 * j)).2 (hP1 (i - 2 * j) (by omega) (by omega))
    rwa [sub_add_cancel] at h3
  · rintro ⟨h1, h2⟩
    rw [mem_fixIdx_lab] at h1
    refine hn1 ⟨by simpa [show a + 2 * j - 1 - 2 * j = a - 1 by omega] using h1, ?_⟩
    have := (hP (a - 1)).1 (by simpa [show a - 1 + 2 * j = a + 2 * j - 1 by omega] using h2)
    exact this
  · rintro ⟨h1, h2⟩
    rw [mem_fixIdx_lab] at h1
    refine hn2 ⟨by simpa using h1, ?_⟩
    exact (hP b).1 (by simpa using h2)

theorem isCore_lab (T : Track Γ G) {z : G} (j : ℤ) {a b : ℤ} (h : T.line.IsCore z a b) :
    T.line.IsCore (lab T z j) (a + 2 * j) (b + 2 * j) :=
  isCoreWith_lab T j (fun i => lab_mem_Cen_edgeStab T z j i) h

theorem isCoreC_lab (F : FanTree Γ G) (T : Track Γ G) {z : G} (j : ℤ) {a b : ℤ}
    (h : T.line.IsCoreC z a b) : T.line.IsCoreC (lab T z j) (a + 2 * j) (b + 2 * j) :=
  isCoreWith_lab T j (fun i => lab_mem_Cen_edgeCirc F T z j i) h

theorem isCoreFix_lab (T : Track Γ G) {z : G} (j : ℤ) {a b tL tR : ℤ}
    (h : T.line.IsCoreFix z a b tL tR) :
    T.line.IsCoreFix (lab T z j) (a + 2 * j) (b + 2 * j) (tL + 2 * j) (tR + 2 * j) :=
  ⟨fun i => by rw [mem_fixIdx_lab, h.fix]; omega, isCore_lab T j h.core⟩

theorem isCoreCFix_lab (F : FanTree Γ G) (T : Track Γ G) {z : G} (j : ℤ) {a b tL tR : ℤ}
    (h : T.line.IsCoreCFix z a b tL tR) :
    T.line.IsCoreCFix (lab T z j) (a + 2 * j) (b + 2 * j) (tL + 2 * j) (tR + 2 * j) :=
  ⟨fun i => by rw [mem_fixIdx_lab, h.fix]; omega, isCoreC_lab F T j h.core⟩

end P514

end CFSG.Quasithin.Fan86
