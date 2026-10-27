module

public import CFSG.RankThree.PartOne.MB3.Plane

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Xdata (A : Subgroup G) (c : G) (L B : Subgroup G) (x : G) (lam : ℤ) : Prop where
  mem_L : x ∈ L
  cube : x ^ 3 = 1
  comm_c : x * c = c * x
  mem_normalizer_A : x ∈ Subgroup.normalizer (A : Set G)
  scalar : ∀ b ∈ B, x * b * x⁻¹ = b ^ lam
  not_dvd : ¬ (7 : ℤ) ∣ lam - 1

omit [Finite G] in
theorem closure_pair_eq_sup (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))

theorem exists_xdata {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ}
    (h : Sec109.Config p A c L B n) : ∃ (x : G) (lam : ℤ), Xdata A c L B x lam := by
  obtain ⟨b₁, b₂, x₁, x₂, x, -, -, -, -, -, hx₁L, hx₂L, hx₁N, hx₂N, ho₁, ho₂, hcom, -, -, hxcl,
    -, ⟨lam, hlam, hx⟩, -⟩ := h.structure_B
  have hle : Subgroup.closure ({x₁, x₂} : Set G) ≤ L := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hx₁L
    · exact hx₂L
  have hleN : Subgroup.closure ({x₁, x₂} : Set G) ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hx₁N
    · exact hx₂N
  have hxL : x ∈ L := hle hxcl
  have hxc : x * c = c * x := h.mem_L_comm_c hxL
  have hx₁3 : x₁ ^ 3 = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one x₁
  have hx₂3 : x₂ ^ 3 = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one x₂
  have hcube : x ^ 3 = 1 := by
    rw [closure_pair_eq_sup] at hxcl
    obtain ⟨s, t, rfl⟩ := (S11d.mem_zpowers_sup_zpowers_iff (show Commute x₁ x₂ from hcom)).mp hxcl
    rw [(Commute.zpow_zpow (show Commute x₁ x₂ from hcom) s t).mul_pow]
    have e1 : (x₁ ^ s) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx₁3, one_zpow]
    have e2 : (x₂ ^ t) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx₂3, one_zpow]
    rw [e1, e2, one_mul]
  exact ⟨x, lam, ⟨hxL, hcube, hxc, h.mem_normalizer_A (hleN hxcl) hxc, hx, hlam⟩⟩

omit [Finite G] in
theorem mem_zpowers_zpow_of_not_dvd {p : ℕ} (hp : p.Prime) {g : G} (hg : g ^ p = 1) {m : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) : g ∈ Subgroup.zpowers (g ^ m) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (p : ℤ) m := (Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hm
  obtain ⟨v, u, huv⟩ := hcop
  refine ⟨u, ?_⟩
  have h2 : g ^ (v * (p : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  calc (g ^ m) ^ u = g ^ (v * (p : ℤ) + u * m) := by
        rw [← zpow_mul, zpow_add, h2, one_mul, mul_comm]
    _ = g := by rw [huv, zpow_one]

theorem conj_mem_thetaQuotientCentralizer {p : ℕ} (hp : p.Prime) {A K : Subgroup G} {x d : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hd : d ∈ thetaQuotientCentralizer p A K) : x * d * x⁻¹ ∈ thetaQuotientCentralizer p A K := by
  obtain ⟨hdA, hdN, hdθ⟩ := mem_thetaQuotientCentralizer_iff.mp hd
  rw [mem_thetaQuotientCentralizer_iff]
  have hxθ : x ∈ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore p) K : Subgroup G) : Set G) :=
    le_normalizer_theta_of_le_normalizer hp (A := Subgroup.zpowers x)
      (Subgroup.zpowers_le.mpr hxK) (Subgroup.mem_zpowers x)
  refine ⟨(Subgroup.mem_normalizer_iff.mp hxA d).mp hdA, ?_, fun k hk => ?_⟩
  · exact (Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).mul_mem hxK hdN)
      ((Subgroup.normalizer (K : Set G)).inv_mem hxK)
  · set k₀ := x⁻¹ * k * x with hk₀
    have hk₀K : k₀ ∈ K := (Subgroup.mem_normalizer_iff.mp hxK k₀).mpr (by
      have : x * k₀ * x⁻¹ = k := by
        rw [hk₀]
        group
      rw [this]
      exact hk)
    have e : x * d * x⁻¹ * k * (x * d * x⁻¹)⁻¹ * k⁻¹ = x * (d * k₀ * d⁻¹ * k₀⁻¹) * x⁻¹ := by
      rw [hk₀]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hxθ _).mp (hdθ k₀ hk₀K)

omit [Finite G] in
theorem isQuasisimple_conjBy {K : Subgroup G} (hq : CFSG.IsQuasisimple K) (w : G) :
    CFSG.IsQuasisimple (conjBy w K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective) hq

theorem commute_of_ne_thetaComponents {p : ℕ} {b : G} {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ thetaComponentsAt p b) (h₂ : K₂ ∈ thetaComponentsAt p b)
    (hq₁ : CFSG.IsQuasisimple K₁) (hq₂ : CFSG.IsQuasisimple K₂) (hne : K₁ ≠ K₂) :
    ∀ k ∈ K₁, ∀ k' ∈ K₂, k * k' = k' * k := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hK₁C : K₁ ≤ C := (mem_thetaComponentsAt_iff.mp h₁).1
  have hK₂C : K₂ ≤ C := (mem_thetaComponentsAt_iff.mp h₂).1
  have hc₁ : CFSG.IsComponent (K₁.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK₁C).symm hq₁,
      isSubnormal_of_mem_thetaComponentsAt h₁⟩
  have hc₂ : CFSG.IsComponent (K₂.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK₂C).symm hq₂,
      isSubnormal_of_mem_thetaComponentsAt h₂⟩
  have hne' : K₁.subgroupOf C ≠ K₂.subgroupOf C := fun h => hne (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hK₁C, ← Subgroup.map_subgroupOf_eq_of_le hK₂C, h])
  have hcomm := (CFSG.LocalCores.distinct_components_commute hc₁ hc₂).resolve_left hne'
  intro k hk k' hk'
  have h1 : (⟨k, hK₁C hk⟩ : C) ∈ K₁.subgroupOf C := Subgroup.mem_subgroupOf.mpr hk
  have h2 : (⟨k', hK₂C hk'⟩ : C) ∈ K₂.subgroupOf C := Subgroup.mem_subgroupOf.mpr hk'
  have h3 : ⁅(⟨k, hK₁C hk⟩ : C), ⟨k', hK₂C hk'⟩⁆ ∈ ⁅K₁.subgroupOf C, K₂.subgroupOf C⁆ :=
    Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact congrArg Subtype.val h3

omit [Finite G] in
theorem conj_mem_conjBy {K : Subgroup G} {e : G} (he : e ∈ K) (w : G) :
    w * e * w⁻¹ ∈ conjBy w K := by
  rw [Equivariance.mem_conjBy]
  have : w⁻¹ * (w * e * w⁻¹) * w = e := by group
  rw [this]
  exact he

omit [Finite G] in
theorem conjBy_cube {x : G} (hx : x ^ 3 = 1) (K₀ : Subgroup G) :
    conjBy x (conjBy x (conjBy x K₀)) = K₀ := by
  have h3 : x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx
  ext y
  rw [Equivariance.mem_conjBy, Equivariance.mem_conjBy, Equivariance.mem_conjBy]
  have : x⁻¹ * (x⁻¹ * (x⁻¹ * y * x) * x) * x = (x * x * x)⁻¹ * y * (x * x * x) := by group
  rw [this, h3]
  simp

namespace Branch

variable {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ} {b : G} {S K K' : Subgroup G}
  {a' : G} (H : Branch p A c L B n b S K K' a') {x : G} {lam : ℤ} (X : Xdata A c L B x lam)

include H X

theorem not_dvd_lam_sub_one : ¬ (p : ℤ) ∣ lam - 1 := by
  rw [H.p_eq]
  exact_mod_cast X.not_dvd

theorem not_dvd_lam : ¬ (p : ℤ) ∣ lam := by
  intro hdvd
  have hb1 : b ≠ 1 := H.witness.b_ne_one
  obtain ⟨k, hk⟩ := hdvd
  apply hb1
  have h1 : b ^ lam = 1 := by rw [hk, zpow_mul, zpow_natCast, H.b_pow, one_zpow]
  have h2 : x * b * x⁻¹ = 1 := by rw [X.scalar b H.witness.b_mem, h1]
  simpa using h2

theorem x_notMem_normalizer_K : x ∉ Subgroup.normalizer (K : Set G) := by
  intro hxK
  have hlam := H.not_dvd_lam_sub_one X
  have ha'' : x * a' * x⁻¹ ∈ thetaQuotientCentralizer p A K :=
    conj_mem_thetaQuotientCentralizer H.prime X.mem_normalizer_A hxK H.a'_mem_D
  obtain ⟨β, hβB, j, hj⟩ := H.config.exists_decomp H.a'_mem
  have hβA : β ∈ A := H.config.B_le_A hβB
  have hcp : c ^ p = 1 := H.config.pow_p_eq_one H.config.c_mem
  have hβp : β ^ p = 1 := H.config.pow_p_eq_one hβA
  have hxc : x * c * x⁻¹ = c := by
    rw [X.comm_c]
    group
  have hxcj : x * c ^ j * x⁻¹ = c ^ j := by
    rw [← conj_zpow, hxc]
  have e1 : x * a' * x⁻¹ = β ^ lam * c ^ j := by
    rw [hj]
    calc x * (β * c ^ j) * x⁻¹ = (x * β * x⁻¹) * (x * c ^ j * x⁻¹) := by group
      _ = β ^ lam * c ^ j := by rw [X.scalar β hβB, hxcj]
  have hγ : β ^ (lam - 1) ∈ thetaQuotientCentralizer p A K := by
    have h1 := (thetaQuotientCentralizer p A K).mul_mem ha''
      ((thetaQuotientCentralizer p A K).inv_mem H.a'_mem_D)
    have e2 : x * a' * x⁻¹ * a'⁻¹ = β ^ (lam - 1) := by
      rw [e1, hj, zpow_sub_one]
      group
    rwa [e2] at h1
  have hβD : β ∈ thetaQuotientCentralizer p A K :=
    (Subgroup.zpowers_le.mpr hγ) (mem_zpowers_zpow_of_not_dvd H.prime hβp hlam)
  have hcjD : c ^ j ∈ thetaQuotientCentralizer p A K := by
    have h1 := (thetaQuotientCentralizer p A K).mul_mem
      ((thetaQuotientCentralizer p A K).inv_mem hβD) H.a'_mem_D
    have e3 : β⁻¹ * a' = c ^ j := by
      rw [hj]
      group
    rwa [e3] at h1
  have hj7 : ¬ (p : ℤ) ∣ j := by
    intro hdvd
    obtain ⟨m, hm⟩ := hdvd
    apply H.a'_notMem
    have h1 : c ^ j = 1 := by rw [hm, zpow_mul, zpow_natCast, hcp, one_zpow]
    rw [hj, h1, mul_one]
    exact hβB
  exact H.c_notMem_D
    ((Subgroup.zpowers_le.mpr hcjD) (mem_zpowers_zpow_of_not_dvd H.prime hcp hj7))

theorem K₁_mem : conjBy x K ∈ thetaComponentsAt p b :=
  S11d.conjBy_mem_thetaComponentsAt_of_zpow H.prime H.K_mem.2 H.b_pow (H.not_dvd_lam X)
    (X.scalar b H.witness.b_mem)

theorem K₂_mem : conjBy x (conjBy x K) ∈ thetaComponentsAt p b :=
  S11d.conjBy_mem_thetaComponentsAt_of_zpow H.prime (H.K₁_mem X) H.b_pow (H.not_dvd_lam X)
    (X.scalar b H.witness.b_mem)

theorem K₁_ne : conjBy x K ≠ K := fun h =>
  H.x_notMem_normalizer_K X (by rw [Subgroup.mem_normalizer_iff_map_conj_eq]; exact h)

theorem K₂_ne_K : conjBy x (conjBy x K) ≠ K := fun h => by
  have h1 : conjBy x (conjBy x (conjBy x K)) = conjBy x K := by rw [h]
  rw [conjBy_cube X.cube] at h1
  exact H.K₁_ne X h1.symm

theorem K₂_ne_K₁ : conjBy x (conjBy x K) ≠ conjBy x K := fun h => by
  have hx₁ : x ∈ Subgroup.normalizer ((conjBy x K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h
  have h1 : conjBy x⁻¹ (conjBy x K) = conjBy x K :=
    Equivariance.conjBy_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hx₁)
  rw [Equivariance.conjBy_inv_conjBy] at h1
  exact H.K₁_ne X h1.symm

theorem comm₀₁ (hq : CFSG.IsQuasisimple K) :
    ∀ k ∈ K, ∀ k' ∈ conjBy x K, k * k' = k' * k :=
  commute_of_ne_thetaComponents H.K_mem.2 (H.K₁_mem X) hq (isQuasisimple_conjBy hq x)
    (H.K₁_ne X).symm

theorem comm₀₂ (hq : CFSG.IsQuasisimple K) :
    ∀ k ∈ K, ∀ k' ∈ conjBy x (conjBy x K), k * k' = k' * k :=
  commute_of_ne_thetaComponents H.K_mem.2 (H.K₂_mem X) hq
    (isQuasisimple_conjBy (isQuasisimple_conjBy hq x) x) (H.K₂_ne_K X).symm

theorem comm₁₂ (hq : CFSG.IsQuasisimple K) :
    ∀ k ∈ conjBy x K, ∀ k' ∈ conjBy x (conjBy x K), k * k' = k' * k :=
  commute_of_ne_thetaComponents (H.K₁_mem X) (H.K₂_mem X) (isQuasisimple_conjBy hq x)
    (isQuasisimple_conjBy (isQuasisimple_conjBy hq x) x) (H.K₂_ne_K₁ X).symm

end Branch

end CFSG.RankThree.PartOne.MB3
