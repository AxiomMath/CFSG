module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.FTL

open Subgroup CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

theorem commute_of_powerMap {V : Type*} [Group V] {α β : MulAut V} {k : ℕ}
    (hα : ∀ v : V, α v = v ^ k) : α * β = β * α := by
  refine MulEquiv.ext fun v => ?_
  change α (β v) = β (α v)
  rw [hα, hα, map_pow]

theorem mk_commute_iff {E V : Type*} [Group E] [Group V] (σ : E →* MulAut V) (x y : E) :
    ((x : E ⧸ σ.ker) * (y : E ⧸ σ.ker) = (y : E ⧸ σ.ker) * (x : E ⧸ σ.ker)) ↔
      σ x * σ y = σ y * σ x := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, MonoidHom.mem_ker,
    map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul]

theorem hom_trivial_of_scalar {E V : Type*} [Group E] [Group V] (hE : CFSG.IsQuasisimple E)
    {d : E} (hd : d ∉ Subgroup.center E) (σ : E →* MulAut V)
    (hs : ∃ k : ℕ, ∀ v : V, σ d v = v ^ k) : ∀ e : E, σ e = 1 := by
  obtain ⟨k, hk⟩ := hs
  have hKn : σ.ker.Normal := σ.normal_ker
  set C : Subgroup E := (Subgroup.center (E ⧸ σ.ker)).comap (QuotientGroup.mk' σ.ker) with hC
  have hCn : C.Normal := Subgroup.Normal.comap inferInstance _
  have hdC : d ∈ C := by
    rw [hC, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
    have h := (mk_commute_iff σ e d).mpr (commute_of_powerMap (α := σ d) (β := σ e) hk).symm
    simpa [QuotientGroup.mk'_apply] using h
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hE hCn with htop | hle
  · have hcomm : ∀ x y : E, σ x * σ y = σ y * σ x := by
      intro x y
      have hx : x ∈ C := htop ▸ Subgroup.mem_top x
      rw [hC, Subgroup.mem_comap, Subgroup.mem_center_iff] at hx
      have h := hx (y : E ⧸ σ.ker)
      have h2 : ((y : E ⧸ σ.ker) * (x : E ⧸ σ.ker) = (x : E ⧸ σ.ker) * (y : E ⧸ σ.ker)) := by
        simpa [QuotientGroup.mk'_apply] using h
      exact ((mk_commute_iff σ y x).mp h2).symm
    have hker : (⊤ : Subgroup E) ≤ σ.ker := by
      have hperf : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ := by
        have := hE.1.commutator_eq_top
        rwa [_root_.commutator_def] at this
      rw [← hperf, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h := hcomm x y
      calc σ x * σ y * (σ x)⁻¹ * (σ y)⁻¹ = (σ x * σ y) * ((σ x)⁻¹ * (σ y)⁻¹) := by group
        _ = (σ y * σ x) * ((σ x)⁻¹ * (σ y)⁻¹) := by rw [h]
        _ = 1 := by group
    intro e
    exact (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top e)))
  · exact absurd (hle hdC) hd

theorem eq_one_of_trivial_mod_frattini {q : ℕ} [Fact q.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup q P) {τ : MulAut P} {m : ℕ} (hτ : τ ^ m = 1) (hcop : Nat.Coprime m q)
    (htriv : quotientAutomorphism (frattini P) τ = 1) : τ = 1 := by
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel (p := q) hP
  have hmem : τ ∈ (quotientAutomorphism (frattini P)).ker := htriv
  obtain ⟨j, hj⟩ := hker ⟨τ, hmem⟩
  have hj' : τ ^ (q ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hcop' : Nat.Coprime m (q ^ j) := Nat.Coprime.pow_right j hcop
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτ) (orderOf_dvd_of_pow_eq_one hj')
  rw [hcop'.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

theorem centralizes_of_scalar_action {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hqp : q ≠ p) {E X : Subgroup G} {d : G} (hEq : CFSG.IsQuasisimple ↥E)
    (hdE : d ∈ E) (hdnc : ∃ e ∈ E, d * e ≠ e * d) (hEX : E ≤ normalizer (X : Set G))
    (hXq : IsPGroup q ↥X) (hdp : d ^ p = 1)
    (hscalar : ∃ k : ℕ, ∀ x ∈ X, (d * x * d⁻¹)⁻¹ * x ^ k ∈ inSubgroup frattini X) :
    ∀ x ∈ X, d * x * d⁻¹ = x := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hscalar
  let ψ : ↥E →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hEX)
  have hψ : ∀ (e : ↥E) (x : ↥X), ((ψ e x : ↥X) : G) = (e : G) * x * (e : G)⁻¹ := fun _ _ => rfl
  let σ : ↥E →* MulAut (↥X ⧸ frattini ↥X) := (quotientAutomorphism (frattini ↥X)).comp ψ
  have hdnc' : (⟨d, hdE⟩ : ↥E) ∉ Subgroup.center ↥E := by
    intro hc
    obtain ⟨e, he, hne⟩ := hdnc
    exact hne (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) ⟨e, he⟩).symm)
  have hs : ∃ k : ℕ, ∀ v : ↥X ⧸ frattini ↥X, σ ⟨d, hdE⟩ v = v ^ k := by
    refine ⟨k, fun v => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    change quotientAutomorphism (frattini ↥X) (ψ ⟨d, hdE⟩) (QuotientGroup.mk' (frattini ↥X) x) =
      (QuotientGroup.mk' (frattini ↥X) x) ^ k
    rw [quotientAutomorphism_apply, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h := hk x x.2
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h
    have hyeq' : (y : G) = (d * (x : G) * d⁻¹)⁻¹ * (x : G) ^ k := hyeq
    have : y = ((ψ ⟨d, hdE⟩ x)⁻¹ * x ^ k) := by
      apply Subtype.ext
      rw [hyeq']
      simp [hψ]
    rw [← this]
    exact hy
  have htriv := hom_trivial_of_scalar hEq hdnc' σ hs ⟨d, hdE⟩
  have hτ : (ψ ⟨d, hdE⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨d, hdE⟩ : ↥E) ^ p = 1 := Subtype.ext (by simpa using hdp)
    rw [this, map_one]
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (Ne.symm hqp)
  have hτ1 : ψ ⟨d, hdE⟩ = 1 :=
    eq_one_of_trivial_mod_frattini hXq hτ hcop htriv
  intro x hx
  have := congrArg (fun τ : MulAut ↥X => ((τ ⟨x, hx⟩ : ↥X) : G)) hτ1
  simpa [hψ] using this

theorem le_centralizer_of_mem_centralizer {G : Type} [Group G] {E M : Subgroup G}
    (hEq : CFSG.IsQuasisimple ↥E) {d : G} (hdE : d ∈ E) (hdnc : ∃ e ∈ E, d * e ≠ e * d)
    (hEM : E ≤ normalizer (M : Set G)) (hd : d ∈ Subgroup.centralizer (M : Set G)) :
    E ≤ Subgroup.centralizer (M : Set G) := by
  set N : Subgroup ↥E := (Subgroup.centralizer (M : Set G)).subgroupOf E with hN
  have hNn : N.Normal := by
    refine ⟨fun h hh g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hh ⊢
    rw [Subgroup.mem_centralizer_iff] at hh ⊢
    intro x hx
    have hg : (g : G) ∈ normalizer (M : Set G) := hEM g.2
    have hx' : (g : G)⁻¹ * x * (g : G) ∈ M := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa using this
    have h1 := hh _ hx'
    change x * ((g : G) * (h : G) * (g : G)⁻¹) = ((g : G) * (h : G) * (g : G)⁻¹) * x
    calc x * ((g : G) * (h : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * x * (g : G)) * (h : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((h : G) * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * (h : G) * (g : G)⁻¹) * x := by group
  have hdnc' : (⟨d, hdE⟩ : ↥E) ∉ Subgroup.center ↥E := by
    intro hc
    obtain ⟨e, he, hne⟩ := hdnc
    exact hne (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) ⟨e, he⟩).symm)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hEq hNn with htop | hle
  · intro e he
    have : (⟨e, he⟩ : ↥E) ∈ N := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this)
  · exact absurd (hle (show (⟨d, hdE⟩ : ↥E) ∈ N from Subgroup.mem_subgroupOf.mpr hd)) hdnc'

end CFSG.RankThree.PartOne.FTL
