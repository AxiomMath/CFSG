module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open scoped Pointwise

theorem mul_self_of_sq {Q : Type*} [Group Q] {x : Q} (hx : x ^ 2 = 1) : x * x = 1 := by
  rw [← sq, hx]

theorem inv_eq_of_sq {Q : Type*} [Group Q] {x : Q} (hx : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left (mul_self_of_sq hx)

theorem mem_range_six {Q : Type*} [Group Q] {x y : Q} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : (x * y) ^ 3 = 1) {q : Q} (hq : q ∈ Subgroup.closure {x, y}) :
    q ∈ Set.range ![1, x, y, x * y, y * x, x * y * x] := by
  have hxx := mul_self_of_sq hx
  have hyy := mul_self_of_sq hy
  have hbr : x * y * x = y * x * y := by
    have h : x * y * x * (y * x * y) = 1 := by
      rw [← hxy]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have h2 := eq_inv_of_mul_eq_one_left h
    rw [h2, mul_inv_rev, mul_inv_rev, inv_eq_of_sq hx, inv_eq_of_sq hy, mul_assoc]
  have step : ∀ g ∈ ({x, y} : Set Q), ∀ r ∈ Set.range ![1, x, y, x * y, y * x, x * y * x],
      g * r ∈ Set.range ![1, x, y, x * y, y * x, x * y * x] := by
    rintro g hg r ⟨i, rfl⟩
    rcases hg with hg | hg <;> subst g
    · fin_cases i
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hxx]⟩
      · exact ⟨3, by simp⟩
      · exact ⟨2, by simp [← mul_assoc, hxx]⟩
      · exact ⟨5, by simp [mul_assoc]⟩
      · exact ⟨4, by simp [← mul_assoc, hxx]⟩
    · fin_cases i
      · exact ⟨2, by simp⟩
      · exact ⟨4, by simp⟩
      · exact ⟨0, by simp [hyy]⟩
      · exact ⟨5, by simp [← mul_assoc, hbr]⟩
      · exact ⟨1, by simp [← mul_assoc, hyy]⟩
      · refine ⟨3, ?_⟩
        change x * y = y * (x * y * x)
        rw [hbr, ← mul_assoc, ← mul_assoc, hyy, one_mul]
  induction hq using Subgroup.closure_induction_left with
  | one => exact ⟨0, by simp⟩
  | mul_left g hg r _ ih => exact step g hg r ih
  | inv_mul_cancel g hg r _ ih =>
    have hg' : g⁻¹ = g := by
      rcases hg with rfl | rfl
      · exact inv_eq_of_sq hx
      · exact inv_eq_of_sq hy
    rw [hg']
    exact step g hg r ih

theorem index_le_six {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {α β : G}
    (hα : α ^ 2 ∈ N) (hβ : β ^ 2 ∈ N) (hαβ : (α * β) ^ 3 ∈ N)
    (hgen : N ⊔ Subgroup.zpowers α ⊔ Subgroup.zpowers β = ⊤) : N.index ≤ 6 ∧ N.index ≠ 0 := by
  set x : G ⧸ N := QuotientGroup.mk α
  set y : G ⧸ N := QuotientGroup.mk β
  have hx : x ^ 2 = 1 := (QuotientGroup.eq_one_iff _).2 hα
  have hy : y ^ 2 = 1 := (QuotientGroup.eq_one_iff _).2 hβ
  have hxy : (x * y) ^ 3 = 1 := (QuotientGroup.eq_one_iff _).2 hαβ
  have hcl : Subgroup.closure {x, y} = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgen
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, QuotientGroup.range_mk'] at h
    refine eq_top_iff.2 (h ▸ sup_le (sup_le ?_ ?_) ?_)
    · rw [Subgroup.map_le_iff_le_comap]
      intro n hn
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn]
      exact one_mem _
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hsurj : Function.Surjective (![1, x, y, x * y, y * x, x * y * x] : Fin 6 → G ⧸ N) :=
    fun q => mem_range_six hx hy hxy (hcl ▸ Subgroup.mem_top q)
  have : Finite (G ⧸ N) := Finite.of_surjective _ hsurj
  rw [Subgroup.index_eq_card]
  exact ⟨(Nat.card_le_card_of_surjective _ hsurj).trans (by rw [Nat.card_eq_fintype_card,
    Fintype.card_fin]), Nat.card_pos.ne'⟩

theorem le_normalizer_of_conj {G : Type*} [Group G] {M H : Subgroup G}
    (h : ∀ g ∈ M, ∀ x ∈ H, g * x * g⁻¹ ∈ H) : M ≤ Subgroup.normalizer (H : Set G) :=
  fun g hg => Subgroup.mem_normalizer_iff.2 fun x => ⟨h g hg x, fun hx => by
    have := h g⁻¹ (M.inv_mem hg) _ hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this⟩

theorem exists_mul_zpow_of_mem_sup {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {c x : X}
    (hx : x ∈ K ⊔ Subgroup.zpowers c) : ∃ k ∈ K, ∃ n : ℤ, x = k * c ^ n := by
  have hx' : x ∈ (K : Set X) * (Subgroup.zpowers c : Set X) := by
    rw [← Subgroup.normal_mul]
    exact hx
  obtain ⟨k, hk, z, hz, rfl⟩ := hx'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ⟨k, hk, n, rfl⟩

theorem exists_unique_extend_of_sThree {X Y : Type*} [Group X] [Group Y] {K A₁ A₂ : Subgroup X}
    [K.Normal] {a b : X} (hA₁ : A₁ = K ⊔ Subgroup.zpowers a) (hA₂ : A₂ = K ⊔ Subgroup.zpowers b)
    (ha : a ^ 2 ∈ K) (hb : b ^ 2 ∈ K) (hab : (a * b) ^ 3 ∈ K)
    (hgen : K ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b = ⊤) (hidx : K.index = 6)
    (f₁ : A₁ →* Y) (f₂ : A₂ →* Y)
    (hf : ∀ (k : X) (h₁ : k ∈ A₁) (h₂ : k ∈ A₂), k ∈ K → f₁ ⟨k, h₁⟩ = f₂ ⟨k, h₂⟩)
    (hrel : ∀ (h₁ : a ∈ A₁) (h₂ : b ∈ A₂) (h₃ : (a * b) ^ 3 ∈ A₁),
      (f₁ ⟨a, h₁⟩ * f₂ ⟨b, h₂⟩) ^ 3 = f₁ ⟨(a * b) ^ 3, h₃⟩) :
    ∃! f : X →* Y, f.comp A₁.subtype = f₁ ∧ f.comp A₂.subtype = f₂ := by
  have hK₁ : K ≤ A₁ := hA₁ ▸ le_sup_left
  have hK₂ : K ≤ A₂ := hA₂ ▸ le_sup_left
  have ha₁ : a ∈ A₁ := hA₁ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hb₂ : b ∈ A₂ := hA₂ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have htop : A₁ ⊔ A₂ = ⊤ := top_le_iff.1 (hgen ▸ sup_le (sup_le (hK₁.trans le_sup_left)
    ((Subgroup.zpowers_le.2 ha₁).trans le_sup_left))
      ((Subgroup.zpowers_le.2 hb₂).trans le_sup_right))
  let g₁ : A₁ →* X × Y := A₁.subtype.prod f₁
  let g₂ : A₂ →* X × Y := A₂.subtype.prod f₂
  let gK : K →* X × Y := K.subtype.prod (f₁.comp (Subgroup.inclusion hK₁))
  let ΓK : Subgroup (X × Y) := gK.range
  let Γ : Subgroup (X × Y) := g₁.range ⊔ g₂.range
  have hgK₁ : ∀ k : K, gK k = g₁ (Subgroup.inclusion hK₁ k) := fun k => rfl
  have hgK₂ : ∀ k : K, gK k = g₂ (Subgroup.inclusion hK₂ k) := fun k =>
    Prod.ext rfl (hf k (hK₁ k.2) (hK₂ k.2) k.2)
  have hΓK₁ : ΓK ≤ g₁.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, (hgK₁ k).symm⟩
  have hΓK₂ : ΓK ≤ g₂.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, (hgK₂ k).symm⟩
  have hΓKΓ : ΓK ≤ Γ := hΓK₁.trans le_sup_left
  set α : X × Y := g₁ ⟨a, ha₁⟩ with hα
  set β : X × Y := g₂ ⟨b, hb₂⟩ with hβ
  have hαΓ : α ∈ Γ := Subgroup.mem_sup_left ⟨_, rfl⟩
  have hβΓ : β ∈ Γ := Subgroup.mem_sup_right ⟨_, rfl⟩
  have hconj : ∀ (A : Subgroup X) (g : A →* X × Y), (∀ x : A, (g x).1 = x) →
      (∀ (x : A) (k : K), ∃ k' : K, g x * gK k * (g x)⁻¹ = gK k') → g.range ≤
        Subgroup.normalizer (ΓK : Set (X × Y)) := by
    intro A g _ h
    refine le_normalizer_of_conj ?_
    rintro _ ⟨x, rfl⟩ _ ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := h x k
    exact hk' ▸ ⟨k', rfl⟩
  have hnorm : Γ ≤ Subgroup.normalizer (ΓK : Set (X × Y)) := by
    refine sup_le (hconj A₁ g₁ (fun _ => rfl) fun x k => ?_)
      (hconj A₂ g₂ (fun _ => rfl) fun x k => ?_)
    · refine ⟨⟨x * k * x⁻¹, Subgroup.Normal.conj_mem inferInstance _ k.2 _⟩, ?_⟩
      rw [hgK₁, hgK₁, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · refine ⟨⟨x * k * x⁻¹, Subgroup.Normal.conj_mem inferInstance _ k.2 _⟩, ?_⟩
      rw [hgK₂, hgK₂, ← map_inv, ← map_mul, ← map_mul]
      rfl
  have hgen₁ : g₁.range ≤ ΓK ⊔ Subgroup.zpowers α ⊔ Subgroup.zpowers β := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk, n, hx⟩ :=
      exists_mul_zpow_of_mem_sup (hA₁ ▸ x.2 : (x : X) ∈ K ⊔ Subgroup.zpowers a)
    have e : x = Subgroup.inclusion hK₁ ⟨k, hk⟩ * ⟨a, ha₁⟩ ^ n := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_zpow]
      exact hx)
    rw [e, map_mul, map_zpow, ← hgK₁]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨_, rfl⟩))
      (Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers α))) n)
  have hgen₂ : g₂.range ≤ ΓK ⊔ Subgroup.zpowers α ⊔ Subgroup.zpowers β := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk, n, hx⟩ :=
      exists_mul_zpow_of_mem_sup (hA₂ ▸ x.2 : (x : X) ∈ K ⊔ Subgroup.zpowers b)
    have e : x = Subgroup.inclusion hK₂ ⟨k, hk⟩ * ⟨b, hb₂⟩ ^ n := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_zpow]
      exact hx)
    rw [e, map_mul, map_zpow, ← hgK₂]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨_, rfl⟩))
      (Subgroup.zpow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers β)) n)
  have hΓ : Γ = ΓK ⊔ Subgroup.zpowers α ⊔ Subgroup.zpowers β :=
    le_antisymm (sup_le hgen₁ hgen₂) (sup_le (sup_le hΓKΓ (Subgroup.zpowers_le.2 hαΓ))
      (Subgroup.zpowers_le.2 hβΓ))
  let N : Subgroup Γ := ΓK.subgroupOf Γ
  have : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hΓKΓ).2 hnorm
  have hα2 : (⟨α, hαΓ⟩ : Γ) ^ 2 ∈ N := by
    have h : gK ⟨a ^ 2, ha⟩ = α ^ 2 := by
      rw [hgK₁, hα, ← map_pow]
      rfl
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact ⟨⟨a ^ 2, ha⟩, h⟩
  have hβ2 : (⟨β, hβΓ⟩ : Γ) ^ 2 ∈ N := by
    have h : gK ⟨b ^ 2, hb⟩ = β ^ 2 := by
      rw [hgK₂, hβ, ← map_pow]
      rfl
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact ⟨⟨b ^ 2, hb⟩, h⟩
  have hαβ3 : ((⟨α, hαΓ⟩ : Γ) * ⟨β, hβΓ⟩) ^ 3 ∈ N := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, Subgroup.coe_mul]
    refine ⟨⟨(a * b) ^ 3, hab⟩, Prod.ext rfl ?_⟩
    change f₁ ⟨(a * b) ^ 3, hK₁ hab⟩ = (f₁ ⟨a, ha₁⟩ * f₂ ⟨b, hb₂⟩) ^ 3
    rw [hrel ha₁ hb₂ (hK₁ hab)]
  have hgenΓ : N ⊔ Subgroup.zpowers (⟨α, hαΓ⟩ : Γ) ⊔ Subgroup.zpowers ⟨β, hβΓ⟩ = ⊤ := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hΓKΓ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hΓ.symm
  obtain ⟨hN6, hN0⟩ := index_le_six hα2 hβ2 hαβ3 hgenΓ
  let π : Γ →* X := (MonoidHom.fst X Y).comp Γ.subtype
  have hπ : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_comp, MonoidHom.fst_comp_prod,
      MonoidHom.fst_comp_prod, Subgroup.range_subtype, Subgroup.range_subtype]
    exact htop
  let M : Subgroup Γ := K.comap π
  have hM : M.index = 6 := by rw [Subgroup.index_comap_of_surjective _ hπ, hidx]
  have hNM : N ≤ M := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.1 hzN
    have hk' : gK k = z := hk
    change z.1 ∈ K
    rw [← hk']
    exact k.2
  have hrel1 : N.relIndex M = 1 := by
    have h := Subgroup.relIndex_mul_index hNM
    rw [hM] at h
    omega
  have hMN : M ≤ N := Subgroup.relIndex_eq_one.1 hrel1
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hγM : γ ∈ M := by
      change π γ ∈ K
      rw [hγ]
      exact one_mem _
    obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.1 (hMN hγM)
    have hk1 : k = 1 := by
      have h1 : (k : X) = π γ := congrArg Prod.fst hk
      rw [hγ] at h1
      exact Subtype.ext h1
    apply Subtype.ext
    rw [← hk, hk1, map_one]
    rfl
  let e : Γ ≃* X := MulEquiv.ofBijective π ⟨hπinj, hπ⟩
  let f : X →* Y := ((MonoidHom.snd X Y).comp Γ.subtype).comp e.symm.toMonoidHom
  have hfe : ∀ γ : Γ, f (π γ) = (γ : X × Y).2 := fun γ => by
    change ((e.symm (e γ) : Γ) : X × Y).2 = _
    rw [MulEquiv.symm_apply_apply]
  have hf₁ : f.comp A₁.subtype = f₁ :=
    MonoidHom.ext fun x => hfe ⟨g₁ x, Subgroup.mem_sup_left ⟨x, rfl⟩⟩
  have hf₂ : f.comp A₂.subtype = f₂ :=
    MonoidHom.ext fun x => hfe ⟨g₂ x, Subgroup.mem_sup_right ⟨x, rfl⟩⟩
  refine ⟨f, ⟨hf₁, hf₂⟩, fun f' hf' => ?_⟩
  have hcl : Subgroup.closure ((A₁ : Set X) ∪ A₂) = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, htop]
  refine MonoidHom.eq_of_eqOn_dense hcl ?_
  rintro x (hx | hx)
  · have h1 := congrArg (fun φ : A₁ →* Y => φ ⟨x, hx⟩) (hf'.1.trans hf₁.symm)
    exact h1
  · have h1 := congrArg (fun φ : A₂ →* Y => φ ⟨x, hx⟩) (hf'.2.trans hf₂.symm)
    exact h1

theorem perm_three_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = Equiv.swap 1 2 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
      σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
        σ = Equiv.swap 1 2 * Equiv.swap 0 1 * Equiv.swap 1 2 := by
  revert σ
  decide

theorem exists_unique_extend_of_permThree {X Y : Type*} [Group X] [Group Y]
    (χ : X →* Equiv.Perm (Fin 3)) {A₁ A₂ : Subgroup X}
    (hA₁ : ∀ x, x ∈ A₁ ↔ χ x 0 = 0) (hA₂ : ∀ x, x ∈ A₂ ↔ χ x 2 = 2)
    {a b : X} (ha : χ a = Equiv.swap 1 2) (hb : χ b = Equiv.swap 0 1)
    (f₁ : A₁ →* Y) (f₂ : A₂ →* Y)
    (hf : ∀ (k : X) (h₁ : k ∈ A₁) (h₂ : k ∈ A₂), f₁ ⟨k, h₁⟩ = f₂ ⟨k, h₂⟩)
    (hrel : ∀ (h₁ : a ∈ A₁) (h₂ : b ∈ A₂) (h₃ : (a * b) ^ 3 ∈ A₁),
      (f₁ ⟨a, h₁⟩ * f₂ ⟨b, h₂⟩) ^ 3 = f₁ ⟨(a * b) ^ 3, h₃⟩) :
    ∃! f : X →* Y, f.comp A₁.subtype = f₁ ∧ f.comp A₂.subtype = f₂ := by
  have hword : ∀ σ : Equiv.Perm (Fin 3), ∃ w ∈ Subgroup.closure ({a, b} : Set X), χ w = σ := by
    have hca : a ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (Set.mem_insert _ _)
    have hcb : b ∈ Subgroup.closure ({a, b} : Set X) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    intro σ
    rcases perm_three_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, map_one χ⟩
    · exact ⟨a, hca, ha⟩
    · exact ⟨b, hcb, hb⟩
    · exact ⟨a * b, mul_mem hca hcb, by rw [map_mul, ha, hb]⟩
    · exact ⟨b * a, mul_mem hcb hca, by rw [map_mul, ha, hb]⟩
    · exact ⟨a * b * a, mul_mem (mul_mem hca hcb) hca, by rw [map_mul, map_mul, ha, hb]⟩
  have hsurj : Function.Surjective χ := fun σ =>
    let ⟨w, _, hw⟩ := hword σ
    ⟨w, hw⟩
  have hstab₀ : ∀ σ : Equiv.Perm (Fin 3), σ 0 = 0 → σ = 1 ∨ σ = Equiv.swap 1 2 := by
    decide
  have hstab₂ : ∀ σ : Equiv.Perm (Fin 3), σ 2 = 2 → σ = 1 ∨ σ = Equiv.swap 0 1 := by
    decide
  have hsup : ∀ {A : Subgroup X} {c : X} {τ : Equiv.Perm (Fin 3)} {i : Fin 3},
      (∀ x, x ∈ A ↔ χ x i = i) → χ c = τ → τ i = i →
      (∀ σ : Equiv.Perm (Fin 3), σ i = i → σ = 1 ∨ σ = τ) → A = χ.ker ⊔ Subgroup.zpowers c := by
    intro A c τ i hA hc hτ hσ
    refine le_antisymm (fun x hx => ?_) (sup_le (fun k hk => (hA k).2 ?_) ?_)
    · rcases hσ (χ x) ((hA x).1 hx) with h | h
      · exact Subgroup.mem_sup_left (by rw [MonoidHom.mem_ker, h])
      · have hk : x * c⁻¹ ∈ χ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h, hc, mul_inv_cancel]
        have := mul_mem (Subgroup.mem_sup_left hk : x * c⁻¹ ∈ χ.ker ⊔ Subgroup.zpowers c)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
        rwa [inv_mul_cancel_right] at this
    · rw [(MonoidHom.mem_ker).1 hk]
      rfl
    · rw [Subgroup.zpowers_le, hA, hc, hτ]
  have hA₁' : A₁ = χ.ker ⊔ Subgroup.zpowers a := hsup hA₁ ha (by decide) hstab₀
  have hA₂' : A₂ = χ.ker ⊔ Subgroup.zpowers b := hsup hA₂ hb (by decide) hstab₂
  have ha2 : a ^ 2 ∈ χ.ker := by
    rw [MonoidHom.mem_ker, map_pow, ha]
    decide
  have hb2 : b ^ 2 ∈ χ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hb]
    decide
  have hab3 : (a * b) ^ 3 ∈ χ.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, ha, hb]
    decide
  have hgen : χ.ker ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨w, hw, hwx⟩ := hword (χ x)
    have hwL : w ∈ χ.ker ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
      refine (Subgroup.closure_le _).2 ?_ hw
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hk : x * w⁻¹ ∈ χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwx, mul_inv_cancel]
    have := mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk) :
      x * w⁻¹ ∈ χ.ker ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b) hwL
    rwa [inv_mul_cancel_right] at this
  have hidx : χ.ker.index = 6 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  exact exists_unique_extend_of_sThree hA₁' hA₂' ha2 hb2 hab3 hgen hidx f₁ f₂
    (fun k h₁ h₂ _ => hf k h₁ h₂) hrel

end CFSG.Monster.B.Recog
