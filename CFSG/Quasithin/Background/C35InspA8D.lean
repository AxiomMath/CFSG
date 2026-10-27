module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.C35InspA8B
public import CFSG.Quasithin.Background.C35InspL45C

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.C48Pf.FMod
open scoped commutatorElement

variable {A : Type} [Group A]

theorem isNaturalSection_of_surj {M₀ V Z : Subgroup A} {N : Subgroup ↥M₀} {m : ℕ}
    (hMV : M₀ ≤ Subgroup.normalizer (V : Set A))
    (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hα : Function.Surjective α)
    (hker : α.ker = N) (β : ↥V →* Multiplicative (Fin m → ZMod 2))
    (hβs : Function.Surjective β) (hβker : β.ker = Z.subgroupOf V)
    (hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u)) :
    IsNaturalSection M₀ V Z N (StatedSL m (ZMod 2)) := by
  refine ⟨hMV, (specialLinearGroupEquivStatedSL m (ZMod 2)).toMonoidHom.comp α,
    (specialLinearGroupEquivStatedSL m (ZMod 2)).surjective.comp hα, ?_, β, hβs, hβker,
    fun a u v huv => hequiv a u v huv⟩
  rw [← hker]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem eq_zero_of_transvection_fixed {w : Fin 3 → ZMod 2}
    (h : ∀ r s : Fin 3, r ≠ s → (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w = w) : w = 0 := by
  funext s
  obtain ⟨r, hrs⟩ : ∃ r : Fin 3, r ≠ s := ⟨s + 1, by fin_cases s <;> decide⟩
  have h1 := congrFun (h r s hrs) r
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Matrix.single_mulVec, one_mul,
    Function.update_self, add_eq_left] at h1
  show w s = 0
  exact h1

theorem eq_one_of_mulVec_eq {m : ℕ} {M : Matrix (Fin m) (Fin m) (ZMod 2)}
    (h : ∀ w, M *ᵥ w = w) : M = 1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  rw [h1, Matrix.one_apply]

theorem beta_surjective {M₀ V : Subgroup A} {m : ℕ} (hm : 2 ≤ m)
    (hMV : M₀ ≤ Subgroup.normalizer (V : Set A))
    (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hαs : Function.Surjective α)
    (β : ↥V →* Multiplicative (Fin m → ZMod 2))
    (hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u))
    (hne : ∃ v, β v ≠ 1) : Function.Surjective β := by
  let W : AddSubgroup (Fin m → ZMod 2) :=
    { carrier := {w | ∃ v, Multiplicative.toAdd (β v) = w}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
  have hW : W ≠ ⊥ := by
    intro hW
    obtain ⟨v, hv⟩ := hne
    have h1 : Multiplicative.toAdd (β v) ∈ W := ⟨v, rfl⟩
    rw [hW, AddSubgroup.mem_bot] at h1
    exact hv (Multiplicative.toAdd.injective h1)
  have hinv : ∀ r s : Fin m, r ≠ s → ∀ w ∈ W, (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w ∈ W := by
    rintro r s hrs _ ⟨u, rfl⟩
    obtain ⟨a, ha⟩ := hαs (SpecialLinearGroup.transvection hrs (1 : ZMod 2))
    have hmem : (a : A) * u * (a : A)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hMV a.2) u).1 u.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [hequiv a u ⟨_, hmem⟩ rfl, ha, CFSG.LinearGroups.coe_transvection]
  have htop := eq_top_of_transvection_invariant hm W hW hinv
  intro y
  have hy : Multiplicative.toAdd y ∈ W := by
    rw [htop]
    exact AddSubgroup.mem_top _
  obtain ⟨v, hv⟩ := hy
  exact ⟨v, Multiplicative.toAdd.injective hv⟩

theorem card_centerOf (K : Subgroup A) :
    Nat.card ↥(centerOf K) = Nat.card ↥(Subgroup.center ↥K) := by
  have e : (Subgroup.center ↥K).map K.subtype = centerOf K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_centerOf_iff.2 hy
    · intro hx
      exact ⟨⟨x, hx.1⟩, mem_centerOf_iff.1 hx, rfl⟩
  rw [← e]
  exact Nat.card_congr ((Subgroup.center ↥K).equivMapOfInjective K.subtype
    K.subtype_injective).toEquiv.symm

theorem eq_of_centerOf_two {K : Subgroup A} (hc2 : Nat.card ↥(Subgroup.center ↥K) = 2)
    {x y : A} (hx : x ∈ centerOf K) (hy : y ∈ centerOf K) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x = y := by
  rw [← card_centerOf] at hc2
  obtain ⟨u, hu1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(centerOf K))).mp hc2
  have h1 := huniq ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
  have h2 := huniq ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem commutatorElement_mul_centerOf {K : Subgroup A} {v c m : A} (hv : v ∈ K)
    (hc : c ∈ centerOf K) (hm : m ∈ K) : ⁅v * c, m⁆ = ⁅v, m⁆ := by
  have h := commutatorElement_mul_central_left ((mem_centerOf_iff (x := ⟨c, hc.1⟩)).1 hc)
    (⟨v, hv⟩ : ↥K) ⟨m, hm⟩
  exact congrArg Subtype.val h

theorem comm_of_elem {V : Subgroup A} (hV : IsElemAbelian 2 V) {u v : A} (hu : u ∈ V)
    (hv : v ∈ V) : u * v = v * u := CFSG.Open.IsElemAbelian.comm hV hu hv

variable [Finite A]

omit [Finite A] in
theorem exists_beta_ne_one {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    {G : Type} [Group G] (θ : ↥K →* G) (hθker : θ.ker = Subgroup.center ↥K)
    {m : ℕ} (β : ↥V →* Multiplicative (Fin m → ZMod 2))
    (hβθ : ∀ v : ↥V, β v = 1 ↔ θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1) : ∃ v, β v ≠ 1 := by
  by_contra hall
  push Not at hall
  apply hD.V_ne
  rw [← hD.V_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  have h1 : (⟨v, hM₀K (hD.V_le hv)⟩ : ↥K) ∈ θ.ker := (hβθ ⟨v, hv⟩).1 (hall _)
  rw [hθker] at h1
  have hvZ : v ∈ centerOf K := mem_centerOf_iff.2 h1
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact Subgroup.mem_centralizer_iff.1 hvZ.2 m (hM₀K hm)

theorem b48_of_coords {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    {G : Type} [Group G] (θ : ↥K →* G) (hθker : θ.ker = Subgroup.center ↥K)
    (hc2 : Nat.card ↥(Subgroup.center ↥K) = 2)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥M₀) (β : ↥V →* Multiplicative (Fin 3 → ZMod 2))
    (hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u))
    (hβθ : ∀ v : ↥V, β v = 1 ↔ θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1) (hβs : Function.Surjective β)
    (hO : ∀ y : ↥M₀, α y = 1 → ∃ v : ↥V, θ ⟨v, hM₀K (hD.V_le v.2)⟩ = θ ⟨y, hM₀K y.2⟩)
    {v₀ m₀ : A} (hv₀ : v₀ ∈ V) (hm₀ : m₀ ∈ M₀) (hz1 : ⁅v₀, m₀⁆ ≠ 1)
    (hzc : ⁅v₀, m₀⁆ ∈ centerOf K) :
    centerOf K = V ⊓ Subgroup.centralizer (M₀ : Set A) ∧ IsB48TwoModule M₀ V := by
  classical
  have hMV := le_normalizer_of_comm hD.V_comm
  have hVK : V ≤ K := hD.V_le.trans hM₀K
  set z := ⁅v₀, m₀⁆ with hzdef
  have hzV : z ∈ V := hD.V_comm ▸ Subgroup.commutator_mem_commutator hv₀ hm₀
  have hZ : ∀ x ∈ centerOf K, x = 1 ∨ x = z := fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (eq_of_centerOf_two hc2 hx hzc h1 hz1)
  have hZV : centerOf K ≤ V := fun x hx => by
    rcases hZ x hx with rfl | rfl
    · exact V.one_mem
    · exact hzV
  have hβZ : ∀ v : ↥V, β v = 1 ↔ (v : A) ∈ centerOf K := fun v => by
    rw [hβθ, ← MonoidHom.mem_ker, hθker]
    exact mem_centerOf_iff.symm
  have hfix : ∀ w : Fin 3 → ZMod 2,
      (∀ a : ↥M₀, ((α a : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w) → w = 0 := fun w hw =>
    eq_zero_of_transvection_fixed fun r s hrs => by
      obtain ⟨a, ha⟩ := hαs (SpecialLinearGroup.transvection hrs (1 : ZMod 2))
      have := hw a
      rwa [ha, CFSG.LinearGroups.coe_transvection] at this
  have hcen : centerOf K = V ⊓ Subgroup.centralizer (M₀ : Set A) := by
    apply le_antisymm
    · intro x hx
      refine Subgroup.mem_inf.2 ⟨hZV hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_iff.1 hx.2 m (hM₀K hm)
    · intro x hx
      obtain ⟨hxV, hxC⟩ := hx
      refine (hβZ ⟨x, hxV⟩).1 ?_
      have h0 : Multiplicative.toAdd (β ⟨x, hxV⟩) = 0 := hfix _ fun a => by
        have hax : (x : A) = a * x * (a : A)⁻¹ := by
          rw [Subgroup.mem_centralizer_iff.1 hxC a a.2, mul_inv_cancel_right]
        exact (hequiv a ⟨x, hxV⟩ ⟨x, hxV⟩ hax).symm
      exact Multiplicative.toAdd.injective h0
  have hkerV : α.ker = V.subgroupOf M₀ := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      obtain ⟨v, hv⟩ := hO y hy
      have h1 : (⟨v, hM₀K (hD.V_le v.2)⟩ : ↥K)⁻¹ * ⟨y, hM₀K y.2⟩ ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hv, inv_mul_cancel]
      rw [hθker] at h1
      have h2 := hZV (mem_centerOf_iff.2 h1)
      have h3 := V.mul_mem v.2 h2
      simpa using h3
    · intro hy
      rw [← MonoidHom.mem_ker, hker]
      obtain ⟨y', hy', hyy'⟩ := (le_pCoreOf_of_data hD).1 hy
      have : y' = y := Subtype.ext hyy'
      rw [← this]
      exact hy'
  have hβker : β.ker = (centerOf K).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβZ]
  have hcard : Nat.card ↥V = 2 ^ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv, card_centerOf, hc2] at h1
    rw [h1]
    simp
  have hcent : M₀ ⊓ Subgroup.centralizer (V : Set A) = V := by
    refine le_antisymm (fun m hm => ?_) (fun v hv => Subgroup.mem_inf.2 ⟨hD.V_le hv, ?_⟩)
    · obtain ⟨hmM, hmC⟩ := hm
      have hα1 : α ⟨m, hmM⟩ = 1 := by
        apply Subtype.ext
        refine eq_one_of_mulVec_eq fun w => ?_
        obtain ⟨u, rfl⟩ := hβs (Multiplicative.ofAdd w)
        have hmu : (u : A) = (⟨m, hmM⟩ : ↥M₀) * u * ((⟨m, hmM⟩ : ↥M₀) : A)⁻¹ := by
          show (u : A) = m * u * m⁻¹
          rw [← Subgroup.mem_centralizer_iff.1 hmC u u.2, mul_inv_cancel_right]
        exact (hequiv _ u u hmu).symm
      have := (Subgroup.mem_subgroupOf.1 ((hkerV ▸ (MonoidHom.mem_ker.2 hα1)) :
        (⟨m, hmM⟩ : ↥M₀) ∈ V.subgroupOf M₀))
      exact this
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact comm_of_elem hD.V_elem hu hv
  have hβZsub : ∀ V₁ : Subgroup A, V₁ ≤ V →
      (∀ v : ↥V, (v : A) ∈ V₁ → β v = 1) → V₁ ≤ centerOf K := fun V₁ h1 h x hx =>
    (hβZ ⟨x, h1 hx⟩).1 (h _ hx)
  have hzin : ∀ V₁ : Subgroup A, V₁ ≤ centerOf K → V₁ ≠ ⊥ → z ∈ V₁ := fun V₁ h1 hne => by
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hxx : (x : A) = z := eq_of_centerOf_two hc2 (h1 x.2) hzc
      (fun h => hx1 (Subtype.ext h)) hz1
    rw [← hxx]
    exact x.2
  have hcomm_in : ∀ V₂ : Subgroup A, V₂ ≤ V → M₀ ≤ Subgroup.normalizer (V₂ : Set A) →
      ∀ v₂ : ↥V, (v₂ : A) ∈ V₂ → β v₂ = β ⟨v₀, hv₀⟩ → z ∈ V₂ := by
    intro V₂ _ hn v₂ hv₂ hβ
    have hc : (v₂ : A)⁻¹ * v₀ ∈ centerOf K := by
      have := (hβZ ((v₂)⁻¹ * ⟨v₀, hv₀⟩)).1 (by rw [map_mul, map_inv, hβ, inv_mul_cancel])
      simpa using this
    have e : z = ⁅(v₂ : A), m₀⁆ := by
      rw [hzdef, show v₀ = (v₂ : A) * ((v₂ : A)⁻¹ * v₀) by group,
        commutatorElement_mul_centerOf (hVK v₂.2) hc (hM₀K hm₀)]
    rw [e, commutatorElement_def]
    have hmv := (Subgroup.mem_normalizer_iff.1 (hn hm₀) (v₂ : A)⁻¹).1 (V₂.inv_mem hv₂)
    have := V₂.mul_mem hv₂ hmv
    simpa [mul_assoc] using this
  have himg : ∀ V₁ : Subgroup A, V₁ ≤ V → M₀ ≤ Subgroup.normalizer (V₁ : Set A) →
      (∀ v : ↥V, (v : A) ∈ V₁ → β v = 1) ∨
        ∀ w : Fin 3 → ZMod 2, ∃ v : ↥V, (v : A) ∈ V₁ ∧ Multiplicative.toAdd (β v) = w := by
    intro V₁ h1 hn
    let W : AddSubgroup (Fin 3 → ZMod 2) :=
      { carrier := {w | ∃ v : ↥V, (v : A) ∈ V₁ ∧ Multiplicative.toAdd (β v) = w}
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
          exact ⟨u * v, V₁.mul_mem hu hv, by rw [map_mul, toAdd_mul]⟩
        zero_mem' := ⟨1, V₁.one_mem, by rw [map_one, toAdd_one]⟩
        neg_mem' := by
          rintro _ ⟨u, hu, rfl⟩
          exact ⟨u⁻¹, V₁.inv_mem hu, by rw [map_inv, toAdd_inv]⟩ }
    by_cases hW : W = ⊥
    · left
      intro v hv
      have h0 : Multiplicative.toAdd (β v) ∈ W := ⟨v, hv, rfl⟩
      rw [hW, AddSubgroup.mem_bot] at h0
      exact Multiplicative.toAdd.injective h0
    · right
      have hinv : ∀ r s : Fin 3, r ≠ s → ∀ w ∈ W,
          (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w ∈ W := by
        rintro r s hrs _ ⟨u, hu, rfl⟩
        obtain ⟨a, ha⟩ := hαs (SpecialLinearGroup.transvection hrs (1 : ZMod 2))
        have hmem : (a : A) * u * (a : A)⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (hMV a.2) u).1 u.2
        have hmem₁ : (a : A) * u * (a : A)⁻¹ ∈ V₁ :=
          (Subgroup.mem_normalizer_iff.1 (hn a.2) u).1 hu
        refine ⟨⟨_, hmem⟩, hmem₁, ?_⟩
        rw [hequiv a u ⟨_, hmem⟩ rfl, ha, CFSG.LinearGroups.coe_transvection]
      have htop := eq_top_of_transvection_invariant (by norm_num) W hW hinv
      intro w
      have : w ∈ W := by
        rw [htop]
        exact AddSubgroup.mem_top _
      exact this
  have hbig : ∀ V₁ : Subgroup A, V₁ ≤ V →
      (∀ w : Fin 3 → ZMod 2, ∃ v : ↥V, (v : A) ∈ V₁ ∧ Multiplicative.toAdd (β v) = w) →
      8 ≤ Nat.card ↥V₁ := by
    intro V₁ h1 h
    have hs : Function.Surjective fun x : ↥V₁ =>
        Multiplicative.toAdd (β ⟨x, h1 x.2⟩) := fun w => by
      obtain ⟨v, hv, hvw⟩ := h w
      exact ⟨⟨v, hv⟩, hvw⟩
    have := Nat.card_le_card_of_surjective _ hs
    simpa [Nat.card_fun, Nat.card_zmod] using this
  have hind : IsIndecomposableUnder M₀ V := by
    refine ⟨hD.V_ne, fun V₁ V₂ h1 h2 hn1 hn2 hinf _ => ?_⟩
    have hdisj : ∀ x, x ∈ V₁ → x ∈ V₂ → x = 1 := fun x hx1 hx2 => by
      have : x ∈ V₁ ⊓ V₂ := ⟨hx1, hx2⟩
      rw [hinf] at this
      exact this
    rcases himg V₁ h1 hn1 with hW₁ | hW₁ <;> rcases himg V₂ h2 hn2 with hW₂ | hW₂
    ·
      by_cases hV₁ : V₁ = ⊥
      · exact Or.inl hV₁
      · right
        rw [eq_bot_iff]
        intro y hy
        have hyZ := hβZsub V₂ h2 hW₂ hy
        rcases hZ y hyZ with rfl | rfl
        · exact Subgroup.one_mem _
        · exact absurd (hdisj _ (hzin V₁ (hβZsub V₁ h1 hW₁) hV₁) hy) hz1
    ·
      left
      by_contra hV₁
      obtain ⟨v₂, hv₂, hβ⟩ := hW₂ (Multiplicative.toAdd (β ⟨v₀, hv₀⟩))
      exact hz1 (hdisj _ (hzin V₁ (hβZsub V₁ h1 hW₁) hV₁)
        (hcomm_in V₂ h2 hn2 v₂ hv₂ (Multiplicative.toAdd.injective hβ)))
    ·
      right
      by_contra hV₂
      obtain ⟨v₁, hv₁, hβ⟩ := hW₁ (Multiplicative.toAdd (β ⟨v₀, hv₀⟩))
      exact hz1 (hdisj _ (hcomm_in V₁ h1 hn1 v₁ hv₁ (Multiplicative.toAdd.injective hβ))
        (hzin V₂ (hβZsub V₂ h2 hW₂) hV₂))
    ·
      exfalso
      have hc1 := hbig V₁ h1 hW₁
      have hc2' := hbig V₂ h2 hW₂
      have hinj : Function.Injective fun p : ↥V₁ × ↥V₂ =>
          (⟨(p.1 : A) * p.2, V.mul_mem (h1 p.1.2) (h2 p.2.2)⟩ : ↥V) := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ h
        have h' : (a : A) * b = a' * b' := congrArg Subtype.val h
        have e1 : (a' : A)⁻¹ * a = b' * (b : A)⁻¹ := by
          calc (a' : A)⁻¹ * a = (a' : A)⁻¹ * (a * b) * (b : A)⁻¹ := by group
            _ = (a' : A)⁻¹ * (a' * b') * (b : A)⁻¹ := by rw [h']
            _ = b' * (b : A)⁻¹ := by group
        have e2 := hdisj _ (V₁.mul_mem (V₁.inv_mem a'.2) a.2)
          (e1 ▸ V₂.mul_mem b'.2 (V₂.inv_mem b.2))
        have ha : a = a' := Subtype.ext (by
          have := congrArg (fun t => (a' : A) * t) e2
          simpa using this)
        have hb : b = b' := Subtype.ext (by
          subst ha
          simpa using h')
        rw [ha, hb]
      have := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, hcard] at this
      nlinarith
  have hnat : IsNaturalSection M₀ V (V ⊓ Subgroup.centralizer (M₀ : Set A)) (V.subgroupOf M₀)
      (StatedSL 3 (ZMod 2)) :=
    isNaturalSection_of_surj hMV α hαs hkerV β hβs (hcen ▸ hβker) hequiv
  exact ⟨hcen, hD.V_le, hD.V_elem, hcard, hcent, hind, hnat⟩

end CFSG.Quasithin.C35Pf
