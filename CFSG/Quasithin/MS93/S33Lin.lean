module

public import CFSG.Quasithin.MS93.S34Lin

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

section Coord

variable {V : Subgroup G} {F : Type} [Field F] {β : ↥V →* Multiplicative (Fin 1 → Fin 3 → F)}

@[expose] def crd (β : ↥V →* Multiplicative (Fin 1 → Fin 3 → F)) (u : ↥V) : Fin 3 → F :=
  Multiplicative.toAdd (β u) 0

theorem crd_mul (u v : ↥V) : crd β (u * v) = crd β u + crd β v := by
  simp only [crd, map_mul, toAdd_mul, Pi.add_apply]

theorem crd_one : crd β 1 = 0 := by
  simp only [crd, map_one, toAdd_one, Pi.zero_apply]

theorem crd_inv (u : ↥V) : crd β u⁻¹ = - crd β u := by
  simp only [crd, map_inv, toAdd_inv, Pi.neg_apply]

@[expose] def coordSub (β : ↥V →* Multiplicative (Fin 1 → Fin 3 → F)) (S : Subgroup G) :
    AddSubgroup (Fin 3 → F) where
  carrier := {x | ∃ u : ↥V, (u : G) ∈ S ∧ crd β u = x}
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, mul_mem hu hv, crd_mul u v⟩
  zero_mem' := ⟨1, one_mem _, crd_one⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, inv_mem hu, crd_inv u⟩

variable (hβker : β.ker = (⊥ : Subgroup G).subgroupOf V)
include hβker

theorem crd_injective : Function.Injective (crd β) := by
  intro u u' huu'
  have h := mul_inv_mem_of_coord_eq hβker huu'
  rw [Subgroup.mem_bot, inv_mul_eq_one] at h
  exact Subtype.ext h

theorem crd_mem_coordSub_iff {S : Subgroup G} (u : ↥V) : crd β u ∈ coordSub β S ↔ (u : G) ∈ S := by
  refine ⟨?_, fun hu => ⟨u, hu, rfl⟩⟩
  rintro ⟨u', hu', he⟩
  rw [← crd_injective hβker he]
  exact hu'

theorem coordSub_le_coordSub_iff {S S' : Subgroup G} (hS : S ≤ V) :
    coordSub β S ≤ coordSub β S' ↔ S ≤ S' := by
  refine ⟨fun h s hs => ?_, fun h x => ?_⟩
  · have := h ⟨⟨s, hS hs⟩, hs, rfl⟩
    exact (crd_mem_coordSub_iff hβker (S := S') ⟨s, hS hs⟩).1 this
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, h hu, rfl⟩

theorem card_coordSub {S : Subgroup G} (hS : S ≤ V) : Nat.card (coordSub β S) = Nat.card S := by
  refine (Nat.card_congr ?_).symm
  exact
    { toFun := fun s => ⟨crd β ⟨s, hS s.2⟩, ⟨s, hS s.2⟩, s.2, rfl⟩
      invFun := fun x => ⟨(x.2.choose : G), x.2.choose_spec.1⟩
      left_inv := fun s => by
        have hx := (⟨crd β ⟨s, hS s.2⟩, ⟨s, hS s.2⟩, s.2, rfl⟩ :
          ↥(coordSub β S)).2.choose_spec.2
        have h2 := congrArg Subtype.val (crd_injective hβker hx)
        exact Subtype.ext h2
      right_inv := fun x => Subtype.ext x.2.choose_spec.2 }

omit hβker in
theorem coordSub_self (hβ : Function.Surjective β) : coordSub β V = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨u, hu⟩ := exists_coord_eq hβ x
  exact ⟨u, u.2, hu⟩

theorem coordSub_eq_top_iff (hβ : Function.Surjective β) {S : Subgroup G} (hS : S ≤ V) :
    coordSub β S = ⊤ ↔ S = V := by
  refine ⟨fun h => le_antisymm hS ?_, fun h => h ▸ coordSub_self hβ⟩
  rw [← coordSub_le_coordSub_iff hβker le_rfl, h, coordSub_self hβ]

end Coord

section Commutator

variable {V : Subgroup G} {F : Type} [Field F] {β : ↥V →* Multiplicative (Fin 1 → Fin 3 → F)}

theorem crd_commutator {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    {f : (Fin 3 → F) → (Fin 3 → F)} (hf : IsCoordAct β g f) (u : ↥V) (hc : ⁅(u : G), g⁆ ∈ V) :
    crd β ⟨⁅(u : G), g⁆, hc⟩ = crd β u - f (crd β u) := by
  set w : ↥V := ⟨g * u * g⁻¹, conj_mem_of_mem_normalizer hg u⟩
  have he : (⟨⁅(u : G), g⁆, hc⟩ : ↥V) = u * w⁻¹ := by
    apply Subtype.ext
    simp only [w, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he, crd_mul, crd_inv, ← sub_eq_add_neg]
  congr 1
  exact hf u w rfl

theorem crd_commutator' {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    {f : (Fin 3 → F) → (Fin 3 → F)} (hf : IsCoordAct β g f) (u : ↥V) (hc : ⁅g, (u : G)⁆ ∈ V) :
    crd β ⟨⁅g, (u : G)⁆, hc⟩ = f (crd β u) - crd β u := by
  set w : ↥V := ⟨g * u * g⁻¹, conj_mem_of_mem_normalizer hg u⟩
  have he : (⟨⁅g, (u : G)⁆, hc⟩ : ↥V) = w * u⁻¹ := by
    apply Subtype.ext
    simp only [w, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he, crd_mul, crd_inv, ← sub_eq_add_neg]
  congr 1
  exact hf u w rfl

variable (hβ : Function.Surjective β) (hβker : β.ker = (⊥ : Subgroup G).subgroupOf V)
include hβ hβker

theorem exists_isCoordAct' {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    ∃ f : (Fin 3 → F) →+ (Fin 3 → F), IsCoordAct β g f := by
  refine exists_isCoordAct hβ hβker hg ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl
    group
  · intro hx
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, hx]
    group

omit hβker in
theorem sub_mem_coordSub_commutator {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G)) {k : G} (hk : k ∈ K)
    {f : (Fin 3 → F) → (Fin 3 → F)} (hf : IsCoordAct β k f) (x : Fin 3 → F) :
    f x - x ∈ coordSub β ⁅V, K⁆ := by
  obtain ⟨u, rfl⟩ := exists_coord_eq hβ x
  have hc : ⁅k, (u : G)⁆ ∈ V := by
    rw [commutatorElement_def]
    exact mul_mem (conj_mem_of_mem_normalizer (hK hk) u) (inv_mem u.2)
  refine ⟨⟨_, hc⟩, ?_, crd_commutator' (hK hk) hf u hc⟩
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hk u.2

omit hβ in
theorem coordSub_commutator_le (hβ : Function.Surjective β) {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G)) {P : AddSubgroup (Fin 3 → F)}
    (hP : ∀ k ∈ K, ∀ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β k f → ∀ x, f x - x ∈ P) :
    coordSub β ⁅V, K⁆ ≤ P := by
  let Pre : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ V, crd β ⟨g, hg⟩ ∈ P}
      mul_mem' := by
        rintro a b ⟨ha, hPa⟩ ⟨hb, hPb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have : (⟨a * b, mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [this, crd_mul]
        exact add_mem hPa hPb
      one_mem' := ⟨one_mem _, by
        have : (⟨1, one_mem _⟩ : ↥V) = 1 := rfl
        rw [this, crd_one]
        exact zero_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, hPa⟩
        refine ⟨inv_mem ha, ?_⟩
        have : (⟨a⁻¹, inv_mem ha⟩ : ↥V) = (⟨a, ha⟩ : ↥V)⁻¹ := rfl
        rw [this, crd_inv]
        exact neg_mem hPa }
  have hle : ⁅V, K⁆ ≤ Pre := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    have hc : ⁅v, k⁆ ∈ V := by
      have h2 : k * v⁻¹ * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hK hk) _).1 (inv_mem hv)
      have e : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hv h2
    obtain ⟨f, hf⟩ := exists_isCoordAct' hβ hβker (hK hk)
    refine ⟨hc, ?_⟩
    have := crd_commutator (hK hk) hf ⟨v, hv⟩ hc
    simp only at this
    rw [this, ← neg_sub]
    exact neg_mem (hP k hk f hf _)
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨hg, hPu⟩ := hle hu
  exact hPu

theorem smul_mem_coordSub_commutator {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G))
    (hlin : ∀ k ∈ K, ∀ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β k f →
      ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x)
    (c : F) {x : Fin 3 → F} (hx : x ∈ coordSub β ⁅V, K⁆) : c • x ∈ coordSub β ⁅V, K⁆ := by
  let P : AddSubgroup (Fin 3 → F) :=
    { carrier := {y | c • y ∈ coordSub β ⁅V, K⁆}
      add_mem' := fun {a b} ha hb => by
        change c • (a + b) ∈ coordSub β ⁅V, K⁆
        rw [smul_add]
        exact add_mem ha hb
      zero_mem' := by
        change c • (0 : Fin 3 → F) ∈ coordSub β ⁅V, K⁆
        rw [smul_zero]
        exact zero_mem _
      neg_mem' := fun {a} ha => by
        change c • (-a) ∈ coordSub β ⁅V, K⁆
        rw [smul_neg]
        exact neg_mem ha }
  have hle : coordSub β ⁅V, K⁆ ≤ P := by
    refine coordSub_commutator_le hβker hβ hK fun k hk f hf y => ?_
    change c • (f y - y) ∈ coordSub β ⁅V, K⁆
    rw [smul_sub, ← hlin k hk f hf c y]
    exact sub_mem_coordSub_commutator hβ hK hk hf (c • y)
  exact hle hx

end Commutator

section Subspace

variable {F : Type} [Field F]

@[expose] def subOf (P : AddSubgroup (Fin 3 → F))
    (hP : ∀ (c : F) (x : Fin 3 → F), x ∈ P → c • x ∈ P) : Submodule F (Fin 3 → F) where
  carrier := P
  add_mem' := P.add_mem
  zero_mem' := P.zero_mem
  smul_mem' c x hx := hP c x hx

theorem card_subOf (P : AddSubgroup (Fin 3 → F))
    (hP : ∀ (c : F) (x : Fin 3 → F), x ∈ P → c • x ∈ P) :
    Nat.card (subOf P hP) = Nat.card P :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem card_submodule [Fintype F] (S : Submodule F (Fin 3 → F)) :
    Nat.card S = Fintype.card F ^ Module.finrank F S := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥S), Nat.card_eq_fintype_card]

theorem sub_mem_of_finrank_two [CharP F 2] {P : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x) (hfix : ∀ x ∈ P, f x = x)
    {e : ℕ} (hpow : ∀ x, f^[2 ^ e] x = x) (x : Fin 3 → F) : f x - x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hx
  have hxP : x ∉ P := fun h => hx (by rw [hfix x h, sub_self]; exact zero_mem _)
  have htop : P ⊔ Submodule.span F {x} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hlt : P < P ⊔ Submodule.span F {x} := by
      refine lt_of_le_of_ne le_sup_left fun h => hxP ?_
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (P ⊔ Submodule.span F {x})
    rw [Module.finrank_fin_fun] at h2 ⊢
    omega
  have hfxm : f x ∈ P ⊔ Submodule.span F {x} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨p, hp, y, hy, hfx⟩ := Submodule.mem_sup.1 hfxm
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have key : ∀ m : ℕ, f^[m] x - c ^ m • x ∈ P := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      set q := f^[m] x - c ^ m • x with hq
      have hfm : f^[m] x = q + c ^ m • x := by rw [hq]; abel
      rw [hfm, map_add, hfix q ih, hlin, ← hfx]
      have e' : q + c ^ m • (p + c • x) - c ^ (m + 1) • x = q + c ^ m • p := by
        rw [smul_add, smul_smul, ← pow_succ]
        abel
      rw [e']
      exact add_mem ih (P.smul_mem _ hp)
  have h2 := key (2 ^ e)
  rw [hpow x] at h2
  have hc : c ^ 2 ^ e = 1 := by
    by_contra hc
    apply hxP
    have hne : (1 - c ^ 2 ^ e) ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
    rw [← Submodule.smul_mem_iff P hne, sub_smul, one_smul]
    exact h2
  have hc1 : c = 1 := by
    have h0 : (c - 1) ^ 2 ^ e = 0 := by rw [sub_pow_char_pow, hc, one_pow, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero e two_ne_zero)).1 h0)
  apply hx
  rw [← hfx, hc1, one_smul, add_sub_cancel_right]
  exact hp

end Subspace

section Powers

variable {V : Subgroup G} {F : Type} [Field F] {β : ↥V →* Multiplicative (Fin 1 → Fin 3 → F)}

theorem isCoordAct_iterate {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    {f : (Fin 3 → F) → (Fin 3 → F)} (hf : IsCoordAct β g f) (m : ℕ) :
    IsCoordAct β (g ^ m) (f^[m]) := by
  induction m with
  | zero => simpa using (isCoordAct_one (β := β))
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ]
    exact ih.mul hg hf

theorem iterate_eq_of_pow_eq_one (hβ : Function.Surjective β) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) {f : (Fin 3 → F) → (Fin 3 → F)}
    (hf : IsCoordAct β g f) {m : ℕ} (hm : g ^ m = 1) (x : Fin 3 → F) : f^[m] x = x := by
  have h := isCoordAct_iterate hg hf m
  rw [hm] at h
  exact congrFun (IsCoordAct.unique hβ (one_mem _) h isCoordAct_one) x

end Powers

end CFSG.Quasithin.MS93.S33
