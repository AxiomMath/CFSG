module

public import CFSG.RankThree.GF2n.Tim79a34A9Core
public import CFSG.Sporadic.Th.Recog.A9Mod.Classify

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Sporadic.Th.Recog

local instance (priority := high) instAddCommGroupZMod2A9AbsIrr : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

def va : V8 := Pi.single 0 1 + Pi.single 1 1 + Pi.single 5 1

def vp : V8 := fun i => if i = 4 then 0 else 1

def w1 : List Bool := [false, false]

def w2 : List Bool := [true, false, true, false]

theorem va_ne_zero : va ≠ 0 := by decide +kernel

theorem qf_single (i : Fin 8) : qf (Pi.single i 1) = 0 := by
  revert i; decide +kernel

theorem single_ne_zero (i : Fin 8) : (Pi.single i 1 : V8) ≠ 0 := by
  revert i; decide +kernel

theorem applyWord_w1_va : applyWord w1 va = va := by decide +kernel

theorem applyWord_w2_va : applyWord w2 va = va := by decide +kernel

theorem fixed_va (x : V8) (h1 : applyWord w1 x = x) (h2 : applyWord w2 x = x) :
    x = 0 ∨ x = va := by
  revert x; decide +kernel

theorem fixed_vp (x : V8) (h1 : rho8p (permWord w1) x = x)
    (h2 : rho8p (permWord w2) x = x) : x = 0 ∨ x = vp := by
  revert x; decide +kernel

theorem rho8p_w1_vp : rho8p (permWord w1) vp = vp := by
  decide +kernel

theorem rho8p_w2_vp : rho8p (permWord w2) vp = vp := by
  decide +kernel

def subrepresentationCompAut {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (ψ : G ≃* G) :
    Subrepresentation (ρ.comp ψ.toMonoidHom) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _v hv => by
        have h := S.apply_mem_toSubmodule (ψ.symm g) hv
        simpa using h }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _v hv => by
        have h := S.apply_mem_toSubmodule (ψ g) hv
        simpa using h }
  left_inv S := Subrepresentation.toSubmodule_injective rfl
  right_inv S := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_aut {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (ψ : G ≃* G) :
    Representation.IsIrreducible (ρ.comp ψ.toMonoidHom) ↔
      Representation.IsIrreducible ρ :=
  OrderIso.isSimpleOrder_iff (subrepresentationCompAut ρ ψ)

theorem isAbsolutelyIrreducible_comp_aut {F G V : Type*} [Field F] [Group G] [AddCommGroup V]
    [Module F V] (ρ : Representation F G V) (ψ : G ≃* G) :
    CFSG.Theory.Representation.IsAbsolutelyIrreducible (ρ.comp ψ.toMonoidHom) ↔
      CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ := by
  rw [CFSG.Theory.Representation.isAbsolutelyIrreducible_iff,
    CFSG.Theory.Representation.isAbsolutelyIrreducible_iff]
  have h : CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) (ρ.comp ψ.toMonoidHom) =
      (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) ρ).comp ψ.toMonoidHom := by
    ext g
    rfl
  rw [h]
  exact isIrreducible_comp_aut _ ψ

theorem isIrreducible_of_forall {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V]
    [Module F V] [Nontrivial V] (ρ : Representation F G V)
    (h : ∀ S : Subrepresentation ρ, S ≠ ⊥ → S = ⊤) : Representation.IsIrreducible ρ :=
  IsSimpleOrder.of_forall_eq_top h

theorem end_apply_eq {F G V : Type*} [CommRing F] [Monoid G] [AddCommGroup V] [Module F V]
    {ρ : Representation F G V} (T : CFSG.Theory.Representation.End ρ) (g : G) (v : V) :
    T (ρ g v) = ρ g (T v) := by
  have h := LinearMap.congr_fun (T.isIntertwining' g) v
  simpa only [LinearMap.comp_apply, CFSG.Theory.Representation.RepMap.coe_toLinearMap] using h

theorem surjective_algebraMap_of_cyclic {F G V : Type*} [Field F] [Group G] [AddCommGroup V]
    [Module F V] (ρ : Representation F G V) (v : V)
    (hv : Submodule.span F (Set.range fun g : G => ρ g v) = ⊤) (S : Finset G)
    (hSv : ∀ s ∈ S, ρ s v = v)
    (hfix : ∀ w : V, (∀ s ∈ S, ρ s w = w) → ∃ c : F, w = c • v) :
    Function.Surjective (algebraMap F (CFSG.Theory.Representation.End ρ)) := by
  intro T
  obtain ⟨c, hc⟩ := hfix (T v) fun s hs => by
    rw [← end_apply_eq T s v, hSv s hs]
  refine ⟨c, ?_⟩
  apply CFSG.Theory.Representation.RepMap.toLinearMap_injective
  rw [CFSG.Theory.Representation.End.algebraMap_apply]
  apply LinearMap.ext_on hv
  intro x hx
  obtain ⟨g, rfl⟩ := hx
  change (c • (1 : CFSG.Theory.Representation.End ρ)) (ρ g v) = T (ρ g v)
  rw [CFSG.Theory.Representation.RepMap.smul_apply,
    CFSG.Theory.Representation.End.one_apply, end_apply_eq T g v, hc, map_smul]

theorem qf_u2 : qf (Pi.single 0 1 + Pi.single 2 1 : V8) = 1 := by decide +kernel

theorem u2_ne_zero : (Pi.single 0 1 + Pi.single 2 1 : V8) ≠ 0 := by decide +kernel

theorem qf_u1_add_u2 : qf (e01 + (Pi.single 0 1 + Pi.single 2 1) : V8) = 0 := by
  decide +kernel

theorem u1_add_u2_ne_zero : (e01 + (Pi.single 0 1 + Pi.single 2 1) : V8) ≠ 0 := by
  decide +kernel

theorem rho8a_eq_top_of_singular (T : Submodule (ZMod 2) V8)
    (hT : ∀ (g : alternatingGroup (Fin 9)) ⦃x : V8⦄, x ∈ T → (A9Mod.endHom rho8a) g x ∈ T)
    {z : V8} (hz : z ∈ T) (hz0 : z ≠ 0) (hzq : qf z = 0) : T = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin 8)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨g, hg⟩ := exists_rho8a_eq hz0 (single_ne_zero i) (hzq.trans (qf_single i).symm)
  have h := hT g hz
  rw [A9Mod.endHom_apply, hg] at h
  simpa using h

theorem rho8a_eq_top (T : Submodule (ZMod 2) V8)
    (hT : ∀ (g : alternatingGroup (Fin 9)) ⦃x : V8⦄, x ∈ T → (A9Mod.endHom rho8a) g x ∈ T)
    {y : V8} (hy : y ∈ T) (hy0 : y ≠ 0) : T = ⊤ := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (qf y) with hq | hq
  · exact rho8a_eq_top_of_singular T hT hy hy0 hq
  · have hall : ∀ z : V8, z ≠ 0 → qf z = 1 → z ∈ T := by
      intro z hz hzq
      obtain ⟨g, hg⟩ := exists_rho8a_eq hy0 hz (hq.trans hzq.symm)
      have h := hT g hy
      rwa [A9Mod.endHom_apply, hg] at h
    have h1 : e01 ∈ T := hall e01 e01_ne_zero qf_e01
    have h2 : (Pi.single 0 1 + Pi.single 2 1 : V8) ∈ T :=
      hall _ u2_ne_zero qf_u2
    exact rho8a_eq_top_of_singular T hT (Submodule.add_mem T h1 h2)
      u1_add_u2_ne_zero qf_u1_add_u2

theorem rho8a_irreducible : Representation.IsIrreducible (A9Mod.endHom rho8a) := by
  apply isIrreducible_of_forall
  intro S hS
  have hTne : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective (by simpa using h))
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
  exact Subrepresentation.toSubmodule_injective (by
    simpa using rho8a_eq_top S.toSubmodule (fun g _ hx => S.apply_mem_toSubmodule g hx) hy hy0)

theorem rho8a_span_va :
    Submodule.span (ZMod 2)
      (Set.range fun g : alternatingGroup (Fin 9) => (A9Mod.endHom rho8a) g va) = ⊤ := by
  let T : Submodule (ZMod 2) V8 :=
    Submodule.span (ZMod 2) (Set.range fun g : alternatingGroup (Fin 9) => (A9Mod.endHom rho8a) g va)
  have hinv : ∀ (g : alternatingGroup (Fin 9)) ⦃x : V8⦄, x ∈ T →
      (A9Mod.endHom rho8a) g x ∈ T := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨h, rfl⟩ := hz
        rw [← Module.End.mul_apply, ← map_mul]
        exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem T
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem T ihx ihy
    | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem T c ih
  exact rho8a_eq_top T hinv (Submodule.subset_span ⟨1, by simp⟩) va_ne_zero

theorem rho8a_algebraMap_surjective :
    Function.Surjective (algebraMap (ZMod 2)
      (CFSG.Theory.Representation.End (A9Mod.endHom rho8a))) := by
  refine surjective_algebraMap_of_cyclic _ va rho8a_span_va
    {permWord w1, permWord w2} ?_ ?_
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [A9Mod.endHom_apply, ← applyWord_eq_rho8a]
      exact applyWord_w1_va
    · rw [A9Mod.endHom_apply, ← applyWord_eq_rho8a]
      exact applyWord_w2_va
  · intro x hx
    have h1 : applyWord w1 x = x := by
      have h := hx (permWord w1) (by simp)
      rwa [A9Mod.endHom_apply, ← applyWord_eq_rho8a] at h
    have h2 : applyWord w2 x = x := by
      have h := hx (permWord w2) (by simp)
      rwa [A9Mod.endHom_apply, ← applyWord_eq_rho8a] at h
    rcases fixed_va x h1 h2 with h | h
    · exact ⟨0, by rw [h, zero_smul]⟩
    · exact ⟨1, by rw [h, one_smul]⟩

theorem rho8a_absIrr :
    CFSG.Theory.Representation.IsAbsolutelyIrreducible (A9Mod.endHom rho8a) := by
  haveI : FiniteDimensional (ZMod 2) V8 := inferInstance
  haveI : Representation.IsIrreducible (A9Mod.endHom rho8a) := rho8a_irreducible
  exact (CFSG.Theory.Representation.isAbsolutelyIrreducible_iff_surjective _).mpr
    rho8a_algebraMap_surjective

open scoped symmDiff

theorem finset_image_swap_of_mem_of_notMem {α : Type*} [DecidableEq α] (s : Finset α) {i j : α}
    (hi : i ∈ s) (hj : j ∉ s) : s.image (Equiv.swap i j) = s.erase i ∪ {j} := by
  ext x
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases eq_or_ne y i with h | h
    · subst h
      rw [Equiv.swap_apply_left]
      exact Or.inr rfl
    · rw [Equiv.swap_apply_of_ne_of_ne h (show y ≠ j from fun h' => hj (h' ▸ hy))]
      exact Or.inl ⟨h, hy⟩
  · rintro (⟨hxi, hxs⟩ | rfl)
    · refine ⟨Equiv.swap i j x, ?_, by simp⟩
      rw [Equiv.swap_apply_of_ne_of_ne hxi (show x ≠ j from fun h' => hj (h' ▸ hxs))]
      exact hxs
    · exact ⟨i, hi, Equiv.swap_apply_left ..⟩

theorem finset_image_swap_of_mem_of_mem {α : Type*} [DecidableEq α] (s : Finset α) {i j : α}
    (hi : i ∈ s) (hj : j ∈ s) : s.image (Equiv.swap i j) = s := by
  ext x
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases eq_or_ne y i with h | h
    · subst h; rwa [Equiv.swap_apply_left]
    · rcases eq_or_ne y j with h' | h'
      · subst h'; rwa [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne h h']; exact hy
  · intro hx
    refine ⟨Equiv.swap i j x, ?_, by simp⟩
    rcases eq_or_ne x i with h | h
    · subst h; rwa [Equiv.swap_apply_left]
    · rcases eq_or_ne x j with h' | h'
      · subst h'; rwa [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne h h']; exact hx

theorem supp9_add (x y : V8) : supp9 (x + y) = supp9 x ∆ supp9 y := by
  ext j
  rw [mem_supp9, ext9_add, Pi.add_apply, Finset.mem_symmDiff]
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (ext9 x j) with hx | hx <;>
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (ext9 y j) with hy | hy <;>
    simp [hx, hy, mem_supp9]

theorem supp9_rho8p (σ : alternatingGroup (Fin 9)) (x : V8) :
    supp9 (rho8p σ x) = (supp9 x).image (σ : Fin 9 → Fin 9) := by
  ext j
  rw [Finset.mem_image]
  constructor
  · intro hj
    rw [mem_supp9, ext9_rho8p] at hj
    exact ⟨((σ : Equiv.Perm (Fin 9))⁻¹) j, (mem_supp9 x _).mpr hj, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    rw [mem_supp9, ext9_rho8p]
    simpa using (mem_supp9 x i).mp hi

theorem ext9_eq_indicator (x : V8) :
    ext9 x = fun j => if j ∈ supp9 x then 1 else 0 := by
  funext j
  by_cases h : j ∈ supp9 x
  · rw [if_pos h, (mem_supp9 x j).mp h]
  · rw [if_neg h]
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (ext9 x j) with h0 | h1
    · exact h0
    · exact absurd ((mem_supp9 x j).mpr h1) h

theorem ext9_single (i : Fin 8) :
    ext9 (Pi.single i 1 : V8) =
      fun j => if j = Fin.castSucc i ∨ j = Fin.last 8 then 1 else 0 := by
  revert i
  decide +kernel

theorem eq_single_of_supp (x : V8) (i : Fin 8)
    (h : supp9 x = {Fin.castSucc i, Fin.last 8}) : x = Pi.single i 1 := by
  apply ext9_injective
  rw [ext9_eq_indicator, ext9_single, h]
  simp [Finset.mem_insert, Finset.mem_singleton]

theorem alternatingGroup_two_pretransitive :
    MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 9)) (Fin 9) 2 := by
  have h7 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 9)) (Fin 9) 7 := by
    simpa using alternatingGroup.isMultiplyPretransitive (Fin 9)
  exact MulAction.isMultiplyPretransitive_of_le (m := 2) (n := 7) (by norm_num) (by norm_num)

theorem exists_perm_pair (a b c d : Fin 9) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : alternatingGroup (Fin 9), (g : Fin 9 → Fin 9) a = c ∧
      (g : Fin 9 → Fin 9) b = d := by
  have h2 := alternatingGroup_two_pretransitive
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨g, hgc, hgd⟩ := h2 hab hcd
  exact ⟨g, by simpa [Subgroup.smul_def] using hgc,
    by simpa [Subgroup.smul_def] using hgd⟩

theorem vp_ne_zero : vp ≠ 0 := by decide +kernel

theorem rho8p_eq_top_of_weight_two (T : Submodule (ZMod 2) V8)
    (hT : ∀ (g : alternatingGroup (Fin 9)) ⦃x : V8⦄, x ∈ T → (A9Mod.endHom rho8p) g x ∈ T)
    {y : V8} (hy : y ∈ T) (hcard : (supp9 y).card = 2) : T = ⊤ := by
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp hcard
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin 8)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨g, hga, hgb⟩ := exists_perm_pair a b (Fin.last 8) (Fin.castSucc i) hab
    (Fin.castSucc_ne_last i).symm
  have hmem : (A9Mod.endHom rho8p) g y ∈ T := hT g hy
  have hsupp' : supp9 ((A9Mod.endHom rho8p) g y) = {Fin.castSucc i, Fin.last 8} := by
    rw [A9Mod.endHom_apply, supp9_rho8p, hsupp]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [hga, hgb]
    exact Finset.pair_comm _ _
  have heq : (A9Mod.endHom rho8p) g y = Pi.single i 1 := eq_single_of_supp _ i hsupp'
  rw [heq] at hmem
  simpa using hmem

theorem rho8p_exists_weight_two (y : V8) (hy : y ≠ 0) (hcard : 4 ≤ (supp9 y).card) :
    ∃ σ : alternatingGroup (Fin 9),
      (y + (A9Mod.endHom rho8p) σ y) ≠ 0 ∧
        (supp9 (y + (A9Mod.endHom rho8p) σ y)).card = 2 := by
  obtain ⟨a, ha⟩ := supp9_nonempty hy
  have hnotuniv : supp9 y ≠ Finset.univ := by
    intro h
    have he := even_card_supp9 y
    rw [h, Finset.card_univ, Fintype.card_fin] at he
    exact absurd he (by decide)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ supp9 y := by
    by_contra h
    push Not at h
    exact hnotuniv (Finset.eq_univ_of_forall h)
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  obtain ⟨c, hcA, hca⟩ : ∃ c ∈ supp9 y, c ≠ a := by
    have h1 : 1 < ((supp9 y).erase a).card := by
      rw [Finset.card_erase_of_mem ha]
      omega
    obtain ⟨c, hc, _d, _hd, _hcd⟩ := Finset.one_lt_card.mp h1
    exact ⟨c, (Finset.mem_erase.mp hc).2, (Finset.mem_erase.mp hc).1⟩
  have hbc : b ≠ c := fun h => hb (h ▸ hcA)
  have hac : a ≠ c := hca.symm
  let σ : alternatingGroup (Fin 9) :=
    ⟨Equiv.swap a b * Equiv.swap b c, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbc]
      simp⟩
  have hσfun : ((σ : alternatingGroup (Fin 9)) : Fin 9 → Fin 9) =
      ((Equiv.swap a b : Equiv.Perm (Fin 9)) : Fin 9 → Fin 9) ∘
        ((Equiv.swap b c : Equiv.Perm (Fin 9)) : Fin 9 → Fin 9) := by
    funext x
    rfl
  have himg : (supp9 y).image ((σ : alternatingGroup (Fin 9)) : Fin 9 → Fin 9) =
      (supp9 y).erase c ∪ {b} := by
    have h1 : (supp9 y).image ((Equiv.swap b c : Equiv.Perm (Fin 9)) : Fin 9 → Fin 9) =
        (supp9 y).erase c ∪ {b} := by
      rw [Equiv.swap_comm]
      exact finset_image_swap_of_mem_of_notMem _ hcA hb
    have h2 : ((supp9 y).erase c ∪ {b}).image
        ((Equiv.swap a b : Equiv.Perm (Fin 9)) : Fin 9 → Fin 9) = (supp9 y).erase c ∪ {b} :=
      finset_image_swap_of_mem_of_mem _
        (by simp [hac, ha]) (by simp)
    rw [hσfun, Finset.image_comp, h1, h2]
  have hcb : c ≠ b := hbc.symm
  have hsym : (supp9 y) ∆ ((supp9 y).erase c ∪ {b}) = {c, b} := by
    ext j
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton]
    by_cases hjc : j = c
    · subst hjc; simp [hcA, hcb, hb]
    · by_cases hjb : j = b
      · subst hjb; simp [hb]
      · by_cases hjA : j ∈ supp9 y <;> simp [hjc, hjb, hjA, hb]
  have hz : (y + (A9Mod.endHom rho8p) σ y) ≠ 0 := by
    intro h
    have h2 : (supp9 (y + (A9Mod.endHom rho8p) σ y)).card = 2 := by
      rw [supp9_add, A9Mod.endHom_apply, supp9_rho8p, himg, hsym, Finset.card_pair_eq_two_iff]
      exact hcb
    rw [h] at h2
    have h0 : (supp9 (0 : V8)).card = 0 := by decide +kernel
    omega
  refine ⟨σ, hz, ?_⟩
  rw [supp9_add, A9Mod.endHom_apply, supp9_rho8p, himg, hsym, Finset.card_pair_eq_two_iff]
  exact hcb

theorem rho8p_eq_top (T : Submodule (ZMod 2) V8)
    (hT : ∀ (g : alternatingGroup (Fin 9)) ⦃x : V8⦄, x ∈ T → (A9Mod.endHom rho8p) g x ∈ T)
    {y : V8} (hy : y ∈ T) (hy0 : y ≠ 0) : T = ⊤ := by
  have heven := even_card_supp9 y
  have hpos : 0 < (supp9 y).card := (supp9_nonempty hy0).card_pos
  have hle : (supp9 y).card ≤ 9 := by
    simpa using Finset.card_le_univ (supp9 y)
  by_cases h2 : (supp9 y).card = 2
  · exact rho8p_eq_top_of_weight_two T hT hy h2
  · have h4 : 4 ≤ (supp9 y).card := by
      obtain ⟨m, hm⟩ := heven
      omega
    obtain ⟨σ, hz0, hzcard⟩ := rho8p_exists_weight_two y hy0 h4
    exact rho8p_eq_top_of_weight_two T hT (Submodule.add_mem T hy (hT σ hy)) hzcard

theorem rho8p_irreducible : Representation.IsIrreducible (A9Mod.endHom rho8p) := by
  apply isIrreducible_of_forall
  intro S hS
  have hTne : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective (by simpa using h))
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
  exact Subrepresentation.toSubmodule_injective (by
    simpa using rho8p_eq_top S.toSubmodule (fun g _ hx => S.apply_mem_toSubmodule g hx) hy hy0)

theorem rho8p_span_vp :
    Submodule.span (ZMod 2)
      (Set.range fun g : alternatingGroup (Fin 9) => (A9Mod.endHom rho8p) g vp) = ⊤ := by
  let T : Submodule (ZMod 2) V8 :=
    Submodule.span (ZMod 2) (Set.range fun g : alternatingGroup (Fin 9) => (A9Mod.endHom rho8p) g vp)
  have hinv : ∀ (g : alternatingGroup (Fin 9)) ⦃x : V8⦄, x ∈ T →
      (A9Mod.endHom rho8p) g x ∈ T := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨h, rfl⟩ := hz
        rw [← Module.End.mul_apply, ← map_mul]
        exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem T
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem T ihx ihy
    | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem T c ih
  exact rho8p_eq_top T hinv (Submodule.subset_span ⟨1, by simp⟩) vp_ne_zero

theorem rho8p_algebraMap_surjective :
    Function.Surjective (algebraMap (ZMod 2)
      (CFSG.Theory.Representation.End (A9Mod.endHom rho8p))) := by
  refine surjective_algebraMap_of_cyclic _ vp rho8p_span_vp
    {permWord w1, permWord w2} ?_ ?_
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · simpa [A9Mod.endHom_apply] using rho8p_w1_vp
    · simpa [A9Mod.endHom_apply] using rho8p_w2_vp
  · intro x hx
    have h1 : rho8p (permWord w1) x = x := by
      simpa [A9Mod.endHom_apply] using hx (permWord w1) (by simp)
    have h2 : rho8p (permWord w2) x = x := by
      simpa [A9Mod.endHom_apply] using hx (permWord w2) (by simp)
    rcases fixed_vp x h1 h2 with h | h
    · exact ⟨0, by rw [h, zero_smul]⟩
    · exact ⟨1, by rw [h, one_smul]⟩

theorem rho8p_absIrr :
    CFSG.Theory.Representation.IsAbsolutelyIrreducible (A9Mod.endHom rho8p) := by
  haveI : FiniteDimensional (ZMod 2) V8 := inferInstance
  haveI : Representation.IsIrreducible (A9Mod.endHom rho8p) := rho8p_irreducible
  exact (CFSG.Theory.Representation.isAbsolutelyIrreducible_iff_surjective _).mpr
    rho8p_algebraMap_surjective

theorem injective_of_pow_eq_one {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (n : ℕ) (hn : 0 < n) (h : T ^ n = 1) : Function.Injective T := by
  intro x y hxy
  have hzero : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hxy0 : x - y = 0 := by
    calc x - y = (T ^ (k + 1)) (x - y) := by rw [h, Module.End.one_apply]
      _ = (T ^ k) (T (x - y)) := by rw [pow_succ, Module.End.mul_apply]
      _ = 0 := by rw [hzero, map_zero]
  exact sub_eq_zero.mp hxy0

theorem a9AbsIrrStatement_holds : A9AbsIrrStatement := by
  intro U _ _ _ ρ hρ hU
  have hinj : ∀ g : alternatingGroup (Fin 9), Function.Injective (ρ g) := fun g =>
    injective_of_pow_eq_one (ρ g) (orderOf g) (orderOf_pos g) (by
      rw [← map_pow, pow_orderOf_eq_one, map_one])
  let ρu : alternatingGroup (Fin 9) →* (U ≃ₗ[ZMod 2] U) :=
    { toFun := fun g => LinearEquiv.ofInjectiveEndo (ρ g) (hinj g)
      map_one' := by
        ext v
        rw [LinearEquiv.coe_ofInjectiveEndo]
        simp
      map_mul' := fun g h => by
        ext v
        rw [LinearEquiv.coe_ofInjectiveEndo, LinearEquiv.mul_apply,
          LinearEquiv.coe_ofInjectiveEndo, LinearEquiv.coe_ofInjectiveEndo, map_mul,
          Module.End.mul_apply] }
  have hend : A9Mod.endHom ρu = ρ := by
    ext g v
    change (LinearEquiv.ofInjectiveEndo (ρ g) (hinj g)) v = ρ g v
    rw [LinearEquiv.coe_ofInjectiveEndo]
  have hfaith : Function.Injective ρu := by
    intro g h hgh
    apply hρ
    have h2 : (A9Mod.endHom ρu) g = (A9Mod.endHom ρu) h := by
      ext v
      rw [A9Mod.endHom_apply, A9Mod.endHom_apply, hgh]
    calc ρ g = A9Mod.endHom ρu g := by rw [hend]
      _ = A9Mod.endHom ρu h := h2
      _ = ρ h := by rw [hend]
  obtain ⟨σ, e, he | he⟩ := a9FaithfulDimEight_holds (V := U) hU ρu hfaith
  · have hRep : CFSG.Theory.Representation.RepEquiv ρ
        ((A9Mod.endHom rho8a).comp (conjA σ).toMonoidHom) :=
      CFSG.Theory.Representation.RepEquiv.mk e fun g => by
        ext v i
        have h1 : ρ g v = ρu g v := by
          rw [← hend]
          rfl
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply,
          h1, A9Mod.endHom_apply]
        exact congrFun (he g v) i
    exact (CFSG.RankThree.GF2n.Tim79a.isAbsolutelyIrreducible_iff_of_repEquiv hRep).mpr
      ((isAbsolutelyIrreducible_comp_aut (A9Mod.endHom rho8a) (conjA σ)).mpr rho8a_absIrr)
  · have hRep : CFSG.Theory.Representation.RepEquiv ρ (A9Mod.endHom rho8p) :=
      CFSG.Theory.Representation.RepEquiv.mk e fun g => by
        ext v i
        have h1 : ρ g v = ρu g v := by
          rw [← hend]
          rfl
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, A9Mod.endHom_apply]
        exact congrFun (he g v) i
    exact (CFSG.RankThree.GF2n.Tim79a.isAbsolutelyIrreducible_iff_of_repEquiv hRep).mpr
      rho8p_absIrr

end CFSG.RankThree.GF2n.Tim79a

end
