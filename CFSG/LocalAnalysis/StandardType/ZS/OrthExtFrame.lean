module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtWitt
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtLemmas
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.OrthRefl
public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.ClassicalGroups.Orthogonal.TwoHyperplanes.Basic
public import CFSG.LieType.Universal.SpinOmega.Reflections

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private def IsFullType (Q : QuadraticForm (ZMod p) U)
    (H : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  H = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
    HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H}

private def IsClassType (Q : QuadraticForm (ZMod p) U)
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (c : ZMod p) : Prop :=
  H = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
    HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H}

private theorem commute_reflect_reflect {Q : QuadraticForm (ZMod p) U} {a b : U}
    (h : polar Q a b = 0) :
    reflect Q a * reflect Q b = reflect Q b * reflect Q a := by
  have hconj := reflect_conj (reflect_mem_orthogonalGroup Q a) b
  have hfix : reflect Q a b = b := reflect_apply_of_polar_eq_zero h
  rw [hfix] at hconj
  have hinv : (reflect Q a)⁻¹ = reflect Q a :=
    inv_eq_of_mul_eq_one_left (reflect_mul_self Q a)
  calc reflect Q a * reflect Q b
      = reflect Q a * reflect Q b * 1 := (mul_one _).symm
    _ = reflect Q a * reflect Q b * ((reflect Q a)⁻¹ * reflect Q a) := by
        rw [inv_mul_cancel]
    _ = (reflect Q a * reflect Q b * (reflect Q a)⁻¹) * reflect Q a := by group
    _ = reflect Q b * reflect Q a := by rw [hconj]

private theorem mem_orthogonal_polar_iff {Q : QuadraticForm (ZMod p) U}
    {W : Submodule (ZMod p) U} {v : U} :
    v ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W ↔
      ∀ x ∈ W, polar Q x v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp [QuadraticMap.polarBilin_apply_apply]

private theorem polar_eq_zero_of_mem_centralizerSpace_of_mem_commutatorSpace
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    (hiso : ∀ h ∈ H, IsIsom p Q h) {u v : U}
    (hu : u ∈ centralizerSpace H) (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H) :
    polar Q v u = 0 := by
  rw [HardMathSupport.Kantor79.commutatorSpace] at hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨h, hh, w, rfl⟩
    rw [polar_sub_left]
    have hfix : h u = u := (mem_centralizerSpace).mp hu h hh
    have hpol := (hiso h hh).polar_apply w u
    rw [hfix] at hpol
    rw [hpol, sub_self]
  · rw [polar_zero_left]
  · intro x y hx hy ihx ihy
    rw [polar_add_left, ihx, ihy, add_zero]
  · intro c x hx ih
    rw [polar_smul_left, ih, smul_zero]

private theorem polarNondegOn_of_isCompl_of_orthogonal
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {W C : Submodule (ZMod p) U} (hcompl : IsCompl W C)
    (horth : ∀ w ∈ W, ∀ c ∈ C, polar Q w c = 0) : PolarNondegOn Q W := by
  intro x hxW hx
  apply hQ.1 x
  intro y
  have hy : y ∈ W ⊔ C := by rw [hcompl.sup_eq_top]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hy
  rw [QuadraticMap.polarBilin_apply_apply, polar_add_right, hx w hw, horth x hxW c hc,
    add_zero]

private theorem exists_ne_zero_mem_of_finrank_eq_one {C : Submodule (ZMod p) U}
    [Module.Finite (ZMod p) U] (hC : Module.finrank (ZMod p) C = 1) :
    ∃ e ∈ C, e ≠ 0 := by
  have hne : C ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hC
    omega
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

private noncomputable def frameIdx (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (i : Fin (Module.finrank (ZMod p) U - 2)) :
    Fin (Module.finrank (ZMod p) U - 1) :=
  ⟨i.val, by omega⟩

private noncomputable def frameLast (h4 : 4 ≤ Module.finrank (ZMod p) U) :
    Fin (Module.finrank (ZMod p) U - 1) :=
  ⟨Module.finrank (ZMod p) U - 2, by omega⟩

private noncomputable def frameZero (h4 : 4 ≤ Module.finrank (ZMod p) U) :
    Fin (Module.finrank (ZMod p) U - 2) :=
  ⟨0, by omega⟩

private noncomputable def frameOne (h4 : 4 ≤ Module.finrank (ZMod p) U) :
    Fin (Module.finrank (ZMod p) U - 2) :=
  ⟨1, by omega⟩

private noncomputable def framePenultimate (h4 : 4 ≤ Module.finrank (ZMod p) U) :
    Fin (Module.finrank (ZMod p) U - 2) :=
  ⟨Module.finrank (ZMod p) U - 3, by omega⟩

private noncomputable def frameTwo (h5 : 5 ≤ Module.finrank (ZMod p) U) :
    Fin (Module.finrank (ZMod p) U - 2) :=
  ⟨2, by omega⟩

private noncomputable def frameE {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    (i : Fin (Module.finrank (ZMod p) U - 2)) : U :=
  (v (frameIdx h4 i) : U)

private noncomputable def frameELast {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)) : U :=
  (v (frameLast h4) : U)

private noncomputable def frameW {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) (Set.range (frameE h4 v))

private noncomputable def frameZ {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    (Q : QuadraticForm (ZMod p) U) : U ≃ₗ[ZMod p] U :=
  ((List.finRange (Module.finrank (ZMod p) U - 2)).map
    (fun i => reflect Q (frameE h4 v i))).prod

private theorem list_prod_mem_of_mem {G : Type*} [Group G] {K : Subgroup G} {l : List G}
    (h : ∀ x ∈ l, x ∈ K) : l.prod ∈ K :=
  Subgroup.list_prod_mem K h

private theorem list_prod_commute_of_forall {G : Type*} [Group G] {l : List G} {a : G}
    (h : ∀ x ∈ l, a * x = x * a) : a * l.prod = l.prod * a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.prod_cons, ← mul_assoc, h x (by simp), mul_assoc,
        ih (fun y hy => h y (by simp [hy])), mul_assoc]

private theorem list_prod_apply_of_forall_eq {ι : Type*} (l : List ι)
    (f : ι → U ≃ₗ[ZMod p] U) (x : U) (h : ∀ i ∈ l, f i x = x) :
    (l.map f).prod x = x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply,
        ih (fun i hi => h i (by simp [hi]))]
      exact h a (by simp)

private theorem list_prod_apply_of_forall_eq_of_mem_neg {ι : Type*} (l : List ι)
    (hl : l.Nodup) (f : ι → U ≃ₗ[ZMod p] U) (x : U) (i0 : ι) (hi0 : i0 ∈ l)
    (hfix : ∀ i ∈ l, i ≠ i0 → f i x = x) (hneg : f i0 x = -x) :
    (l.map f).prod x = -x := by
  induction l with
  | nil => simp at hi0
  | cons a l ih =>
      obtain ⟨hal, hl'⟩ := List.nodup_cons.mp hl
      rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply]
      by_cases ha : a = i0
      · subst ha
        have hfix' : ∀ i ∈ l, i ≠ a → f i x = x := by
          intro i hi hne
          exact hfix i (by simp [hi]) hne
        have hprod : (l.map f).prod x = x :=
          list_prod_apply_of_forall_eq l f x (fun i hi => hfix' i hi (by
            intro h; subst h; exact hal hi))
        rw [hprod, hneg]
      · have hfa : f a x = x := hfix a (by simp) ha
        have hfix' : ∀ i ∈ l, i ≠ i0 → f i x = x := by
          intro i hi hne
          exact hfix i (by simp [hi]) hne
        have hprod : (l.map f).prod x = -x := ih hl' (by
          rcases List.mem_cons.mp hi0 with h | h
          · exact absurd h.symm ha
          · exact h) hfix'
        rw [hprod, map_neg, hfa]

private theorem frameZ_apply_of_mem_orthogonal {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} {w : U}
    (hw : w ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (frameW h4 v)) :
    frameZ h4 v Q w = w := by
  apply list_prod_apply_of_forall_eq
  intro i hi
  apply reflect_apply_of_polar_eq_zero
  have hw' := (mem_orthogonal_polar_iff (Q := Q)).mp hw
  exact hw' (frameE h4 v i) (Submodule.subset_span ⟨i, rfl⟩)

private theorem frameZ_apply_frameE {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (i0 : Fin (Module.finrank (ZMod p) U - 2)) :
    frameZ h4 v Q (frameE h4 v i0) = -frameE h4 v i0 := by
  apply list_prod_apply_of_forall_eq_of_mem_neg (List.finRange _)
    (List.nodup_finRange _) (fun i => reflect Q (frameE h4 v i)) (frameE h4 v i0) i0
    (List.mem_finRange i0)
  · intro i hi hne
    apply reflect_apply_of_polar_eq_zero
    exact hvorth i i0 hne
  · apply reflect_apply_self
    rw [hQnorm i0]
    exact hc0

private theorem frame_apply_of_mem {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    {w : U} (hw : w ∈ frameW h4 v) :
    frameZ h4 v Q w = -w := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨i, rfl⟩
    exact frameZ_apply_frameE h4 v c0 hc0 hQnorm hvorth i
  · rw [map_zero, neg_zero]
  · intro x y hx hy ihx ihy
    rw [map_add, ihx, ihy]
    abel
  · intro c x hx ih
    rw [map_smul, ih, smul_neg]

private theorem exists_beta_gamma_of_eq_neg_one (hp2 : p ≠ 2) (hp3 : p ≠ 3) {ν : ZMod p}
    (hν : ¬ IsSquare ν) (hν1 : ν = -1) :
    ∃ β γ : ZMod p, β ≠ 0 ∧ γ ≠ 0 ∧ γ ^ 2 + ν * β ^ 2 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  let u : ZMod p := (2 + ν / 2) / 2
  let t : ZMod p := (ν / 2 - 2) / 2
  have huv : u ^ 2 - t ^ 2 = ν := by
    dsimp [u, t]
    field_simp [h2]
    ring
  have ht : t ≠ 0 := by
    intro ht0
    apply hν
    refine ⟨u, ?_⟩
    have hνeq : ν = u ^ 2 := by
      rw [← huv, ht0]
      ring
    rw [hνeq, pow_two]
  have hu : u ≠ 0 := by
    intro hu0
    apply hp3
    have h3 : (3 : ZMod p) = 0 := by
      dsimp [u] at hu0
      rw [hν1] at hu0
      field_simp [h2] at hu0
      linear_combination hu0
    have hprime : p.Prime := Fact.out
    exact (Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  refine ⟨u⁻¹, t * u⁻¹, inv_ne_zero hu, mul_ne_zero ht (inv_ne_zero hu), ?_⟩
  have hmain : t ^ 2 + ν = u ^ 2 := by
    rw [← huv]
    ring
  field_simp [hu]
  rw [hmain]

private theorem exists_beta_gamma_of_ne_neg_one (hp2 : p ≠ 2) {ν : ZMod p}
    (hν : ¬ IsSquare ν) (hν1 : ν ≠ -1) :
    ∃ β γ : ZMod p, β ≠ 0 ∧ γ ≠ 0 ∧ γ ^ 2 + ν * β ^ 2 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  let u : ZMod p := (1 + ν) / 2
  let t : ZMod p := (ν - 1) / 2
  have huv : u ^ 2 - t ^ 2 = ν := by
    dsimp [u, t]
    field_simp [h2]
    ring
  have ht : t ≠ 0 := by
    intro ht0
    apply hν
    refine ⟨u, ?_⟩
    have hνeq : ν = u ^ 2 := by
      rw [← huv, ht0]
      ring
    rw [hνeq, pow_two]
  have hu : u ≠ 0 := by
    intro hu0
    apply hν1
    dsimp [u] at hu0
    field_simp [h2] at hu0
    linear_combination hu0
  refine ⟨u⁻¹, t * u⁻¹, inv_ne_zero hu, mul_ne_zero ht (inv_ne_zero hu), ?_⟩
  have hmain : t ^ 2 + ν = u ^ 2 := by
    rw [← huv]
    ring
  field_simp [hu]
  rw [hmain]

private theorem exists_beta_gamma (hp2 : p ≠ 2) (hp3 : p ≠ 3) {ν : ZMod p}
    (hν : ¬ IsSquare ν) :
    ∃ β γ : ZMod p, β ≠ 0 ∧ γ ≠ 0 ∧ γ ^ 2 + ν * β ^ 2 = 1 := by
  by_cases hν1 : ν = -1
  · exact exists_beta_gamma_of_eq_neg_one hp2 hp3 hν hν1
  · exact exists_beta_gamma_of_ne_neg_one hp2 hν hν1

private theorem frameW_le_commutatorSpace {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)) :
    frameW h4 v ≤ HardMathSupport.Kantor79.commutatorSpace H := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact (v (frameIdx h4 i)).2

private theorem mem_span_coe_iff {H : Subgroup (U ≃ₗ[ZMod p] U)} {ι : Type*}
    (w : ι → HardMathSupport.Kantor79.commutatorSpace H)
    {x : HardMathSupport.Kantor79.commutatorSpace H} :
    (x : U) ∈ Submodule.span (ZMod p) (Set.range fun i => (w i : U)) ↔
      x ∈ Submodule.span (ZMod p) (Set.range w) := by
  have hmap : (Submodule.span (ZMod p) (Set.range w)).map
      (HardMathSupport.Kantor79.commutatorSpace H).subtype =
      Submodule.span (ZMod p) (Set.range fun i => (w i : U)) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨w i, ⟨i, rfl⟩, rfl⟩
  constructor
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    rwa [show y = x from Subtype.ext hyx] at hy
  · intro hx
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

private theorem frameIdx_injective (h4 : 4 ≤ Module.finrank (ZMod p) U) :
    Function.Injective (frameIdx (p := p) (U := U) h4) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [frameIdx] using this

private theorem frameIdx_ne_last (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (i : Fin (Module.finrank (ZMod p) U - 2)) :
    frameIdx (p := p) (U := U) h4 i ≠ frameLast (p := p) (U := U) h4 := by
  intro h
  have := congrArg Fin.val h
  simp [frameIdx, frameLast] at this
  omega

private theorem frameELast_not_mem_frameW {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)) :
    frameELast h4 v ∉ frameW h4 v := by
  intro hmem
  have hmemV : v (frameLast h4) ∈ Submodule.span (ZMod p)
      (Set.range fun i => v (frameIdx h4 i)) :=
    (mem_span_coe_iff (fun i => v (frameIdx h4 i))).mp hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hmemV
  have hcoord1 : v.coord (frameLast h4) (v (frameLast h4)) = 1 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    simp
  have hcoord0 : v.coord (frameLast h4) (v (frameLast h4)) = 0 := by
    rw [← hc, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    rw [if_neg (frameIdx_ne_last h4 i), smul_zero]
  rw [hcoord1] at hcoord0
  exact one_ne_zero hcoord0

private theorem frameW_restrict_nondegenerate {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) (frameW h4 v)).Nondegenerate := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h := (CFSG.RankThree.Classical.nondegenerate_restrict_span h2 Q hvorth
    (fun i => by rw [hQnorm i]; exact hc0)).2
  change (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q)
    (Submodule.span (ZMod p) (Set.range (frameE h4 v)))).Nondegenerate
  exact h

private theorem frameW_isCompl {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    IsCompl (frameW h4 v)
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (frameW h4 v)) := by
  have hrefl : (QuadraticMap.polarBilin Q).IsRefl := fun x y h => by
    rw [QuadraticMap.polarBilin_apply_apply] at h ⊢
    rwa [QuadraticMap.polar_comm]
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl
    (frameW_restrict_nondegenerate hp h4 v c0 hc0 hQnorm hvorth)

private theorem frame_mem {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U}
    (hgen : ∀ i : Fin (Module.finrank (ZMod p) U - 2), reflect Q (frameE h4 v i) ∈ H) :
    frameZ h4 v Q ∈ H := by
  apply list_prod_mem_of_mem
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  exact hgen i

private theorem frameZ_mul_self {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    frameZ h4 v Q * frameZ h4 v Q = 1 := by
  ext x
  have hcompl := frameW_isCompl hp h4 v c0 hc0 hQnorm hvorth
  have hx : x ∈ frameW h4 v ⊔
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (frameW h4 v) := by
    rw [hcompl.sup_eq_top]
    trivial
  obtain ⟨w, hw, y, hy, hxy⟩ := Submodule.mem_sup.mp hx
  have hzw := frame_apply_of_mem h4 v c0 hc0 hQnorm hvorth hw
  have hzy := frameZ_apply_of_mem_orthogonal h4 v hy
  calc (frameZ h4 v Q * frameZ h4 v Q) x
      = frameZ h4 v Q (frameZ h4 v Q x) := by rw [LinearEquiv.mul_apply]
    _ = frameZ h4 v Q (frameZ h4 v Q (w + y)) := by rw [← hxy]
    _ = frameZ h4 v Q (frameZ h4 v Q w + frameZ h4 v Q y) := by rw [map_add]
    _ = frameZ h4 v Q (-w + y) := by rw [hzw, hzy]
    _ = frameZ h4 v Q (-w) + frameZ h4 v Q y := by rw [map_add]
    _ = - frameZ h4 v Q w + frameZ h4 v Q y := by rw [map_neg]
    _ = -(-w) + y := by rw [hzw, hzy]
    _ = w + y := by rw [neg_neg]
    _ = x := hxy

private theorem movedSpace_frameZ_eq_frameW {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q) = frameW h4 v := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hcompl := frameW_isCompl hp h4 v c0 hc0 hQnorm hvorth
    have hx : x ∈ frameW h4 v ⊔
        LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (frameW h4 v) := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨w, hw, y, hy, hxy⟩ := Submodule.mem_sup.mp hx
    have hzw := frame_apply_of_mem h4 v c0 hc0 hQnorm hvorth hw
    have hzy := frameZ_apply_of_mem_orthogonal h4 v hy
    have hval : frameZ h4 v Q x - x = -(2 : ZMod p) • w := by
      rw [← hxy, map_add, hzw, hzy]
      module
    change frameZ h4 v Q x - x ∈ frameW h4 v
    rw [hval]
    exact Submodule.smul_mem _ (-(2 : ZMod p)) hw
  · intro w hw
    exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp)
      (frame_apply_of_mem h4 v c0 hc0 hQnorm hvorth hw)

private theorem finrank_frameW {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    Module.finrank (ZMod p) (frameW h4 v) = Module.finrank (ZMod p) U - 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hli := (CFSG.RankThree.Classical.nondegenerate_restrict_span h2 Q hvorth
    (fun i => by rw [hQnorm i]; exact hc0)).1
  rw [frameW, finrank_span_eq_card hli, Fintype.card_fin]

private theorem finrank_movedSpace_frameZ {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q)) + 2 =
      Module.finrank (ZMod p) U := by
  rw [movedSpace_frameZ_eq_frameW hp h4 v c0 hc0 hQnorm hvorth,
    finrank_frameW hp h4 v c0 hc0 hQnorm hvorth]
  omega

private theorem exists_h_frame {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hgen : ∀ i : Fin (Module.finrank (ZMod p) U - 2), reflect Q (frameE h4 v i) ∈ H) :
    ∃ h ∈ (Set.univ : Set (U ≃ₗ[ZMod p] U)), h ∈ H ∧ IsRefl p h ∧
      h * frameZ h4 v Q = frameZ h4 v Q * h ∧
      HardMathSupport.Kantor79.movedSpace h ≤
        HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q) := by
  let h : U ≃ₗ[ZMod p] U := reflect Q (frameE h4 v (frameZero h4))
  have hhH : h ∈ H := hgen (frameZero h4)
  have hhrefl : IsRefl p h := by
    apply isRefl_reflect hp
    rw [hQnorm (frameZero h4)]
    exact hc0
  have hcomm : ∀ g ∈ (List.finRange (Module.finrank (ZMod p) U - 2)).map
      (fun i => reflect Q (frameE h4 v i)), h * g = g * h := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    by_cases hiz : i = frameZero h4
    · subst hiz
      rw [reflect_mul_self]
    · exact commute_reflect_reflect (hvorth (frameZero h4) i (fun h => hiz h.symm))
  have hhz : h * frameZ h4 v Q = frameZ h4 v Q * h := by
    simpa [frameZ] using list_prod_commute_of_forall (a := h) hcomm
  have hV : HardMathSupport.Kantor79.movedSpace h ≤
      HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q) := by
    rw [movedSpace_reflect_eq_span hp (by rw [hQnorm (frameZero h4)]; exact hc0),
      movedSpace_frameZ_eq_frameW hp h4 v c0 hc0 hQnorm hvorth]
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Submodule.subset_span ⟨frameZero h4, rfl⟩
  exact ⟨h, Set.mem_univ _, hhH, hhrefl, hhz, hV⟩

private theorem mem_span_pair_of_mem_frameW_of_finrank_four {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    (h4eq : Module.finrank (ZMod p) U = 4) {a : U} (ha : a ∈ frameW h4 v) :
    a ∈ Submodule.span (ZMod p)
      ({frameE h4 v (frameZero h4), frameE h4 v (frameOne h4)} : Set U) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp ha
  have hzero_one : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      i = frameZero h4 ∨ i = frameOne h4 := by
    intro i
    have hlt : i.val < 2 := by have := i.isLt; omega
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · left
      apply Fin.ext
      simp [frameZero, h0]
    · right
      apply Fin.ext
      have h1 : i.val = 1 := by omega
      simp [frameOne, h1]
  have hne : frameZero h4 ≠ frameOne h4 := by
    intro h
    have := congrArg Fin.val h
    simp [frameZero, frameOne] at this
  have hsum : (∑ i, c i • frameE h4 v i) =
      c (frameZero h4) • frameE h4 v (frameZero h4) +
        c (frameOne h4) • frameE h4 v (frameOne h4) := by
    refine Fintype.sum_eq_add (frameZero h4) (frameOne h4) hne ?_
    intro x hx
    rcases hzero_one x with h | h
    · exact absurd h hx.1
    · exact absurd h hx.2
  rw [← hc, hsum]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem exists_plane_orthogonal_same_norm {Q : QuadraticForm (ZMod p) U}
    {u w a : U} (huw : polar Q u w = 0) (hQeq : Q u = Q w)
    (ha : a ∈ Submodule.span (ZMod p) ({u, w} : Set U)) :
    ∃ b ∈ Submodule.span (ZMod p) ({u, w} : Set U), Q b = Q a ∧ polar Q a b = 0 := by
  obtain ⟨α, β, rfl⟩ := (Submodule.mem_span_pair).mp ha
  refine ⟨-β • u + α • w, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · have hQa : Q (α • u + β • w) = (α * α) * Q u + (β * β) * Q w := by
      rw [show Q (α • u + β • w) = Q (α • u) + Q (β • w) + polar Q (α • u) (β • w)
        from QuadraticMap.map_add Q (α • u) (β • w), QuadraticMap.map_smul Q α u,
        QuadraticMap.map_smul Q β w, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul, huw, mul_zero, add_zero]
    have hQb : Q (-β • u + α • w) = (β * β) * Q u + (α * α) * Q w := by
      rw [show Q (-β • u + α • w) = Q (-β • u) + Q (α • w) + polar Q (-β • u) (α • w)
        from QuadraticMap.map_add Q (-β • u) (α • w), QuadraticMap.map_smul Q (-β) u,
        QuadraticMap.map_smul Q α w, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul, huw, mul_zero, add_zero, neg_mul_neg]
    rw [hQa, hQb, hQeq]
    ring
  · simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_neg_right, huw, QuadraticMap.polar_comm Q w u,
      QuadraticMap.polar_self, hQeq, smul_zero, add_zero, zero_add, neg_smul, smul_smul]
    ring

private theorem mem_classRefl_of_mem_classType {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (hclass : IsClassType (p := p) Q H c) {x : U ≃ₗ[ZMod p] U} (hxH : x ∈ H)
    (hxr : IsRefl p x) : x ∈ ClassRefl p Q c := by
  have hle : Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H} ≤
      Subgroup.closure (ClassRefl p Q c) :=
    (Subgroup.closure_le (Subgroup.closure (ClassRefl p Q c))).mpr
      (fun t ht => Subgroup.subset_closure ht.1)
  exact mem_classRefl_of_isRefl_mem_closure hp hQ hc (hle (hclass ▸ hxH)) hxr

private theorem exists_root_mem_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hX : IsOrthOn p Q H)
    {x : U ≃ₗ[ZMod p] U} (hxH : x ∈ H) (hxr : IsRefl p x) :
    ∃ a ∈ HardMathSupport.Kantor79.commutatorSpace H, Q a ≠ 0 ∧ x = reflect Q a := by
  have hmemVH : ∀ {b : U}, Q b ≠ 0 → x = reflect Q b →
      b ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro b hbQ hxb
    have hbVx : b ∈ HardMathSupport.Kantor79.movedSpace x := by
      rw [hxb, movedSpace_reflect_eq_span hp hbQ]
      exact Submodule.subset_span (Set.mem_singleton b)
    exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hxH hbVx
  rcases hX with hfull | ⟨c, hc, hclass⟩
  · have hxiso : IsIsom p Q x :=
      IsOrthOn.isIsom (X := H) (Q := Q) (Or.inl hfull) hxH
    obtain ⟨a, haQ, hax⟩ :=
      CFSG.StandardType.ZS.DimThree.exists_root_of_isRefl_isIsom hp hQ hxr hxiso
    have hxClass : x ∈ ClassRefl p Q (Q a) := ⟨hxr, hxiso, a, rfl, hax⟩
    obtain ⟨b, hQb, hxb⟩ := (mem_classRefl_iff hp hQ haQ x).mp hxClass
    exact ⟨b, hmemVH (by rw [hQb]; exact haQ) hxb, by rw [hQb]; exact haQ, hxb⟩
  · have hle : Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
        HardMathSupport.Kantor79.movedSpace t ≤
          HardMathSupport.Kantor79.commutatorSpace H} ≤
        Subgroup.closure (ClassRefl p Q c) :=
      (Subgroup.closure_le (Subgroup.closure (ClassRefl p Q c))).mpr
        (fun t ht => Subgroup.subset_closure ht.1)
    have hxClosure : x ∈ Subgroup.closure (ClassRefl p Q c) := hle (hclass ▸ hxH)
    have hxClass := mem_classRefl_of_isRefl_mem_closure hp hQ hc hxClosure hxr
    obtain ⟨b, hQb, hxb⟩ := (mem_classRefl_iff hp hQ hc x).mp hxClass
    exact ⟨b, hmemVH (by rw [hQb]; exact hc) hxb, by rw [hQb]; exact hc, hxb⟩

private theorem reflect_mem_of_isOrthOn_full [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hfull : H = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H})
    {b : U} (hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace H) (hb : Q b ≠ 0) :
    reflect Q b ∈ H := by
  rw [hfull]
  apply Subgroup.subset_closure
  refine ⟨isRefl_reflect hp hb, isIsom_reflect Q b, ?_⟩
  rw [movedSpace_reflect_eq_span hp hb]
  exact Submodule.span_le.mpr (by rintro _ rfl; exact hbV)

private theorem reflect_mem_of_isOrthOn_class [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {c : ZMod p} (hc : c ≠ 0)
    (hclass : H = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H})
    {b : U} (hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace H) (hb : Q b = c) :
    reflect Q b ∈ H := by
  rw [hclass]
  apply Subgroup.subset_closure
  refine ⟨(mem_classRefl_iff hp hQ hc (reflect Q b)).mpr ⟨b, hb, rfl⟩, ?_⟩
  rw [movedSpace_reflect_eq_span hp (by rw [hb]; exact hc)]
  exact Submodule.span_le.mpr (by rintro _ rfl; exact hbV)

private theorem frameW_polarNondegOn {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    PolarNondegOn Q (frameW h4 v) := by
  have hnd := frameW_restrict_nondegenerate hp h4 v c0 hc0 hQnorm hvorth
  intro x hx hxorth
  have hx0 : (⟨x, hx⟩ : frameW h4 v) = 0 := by
    refine hnd.1 ⟨x, hx⟩ fun y => ?_
    simpa [CFSG.ClassicalGroups.Orthogonal.polar_restrict] using hxorth y y.2
  exact congrArg Subtype.val hx0

private theorem exists_b_frame_dim_four {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (c0 : ZMod p)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (h4eq : Module.finrank (ZMod p) U = 4) {a : U} (haW : a ∈ frameW h4 v) :
    ∃ b ∈ frameW h4 v, Q b = Q a ∧ polar Q a b = 0 := by
  have hne : frameZero h4 ≠ frameOne h4 := by
    intro h
    have := congrArg Fin.val h
    simp [frameZero, frameOne] at this
  have huw : polar Q (frameE h4 v (frameZero h4)) (frameE h4 v (frameOne h4)) = 0 :=
    hvorth _ _ hne
  have hQeq : Q (frameE h4 v (frameZero h4)) = Q (frameE h4 v (frameOne h4)) := by
    rw [hQnorm, hQnorm]
  have hspan := mem_span_pair_of_mem_frameW_of_finrank_four h4 v h4eq haW
  obtain ⟨b, hbSpan, hQb, hpol⟩ := exists_plane_orthogonal_same_norm huw hQeq hspan
  refine ⟨b, ?_, hQb, hpol⟩
  refine Submodule.span_le.mpr ?_ hbSpan
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Submodule.subset_span ⟨frameZero h4, rfl⟩
  · exact Submodule.subset_span ⟨frameOne h4, rfl⟩

private theorem exists_b_of_inf_ker (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {W : Submodule (ZMod p) U}
    (hWnd : PolarNondegOn Q W) (hfinW : Module.finrank (ZMod p) W =
      Module.finrank (ZMod p) U - 2)
    {a : U} (haW : a ∈ W) (haQ : Q a ≠ 0) (d : ZMod p)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) :
    ∃ b ∈ W, Q b = d ∧ polar Q a b = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let S : Submodule (ZMod p) U := LinearMap.ker (QuadraticMap.polarBilin Q a)
  have hSnd : PolarNondegOn Q (W ⊓ S) := PolarNondegOn.inf_ker h2 hWnd haW haQ
  have hdim : 2 ≤ Module.finrank (ZMod p) ↥(W ⊓ S) := by
    have h1 := finrank_inf_ker_polarBilin_add_one h2 haW haQ
    dsimp [S] at h1 ⊢
    omega
  obtain ⟨b, hbS, hQb⟩ := hSnd.exists_map_eq h2 hdim d
  refine ⟨b, hbS.1, hQb, ?_⟩
  have hker := hbS.2
  dsimp [S] at hker
  simpa [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] using hker

private theorem isCaseCRefl_of_mem {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c0 : ZMod p) (hc0 : c0 ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0)
    (hQlast : Q (frameELast h4 v) ≠ 0)
    (hτH : reflect Q (frameELast h4 v) ∈ H) :
    IsCaseCRefl p H (frameZ h4 v Q) (reflect Q (frameELast h4 v)) := by
  refine ⟨hτH, isRefl_reflect hp hQlast, ?_, ?_⟩
  · have hcomm : ∀ g ∈ (List.finRange (Module.finrank (ZMod p) U - 2)).map
        (fun i => reflect Q (frameE h4 v i)),
        reflect Q (frameELast h4 v) * g = g * reflect Q (frameELast h4 v) := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
      exact commute_reflect_reflect (hvorthLast i)
    simpa [frameZ] using
      list_prod_commute_of_forall (a := reflect Q (frameELast h4 v)) hcomm
  · rw [movedSpace_reflect_eq_span hp hQlast,
      movedSpace_frameZ_eq_frameW hp h4 v c0 hc0 hQnorm hvorth]
    intro hle
    exact frameELast_not_mem_frameW h4 v
      (hle (Submodule.subset_span (Set.mem_singleton (frameELast h4 v))))

private theorem frameELast_mem_orthogonal_frameW {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U}
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0) :
    frameELast h4 v ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (frameW h4 v) := by
  rw [mem_orthogonal_polar_iff]
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [polar_comm]
    exact hvorthLast i
  · rw [polar_zero_left]
  · intro a b ha hb iha ihb
    rw [polar_add_left, iha, ihb, add_zero]
  · intro a b hb ih
    rw [polar_smul_left, ih, smul_zero]

private theorem quadratic_frameD_ne_three (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (hc : c ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0)
    {β γ : ZMod p}
    (hβγ : γ ^ 2 + (Q (frameELast h4 v) / c) * β ^ 2 = 1) :
    Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) = c := by
  have hν : Q (frameELast h4 v) = (Q (frameELast h4 v) / c) * c := by
    field_simp [hc]
  have hQe' : Q (frameE h4 v (framePenultimate h4)) = c := hQnorm _
  have hpol : polar Q (frameELast h4 v) (frameE h4 v (framePenultimate h4)) = 0 :=
    hvorthLast _
  have hQw : Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) =
      (β * β) * Q (frameELast h4 v) +
        (γ * γ) * Q (frameE h4 v (framePenultimate h4)) := by
    rw [show Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) =
        Q (β • frameELast h4 v) + Q (γ • frameE h4 v (framePenultimate h4)) +
          polar Q (β • frameELast h4 v) (γ • frameE h4 v (framePenultimate h4))
        from QuadraticMap.map_add Q _ _]
    rw [QuadraticMap.map_smul Q β (frameELast h4 v),
      QuadraticMap.map_smul Q γ (frameE h4 v (framePenultimate h4)),
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpol]
    simp only [smul_eq_mul, mul_zero, add_zero]
  rw [hQw, hQe', hν]
  calc (β * β) * ((Q (frameELast h4 v) / c) * c) + (γ * γ) * c
      = c * (γ ^ 2 + (Q (frameELast h4 v) / c) * β ^ 2) := by ring
    _ = c := by rw [hβγ, mul_one]

private theorem nu_not_square {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : H = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H})
    (hQlast : Q (frameELast h4 v) ≠ 0)
    (hτnot : reflect Q (frameELast h4 v) ∉ H) :
    ¬ IsSquare (Q (frameELast h4 v) / c) := by
  intro ⟨s, hs⟩
  have hs0 : s ≠ 0 := by
    intro h0
    apply hQlast
    have hzero : Q (frameELast h4 v) / c = 0 := by rw [hs, h0, mul_zero]
    exact (div_eq_zero_iff.mp hzero).resolve_right hc
  have hQe : Q (frameELast h4 v) = s * s * c := by
    have h := hs
    rw [div_eq_iff hc] at h
    exact h
  have hQsmul : Q (s⁻¹ • frameELast h4 v) = c := by
    rw [QuadraticMap.map_smul, smul_eq_mul, hQe]
    field_simp [hs0]
  have hτeq : reflect Q (s⁻¹ • frameELast h4 v) = reflect Q (frameELast h4 v) :=
    CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (Q := Q) (inv_ne_zero hs0)
      (frameELast h4 v)
  apply hτnot
  rw [← hτeq]
  exact reflect_mem_of_isOrthOn_class hp hQ hc hclass
    (Submodule.smul_mem _ _ (v (frameLast h4)).2) hQsmul

private theorem quadratic_frameD_three (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0)
    (hQeLast : Q (frameELast h4 v) = -c) :
    Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v) = c := by
  have hne : frameZero h4 ≠ frameOne h4 := by
    intro h
    have := congrArg Fin.val h
    simp [frameZero, frameOne] at this
  have hQ01 : Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) = c + c := by
    rw [show Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) =
        Q (frameE h4 v (frameZero h4)) + Q (frameE h4 v (frameOne h4)) +
          polar Q (frameE h4 v (frameZero h4)) (frameE h4 v (frameOne h4))
        from QuadraticMap.map_add Q _ _]
    rw [hQnorm (frameZero h4), hQnorm (frameOne h4), hvorth _ _ hne]
    ring
  have hpolar : polar Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4))
      (frameELast h4 v) = 0 := by
    rw [polar_add_left,
      QuadraticMap.polar_comm Q (frameE h4 v (frameZero h4)) (frameELast h4 v),
      QuadraticMap.polar_comm Q (frameE h4 v (frameOne h4)) (frameELast h4 v),
      hvorthLast (frameZero h4), hvorthLast (frameOne h4), add_zero]
  rw [show Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v) =
      Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) + Q (frameELast h4 v) +
        polar Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) (frameELast h4 v)
      from QuadraticMap.map_add Q _ _]
  rw [hQ01, hQeLast, hpolar]
  ring

private theorem last_norm_eq_neg_of_three (hp3 : p = 3) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (hc : c ≠ 0)
    (hQlast : Q (frameELast h4 v) ≠ 0)
    (hνsq : ¬ IsSquare (Q (frameELast h4 v) / c)) :
    Q (frameELast h4 v) = -c := by
  subst p
  have hνne : Q (frameELast h4 v) / c ≠ 0 := div_ne_zero hQlast hc
  have hcases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 := by
    intro x
    fin_cases x
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  have hν : Q (frameELast h4 v) / c = -1 := by
    rcases hcases (Q (frameELast h4 v) / c) with h0 | h1 | hm1
    · exact absurd h0 hνne
    · exfalso
      apply hνsq
      rw [h1]
      exact ⟨1, by ring⟩
    · exact hm1
  have h := congrArg (fun x : ZMod 3 => x * c) hν
  field_simp [hc] at h
  exact h

private theorem isCaseDPair_of_w_data {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : IsClassType (p := p) Q H c)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    {w b : U} (hQw : Q w = c) (hb : Q b = c)
    (hwV : w ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hbW : b ∈ frameW h4 v) (hwW : w ∉ frameW h4 v)
    (hwb : polar Q w b = 0) (hzwne : frameZ h4 v Q w ≠ w) :
    IsCaseDPair p H (frameZ h4 v Q) (reflect Q w) (reflect Q b) := by
  have hτH : reflect Q w ∈ H :=
    reflect_mem_of_isOrthOn_class hp hQ hc hclass hwV hQw
  have hh'H : reflect Q b ∈ H :=
    reflect_mem_of_isOrthOn_class hp hQ hc hclass hbV hb
  have hτrefl : IsRefl p (reflect Q w) := isRefl_reflect hp (by rw [hQw]; exact hc)
  have hh'refl : IsRefl p (reflect Q b) := isRefl_reflect hp (by rw [hb]; exact hc)
  have hcomm : reflect Q w * reflect Q b = reflect Q b * reflect Q w :=
    commute_reflect_reflect hwb
  have hVh' : HardMathSupport.Kantor79.movedSpace (reflect Q b) ≤
      HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q) := by
    rw [movedSpace_reflect_eq_span hp (by rw [hb]; exact hc),
      movedSpace_frameZ_eq_frameW hp h4 v c hc hQnorm hvorth]
    exact Submodule.span_le.mpr (by rintro _ rfl; exact hbW)
  have hVτ_not_W : ¬ HardMathSupport.Kantor79.movedSpace (reflect Q w) ≤
      HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q) := by
    intro hle
    apply hwW
    rw [movedSpace_frameZ_eq_frameW hp h4 v c hc hQnorm hvorth] at hle
    rw [movedSpace_reflect_eq_span hp (by rw [hQw]; exact hc)] at hle
    exact hle (Submodule.subset_span (Set.mem_singleton w))
  have hVτ_not_ker : ¬ HardMathSupport.Kantor79.movedSpace (reflect Q w) ≤
      LinearMap.ker ((frameZ h4 v Q : U →ₗ[ZMod p] U) - 1) := by
    intro hle
    apply hzwne
    rw [movedSpace_reflect_eq_span hp (by rw [hQw]; exact hc)] at hle
    have hmem := hle (Submodule.subset_span (Set.mem_singleton w))
    simpa [LinearMap.mem_ker, sub_eq_zero] using hmem
  exact ⟨hτH, hh'H, hτrefl, hh'refl, hcomm, hVh', hVτ_not_W, hVτ_not_ker⟩

private theorem caseD_ne_three_w_not_mem (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {β γ : ZMod p} (hβ : β ≠ 0) :
    β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4) ∉ frameW h4 v := by
  intro hw
  have hγW : γ • frameE h4 v (framePenultimate h4) ∈ frameW h4 v :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨framePenultimate h4, rfl⟩)
  have hβW : β • frameELast h4 v ∈ frameW h4 v := by
    have hsub : β • frameELast h4 v =
        (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) -
          γ • frameE h4 v (framePenultimate h4) := by abel
    rw [hsub]
    exact Submodule.sub_mem _ hw hγW
  have heLastW : frameELast h4 v ∈ frameW h4 v := by
    have := Submodule.smul_mem (frameW h4 v) β⁻¹ hβW
    rwa [smul_smul, inv_mul_cancel₀ hβ, one_smul] at this
  exact frameELast_not_mem_frameW h4 v heLastW

private theorem caseD_ne_three_polar_h0 (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U}
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0) (β γ : ZMod p) :
    polar Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4))
      (frameE h4 v (frameZero h4)) = 0 := by
  have hwe' : polar Q (frameE h4 v (framePenultimate h4)) (frameE h4 v (frameZero h4)) = 0 := by
    apply hvorth
    intro h
    have := congrArg Fin.val h
    simp [framePenultimate, frameZero] at this
    omega
  rw [polar_add_left, polar_smul_left, polar_smul_left, hvorthLast (frameZero h4), hwe']
  simp

private theorem caseD_ne_three_zw_ne (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (hc : c ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0)
    {β γ : ZMod p} (hγ : γ ≠ 0) :
    frameZ h4 v Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) ≠
      β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4) := by
  have hzeLast : frameZ h4 v Q (frameELast h4 v) = frameELast h4 v :=
    frameZ_apply_of_mem_orthogonal h4 v
      (frameELast_mem_orthogonal_frameW h4 v hvorthLast)
  have hze' : frameZ h4 v Q (frameE h4 v (framePenultimate h4)) =
      -frameE h4 v (framePenultimate h4) :=
    frameZ_apply_frameE h4 v c hc hQnorm hvorth (framePenultimate h4)
  have hzw : frameZ h4 v Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) =
      β • frameELast h4 v - γ • frameE h4 v (framePenultimate h4) := by
    rw [map_add, map_smul, map_smul, hzeLast, hze', smul_neg, sub_eq_add_neg]
  have he'ne : frameE h4 v (framePenultimate h4) ≠ 0 := by
    intro h0
    have := hQnorm (framePenultimate h4)
    rw [h0, map_zero] at this
    exact hc this.symm
  intro h
  have hdiff : frameZ h4 v Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) -
      (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) =
      (-(2 * γ)) • frameE h4 v (framePenultimate h4) := by
    rw [hzw]
    module
  have hzero : (-(2 * γ)) • frameE h4 v (framePenultimate h4) = 0 := by
    rw [← hdiff, sub_eq_zero.mpr h]
  have h2γ : (2 : ZMod p) * γ = 0 := by
    rcases smul_eq_zero.mp hzero with hneg | he
    · exact neg_eq_zero.mp hneg
    · exact absurd he he'ne
  exact hγ ((mul_eq_zero.mp h2γ).resolve_left (ZMod.prime_ne_zero p 2 hp))

private theorem isCaseDPair_of_not_mem_of_p_ne_three {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (hp3 : p ≠ 3)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : H = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H})
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0)
    (hQlast : Q (frameELast h4 v) ≠ 0)
    (hτnot : reflect Q (frameELast h4 v) ∉ H) :
    ∃ τ h' : U ≃ₗ[ZMod p] U, IsCaseDPair p H (frameZ h4 v Q) τ h' := by
  have hνsq : ¬ IsSquare (Q (frameELast h4 v) / c) :=
    nu_not_square hp h4 v hQ hc hclass hQlast hτnot
  obtain ⟨β, γ, hβ, hγ, hβγ⟩ := exists_beta_gamma hp hp3 hνsq
  have hQw : Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)) = c :=
    quadratic_frameD_ne_three h4 v hc hQnorm hvorthLast hβγ
  have hwV : β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4) ∈
      HardMathSupport.Kantor79.commutatorSpace H :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (v (frameLast h4)).2)
      (Submodule.smul_mem _ _ (v (frameIdx h4 (framePenultimate h4))).2)
  have hwW := caseD_ne_three_w_not_mem (γ := γ) h4 v hβ
  have hwb := caseD_ne_three_polar_h0 h4 v hvorth hvorthLast β γ
  have hzwne := caseD_ne_three_zw_ne hp h4 v hc hQnorm hvorth hvorthLast
    (β := β) (γ := γ) hγ
  refine ⟨reflect Q (β • frameELast h4 v + γ • frameE h4 v (framePenultimate h4)),
    reflect Q (frameE h4 v (frameZero h4)), ?_⟩
  exact isCaseDPair_of_w_data hp h4 v hQ hc hclass hQnorm hvorth hQw
    (hQnorm (frameZero h4))
    hwV (v (frameIdx h4 (frameZero h4))).2
    (Submodule.subset_span ⟨frameZero h4, rfl⟩) hwW hwb hzwne

private theorem caseD_three_w_not_mem (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H)) :
    frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v ∉
      frameW h4 v := by
  intro hw
  have h01W : frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) ∈ frameW h4 v :=
    Submodule.add_mem _ (Submodule.subset_span ⟨frameZero h4, rfl⟩)
      (Submodule.subset_span ⟨frameOne h4, rfl⟩)
  have heLastW : frameELast h4 v ∈ frameW h4 v := by
    have hsub : frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v -
        (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) = frameELast h4 v := by
      abel
    rw [← hsub]
    exact Submodule.sub_mem _ hw h01W
  exact frameELast_not_mem_frameW h4 v heLastW

private theorem caseD_three_polar_h2 (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (h5 : 5 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U}
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0) :
    polar Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v)
      (frameE h4 v (frameTwo h5)) = 0 := by
  have h02 : polar Q (frameE h4 v (frameZero h4)) (frameE h4 v (frameTwo h5)) = 0 := by
    apply hvorth
    intro h
    have := congrArg Fin.val h
    simp [frameZero, frameTwo] at this
  have h12 : polar Q (frameE h4 v (frameOne h4)) (frameE h4 v (frameTwo h5)) = 0 := by
    apply hvorth
    intro h
    have := congrArg Fin.val h
    simp [frameOne, frameTwo] at this
  have hl2 : polar Q (frameELast h4 v) (frameE h4 v (frameTwo h5)) = 0 := hvorthLast _
  rw [polar_add_left, polar_add_left, h02, h12, hl2, add_zero, add_zero]

private theorem caseD_three_sum_ne (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (hc : c ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) :
    frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) ≠ 0 := by
  have hQsum : Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) = c + c := by
    rw [show Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) =
        Q (frameE h4 v (frameZero h4)) + Q (frameE h4 v (frameOne h4)) +
          polar Q (frameE h4 v (frameZero h4)) (frameE h4 v (frameOne h4))
        from QuadraticMap.map_add Q _ _]
    rw [hQnorm (frameZero h4), hQnorm (frameOne h4),
      hvorth _ _ (by
        intro h
        have := congrArg Fin.val h
        simp [frameZero, frameOne] at this)]
    ring
  intro h0
  have hzero : c + c = 0 := by
    have := hQsum
    rw [h0, map_zero] at this
    exact this.symm
  have h2c : (2 : ZMod p) * c = 0 := by
    rw [two_mul]
    exact hzero
  exact (mul_ne_zero (ZMod.prime_ne_zero p 2 hp) hc) h2c

private theorem caseD_three_zw_ne (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (hc : c ≠ 0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0) :
    frameZ h4 v Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v) ≠
      frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v := by
  have hzeLast : frameZ h4 v Q (frameELast h4 v) = frameELast h4 v :=
    frameZ_apply_of_mem_orthogonal h4 v
      (frameELast_mem_orthogonal_frameW h4 v hvorthLast)
  have hze0 : frameZ h4 v Q (frameE h4 v (frameZero h4)) = -frameE h4 v (frameZero h4) :=
    frameZ_apply_frameE h4 v c hc hQnorm hvorth (frameZero h4)
  have hze1 : frameZ h4 v Q (frameE h4 v (frameOne h4)) = -frameE h4 v (frameOne h4) :=
    frameZ_apply_frameE h4 v c hc hQnorm hvorth (frameOne h4)
  have hzw : frameZ h4 v Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) +
      frameELast h4 v) =
      -frameE h4 v (frameZero h4) - frameE h4 v (frameOne h4) + frameELast h4 v := by
    rw [map_add, map_add, hze0, hze1, hzeLast]
    abel
  have hsumne := caseD_three_sum_ne hp h4 v hc hQnorm hvorth
  intro h
  have hdiff : frameZ h4 v Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) +
      frameELast h4 v) -
      (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v) =
      (-(2 : ZMod p)) • (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) := by
    rw [hzw]
    module
  have hzero : (-(2 : ZMod p)) • (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4)) = 0 := by
    rw [← hdiff, sub_eq_zero.mpr h]
  exact (smul_ne_zero (neg_ne_zero.mpr (ZMod.prime_ne_zero p 2 hp)) hsumne) hzero

private theorem isCaseDPair_of_not_mem_of_p_eq_three {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (hp3 : p = 3) (h5 : 5 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : H = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H})
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0)
    (hQlast : Q (frameELast h4 v) ≠ 0)
    (hτnot : reflect Q (frameELast h4 v) ∉ H) :
    ∃ τ h' : U ≃ₗ[ZMod p] U, IsCaseDPair p H (frameZ h4 v Q) τ h' := by
  have hνsq : ¬ IsSquare (Q (frameELast h4 v) / c) :=
    nu_not_square hp h4 v hQ hc hclass hQlast hτnot
  have hQeLast : Q (frameELast h4 v) = -c :=
    last_norm_eq_neg_of_three hp3 h4 v hc hQlast hνsq
  have hQw : Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) +
      frameELast h4 v) = c :=
    quadratic_frameD_three h4 v hQnorm hvorth hvorthLast hQeLast
  have hwV : frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) + frameELast h4 v ∈
      HardMathSupport.Kantor79.commutatorSpace H :=
    Submodule.add_mem _ (Submodule.add_mem _
      (v (frameIdx h4 (frameZero h4))).2 (v (frameIdx h4 (frameOne h4))).2)
      (v (frameLast h4)).2
  have hwW := caseD_three_w_not_mem h4 v
  have hwb := caseD_three_polar_h2 h4 h5 v hvorth hvorthLast
  have hzwne := caseD_three_zw_ne hp h4 v hc hQnorm hvorth hvorthLast
  refine ⟨reflect Q (frameE h4 v (frameZero h4) + frameE h4 v (frameOne h4) +
      frameELast h4 v), reflect Q (frameE h4 v (frameTwo h5)), ?_⟩
  exact isCaseDPair_of_w_data hp h4 v hQ hc hclass hQnorm hvorth hQw
    (hQnorm (frameTwo h5))
    hwV (v (frameIdx h4 (frameTwo h5))).2
    (Submodule.subset_span ⟨frameTwo h5, rfl⟩) hwW hwb hzwne

private theorem exists_h_fix_full {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hfull : H = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H})
    (c0 : ZMod p)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hWnd : PolarNondegOn Q (frameW h4 v))
    (hfinW : Module.finrank (ZMod p) (frameW h4 v) = Module.finrank (ZMod p) U - 2)
    {x : U ≃ₗ[ZMod p] U} (hxH : x ∈ H) (hxr : IsRefl p x)
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ frameW h4 v) :
    ∃ h ∈ H, IsRefl p h ∧ HardMathSupport.Kantor79.movedSpace h ≤
      frameW h4 v ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  obtain ⟨a, haV, haQ, hxeq⟩ :=
    exists_root_mem_of_isOrthOn hp hQ (Or.inl hfull) hxH hxr
  have haVx : a ∈ HardMathSupport.Kantor79.movedSpace x := by
    rw [hxeq, movedSpace_reflect_eq_span hp haQ]
    exact Submodule.subset_span (Set.mem_singleton a)
  have haW : a ∈ frameW h4 v := hxV haVx
  have hb_exists : ∃ b ∈ frameW h4 v, Q b ≠ 0 ∧ polar Q a b = 0 := by
    by_cases h5 : 5 ≤ Module.finrank (ZMod p) U
    · obtain ⟨b, hbW, hQb, hpol⟩ := exists_b_of_inf_ker hp hWnd hfinW haW haQ 1 h5
      exact ⟨b, hbW, by rw [hQb]; exact one_ne_zero, hpol⟩
    · have h4eq : Module.finrank (ZMod p) U = 4 := by omega
      obtain ⟨b, hbW, hQb, hpol⟩ :=
        exists_b_frame_dim_four h4 v c0 hQnorm hvorth h4eq haW
      exact ⟨b, hbW, by rw [hQb]; exact haQ, hpol⟩
  obtain ⟨b, hbW, hbQ, hpol⟩ := hb_exists
  refine ⟨reflect Q b, ?_, ?_, ?_⟩
  · exact reflect_mem_of_isOrthOn_full hp hQ hfull
      (frameW_le_commutatorSpace h4 v hbW) hbQ
  · exact isRefl_reflect hp hbQ
  · refine le_inf ?_ ?_
    · rw [movedSpace_reflect_eq_span hp hbQ]
      exact Submodule.span_le.mpr (by rintro _ rfl; exact hbW)
    · rw [movedSpace_reflect_eq_span hp hbQ]
      apply Submodule.span_le.mpr
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hxb : x y = y := by rw [hxeq, reflect_apply_of_polar_eq_zero hpol]
      exact LinearMap.mem_ker.mpr (by simp [hxb])

private theorem exists_h_fix_class {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : H = Subgroup.closure {t | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤
        HardMathSupport.Kantor79.commutatorSpace H})
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hWnd : PolarNondegOn Q (frameW h4 v))
    (hfinW : Module.finrank (ZMod p) (frameW h4 v) = Module.finrank (ZMod p) U - 2)
    {x : U ≃ₗ[ZMod p] U} (hxH : x ∈ H) (hxr : IsRefl p x)
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ frameW h4 v) :
    ∃ h ∈ H, IsRefl p h ∧ HardMathSupport.Kantor79.movedSpace h ≤
      frameW h4 v ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  have hxClass := mem_classRefl_of_mem_classType hp hQ hc hclass hxH hxr
  obtain ⟨a, hQa, hxeq⟩ := (mem_classRefl_iff hp hQ hc x).mp hxClass
  have haQ : Q a ≠ 0 := by rw [hQa]; exact hc
  have haVx : a ∈ HardMathSupport.Kantor79.movedSpace x := by
    rw [hxeq, movedSpace_reflect_eq_span hp haQ]
    exact Submodule.subset_span (Set.mem_singleton a)
  have haW : a ∈ frameW h4 v := hxV haVx
  have hb_exists : ∃ b ∈ frameW h4 v, Q b = c ∧ polar Q a b = 0 := by
    by_cases h5 : 5 ≤ Module.finrank (ZMod p) U
    · obtain ⟨b, hbW, hQb, hpol⟩ := exists_b_of_inf_ker hp hWnd hfinW haW haQ c h5
      exact ⟨b, hbW, hQb, hpol⟩
    · have h4eq : Module.finrank (ZMod p) U = 4 := by omega
      obtain ⟨b, hbW, hQb, hpol⟩ :=
        exists_b_frame_dim_four h4 v c hQnorm hvorth h4eq haW
      exact ⟨b, hbW, by rw [hQb, hQa], hpol⟩
  obtain ⟨b, hbW, hbQ, hpol⟩ := hb_exists
  refine ⟨reflect Q b, ?_, ?_, ?_⟩
  · exact reflect_mem_of_isOrthOn_class hp hQ hc hclass
      (frameW_le_commutatorSpace h4 v hbW) hbQ
  · exact isRefl_reflect hp (by rw [hbQ]; exact hc)
  · refine le_inf ?_ ?_
    · rw [movedSpace_reflect_eq_span hp (by rw [hbQ]; exact hc)]
      exact Submodule.span_le.mpr (by rintro _ rfl; exact hbW)
    · rw [movedSpace_reflect_eq_span hp (by rw [hbQ]; exact hc)]
      apply Submodule.span_le.mpr
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hxb : x y = y := by rw [hxeq, reflect_apply_of_polar_eq_zero hpol]
      exact LinearMap.mem_ker.mpr (by simp [hxb])

private theorem exists_h_fix_of_basis {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c0 : ZMod p} (hc0 : c0 ≠ 0)
    (hcase : IsFullType (p := p) Q H ∨ IsClassType (p := p) Q H c0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hWnd : PolarNondegOn Q (frameW h4 v))
    (hfinW : Module.finrank (ZMod p) (frameW h4 v) = Module.finrank (ZMod p) U - 2) :
    ∀ x ∈ H, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q) →
      ∃ h ∈ H, IsRefl p h ∧ HardMathSupport.Kantor79.movedSpace h ≤
        HardMathSupport.Kantor79.movedSpace (frameZ h4 v Q) ⊓
          LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  intro x hxH hxr hxV
  rw [movedSpace_frameZ_eq_frameW hp h4 v c0 hc0 hQnorm hvorth] at hxV
  rcases hcase with hfull | hclass
  · obtain ⟨h, hhH, hhrefl, hle⟩ :=
      exists_h_fix_full hp h4 v hQ hfull c0 hQnorm hvorth hWnd hfinW hxH hxr hxV
    refine ⟨h, hhH, hhrefl, ?_⟩
    rw [movedSpace_frameZ_eq_frameW hp h4 v c0 hc0 hQnorm hvorth]
    exact hle
  · obtain ⟨h, hhH, hhrefl, hle⟩ :=
      exists_h_fix_class hp h4 v hQ hc0 hclass hQnorm hvorth hWnd hfinW hxH hxr hxV
    refine ⟨h, hhH, hhrefl, ?_⟩
    rw [movedSpace_frameZ_eq_frameW hp h4 v c0 hc0 hQnorm hvorth]
    exact hle

private theorem lemmaTwoThreeFrame_of_basis {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hp : p ≠ 2) [Module.Finite (ZMod p) U] (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (hHG : H ≤ G) (hG : QTwoLin.TransvectionFree G) (hH : ReflGen p H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H)
    (hirr : ∀ b ∈ G, IsRefl p b →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H →
      IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c0 : ZMod p} (hc0 : c0 ≠ 0)
    (hcase : IsFullType (p := p) Q H ∨ IsClassType (p := p) Q H c0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hgen0 : ∀ i : Fin (Module.finrank (ZMod p) U - 2), reflect Q (frameE h4 v i) ∈ H) :
    LemmaTwoThreeFrame p G H (frameZ h4 v Q) Set.univ := by
  have hWnd := frameW_polarNondegOn hp h4 v c0 hc0 hQnorm hvorth
  have hfinW := finrank_frameW hp h4 v c0 hc0 hQnorm hvorth
  refine
    { le := hHG
      transvectionFree := hG
      reflGen := hH
      splitSupport := hs
      four_le := h4
      mem_of_le := hmem
      irred := hirr
      z_mem := frame_mem h4 v hgen0
      z_mul_self := frameZ_mul_self hp h4 v c0 hc0 hQnorm hvorth
      finrank_movedSpace_z := finrank_movedSpace_frameZ hp h4 v c0 hc0 hQnorm hvorth
      conj_mem := by intro g hg s hs; trivial
      exists_h := exists_h_frame hp h4 v hQ c0 hc0 hQnorm hvorth hgen0
      exists_h_fix := by
        intro x hxH hxr hxV
        obtain ⟨h, hhH, hhrefl, hle⟩ :=
          exists_h_fix_of_basis hp h4 v hQ hc0 hcase hQnorm hvorth hWnd hfinW
            x hxH hxr hxV
        exact ⟨h, Set.mem_univ h, hhH, hhrefl, hle⟩ }

private theorem caseC_or_D_of_basis {H : Subgroup (U ≃ₗ[ZMod p] U)}
    [Module.Finite (ZMod p) U] (hp : p ≠ 2) (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c0 : ZMod p} (hc0 : c0 ≠ 0)
    (hcase : IsFullType (p := p) Q H ∨ IsClassType (p := p) Q H c0)
    (hQnorm : ∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0)
    (hvorth : ∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0)
    (hvorthLast : ∀ i : Fin (Module.finrank (ZMod p) U - 2),
      polar Q (frameELast h4 v) (frameE h4 v i) = 0)
    (hQlast : Q (frameELast h4 v) ≠ 0) :
    (∃ τ, IsCaseCRefl p H (frameZ h4 v Q) τ) ∨
      ∃ τ h', IsCaseDPair p H (frameZ h4 v Q) τ h' := by
  by_cases hτH : reflect Q (frameELast h4 v) ∈ H
  · left
    exact ⟨reflect Q (frameELast h4 v),
      isCaseCRefl_of_mem hp h4 v hQ c0 hc0 hQnorm hvorth hvorthLast hQlast hτH⟩
  · rcases hcase with hfull | hclass
    · exfalso
      exact hτH (reflect_mem_of_isOrthOn_full hp hQ hfull
        (v (frameLast h4)).2 hQlast)
    · right
      by_cases hp3 : p = 3
      · exact isCaseDPair_of_not_mem_of_p_eq_three hp h4 hp3 (h43 hp3) v hQ hc0
          hclass hQnorm hvorth hvorthLast hQlast hτH
      · exact isCaseDPair_of_not_mem_of_p_ne_three hp h4 hp3 v hQ hc0
          hclass hQnorm hvorth hvorthLast hQlast hτH

private theorem exists_basis_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {Q : QuadraticForm (ZMod p) U}
    (hQH : PolarNondegOn Q (HardMathSupport.Kantor79.commutatorSpace H))
    (c0 : ZMod p) (hc0 : c0 ≠ 0) :
    ∃ v : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
        (HardMathSupport.Kantor79.commutatorSpace H),
      (∀ i j, i ≠ j → polar Q (frameE h4 v i) (frameE h4 v j) = 0) ∧
      (∀ i : Fin (Module.finrank (ZMod p) U - 2),
        polar Q (frameELast h4 v) (frameE h4 v i) = 0) ∧
      (∀ i : Fin (Module.finrank (ZMod p) U - 2), Q (frameE h4 v i) = c0) ∧
      Q (frameELast h4 v) ≠ 0 := by
  have hn1 : 2 ≤ Module.finrank (ZMod p) U - 1 := by omega
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
      Module.finrank (ZMod p) U - 1 := hs.2.1
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨v, hvorth, hva, hvlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod p)
      (V := HardMathSupport.Kantor79.commutatorSpace H) hodd (d := Module.finrank (ZMod p) U - 1)
      hfin hn1 (Q.restrict (HardMathSupport.Kantor79.commutatorSpace H))
      (nondegenerate_polarBilin_restrict hQH) hc0
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h := hvorth (frameIdx h4 i) (frameIdx h4 j) (fun h => hij (frameIdx_injective h4 h))
    simpa [frameE, polar_restrict] using h
  · intro i
    have h := hvorth (frameLast h4) (frameIdx h4 i)
      (fun h => frameIdx_ne_last h4 i h.symm)
    simpa [frameELast, frameE, polar_restrict] using h
  · intro i
    have hi : (frameIdx h4 i).val + 1 < Module.finrank (ZMod p) U - 1 := by
      have := (frameIdx h4 i).isLt
      simp [frameIdx] at this ⊢
      omega
    have h := hva (frameIdx h4 i) hi
    simpa [frameE, restrict_apply'] using h
  · have h := hvlast
    have hidx : (⟨Module.finrank (ZMod p) U - 1 - 1, by omega⟩ :
        Fin (Module.finrank (ZMod p) U - 1)) = frameLast h4 := by
      apply Fin.ext
      simp [frameLast]
      omega
    rw [hidx] at h
    simpa [frameELast, restrict_apply'] using h

private theorem exists_frame_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hHG : H ≤ G) (hG : QTwoLin.TransvectionFree G)
    (hH : ReflGen p H) (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H)
    (hirr : ∀ b ∈ G, IsRefl p b →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H →
      IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hX : IsOrthOn p Q H) :
    ∃ z, LemmaTwoThreeFrame p G H z Set.univ ∧
      ((∃ τ, IsCaseCRefl p H z τ) ∨ ∃ τ h', IsCaseDPair p H z τ h') := by
  have hiso : ∀ g ∈ H, IsIsom p Q g := fun g hg => IsOrthOn.isIsom (X := H) (Q := Q) hX hg
  have horthVH : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
      ∀ u ∈ centralizerSpace H, polar Q w u = 0 := by
    intro w hw u hu
    exact polar_eq_zero_of_mem_centralizerSpace_of_mem_commutatorSpace hiso hu hw
  have hQH : PolarNondegOn Q (HardMathSupport.Kantor79.commutatorSpace H) :=
    polarNondegOn_of_isCompl_of_orthogonal hQ hs.1 horthVH
  rcases hX with hfull | ⟨c, hc, hclass⟩
  · obtain ⟨v, hvorth, hvorthLast, hQnorm, hQlast⟩ :=
      exists_basis_of_isOrthOn hp h4 hs hQH 1 one_ne_zero
    have hcase : IsFullType (p := p) Q H ∨ IsClassType (p := p) Q H 1 := Or.inl hfull
    have hgen : ∀ i : Fin (Module.finrank (ZMod p) U - 2), reflect Q (frameE h4 v i) ∈ H := by
      intro i
      exact reflect_mem_of_isOrthOn_full hp hQ hfull (v (frameIdx h4 i)).2
        (by rw [hQnorm i]; exact one_ne_zero)
    refine ⟨frameZ h4 v Q,
      lemmaTwoThreeFrame_of_basis hp h4 hHG hG hH hs hmem hirr v hQ one_ne_zero
        hcase hQnorm hvorth hgen, ?_⟩
    exact caseC_or_D_of_basis hp h4 h43 v hQ one_ne_zero hcase hQnorm hvorth hvorthLast hQlast
  · obtain ⟨v, hvorth, hvorthLast, hQnorm, hQlast⟩ :=
      exists_basis_of_isOrthOn hp h4 hs hQH c hc
    have hcase : IsFullType (p := p) Q H ∨ IsClassType (p := p) Q H c := Or.inr hclass
    have hgen : ∀ i : Fin (Module.finrank (ZMod p) U - 2), reflect Q (frameE h4 v i) ∈ H := by
      intro i
      exact reflect_mem_of_isOrthOn_class hp hQ hc hclass (v (frameIdx h4 i)).2 (hQnorm i)
    refine ⟨frameZ h4 v Q,
      lemmaTwoThreeFrame_of_basis hp h4 hHG hG hH hs hmem hirr v hQ hc
        hcase hQnorm hvorth hgen, ?_⟩
    exact caseC_or_D_of_basis hp h4 h43 v hQ hc hcase hQnorm hvorth hvorthLast hQlast

theorem exists_lemmaTwoThreeFrame_of_isOrthType (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hHG : H ≤ G) (hG : QTwoLin.TransvectionFree G)
    (hH : ReflGen p H) (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (horth : IsOrthType p (movedGroup H))
    (hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H)
    (hirr : ∀ b ∈ G, IsRefl p b →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H →
      ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H →
      IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤) :
    ∃ z, LemmaTwoThreeFrame p G H z Set.univ ∧
      ((∃ τ, IsCaseCRefl p H z τ) ∨ ∃ τ h', IsCaseDPair p H z τ h') := by
  have hC : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have h := hs.finrank_centralizerSpace
    omega
  obtain ⟨e0, he0, he00⟩ := exists_ne_zero_mem_of_finrank_eq_one hC
  obtain ⟨Q, hQ, hX, -⟩ :=
    exists_isOrthOn_of_isOrthType_movedGroup hp hs horth he0 he00 (c := 1) one_ne_zero
  exact exists_frame_of_isOrthOn hp h4 h43 hHG hG hH hs hmem hirr hQ hX

end CFSG.StandardType.ZS

end
