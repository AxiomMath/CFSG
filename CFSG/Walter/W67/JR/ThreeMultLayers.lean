module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Walter.W67

namespace ThreeMult

open scoped commutatorElement Pointwise

variable {E : Type*} [Group E] (P : Subgroup E)

abbrev γ (i : ℕ) : Subgroup E := P.lowerCentralSeries i

theorem γ_succ (i : ℕ) : γ P (i + 1) = ⁅γ P i, P⁆ := rfl

theorem γ_le (i : ℕ) : γ P i ≤ P := by
  have := Subgroup.lowerCentralSeries_antitone (S := P) (Nat.zero_le i)
  simpa using this

theorem γ_succ_le (i : ℕ) : γ P (i + 1) ≤ γ P i :=
  Subgroup.lowerCentralSeries_antitone (S := P) (Nat.le_succ i)

theorem commutator_mem_γ {i : ℕ} {u y : E} (hu : u ∈ γ P i) (hy : y ∈ P) :
    ⁅u, y⁆ ∈ γ P (i + 1) :=
  Subgroup.commutator_mem_commutator hu hy

theorem conj_mem_γ {i : ℕ} {g c : E} (hg : g ∈ P) (hc : c ∈ γ P i) : g * c * g⁻¹ ∈ γ P i :=
  ((Subgroup.mem_normalizer_iff.mp
    (Subgroup.self_le_normalizer_lowerCentralSeries P i hg)) c).mp hc

theorem conj_mul_inv_mem_γ {i : ℕ} {g c : E} (hg : g ∈ P) (hc : c ∈ γ P (i + 1)) :
    (g * c * g⁻¹) * c⁻¹ ∈ γ P (i + 2) := by
  have h : (g * c * g⁻¹) * c⁻¹ = ⁅c, g⁆⁻¹ := by
    rw [commutatorElement_def]; group
  rw [h]
  exact Subgroup.inv_mem _ (commutator_mem_γ P hc hg)

instance normal_layer (i : ℕ) : ((γ P (i + 1)).subgroupOf (γ P i)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact conj_mem_γ P (γ_le P i g.2) hn

abbrev LayerQ (i : ℕ) : Type _ := ↥(γ P i) ⧸ (γ P (i + 1)).subgroupOf (γ P i)

theorem layer_comm (i : ℕ) (a b : LayerQ P i) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H x =>
  induction b using QuotientGroup.induction_on with
  | H y =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  have h : ((x * y)⁻¹ * (y * x) : ↥(γ P i)) = ⁅(y : E)⁻¹, (x : E)⁻¹⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  rw [show ((((x * y)⁻¹ * (y * x) : ↥(γ P i)) : E)) = ⁅(y : E)⁻¹, (x : E)⁻¹⁆ from h]
  exact commutator_mem_γ P (Subgroup.inv_mem _ y.2) (γ_le P i (Subgroup.inv_mem _ x.2))

noncomputable instance layerCommGroup (i : ℕ) : CommGroup (LayerQ P i) :=
  { (inferInstance : Group (LayerQ P i)) with mul_comm := layer_comm P i }

abbrev lmk {i : ℕ} (x : γ P i) : LayerQ P i := QuotientGroup.mk x

theorem lmk_eq_lmk_iff {i : ℕ} {x y : γ P i} :
    lmk P x = lmk P y ↔ ((x : E)⁻¹ * y) ∈ γ P (i + 1) := by
  rw [lmk, lmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem lmk_eq_one_iff {i : ℕ} {x : γ P i} : lmk P x = 1 ↔ (x : E) ∈ γ P (i + 1) := by
  rw [lmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem lmk_conj {i : ℕ} {g : E} (hg : g ∈ P) (c : γ P (i + 1)) :
    lmk P (⟨g * c * g⁻¹, conj_mem_γ P hg c.2⟩ : γ P (i + 1)) = lmk P c := by
  rw [lmk_eq_lmk_iff]
  have h := conj_mul_inv_mem_γ P hg c.2
  have h2 : (g * (c : E) * g⁻¹)⁻¹ * c = (c : E)⁻¹ * ((g * c * g⁻¹) * (c : E)⁻¹)⁻¹ * c := by
    group
  rw [h2]
  have := conj_mem_γ P (Subgroup.inv_mem _ (γ_le P _ c.2)) (Subgroup.inv_mem _ h)
  rwa [inv_inv] at this

theorem conj_inv_mul_mem_γ {i : ℕ} {g c : E} (hg : g ∈ P) (hc : c ∈ γ P (i + 1)) :
    (g * c * g⁻¹)⁻¹ * c ∈ γ P (i + 2) := by
  have h := conj_mul_inv_mem_γ P hg hc
  have h2 : (g * c * g⁻¹)⁻¹ * c = c⁻¹ * ((g * c * g⁻¹) * c⁻¹)⁻¹ * c := by group
  rw [h2]
  have := conj_mem_γ P (Subgroup.inv_mem _ (γ_le P _ hc)) (Subgroup.inv_mem _ h)
  rwa [inv_inv] at this

theorem subgroupOf_γ_one_le : (γ P 1).subgroupOf (γ P 0) ≤ commutator ↥(γ P 0) := by
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  have hmap : (commutator ↥(γ P 0)).map (γ P 0).subtype = γ P 1 := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, γ_succ]
    rfl
  have hy' : (y : E) ∈ (commutator ↥(γ P 0)).map (γ P 0).subtype := by
    rw [hmap]
    exact hy
  obtain ⟨y', hy', hyy'⟩ := hy'
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

@[expose] noncomputable def pairAux (i : ℕ) (u : γ P i) : ↥(γ P 0) →* LayerQ P (i + 1) where
  toFun y := lmk P (⟨⁅(u : E), (y : E)⁆, commutator_mem_γ P u.2 (γ_le P 0 y.2)⟩ :
    γ P (i + 1))
  map_one' := by
    rw [lmk_eq_one_iff]
    simp only [OneMemClass.coe_one, commutatorElement_one_right]
    exact Subgroup.one_mem _
  map_mul' y y' := by
    rw [← QuotientGroup.mk_mul, lmk_eq_lmk_iff]
    simp only [Subgroup.coe_mul]
    have hc := commutator_mem_γ P u.2 (γ_le P 0 y'.2)
    have h1 : (⁅(u : E), (y : E) * y'⁆)⁻¹ * (⁅(u : E), (y : E)⁆ * ⁅(u : E), (y' : E)⁆) =
        ((y : E) * ⁅(u : E), (y' : E)⁆ * (y : E)⁻¹)⁻¹ * ⁅(u : E), (y' : E)⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact conj_inv_mul_mem_γ P (γ_le P 0 y.2) hc

theorem pairAux_apply (i : ℕ) (u : γ P i) (y : γ P 0) :
    pairAux P i u y = lmk P (⟨⁅(u : E), (y : E)⁆, commutator_mem_γ P u.2 (γ_le P 0 y.2)⟩ :
      γ P (i + 1)) := rfl

theorem pairAux_ker (i : ℕ) (u : γ P i) : (γ P 1).subgroupOf (γ P 0) ≤ (pairAux P i u).ker :=
  (subgroupOf_γ_one_le P).trans (Abelianization.commutator_subset_ker _)

@[expose] noncomputable def pairY (i : ℕ) (u : γ P i) : LayerQ P 0 →* LayerQ P (i + 1) :=
  QuotientGroup.lift ((γ P 1).subgroupOf (γ P 0)) (pairAux P i u) (pairAux_ker P i u)

theorem pairY_lmk (i : ℕ) (u : γ P i) (y : γ P 0) :
    pairY P i u (lmk P y) = lmk P (⟨⁅(u : E), (y : E)⁆, commutator_mem_γ P u.2 (γ_le P 0 y.2)⟩ :
      γ P (i + 1)) := rfl

@[expose] noncomputable def pairU (i : ℕ) : ↥(γ P i) →* (LayerQ P 0 →* LayerQ P (i + 1)) where
  toFun u := pairY P i u
  map_one' := by
    refine MonoidHom.ext fun y => QuotientGroup.induction_on y fun y => ?_
    rw [pairY_lmk, MonoidHom.one_apply, lmk_eq_one_iff]
    simp only [OneMemClass.coe_one, commutatorElement_one_left]
    exact Subgroup.one_mem _
  map_mul' u u' := by
    refine MonoidHom.ext fun y => QuotientGroup.induction_on y fun y => ?_
    rw [MonoidHom.mul_apply]
    change pairY P i (u * u') (lmk P y) = pairY P i u (lmk P y) * pairY P i u' (lmk P y)
    rw [pairY_lmk, pairY_lmk, pairY_lmk]
    have hc := commutator_mem_γ P u'.2 (γ_le P 0 y.2)
    have hd := commutator_mem_γ P u.2 (γ_le P 0 y.2)
    have h1 : (⟨⁅((u * u' : γ P i) : E), (y : E)⁆,
        commutator_mem_γ P (u * u').2 (γ_le P 0 y.2)⟩ :
        γ P (i + 1)) = ⟨(u : E) * ⁅(u' : E), (y : E)⁆ * (u : E)⁻¹,
          conj_mem_γ P (γ_le P i u.2) hc⟩ * ⟨⁅(u : E), (y : E)⁆, hd⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    rw [h1]
    have hmul : lmk P ((⟨(u : E) * ⁅(u' : E), (y : E)⁆ * (u : E)⁻¹,
        conj_mem_γ P (γ_le P i u.2) hc⟩ : γ P (i + 1)) * ⟨⁅(u : E), (y : E)⁆, hd⟩) =
        lmk P (⟨(u : E) * ⁅(u' : E), (y : E)⁆ * (u : E)⁻¹,
          conj_mem_γ P (γ_le P i u.2) hc⟩ : γ P (i + 1)) *
        lmk P (⟨⁅(u : E), (y : E)⁆, hd⟩ : γ P (i + 1)) := rfl
    rw [hmul, lmk_conj P (γ_le P i u.2) ⟨_, hc⟩, mul_comm]

theorem pairU_ker (i : ℕ) : (γ P (i + 1)).subgroupOf (γ P i) ≤ (pairU P i).ker := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  rw [MonoidHom.mem_ker]
  refine MonoidHom.ext fun y => QuotientGroup.induction_on y fun y => ?_
  change pairY P i g (lmk P y) = 1
  rw [pairY_lmk, lmk_eq_one_iff]
  exact commutator_mem_γ P hg (γ_le P 0 y.2)

@[expose] noncomputable def pair (i : ℕ) : LayerQ P i →* (LayerQ P 0 →* LayerQ P (i + 1)) :=
  QuotientGroup.lift _ (pairU P i) (pairU_ker P i)

theorem pair_lmk (i : ℕ) (u : γ P i) (y : γ P 0) :
    pair P i (lmk P u) (lmk P y) = lmk P (⟨⁅(u : E), (y : E)⁆,
      commutator_mem_γ P u.2 (γ_le P 0 y.2)⟩ : γ P (i + 1)) := rfl

theorem closure_range_pair (i : ℕ) :
    Subgroup.closure (Set.range fun uy : LayerQ P i × LayerQ P 0 => pair P i uy.1 uy.2) = ⊤ := by
  rw [eq_top_iff]
  intro m hm
  clear hm
  induction m using QuotientGroup.induction_on with
  | H x =>
  obtain ⟨x, hx⟩ := x
  change lmk P (⟨x, hx⟩ : γ P (i + 1)) ∈ _
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact Subgroup.subset_closure ⟨(lmk P (⟨a, ha⟩ : γ P i), lmk P (⟨b, hb⟩ : γ P 0)), rfl⟩
  | one => exact Subgroup.one_mem _
  | mul g h hg hh ihg ihh =>
    have : lmk P (⟨g * h, Subgroup.mul_mem _ hg hh⟩ : γ P (i + 1)) =
        lmk P (⟨g, hg⟩ : γ P (i + 1)) * lmk P (⟨h, hh⟩ : γ P (i + 1)) := rfl
    rw [this]
    exact Subgroup.mul_mem _ ihg ihh
  | inv g hg ihg =>
    have : lmk P (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : γ P (i + 1)) =
        (lmk P (⟨g, hg⟩ : γ P (i + 1)))⁻¹ := rfl
    rw [this]
    exact Subgroup.inv_mem _ ihg

section Conj

variable {P}

theorem map_conj_eq_of_mem_normalizer {g : E} (hg : g ∈ Subgroup.normalizer (P : Set E)) :
    P.map (MulAut.conj g).toMonoidHom = P := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this

theorem conj_mem_γ_of_normalizer {g : E} (hg : g ∈ Subgroup.normalizer (P : Set E)) {i : ℕ}
    {x : E} (hx : x ∈ γ P i) : g * x * g⁻¹ ∈ γ P i := by
  have h := Subgroup.map_lowerCentralSeries (S := P) (MulAut.conj g).toMonoidHom i
  rw [map_conj_eq_of_mem_normalizer hg] at h
  change x ∈ P.lowerCentralSeries i at hx
  change g * x * g⁻¹ ∈ P.lowerCentralSeries i
  rw [← h]
  exact ⟨x, hx, rfl⟩

@[expose] noncomputable def conjγ (g : E) (hg : g ∈ Subgroup.normalizer (P : Set E)) (i : ℕ) :
    ↥(γ P i) →* ↥(γ P i) where
  toFun x := ⟨g * x * g⁻¹, conj_mem_γ_of_normalizer hg x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

@[expose] noncomputable def layerConj (g : E) (hg : g ∈ Subgroup.normalizer (P : Set E))
    (i : ℕ) : LayerQ P i →* LayerQ P i :=
  QuotientGroup.map _ _ (conjγ g hg i) (by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact conj_mem_γ_of_normalizer hg hx)

theorem layerConj_lmk (g : E) (hg : g ∈ Subgroup.normalizer (P : Set E)) {i : ℕ} (x : γ P i) :
    layerConj g hg i (lmk P x) =
      lmk P (⟨g * x * g⁻¹, conj_mem_γ_of_normalizer hg x.2⟩ : γ P i) := rfl

theorem layerConj_pair (g : E) (hg : g ∈ Subgroup.normalizer (P : Set E)) (i : ℕ)
    (u : LayerQ P i) (y : LayerQ P 0) :
    layerConj g hg (i + 1) (pair P i u y) =
      pair P i (layerConj g hg i u) (layerConj g hg 0 y) := by
  induction u using QuotientGroup.induction_on with
  | H u =>
  induction y using QuotientGroup.induction_on with
  | H y =>
  change layerConj g hg (i + 1) (pair P i (lmk P u) (lmk P y)) =
    pair P i (layerConj g hg i (lmk P u)) (layerConj g hg 0 (lmk P y))
  rw [pair_lmk, layerConj_lmk, layerConj_lmk, layerConj_lmk, pair_lmk]
  congr 1
  apply Subtype.ext
  change g * ⁅(u : E), (y : E)⁆ * g⁻¹ = ⁅g * (u : E) * g⁻¹, g * (y : E) * g⁻¹⁆
  simp only [commutatorElement_def]
  group

theorem layerConj_of_mem_center {g : E} (hg : g ∈ Subgroup.normalizer (P : Set E))
    (hgc : g ∈ Subgroup.center E) (i : ℕ) (x : LayerQ P i) : layerConj g hg i x = x := by
  induction x using QuotientGroup.induction_on with
  | H x =>
  change layerConj g hg i (lmk P x) = lmk P x
  rw [layerConj_lmk]
  congr 1
  apply Subtype.ext
  change g * (x : E) * g⁻¹ = x
  rw [← Subgroup.mem_center_iff.mp hgc (x : E), mul_inv_cancel_right]

theorem layerConj_mul {g h : E} (hg : g ∈ Subgroup.normalizer (P : Set E))
    (hh : h ∈ Subgroup.normalizer (P : Set E)) (i : ℕ) (x : LayerQ P i) :
    layerConj (g * h) (Subgroup.mul_mem _ hg hh) i x = layerConj g hg i (layerConj h hh i x) := by
  induction x using QuotientGroup.induction_on with
  | H x =>
  change layerConj (g * h) _ i (lmk P x) = layerConj g hg i (layerConj h hh i (lmk P x))
  rw [layerConj_lmk, layerConj_lmk, layerConj_lmk]
  congr 1
  apply Subtype.ext
  change g * h * (x : E) * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹
  group

theorem layerConj_pow {g : E} (hg : g ∈ Subgroup.normalizer (P : Set E)) (i j : ℕ)
    (x : LayerQ P i) :
    layerConj (g ^ j) (Subgroup.pow_mem _ hg j) i x = (layerConj g hg i)^[j] x := by
  induction j generalizing x with
  | zero =>
    induction x using QuotientGroup.induction_on with
    | H x =>
    change layerConj (g ^ 0) _ i (lmk P x) = lmk P x
    rw [layerConj_lmk]
    congr 1
    apply Subtype.ext
    change g ^ 0 * (x : E) * (g ^ 0)⁻¹ = x
    simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    have key : ∀ (a b : E) (ha : a ∈ Subgroup.normalizer (P : Set E))
        (hb : b ∈ Subgroup.normalizer (P : Set E)), a = b →
        layerConj a ha i x = layerConj b hb i x := by
      intro a b ha hb hab
      subst hab
      rfl
    rw [key _ _ _ (Subgroup.mul_mem _ hg (Subgroup.pow_mem _ hg j)) (pow_succ' g j)]
    exact layerConj_mul (P := P) hg (Subgroup.pow_mem _ hg j) i x

end Conj

end ThreeMult

end CFSG.Walter.W67
