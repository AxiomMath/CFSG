module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open scoped commutatorElement

namespace OrthRestTail

variable {ι K : Type} [Fintype ι] [Field K]

section Supp

variable [DecidableEq ι]

theorem gl_ext {x y : GL ι K} (h : ∀ v, (x : Matrix ι ι K) *ᵥ v = (y : Matrix ι ι K) *ᵥ v) :
    x = y :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]))

theorem mul_mulVec (x y : GL ι K) (v : ι → K) :
    ((x * y : GL ι K) : Matrix ι ι K) *ᵥ v = (x : Matrix ι ι K) *ᵥ ((y : Matrix ι ι K) *ᵥ v) := by
  rw [Units.val_mul, mulVec_mulVec]

theorem inv_mulVec_mulVec (x : GL ι K) (v : ι → K) :
    ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((x : Matrix ι ι K) *ᵥ v) = v := by
  rw [← mul_mulVec, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mulVec_inv_mulVec (x : GL ι K) (v : ι → K) :
    (x : Matrix ι ι K) *ᵥ (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = v := by
  rw [← mul_mulVec, mul_inv_cancel, Units.val_one, one_mulVec]

@[expose] def IsSuppMat (S : Set ι) (g : Matrix ι ι K) : Prop :=
  (∀ v k, k ∉ S → (g *ᵥ v) k = v k) ∧
    ∀ v w, (∀ k ∈ S, v k = w k) → ∀ k ∈ S, (g *ᵥ v) k = (g *ᵥ w) k

omit [DecidableEq ι] in
theorem IsSuppMat.mulVec_comm {S T : Set ι} {g h : Matrix ι ι K} (hg : IsSuppMat S g)
    (hh : IsSuppMat T h) (hST : Disjoint S T) (v : ι → K) : g *ᵥ (h *ᵥ v) = h *ᵥ (g *ᵥ v) := by
  funext k
  by_cases hkS : k ∈ S
  · rw [hh.1 _ k (Set.disjoint_left.mp hST hkS)]
    exact hg.2 _ _ (fun j hj => hh.1 v j (Set.disjoint_left.mp hST hj)) k hkS
  · by_cases hkT : k ∈ T
    · rw [hg.1 _ k hkS]
      exact (hh.2 _ _ (fun j hj => hg.1 v j (Set.disjoint_right.mp hST hj)) k hkT).symm
    · rw [hg.1 _ k hkS, hh.1 _ k hkT, hh.1 _ k hkT, hg.1 _ k hkS]

omit [DecidableEq ι] in
theorem IsSuppMat.mono {S T : Set ι} {g : Matrix ι ι K} (hg : IsSuppMat S g) (hST : S ⊆ T) :
    IsSuppMat T g := by
  refine ⟨fun v k hk => hg.1 v k fun h => hk (hST h), fun v w hvw k hk => ?_⟩
  by_cases hkS : k ∈ S
  · exact hg.2 v w (fun j hj => hvw j (hST hj)) k hkS
  · rw [hg.1 v k hkS, hg.1 w k hkS]
    exact hvw k hk

omit [DecidableEq ι] in
theorem IsSuppMat.mulVec_eq_zero {S : Set ι} {g : Matrix ι ι K} (hg : IsSuppMat S g)
    {v : ι → K} (hv : ∀ k ∉ S, v k = 0) (k : ι) (hk : k ∉ S) : (g *ᵥ v) k = 0 := by
  rw [hg.1 v k hk, hv k hk]

omit [DecidableEq ι] in
theorem IsSuppMat.mulVec_eq_self {S : Set ι} {g : Matrix ι ι K} (hg : IsSuppMat S g)
    {v : ι → K} (hv : ∀ k ∈ S, v k = 0) : g *ᵥ v = v := by
  funext k
  by_cases hk : k ∈ S
  · rw [hg.2 v 0 hv k hk, mulVec_zero, Pi.zero_apply, hv k hk]
  · exact hg.1 v k hk

variable (K) in
@[expose] def suppSub (S : Set ι) : Subgroup (GL ι K) where
  carrier := {g | IsSuppMat S (g : Matrix ι ι K)}
  one_mem' := ⟨fun v k _ => by rw [Units.val_one, one_mulVec],
    fun v w h k hk => by rw [Units.val_one, one_mulVec, one_mulVec]; exact h k hk⟩
  mul_mem' {g h} hg hh := by
    have hg' : IsSuppMat S (g : Matrix ι ι K) := hg
    have hh' : IsSuppMat S (h : Matrix ι ι K) := hh
    refine ⟨fun v k hk => ?_, fun v w hvw k hk => ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hg'.1 _ k hk, hh'.1 v k hk]
    · rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
      exact hg'.2 _ _ (fun j hj => hh'.2 v w hvw j hj) k hk
  inv_mem' {g} hg := by
    classical
    have hg' : IsSuppMat S (g : Matrix ι ι K) := hg
    refine ⟨fun v k hk => ?_, fun v w hvw k hk => ?_⟩
    · have h1 := hg'.1 (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) k hk
      rw [mulVec_inv_mulVec] at h1
      exact h1.symm
    · let x := ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
      let y := ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w
      have hzy : (g : Matrix ι ι K) *ᵥ S.piecewise x y = (g : Matrix ι ι K) *ᵥ y := by
        funext j
        by_cases hj : j ∈ S
        · rw [hg'.2 (S.piecewise x y) x (fun i hi => Set.piecewise_eq_of_mem _ _ _ hi) j hj]
          change ((g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)) j =
            ((g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w)) j
          rw [mulVec_inv_mulVec, mulVec_inv_mulVec]
          exact hvw j hj
        · rw [hg'.1 _ j hj, hg'.1 y j hj]
          exact Set.piecewise_eq_of_notMem _ _ _ hj
      have h2 : S.piecewise x y = y := by
        rw [← inv_mulVec_mulVec g (S.piecewise x y), hzy, inv_mulVec_mulVec]
      have h3 := congrFun h2 k
      rw [Set.piecewise_eq_of_mem _ _ _ hk] at h3
      exact h3

theorem mem_suppSub {S : Set ι} {g : GL ι K} :
    g ∈ suppSub K S ↔ IsSuppMat S (g : Matrix ι ι K) :=
  Iff.rfl

theorem suppSub_mono {S T : Set ι} (hST : S ⊆ T) : suppSub K S ≤ suppSub K T :=
  fun _ hg => IsSuppMat.mono hg hST

theorem commute_of_mem_suppSub {S T : Set ι} (hST : Disjoint S T) {g h : GL ι K}
    (hg : g ∈ suppSub K S) (hh : h ∈ suppSub K T) : g * h = h * g :=
  gl_ext fun v => by
    rw [mul_mulVec, mul_mulVec]
    exact IsSuppMat.mulVec_comm hg hh hST v

theorem inf_suppSub_eq_bot {S T : Set ι} (hST : Disjoint S T) :
    suppSub K S ⊓ suppSub K T = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgS, hgT⟩
  rw [Subgroup.mem_bot]
  refine gl_ext fun v => ?_
  rw [Units.val_one, one_mulVec]
  funext k
  by_cases hk : k ∈ S
  · exact (mem_suppSub.mp hgT).1 v k (Set.disjoint_left.mp hST hk)
  · exact (mem_suppSub.mp hgS).1 v k hk

end Supp

section Join

open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_sup_of_le_normalizer {N H : Subgroup G} (hle : H ≤ Subgroup.normalizer (N : Set G))
    (hdisj : N ⊓ H = ⊥) : Nat.card (N ⊔ H : Subgroup G) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : N × H => (⟨x.1 * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : (N ⊔ H : Subgroup G)))
    ⟨fun x y hxy => ?_, fun z => ?_⟩)
  · exact Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdisj) (congrArg Subtype.val hxy)
  · have hz : (z : G) ∈ (N : Set G) * (H : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N H hle]
      exact z.2
    obtain ⟨a, ha, b, hb, hab⟩ := hz
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem le_normalizer_of_commute {N H : Subgroup G} (h : ∀ x ∈ N, ∀ y ∈ H, x * y = y * x) :
    H ≤ Subgroup.normalizer (N : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h x hx y hy, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h _ hx y hy
    have h2 : y * x = y * (y * x * y⁻¹) := by
      calc y * x = y * x * y⁻¹ * y := by group
        _ = y * (y * x * y⁻¹) := h1
    rw [mul_left_cancel h2]
    exact hx

end Join

variable [DecidableEq ι]

theorem card_sup_of_suppSub {S T : Set ι} (hST : Disjoint S T) {H H' : Subgroup (GL ι K)}
    (hH : H ≤ suppSub K S) (hH' : H' ≤ suppSub K T) :
    Nat.card (H ⊔ H' : Subgroup (GL ι K)) = Nat.card H * Nat.card H' := by
  refine card_sup_of_le_normalizer
    (le_normalizer_of_commute fun x hx y hy => commute_of_mem_suppSub hST (hH hx) (hH' hy)) ?_
  rw [eq_bot_iff]
  intro g hg
  rw [← inf_suppSub_eq_bot (K := K) hST]
  exact ⟨hH hg.1, hH' hg.2⟩

section Pos

variable {J : Type} [Fintype J] [DecidableEq J] (pos : J ↪ ι)

@[expose] noncomputable def posLin (T : Matrix J J K) : (ι → K) →ₗ[K] (ι → K) where
  toFun v := Function.extend pos (T *ᵥ (v ∘ pos)) v
  map_add' v w := by
    funext k
    by_cases hk : ∃ j, pos j = k
    · obtain ⟨j, rfl⟩ := hk
      simp only [Pi.add_apply, pos.injective.extend_apply]
      rw [show (v + w) ∘ pos = v ∘ pos + w ∘ pos from rfl, mulVec_add, Pi.add_apply]
    · simp only [Pi.add_apply, Function.extend_apply' _ _ _ hk]
  map_smul' c v := by
    funext k
    by_cases hk : ∃ j, pos j = k
    · obtain ⟨j, rfl⟩ := hk
      simp only [Pi.smul_apply, RingHom.id_apply, pos.injective.extend_apply]
      rw [show (c • v) ∘ pos = c • (v ∘ pos) from rfl, mulVec_smul, Pi.smul_apply]
    · simp only [Pi.smul_apply, RingHom.id_apply, Function.extend_apply' _ _ _ hk]

omit [Fintype ι] [DecidableEq J] in
theorem posLin_apply_pos (T : Matrix J J K) (v : ι → K) (j : J) :
    posLin pos T v (pos j) = (T *ᵥ (v ∘ pos)) j :=
  pos.injective.extend_apply _ _ _

omit [Fintype ι] [DecidableEq J] in
theorem posLin_apply_of_not_mem (T : Matrix J J K) (v : ι → K) {k : ι}
    (hk : k ∉ Set.range pos) : posLin pos T v k = v k :=
  Function.extend_apply' _ _ _ hk

omit [Fintype ι] [DecidableEq J] in
theorem posLin_comp_pos (T : Matrix J J K) (v : ι → K) :
    posLin pos T v ∘ pos = T *ᵥ (v ∘ pos) :=
  funext fun j => posLin_apply_pos pos T v j

omit [Fintype ι] [DecidableEq J] in
theorem posLin_mul (T T' : Matrix J J K) (v : ι → K) :
    posLin pos (T * T') v = posLin pos T (posLin pos T' v) := by
  funext k
  by_cases hk : k ∈ Set.range pos
  · obtain ⟨j, rfl⟩ := hk
    rw [posLin_apply_pos, posLin_apply_pos, posLin_comp_pos, mulVec_mulVec]
  · rw [posLin_apply_of_not_mem pos _ _ hk, posLin_apply_of_not_mem pos _ _ hk,
      posLin_apply_of_not_mem pos _ _ hk]

omit [Fintype ι] in
theorem posLin_one (v : ι → K) : posLin pos (1 : Matrix J J K) v = v := by
  funext k
  by_cases hk : k ∈ Set.range pos
  · obtain ⟨j, rfl⟩ := hk
    rw [posLin_apply_pos, one_mulVec, Function.comp_apply]
  · rw [posLin_apply_of_not_mem pos _ _ hk]

@[expose] noncomputable def posMat : Matrix J J K →* Matrix ι ι K where
  toFun T := LinearMap.toMatrix' (posLin pos T)
  map_one' := by
    rw [show posLin pos (1 : Matrix J J K) = LinearMap.id from LinearMap.ext (posLin_one pos),
      LinearMap.toMatrix'_id]
  map_mul' T T' := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext (posLin_mul pos T T')

@[expose] noncomputable def posGL : GL J K →* GL ι K :=
  Units.map (posMat pos)

theorem posGL_mulVec (T : GL J K) (v : ι → K) :
    ((posGL pos T : GL ι K) : Matrix ι ι K) *ᵥ v = posLin pos (T : Matrix J J K) v := by
  change LinearMap.toMatrix' (posLin pos (T : Matrix J J K)) *ᵥ v = _
  rw [LinearMap.toMatrix'_mulVec]

theorem posGL_mem_suppSub (T : GL J K) : posGL pos T ∈ suppSub K (Set.range pos) := by
  refine ⟨fun v k hk => ?_, fun v w hvw k hk => ?_⟩
  · rw [posGL_mulVec, posLin_apply_of_not_mem pos _ _ hk]
  · obtain ⟨j, rfl⟩ := hk
    rw [posGL_mulVec, posGL_mulVec, posLin_apply_pos, posLin_apply_pos,
      show v ∘ pos = w ∘ pos from funext fun i => hvw (pos i) ⟨i, rfl⟩]

theorem posGL_injective : Function.Injective (posGL (K := K) pos) := by
  rw [injective_iff_map_eq_one]
  intro T hT
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  have h := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ Function.extend pos x 0) hT
  simp only [posGL_mulVec, Units.val_one, one_mulVec] at h
  funext j
  have h2 := congrFun h (pos j)
  rw [posLin_apply_pos, pos.injective.extend_apply] at h2
  rw [Matrix.toLin'_apply, Units.val_one, Matrix.toLin'_apply, one_mulVec]
  rw [show Function.extend pos x 0 ∘ pos = x from
    funext fun i => pos.injective.extend_apply _ _ _] at h2
  exact h2

end Pos

theorem mem_omega_of_conj_inv {Q : (ι → K) → K} {g w : GL ι K} (hg : g ∈ LargeEvenOrthGroup Q)
    (hw : w ∈ LargeEvenOrthGroup Q) (hwg : w * g * w⁻¹ = g⁻¹) {p : ℕ} (hp : Odd p)
    (hgp : g ^ p = 1) : g ∈ LargeEvenOmega Q := by
  obtain ⟨k, hk⟩ := hp
  have hconj : w * g ^ (k + 1) * w⁻¹ = (g ^ (k + 1))⁻¹ := by
    rw [← conj_pow, hwg, inv_pow]
  have h1 : w * (g ^ (k + 1))⁻¹ * w⁻¹ = g ^ (k + 1) := by
    calc w * (g ^ (k + 1))⁻¹ * w⁻¹ = (w * g ^ (k + 1) * w⁻¹)⁻¹ := by group
      _ = g ^ (k + 1) := by rw [hconj, inv_inv]
  have heq : ⁅g ^ (k + 1), w⁆ = g := by
    rw [commutatorElement_def]
    calc g ^ (k + 1) * w * (g ^ (k + 1))⁻¹ * w⁻¹
        = g ^ (k + 1) * (w * (g ^ (k + 1))⁻¹ * w⁻¹) := by group
      _ = g ^ (k + 1) * g ^ (k + 1) := by rw [h1]
      _ = g ^ p * g := by rw [← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ]
      _ = g := by rw [hgp, one_mul]
  rw [← heq]
  exact Subgroup.commutator_mem_commutator (Subgroup.pow_mem _ hg _) hw

end OrthRestTail

end CFSG.StandardType
