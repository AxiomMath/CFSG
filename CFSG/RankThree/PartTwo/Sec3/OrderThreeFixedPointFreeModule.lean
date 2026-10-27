module

public import CFSG.Assembly.LowTwoRankDefs
import CFSG.LocalAnalysis.RankTwoShapes.FixedPointFreeThree
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.Sporadic.J1
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup CFSG.Assembly.LowTwoRank

section Fixed

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero_of_zmod_two (w : V) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_eq_self_of_zmod_two (w : V) : -w = w :=
  (neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_zmod_two w))

theorem add_add_eq_zero_of_fixedPointFree (ρ : Representation (ZMod 2) K V) {x : K}
    (hx3 : x ^ 3 = 1) (hCV : ∀ v, ρ x v = v → v = 0) (w : V) :
    w + ρ x w + ρ (x ^ 2) w = 0 := by
  have hx3' : x * x ^ 2 = 1 := by rw [← pow_succ']; exact hx3
  apply hCV
  rw [map_add, map_add, ← Module.End.mul_apply (ρ x) (ρ (x ^ 2)), ← map_mul, hx3', map_one,
    Module.End.one_apply, ← Module.End.mul_apply, ← map_mul, ← pow_two]
  abel

theorem apply_eq_self_of_fixedPointFree_three (ρ : Representation (ZMod 2) K V) {x : K}
    (hx3 : x ^ 3 = 1) (hCV : ∀ v, ρ x v = v → v = 0) {F : Subgroup K} [Finite F]
    (hFodd : Odd (Nat.card F)) (hxF : ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hCF : ∀ f ∈ F, x * f * x⁻¹ = f → f = 1) {f : K} (hf : f ∈ F) (v : V) : ρ f v = v := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have e3 : ∀ (a b c : K) (w : V), ρ a (ρ b (ρ c w)) = ρ (a * b * c) w := fun a b c w => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hconj : ∀ h : K, v + ρ (h⁻¹ * x * h) v + ρ (h⁻¹ * x ^ 2 * h) v = 0 := by
    intro h
    have h1 := congrArg (ρ h⁻¹) (add_add_eq_zero_of_fixedPointFree ρ hx3 hCV (ρ h v))
    rw [map_add, map_add, map_zero, e3, e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] at h1
    exact h1
  have hx2F : ∀ g ∈ F, x ^ 2 * g * (x ^ 2)⁻¹ ∈ F := fun g hg => by
    have := hxF _ (hxF g hg)
    rwa [show x * (x * g * x⁻¹) * x⁻¹ = x ^ 2 * g * (x ^ 2)⁻¹ by simp only [pow_two]; group]
      at this
  have hx4 : x ^ 2 * x ^ 2 = x := by
    rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hx3, one_mul]
  let φ₁ : F → F := fun h => ⟨(h : K)⁻¹ * (x * h * x⁻¹), F.mul_mem (F.inv_mem h.2) (hxF h h.2)⟩
  let φ₂ : F → F := fun h =>
    ⟨(h : K)⁻¹ * (x ^ 2 * h * (x ^ 2)⁻¹), F.mul_mem (F.inv_mem h.2) (hx2F h h.2)⟩
  have hφ₁ : Function.Bijective φ₁ := by
    refine Finite.injective_iff_bijective.mp fun a b hab => ?_
    have h : (a : K)⁻¹ * (x * a * x⁻¹) = (b : K)⁻¹ * (x * b * x⁻¹) := congrArg Subtype.val hab
    have h' : x * ((b : K) * (a : K)⁻¹) * x⁻¹ = (b : K) * (a : K)⁻¹ := by
      calc x * ((b : K) * (a : K)⁻¹) * x⁻¹
          = b * ((b : K)⁻¹ * (x * b * x⁻¹)) * (x * (a : K)⁻¹ * x⁻¹) := by group
        _ = b * ((a : K)⁻¹ * (x * a * x⁻¹)) * (x * (a : K)⁻¹ * x⁻¹) := by rw [← h]
        _ = (b : K) * (a : K)⁻¹ := by group
    have h1 := hCF _ (F.mul_mem b.2 (F.inv_mem a.2)) h'
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  have hφ₂ : Function.Bijective φ₂ := by
    refine Finite.injective_iff_bijective.mp fun a b hab => ?_
    have h : (a : K)⁻¹ * (x ^ 2 * a * (x ^ 2)⁻¹) = (b : K)⁻¹ * (x ^ 2 * b * (x ^ 2)⁻¹) :=
      congrArg Subtype.val hab
    have h' : x ^ 2 * ((b : K) * (a : K)⁻¹) * (x ^ 2)⁻¹ = (b : K) * (a : K)⁻¹ := by
      calc x ^ 2 * ((b : K) * (a : K)⁻¹) * (x ^ 2)⁻¹
          = b * ((b : K)⁻¹ * (x ^ 2 * b * (x ^ 2)⁻¹)) * (x ^ 2 * (a : K)⁻¹ * (x ^ 2)⁻¹) := by
            group
        _ = b * ((a : K)⁻¹ * (x ^ 2 * a * (x ^ 2)⁻¹)) * (x ^ 2 * (a : K)⁻¹ * (x ^ 2)⁻¹) := by
            rw [← h]
        _ = (b : K) * (a : K)⁻¹ := by group
    have h'' : x * ((b : K) * (a : K)⁻¹) * x⁻¹ = (b : K) * (a : K)⁻¹ := by
      calc x * ((b : K) * (a : K)⁻¹) * x⁻¹
          = (x ^ 2 * x ^ 2) * ((b : K) * (a : K)⁻¹) * (x ^ 2 * x ^ 2)⁻¹ := by rw [hx4]
        _ = x ^ 2 * (x ^ 2 * ((b : K) * (a : K)⁻¹) * (x ^ 2)⁻¹) * (x ^ 2)⁻¹ := by group
        _ = (b : K) * (a : K)⁻¹ := by rw [h', h']
    have h1 := hCF _ (F.mul_mem b.2 (F.inv_mem a.2)) h''
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  set T : V → V := fun w => ∑ k : F, ρ (k : K) w with hT
  have hT1 : ∑ h : F, ρ ((h : K)⁻¹ * x * h) v = T (ρ x v) := by
    refine Fintype.sum_bijective φ₁ hφ₁ _ _ fun h => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    change (h : K)⁻¹ * x * h = (h : K)⁻¹ * (x * h * x⁻¹) * x
    group
  have hT2 : ∑ h : F, ρ ((h : K)⁻¹ * x ^ 2 * h) v = T (ρ (x ^ 2) v) := by
    refine Fintype.sum_bijective φ₂ hφ₂ _ _ fun h => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    change (h : K)⁻¹ * x ^ 2 * h = (h : K)⁻¹ * (x ^ 2 * h * (x ^ 2)⁻¹) * x ^ 2
    group
  have hsum : ∑ h : F, (v + ρ ((h : K)⁻¹ * x * h) v + ρ ((h : K)⁻¹ * x ^ 2 * h) v) = 0 :=
    Finset.sum_eq_zero fun h _ => hconj h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hT1, hT2, Finset.sum_const,
    Finset.card_univ] at hsum
  have hodd : Fintype.card F • v = v := by
    obtain ⟨k, hk⟩ := hFodd
    rw [← Nat.card_eq_fintype_card, hk, add_smul, one_smul, mul_comm, mul_smul, two_smul,
      add_self_eq_zero_of_zmod_two, smul_zero, zero_add]
  rw [hodd] at hsum
  have hadd : T (ρ x v) + T (ρ (x ^ 2) v) = T (ρ x v + ρ (x ^ 2) v) := by
    simp only [hT, map_add, Finset.sum_add_distrib]
  have hxv : ρ x v + ρ (x ^ 2) v = v := by
    have h := add_add_eq_zero_of_fixedPointFree ρ hx3 hCV v
    rw [add_assoc, add_eq_zero_iff_eq_neg, neg_eq_self_of_zmod_two] at h
    exact h.symm
  rw [add_assoc, hadd, hxv, add_eq_zero_iff_eq_neg, neg_eq_self_of_zmod_two] at hsum
  have hTv : T v = v := hsum.symm
  rw [← hTv, hT]
  simp only [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Fintype.sum_bijective (fun k : F => (⟨f, hf⟩ : F) * k)
    (Group.mulLeft_bijective _) _ _ fun k => rfl

theorem quadratic_of_fixedPointFree_three [Finite V] (ρ : Representation (ZMod 2) K V) {x : K}
    (hx3 : x ^ 3 = 1) (hCV : ∀ v, ρ x v = v → v = 0) {U : Subgroup K} [Finite U]
    (hxU : x ∈ normalizer (U : Set K)) (hCU : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1) {u u' : K}
    (hu : u ∈ U) (hu' : u' ∈ U) (v : V) : ρ u' (ρ u v - v) = ρ u v - v := by
  classical
  let ψ : K →* MulAut (Multiplicative V) :=
    { toFun := fun k =>
        { toFun := fun m => Multiplicative.ofAdd (ρ k (Multiplicative.toAdd m))
          invFun := fun m => Multiplicative.ofAdd (ρ k⁻¹ (Multiplicative.toAdd m))
          left_inv := fun m => by
            change Multiplicative.ofAdd (ρ k⁻¹ (ρ k (Multiplicative.toAdd m))) = m
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply]
            rfl
          right_inv := fun m => by
            change Multiplicative.ofAdd (ρ k (ρ k⁻¹ (Multiplicative.toAdd m))) = m
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
              Module.End.one_apply]
            rfl
          map_mul' := fun a b => by
            change Multiplicative.ofAdd (ρ k (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
              Multiplicative.ofAdd (ρ k (Multiplicative.toAdd a) + ρ k (Multiplicative.toAdd b))
            rw [map_add] }
      map_one' := MulEquiv.ext fun m => by
        change Multiplicative.ofAdd (ρ 1 (Multiplicative.toAdd m)) = m
        rw [map_one, Module.End.one_apply]
        rfl
      map_mul' := fun k l => MulEquiv.ext fun m => by
        change Multiplicative.ofAdd (ρ (k * l) (Multiplicative.toAdd m)) =
          Multiplicative.ofAdd (ρ k (ρ l (Multiplicative.toAdd m)))
        rw [map_mul, Module.End.mul_apply] }
  have hψ : ∀ (k : K) (m : Multiplicative V),
      ψ k m = Multiplicative.ofAdd (ρ k (Multiplicative.toAdd m)) := fun _ _ => rfl
  let φ : U →* MulAut (Multiplicative V) := ψ.comp U.subtype
  let θ : MulAut U := U.normalizerMonoidHom ⟨x, hxU⟩
  have hθ : ∀ g : U, ((θ g : U) : K) = x * g * x⁻¹ := fun g =>
    normalizerMonoidHom_apply_apply_coe _ _ _
  have hcompat : ∀ g : U, (φ g).trans (ψ x) = (ψ x).trans (φ (θ g)) := by
    intro g
    have h : ψ x * ψ g = ψ (x * g * x⁻¹) * ψ x := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    apply MulEquiv.ext
    intro m
    have := congrArg (fun σ : MulAut (Multiplicative V) => σ m) h
    simp only [MulAut.mul_apply] at this
    change ψ x (ψ g m) = ψ ((θ g : U) : K) (ψ x m)
    rw [hθ]
    exact this
  let α : MulAut (Multiplicative V ⋊[φ] U) := SemidirectProduct.congr (ψ x) θ hcompat
  have hα : ∀ q : Multiplicative V ⋊[φ] U, α q = ⟨ψ x q.left, θ q.right⟩ := fun _ => rfl
  have hαk : ∀ (k : ℕ) (q : Multiplicative V ⋊[φ] U),
      (α ^ k) q = ⟨(ψ x ^ k) q.left, (θ ^ k) q.right⟩ := by
    intro k
    induction k with
    | zero => intro q; rfl
    | succ k ih =>
      intro q
      rw [pow_succ', MulAut.mul_apply, ih, hα, pow_succ', pow_succ', MulAut.mul_apply,
        MulAut.mul_apply]
  have hα3 : α ^ 3 = 1 := by
    have hθ3 : θ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxU⟩ : normalizer (U : Set K)) ^ 3 = 1 := Subtype.ext (by simp [hx3])
      rw [this, map_one]
    apply MulEquiv.ext
    intro q
    rw [hαk, ← map_pow, hx3, map_one, hθ3]
    rfl
  have hfpf : ∀ q : Multiplicative V ⋊[φ] U, α q = q → q = 1 := by
    intro q hq
    rw [hα] at hq
    have hr : θ q.right = q.right := congrArg SemidirectProduct.right hq
    have hl : ψ x q.left = q.left := congrArg SemidirectProduct.left hq
    have hr1 : q.right = 1 := by
      have h1 := hCU _ q.right.2 (by rw [← hθ]; exact congrArg Subtype.val hr)
      exact Subtype.ext h1
    have hl1 : q.left = 1 := by
      rw [hψ] at hl
      have h2 : ρ x (Multiplicative.toAdd q.left) = Multiplicative.toAdd q.left :=
        congrArg Multiplicative.toAdd hl
      have h3 := hCV _ h2
      exact Multiplicative.toAdd.injective (by rw [h3]; rfl)
    exact SemidirectProduct.ext hl1 hr1
  have : Finite (Multiplicative V ⋊[φ] U) :=
    Finite.of_injective (fun q : Multiplicative V ⋊[φ] U => (q.left, q.right)) fun a b h =>
      SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  obtain ⟨hcen, -⟩ := CFSG.RankTwoShapes.fixedPointFree_three_class_two α hα3 hfpf
  let g : U := ⟨u, hu⟩
  let g' : U := ⟨u', hu'⟩
  let w : Multiplicative V := Multiplicative.ofAdd (v - ρ u v)
  have hab : SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g *
      (SemidirectProduct.inl (Multiplicative.ofAdd v))⁻¹ * (SemidirectProduct.inr g)⁻¹ ∈
      center (Multiplicative V ⋊[φ] U) :=
    hcen (commutator_mem_commutator (mem_top _) (mem_top _))
  have hcalc : SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g *
      (SemidirectProduct.inl (Multiplicative.ofAdd v))⁻¹ * (SemidirectProduct.inr g)⁻¹ =
      (SemidirectProduct.inl w : Multiplicative V ⋊[φ] U) := by
    have e1 : SemidirectProduct.inr g * (SemidirectProduct.inl (Multiplicative.ofAdd v))⁻¹ *
        (SemidirectProduct.inr g)⁻¹ =
        (SemidirectProduct.inl (φ g (Multiplicative.ofAdd v)⁻¹) : Multiplicative V ⋊[φ] U) := by
      rw [SemidirectProduct.inl_aut, ← map_inv SemidirectProduct.inr,
        ← map_inv SemidirectProduct.inl]
    rw [mul_assoc _ (SemidirectProduct.inr g), mul_assoc, e1, ← map_mul]
    congr 1
    change Multiplicative.ofAdd v * Multiplicative.ofAdd (ρ u (-v)) = _
    rw [map_neg, ← ofAdd_add, ← sub_eq_add_neg]
  rw [hcalc, mem_center_iff] at hab
  have h1 := hab (SemidirectProduct.inr g')
  have h2 : (SemidirectProduct.inl (φ g' w) : Multiplicative V ⋊[φ] U) =
      SemidirectProduct.inl w := by
    rw [SemidirectProduct.inl_aut, map_inv, h1, mul_inv_cancel_right]
  have h4 : ρ u' (v - ρ u v) = v - ρ u v :=
    congrArg Multiplicative.toAdd (SemidirectProduct.inl_injective h2)
  rw [show ρ u v - v = -(v - ρ u v) by abel, map_neg, h4]

end Fixed

section FourGroup

theorem exists_fourGroup_of_cyclic {G : Type*} [Group G] {s t y : G} (hs : s * s = 1)
    (ht : t * t = 1) (hst : t * s = s * t) (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hne : s ≠ t)
    (hys : y * s * y⁻¹ = t) (hyt : y * t * y⁻¹ = s * t) :
    ∃ U : Subgroup G, Nat.card U = 4 ∧ (∀ g ∈ U, g ^ 2 = 1) ∧ y ∈ normalizer (U : Set G) ∧
      ∀ g ∈ U, y * g * y⁻¹ = g → g = 1 := by
  have hss : ∀ g, s * (s * g) = g := fun g => by rw [← mul_assoc, hs, one_mul]
  have htt : ∀ g, t * (t * g) = g := fun g => by rw [← mul_assoc, ht, one_mul]
  have hts : ∀ g, t * (s * g) = s * (t * g) := fun g => by rw [← mul_assoc, hst, mul_assoc]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let U : Subgroup G :=
    { carrier := {1, s, t, s * t}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [mul_assoc, hs, ht, hst, hss, hts]
      one_mem' := Set.mem_insert _ _
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> simp [hsi, hti, hst] }
  have hmem : ∀ g, g ∈ U ↔ g = 1 ∨ g = s ∨ g = t ∨ g = s * t := fun g => Iff.rfl
  have hst1 : s * t ≠ 1 := fun h => hne (by rw [← hsi]; exact (eq_inv_of_mul_eq_one_right h).symm)
  have hsts : s * t ≠ s := fun h => ht1 (by simpa using h)
  have hstt : s * t ≠ t := fun h => hs1 (by simpa using h)
  have hys' : y * (s * t) * y⁻¹ = s := by
    rw [show y * (s * t) * y⁻¹ = (y * s * y⁻¹) * (y * t * y⁻¹) by group, hys, hyt, hts, ht,
      mul_one]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · change Nat.card ({1, s, t, s * t} : Set G) = 4
    rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hstt.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hsts.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hs1.symm, ht1.symm, hst1.symm⟩
  · intro g hg
    rcases (hmem g).mp hg with h | h | h | h <;> rw [h]
    · exact one_pow 2
    · rw [sq, hs]
    · rw [sq, ht]
    · rw [sq, mul_assoc, hts, ht, mul_one, hs]
  · have h1 : ∀ g ∈ U, y * g * y⁻¹ ∈ U := fun g hg => by
      rw [hmem]
      rcases (hmem g).mp hg with h | h | h | h <;> rw [h]
      · left; group
      · right; right; left; exact hys
      · right; right; right; exact hyt
      · right; left; exact hys'
    have h2 : ∀ g ∈ U, y⁻¹ * g * y ∈ U := fun g hg => by
      rw [hmem]
      rcases (hmem g).mp hg with h | h | h | h <;> rw [h]
      · left; group
      · right; right; right
        calc y⁻¹ * s * y = y⁻¹ * (y * (s * t) * y⁻¹) * y := by rw [hys']
          _ = s * t := by group
      · right; left
        rw [← hys, show y⁻¹ * (y * s * y⁻¹) * y = s by group]
      · right; right; left
        rw [← hyt, show y⁻¹ * (y * t * y⁻¹) * y = t by group]
    refine mem_normalizer_iff.mpr fun g => ⟨h1 g, fun hg => ?_⟩
    have := h2 _ hg
    rwa [show y⁻¹ * (y * g * y⁻¹) * y = g by group] at this
  · intro g hg hyg
    rcases (hmem g).mp hg with h | h | h | h <;> rw [h] at hyg ⊢
    · exact absurd (hys.symm.trans hyg) hne.symm
    · exact absurd (hyt.symm.trans hyg) hstt
    · exact absurd ((hys'.symm.trans hyg).symm) hsts

section Matrix2

variable {F : Type*} [Field F]

theorem trace_eq_neg_one_of_cube_eq_one (h2 : (2 : F) ≠ 0) {ω : Matrix (Fin 2) (Fin 2) F}
    (hdet : ω.det = 1) (h3ω : ω * ω * ω = 1) (h1 : ω ≠ 1) : ω 0 0 + ω 1 1 = -1 := by
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ i j, (ω * ω * ω) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [h3ω]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have k01 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 0 1 = 0 := by linear_combination e01 + ω 0 1 * hdet
  have k10 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 1 0 = 0 := by linear_combination e10 + ω 1 0 * hdet
  have k00 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 0 0 - (1 + (ω 0 0 + ω 1 1)) = 0 := by
    linear_combination e00 + (2 * ω 0 0 + ω 1 1) * hdet
  have k11 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 1 1 - (1 + (ω 0 0 + ω 1 1)) = 0 := by
    linear_combination e11 + (ω 0 0 + 2 * ω 1 1) * hdet
  by_cases hτ : (ω 0 0 + ω 1 1) ^ 2 - 1 = 0
  · rw [hτ, zero_mul, zero_sub, neg_eq_zero] at k00
    linear_combination k00
  · exfalso
    have hb := (mul_eq_zero.mp k01).resolve_left hτ
    have hc := (mul_eq_zero.mp k10).resolve_left hτ
    have had : ω 0 0 = ω 1 1 := mul_left_cancel₀ hτ (by linear_combination k00 - k11)
    have ha2 : ω 0 0 * ω 0 0 = 1 := by
      rw [hb, hc, ← had] at hdet
      linear_combination hdet
    rcases mul_self_eq_one_iff.mp ha2 with ha | ha
    · apply h1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, ← had]
    · rw [← had, ha] at k00
      exact h2 (by linear_combination -k00)

theorem exists_conj_companion (h3 : (3 : F) ≠ 0) {ω : Matrix (Fin 2) (Fin 2) F}
    (hdet : ω.det = 1) (htr : ω 0 0 + ω 1 1 = -1) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) F, P * Q = 1 ∧ Q * P = 1 ∧
      ω * P = P * !![0, -1; 1, -1] := by
  rw [Matrix.det_fin_two] at hdet
  have key : ∀ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 → ω * P = P * !![0, -1; 1, -1] →
      ∃ P Q : Matrix (Fin 2) (Fin 2) F, P * Q = 1 ∧ Q * P = 1 ∧
        ω * P = P * !![0, -1; 1, -1] :=
    fun P hP h => ⟨P, P⁻¹, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP),
      Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP), h⟩
  by_cases hc : ω 1 0 = 0
  · by_cases hb : ω 0 1 = 0
    · refine key !![1, ω 0 0; 1, ω 1 1] ?_ ?_
      · rw [Matrix.det_fin_two_of]
        intro hda
        apply h3
        linear_combination (ω 0 0 + ω 1 1 - 1) * htr - (ω 1 1 - ω 0 0) * hda - 4 * hdet -
          4 * ω 1 0 * hb
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        all_goals first
          | linear_combination hb
          | linear_combination hc
          | linear_combination (ω 0 0 + ω 0 1) * htr - hdet + (-ω 0 0 - ω 1 0 - 1) * hb
          | linear_combination ω 1 1 * htr - hdet - ω 1 0 * hb + ω 0 0 * hc
    · refine key !![0, ω 0 1; 1, ω 1 1] ?_ ?_
      · rw [Matrix.det_fin_two_of]
        simpa using hb
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        all_goals first
          | linear_combination ω 0 1 * htr
          | linear_combination ω 1 1 * htr - hdet
  · refine key !![1, ω 0 0; 0, ω 1 0] ?_ ?_
    · rw [Matrix.det_fin_two_of]
      simpa using hc
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals first
        | linear_combination ω 0 0 * htr - hdet
        | linear_combination ω 1 0 * htr

theorem exists_conic_six [Fintype F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hodd : Fintype.card F % 2 = 1) : ∃ u v : F, u ^ 2 + u * v + v ^ 2 + 6 = 0 := by
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 + Polynomial.C 24) (g := Polynomial.C 3 * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) _) (Polynomial.degree_C_mul_X_pow 2 h3) hodd
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul] at hab
  refine ⟨(a - b) * 2⁻¹, b, ?_⟩
  have hh : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination (2⁻¹ : F) ^ 2 * hab + (-(2⁻¹ : F) * (a * b + b ^ 2 + 12) - b ^ 2 - 6) * hh

theorem exists_quaternion_of_cube [Fintype F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hodd : Fintype.card F % 2 = 1) {ω : Matrix (Fin 2) (Fin 2) F} (hdet : ω.det = 1)
    (h3ω : ω * ω * ω = 1) (h1 : ω ≠ 1) :
    ∃ i j : Matrix (Fin 2) (Fin 2) F, i.det = 1 ∧ j.det = 1 ∧ i * i = -1 ∧ j * j = -1 ∧
      i * j = -(j * i) ∧ ω * i = j * ω ∧ ω * j = -(i * j) * ω := by
  have htr := trace_eq_neg_one_of_cube_eq_one h2 hdet h3ω h1
  obtain ⟨P, Q, hPQ, hQP, hωP⟩ := exists_conj_companion h3 hdet htr
  obtain ⟨u, v, huv⟩ := exists_conic_six h2 h3 hodd
  have hc : ∀ A B : Matrix (Fin 2) (Fin 2) F, (P * A * Q) * (P * B * Q) = P * (A * B) * Q := by
    intro A B
    calc (P * A * Q) * (P * B * Q) = P * A * (Q * P) * B * Q := by simp only [mul_assoc]
      _ = P * (A * B) * Q := by rw [hQP, mul_one]; simp only [mul_assoc]
  have hω : ω = P * !![0, -1; 1, -1] * Q := by rw [← hωP, mul_assoc, hPQ, mul_one]
  have hII : !![1 + u, -2 + v; 2 + u + v, -1 - u] * !![1 + u, -2 + v; 2 + u + v, -1 - u] =
      (-9 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | linear_combination huv
  have hJJ : !![v + 1, -u - v - 2; 2 - u, -v - 1] * !![v + 1, -u - v - 2; 2 - u, -v - 1] =
      (-9 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | linear_combination huv
  have hIJ : !![1 + u, -2 + v; 2 + u + v, -1 - u] * !![v + 1, -u - v - 2; 2 - u, -v - 1] =
      -(!![v + 1, -u - v - 2; 2 - u, -v - 1] * !![1 + u, -2 + v; 2 + u + v, -1 - u]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | linear_combination -huv
  have hCI : !![0, -1; 1, -1] * !![1 + u, -2 + v; 2 + u + v, -1 - u] =
      !![v + 1, -u - v - 2; 2 - u, -v - 1] * (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hCJ : !![1 + u, -2 + v; 2 + u + v, -1 - u] * !![v + 1, -u - v - 2; 2 - u, -v - 1] *
      !![0, -1; 1, -1] = -((3 : F) • (!![0, -1; 1, -1] *
        (!![v + 1, -u - v - 2; 2 - u, -v - 1] : Matrix (Fin 2) (Fin 2) F))) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | linear_combination -huv | linear_combination huv
  have hdI : (!![1 + u, -2 + v; 2 + u + v, -1 - u] : Matrix (Fin 2) (Fin 2) F).det = 9 := by
    rw [Matrix.det_fin_two_of]
    linear_combination -huv
  have hdJ : (!![v + 1, -u - v - 2; 2 - u, -v - 1] : Matrix (Fin 2) (Fin 2) F).det = 9 := by
    rw [Matrix.det_fin_two_of]
    linear_combination -huv
  have ht : (3 : F) * 3⁻¹ = 1 := mul_inv_cancel₀ h3
  have hdPQ : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  have hsq : (3 : F)⁻¹ * 3⁻¹ * -9 = -1 := by linear_combination (-(3 * (3 : F)⁻¹ + 1)) * ht
  refine ⟨(3 : F)⁻¹ • (P * !![1 + u, -2 + v; 2 + u + v, -1 - u] * Q),
    (3 : F)⁻¹ • (P * !![v + 1, -u - v - 2; 2 - u, -v - 1] * Q), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, hdI, Fintype.card_fin]
    linear_combination (9 * (3 : F)⁻¹ ^ 2) * hdPQ + (3 * (3 : F)⁻¹ + 1) * ht
  · rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, hdJ, Fintype.card_fin]
    linear_combination (9 * (3 : F)⁻¹ ^ 2) * hdPQ + (3 * (3 : F)⁻¹ + 1) * ht
  · rw [smul_mul_smul_comm, hc, hII, Matrix.mul_smul, mul_one, Matrix.smul_mul, hPQ, smul_smul,
      hsq, neg_one_smul]
  · rw [smul_mul_smul_comm, hc, hJJ, Matrix.mul_smul, mul_one, Matrix.smul_mul, hPQ, smul_smul,
      hsq, neg_one_smul]
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, hc, hc, hIJ, Matrix.mul_neg, Matrix.neg_mul,
      smul_neg]
  · rw [hω, Matrix.mul_smul, Matrix.smul_mul, hc, hc, hCI]
  · rw [hω, Matrix.mul_smul, smul_mul_smul_comm, Matrix.neg_mul, Matrix.smul_mul, hc, hc, hc,
      hCJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_neg, neg_neg, smul_smul]
    congr 1
    linear_combination (-(3 : F)⁻¹) * ht

end Matrix2

theorem exists_fourGroup_psl_two {K : Type} [Group K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSL 2 p f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x : K}
    (hx : orderOf x = 3) :
    ∃ U : Subgroup K, Nat.card U = 4 ∧ (∀ g ∈ U, g ^ 2 = 1) ∧ x ∈ normalizer (U : Set K) ∧
      ∀ g ∈ U, x * g * x⁻¹ = g → g = 1 := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := hK
  have e' : K ≃* StatedProj (StatedSL 2 F) := e
  let E : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    e'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have : Fintype F := Fintype.ofFinite F
  have hpF : ((p : ℕ) : F) = 0 := by
    have h0 := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF, Nat.cast_pow] at h0
    exact (pow_eq_zero_iff (by omega)).mp h0
  have h2 : (2 : F) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have h' : ((p : ℕ) : F) = 2 * k + 1 := by rw [hk]; push_cast; ring
    rw [hpF, h, zero_mul, zero_add] at h'
    exact zero_ne_one h'
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have hm : p % 3 ≠ 0 := fun h0 =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    have h' : ((p : ℕ) : F) = 3 * ((p / 3 : ℕ) : F) + ((p % 3 : ℕ) : F) := by
      conv_lhs => rw [← Nat.div_add_mod p 3]
      push_cast
      ring
    rw [hpF, h, zero_mul, zero_add] at h'
    rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with hm' | hm' <;> rw [hm'] at h'
    · exact zero_ne_one (by exact_mod_cast h')
    · exact h2 (by exact_mod_cast h'.symm)
  have hodd : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, hF]
    exact Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  have hcen : ∀ z ∈ center (Matrix.SpecialLinearGroup (Fin 2) F), z ^ 2 = 1 := by
    intro z hz
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hrz, ← map_pow,
      hr, map_one]
  set y := E x with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    have hx1 : x = 1 := E.injective (by rw [← hy, h, map_one])
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  obtain ⟨ω₁, hω₁⟩ := QuotientGroup.mk_surjective y
  have hz : ω₁ ^ 3 ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hω₁, hy3]
  set ω := ω₁ ^ 4 with hωdef
  have hmkω : (ω : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = y := by
    rw [hωdef, QuotientGroup.mk_pow, hω₁, pow_succ, hy3, one_mul]
  have hω3 : ω ^ 3 = 1 := by
    rw [hωdef, ← pow_mul, show 4 * 3 = 3 * 2 * 2 by norm_num, pow_mul, pow_mul, hcen _ hz,
      one_pow]
  have hW1 : (ω : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h
    apply hy1
    rw [← hmkω, show ω = 1 from Subtype.ext h, QuotientGroup.mk_one]
  have hW3 : (ω : Matrix (Fin 2) (Fin 2) F) * ω * ω = 1 := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F)) hω3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
    rw [← pow_three', h]
  obtain ⟨i, j, hi, hj, hii, hjj, hij, hωi, hωj⟩ :=
    exists_quaternion_of_cube h2 h3 hodd (Matrix.SpecialLinearGroup.det_coe ω) hW3 hW1
  let I : Matrix.SpecialLinearGroup (Fin 2) F := ⟨i, hi⟩
  let J : Matrix.SpecialLinearGroup (Fin 2) F := ⟨j, hj⟩
  let M : Matrix.SpecialLinearGroup (Fin 2) F := ⟨-1, by simp [Matrix.det_neg]⟩
  have hM : M ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by norm_num, by rw [map_neg, map_one]⟩
  have hMq : (M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 1 :=
    (QuotientGroup.eq_one_iff M).mpr hM
  have hII : I * I = M := Subtype.ext (show i * i = -1 from hii)
  have hJJ : J * J = M := Subtype.ext (show j * j = -1 from hjj)
  have hIJ : I * J = M * (J * I) :=
    Subtype.ext (show i * j = -1 * (j * i) by rw [hij, neg_one_mul])
  have hωI : ω * I = J * ω := Subtype.ext (show (ω : Matrix (Fin 2) (Fin 2) F) * i = j * ω from hωi)
  have hωJ : ω * J = M * (I * J) * ω :=
    Subtype.ext (show (ω : Matrix (Fin 2) (Fin 2) F) * j = -1 * (i * j) * ω by
      rw [hωj, neg_one_mul])
  have hnc : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F) * A = -1 →
      (A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1 := by
    intro A hA hA1
    obtain ⟨r, hr, hrA⟩ :=
      Matrix.SpecialLinearGroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff A).mp hA1)
    rw [Fintype.card_fin] at hr
    rw [← hrA, ← map_mul, ← sq, hr, map_one] at hA
    have h00 := congrFun (congrFun hA 0) 0
    simp at h00
    exact h2 (by linear_combination h00)
  set s' := (I : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) with hs'
  set t' := (J : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) with ht'
  have hss : s' * s' = 1 := by rw [hs', ← QuotientGroup.mk_mul, hII, hMq]
  have htt : t' * t' = 1 := by rw [ht', ← QuotientGroup.mk_mul, hJJ, hMq]
  have hts : t' * s' = s' * t' := by
    have h : ((I * J : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = ((J * I : Matrix.SpecialLinearGroup
          (Fin 2) F) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      rw [hIJ, QuotientGroup.mk_mul, hMq, one_mul]
    rw [hs', ht', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  have hys : y * s' * y⁻¹ = t' := by
    rw [← hmkω, hs', ht', ← QuotientGroup.mk_mul, hωI, QuotientGroup.mk_mul,
      mul_inv_cancel_right]
  have hyt : y * t' * y⁻¹ = s' * t' := by
    rw [← hmkω, hs', ht', ← QuotientGroup.mk_mul, hωJ, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, hMq, one_mul, QuotientGroup.mk_mul, mul_inv_cancel_right]
  have hs1 : s' ≠ 1 := hnc I hii
  have ht1 : t' ≠ 1 := hnc J hjj
  have hne : s' ≠ t' := by
    intro h
    obtain ⟨r, hr, hrc⟩ :=
      Matrix.SpecialLinearGroup.mem_center_iff.mp (QuotientGroup.eq.mp h)
    rw [Fintype.card_fin] at hr
    have hJ' : j = i * Matrix.scalar (Fin 2) r := by
      have h' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F)) (show J = I * (I⁻¹ * J) by group)
      simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
      rw [hrc]
      exact h'
    have hc : Matrix.scalar (Fin 2) r * i = i * Matrix.scalar (Fin 2) r :=
      (Matrix.scalar_commute r (fun r' => Commute.all r r') i).eq
    rw [hJ', ← mul_assoc, hii, mul_assoc, hc, ← mul_assoc, hii, neg_one_mul, neg_neg] at hij
    have h00 := congrFun (congrFun hij 0) 0
    simp at h00
    have hr0 : r = 0 := by
      have h2r : 2 * r = 0 := by linear_combination -h00
      exact (mul_eq_zero.mp h2r).resolve_left h2
    rw [hr0] at hr
    simp at hr
  have hxy : x = E.symm y := (E.symm_apply_apply x).symm
  refine exists_fourGroup_of_cyclic (s := E.symm s') (t := E.symm t') ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, hss, map_one]
  · rw [← map_mul, htt, map_one]
  · rw [← map_mul, ← map_mul, hts]
  · exact fun h => hs1 (E.symm.injective (h.trans (map_one _).symm))
  · exact fun h => ht1 (E.symm.injective (h.trans (map_one _).symm))
  · exact fun h => hne (E.symm.injective h)
  · rw [hxy, ← map_inv, ← map_mul, ← map_mul, hys]
  · rw [hxy, ← map_inv, ← map_mul, ← map_mul, hyt, map_mul]

end FourGroup

universe u

@[expose] def L3SingerFact : Prop :=
  (∀ (K : Type) [Group K] [Finite K] (p f : ℕ), StatedClassicalModel K .PSL 3 p f →
    p ^ f % 3 = 2 → ∀ x : K, orderOf x = 3 → ∃ C : Subgroup K, IsCyclic C ∧
      Nat.card C = (p ^ f) ^ 2 + p ^ f + 1 ∧ x ∈ normalizer (C : Set K) ∧
      ∀ c ∈ C, x * c * x⁻¹ = c → c = 1) ∧
  (∀ (K : Type) [Group K] [Finite K] (p f : ℕ), StatedClassicalModel K .PSU 3 p f →
    p ^ f % 3 = 1 → ∀ x : K, orderOf x = 3 → ∃ C : Subgroup K, IsCyclic C ∧
      Nat.card C = (p ^ f) ^ 2 - p ^ f + 1 ∧ x ∈ normalizer (C : Set K) ∧
      ∀ c ∈ C, x * c * x⁻¹ = c → c = 1)

@[expose] def J1SevenFact : Prop :=
  ∀ x : CFSG.Blueprint.NativeSporadic.J1, orderOf x = 3 →
    ∃ F : Subgroup CFSG.Blueprint.NativeSporadic.J1, Nat.card F = 7 ∧
      x ∈ normalizer (F : Set CFSG.Blueprint.NativeSporadic.J1) ∧
      ∀ g ∈ F, x * g * x⁻¹ = g → g = 1

section Cases

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

theorem false_of_frobenius_kernel {K : Type*} [Group K] [IsSimpleGroup K]
    (ρ : Representation (ZMod 2) K V) (hV : ∃ k v, ρ k v ≠ v) {x : K} (hx3 : x ^ 3 = 1)
    (hCV : ∀ v, ρ x v = v → v = 0) {F : Subgroup K} [Finite F] (hF1 : F ≠ ⊥)
    (hFodd : Odd (Nat.card F)) (hxF : x ∈ normalizer (F : Set K))
    (hCF : ∀ f ∈ F, x * f * x⁻¹ = f → f = 1) : False := by
  obtain ⟨k, v, hkv⟩ := hV
  have hker : F ≤ ρ.ker := fun f hf => by
    rw [MonoidHom.mem_ker]
    exact LinearMap.ext fun w => apply_eq_self_of_fixedPointFree_three ρ hx3 hCV hFodd
      (fun g hg => (mem_normalizer_iff.mp hxF g).mp hg) hCF hf w
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · exact hF1 (le_bot_iff.mp (h ▸ hker))
  · have hk : ρ k = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top k)
    exact hkv (by rw [hk]; rfl)

theorem isSimpleGroup_of_statedClassicalModel_psl {K : Type} [Group K] {n p f : ℕ}
    (h : StatedClassicalModel K .PSL n p f) : IsSimpleGroup K :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ h).2

theorem card_ne_one_odd_of_eq {K : Type*} [Group K] {C : Subgroup K} {m : ℕ}
    (hC : Nat.card C = m) (hm1 : m ≠ 1) (hm : Odd m) : C ≠ ⊥ ∧ Odd (Nat.card C) :=
  ⟨fun h => hm1 (by rw [← hC, h, card_bot]), hC ▸ hm⟩

theorem false_of_psl_three (hL3 : L3SingerFact) {K : Type} [Group K] [Finite K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSL 3 p f) (hq : p ^ f % 3 = 2) {x : K} (hx : orderOf x = 3)
    (ρ : Representation (ZMod 2) K V) (hV : ∃ k v, ρ k v ≠ v)
    (hCV : ∀ v, ρ x v = v → v = 0) : False := by
  obtain ⟨C, -, hC, hxC, hCC⟩ := hL3.1 K p f hK hq x hx
  have := isSimpleGroup_of_statedClassicalModel_psl hK
  have hq1 : 1 ≤ p ^ f := Nat.one_le_iff_ne_zero.mpr (by omega)
  have he : Even ((p ^ f) ^ 2 + p ^ f) := by
    rw [sq, ← Nat.mul_succ]
    exact Nat.even_mul_succ_self _
  obtain ⟨hC1, hCodd⟩ := card_ne_one_odd_of_eq hC (by intro h; nlinarith) he.add_one
  exact false_of_frobenius_kernel ρ hV (hx ▸ pow_orderOf_eq_one x) hCV hC1 hCodd hxC hCC

theorem false_of_psu_three (hL3 : L3SingerFact) {K : Type} [Group K] [Finite K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSU 3 p f) (hq : p ^ f % 3 = 1) {x : K} (hx : orderOf x = 3)
    (ρ : Representation (ZMod 2) K V) (hV : ∃ k v, ρ k v ≠ v)
    (hCV : ∀ v, ρ x v = v → v = 0) : False := by
  obtain ⟨C, -, hC, hxC, hCC⟩ := hL3.2 K p f hK hq x hx
  have := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity K 3 p f hK).2
  have hq2 : 2 ≤ p ^ f := by
    have hp := hK.1.1
    exact le_trans hp.two_le (Nat.le_self_pow (by have := hK.1.2.1; omega) p)
  have hlt : p ^ f < (p ^ f) ^ 2 := by nlinarith
  obtain ⟨hC1, hCodd⟩ := card_ne_one_odd_of_eq hC (by omega) (by
    have he : Even ((p ^ f) ^ 2 - p ^ f) := by
      rw [sq, ← Nat.mul_sub_one]
      exact Nat.even_mul_pred_self _
    exact he.add_one)
  exact false_of_frobenius_kernel ρ hV (hx ▸ pow_orderOf_eq_one x) hCV hC1 hCodd hxC hCC

theorem false_of_J1 (hJ1 : J1SevenFact) {K : Type} [Group K] [Finite K]
    (e : K ≃* CFSG.Blueprint.NativeSporadic.J1) {x : K} (hx : orderOf x = 3)
    (ρ : Representation (ZMod 2) K V) (hV : ∃ k v, ρ k v ≠ v)
    (hCV : ∀ v, ρ x v = v → v = 0) : False := by
  have := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J1.isSimpleGroup_J1 e
  obtain ⟨F', hF', hxF', hCF'⟩ :=
    hJ1 (e x) ((orderOf_injective e.toMonoidHom e.injective x).trans hx)
  set F : Subgroup K := F'.map e.symm.toMonoidHom with hFdef
  have hmem : ∀ g, g ∈ F ↔ e g ∈ F' := fun g => mem_map_equiv
  have hF : Nat.card F = 7 := by
    rw [hFdef, card_map_of_injective e.symm.injective, hF']
  obtain ⟨hF1, hFodd⟩ := card_ne_one_odd_of_eq hF (by norm_num) (by decide)
  refine false_of_frobenius_kernel ρ hV (hx ▸ pow_orderOf_eq_one x) hCV hF1 hFodd ?_ ?_
  · rw [mem_normalizer_iff]
    intro g
    rw [hmem, hmem, map_mul, map_mul, map_inv]
    exact mem_normalizer_iff.mp hxF' (e g)
  · intro g hg hxg
    have h1 := hCF' (e g) ((hmem g).mp hg) (by rw [← map_inv, ← map_mul, ← map_mul, hxg])
    exact e.injective (by rw [h1, map_one])

theorem statedClassicalModel_psl_two_four_of_five {K : Type} [Group K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSL 2 p f) (h5 : p ^ f = 5) :
    StatedClassicalModel K .PSL 2 2 2 := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  have e' : K ≃* StatedProj (StatedSL 2 F) := e
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inr (by rw [hF, h5]))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hcard]; norm_num))
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hcard, ⟨(e'.trans e5).trans e4.symm⟩⟩

theorem statedClassicalModel_psl_three_two_of_seven {K : Type} [Group K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSL 2 p f) (h7 : p ^ f = 7) :
    StatedClassicalModel K .PSL 3 2 1 := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  have e' : K ≃* StatedProj (StatedSL 2 F) := e
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF, h7]
  let φ : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let f₁ : StatedProj (StatedSL 2 F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨((((e'.trans f₁).trans e₄.symm).trans e₃.symm).trans e₂.symm).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

end Cases

end CFSG.RankThree.PartTwo.Sec3
