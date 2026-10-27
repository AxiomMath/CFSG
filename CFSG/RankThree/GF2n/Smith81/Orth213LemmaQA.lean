module

public import CFSG.RankThree.GF2n.Smith81.Orth213LemmaQE
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.GF2n.Smith81.Orth213.LemmaQ

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Eichler

variable {K : Type} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

@[expose] def eN (u w : V) : V →ₗ[K] V where
  toFun v := polar Q v u • w + polar Q v w • u
  map_add' x y := by
    simp only [polar_add_left, add_smul]
    abel
  map_smul' c x := by
    simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply]
    module

theorem eN_apply (u w v : V) : eN Q u w v = polar Q v u • w + polar Q v w • u := rfl

@[expose] def gramScalar (u w u' w' : V) : K :=
  polar Q u u' * polar Q w w' + polar Q u w' * polar Q w u'

variable {Q}

theorem eichler_eq_add_eN {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (v : V) : eichler Q u w v = v + eN Q u w v := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero, sub_eq_add_neg, neg_eq_self_mod K, eN_apply,
    add_assoc]

theorem eN_eN {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) (v : V) :
    eN Q u w (eN Q u w v) = 0 := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have hww : polar Q w w = 0 := polar_self_eq_zero hw
  simp only [eN_apply, polar_add_left, polar_smul_left, smul_eq_mul, hwu, huu, hww, huw, mul_zero,
    add_zero, zero_smul]

theorem eN_eq_zero_iff {u w : V} (hind : LinearIndependent K ![u, w]) (v : V) :
    eN Q u w v = 0 ↔ polar Q v u = 0 ∧ polar Q v w = 0 := by
  constructor
  · intro h
    rw [eN_apply, add_comm] at h
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hind _ _ h
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    rw [eN_apply, h1, h2, zero_smul, zero_smul, add_zero]

theorem eN_mem {S : Submodule K V} {u w : V} (hu : u ∈ S) (hw : w ∈ S) (v : V) :
    eN Q u w v ∈ S := by
  rw [eN_apply]
  exact S.add_mem (S.smul_mem _ hw) (S.smul_mem _ hu)

theorem qU_smul_add_smul {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (α β : K) : Q (α • u + β • w) = 0 := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hu, hw, polar_smul_left_eq,
    polar_smul_right_eq, huw]
  ring

theorem exists_polar_eq (hnd : ∀ x : V, (∀ y : V, polar Q x y = 0) → x = 0) {u w : V}
    (hind : LinearIndependent K ![u, w]) (a b : K) :
    ∃ s : V, polar Q s u = a ∧ polar Q s w = b := by
  let T : V →ₗ[K] K × K := ((polarBilin Q).flip u).prod ((polarBilin Q).flip w)
  have hTs : ∀ s, T s = (polar Q s u, polar Q s w) := fun s => rfl
  have hT : Function.Surjective T := by
    rw [← LinearMap.dualMap_injective_iff]
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    have h1 : ∀ s, φ (T s) = 0 := fun s => by
      simpa using LinearMap.congr_fun hφ s
    have hφxy : ∀ x y : K, φ (x, y) = x * φ (1, 0) + y * φ (0, 1) := by
      intro x y
      have : ((x, y) : K × K) = x • ((1, 0) : K × K) + y • ((0, 1) : K × K) := by simp
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    set l := φ (1, 0) with hl_def
    set m := φ (0, 1) with hm_def
    have h2 : ∀ s, polar Q s (l • u + m • w) = 0 := by
      intro s
      have := h1 s
      rw [hTs, hφxy] at this
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]
      linear_combination this
    have h3 : l • u + m • w = 0 := hnd _ (fun s => by rw [polar_comm]; exact h2 s)
    obtain ⟨hl, hm⟩ := LinearIndependent.pair_iff.mp hind l m h3
    refine LinearMap.ext fun p => ?_
    obtain ⟨x, y⟩ := p
    simp [hφxy x y, hl, hm]
  obtain ⟨s, hs⟩ := hT (a, b)
  exact ⟨s, congrArg Prod.fst hs, congrArg Prod.snd hs⟩

theorem eichler_invol {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) (v : V) :
    eichler Q u w (eichler Q u w v) = v := by
  rw [eichler_eq_add_eN hu hw huw, eichler_eq_add_eN hu hw huw, map_add, eN_eN hu hw huw,
    add_zero, add_assoc, add_self_eq_zero_mod K, add_zero]

theorem eN_pair_u {u w u' w' : V} (hu : Q u = 0) (huw : polar Q u w = 0) :
    eN Q u w (eN Q u' w' u) + eN Q u' w' (eN Q u w u) = gramScalar Q u w u' w' • u := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have h2 : (2 : K) • w = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have e1 : polar Q w' u = polar Q u w' := polar_comm Q w' u
  have e2 : polar Q w' w = polar Q w w' := polar_comm Q w' w
  have e3 : polar Q u' u = polar Q u u' := polar_comm Q u' u
  have e4 : polar Q u' w = polar Q w u' := polar_comm Q u' w
  simp only [gramScalar, eN_apply, polar_add_left, polar_smul_left_eq, huu, huw, e1, e2, e3, e4,
    zero_smul, smul_zero, add_zero, polar_zero_left]
  linear_combination (norm := module) (polar Q u u' * polar Q u w') • h2

theorem eN_pair_w {u w u' w' : V} (hw : Q w = 0) (huw : polar Q u w = 0) :
    eN Q u w (eN Q u' w' w) + eN Q u' w' (eN Q u w w) = gramScalar Q u w u' w' • w := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have hww : polar Q w w = 0 := polar_self_eq_zero hw
  have h2 : (2 : K) • u = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have e1 : polar Q w' u = polar Q u w' := polar_comm Q w' u
  have e2 : polar Q w' w = polar Q w w' := polar_comm Q w' w
  have e3 : polar Q u' u = polar Q u u' := polar_comm Q u' u
  have e4 : polar Q u' w = polar Q w u' := polar_comm Q u' w
  simp only [gramScalar, eN_apply, polar_add_left, polar_smul_left_eq, hww, hwu, e1, e2, e3, e4,
    zero_smul, smul_zero, add_zero, polar_zero_left]
  linear_combination (norm := module) (polar Q w u' * polar Q w w') • h2

theorem gramScalar_swap (u w u' w' : V) :
    gramScalar Q u' w' u w = gramScalar Q u w u' w' := by
  simp only [gramScalar, polar_comm Q u' u, polar_comm Q w' w, polar_comm Q u' w,
    polar_comm Q w' u]
  ring

theorem C_eq_of_mem_span {ux wx uy wy : V} (hux : Q ux = 0) (hwx : Q wx = 0)
    (huwx : polar Q ux wx = 0) (huy : Q uy = 0) (hwy : Q wy = 0) (huwy : polar Q uy wy = 0)
    {z : V} (hz : z ∈ Submodule.span K ({ux, wx, uy, wy} : Set V)) :
    eN Q ux wx (eN Q uy wy z) + eN Q uy wy (eN Q ux wx z) = gramScalar Q ux wx uy wy • z := by
  let C : V →ₗ[K] V := (eN Q ux wx) ∘ₗ (eN Q uy wy) + (eN Q uy wy) ∘ₗ (eN Q ux wx)
  have hC : ∀ z, C z = eN Q ux wx (eN Q uy wy z) + eN Q uy wy (eN Q ux wx z) := fun z => rfl
  let G : V →ₗ[K] V := gramScalar Q ux wx uy wy • (LinearMap.id : V →ₗ[K] V)
  have hG : ∀ z, G z = gramScalar Q ux wx uy wy • z := fun z => rfl
  have key : Set.EqOn C G ({ux, wx, uy, wy} : Set V) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [hC, hG]
      exact eN_pair_u hux huwx
    · rw [hC, hG]
      exact eN_pair_w hwx huwx
    · rw [hC, hG, add_comm, ← gramScalar_swap]
      exact eN_pair_u huy huwy
    · rw [hC, hG, add_comm, ← gramScalar_swap]
      exact eN_pair_w hwy huwy
  have := LinearMap.eqOn_span key hz
  rw [hC, hG] at this
  exact this

theorem eichler_anticomm {u w u' w' : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (hu' : Q u' = 0) (hw' : Q w' = 0) (huw' : polar Q u' w' = 0) (z : V) :
    eichler Q u w (eichler Q u' w' z) + eichler Q u' w' (eichler Q u w z) =
      eN Q u w (eN Q u' w' z) + eN Q u' w' (eN Q u w z) := by
  rw [eichler_eq_add_eN hu hw huw, eichler_eq_add_eN hu' hw' huw', eichler_eq_add_eN hu hw huw,
    eichler_eq_add_eN hu' hw' huw']
  simp only [map_add]
  have h1 := add_self_eq_zero_mod K z
  have h2 := add_self_eq_zero_mod K (eN Q u w z)
  have h3 := add_self_eq_zero_mod K (eN Q u' w' z)
  linear_combination (norm := module) h1 + h2 + h3

theorem AA_odd [Finite V] {ux wx uy wy : V} (hux : Q ux = 0) (hwx : Q wx = 0)
    (huwx : polar Q ux wx = 0) (huy : Q uy = 0) (hwy : Q wy = 0) (huwy : polar Q uy wy = 0)
    (ht : gramScalar Q ux wx uy wy ≠ 0) :
    ∃ k : ℕ, Odd k ∧ (eichler Q ux wx * eichler Q uy wy) ^ k = 1 := by
  have hXX : ∀ v, eichler Q ux wx (eichler Q ux wx v) = v := eichler_invol hux hwx huwx
  have hYY : ∀ v, eichler Q uy wy (eichler Q uy wy v) = v := eichler_invol huy hwy huwy
  refine exists_odd_pow_eq_one_of_cubic K (eichler Q ux wx * eichler Q uy wy) ht (fun v => ?_)
  set W' : Submodule K V := Submodule.span K ({ux, wx, uy, wy} : Set V) with hW'
  have hux' : ux ∈ W' := Submodule.subset_span (by simp)
  have hwx' : wx ∈ W' := Submodule.subset_span (by simp)
  have huy' : uy ∈ W' := Submodule.subset_span (by simp)
  have hwy' : wy ∈ W' := Submodule.subset_span (by simp)
  have hz : (eichler Q ux wx * eichler Q uy wy) v + v ∈ W' := by
    have h : (eichler Q ux wx * eichler Q uy wy) v + v =
        eN Q uy wy v + eN Q ux wx v + eN Q ux wx (eN Q uy wy v) := by
      rw [LinearEquiv.mul_apply, eichler_eq_add_eN huy hwy huwy, eichler_eq_add_eN hux hwx huwx,
        map_add]
      have h1 := add_self_eq_zero_mod K v
      linear_combination (norm := module) h1
    rw [h]
    exact W'.add_mem (W'.add_mem (eN_mem huy' hwy' v) (eN_mem hux' hwx' v))
      (eN_mem hux' hwx' _)
  have hzz : eichler Q ux wx (eichler Q uy wy ((eichler Q ux wx * eichler Q uy wy) v + v)) +
      eichler Q uy wy (eichler Q ux wx ((eichler Q ux wx * eichler Q uy wy) v + v)) =
      gramScalar Q ux wx uy wy • ((eichler Q ux wx * eichler Q uy wy) v + v) := by
    rw [eichler_anticomm hux hwx huwx huy hwy huwy]
    exact C_eq_of_mem_span hux hwx huwx huy hwy huwy hz
  exact ap_cubic (eichler Q ux wx) (eichler Q uy wy) hXX hYY hzz

theorem gramScalar_ne_zero {ux wx uy wy : V}
    (hcase : ∀ α β : K, polar Q (α • ux + β • wx) uy = 0 → polar Q (α • ux + β • wx) wy = 0 →
      α = 0 ∧ β = 0) : gramScalar Q ux wx uy wy ≠ 0 := by
  intro ht
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ∀ α β : K, α * polar Q ux uy + β * polar Q wx uy = 0 →
      α * polar Q ux wy + β * polar Q wx wy = 0 → α = 0 ∧ β = 0 := by
    intro α β h1 h2
    apply hcase
    · simpa only [polar_add_left, polar_smul_left_eq] using h1
    · simpa only [polar_add_left, polar_smul_left_eq] using h2
  unfold gramScalar at ht
  obtain ⟨h21, h11⟩ := key (polar Q wx uy) (polar Q ux uy)
    (by linear_combination (polar Q ux uy * polar Q wx uy) * h2)
    (by linear_combination ht)
  obtain ⟨h22, h12⟩ := key (polar Q wx wy) (polar Q ux wy)
    (by linear_combination ht)
    (by linear_combination (polar Q ux wy * polar Q wx wy) * h2)
  have := (key 1 0 (by rw [h11]; ring) (by rw [h12]; ring)).1
  exact one_ne_zero this

end Eichler

section Prod

variable {K : Type} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]

theorem pow_prod_apply (A B : V ≃ₗ[K] V) (X Y : (V × V) ≃ₗ[K] (V × V))
    (hX : ∀ p, X p = (A p.1, A p.2)) (hY : ∀ p, Y p = (B p.1, B p.2)) (k : ℕ) (p : V × V) :
    ((X * Y) ^ k) p = (((A * B) ^ k) p.1, ((A * B) ^ k) p.2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (X * Y), LinearEquiv.mul_apply, ih]
    simp only [LinearEquiv.mul_apply, hX, hY, pow_succ' (A * B)]

end Prod

section AACases

variable {K : Type} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem eichler_fix_iff {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) (z : V) :
    eichler Q u w z = z ↔ eN Q u w z = 0 := by
  rw [eichler_eq_add_eN hu hw huw, add_eq_left]

theorem eN_eq_zero_of_eN {ux wx uy wy : V} (hindy : LinearIndependent K ![uy, wy])
    (hcase : ∀ α β : K, polar Q (α • ux + β • wx) uy = 0 → polar Q (α • ux + β • wx) wy = 0 →
      α = 0 ∧ β = 0) (z : V) (h : eN Q uy wy (eN Q ux wx z) = 0) : eN Q ux wx z = 0 := by
  obtain ⟨h1, h2⟩ := (eN_eq_zero_iff hindy _).mp h
  have hform : eN Q ux wx z = polar Q z wx • ux + polar Q z ux • wx := by
    rw [eN_apply, add_comm]
  rw [hform] at h1 h2
  obtain ⟨hα, hβ⟩ := hcase _ _ h1 h2
  rw [hform, hα, hβ, zero_smul, zero_smul, add_zero]

theorem AA_right [Finite V] {ux wx uy wy : V} (hux : Q ux = 0) (hwx : Q wx = 0)
    (huwx : polar Q ux wx = 0) (huy : Q uy = 0) (hwy : Q wy = 0) (huwy : polar Q uy wy = 0)
    (hindy : LinearIndependent K ![uy, wy])
    (hcase : ∀ α β : K, polar Q (α • ux + β • wx) uy = 0 → polar Q (α • ux + β • wx) wy = 0 →
      α = 0 ∧ β = 0)
    (X Y : (V × V) ≃ₗ[K] (V × V))
    (hX : ∀ p, X p = (eichler Q ux wx p.1, eichler Q ux wx p.2))
    (hY : ∀ p, Y p = (eichler Q uy wy p.1, eichler Q uy wy p.2)) :
    ∃ k : ℕ, Odd k ∧ (X * Y) ^ k = 1 ∧
      ∀ v ∈ LinearMap.range ((X : (V × V) →ₗ[K] (V × V)) - 1), (X * Y) v = v → v = 0 := by
  obtain ⟨k, hk, hSk⟩ := AA_odd hux hwx huwx huy hwy huwy (gramScalar_ne_zero hcase)
  refine ⟨k, hk, ?_, ?_⟩
  · apply LinearEquiv.ext
    intro p
    rw [pow_prod_apply _ _ X Y hX hY, hSk]
    rfl
  · intro v hv hfix
    have hXX : ∀ p, X (X p) = p := by
      intro p
      rw [hX, hX, eichler_invol hux hwx huwx, eichler_invol hux hwx huwx]
    rw [mul_fix_iff X Y hXX hv] at hfix
    obtain ⟨w, rfl⟩ := (mem_range_sub_one_iff X v).mp hv
    have hw : X w - w = (eN Q ux wx w.1, eN Q ux wx w.2) := by
      rw [hX]
      refine Prod.ext ?_ ?_
      · simp [eichler_eq_add_eN hux hwx huwx]
      · simp [eichler_eq_add_eN hux hwx huwx]
    rw [hw] at hfix ⊢
    rw [hY] at hfix
    simp only [Prod.mk.injEq] at hfix
    obtain ⟨hf1, hf2⟩ := hfix
    rw [eichler_fix_iff huy hwy huwy] at hf1 hf2
    rw [eN_eq_zero_of_eN hindy hcase _ hf1, eN_eq_zero_of_eN hindy hcase _ hf2]
    rfl

theorem AA_left {ι : Type} {Q : QuadraticForm K (ι → K)}
    (hnd : ∀ x : ι → K, (∀ y : ι → K, polar Q x y = 0) → x = 0) {ux wx uy wy : ι → K}
    (hux : Q ux = 0) (hwx : Q wx = 0) (huwx : polar Q ux wx = 0)
    (hindx : LinearIndependent K ![ux, wx]) (huy : Q uy = 0) (hwy : Q wy = 0)
    (huwy : polar Q uy wy = 0) {α β : K} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (h1 : polar Q (α • ux + β • wx) uy = 0) (h2 : polar Q (α • ux + β • wx) wy = 0)
    (X Y : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K)))
    (hX : ∀ p, X p = (eichler Q ux wx p.1, eichler Q ux wx p.2))
    (hY : ∀ p, Y p = (eichler Q uy wy p.1, eichler Q uy wy p.2)) :
    ∃ v, v ∈ LinearMap.range ((X : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K))) - 1) ∧
      Y v = v ∧ PairTypeA Q v := by
  set p := α • ux + β • wx with hp
  have hp0 : p ≠ 0 := by
    intro h
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hindx α β h
    rcases hαβ with h | h
    · exact h h1
    · exact h h2
  have hQp : Q p = 0 := qU_smul_add_smul hux hwx huwx α β
  obtain ⟨s, hs1, hs2⟩ := exists_polar_eq hnd hindx β α
  have hNs : eN Q ux wx s = p := by rw [eN_apply, hs1, hs2, hp, add_comm]
  refine ⟨(p, 0), ?_, ?_, ⟨1, 0, p, Or.inl one_ne_zero, hp0, hQp, by simp⟩⟩
  · rw [mem_range_sub_one_iff]
    refine ⟨(s, 0), ?_⟩
    rw [hX]
    simp [eichler_eq_add_eN hux hwx huwx, hNs]
  · rw [hY]
    have : eichler Q uy wy p = p := (eichler_fix_iff huy hwy huwy p).mpr
      (by rw [eN_apply, h1, h2, zero_smul, zero_smul, add_zero])
    simp [this]

end AACases

end CFSG.RankThree.GF2n.Smith81.Orth213.LemmaQ
