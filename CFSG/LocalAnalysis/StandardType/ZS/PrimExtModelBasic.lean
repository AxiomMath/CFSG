module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvLinAlg
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.PrimModel

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem eq_of_toMatrix_eq {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {x y : U ≃ₗ[ZMod p] U}
    (h : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (y : U →ₗ[ZMod p] U)) : x = y := by
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix f f).injective h)

theorem eq_mul_of_toMatrix_eq_mul {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {x y z : U ≃ₗ[ZMod p] U}
    (h : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) * LinearMap.toMatrix f f (y : U →ₗ[ZMod p] U)) :
    z = x * y := by
  refine eq_of_toMatrix_eq f ?_
  rw [h, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

theorem eq_neg_of_toMatrix_eq_neg_one {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {z : U ≃ₗ[ZMod p] U} (h : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) = -1) :
    z = LinearEquiv.neg (ZMod p) := by
  refine eq_of_toMatrix_eq f ?_
  rw [h]
  have hneg : ((LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = -LinearMap.id := by
    ext v; rfl
  rw [hneg, map_neg, LinearMap.toMatrix_id]

theorem apply_basis_of_toMatrix_eq_diagonal {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {z : U ≃ₗ[ZMod p] U} {d : Fin n → ZMod p}
    (h : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) = Matrix.diagonal d) (i : Fin n) :
    z (f i) = d i • f i := by
  rw [f.ext_elem_iff]
  intro j
  have h1 : f.repr (z (f i)) j = LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) j i :=
    (LinearMap.toMatrix_apply f f (z : U →ₗ[ZMod p] U) j i).symm
  rw [h1, h, Matrix.diagonal_apply, map_smul, Module.Basis.repr_self]
  by_cases hj : j = i
  · subst hj; simp
  · rw [if_neg hj, Finsupp.smul_apply, Finsupp.single_eq_of_ne hj, smul_zero]

theorem ker_sub_one_of_toMatrix_eq_diagSignMat (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {t : U ≃ₗ[ZMod p] U} {i : Fin n}
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = diagSignMat i) :
    LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) = LinearMap.ker (f.coord i) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ht_eq : (t : U →ₗ[ZMod p] U) = 1 - (f.coord i).smulRight ((2 : ZMod p) • f i) := by
    apply f.ext
    intro j
    have happ := apply_basis_of_toMatrix_eq_diagonal f
      (d := fun j => if j = i then -1 else 1) (by simpa [diagSignMat] using ht) j
    have htj : (↑t : U →ₗ[ZMod p] U) (f j) = t (f j) := rfl
    rw [htj, happ, LinearMap.sub_apply, LinearMap.smulRight_apply, Module.End.one_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, Finsupp.single_eq_same, one_smul, two_smul, neg_smul, one_smul]
      abel
    · simp [hj]
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ht_eq]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smulRight_apply]
  have hsimp : v - (f.coord i) v • ((2 : ZMod p) • f i) - v =
      -((f.coord i) v • ((2 : ZMod p) • f i)) := by abel
  rw [hsimp, neg_eq_zero, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      rw [smul_eq_zero] at h
      rcases h with h | h
      · exact h2 h
      · exact f.ne_zero i h
  · intro h; exact Or.inl h

theorem finrank_span_basis_image {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (I : Finset (Fin n)) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) (f '' ↑I)) = I.card := by
  rw [Set.image_eq_range]
  rw [finrank_span_eq_card]
  · simp
  · exact f.linearIndependent.comp _ Subtype.val_injective

private theorem mem_span_image_iff_support_subset {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {s : Set (Fin n)} {v : U} :
    v ∈ Submodule.span (ZMod p) (f '' s) ↔ ↑(f.repr v).support ⊆ s := by
  constructor
  · intro hv
    exact Module.Basis.repr_support_subset_of_mem_span f s hv
  · intro hv
    exact Submodule.span_mono (Set.image_mono hv) (Module.Basis.mem_span_repr_support f v)

theorem span_image_erase_eq_ker_coord {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (i : Fin n) :
    Submodule.span (ZMod p) (f '' ↑(Finset.univ.erase i)) = LinearMap.ker (f.coord i) := by
  ext v
  rw [mem_span_image_iff_support_subset, LinearMap.mem_ker, Module.Basis.coord_apply]
  constructor
  · intro h
    by_contra hne
    have hmem := h (Finsupp.mem_support_iff.mpr hne)
    rw [Finset.mem_coe, Finset.mem_erase] at hmem
    exact hmem.1 rfl
  · intro hzero j hj
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
    intro hji
    exact (Finsupp.mem_support_iff.mp (by rwa [hji] at hj)) hzero

theorem iInf_ker_coord_eq_span_image {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (I : Finset (Fin n)) :
    ⨅ i ∈ I, LinearMap.ker (f.coord i) = Submodule.span (ZMod p) (f '' ↑Iᶜ) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Module.Basis.coord_apply]
  constructor
  · intro hv
    rw [mem_span_image_iff_support_subset]
    intro i hi
    rw [Finset.mem_coe, Finset.mem_compl]
    intro hiI
    exact (Finsupp.mem_support_iff.mp hi) (hv i hiI)
  · intro hv i hi
    by_contra hne
    have hsub := (mem_span_image_iff_support_subset f).mp hv
    have hmem : i ∈ (Iᶜ : Finset (Fin n)) :=
      Finset.mem_coe.mp (hsub (Finsupp.mem_support_iff.mpr hne))
    exact (Finset.mem_compl.mp hmem) hi

theorem diagSignMat_mul_diagSignMat {K : Type} [Field K] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (diagSignMat i * diagSignMat j : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun l => if l ∈ ({i, j} : Finset (Fin n)) then -1 else 1 := by
  ext l m
  rw [diagSignMat, diagSignMat, Matrix.diagonal_mul_diagonal]
  simp only [Matrix.diagonal_apply]
  by_cases hlm : l = m
  · subst hlm
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      simp_all [Finset.mem_insert, Finset.mem_singleton]
  · simp [hlm]

theorem diagSignMat_mul_diagSignMat_mul_diagSignMat {K : Type} [Field K] {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (diagSignMat i * diagSignMat j * diagSignMat k : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun l => if l ∈ ({i, j, k} : Finset (Fin n)) then -1 else 1 := by
  ext l m
  rw [diagSignMat, diagSignMat, diagSignMat, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  simp only [Matrix.diagonal_apply]
  by_cases hlm : l = m
  · subst hlm
    by_cases hli : l = i <;> by_cases hlj : l = j <;> by_cases hlk : l = k <;>
      simp_all [Finset.mem_insert, Finset.mem_singleton]
  · simp [hlm]

theorem reflection_mul_comm {r r' : U} {c c' : Module.Dual (ZMod p) U} (hc : c r = 2)
    (hc' : c' r' = 2) (h₁ : c r' = 0) (h₂ : c' r = 0) :
    Module.reflection hc * Module.reflection hc' =
      Module.reflection hc' * Module.reflection hc := by
  ext v
  change Module.reflection hc (Module.reflection hc' v) =
    Module.reflection hc' (Module.reflection hc v)
  simp only [Module.reflection_apply]
  simp only [map_sub, map_smul, h₁, h₂, smul_eq_mul, mul_zero, sub_zero]
  abel

theorem transvectionFree_of_isometry (hp : p ≠ 2) (B : LinearMap.BilinForm (ZMod p) U)
    (hB : B.IsSymm) (hnd : B.Nondegenerate) {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : ∀ g ∈ G, ∀ x y, B (g x) (g y) = B x y) : QTwoLin.TransvectionFree G := by
  intro g hg htv
  rw [QTwoLin.IsTransvectionLin] at htv
  obtain ⟨u, ψ, hu, hψ, hψu, hgv⟩ := htv
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hE : ∀ x y, ψ y * B x u + ψ x * B u y + ψ x * ψ y * B u u = 0 := by
    intro x y
    have h := hG g hg x y
    rw [hgv x, hgv y] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    linear_combination h
  have hne : ∃ x, ψ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (LinearMap.ext h)
  have huu : B u u = 0 := by
    obtain ⟨x, hx⟩ := hne
    have h := hE x u
    simp only [hψu, zero_mul, mul_zero, add_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hx
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀u : B x₀ u = 0 := by
    have h := hE x₀ x₀
    rw [huu, mul_zero, add_zero, hB.eq u x₀] at h
    have h2' : (2 : ZMod p) * (ψ x₀ * B x₀ u) = 0 := by linear_combination h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left h2)).resolve_left hx₀
  have hBu : ∀ y, B u y = 0 := by
    intro y
    have h := hE x₀ y
    simp only [huu, hx₀u, mul_zero, add_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hx₀
  exact hu (hnd.1 u hBu)

theorem isometry_of_mem_closure (B : LinearMap.BilinForm (ZMod p) U)
    {S : Set (U ≃ₗ[ZMod p] U)} (hS : ∀ s ∈ S, ∀ x y, B (s x) (s y) = B x y)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ Subgroup.closure S) (x y : U) : B (g x) (g y) = B x y := by
  refine Subgroup.closure_induction (p := fun g _ => ∀ x y, B (g x) (g y) = B x y)
    (fun s hs => hS s hs) ?_ ?_ ?_ hg x y
  · intro x y; simp
  · intro a b _ _ iha ihb x y
    change B (a (b x)) (a (b y)) = B x y
    rw [iha (b x) (b y), ihb x y]
  · intro a _ iha x y
    simpa using (iha (a⁻¹ x) (a⁻¹ y)).symm

theorem reflection_isometry (hp : p ≠ 2) (B : LinearMap.BilinForm (ZMod p) U) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) {r : U} {c : Module.Dual (ZMod p) U} (hc : c r = 2)
    (hcB : ∀ v, B r r * c v = 2 * B r v) (x y : U) :
    B (Module.reflection hc x) (Module.reflection hc y) = B x y := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hk : B r r ≠ 0 := by
    intro h0
    have hr0 : r = 0 := hnd.1 r fun v => by
      have := hcB v
      rw [h0, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_left h2
    rw [hr0, map_zero] at hc
    exact h2 hc.symm
  have hcv : ∀ v, c v = 2 * B r v / B r r := by
    intro v
    field_simp
    linear_combination hcB v
  have hexp : B (Module.reflection hc x) (Module.reflection hc y) =
      B x y - c y * B x r - c x * B r y + c x * c y * B r r := by
    rw [Module.reflection_apply, Module.reflection_apply]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexp, hB.eq x r, hcv x, hcv y]
  field_simp
  ring

theorem transvectionFree_of_not_dvd_card {G : Subgroup (U ≃ₗ[ZMod p] U)} (_hG : Nat.card G ≠ 0)
    (hpG : ¬ p ∣ Nat.card G) : QTwoLin.TransvectionFree G := by
  intro g hg htv
  rw [QTwoLin.IsTransvectionLin] at htv
  obtain ⟨u, ψ, hu, hψ, hψu, hgv⟩ := htv
  have hpow : ∀ (w : U) (n : ℕ), (g ^ n) w = w + (n : ZMod p) • (ψ w • u) := by
    intro w n
    induction n with
    | zero => simp
    | succ n ih =>
      have hψn : ψ (w + (n : ZMod p) • (ψ w • u)) = ψ w := by
        simp [map_add, map_smul, hψu, smul_eq_mul]
      rw [pow_succ', show (g * g ^ n) w = g ((g ^ n) w) from rfl, ih, hgv, hψn]
      rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
  have hgp : g ^ p = 1 := by
    ext w
    rw [hpow w p, ZMod.natCast_self, zero_smul, add_zero]
    rfl
  obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (LinearMap.ext h)
  have hgne : g ≠ 1 := by
    intro hg1
    have hvv : g v = v := by rw [hg1]; rfl
    rw [hgv v] at hvv
    have hzero : ψ v • u = 0 := by
      have h' : v + ψ v • u = v + 0 := by simpa using hvv
      exact add_left_cancel h'
    rcases smul_eq_zero.mp hzero with h | h
    · exact hv h
    · exact hu h
  let x : G := ⟨g, hg⟩
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    simpa [x, Subgroup.coe_pow] using hgp
  have hxne : x ≠ 1 := by
    intro hx1
    exact hgne (by simpa [x] using congrArg Subtype.val hx1)
  have hdvd : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  rw [orderOf_eq_prime hxp hxne] at hdvd
  exact hpG hdvd

section Orbit

variable {m P d M : ℕ} {g : Fin m → U ≃ₗ[ZMod p] U} {x : Fin P → U} {π : Fin m → Fin P → Fin P}
  {O : Fin M → Fin d → Fin P}

theorem exists_orbit_index_of_mem_closure (hg : ∀ k, g k * g k = 1)
    (hπ : ∀ k i, g k (x i) = x (π k i)) {nxt : Fin m → Fin M → Fin M}
    (hnxt : ∀ k i, O (nxt k i) = fun l => π k (O i l)) {h : U ≃ₗ[ZMod p] U}
    (hh : h ∈ Subgroup.closure (Set.range g)) (i : Fin M) :
    ∃ i', ∀ l, h (x (O i l)) = x (O i' l) := by
  have key : ∀ h ∈ Subgroup.closure (Set.range g),
      ∀ i, ∃ i', ∀ l, h (x (O i l)) = x (O i' l) := by
    intro h hh
    refine Subgroup.closure_induction'' (p := fun h _ => ∀ i, ∃ i', ∀ l,
      h (x (O i l)) = x (O i' l)) ?_ ?_ ?_ ?_ hh
    · intro k hk i
      obtain ⟨k', rfl⟩ := hk
      exact ⟨nxt k' i, fun l => by rw [hπ k' (O i l), hnxt k' i]⟩
    · intro k hk i
      obtain ⟨k', rfl⟩ := hk
      refine ⟨nxt k' i, fun l => ?_⟩
      rw [inv_eq_of_mul_eq_one_right (hg k'), hπ k' (O i l), hnxt k' i]
    · intro i
      exact ⟨i, fun l => by simp⟩
    · intro a b _ _ iha ihb i
      obtain ⟨i1, h1⟩ := ihb i
      obtain ⟨i2, h2⟩ := iha i1
      exact ⟨i2, fun l => by
        rw [show (a * b) (x (O i l)) = a (b (x (O i l))) from rfl, h1 l, h2 l]⟩
  exact key h hh i

theorem exists_mem_closure_of_orbit (hπ : ∀ k i, g k (x i) = x (π k i))
    {pred : Fin M → Fin M} {pk : Fin M → Fin m} (i₀ : Fin M)
    (hpred : ∀ i, i = i₀ ∨ (pred i < i ∧ O i = fun l => π (pk i) (O (pred i) l))) (i : Fin M) :
    ∃ h ∈ Subgroup.closure (Set.range g), ∀ l, h (x (O i₀ l)) = x (O i l) := by
  have key : ∀ k, ∀ hk : k < M, ∃ h ∈ Subgroup.closure (Set.range g),
      ∀ l, h (x (O i₀ l)) = x (O ⟨k, hk⟩ l) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hbase : (⟨k, hk⟩ : Fin M) = i₀
      · refine ⟨1, Subgroup.one_mem _, fun l => ?_⟩
        simp [hbase]
      · rcases (hpred ⟨k, hk⟩).resolve_left hbase with ⟨hlt, hOi⟩
        obtain ⟨h', hh', hspec⟩ :=
          ih (pred ⟨k, hk⟩).val (show (pred ⟨k, hk⟩).val < k from hlt) (pred ⟨k, hk⟩).isLt
        refine ⟨g (pk ⟨k, hk⟩) * h', Subgroup.mul_mem _
          (Subgroup.subset_closure ⟨pk ⟨k, hk⟩, rfl⟩) hh', fun l => ?_⟩
        rw [show (g (pk ⟨k, hk⟩) * h') (x (O i₀ l)) =
            g (pk ⟨k, hk⟩) (h' (x (O i₀ l))) from rfl,
          hspec l, hπ (pk ⟨k, hk⟩) (O (pred ⟨k, hk⟩) l), hOi]
  exact key i.val i.isLt

omit [AddCommGroup U] in
private theorem orbit_index_unique (hx : Function.Injective x) (hO : Function.Injective O)
    {i i' : Fin M} (h : ∀ l, x (O i l) = x (O i' l)) : i = i' := by
  exact hO (funext fun l => hx (h l))

theorem card_closure_eq_of_orbit (hg : ∀ k, g k * g k = 1) (hx : Function.Injective x)
    (hπ : ∀ k i, g k (x i) = x (π k i)) (hO : Function.Injective O) (i₀ : Fin M)
    (hb : ∀ h : U ≃ₗ[ZMod p] U, (∀ l, h (x (O i₀ l)) = x (O i₀ l)) → h = 1)
    {nxt : Fin m → Fin M → Fin M} (hnxt : ∀ k i, O (nxt k i) = fun l => π k (O i l))
    {pred : Fin M → Fin M} {pk : Fin M → Fin m}
    (hpred : ∀ i, i = i₀ ∨ (pred i < i ∧ O i = fun l => π (pk i) (O (pred i) l))) :
    Nat.card (Subgroup.closure (Set.range g)) = M := by
  let G := Subgroup.closure (Set.range g)
  let Φ : G → Fin M := fun h =>
    Classical.choose (exists_orbit_index_of_mem_closure hg hπ hnxt h.2 i₀)
  have hspec : ∀ (h : G) (l : Fin d),
      (h : U ≃ₗ[ZMod p] U) (x (O i₀ l)) = x (O (Φ h) l) := fun h l =>
    Classical.choose_spec (exists_orbit_index_of_mem_closure hg hπ hnxt h.2 i₀) l
  have hinj : Function.Injective Φ := by
    intro h h' heq
    have hfix : ∀ l, ((h'⁻¹ * h : G) : U ≃ₗ[ZMod p] U) (x (O i₀ l)) = x (O i₀ l) := by
      intro l
      have hmem : ((h'⁻¹ * h : G) : U ≃ₗ[ZMod p] U) (x (O i₀ l)) =
          ((h' : G) : U ≃ₗ[ZMod p] U)⁻¹ (((h : G) : U ≃ₗ[ZMod p] U) (x (O i₀ l))) := rfl
      rw [hmem, hspec h l, heq, ← hspec h' l]
      simp
    have h1 : (h'⁻¹ * h : G) = 1 := by
      apply Subtype.ext
      exact hb ((h'⁻¹ * h : G) : U ≃ₗ[ZMod p] U) hfix
    calc h = h' * (h'⁻¹ * h) := by group
      _ = h' * 1 := by rw [h1]
      _ = h' := by simp
  have hsurj : Function.Surjective Φ := by
    intro i
    obtain ⟨h, hh, hspec'⟩ := exists_mem_closure_of_orbit hπ i₀ hpred i
    refine ⟨⟨h, hh⟩, ?_⟩
    apply orbit_index_unique hx hO
    intro l
    rw [← hspec (⟨h, hh⟩ : G) l]
    exact hspec' l
  have hcard := Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩
  rw [show Nat.card (Fin M) = M by simp] at hcard
  simpa [G] using hcard

end Orbit

theorem coord_smul_mem_of_signChange (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {X : Submodule (ZMod p) U} {i : Fin n} {d : U ≃ₗ[ZMod p] U}
    (hd : d (f i) = -f i ∧ ∀ j, j ≠ i → d (f j) = f j) (hX : ∀ x ∈ X, d x ∈ X) {x : U}
    (hx : x ∈ X) : f.coord i x • f i ∈ X := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hd_eq : (d : U →ₗ[ZMod p] U) = 1 - (f.coord i).smulRight ((2 : ZMod p) • f i) := by
    apply f.ext
    intro j
    have hdj : (↑d : U →ₗ[ZMod p] U) (f j) = d (f j) := rfl
    rw [hdj]
    by_cases hj : j = i
    · subst hj
      rw [hd.1, LinearMap.sub_apply, LinearMap.smulRight_apply, Module.End.one_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul,
        two_smul]
      abel
    · rw [hd.2 j hj, LinearMap.sub_apply, LinearMap.smulRight_apply, Module.End.one_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hj),
        zero_smul, sub_zero]
  have hdx : d x = x - (f.coord i x) • ((2 : ZMod p) • f i) := by
    rw [show d x = (d : U →ₗ[ZMod p] U) x from rfl, hd_eq, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.smulRight_apply]
  have hxsub : x - d x = (f.coord i x) • ((2 : ZMod p) • f i) := by
    rw [hdx]; abel
  have hthis : f.coord i x • f i = (2 : ZMod p)⁻¹ • (x - d x) := by
    rw [hxsub, smul_smul, smul_smul]
    congr 1
    field_simp
  rw [hthis]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx (hX x hx))

theorem irredOnSection_span_of_hub (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (I : Finset (Fin n)) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hd : ∀ i ∈ I, ∃ d ∈ H, d (f i) = -f i ∧ ∀ j, j ≠ i → d (f j) = f j)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ H) {r : U} {c : Module.Dual (ZMod p) U}
    (htr : ∀ v, t v = v - c v • r) (hr : ∀ i ∈ I, f.coord i r ≠ 0)
    (hc : ∀ i ∈ I, c (f i) ≠ 0) : IrredOnSection H ⊥ (Submodule.span (ZMod p) (f '' ↑I)) := by
  intro X _ hXle hinv
  by_cases hXbot : X = ⊥
  · exact Or.inl hXbot
  · right
    apply le_antisymm hXle
    obtain ⟨x, hxX, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXbot
    have hxW : x ∈ Submodule.span (ZMod p) (f '' ↑I) := hXle hxX
    have hrepne : f.repr x ≠ 0 := by
      intro h
      exact hxne (f.repr.injective (by rw [h, map_zero]))
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrepne
    have hiI : i ∈ I := Finset.mem_coe.mp ((mem_span_image_iff_support_subset f).mp hxW hi)
    have hcxi : f.coord i x ≠ 0 := by
      rw [Module.Basis.coord_apply]
      exact Finsupp.mem_support_iff.mp hi
    have hfiX : f i ∈ X := by
      obtain ⟨d, hdH, hdval, hdrest⟩ := hd i hiI
      have h := Submodule.smul_mem _ ((f.coord i x)⁻¹)
        (coord_smul_mem_of_signChange (X := X) (i := i) (d := d) (x := x) hp f
          ⟨hdval, hdrest⟩ (hinv d hdH) hxX)
      rwa [smul_smul, inv_mul_cancel₀ hcxi, one_smul] at h
    have hrX : r ∈ X := by
      have hsub : t (f i) - f i ∈ X := Submodule.sub_mem _ (hinv t ht (f i) hfiX) hfiX
      have hsub' : (-(c (f i))) • r ∈ X := by
        have : t (f i) - f i = (-(c (f i))) • r := by rw [htr (f i)]; module
        rwa [this] at hsub
      have h := Submodule.smul_mem _ ((-(c (f i)))⁻¹) hsub'
      rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr (hc i hiI)), one_smul] at h
    rw [Submodule.span_le]
    rintro w ⟨j, hj, rfl⟩
    have hjI : j ∈ I := Finset.mem_coe.mp hj
    obtain ⟨d', hdH', hdval', hdrest'⟩ := hd j hjI
    have h := Submodule.smul_mem _ ((f.coord j r)⁻¹)
      (coord_smul_mem_of_signChange (X := X) (i := j) (d := d') (x := r) hp f
        ⟨hdval', hdrest'⟩ (hinv d' hdH') hrX)
    rwa [smul_smul, inv_mul_cancel₀ (hr j hjI), one_smul] at h

theorem movedSpace_of_toMatrix_eq_diagonal (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) (I : Finset (Fin n)) {z : U ≃ₗ[ZMod p] U}
    (hz : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) =
      Matrix.diagonal fun i => if i ∈ I then -1 else 1) :
    HardMathSupport.Kantor79.movedSpace z = Submodule.span (ZMod p) (f '' ↑I) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hzj : ∀ j, ((z : U →ₗ[ZMod p] U) - 1) (f j) =
      (if j ∈ I then (-2 : ZMod p) else 0) • f j := by
    intro j
    have happ := apply_basis_of_toMatrix_eq_diagonal f hz j
    rw [LinearMap.sub_apply, Module.End.one_apply,
      show (↑z : U →ₗ[ZMod p] U) (f j) = z (f j) from rfl, happ]
    by_cases hj : j ∈ I
    · rw [if_pos hj, if_pos hj, neg_smul, one_smul, neg_smul, two_smul]
      abel
    · rw [if_neg hj, if_neg hj, one_smul, sub_self, zero_smul]
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    have hsum : ((z : U →ₗ[ZMod p] U) - 1) v =
        ∑ j, f.coord j v • (((z : U →ₗ[ZMod p] U) - 1) (f j)) := by
      calc ((z : U →ₗ[ZMod p] U) - 1) v
          = ((z : U →ₗ[ZMod p] U) - 1) (∑ j, f.repr v j • f j) := by
              rw [f.sum_repr]
        _ = ∑ j, f.repr v j • (((z : U →ₗ[ZMod p] U) - 1) (f j)) := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
        _ = ∑ j, f.coord j v • (((z : U →ₗ[ZMod p] U) - 1) (f j)) := by
              exact Finset.sum_congr rfl fun j _ => by rw [Module.Basis.coord_apply]
    rw [hsum]
    apply Submodule.sum_mem
    intro j _
    rw [hzj j]
    by_cases hj : j ∈ I
    · rw [if_pos hj]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_image_of_mem f (Finset.mem_coe.mpr hj))))
    · rw [if_neg hj, zero_smul, smul_zero]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro w ⟨j, hj, rfl⟩
    rw [Finset.mem_coe] at hj
    refine ⟨(-(2 : ZMod p)⁻¹) • f j, ?_⟩
    rw [map_smul, hzj j, if_pos hj, smul_smul]
    rw [show (-(2 : ZMod p)⁻¹) * (-2) = 1 by
      rw [neg_mul, mul_neg, neg_neg, inv_mul_cancel₀ h2]]
    rw [one_smul]

theorem isRefl_of_toMatrix_eq_diagSignMat (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {t : U ≃ₗ[ZMod p] U} {i : Fin n}
    (ht : LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) = diagSignMat i) : IsRefl p t := by
  constructor
  · refine eq_of_toMatrix_eq f ?_
    rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, ht,
      show ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id from rfl,
      LinearMap.toMatrix_id]
    ext l m
    simp only [diagSignMat, Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
    by_cases hl : l = m
    · subst hl
      by_cases hli : l = i <;> simp [hli]
    · simp [hl]
  · have hmoved : HardMathSupport.Kantor79.movedSpace t =
        Submodule.span (ZMod p) (f '' ↑({i} : Finset (Fin n))) :=
      movedSpace_of_toMatrix_eq_diagonal hp f ({i} : Finset (Fin n))
        (by simpa [diagSignMat] using ht)
    change Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1
    rw [hmoved, Finset.coe_singleton, Set.image_singleton,
      finrank_span_singleton (f.ne_zero i)]

private theorem diagonal_mul_self_eq_one {K : Type} [Field K] {n : ℕ} {d : Fin n → K}
    (hd : ∀ i, d i * d i = 1) :
    Matrix.diagonal d * Matrix.diagonal d = (1 : Matrix (Fin n) (Fin n) K) := by
  ext l m
  rw [Matrix.diagonal_mul_diagonal, Matrix.one_apply]
  simp only [Matrix.diagonal_apply]
  by_cases hl : l = m
  · subst hl; simp [hd l]
  · simp [hl]

private theorem diagonal_mul_diagonal_comm {K : Type} [Field K] {n : ℕ} (d e : Fin n → K) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  ext l m
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp only [Matrix.diagonal_apply]
  by_cases hl : l = m
  · subst hl; ring_nf
  · simp [hl]

private theorem diagonal_involutions_comm {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {I : Finset (Fin n)} {i₁ iτ : Fin n}
    {h₁ z τ : U ≃ₗ[ZMod p] U}
    (hz : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) =
      Matrix.diagonal fun i => if i ∈ I then -1 else 1)
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat i₁)
    (hτ : LinearMap.toMatrix f f (τ : U →ₗ[ZMod p] U) = diagSignMat iτ) :
    z * z = 1 ∧ h₁ * z = z * h₁ ∧ τ * z = z * τ := by
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_toMatrix_eq f ?_
    rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hz,
      show ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id from rfl, LinearMap.toMatrix_id]
    exact diagonal_mul_self_eq_one fun i => by by_cases hi : i ∈ I <;> simp [hi]
  · refine eq_of_toMatrix_eq f ?_
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hh₁, hz, diagSignMat]
    exact diagonal_mul_diagonal_comm (K := ZMod p) (n := n)
      (fun i => if i = i₁ then -1 else 1) (fun i => if i ∈ I then -1 else 1)
  · refine eq_of_toMatrix_eq f ?_
    simp only [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hτ, hz, diagSignMat]
    exact diagonal_mul_diagonal_comm (K := ZMod p) (n := n)
      (fun i => if i = iτ then -1 else 1) (fun i => if i ∈ I then -1 else 1)

theorem primFrameData_of_diagonal (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} {h₁ z τ : U ≃ₗ[ZMod p] U} (I : Finset (Fin n))
    {i₁ iτ : Fin n} (hi₁ : i₁ ∈ I) (hiτ : iτ ∉ I) (hn : I.card + 2 = n)
    (hz : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) =
      Matrix.diagonal fun i => if i ∈ I then -1 else 1)
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat i₁)
    (hτ : LinearMap.toMatrix f f (τ : U →ₗ[ZMod p] U) = diagSignMat iτ)
    (hzG : z ∈ G) (hh₁G : h₁ ∈ G) (hτG : ∃ g ∈ G, τ = g * h₁ * g⁻¹)
    (hfix : ∀ x ∈ G, IsRefl p x →
      HardMathSupport.Kantor79.movedSpace x ≤ Submodule.span (ZMod p) (f '' ↑I) →
      ∃ g ∈ G, HardMathSupport.Kantor79.movedSpace (g * h₁ * g⁻¹) ≤
        Submodule.span (ZMod p) (f '' ↑I) ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1)) :
    PrimFrameData p G h₁ z τ := by
  have hmz := movedSpace_of_toMatrix_eq_diagonal hp f I hz
  have h1moved := movedSpace_of_toMatrix_eq_diagonal hp f ({i₁} : Finset (Fin n))
    (by simpa [diagSignMat] using hh₁)
  have htmoved := movedSpace_of_toMatrix_eq_diagonal hp f ({iτ} : Finset (Fin n))
    (by simpa [diagSignMat] using hτ)
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace z) + 2 =
      Module.finrank (ZMod p) U := by
    rw [hmz, finrank_span_basis_image, Module.finrank_eq_card_basis f, Fintype.card_fin]
    exact hn
  obtain ⟨hzz, h1z, hz1⟩ := diagonal_involutions_comm f hz hh₁ hτ
  have hh1mz : HardMathSupport.Kantor79.movedSpace h₁ ≤
      HardMathSupport.Kantor79.movedSpace z := by
    rw [h1moved, hmz]
    apply Submodule.span_mono
    intro w hw
    obtain ⟨j, hj, rfl⟩ := hw
    rw [Finset.mem_coe, Finset.mem_singleton] at hj
    exact Set.mem_image_of_mem f (by subst hj; exact Finset.mem_coe.mpr hi₁)
  have hτG' : τ ∈ G := by
    obtain ⟨g, hg, rfl⟩ := hτG
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh₁G) (Subgroup.inv_mem _ hg)
  have hnotle : ¬ HardMathSupport.Kantor79.movedSpace τ ≤
      HardMathSupport.Kantor79.movedSpace z := by
    intro hle
    have hmem : f iτ ∈ HardMathSupport.Kantor79.movedSpace τ := by
      rw [htmoved]
      exact Submodule.subset_span (Set.mem_image_of_mem f (by simp))
    have := hle hmem
    rw [hmz] at this
    exact hiτ (Finset.mem_coe.mp ((Module.Basis.self_mem_span_image f).mp this))
  refine ⟨hzG, hzz, hfin, hh₁G, isRefl_of_toMatrix_eq_diagSignMat hp f hh₁,
    h1z, hh1mz, ⟨hτG', isRefl_of_toMatrix_eq_diagSignMat hp f hτ, hz1, hnotle⟩, hτG, ?_⟩
  intro x hxG hxr hxle
  rw [hmz] at hxle
  obtain ⟨g, hg, hgle⟩ := hfix x hxG hxr hxle
  exact ⟨g, hg, by rwa [hmz]⟩

theorem oneClass_of_forall_conj {G : Subgroup (U ≃ₗ[ZMod p] U)} {a₀ : U ≃ₗ[ZMod p] U}
    (hcl : ∀ x ∈ G, IsRefl p x → ∃ g ∈ G, x = g * a₀ * g⁻¹) : OneClass p G := by
  intro x hxG y hyG hxr hyr
  obtain ⟨g₁, hg₁, hx₁⟩ := hcl x hxG hxr
  obtain ⟨g₂, hg₂, hy₂⟩ := hcl y hyG hyr
  refine ⟨g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
  rw [hy₂, hx₁]
  group

theorem dMax_of_forall_conj {G : Subgroup (U ≃ₗ[ZMod p] U)} {a₀ : U ≃ₗ[ZMod p] U}
    (ha₀ : a₀ ∈ G) (ha₀r : IsRefl p a₀) (hcl : ∀ x ∈ G, IsRefl p x → ∃ g ∈ G, x = g * a₀ * g⁻¹)
    {d : ℕ} (hle : ∀ y ∈ G, IsRefl p y → orderOf (a₀ * y) ≤ d)
    (hex : ∃ y ∈ G, IsRefl p y ∧ orderOf (a₀ * y) = d) : DMax p G d := by
  constructor
  · intro x hxG y hyG hxr hyr
    obtain ⟨g, hg, hx_eq⟩ := hcl x hxG hxr
    have hyr' : IsRefl p (g⁻¹ * y * g) := IsRefl.conj hyr g⁻¹
    have horder : orderOf (x * y) = orderOf (a₀ * (g⁻¹ * y * g)) := by
      have hconj : x * y = g * (a₀ * (g⁻¹ * y * g)) * g⁻¹ := by
        rw [hx_eq]; group
      rw [hconj]
      exact (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm
    rw [horder]
    exact hle (g⁻¹ * y * g)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hyG) hg) hyr'
  · obtain ⟨y, hyG, hyr, hyord⟩ := hex
    exact ⟨a₀, ha₀, y, hyG, ha₀r, hyr, hyord⟩

private theorem conj_mem_closure_conj {g₀ a₀ b' g' : U ≃ₗ[ZMod p] U}
    (hg' : g' ∈ Subgroup.closure {a₀, b'}) :
    g₀ * g' * g₀⁻¹ ∈ Subgroup.closure {g₀ * a₀ * g₀⁻¹, g₀ * b' * g₀⁻¹} := by
  have key : ∀ x ∈ Subgroup.closure {a₀, b'},
      g₀ * x * g₀⁻¹ ∈ Subgroup.closure {g₀ * a₀ * g₀⁻¹, g₀ * b' * g₀⁻¹} := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => g₀ * x * g₀⁻¹ ∈
        Subgroup.closure {g₀ * a₀ * g₀⁻¹, g₀ * b' * g₀⁻¹}) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    · simp
    · intro x y _ _ ihx ihy
      rw [show g₀ * (x * y) * g₀⁻¹ = (g₀ * x * g₀⁻¹) * (g₀ * y * g₀⁻¹) from by group]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x _ ih
      rw [show g₀ * x⁻¹ * g₀⁻¹ = (g₀ * x * g₀⁻¹)⁻¹ from by group]
      exact Subgroup.inv_mem _ ih
  exact key g' hg'

theorem exists_conj_commute_of_forall_conj {G : Subgroup (U ≃ₗ[ZMod p] U)}
    {a₀ : U ≃ₗ[ZMod p] U} (hcl : ∀ x ∈ G, IsRefl p x → ∃ g ∈ G, x = g * a₀ * g⁻¹)
    (h₀ : ∀ b ∈ G, ∀ c ∈ G, IsRefl p b → IsRefl p c → orderOf (a₀ * b) = 5 →
      ∃ g ∈ Subgroup.closure {a₀, b}, g * c * g⁻¹ * a₀ = a₀ * (g * c * g⁻¹)) :
    ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, IsRefl p a → IsRefl p b → IsRefl p c → orderOf (a * b) = 5 →
      ∃ g ∈ Subgroup.closure {a, b}, g * c * g⁻¹ * a = a * (g * c * g⁻¹) := by
  intro a haG b hbG c hcG har hbr hcr hab
  obtain ⟨g₀, hg₀G, ha_eq⟩ := hcl a haG har
  let b' : U ≃ₗ[ZMod p] U := g₀⁻¹ * b * g₀
  let c' : U ≃ₗ[ZMod p] U := g₀⁻¹ * c * g₀
  have hb'G : b' ∈ G := Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀G) hbG) hg₀G
  have hc'G : c' ∈ G := Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀G) hcG) hg₀G
  have hb'r : IsRefl p b' := IsRefl.conj hbr g₀⁻¹
  have hc'r : IsRefl p c' := IsRefl.conj hcr g₀⁻¹
  have horder : orderOf (a₀ * b') = 5 := by
    have hconj : g₀ * (a₀ * b') * g₀⁻¹ = a * b := by
      rw [ha_eq]; simp only [b']; group
    rw [← hab, ← hconj]
    exact SemiconjBy.orderOf_eq g₀ (by unfold SemiconjBy; group)
  obtain ⟨g', hg'clos, hg'comm⟩ := h₀ b' hb'G c' hc'G hb'r hc'r horder
  let g : U ≃ₗ[ZMod p] U := g₀ * g' * g₀⁻¹
  have hg_clos : g ∈ Subgroup.closure {a, b} := by
    have h1 : g₀ * a₀ * g₀⁻¹ = a := ha_eq.symm
    have h2 : g₀ * b' * g₀⁻¹ = b := by simp only [b']; group
    rw [← h1, ← h2]
    exact conj_mem_closure_conj (g₀ := g₀) (a₀ := a₀) (b' := b') (g' := g') hg'clos
  have hcomm : g * c * g⁻¹ * a = a * (g * c * g⁻¹) := by
    have hgc : g * c * g⁻¹ = g₀ * (g' * c' * g'⁻¹) * g₀⁻¹ := by
      simp only [g, c']; group
    rw [hgc, ha_eq]
    have hd1 : (g₀ * (g' * c' * g'⁻¹) * g₀⁻¹) * (g₀ * a₀ * g₀⁻¹) =
        g₀ * ((g' * c' * g'⁻¹) * a₀) * g₀⁻¹ := by group
    have hd2 : (g₀ * a₀ * g₀⁻¹) * (g₀ * (g' * c' * g'⁻¹) * g₀⁻¹) =
        g₀ * (a₀ * (g' * c' * g'⁻¹)) * g₀⁻¹ := by group
    rw [hd1, hd2, hg'comm]
  exact ⟨g, hg_clos, hcomm⟩

end CFSG.StandardType.ZS.PrimModel

end
