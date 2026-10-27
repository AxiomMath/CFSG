module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin

open Module

namespace SteinbergBQ.BinaryPlanes

theorem matrix_involution_eq : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * A = 1 → B * B = 1 →
    A * B = B * A → A ≠ 1 → B ≠ 1 → A = B := by
  decide +kernel

theorem matrix_involution_fixed : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A * A = 1 → A ≠ 1 →
    (Finset.univ.filter fun v : Fin 2 → ZMod 2 => A.mulVec v = v).card ≤ 2 := by
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem involution_eq (hV : finrank (ZMod 2) V = 2) {s t : V →ₗ[ZMod 2] V} (hs : s * s = 1)
    (ht : t * t = 1) (hst : s * t = t * s) (hs1 : s ≠ 1) (ht1 : t ≠ 1) : s = t := by
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  let b : Basis (Fin 2) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hV
  let e := LinearMap.toMatrixAlgEquiv b
  apply e.injective
  refine matrix_involution_eq (e s) (e t) ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, hs, map_one]
  · rw [← map_mul, ht, map_one]
  · rw [← map_mul, ← map_mul, hst]
  · rw [Ne, ← map_one e, e.injective.eq_iff]
    exact hs1
  · rw [Ne, ← map_one e, e.injective.eq_iff]
    exact ht1

theorem card_fixed_le (hV : finrank (ZMod 2) V = 2) {t : V →ₗ[ZMod 2] V} (ht : t * t = 1)
    (ht1 : t ≠ 1) : Nat.card {y : V // t y = y} ≤ 2 := by
  classical
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  let b : Basis (Fin 2) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hV
  let e := LinearMap.toMatrixAlgEquiv b
  have h1 := matrix_involution_fixed (e t) (by rw [← map_mul, ht, map_one])
    (by rw [Ne, ← map_one e, e.injective.eq_iff]; exact ht1)
  have hiff : ∀ y : V, t y = y ↔ (e t).mulVec ⇑(b.repr y) = ⇑(b.repr y) := by
    intro y
    rw [show (e t).mulVec ⇑(b.repr y) = ⇑(b.repr (t y)) from
      LinearMap.toMatrix_mulVec_repr b b t y, DFunLike.coe_fn_eq, b.repr.injective.eq_iff]
  let f : {y : V // t y = y} → (Finset.univ.filter fun v : Fin 2 → ZMod 2 =>
      (e t).mulVec v = v) := fun y =>
    ⟨⇑(b.repr y), Finset.mem_filter.2 ⟨Finset.mem_univ _, (hiff y).1 y.2⟩⟩
  have hf : Function.Injective f := fun y z h =>
    Subtype.ext (b.repr.injective (DFunLike.coe_injective (congrArg Subtype.val h)))
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ↥(Finset.univ.filter _)), Fintype.card_coe] at this
  exact this.trans h1

theorem card_mul_card_fixed_le [Finite V] (hV : finrank (ZMod 2) V = 2)
    (S : Set (V →ₗ[ZMod 2] V)) (hS : ∀ s ∈ S, s * s = 1)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    Nat.card S * Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 4 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hcardV : Nat.card V = 4 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), hV, ZMod.card]
    rfl
  by_cases h : ∃ t ∈ S, t ≠ 1
  · obtain ⟨t, htS, ht1⟩ := h
    have hS2 : Nat.card S ≤ 2 := by
      have hsub : S ⊆ ({1, t} : Set (V →ₗ[ZMod 2] V)) := by
        intro s hs
        by_cases hs1 : s = 1
        · exact Or.inl hs1
        · exact Or.inr (involution_eq hV (hS s hs) (hS t htS) (hcomm s hs t htS) hs1 ht1)
      calc Nat.card S ≤ Nat.card ({1, t} : Set (V →ₗ[ZMod 2] V)) :=
            Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
            rw [Nat.card_coe_set_eq]
            exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have hF2 : Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 2 := by
      refine le_trans ?_ (card_fixed_le hV (hS t htS) ht1)
      refine Nat.card_le_card_of_injective
        (fun y : {y : V // ∀ s ∈ S, s y = y} => (⟨y.1, y.2 t htS⟩ : {y : V // t y = y}))
        fun y z h => Subtype.ext ?_
      exact congrArg (fun u : {y : V // t y = y} => (u : V)) h
    calc Nat.card S * Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 2 * 2 :=
          Nat.mul_le_mul hS2 hF2
      _ = 4 := rfl
  · push Not at h
    have hS1 : Nat.card S ≤ 1 := by
      calc Nat.card S ≤ Nat.card ({1} : Set (V →ₗ[ZMod 2] V)) :=
            Nat.card_mono (Set.toFinite _) fun s hs => h s hs
        _ = 1 := by rw [Nat.card_coe_set_eq, Set.ncard_singleton]
    have hF4 : Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 4 := by
      rw [← hcardV]
      exact Nat.card_le_card_of_injective (fun y => y.1) Subtype.val_injective
    calc Nat.card S * Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 1 * 4 := Nat.mul_le_mul hS1 hF4
      _ = 4 := rfl

theorem four_mul_le_four_pow {m : ℕ} (hm : 1 ≤ m) : 4 * m ≤ 4 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · norm_num
    · have := ih hm'
      rw [pow_succ]
      omega

section Planes

variable {ι : Type*} [DecidableEq ι] {I : ι → Type*} [∀ i, AddCommGroup (I i)]
  [∀ i, Module (ZMod 2) (I i)]

variable (I) in
abbrev plane (i : ι) : Submodule (ZMod 2) ((j : ι) → I j) :=
  LinearMap.range (LinearMap.single (ZMod 2) I i)

theorem mem_plane {i : ι} {w : (j : ι) → I j} : w ∈ plane I i ↔ ∀ j, j ≠ i → w j = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ j hj
    exact Pi.single_eq_of_ne hj x
  · intro h
    refine ⟨w i, funext fun j => ?_⟩
    by_cases hj : j = i
    · rw [hj]
      exact Pi.single_eq_same i (w i)
    · rw [h j hj]
      exact Pi.single_eq_of_ne hj (w i)

theorem single_mem_plane (i : ι) (x : I i) : Pi.single i x ∈ plane I i := ⟨x, rfl⟩

theorem eq_single_of_mem_plane {i : ι} {w : (j : ι) → I j} (hw : w ∈ plane I i) :
    w = Pi.single i (w i) := by
  funext j
  by_cases hj : j = i
  · rw [hj, Pi.single_eq_same]
  · rw [mem_plane.1 hw j hj, Pi.single_eq_of_ne hj]

theorem plane_injective (hI : ∀ i, Nontrivial (I i)) {i j : ι}
    (h : plane I i = plane I j) : i = j := by
  by_contra hij
  obtain ⟨x, hx⟩ := exists_ne (0 : I i)
  have h1 : Pi.single i x ∈ plane I j := h ▸ single_mem_plane i x
  have h2 := mem_plane.1 h1 i hij
  rw [Pi.single_eq_same] at h2
  exact hx h2

theorem apply_eq_apply_single [Fintype ι] (f : ((j : ι) → I j) →ₗ[ZMod 2] ((j : ι) → I j))
    (τ : ι → ι)
    (hτ : Function.Injective τ) (hf : ∀ j x, f (Pi.single j x) ∈ plane I (τ j))
    (w : (j : ι) → I j) (i : ι) : f w (τ i) = f (Pi.single i (w i)) (τ i) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
  exact mem_plane.1 (hf j (w j)) (τ i) (hτ.ne (Ne.symm hji))

theorem linearMap_ext_single [Finite ι] {f g : ((j : ι) → I j) →ₗ[ZMod 2] ((j : ι) → I j)}
    (h : ∀ i (x : I i), f (Pi.single i x) = g (Pi.single i x)) : f = g :=
  LinearMap.pi_ext h

end Planes

section Bound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Type*} [∀ i, AddCommGroup (I i)]
  [∀ i, Module (ZMod 2) (I i)]

theorem card_mul_card_fixed_le_card (hdim : ∀ i, finrank (ZMod 2) (I i) = 2)
    (E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) ((i : ι) → I i)))
    [IsElementaryAbelian 2 E]
    (hperm : ∀ e ∈ E, ∀ i, ∃ j, (plane I i).map
      ((e : LinearMap.GeneralLinearGroup (ZMod 2) ((i : ι) → I i)) :
        ((i : ι) → I i) →ₗ[ZMod 2] ((i : ι) → I i)) = plane I j)
    (C : Submodule (ZMod 2) ((i : ι) → I i))
    (hC : ∀ w, w ∈ C ↔ ∀ e ∈ E, ((e : LinearMap.GeneralLinearGroup (ZMod 2) ((i : ι) → I i)) :
        ((i : ι) → I i) →ₗ[ZMod 2] ((i : ι) → I i)) w = w) :
    Nat.card E * Nat.card C ≤ Nat.card ((i : ι) → I i) := by
  classical
  let act : E → (((i : ι) → I i) →ₗ[ZMod 2] ((i : ι) → I i)) := fun e =>
    ((e : LinearMap.GeneralLinearGroup (ZMod 2) ((i : ι) → I i)) :
      ((i : ι) → I i) →ₗ[ZMod 2] ((i : ι) → I i))
  have act_mul : ∀ (e f : E) (w : (i : ι) → I i), act (e * f) w = act e (act f w) :=
    fun _ _ _ => rfl
  have act_ext : ∀ e f : E, act e = act f → e = f := fun e f h => Subtype.ext (Units.ext h)
  have hnt : ∀ i, Nontrivial (I i) := fun i =>
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hdim i]; norm_num)
  have hfd : ∀ i, Module.Finite (ZMod 2) (I i) := fun i =>
    Module.finite_of_finrank_pos (by rw [hdim i]; norm_num)
  have hfinI : ∀ i, Finite (I i) := fun i => Module.finite_of_finite (ZMod 2)
  have hsq : ∀ e : E, e * e = 1 := fun e => by
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E)
      (e : LinearMap.GeneralLinearGroup (ZMod 2) ((i : ι) → I i)) e.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h1, Subgroup.coe_one])
  have hcomm : ∀ e f : E, e * f = f * e := fun e f => Std.Commutative.comm e f
  choose σ hσ using fun (e : E) (i : ι) => hperm e e.2 i
  have hmem : ∀ (e : E) (i : ι) (x : I i), act e (Pi.single i x) ∈ plane I (σ e i) :=
    fun e i x => by
      rw [← hσ e i]
      exact Submodule.mem_map_of_mem (single_mem_plane i x)
  have σ_mul : ∀ (e f : E) (i : ι), σ (e * f) i = σ e (σ f i) := by
    intro e f i
    apply plane_injective hnt
    rw [← hσ (e * f) i, ← hσ e (σ f i), ← hσ f i, ← Submodule.map_comp]
    rfl
  have σ_one : ∀ i, σ 1 i = i := fun i => plane_injective hnt (by
    rw [← hσ 1 i]
    exact Submodule.map_id _)
  have σ_comm : ∀ (e f : E) (i : ι), σ e (σ f i) = σ f (σ e i) := fun e f i => by
    rw [← σ_mul, ← σ_mul, hcomm]
  have σ_inj : ∀ e : E, Function.Injective (σ e) := fun e i j h => by
    have h1 := congrArg (σ e⁻¹) h
    rwa [← σ_mul, ← σ_mul, inv_mul_cancel, σ_one, σ_one] at h1
  have hcoord : ∀ (e : E) (w : (i : ι) → I i) (i k : ι), σ e i = k →
      act e w k = act e (Pi.single i (w i)) k := by
    intro e w i k hk
    subst hk
    exact apply_eq_apply_single (act e) (σ e) (σ_inj e) (hmem e) w i
  let ψ : E →* Equiv.Perm ι :=
    { toFun := fun e => ⟨σ e, σ e⁻¹, fun i => by rw [← σ_mul, inv_mul_cancel, σ_one],
        fun i => by rw [← σ_mul, mul_inv_cancel, σ_one]⟩
      map_one' := Equiv.ext σ_one
      map_mul' := fun e f => Equiv.ext (σ_mul e f) }
  have hψ : ∀ (e : E) (i : ι), ψ e i = σ e i := fun _ _ => rfl
  have hker : ∀ g ∈ ψ.ker, ∀ i, σ g i = i := fun g hg i => by
    have h1 := congrArg (fun π : Equiv.Perm ι => π i) (MonoidHom.mem_ker.1 hg)
    exact h1
  have hfix : ∀ g ∈ ψ.ker, ∀ (i : ι) (x : I i),
      act g (Pi.single i x) = Pi.single i (act g (Pi.single i x) i) := fun g hg i x =>
    eq_single_of_mem_plane (by
      have h1 := hmem g i x
      rwa [hker g hg i] at h1)
  let r : Setoid ι :=
    { r := fun i j => ∃ e : E, σ e i = j
      iseqv := ⟨fun i => ⟨1, σ_one i⟩, fun ⟨e, he⟩ => ⟨e⁻¹, by
          rw [← he, ← σ_mul, inv_mul_cancel, σ_one]⟩,
        fun ⟨e, he⟩ ⟨f, hf⟩ => ⟨f * e, by rw [σ_mul, he, hf]⟩⟩ }
  have : Fintype (Quotient r) := @Quotient.fintype ι _ r (Classical.decRel _)
  have hout : ∀ i : ι, ∃ e : E, σ e (Quotient.out (Quotient.mk r i)) = i := fun i =>
    Quotient.mk_out (s := r) i
  have hmk : ∀ (e : E) (q : Quotient r), Quotient.mk r (σ e (Quotient.out q)) = q := fun e q =>
    (Quotient.sound (s := r) ⟨e, rfl⟩).symm.trans (Quotient.out_eq q)
  have hB : Nat.card ψ.range ≤ ∏ q : Quotient r, Nat.card {i // Quotient.mk r i = q} := by
    let Θ : ψ.range → (q : Quotient r) → {i // Quotient.mk r i = q} := fun π q =>
      ⟨π.1 (Quotient.out q), by
        obtain ⟨e, he⟩ := π.2
        rw [← he, hψ]
        exact hmk e q⟩
    have hΘ : Function.Injective Θ := by
      rintro ⟨π, e, rfl⟩ ⟨π', e', rfl⟩ h
      refine Subtype.ext (Equiv.ext fun i => ?_)
      obtain ⟨f, hf⟩ := hout i
      have h1 : σ e (Quotient.out (Quotient.mk r i)) = σ e' (Quotient.out (Quotient.mk r i)) :=
        congrArg (fun F => (F (Quotient.mk r i)).1) h
      change σ e i = σ e' i
      rw [← hf, σ_comm e f, σ_comm e' f, h1]
    calc Nat.card ψ.range ≤ Nat.card ((q : Quotient r) → {i // Quotient.mk r i = q}) :=
          Nat.card_le_card_of_injective Θ hΘ
      _ = _ := Nat.card_pi
  have hfinEnd : ∀ q : Quotient r,
      Finite (I (Quotient.out q) →ₗ[ZMod 2] I (Quotient.out q)) := fun q =>
    Finite.of_injective (fun f : I (Quotient.out q) →ₗ[ZMod 2] I (Quotient.out q) =>
      (f : I (Quotient.out q) → I (Quotient.out q))) DFunLike.coe_injective
  let res : E → (q : Quotient r) → (I (Quotient.out q) →ₗ[ZMod 2] I (Quotient.out q)) :=
    fun e q => (LinearMap.proj (Quotient.out q)) ∘ₗ act e ∘ₗ
      (LinearMap.single (ZMod 2) I (Quotient.out q))
  have hres : ∀ (e : E) (q : Quotient r) (x : I (Quotient.out q)),
      res e q x = act e (Pi.single (Quotient.out q) x) (Quotient.out q) := fun _ _ _ => rfl
  let S : (q : Quotient r) → Set (I (Quotient.out q) →ₗ[ZMod 2] I (Quotient.out q)) :=
    fun q => {s | ∃ g ∈ ψ.ker, res g q = s}
  have hres_mul : ∀ g ∈ ψ.ker, ∀ g' ∈ ψ.ker, ∀ q : Quotient r,
      res (g * g') q = res g q * res g' q := by
    intro g _ g' hg' q
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, hres, hres, hres, act_mul]
    conv_lhs => rw [hfix g' hg' (Quotient.out q) x]
  have hC' : Nat.card ψ.ker ≤ ∏ q : Quotient r, Nat.card (S q) := by
    let Θ : ψ.ker → (q : Quotient r) → S q := fun g q => ⟨res g q, g, g.2, rfl⟩
    have hΘ : Function.Injective Θ := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
      refine Subtype.ext (act_ext g g' (linearMap_ext_single fun i x => ?_))
      obtain ⟨f, hf⟩ := hout i
      set j := Quotient.out (Quotient.mk r i)
      have h1 : res g (Quotient.mk r i) = res g' (Quotient.mk r i) :=
        congrArg (fun F => ((F (Quotient.mk r i) : S (Quotient.mk r i)) :
          I j →ₗ[ZMod 2] I j)) h
      have hx : Pi.single i x ∈ (plane I j).map (act f) := by
        rw [hσ f j, hf]
        exact single_mem_plane i x
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.1 hx
      rw [eq_single_of_mem_plane hv] at hvx
      rw [← hvx, ← act_mul, ← act_mul, hcomm g f, hcomm g' f, act_mul, act_mul, hfix g hg,
        hfix g' hg']
      have h2 := LinearMap.congr_fun h1 (v j)
      rw [hres, hres] at h2
      rw [h2]
    calc Nat.card ψ.ker ≤ Nat.card ((q : Quotient r) → S q) :=
          Nat.card_le_card_of_injective Θ hΘ
      _ = _ := Nat.card_pi
  let F : (q : Quotient r) → Type _ := fun q => {y : I (Quotient.out q) // ∀ s ∈ S q, s y = y}
  have hD : Nat.card C ≤ ∏ q : Quotient r, Nat.card (F q) := by
    let Θ : C → (q : Quotient r) → F q := fun w q => ⟨w.1 (Quotient.out q), by
      rintro s ⟨g, hg, rfl⟩
      rw [hres, ← hcoord g w.1 _ _ (hker g hg _), (hC w.1).1 w.2 g g.2]⟩
    have hΘ : Function.Injective Θ := by
      rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
      refine Subtype.ext (funext fun i => ?_)
      obtain ⟨f, hf⟩ := hout i
      have h1 : w (Quotient.out (Quotient.mk r i)) = w' (Quotient.out (Quotient.mk r i)) :=
        congrArg (fun G => ((G (Quotient.mk r i) : F (Quotient.mk r i)) :
          I (Quotient.out (Quotient.mk r i)))) h
      change w i = w' i
      rw [← (hC w).1 hw f f.2, ← (hC w').1 hw' f f.2, hcoord f w _ i hf, hcoord f w' _ i hf, h1]
    calc Nat.card C ≤ Nat.card ((q : Quotient r) → F q) :=
          Nat.card_le_card_of_injective Θ hΘ
      _ = _ := Nat.card_pi
  have hE : ∀ q : Quotient r, Nat.card (S q) * Nat.card (F q) ≤ 4 := by
    intro q
    refine card_mul_card_fixed_le (hdim _) (S q) ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      rw [← hres_mul g hg g hg, hsq]
      refine LinearMap.ext fun x => ?_
      rw [hres, Module.End.one_apply]
      exact Pi.single_eq_same (Quotient.out q) x
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      rw [← hres_mul g hg g' hg', ← hres_mul g' hg' g hg, hcomm]
  have hW : Nat.card ((i : ι) → I i) =
      ∏ q : Quotient r, 4 ^ Nat.card {i // Quotient.mk r i = q} := by
    rw [Nat.card_pi, Finset.prod_pow_eq_pow_sum]
    have h4 : ∀ i, Nat.card (I i) = 4 := fun i => by
      have : Fintype (I i) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), hdim i, ZMod.card]
      rfl
    simp only [h4, Finset.prod_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk r)),
      Nat.card_sigma]
  have hcardE : Nat.card E = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hm1 : ∀ q : Quotient r, 1 ≤ Nat.card {i // Quotient.mk r i = q} := fun q =>
    Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨⟨Quotient.out q, Quotient.out_eq q⟩⟩,
      inferInstance⟩)
  calc Nat.card E * Nat.card C
      ≤ (∏ q : Quotient r, Nat.card {i // Quotient.mk r i = q}) *
          (∏ q : Quotient r, Nat.card (S q)) * ∏ q : Quotient r, Nat.card (F q) := by
        rw [hcardE]
        exact Nat.mul_le_mul (Nat.mul_le_mul hB hC') hD
    _ = ∏ q : Quotient r, (Nat.card {i // Quotient.mk r i = q} *
          (Nat.card (S q) * Nat.card (F q))) := by
        rw [mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ ≤ ∏ q : Quotient r, (4 * Nat.card {i // Quotient.mk r i = q}) := by
        refine Finset.prod_le_prod fun q _ => ?_
        rw [mul_comm 4]
        exact Nat.mul_le_mul_left _ (hE q)
    _ ≤ ∏ q : Quotient r, 4 ^ Nat.card {i // Quotient.mk r i = q} :=
        Finset.prod_le_prod fun q _ => four_mul_le_four_pow (hm1 q)
    _ = Nat.card ((i : ι) → I i) := hW.symm

end Bound

end SteinbergBQ.BinaryPlanes

open SteinbergBQ.BinaryPlanes

end CFSG.Quasithin
