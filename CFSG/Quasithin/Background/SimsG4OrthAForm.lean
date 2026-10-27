module

public import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Background.SimsG48

public section

namespace CFSG.Quasithin.SimsG4

namespace OrthA

open LinearMap (BilinForm)

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def centreSet (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) : Set V :=
  {r | Q r = 1 ∧ ∃ d ∈ transvSet G₀, ∀ x, d x = x + QuadraticMap.polar Q x r • r}

@[expose] def centreField (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) : Subfield F :=
  Subfield.closure {a | ∃ r ∈ centreSet Q G₀, ∃ s ∈ centreSet Q G₀, a = QuadraticMap.polar Q r s}

@[expose] def centreForm (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Submodule (centreField Q G₀) V :=
  Submodule.span (centreField Q G₀) (centreSet Q G₀)

theorem map_add_smul (Q : QuadraticForm F V) (v u : V) (a : F) :
    Q (v + a • u) = Q v + a * a * Q u + a * QuadraticMap.polar Q v u := by
  rw [QuadraticMap.map_add (⇑Q) v (a • u), QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
    smul_eq_mul, smul_eq_mul]

theorem exists_centre [Finite F] [CharP F 2] (B : BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {G₀ : Subgroup (V ≃ₗ[F] V)} (hSp : G₀ ≤ spGroup B)
    {Q : QuadraticForm F V} (hQB : ∀ x y, QuadraticMap.polar Q x y = B x y)
    (hQ : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) {d : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) :
    ∃ r ∈ centreSet Q G₀, ∀ x, d x = x + QuadraticMap.polar Q x r • r := by
  obtain ⟨u, hu0, c, hc0, hdu, -⟩ := SimsG45.exists_transv_form B halt hnd d (hSp hd.1) hd.2.1
  obtain ⟨v₀, hv₀⟩ := SimsG45.exists_pair_eq_one B halt hnd hu0
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hcQ : c * Q u = 1 := by
    have h1 := hQ d hd.1 v₀
    rw [hdu v₀, hv₀, mul_one, map_add_smul, hQB, hv₀] at h1
    have h3 : c * (c * Q u + 1) = 0 := by linear_combination h1
    have h4 := (mul_eq_zero.mp h3).resolve_left hc0
    linear_combination h4 - h2
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' c
  have hform : ∀ x, d x = x + QuadraticMap.polar Q x (s • u) • (s • u) := fun x => by
    rw [hdu x, QuadraticMap.polar_smul_right, hQB, smul_eq_mul, smul_smul, hs]
    congr 2
    ring
  exact ⟨s • u, ⟨by rw [QuadraticMap.map_smul, smul_eq_mul, ← hs, hcQ], d, hd, hform⟩, hform⟩

theorem polar_apply_apply {Q : QuadraticForm F V} {g : V ≃ₗ[F] V} (hg : ∀ x, Q (g x) = Q x)
    (x y : V) : QuadraticMap.polar Q (g x) (g y) = QuadraticMap.polar Q x y := by
  show Q (g x + g y) - Q (g x) - Q (g y) = Q (x + y) - Q x - Q y
  rw [← map_add, hg, hg, hg]

theorem apply_mem_centreSet {Q : QuadraticForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}
    (hQ : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) {g : V ≃ₗ[F] V} (hg : g ∈ G₀) {r : V}
    (hr : r ∈ centreSet Q G₀) : g r ∈ centreSet Q G₀ := by
  obtain ⟨hQr, d, hd, hdr⟩ := hr
  refine ⟨by rw [hQ g hg, hQr], g * d * g⁻¹, conj_mem_transvSet hg hd, fun x => ?_⟩
  have e := polar_apply_apply (hQ g hg) (g⁻¹ x) r
  rw [mul_inv_apply] at e
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdr, map_add, map_smul, mul_inv_apply, e]

theorem isIrredOnV_of_le {H G : Subgroup (V ≃ₗ[F] V)} (hHG : H ≤ G) (hH : IsIrredOnV H) :
    IsIrredOnV G :=
  fun W hW => hH W fun g hg => hW g (hHG hg)

theorem span_centreSet {Q : QuadraticForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}
    (hQ : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) (hirr : IsIrredOnV G₀)
    (hne : (centreSet Q G₀).Nonempty) : Submodule.span F (centreSet Q G₀) = ⊤ := by
  have hinv : ∀ g ∈ G₀, ∀ w ∈ Submodule.span F (centreSet Q G₀),
      g w ∈ Submodule.span F (centreSet Q G₀) := by
    intro g hg w hw
    have hle : Submodule.span F (centreSet Q G₀) ≤
        (Submodule.span F (centreSet Q G₀)).comap (g : V →ₗ[F] V) :=
      Submodule.span_le.mpr fun r hr => Submodule.subset_span (apply_mem_centreSet hQ hg hr)
    exact hle hw
  rcases hirr _ hinv with h | h
  · obtain ⟨r, hr⟩ := hne
    have hr0 : r ∈ Submodule.span F (centreSet Q G₀) := Submodule.subset_span hr
    rw [h, Submodule.mem_bot] at hr0
    have h1 := hr.1
    rw [hr0, QuadraticMap.map_zero] at h1
    exact absurd h1 zero_ne_one
  · exact h

theorem polar_mem_centreField {Q : QuadraticForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)} {x y : V}
    (hx : x ∈ centreForm Q G₀) (hy : y ∈ centreForm Q G₀) :
    QuadraticMap.polar Q x y ∈ centreField Q G₀ := by
  induction hx using Submodule.span_induction with
  | mem r hr =>
    induction hy using Submodule.span_induction with
    | mem s hs => exact Subfield.subset_closure ⟨r, hr, s, hs, rfl⟩
    | zero => rw [QuadraticMap.polar_zero_right]; exact zero_mem _
    | add y y' _ _ h h' => rw [QuadraticMap.polar_add_right]; exact add_mem h h'
    | smul a y _ h =>
      rw [Subfield.smul_def, QuadraticMap.polar_smul_right, smul_eq_mul]
      exact mul_mem a.2 h
  | zero => rw [QuadraticMap.polar_zero_left]; exact zero_mem _
  | add x x' _ _ h h' => rw [QuadraticMap.polar_add_left]; exact add_mem h h'
  | smul a x _ h =>
    rw [Subfield.smul_def, QuadraticMap.polar_smul_left, smul_eq_mul]
    exact mul_mem a.2 h

theorem apply_mem_centreField {Q : QuadraticForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)} {x : V}
    (hx : x ∈ centreForm Q G₀) : Q x ∈ centreField Q G₀ := by
  induction hx using Submodule.span_induction with
  | mem r hr => rw [hr.1]; exact one_mem _
  | zero => rw [QuadraticMap.map_zero]; exact zero_mem _
  | add x y hx hy h h' =>
    rw [QuadraticMap.map_add (⇑Q) x y]
    exact add_mem (add_mem h h') (polar_mem_centreField hx hy)
  | smul a x _ h =>
    rw [Subfield.smul_def, QuadraticMap.map_smul, smul_eq_mul]
    exact mul_mem (mul_mem a.2 a.2) h

theorem apply_mem_centreForm {Q : QuadraticForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}
    (hQ : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) {g : V ≃ₗ[F] V} (hg : g ∈ G₀) {x : V}
    (hx : x ∈ centreForm Q G₀) : g x ∈ centreForm Q G₀ := by
  induction hx using Submodule.span_induction with
  | mem r hr => exact Submodule.subset_span (apply_mem_centreSet hQ hg hr)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul a x _ h =>
    rw [Subfield.smul_def, map_smul, ← Subfield.smul_def]
    exact Submodule.smul_mem _ a h

theorem span_centreForm {Q : QuadraticForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}
    (h : Submodule.span F (centreSet Q G₀) = ⊤) :
    Submodule.span F (centreForm Q G₀ : Set V) = ⊤ := by
  rw [centreForm, Submodule.span_span_of_tower, h]

section Form

variable {F₀ : Subfield F} {I : Submodule F₀ V} {B : BilinForm F V}

theorem linearIndependent_of_form (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀) (hspan : Submodule.span F (I : Set V) = ⊤)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ i, v i ∈ I) (hli : LinearIndependent F₀ v) :
    LinearIndependent F v :=
  G48.linearIndependent_of_subfield F₀ (I := I.toAddSubgroup) B
    (fun c hc x hx => I.smul_mem ⟨c, hc⟩ hx) hval
    (fun _ _ h => G48.eq_zero_of_forall_left B halt hnd (I := I.toAddSubgroup) hspan h) v hv hli

theorem exists_ne_zero_of_form (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hspan : Submodule.span F (I : Set V) = ⊤) {x : V} (hx0 : x ≠ 0) : ∃ y ∈ I, B x y ≠ 0 :=
  G48.exists_ne_zero_of_span B hnd (I := I.toAddSubgroup) hspan hx0

theorem finrank_span_of_le [Finite V] (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀)
    (hspan : Submodule.span F (I : Set V) = ⊤) {A : Submodule F₀ V} (hA : A ≤ I) :
    Module.finrank F (Submodule.span F (A : Set V)) = Module.finrank F₀ A := by
  let b := Module.finBasis F₀ A
  have hli : LinearIndependent F₀ (fun i => (b i : V)) :=
    b.linearIndependent.map' A.subtype A.ker_subtype
  have hliF := linearIndependent_of_form halt hnd hval hspan _ (fun i => hA (b i).2) hli
  have hrange : Submodule.span F₀ (Set.range fun i => (b i : V)) = A := by
    have e : (Set.range fun i => (b i : V)) = A.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have e : Submodule.span F (A : Set V) = Submodule.span F (Set.range fun i => (b i : V)) := by
    conv_lhs => rw [← hrange]
    exact Submodule.span_span_of_tower _ _ _
  rw [e, finrank_span_eq_card hliF, Fintype.card_fin]

variable (V F₀) in
theorem gc_span :
    GaloisConnection (fun A : Submodule F₀ V => Submodule.span F (A : Set V))
      (fun U : Submodule F V => U.restrictScalars F₀) :=
  fun _ _ => Submodule.span_le

theorem span_sup (A C : Submodule F₀ V) :
    Submodule.span F ((A ⊔ C : Submodule F₀ V) : Set V) =
      Submodule.span F (A : Set V) ⊔ Submodule.span F (C : Set V) :=
  (gc_span V F₀).l_sup

theorem span_iSup {ι : Sort*} (A : ι → Submodule F₀ V) :
    Submodule.span F ((⨆ i, A i : Submodule F₀ V) : Set V) =
      ⨆ i, Submodule.span F (A i : Set V) :=
  (gc_span V F₀).l_iSup

theorem disjoint_span_of_le [Finite V] (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀)
    (hspan : Submodule.span F (I : Set V) = ⊤) {A C : Submodule F₀ V} (hA : A ≤ I) (hC : C ≤ I)
    (hAC : Disjoint A C) :
    Disjoint (Submodule.span F (A : Set V)) (Submodule.span F (C : Set V)) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (A : Set V))
    (Submodule.span F (C : Set V))
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq A C
  rw [← span_sup, finrank_span_of_le halt hnd hval hspan (sup_le hA hC),
    finrank_span_of_le halt hnd hval hspan hA, finrank_span_of_le halt hnd hval hspan hC] at e1
  rw [hAC.eq_bot, finrank_bot] at e2
  rw [disjoint_iff, ← Submodule.finrank_eq_zero]
  omega

theorem finrank_form [Finite V] (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀) (hspan : Submodule.span F (I : Set V) = ⊤) :
    Module.finrank F₀ I = Module.finrank F V := by
  rw [← finrank_span_of_le halt hnd hval hspan le_rfl, hspan, finrank_top]

theorem exists_sympBasis_form [CharP F 2] (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀)
    (hspan : Submodule.span F (I : Set V) = ⊤) (hdim : Module.finrank F V = 4) :
    ∃ b : Module.Basis (Fin 4) F V, IsSympBasis B b ∧ ∀ i, b i ∈ I := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F V)
  have hI0 : I.toAddSubgroup ≠ ⊥ := by
    intro h
    have hI : (I : Set V) ⊆ {0} := fun x hx => by
      have hx' : x ∈ I.toAddSubgroup := hx
      rw [h] at hx'
      exact hx'
    have h0 : Submodule.span F (I : Set V) ≤ ⊥ := by
      rw [Submodule.span_le]
      intro x hx
      exact hI hx
    rw [hspan] at h0
    exact bot_ne_top (le_bot_iff.mp h0).symm
  obtain ⟨e, heI, hgram⟩ := G48.exists_antidiag_family B halt (F₀ := F₀) (I := I.toAddSubgroup)
    (fun c hc x hx => I.smul_mem ⟨c, hc⟩ hx) hval
    (fun _ _ hx0 => G48.exists_ne_zero_of_span B hnd (I := I.toAddSubgroup) hspan hx0) hI0
    (G48.exists_not_mem_span_pair hdim (I := I.toAddSubgroup) hspan)
  have hli := G48.linearIndependent_antidiag B hgram
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb : ⇑b = e := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  exact ⟨b, fun i j => by rw [hb]; exact hgram i j, fun i => by rw [hb]; exact heI i⟩

theorem mem_iff_repr_mem (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀) (b : Module.Basis (Fin 4) F V)
    (hb : IsSympBasis B b) (hbI : ∀ i, b i ∈ I) (x : V) : x ∈ I ↔ ∀ i, b.repr x i ∈ F₀ := by
  constructor
  · intro hx i
    rw [G48.repr_antidiag B b hb x i]
    exact hval _ (hbI _) _ hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => I.smul_mem ⟨b.repr x i, h i⟩ (hbI i)

theorem mem_subfieldSpOf_iff (hval : ∀ x ∈ I, ∀ y ∈ I, B x y ∈ F₀)
    (b : Module.Basis (Fin 4) F V) (hb : IsSympBasis B b) (hbI : ∀ i, b i ∈ I)
    (g : V ≃ₗ[F] V) : g ∈ subfieldSpOf b F₀ ↔ ∀ x ∈ I, g x ∈ I := by
  constructor
  · intro hg x hx
    rw [mem_iff_repr_mem hval b hb hbI] at hx ⊢
    intro i
    have e := congrFun (LinearMap.toMatrix_mulVec_repr b b (g : V →ₗ[F] V) x) i
    simp only [LinearEquiv.coe_coe] at e
    rw [← e]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (hg i j) (hx j)
  · intro hg i j
    rw [LinearMap.toMatrix_apply]
    exact (mem_iff_repr_mem hval b hb hbI _).mp (hg _ (hbI j)) i

end Form

section Restriction

variable {F₀ : Subfield F} {I : Submodule F₀ V}

@[expose] def subForm (Q : QuadraticForm F V) (I : Submodule F₀ V) (hQI : ∀ x ∈ I, Q x ∈ F₀)
    (hPI : ∀ x ∈ I, ∀ y ∈ I, QuadraticMap.polar Q x y ∈ F₀) : QuadraticForm F₀ I where
  toFun x := ⟨Q x, hQI x x.2⟩
  toFun_smul a x := Subtype.ext (by
    simp only [Submodule.coe_smul, Subfield.smul_def, QuadraticMap.map_smul, smul_eq_mul,
      Subfield.coe_mul])
  exists_companion' := ⟨LinearMap.mk₂ F₀
      (fun x y => (⟨QuadraticMap.polar Q x y, hPI x x.2 y y.2⟩ : F₀))
      (fun x x' y => Subtype.ext (by
        simp only [Submodule.coe_add, QuadraticMap.polar_add_left, Subfield.coe_add]))
      (fun a x y => Subtype.ext (by
        simp only [Submodule.coe_smul, Subfield.smul_def, QuadraticMap.polar_smul_left,
          smul_eq_mul, Subfield.coe_mul]))
      (fun x y y' => Subtype.ext (by
        simp only [Submodule.coe_add, QuadraticMap.polar_add_right, Subfield.coe_add]))
      (fun a x y => Subtype.ext (by
        simp only [Submodule.coe_smul, Subfield.smul_def, QuadraticMap.polar_smul_right,
          smul_eq_mul, Subfield.coe_mul])),
    fun x y => Subtype.ext (by
      simp only [Submodule.coe_add, LinearMap.mk₂_apply, Subfield.coe_add]
      exact QuadraticMap.map_add (⇑Q) x y)⟩

theorem coe_subForm (Q : QuadraticForm F V) (hQI : ∀ x ∈ I, Q x ∈ F₀)
    (hPI : ∀ x ∈ I, ∀ y ∈ I, QuadraticMap.polar Q x y ∈ F₀) (x : I) :
    ((subForm Q I hQI hPI x : F₀) : F) = Q x :=
  rfl

theorem coe_polar_subForm (Q : QuadraticForm F V) (hQI : ∀ x ∈ I, Q x ∈ F₀)
    (hPI : ∀ x ∈ I, ∀ y ∈ I, QuadraticMap.polar Q x y ∈ F₀) (x y : I) :
    ((QuadraticMap.polar (subForm Q I hQI hPI) x y : F₀) : F) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, Subfield.coe_sub, coe_subForm, Submodule.coe_add]

@[expose] def restr (g : V ≃ₗ[F] V) (hg : ∀ x ∈ I, g x ∈ I) (hg' : ∀ x ∈ I, g⁻¹ x ∈ I) :
    I ≃ₗ[F₀] I where
  toFun x := ⟨g (x : V), hg x x.2⟩
  invFun x := ⟨g⁻¹ (x : V), hg' x x.2⟩
  map_add' x y := Subtype.ext (map_add g (x : V) y)
  map_smul' a x := Subtype.ext (by
    simp only [Submodule.coe_smul, Subfield.smul_def, map_smul, RingHom.id_apply])
  left_inv x := Subtype.ext (inv_mul_apply g (x : V))
  right_inv x := Subtype.ext (mul_inv_apply g (x : V))

@[expose] def resHom {G₀ : Subgroup (V ≃ₗ[F] V)} (hGI : ∀ g ∈ G₀, ∀ x ∈ I, g x ∈ I) :
    G₀ →* (I ≃ₗ[F₀] I) where
  toFun g := restr g.1 (hGI g.1 g.2) (hGI g.1⁻¹ (G₀.inv_mem g.2))
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

theorem coe_resHom_apply {G₀ : Subgroup (V ≃ₗ[F] V)} (hGI : ∀ g ∈ G₀, ∀ x ∈ I, g x ∈ I)
    (g : G₀) (x : I) : ((resHom hGI g x : I) : V) = (g : V ≃ₗ[F] V) (x : V) :=
  rfl

theorem eq_of_eqOn_span {S : Set V} (hS : Submodule.span F S = ⊤) {g h : V ≃ₗ[F] V}
    (hgh : ∀ x ∈ S, g x = h x) : g = h :=
  LinearEquiv.toLinearMap_injective (LinearMap.ext_on hS fun x hx => hgh x hx)

theorem resHom_injective (hspan : Submodule.span F (I : Set V) = ⊤)
    {G₀ : Subgroup (V ≃ₗ[F] V)} (hGI : ∀ g ∈ G₀, ∀ x ∈ I, g x ∈ I) :
    Function.Injective (resHom hGI) := fun g h hgh =>
  Subtype.ext (eq_of_eqOn_span hspan fun x hx =>
    congrArg (fun φ : I ≃ₗ[F₀] I => ((φ ⟨x, hx⟩ : I) : V)) hgh)

end Restriction

theorem exists_card_subfield [Finite F] [CharP F 2] {n : ℕ} (hn : Nat.card F = 2 ^ n)
    (F₀ : Subfield F) : ∃ k : ℕ, 0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k := by
  letI := Fintype.ofFinite F₀
  obtain ⟨k, -, hk⟩ := FiniteField.card F₀ 2
  have hk' : Nat.card F₀ = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
  refine ⟨k, k.pos, ?_, hk'⟩
  have h := Module.natCard_eq_pow_finrank (K := F₀) (V := F)
  rw [hn, hk', ← pow_mul] at h
  exact ⟨_, Nat.pow_right_injective le_rfl h⟩

end OrthA

end CFSG.Quasithin.SimsG4
