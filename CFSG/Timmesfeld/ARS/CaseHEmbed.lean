module

public import CFSG.Timmesfeld.ARS.CaseHField
public import CFSG.Timmesfeld.ARS.CaseHCoord

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section ShortRoot

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

theorem eq_of_shortRoot_eq (hT : MTransitive R) {A A₀ X Y : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hX : X ∈ lambdaStar R A A₀) (hY : Y ∈ lambdaStar R A A₀)
    (he : shortRoot R A A₀ X = shortRoot R A A₀ Y) : X = Y := by
  by_contra hXY
  have := h.finite
  have hXR : X ∈ R := hX.2.1
  have hV := sup_mem_linesThrough h hA hX.1
  have hYV : ¬ Y ≤ A ⊔ X := fun hle => hXY (eq_of_mem_lambdaStar_of_le h hA hA₀ hX hY hle).symm
  obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hA hA₀ hY
  obtain ⟨u₀, -, huniq⟩ := hreg _ hV _ hV hYV hYV
  have hone : ∀ u ∈ shortRoot R A A₀ Y, u = 1 := by
    intro u hu
    have hu' : u ∈ shortRoot R A A₀ X := he ▸ hu
    have hfix : conjSub (A ⊔ X) u = A ⊔ X := by
      change Subgroup.map _ (A ⊔ X) = _
      rw [Subgroup.map_sup]
      exact congrArg₂ (· ⊔ ·) (conjSub_left_of_mem_shortRoot hu')
        (conjSub_self_of_mem_shortRoot h hXR hu')
    exact congrArg Subtype.val ((huniq ⟨u, hu⟩ hfix).trans (huniq 1 (conjSub_one _)).symm)
  have hbot : shortRoot R A A₀ Y = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hone
  have hcard := card_shortRoot h hH hT hA hA₀ hY
  rw [hbot, Subgroup.card_bot] at hcard
  omega

end ShortRoot

section Diag

variable {F : Type} [Field F]

@[expose] def dvec (l : Fˣ) : Fin 3 → F := ![(l : F), 1, ((l⁻¹ : Fˣ) : F)]

theorem dvec_ne_zero (l : Fˣ) (i : Fin 3) : dvec l i ≠ 0 := by
  fin_cases i <;> simp [dvec]

theorem diag3_mul_tv {i j : Fin 3} (hij : i ≠ j) (l : Fˣ) (u : F) :
    diag3 l * SpecialLinearGroup.transvection hij u =
      SpecialLinearGroup.transvection hij (dvec l i * u * (dvec l j)⁻¹) * diag3 l := by
  have hd := dvec_ne_zero l j
  apply Subtype.ext
  rw [val_mul3, val_mul3, val_tv, val_tv]
  change Matrix.diagonal (dvec l) * _ = _ * Matrix.diagonal (dvec l)
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [this]
  · by_cases hia : i = a <;> by_cases hjb : j = b
    · subst hia hjb
      simp [hab, hd]
    all_goals simp [hab, hia, hjb]

theorem diag3_one : (diag3 1 : SpecialLinearGroup (Fin 3) F) = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) F)
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diag3_inv (l : Fˣ) : (diag3 l)⁻¹ = (diag3 l⁻¹ : SpecialLinearGroup (Fin 3) F) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, diag3_mul, inv_mul_cancel, diag3_one]

theorem conjSub_rootSubgroup_diag3 {i j : Fin 3} (hij : i ≠ j) (l : Fˣ) :
    conjSub (SpecialLinear.rootSubgroup 2 F hij) (diag3 l) = SpecialLinear.rootSubgroup 2 F hij := by
  have key : ∀ (l : Fˣ) (x : SpecialLinearGroup (Fin 3) F),
      x ∈ SpecialLinear.rootSubgroup 2 F hij →
        diag3 l * x * (diag3 l)⁻¹ ∈ SpecialLinear.rootSubgroup 2 F hij := by
    intro l x hx
    obtain ⟨u, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
    rw [diag3_mul_tv, mul_inv_cancel_right]
    exact SpecialLinear.transvection_mem_rootSubgroup hij _
  refine conjSub_eq_self_iff.2 (Subgroup.mem_normalizer_iff.2 fun x => ⟨key l x, fun hx => ?_⟩)
  have := key l⁻¹ _ hx
  rwa [← diag3_inv, inv_inv, show (diag3 l)⁻¹ * (diag3 l * x * (diag3 l)⁻¹) * diag3 l = x by
    group] at this

end Diag

theorem conjSub_map {H : Type*} [Group H] (ψ : H →* G) (X : Subgroup H) (g : H) :
    conjSub (X.map ψ) (ψ g) = (conjSub X g).map ψ := by
  change Subgroup.map _ (Subgroup.map _ _) = Subgroup.map _ (Subgroup.map _ _)
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

variable {A A₀ P P' : Subgroup G}

structure Coords (S : Setup R A A₀ P P') (F E : Type) [Field F] [Field E] where
  ψ : SpecialLinearGroup (Fin (2 + 1)) F →* G
  hψP : (SpecialLinear.rootSubgroup 2 F (show (0 : Fin 3) ≠ 1 by decide)).map ψ = P
  hψP' : (SpecialLinear.rootSubgroup 2 F (show (1 : Fin 3) ≠ 2 by decide)).map ψ = P'
  hψA : (SpecialLinear.rootSubgroup 2 F (show (0 : Fin 3) ≠ 2 by decide)).map ψ = A
  hψQ' : (SpecialLinear.rootSubgroup 2 F (show (1 : Fin 3) ≠ 0 by decide)).map ψ = ⁅A₀, P'⁆
  hψQ : (SpecialLinear.rootSubgroup 2 F (show (2 : Fin 3) ≠ 1 by decide)).map ψ = ⁅A₀, P⁆
  hψA₀ : (SpecialLinear.rootSubgroup 2 F (show (2 : Fin 3) ≠ 0 by decide)).map ψ = A₀
  hcard : Nat.card F = Nat.card A
  φ : ↥(shortRoot R A A₀ P' ⊔ shortRoot R A A₀ P) ≃* SpecialLinearGroup (Fin 2) E
  hφU : ((shortRoot R A A₀ P').subgroupOf (shortRoot R A A₀ P' ⊔ shortRoot R A A₀ P)).map
    φ.toMonoidHom = upperUnipotent E
  hφL : ((shortRoot R A A₀ P).subgroupOf (shortRoot R A A₀ P' ⊔ shortRoot R A A₀ P)).map
    φ.toMonoidHom = lowerUnipotent E

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

@[expose] noncomputable def x1 (s : E) : G := upPar c.φ s

@[expose] noncomputable def x6 (u : F) : G :=
  c.ψ (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) u)

@[expose] noncomputable def k (μ : Eˣ) : G := torPar c.φ μ

@[expose] noncomputable def d (l : Fˣ) : G := c.ψ (diag3 l)

@[expose] noncomputable def c5 (s : E) (u : F) : G := cxy S (c.x1 s) (c.x6 u)

theorem x1_mem (s : E) : c.x1 s ∈ shortRoot R A A₀ P' := upPar_mem c.hφU s

theorem x1_add (s s' : E) : c.x1 (s + s') = c.x1 s * c.x1 s' := upPar_add c.φ s s'

theorem x1_injective : Function.Injective c.x1 := upPar_injective c.φ

theorem x1_zero : c.x1 0 = 1 := upPar_zero c.φ

theorem x6_mem (u : F) : c.x6 u ∈ P := psi_tv_mem _ c.hψP u

theorem x6_add (u u' : F) : c.x6 (u + u') = c.x6 u * c.x6 u' := by
  rw [x6, x6, x6, SpecialLinearGroup.transvection_add, map_mul]

theorem x6_zero : c.x6 0 = 1 := by
  have := c.x6_add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem x6_surjective {y : G} (hy : y ∈ P) : ∃ u, c.x6 u = y := exists_psi_tv_eq _ c.hψP hy

theorem x6_injective [Finite G] (hAP : Nat.card A = Nat.card P) : Function.Injective c.x6 := by
  have hsurj : Function.Surjective fun u : F => (⟨c.x6 u, c.x6_mem u⟩ : P) := fun y => by
    obtain ⟨u, hu⟩ := c.x6_surjective y.2
    exact ⟨u, Subtype.ext hu⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [c.hcard]; exact Nat.card_pos.ne')
  have hbij := hsurj.bijective_of_nat_card_le (by rw [c.hcard, hAP])
  exact fun u u' e => hbij.1 (Subtype.ext e)

theorem k_mem_centralizer (μ : Eˣ) :
    c.k μ ∈ Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) :=
  (sup_le inf_le_left inf_le_left : shortRoot R A A₀ P' ⊔ shortRoot R A A₀ P ≤ _)
    (c.φ.symm (diagElt μ)).2

theorem k_conj_x1 (μ : Eˣ) (s : E) :
    c.k μ * c.x1 s * (c.k μ)⁻¹ = c.x1 ((μ : E) * μ * s) := by
  rw [k, x1, torPar_conj_upPar, sq]
  rfl

theorem conjSub_shortRoot_k (μ : Eˣ) :
    conjSub (shortRoot R A A₀ P') (c.k μ) = shortRoot R A A₀ P' :=
  conjSub_eq_self_iff.2 (coe_mem_normalizer c.hφU le_sup_left (by
    rw [MulEquiv.apply_symm_apply]
    exact diagElt_mem_normalizer_upperUnipotent μ))

theorem conjSub_shortRoot_k' (μ : Eˣ) :
    conjSub (shortRoot R A A₀ P) (c.k μ) = shortRoot R A A₀ P :=
  conjSub_eq_self_iff.2 (coe_mem_normalizer c.hφL le_sup_right (by
    rw [MulEquiv.apply_symm_apply]
    exact diagElt_mem_normalizer_lowerUnipotent μ))

theorem conjSub_P'_k (μ : Eˣ) : conjSub P' (c.k μ) = P' := by
  have hR := S.hyp.root
  refine eq_of_shortRoot_eq S.hyp S.hH S.hT S.hA S.h3 S.hA₀
    (conjSub_mem_lambdaStar hR S.hP' (c.k_mem_centralizer μ)) S.hP' ?_
  rw [← conjSub_shortRoot hR (c.k_mem_centralizer μ), c.conjSub_shortRoot_k]

theorem conjSub_P_k (μ : Eˣ) : conjSub P (c.k μ) = P := by
  have hR := S.hyp.root
  refine eq_of_shortRoot_eq S.hyp S.hH S.hT S.hA S.h3 S.hA₀
    (conjSub_mem_lambdaStar hR S.hP (c.k_mem_centralizer μ)) S.hP ?_
  rw [← conjSub_shortRoot hR (c.k_mem_centralizer μ), c.conjSub_shortRoot_k']

theorem conjSub_A_k (μ : Eˣ) : conjSub A (c.k μ) = A :=
  conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (c.k_mem_centralizer μ) x (Subgroup.mem_sup_left hx)).symm

theorem conjSub_A₀_k (μ : Eˣ) : conjSub A₀ (c.k μ) = A₀ :=
  conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (c.k_mem_centralizer μ) x (Subgroup.mem_sup_right hx)).symm

theorem conjSub_Q_k (μ : Eˣ) : conjSub ⁅A₀, P⁆ (c.k μ) = ⁅A₀, P⁆ := by
  change Subgroup.map _ ⁅A₀, P⁆ = _
  rw [Subgroup.map_commutator]
  exact congrArg₂ (fun X Y => ⁅X, Y⁆) (c.conjSub_A₀_k μ) (c.conjSub_P_k μ)

theorem conjSub_d {i j : Fin 3} (hij : i ≠ j) {X : Subgroup G}
    (hX : (SpecialLinear.rootSubgroup 2 F hij).map c.ψ = X) (l : Fˣ) : conjSub X (c.d l) = X := by
  rw [← hX, d, conjSub_map, conjSub_rootSubgroup_diag3]

theorem d_conj_x6 (l : Fˣ) (u : F) : c.d l * c.x6 u * (c.d l)⁻¹ = c.x6 (l * u) := by
  rw [d, x6, x6, ← map_mul, ← map_inv, ← map_mul, diag3_conj_tv01]

theorem d_mem [CharP F 2] (l : Fˣ) : c.d l ∈ A ⊔ A₀ := psi_diag3_mem c.hψA c.hψA₀ l

theorem d_mul_k [CharP F 2] (l : Fˣ) (μ : Eˣ) : c.d l * c.k μ = c.k μ * c.d l :=
  Subgroup.mem_centralizer_iff.1 (c.k_mem_centralizer μ) _ (c.d_mem l)

theorem d_conj_x1 [CharP F 2] (l : Fˣ) (s : E) : c.d l * c.x1 s * (c.d l)⁻¹ = c.x1 s := by
  rw [Subgroup.mem_centralizer_iff.1 (c.x1_mem s).1 _ (c.d_mem l), mul_inv_cancel_right]

omit c in
theorem _root_.CFSG.Timmesfeld.ARS.CaseH.cxy_conj (S : Setup R A A₀ P P') {g : G}
    (hgA : conjSub A g = A) (hgP' : conjSub P' g = P') (hgQ : conjSub ⁅A₀, P⁆ g = ⁅A₀, P⁆)
    {x y : G} (hx : x ∈ shortRoot R A A₀ P') (hy : y ∈ P)
    (hx' : g * x * g⁻¹ ∈ shortRoot R A A₀ P') (hy' : g * y * g⁻¹ ∈ P) :
    cxy S (g * x * g⁻¹) (g * y * g⁻¹) = g * cxy S x y * g⁻¹ := by
  obtain ⟨h1, h2⟩ := cxy_spec S hx hy
  rw [cxy, FrameSL3.commutatorElement_conj]
  refine comp5_eq S ?_ ?_ ?_
  · rw [← FrameSL3.commutatorElement_conj]
    exact commutator_mem_H S hx' hy'
  · have hU : conjSub (shortRoot R P' ⁅A₀, P⁆ A) g = shortRoot R P' ⁅A₀, P⁆ A := by
      rw [conjSub_shortRoot' S.hyp.root, hgP', hgQ, hgA]
    rw [← hU]
    exact conj_mem_conjSub g h1
  · rw [show g * ⁅x, y⁆ * g⁻¹ * (g * cxy S x y * g⁻¹)⁻¹ = g * (⁅x, y⁆ * (cxy S x y)⁻¹) * g⁻¹ by
      group, ← conjSub_K S.hyp S.hA S.hP'.2.1 hgA hgP']
    exact conj_mem_conjSub g h2

theorem d_conj_c5 [CharP F 2] (l : Fˣ) (s : E) (u : F) :
    c.d l * c.c5 s u * (c.d l)⁻¹ = c.c5 s (l * u) := by
  rw [c5, c5, ← c.d_conj_x6, ← cxy_conj S (c.conjSub_d _ c.hψA l) (c.conjSub_d _ c.hψP' l)
    (c.conjSub_d _ c.hψQ l) (c.x1_mem s) (c.x6_mem u) (by rw [c.d_conj_x1]; exact c.x1_mem s)
    (by rw [c.d_conj_x6]; exact c.x6_mem _), c.d_conj_x1]

theorem exists_torus_scalar [Finite F] [CharP F 2] (μ : Eˣ) :
    ∃ ν : F, ν ≠ 0 ∧ ∀ u, c.k μ * c.x6 u * (c.k μ)⁻¹ = c.x6 (ν * u) := by
  have := S.hyp.finite
  have hinj := c.x6_injective (S.hyp.root.card_eq S.hA S.hP.2.1)
  have hmem : ∀ u, c.k μ * c.x6 u * (c.k μ)⁻¹ ∈ P := fun u => by
    have := conj_mem_conjSub (c.k μ) (c.x6_mem u)
    rwa [c.conjSub_P_k μ] at this
  choose f hf using fun u => c.x6_surjective (hmem u)
  have hf0 : f 0 = 0 := hinj (by rw [hf, c.x6_zero, mul_one, mul_inv_cancel])
  have hlin : ∀ (l : Fˣ) (u : F), f (l * u) = l * f u := by
    intro l u
    apply hinj
    calc c.x6 (f (l * u)) = c.k μ * c.x6 (l * u) * (c.k μ)⁻¹ := hf _
      _ = c.k μ * (c.d l * c.x6 u * (c.d l)⁻¹) * (c.k μ)⁻¹ := by rw [c.d_conj_x6]
      _ = (c.k μ * c.d l) * c.x6 u * (c.k μ * c.d l)⁻¹ := by group
      _ = (c.d l * c.k μ) * c.x6 u * (c.d l * c.k μ)⁻¹ := by rw [c.d_mul_k]
      _ = c.d l * (c.k μ * c.x6 u * (c.k μ)⁻¹) * (c.d l)⁻¹ := by group
      _ = c.d l * c.x6 (f u) * (c.d l)⁻¹ := by rw [hf]
      _ = c.x6 (l * f u) := c.d_conj_x6 l (f u)
  have hf' : ∀ u, f u = f 1 * u := by
    intro u
    by_cases hu : u = 0
    · rw [hu, hf0, mul_zero]
    · have := hlin (Units.mk0 u hu) 1
      rwa [Units.val_mk0, mul_one, mul_comm] at this
  refine ⟨f 1, fun h0 => ?_, fun u => by rw [← hf, hf']⟩
  have h1 := hf 1
  rw [h0, c.x6_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at h1
  exact one_ne_zero (hinj (h1.trans c.x6_zero.symm))

theorem k_conj_c5 (μ : Eˣ) {ν : F} (hν : ∀ u, c.k μ * c.x6 u * (c.k μ)⁻¹ = c.x6 (ν * u))
    (s : E) (u : F) : c.k μ * c.c5 s u * (c.k μ)⁻¹ = c.c5 ((μ : E) * μ * s) (ν * u) := by
  rw [c5, c5, ← c.k_conj_x1, ← hν, cxy_conj S (c.conjSub_A_k μ) (c.conjSub_P'_k μ) (c.conjSub_Q_k μ)
    (c.x1_mem s) (c.x6_mem u) (by rw [c.k_conj_x1]; exact c.x1_mem _)
    (by rw [hν]; exact c.x6_mem _)]

theorem c5_add_left (s s' : E) (u : F) : c.c5 (s + s') u = c.c5 s u * c.c5 s' u := by
  rw [c5, c.x1_add]
  exact cxy_mul_left S (c.x1_mem s) (c.x1_mem s') (c.x6_mem u)

theorem c5_add_right (s : E) (u u' : F) : c.c5 s (u + u') = c.c5 s u * c.c5 s u' := by
  rw [c5, c.x6_add]
  exact cxy_mul_right S (c.x1_mem s) (c.x6_mem u) (c.x6_mem u')

theorem c5_zero_right (s : E) : c.c5 s 0 = 1 := by
  rw [c5, cxy, c.x6_zero, commutatorElement_one_right]
  refine comp5_eq S ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩ (Subgroup.one_mem _) ?_
  rw [inv_one, mul_one]
  exact Subgroup.one_mem _

theorem c5_mem (s : E) (u : F) : c.c5 s u ∈ shortRoot R P' ⁅A₀, P⁆ A :=
  (cxy_spec S (c.x1_mem s) (c.x6_mem u)).1

theorem c5_ne_one {s : E} {u : F} (hs : s ≠ 0) (hu : u ≠ 0) : c.c5 s u ≠ 1 := by
  have := S.hyp.finite
  refine cxy_ne_one S (c.x1_mem s) (c.x6_mem u) (fun h => hs (c.x1_injective ?_))
    (fun h => hu (c.x6_injective (S.hyp.root.card_eq S.hA S.hP.2.1) ?_))
  · rw [h, c.x1_zero]
  · rw [h, c.x6_zero]

theorem c5_one_injective : Function.Injective fun s : E => c.c5 s 1 := by
  intro s s' e
  by_contra hne
  have h := c.c5_add_left (s - s') s' 1
  rw [sub_add_cancel] at h
  simp only at e
  rw [e] at h
  exact c.c5_ne_one (sub_ne_zero.2 hne) one_ne_zero
    (mul_right_cancel (h.symm.trans (one_mul _).symm))

include c in
theorem card_E : Nat.card E = Nat.card (shortRoot R P' ⁅A₀, P⁆ A) := by
  have h := S.hyp
  have hP'R : P' ∈ R := S.hP'.2.1
  obtain ⟨-, -, -, -, -, ⟨hsAQ, -⟩, -, -, -, hQΩ⟩ :=
    apartment h S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hAs' : A ∈ lambdaStar R P' ⁅A₀, P⁆ := ⟨mem_lambdaSet_comm S.hA S.hP'.1, S.hA, hsAQ.symm⟩
  rw [card_shortRoot h S.hH S.hT hP'R hQΩ hAs', ncard_linesThrough_eq h S.hA hP'R,
    ← card_shortRoot h S.hH S.hT S.hA S.hA₀ S.hP']
  refine Nat.card_eq_of_bijective (fun s => ⟨c.x1 s, c.x1_mem s⟩)
    ⟨fun s s' e => c.x1_injective (by have := congrArg Subtype.val e; exact this), fun y => ?_⟩
  obtain ⟨s, hs⟩ := exists_upPar_eq c.hφU le_sup_left y.2
  exact ⟨s, Subtype.ext hs⟩

theorem exists_ringHom [Finite F] [CharP F 2] [Finite E] [CharP E 2] :
    ∃ e : F →+* E, ∀ s u, c.c5 s u = c.c5 (e u * s) 1 := by
  have := S.hyp.finite
  have hinj := c.c5_one_injective
  have hbij : Function.Bijective fun s : E => (⟨c.c5 s 1, c.c5_mem s 1⟩ :
      shortRoot R P' ⁅A₀, P⁆ A) :=
    (Function.Injective.bijective_of_nat_card_le (fun s s' e => hinj (congrArg Subtype.val e))
      c.card_E.ge)
  choose M hM using fun s u => hbij.2 ⟨c.c5 s u, c.c5_mem s u⟩
  replace hM : ∀ s u, c.c5 (M s u) 1 = c.c5 s u := fun s u => congrArg Subtype.val (hM s u)
  have hM1 : ∀ s, M s 1 = s := fun s => hinj (hM s 1)
  have hMadd : ∀ s s' u, M (s + s') u = M s u + M s' u := fun s s' u => hinj (by
    simp only
    rw [hM, c.c5_add_left, c.c5_add_left, hM, hM])
  have hMadd' : ∀ s u u', M s (u + u') = M s u + M s u' := fun s u u' => hinj (by
    simp only
    rw [hM, c.c5_add_right, c.c5_add_left, hM, hM])
  have hM0 : ∀ s, M s 0 = 0 := fun s => by
    have := hMadd' s 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hM0' : ∀ u, M 0 u = 0 := fun u => by
    have := hMadd 0 0 u
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hMmul : ∀ (l : Fˣ) s u, M s (l * u) = M (M s u) l := fun l s u => hinj (by
    simp only
    rw [hM, hM, ← c.d_conj_c5, ← hM, c.d_conj_c5, mul_one])
  have hMinj : ∀ (l : Fˣ) a b, M a l = M b l → a = b := fun l a b e => by
    have key : ∀ a, M (M a l) (l⁻¹ : Fˣ) = a := fun a => by
      rw [← hMmul, ← Units.val_mul, inv_mul_cancel, Units.val_one, hM1]
    rw [← key a, e, key]
  have hMsq : ∀ (μ : Eˣ) s u, M ((μ : E) * μ * s) u = μ * μ * M s u := by
    intro μ s u
    obtain ⟨ν, hν0, hν⟩ := c.exists_torus_scalar μ
    set l : Fˣ := Units.mk0 ν hν0
    have hlν : (l : F) = ν := rfl
    rw [← hlν] at hν
    have e1 : c.c5 (M ((μ : E) * μ * s) (l * u)) 1 = c.c5 (M ((μ : E) * μ * M s u) l) 1 := by
      rw [hM, hM, ← c.k_conj_c5 μ hν, ← mul_one (l : F), ← c.k_conj_c5 μ hν, hM]
    have e2 := hinj e1
    rw [hMmul] at e2
    exact hMinj _ _ _ e2
  have hMlin : ∀ s u, M s u = s * M 1 u := by
    intro s u
    by_cases hs : s = 0
    · rw [hs, hM0', zero_mul]
    · obtain ⟨r, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq E 2) s
      have hr : r ≠ 0 := fun h0 => hs (by rw [h0, mul_zero])
      have := hMsq (Units.mk0 r hr) 1 u
      rwa [Units.val_mk0, mul_one] at this
  refine ⟨{ toFun := fun u => M 1 u
            map_one' := hM1 1
            map_mul' := fun u u' => ?_
            map_zero' := hM0 1
            map_add' := fun u u' => hMadd' 1 u u' }, fun s u => ?_⟩
  · by_cases hu : u = 0
    · simp only [hu, zero_mul, hM0]
    · have := hMmul (Units.mk0 u hu) 1 u'
      rw [Units.val_mk0] at this
      rw [this, hMlin (M 1 u') u, mul_comm]
  · simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← hM, hMlin s u, mul_comm s]

include c in
theorem exists_card_eq_pow [Finite F] [CharP F 2] [Finite E] [CharP E 2] :
    ∃ k : ℕ, Nat.card E = Nat.card F ^ k := by
  obtain ⟨e, -⟩ := c.exists_ringHom
  let _ := e.toAlgebra
  have : Module.Finite F E := Module.Finite.of_finite
  exact ⟨_, Module.natCard_eq_pow_finrank⟩

end Coords

theorem Setup.exists_coords (S : Setup R A A₀ P P') :
    ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nat.card A = 2 ^ n ∧ (linesThrough R A).ncard = 2 ^ m + 1 ∧
      Nonempty (Coords S (GaloisField 2 n) (GaloisField 2 m)) := by
  have h := S.hyp
  have := h.finite
  obtain ⟨n, hn, hq, -⟩ := Opposite.exists_mulEquiv_SL2' h.root S.hA S.hA₀.2
  obtain ⟨ψ, h1, h2, h3, h4, h5, h6, -⟩ :=
    exists_hom_SL3_apartment h S.hH S.hA S.hA₀ S.hP S.hP' S.hPP' hq
  rw [FrameSL3.rootGroup_α₁] at h1
  rw [FrameSL3.rootGroup_α₂] at h2
  rw [FrameSL3.rootGroup_α₁₂] at h3
  rw [FrameSL3.rootGroup_neg_α₁] at h4
  rw [FrameSL3.rootGroup_neg_α₂] at h5
  rw [FrameSL3.rootGroup_neg_α₁₂] at h6
  obtain ⟨m, hm, hlines, φ, hU, hL⟩ :=
    exists_mulEquiv_SL2_shortRoot h S.hH S.hT S.hA S.h3 S.hA₀ S.hP' S.hP S.hPP'.symm
  refine ⟨n, m, hn, hm, hq, hlines, ⟨?_⟩⟩
  exact
    { ψ := ψ
      hψP := h1
      hψP' := h2
      hψA := h3
      hψQ' := h4
      hψQ := h5
      hψA₀ := h6
      hcard := (GaloisField.card 2 n (by omega)).trans hq.symm
      φ := φ
      hφU := hU
      hφL := hL }

theorem Setup.exists_pow (S : Setup R A A₀ P P') :
    ∃ k : ℕ, (linesThrough R A).ncard - 1 = Nat.card A ^ k := by
  obtain ⟨n, m, hn, hm, hq, hl, ⟨c⟩⟩ := S.exists_coords
  obtain ⟨k, hk⟩ := c.exists_card_eq_pow
  rw [GaloisField.card 2 m (by omega), GaloisField.card 2 n (by omega)] at hk
  exact ⟨k, by rw [hl, hq, Nat.add_sub_cancel, hk]⟩

end CaseH

end CFSG.Timmesfeld.ARS
