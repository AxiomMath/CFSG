module

public import CFSG.Timmesfeld.ARS.CaseHAlign
public import CFSG.Timmesfeld.ARS.CaseHEmbed

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

theorem mElt_eq {E : Type*} [Field E] [CharP E 2] (c : E) (hc : c ≠ 0) :
    mElt c hc = diagElt (Units.mk0 c hc) * weylElt E := by
  apply Subtype.ext
  rw [val_mElt, val_mul, coe_diagElt, coe_weylElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

@[expose] noncomputable def x2 (u : F) : G :=
  c.ψ (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) u)

@[expose] noncomputable def x5 (s : E) : G := c.c5 s 1

@[expose] noncomputable def xm1 (s : E) : G := lowPar c.φ s

theorem x2_mem (u : F) : c.x2 u ∈ P' := psi_tv_mem _ c.hψP' u

theorem x2_add (u u' : F) : c.x2 (u + u') = c.x2 u * c.x2 u' := by
  rw [x2, x2, x2, SpecialLinearGroup.transvection_add, map_mul]

theorem x2_zero : c.x2 0 = 1 := by
  have := c.x2_add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem x2_surjective {y : G} (hy : y ∈ P') : ∃ u, c.x2 u = y := exists_psi_tv_eq _ c.hψP' hy

theorem x2_injective [Finite G] (hAP' : Nat.card A = Nat.card P') : Function.Injective c.x2 := by
  have hsurj : Function.Surjective fun u : F => (⟨c.x2 u, c.x2_mem u⟩ : P') := fun y => by
    obtain ⟨u, hu⟩ := c.x2_surjective y.2
    exact ⟨u, Subtype.ext hu⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [c.hcard]; exact Nat.card_pos.ne')
  have hbij := hsurj.bijective_of_nat_card_le (by rw [c.hcard, hAP'])
  exact fun u u' e => hbij.1 (Subtype.ext e)

theorem d_conj_x2 (l : Fˣ) (u : F) : c.d l * c.x2 u * (c.d l)⁻¹ = c.x2 (l * u) := by
  rw [d, x2, x2, ← map_mul, ← map_inv, ← map_mul, diag3_mul_tv, mul_inv_cancel_right]
  congr 2
  simp [dvec, mul_comm]

theorem xm1_mem (s : E) : c.xm1 s ∈ shortRoot R A A₀ P := lowPar_mem c.hφL s

theorem x5_mem (s : E) : c.x5 s ∈ shortRoot R P' ⁅A₀, P⁆ A := c.c5_mem s 1

section Weyl

variable [CharP E 2]

@[expose] noncomputable def m : G := weylPar c.φ

@[expose] noncomputable def x3 (s : E) : G := c.m * c.x5 s * c.m⁻¹

theorem m_mem_centralizer : c.m ∈ Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) :=
  (sup_le inf_le_left inf_le_left : shortRoot R A A₀ P' ⊔ shortRoot R A A₀ P ≤ _)
    (c.φ.symm (weylElt E)).2

theorem m_mul_self : c.m * c.m = 1 := by
  simp only [m, weylPar, ← Subgroup.coe_mul, ← map_mul, weylElt_mul_self, map_one,
    OneMemClass.coe_one]

theorem m_inv : c.m⁻¹ = c.m := inv_eq_of_mul_eq_one_right c.m_mul_self

theorem m_conj_x1 (s : E) : c.m * c.x1 s * c.m⁻¹ = c.xm1 s := weylPar_conj_upPar c.φ s

theorem conjSub_A_m : conjSub A c.m = A :=
  conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 c.m_mem_centralizer x (Subgroup.mem_sup_left hx)).symm

theorem conjSub_A₀_m : conjSub A₀ c.m = A₀ :=
  conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 c.m_mem_centralizer x (Subgroup.mem_sup_right hx)).symm

theorem m_mem_normalizer : c.m ∈ Subgroup.normalizer (A : Set G) :=
  conjSub_eq_self_iff.1 c.conjSub_A_m

theorem conjSub_Xa_m : conjSub (shortRoot R A A₀ P') c.m = shortRoot R A A₀ P := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := exists_upPar_eq c.hφU le_sup_left hx
    change c.m * c.x1 s * c.m⁻¹ ∈ _
    rw [c.m_conj_x1]
    exact c.xm1_mem s
  · obtain ⟨s, rfl⟩ := exists_lowPar_eq c.hφL le_sup_right hy
    rw [← xm1, ← c.m_conj_x1]
    exact conj_mem_conjSub _ (c.x1_mem s)

theorem conjSub_P'_m : conjSub P' c.m = P := by
  have hR := S.hyp.root
  refine eq_of_shortRoot_eq S.hyp S.hH S.hT S.hA S.h3 S.hA₀
    (conjSub_mem_lambdaStar hR S.hP' c.m_mem_centralizer) S.hP ?_
  rw [← conjSub_shortRoot hR c.m_mem_centralizer, c.conjSub_Xa_m]

theorem conjSub_P_m : conjSub P c.m = P' := by
  have := congrArg (fun H => conjSub H c.m) c.conjSub_P'_m
  rw [← conjSub_mul, c.m_mul_self, conjSub_one] at this
  exact this.symm

theorem conjSub_Q_m : conjSub ⁅A₀, P⁆ c.m = ⁅A₀, P'⁆ := by
  change Subgroup.map _ ⁅A₀, P⁆ = _
  rw [Subgroup.map_commutator]
  exact congrArg₂ (fun X Y => ⁅X, Y⁆) c.conjSub_A₀_m c.conjSub_P_m

theorem conjSub_Q'_m : conjSub ⁅A₀, P'⁆ c.m = ⁅A₀, P⁆ := by
  change Subgroup.map _ ⁅A₀, P'⁆ = _
  rw [Subgroup.map_commutator]
  exact congrArg₂ (fun X Y => ⁅X, Y⁆) c.conjSub_A₀_m c.conjSub_P'_m

theorem conjSub_U5_m :
    conjSub (shortRoot R P' ⁅A₀, P⁆ A) c.m = shortRoot R P ⁅A₀, P'⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_P'_m, c.conjSub_Q_m, c.conjSub_A_m]

theorem conjSub_U3_m :
    conjSub (shortRoot R P ⁅A₀, P'⁆ A) c.m = shortRoot R P' ⁅A₀, P⁆ A := by
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_P_m, c.conjSub_Q'_m, c.conjSub_A_m]

theorem conj_m_mem {H H' : Subgroup G} (hH : conjSub H c.m = H') {x : G} (hx : x ∈ H) :
    c.m * x * c.m⁻¹ ∈ H' := hH ▸ conj_mem_conjSub _ hx

theorem x3_mem (s : E) : c.x3 s ∈ shortRoot R P ⁅A₀, P'⁆ A :=
  c.conj_m_mem c.conjSub_U5_m (c.x5_mem s)

theorem m_conj_x3 (s : E) : c.m * c.x3 s * c.m⁻¹ = c.x5 s := by
  rw [x3, c.m_inv]
  simp only [← mul_assoc, c.m_mul_self, one_mul]
  rw [mul_assoc, c.m_mul_self, mul_one]

theorem d_mul_m [CharP F 2] (l : Fˣ) : c.d l * c.m = c.m * c.d l :=
  Subgroup.mem_centralizer_iff.1 c.m_mem_centralizer _ (c.d_mem l)

theorem exists_tau [Finite F] [CharP F 2] :
    ∃ τ : F, τ ≠ 0 ∧ ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u) := by
  have := S.hyp.finite
  have hR := S.hyp.root
  have hinj := c.x2_injective (hR.card_eq S.hA S.hP'.2.1)
  have hinj6 := c.x6_injective (hR.card_eq S.hA S.hP.2.1)
  choose f hf using fun u => c.x2_surjective (c.conj_m_mem c.conjSub_P_m (c.x6_mem u))
  have hf0 : f 0 = 0 := hinj (by rw [hf, c.x6_zero, mul_one, mul_inv_cancel, c.x2_zero])
  have hlin : ∀ (l : Fˣ) (u : F), f (l * u) = l * f u := by
    intro l u
    apply hinj
    calc c.x2 (f (l * u)) = c.m * c.x6 (l * u) * c.m⁻¹ := hf _
      _ = c.m * (c.d l * c.x6 u * (c.d l)⁻¹) * c.m⁻¹ := by rw [c.d_conj_x6]
      _ = (c.m * c.d l) * c.x6 u * (c.m * c.d l)⁻¹ := by group
      _ = (c.d l * c.m) * c.x6 u * (c.d l * c.m)⁻¹ := by rw [c.d_mul_m]
      _ = c.d l * (c.m * c.x6 u * c.m⁻¹) * (c.d l)⁻¹ := by group
      _ = c.d l * c.x2 (f u) * (c.d l)⁻¹ := by rw [hf]
      _ = c.x2 (l * f u) := c.d_conj_x2 l (f u)
  have hf' : ∀ u, f u = f 1 * u := by
    intro u
    by_cases hu : u = 0
    · rw [hu, hf0, mul_zero]
    · have := hlin (Units.mk0 u hu) 1
      rwa [Units.val_mk0, mul_one, mul_comm] at this
  refine ⟨f 1, fun h0 => ?_, fun u => by rw [← hf, hf']⟩
  have h1 := hf 1
  rw [h0, c.x2_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at h1
  exact one_ne_zero (hinj6 (h1.trans c.x6_zero.symm))

theorem x1_mul_xm1_mul_x1 {s : E} (hs : s ≠ 0) :
    c.x1 s * c.xm1 s⁻¹ * c.x1 s = c.k (Units.mk0 s hs) * c.m := by
  simp only [x1, xm1, k, m, upPar, lowPar, torPar, weylPar, ← Subgroup.coe_mul, ← map_mul,
    upperElt_mul_lowerElt_inv_mul_upperElt s hs, mElt_eq]

end Weyl

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
