module

public import CFSG.Timmesfeld.ARS.CaseHIdent

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

theorem mul_self_four {a b c d z₁ z₂ : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hd : d * d = 1) (hab : Commute a b) (hac : Commute a c) (hbd : Commute b d)
    (hcd : Commute c d) (hda : d * a = z₁ * (a * d)) (hcb : c * b = z₂ * (b * c))
    (hz₁ : Commute z₁ (a * b * c)) (hz₂ : Commute z₂ b) :
    a * b * c * d * (a * b * c * d) = z₁ * z₂ := by
  calc a * b * c * d * (a * b * c * d) = a * b * c * (d * a) * b * c * d := by group
    _ = a * b * c * z₁ * a * d * b * c * d := by rw [hda]; group
    _ = z₁ * (a * b * c) * a * d * b * c * d := by rw [← hz₁.eq]
    _ = z₁ * (a * (b * (c * a))) * d * b * c * d := by group
    _ = z₁ * (a * (b * (a * c))) * d * b * c * d := by rw [← hac.eq]
    _ = z₁ * (a * (b * a) * c) * d * b * c * d := by group
    _ = z₁ * (a * (a * b) * c) * d * b * c * d := by rw [← hab.eq]
    _ = z₁ * ((a * a) * (b * c)) * d * b * c * d := by group
    _ = z₁ * b * c * (d * b) * c * d := by rw [ha, one_mul]; group
    _ = z₁ * b * c * (b * d) * c * d := by rw [← hbd.eq]
    _ = z₁ * b * (c * b) * d * c * d := by group
    _ = z₁ * b * (z₂ * (b * c)) * d * c * d := by rw [hcb]
    _ = z₁ * (b * z₂) * b * c * d * c * d := by group
    _ = z₁ * (z₂ * b) * b * c * d * c * d := by rw [← hz₂.eq]
    _ = z₁ * z₂ * (b * b) * c * (d * c) * d := by group
    _ = z₁ * z₂ * (b * b) * c * (c * d) * d := by rw [← hcd.eq]
    _ = z₁ * z₂ * (b * b) * (c * c) * (d * d) := by group
    _ = z₁ * z₂ := by rw [hb, hc, hd]; group

theorem _root_.CFSG.Timmesfeld.ARS.CaseH.Setup.sq_eq_sq_lift (S : Setup R A A₀ P P')
    (g : ↥(M R A)) :
    (g : G) * g = (S.lift (S.proj g) : G) * S.lift (S.proj g) := by
  have := S.hyp.finite
  have hR := S.hyp.root
  obtain ⟨a, ha, hg⟩ := S.exists_eq_mul g
  have hg' : (g : G) = (S.lift (S.proj g) : G) * a := hg
  have hc : Commute a (S.lift (S.proj g) : G) :=
    QD.commuting_M hR S.hA a ha _ (S.lift (S.proj g)).2
  rw [hg', show (S.lift (S.proj g) : G) * a * ((S.lift (S.proj g) : G) * a) =
      (S.lift (S.proj g) : G) * (a * (S.lift (S.proj g) : G)) * a by group, hc.eq,
    show (S.lift (S.proj g) : G) * ((S.lift (S.proj g) : G) * a) * a =
      (S.lift (S.proj g) : G) * (S.lift (S.proj g) : G) * (a * a) by group,
    hR.mul_self A S.hA a ha, mul_one]

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

@[expose] noncomputable def x4 (z : F) : G :=
  c.ψ (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) z)

theorem x4_mem (z : F) : c.x4 z ∈ A := psi_tv_mem _ c.hψA z

theorem x4_add (z z' : F) : c.x4 (z + z') = c.x4 z * c.x4 z' := by
  rw [x4, x4, x4, SpecialLinearGroup.transvection_add, map_mul]

theorem x4_zero : c.x4 0 = 1 := by
  have := c.x4_add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem x4_surjective {y : G} (hy : y ∈ A) : ∃ z, c.x4 z = y := exists_psi_tv_eq _ c.hψA hy

theorem x4_injective [Finite G] : Function.Injective c.x4 := by
  have hsurj : Function.Surjective fun z : F => (⟨c.x4 z, c.x4_mem z⟩ : A) := fun y => by
    obtain ⟨z, hz⟩ := c.x4_surjective y.2
    exact ⟨z, Subtype.ext hz⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [c.hcard]; exact Nat.card_pos.ne')
  have hbij := hsurj.bijective_of_nat_card_le (by rw [c.hcard])
  exact fun z z' e => hbij.1 (Subtype.ext e)

theorem comm_x2_x6 [CharP F 2] (v u : F) : ⁅c.x2 v, c.x6 u⁆ = c.x4 (v * u) := by
  have hinv : ∀ (z : F), (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) z)⁻¹ =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) z := fun z => by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      SpecialLinearGroup.transvection_coeff_zero]
  rw [x2, x6, x4, ← map_commutatorElement, ← commutatorElement_inv,
    SpecialLinearGroup.commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) u v, map_inv,
    ← map_inv, hinv, mul_comm]

variable [CharP E 2]

theorem comm_x3_x5_mem (r w : E) : ⁅c.x3 r, c.x5 w⁆ ∈ A := by
  have h := (positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP').2.2.2.2.2.2.2.1
    (Subgroup.commutator_mem_commutator (c.x5_mem w) (c.x3_mem r))
  rw [← commutatorElement_inv]
  exact A.inv_mem h

@[expose] noncomputable def Tp (r w : E) : F :=
  Classical.choose (c.x4_surjective (c.comm_x3_x5_mem r w))

theorem x4_Tp (r w : E) : c.x4 (c.Tp r w) = ⁅c.x3 r, c.x5 w⁆ :=
  Classical.choose_spec (c.x4_surjective (c.comm_x3_x5_mem r w))

theorem Tp_add_left (r r' w : E) : c.Tp (r + r') w = c.Tp r w + c.Tp r' w := by
  have := S.hyp.finite
  apply c.x4_injective
  have hc : Commute (c.x3 r) ⁅c.x3 r', c.x5 w⁆ :=
    (QD.commuting_M S.hyp.root S.hA _ (c.comm_x3_x5_mem r' w) _
      (Setup.U3_le_M (c.x3_mem r))).symm
  rw [c.x4_add, c.x4_Tp, c.x4_Tp, c.x4_Tp, c.x3_add,
    Plane.commutatorElement_mul_left_of_commute hc]
  exact (S.hyp.root.commuting_self S.hA _ (c.comm_x3_x5_mem r' w) _ (c.comm_x3_x5_mem r w)).eq

theorem Tp_zero_right (r : E) : c.Tp r 0 = 0 := by
  have := S.hyp.finite
  apply c.x4_injective
  rw [c.x4_Tp, c.x5_zero, commutatorElement_one_right, c.x4_zero]

theorem Tp_zero_left (w : E) : c.Tp 0 w = 0 := by
  have := S.hyp.finite
  apply c.x4_injective
  rw [c.x4_Tp, c.x3_zero, commutatorElement_one_left, c.x4_zero]

theorem sq_lift [CharP F 2] (u : F) (w r : E) (v : F) :
    (S.lift (c.vc u w r v) : G) * S.lift (c.vc u w r v) = c.x4 (v * u + c.Tp r w) := by
  have h := S.hyp
  have := h.finite
  have hR := h.root
  have hPR : P ∈ R := S.hP.2.1
  have hP'R : P' ∈ R := S.hP'.2.1
  obtain ⟨-, -, -, -, -, ⟨hsAQ, -⟩, ⟨hsAQ', -⟩, -, hQ'Ω, hQΩ⟩ :=
    apartment h S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm S.hA S.hP.1, S.hA, hsAQ'.symm⟩
  have hAs' : A ∈ lambdaStar R P' ⁅A₀, P⁆ := ⟨mem_lambdaSet_comm S.hA S.hP'.1, S.hA, hsAQ.symm⟩
  obtain ⟨-, -, -, hU5P, hU3P, -, -, -, hU5P', -, hU3P', -, -⟩ :=
    positive_relations h S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  have hcen : ∀ z, z ∈ A → ∀ g ∈ M R A, Commute z g := fun z hz g hg =>
    QD.commuting_M hR S.hA z hz g hg
  change c.x6 u * c.x5 w * c.x3 r * c.x2 v * (c.x6 u * c.x5 w * c.x3 r * c.x2 v) = _
  rw [c.x4_add]
  refine mul_self_four (hR.mul_self P hPR _ (c.x6_mem u))
    ((shortRoot_moufang_of h S.hH S.hT hP'R hQΩ hAs').2.1 _ (c.x5_mem w))
    ((shortRoot_moufang_of h S.hH S.hT hPR hQ'Ω hAs).2.1 _ (c.x3_mem r))
    (hR.mul_self P' hP'R _ (c.x2_mem v)) (hU5P _ (c.x5_mem w) _ (c.x6_mem u)).symm
    (hU3P _ (c.x3_mem r) _ (c.x6_mem u)).symm (hU5P' _ (c.x5_mem w) _ (c.x2_mem v))
    (hU3P' _ (c.x3_mem r) _ (c.x2_mem v)) ?_ ?_
    (hcen _ (c.x4_mem _) _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (S.P_le_M (c.x6_mem u))
      (Setup.U5_le_M (c.x5_mem w))) (Setup.U3_le_M (c.x3_mem r))))
    (hcen _ (c.x4_mem _) _ (Setup.U5_le_M (c.x5_mem w)))
  · rw [← c.comm_x2_x6 v u, commutatorElement_def]
    group
  · rw [c.x4_Tp, commutatorElement_def]
    group

theorem Tp_eq [Finite F] [CharP F 2] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
    (r s : E) : c.Tp r s = c.T s r := by
  have := S.hyp.finite
  have hx := c.x1_mem_normalizer s
  have key : ∀ r, c.N s + c.T s r + (c.Tp r s + c.Tp (c.sharp s) s) = 0 := fun r => by
    have hcen : Commute (c.x1 s) (c.x4 (0 * 1 + c.Tp r 0)) :=
      (positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP').2.2.1 _ (c.x1_mem s)
        _ (c.x4_mem _)
    set g : ↥(M R A) := ⟨c.x1 s * S.lift (c.vc 1 0 r 0) * (c.x1 s)⁻¹,
      conj_mem_M_of_mem_normalizer S.hyp.root hx (S.lift (c.vc 1 0 r 0)).2⟩ with hg
    have h1 : (g : G) * g = c.x4 (0 * 1 + c.Tp r 0) := by
      rw [hg, show c.x1 s * ↑(S.lift (c.vc 1 0 r 0)) * (c.x1 s)⁻¹ *
          (c.x1 s * ↑(S.lift (c.vc 1 0 r 0)) * (c.x1 s)⁻¹) =
          c.x1 s * (↑(S.lift (c.vc 1 0 r 0)) * ↑(S.lift (c.vc 1 0 r 0))) * (c.x1 s)⁻¹ by group,
        c.sq_lift, hcen.eq, mul_inv_cancel_right]
    have h2 : S.proj g = c.vc 1 s (r + c.sharp s) (c.N s + c.T s r) := by
      rw [hg, ← S.ad_apply hx, c.ad_x1 e he]
      simp only [map_one, one_mul, zero_add, c.F3_zero, c.F2_zero, add_zero]
    rw [S.sq_eq_sq_lift g, h2, c.sq_lift, mul_one, c.Tp_zero_right, zero_mul, zero_add,
      c.Tp_add_left] at h1
    exact c.x4_injective h1
  have k0 := key 0
  rw [c.T_zero, c.Tp_zero_left, add_zero, zero_add] at k0
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination key r - k0 - c.T s r * h2

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
