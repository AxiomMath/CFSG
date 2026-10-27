module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Star

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

private theorem s15GapFour_commute_star (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ D.M) (hb : b ∈ D.M)
    (ha0 : a ∈ stabTil V₀ V) (hb0 : b ∈ stabTil V₀ V)
    (ha1 : a ∈ stabTil (v1Sub D.M V₀ V hV L) V) (hb1 : b ∈ stabTil (v1Sub D.M V₀ V hV L) V)
    (hab : actTil V₀ V hV ⟨a, ha0⟩ * actTil V₀ V hV ⟨b, hb0⟩ =
      actTil V₀ V hV ⟨b, hb0⟩ * actTil V₀ V hV ⟨a, ha0⟩) :
    actTil (v1Sub D.M V₀ V hV L) V hV ⟨a, ha1⟩ * actTil (v1Sub D.M V₀ V hV L) V hV ⟨b, hb1⟩ =
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨b, hb1⟩ *
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨a, ha1⟩ := by
  have hM := h.hyp125.pairFacts.le_normalizer
  have hc := fifteen_two_cent D h1217 h hV
  have hs0 : a * b * a⁻¹ * b⁻¹ ∈ stabTil V₀ V :=
    (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ha0 hb0)
      ((stabTil V₀ V).inv_mem ha0)) ((stabTil V₀ V).inv_mem hb0)
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ F11.CTilde D.M V₀ V := by
    rw [mem_cTilde_iff hV hM]
    refine ⟨D.M.mul_mem (D.M.mul_mem (D.M.mul_mem ha hb) (D.M.inv_mem ha)) (D.M.inv_mem hb),
      hs0, ?_⟩
    have : (⟨a * b * a⁻¹ * b⁻¹, hs0⟩ : stabTil V₀ V) =
        ⁅(⟨a, ha0⟩ : stabTil V₀ V), ⟨b, hb0⟩⁆ := rfl
    rw [this, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hab
  rw [← hc, mem_cTilde_iff hV hM] at hmem
  obtain ⟨-, hs1, h1⟩ := hmem
  have : (⟨a * b * a⁻¹ * b⁻¹, hs1⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
      ⁅(⟨a, ha1⟩ : stabTil (v1Sub D.M V₀ V hV L) V), ⟨b, hb1⟩⁆ := rfl
  rw [this, map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem s15GapFour_eq_one_of_centralizes (hAbs : RAbsIrr153) (D : Data G) (h1217 : R1217 D)
    {V₀ V L K₀ : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    {y : MulAut (Vtil V₀ V hV)} (hy : y ∈ Mbar D.M V₀ V hV)
    (hcen : ∀ x ∈ Mbar D.M V₀ V hV,
      x * y * x⁻¹ ∈ centralizer (barSub V₀ V hV K₀ : Set (MulAut (Vtil V₀ V hV)))) :
    y = 1 := by
  have hM := h.hyp125.pairFacts.le_normalizer
  have hM₀ := h.hyp125.pairFacts.le_normalizer₀
  have hM₁ := s15_Infra_le_normalizer_v1Sub (L := L) h.hyp125 hV
  have hc := fifteen_two_cent D h1217 h hV
  obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V hV D.M y).1 hy
  have hg1 : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁ hgM
  have hK₀M : ∀ k ∈ K₀, k ∈ D.M := fun k hk => h.le (hshape.1 hk)
  have hfix : ∀ m ∈ D.M, ∀ w ∈ commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV
      (conjSubgroup K₀ m)), actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ w = w := by
    intro m hm w hw
    have hm0 : m ∈ stabTil V₀ V := le_stabTil hM hM₀ hm
    have hm1 : m ∈ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁ hm
    have hag : m * (g : G) * m⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hm hgM) (D.M.inv_mem hm)
    have hag0 : m * (g : G) * m⁻¹ ∈ stabTil V₀ V := le_stabTil hM hM₀ hag
    have hag1 : m * (g : G) * m⁻¹ ∈ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁ hag
    rw [s15_Infra_barSub_conjSubgroup _ V hV hm1 K₀, s15_Infra_commSub_top_map_conj] at hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
    set B := actTil (v1Sub D.M V₀ V hV L) V hV ⟨m * (g : G) * m⁻¹, hag1⟩ with hB
    have hBeq : B = actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hm1⟩ *
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ *
          (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hm1⟩)⁻¹ := by
      have hsub : (⟨m * (g : G) * m⁻¹, hag1⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
          ⟨m, hm1⟩ * ⟨(g : G), hg1⟩ * ⟨m, hm1⟩⁻¹ := Subtype.ext rfl
      rw [hB, hsub, map_mul, map_mul, map_inv]
    have hcomm1 : ∀ k ∈ barSub (v1Sub D.M V₀ V hV L) V hV K₀, B * k = k * B := by
      intro k hk
      obtain ⟨l, hlK, rfl⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV K₀ k).1 hk
      have hl0 : (l : G) ∈ stabTil V₀ V := le_stabTil hM hM₀ (hK₀M _ hlK)
      have hx : actTil V₀ V hV ⟨m, hm0⟩ ∈ Mbar D.M V₀ V hV :=
        actTil_mem_barSub V₀ V hV hm hm0
      have hlbar : actTil V₀ V hV ⟨(l : G), hl0⟩ ∈ barSub V₀ V hV K₀ :=
        actTil_mem_barSub V₀ V hV hlK hl0
      have hce := Subgroup.mem_centralizer_iff.1 (hcen _ hx) _ hlbar
      have hxg : actTil V₀ V hV ⟨m, hm0⟩ * actTil V₀ V hV ⟨(g : G), le_stabTil hM hM₀ hgM⟩ *
          (actTil V₀ V hV ⟨m, hm0⟩)⁻¹ = actTil V₀ V hV ⟨m * (g : G) * m⁻¹, hag0⟩ := by
        have hsub : (⟨m * (g : G) * m⁻¹, hag0⟩ : stabTil V₀ V) =
            ⟨m, hm0⟩ * ⟨(g : G), le_stabTil hM hM₀ hgM⟩ * ⟨m, hm0⟩⁻¹ := Subtype.ext rfl
        rw [hsub, map_mul, map_mul, map_inv]
      rw [hxg] at hce
      exact s15GapFour_commute_star D h1217 h hV hag (hK₀M _ hlK) hag0 hl0 hag1 l.2 hce.symm
    have hmapeq : (barSub (v1Sub D.M V₀ V hV L) V hV K₀).map (MulAut.conj B).toMonoidHom =
        barSub (v1Sub D.M V₀ V hV L) V hV K₀ := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hk' := hcomm1 k hk
        have : (MulAut.conj B).toMonoidHom k = k := by
          change B * k * B⁻¹ = k
          rw [hk']
          group
        rw [this]
        exact hk
      · intro hx
        refine ⟨x, hx, ?_⟩
        change B * x * B⁻¹ = x
        rw [hcomm1 x hx]
        group
    have hstab : B ∈ stabSub (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) := by
      apply StabLat.mem_stabSub_of_map_eq
      rw [← s15_Infra_commSub_top_map_conj, hmapeq]
    have hBz : B z = z :=
      hAbs (vStar D.M V₀ V hV L) (s15_Infra_vtil_sq_eq_one _ V hV) ↥(barSub V₀ V hV K₀)
        (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
        (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) hperf B hstab hcomm1 z hz
    change actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩
        ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hm1⟩)⁻¹ z) =
      (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hm1⟩)⁻¹ z
    have h2 : actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ *
        (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hm1⟩)⁻¹ =
          (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hm1⟩)⁻¹ * B := by
      rw [hBeq]
      group
    have h3 := congrArg (fun f : MulAut (vStar D.M V₀ V hV L) => f z) h2
    simp only [MulAut.mul_apply] at h3
    rw [h3, hBz]
  have hone : actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ = 1 := by
    let F : Subgroup (vStar D.M V₀ V hV L) :=
      { carrier := {w | actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ w = w}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, ha, hb]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [map_inv, ha] }
    have hle : sSup {Z : Subgroup (vStar D.M V₀ V hV L) | ∃ m ∈ D.M,
        Z = commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m))} ≤ F := by
      refine sSup_le ?_
      rintro Z ⟨m, hm, rfl⟩ w hw
      exact hfix m hm w hw
    rw [hshape.2.2.2.2.2] at hle
    ext w
    exact hle (Subgroup.mem_top w)
  have hmem : (g : G) ∈ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V :=
    (mem_cTilde_iff hV hM).2 ⟨hgM, hg1, hone⟩
  rw [hc, mem_cTilde_iff hV hM] at hmem
  obtain ⟨-, hst, h0⟩ := hmem
  exact h0

end Star

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
