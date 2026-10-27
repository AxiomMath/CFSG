module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTransportMark
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint

private theorem ggSporKRestL11s_isElemAbelian_comap {p : ℕ} {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') {E' : Subgroup K'} (h : IsElemAbelian p E') :
    IsElemAbelian p (E'.comap e.toMonoidHom) :=
  h.comap e.injective

private theorem ggSporKRestL11s_card_comap {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (E' : Subgroup K') (n : ℕ) (h : Nat.card ↥E' = n) :
    Nat.card ↥(E'.comap e.toMonoidHom) = n := by
  have hmap : Subgroup.map e.toMonoidHom (E'.comap e.toMonoidHom) = E' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E'
  rw [← Subgroup.card_map_of_injective (K := E'.comap e.toMonoidHom) (f := e.toMonoidHom)
    e.injective, hmap, h]

private theorem ggSporKRestL11s_controls_comap {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') {E' Y' : Subgroup K'} (h : SporKRestControls E' Y') :
    SporKRestControls (E'.comap e.toMonoidHom) (Y'.comap e.toMonoidHom) := by
  intro x hx hxne g hg
  show e g ∈ Y'
  have hx' : e x ∈ E' := hx
  have hxne' : e x ≠ 1 := fun h1 => hxne (e.injective (by simpa using h1))
  have hg' : (e g)⁻¹ * (e x) * (e g) ∈ Y' := by
    have hconj : e (g⁻¹ * x * g) = (e g)⁻¹ * (e x) * (e g) := by simp
    rw [← hconj]
    exact hg
  exact h (e x) hx' hxne' (e g) hg'

private theorem ggSporKRestL11s_ne_top_comap {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {Y' : Subgroup K'} (h : Y' ≠ ⊤) : Y'.comap e.toMonoidHom ≠ ⊤ := by
  intro htop
  apply h
  have hmap : Subgroup.map e.toMonoidHom (Y'.comap e.toMonoidHom) = Y' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective Y'
  rw [← hmap, htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

private theorem ggSporKRestL11s_sylow_comap {p : ℕ} {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (S' : Sylow p K') :
    ∃ S : Sylow p K, (S : Subgroup K) = (S' : Subgroup K').comap e.toMonoidHom := by
  have hrange : (S' : Subgroup K') ≤ e.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  refine ⟨S'.comapOfInjective e.toMonoidHom e.injective hrange, ?_⟩
  exact Sylow.coe_comapOfInjective S' e.toMonoidHom e.injective hrange

private noncomputable def ggSporKRestL11s_comapMulEquiv {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (Y' : Subgroup K') : ↥(Y'.comap e.toMonoidHom) ≃* ↥Y' :=
  (MulEquiv.subgroupMap e (Y'.comap e.toMonoidHom)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective Y'))

private theorem ggSporKRestL11s_comap_eq_map_symm {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (A : Subgroup K') :
    A.comap e.toMonoidHom = Subgroup.map e.symm.toMonoidHom A := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map]
  exact ⟨fun hx => ⟨e x, hx, by simp⟩, fun hx => by
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hyx]
    simpa using hy⟩

theorem SporKRestCoverOrUnmarked.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {p : ℕ} (h : SporKRestCoverOrUnmarked p K) : SporKRestCoverOrUnmarked p K' := by
  intro E' hE'el hE'card
  have hEel : IsElemAbelian p (E'.comap e.toMonoidHom) :=
    ggSporKRestL11s_isElemAbelian_comap e hE'el
  have hEcard : Nat.card ↥(E'.comap e.toMonoidHom) = p ^ 2 :=
    ggSporKRestL11s_card_comap e E' (p ^ 2) hE'card
  rcases h (E'.comap e.toMonoidHom) hEel hEcard with ⟨x, hxE, hxne, hxgen⟩ | hrest
  · left
    refine ⟨e x, hxE, ?_, SporKRestGenerating.of_mulEquiv e hxgen⟩
    exact fun h1 => hxne (e.injective (by simpa using h1))
  · right
    intro Y' hY'ne hSyl' hCtrl'
    obtain ⟨S', hS'⟩ := hSyl'
    obtain ⟨S, hScoe⟩ := ggSporKRestL11s_sylow_comap e S'
    have hYne : Y'.comap e.toMonoidHom ≠ ⊤ := ggSporKRestL11s_ne_top_comap e hY'ne
    have hSyl : ∃ S : Sylow p K, (S : Subgroup K) ≤ Y'.comap e.toMonoidHom :=
      ⟨S, by rw [hScoe]; exact Subgroup.comap_mono hS'⟩
    have hCtrl : SporKRestControls (E'.comap e.toMonoidHom) (Y'.comap e.toMonoidHom) :=
      ggSporKRestL11s_controls_comap e hCtrl'
    have hunm : SporKRestUnmarked ↥(Y'.comap e.toMonoidHom) :=
      hrest (Y'.comap e.toMonoidHom) hYne hSyl hCtrl
    exact SporKRestUnmarked.of_mulEquiv (ggSporKRestL11s_comapMulEquiv e Y') hunm

theorem SporKRestFi22Exc.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : SporKRestFi22Exc K) : SporKRestFi22Exc K' := by
  intro E' hE'el hE'card Y' hY'ne hSyl' hCtrl' C' hcomp'
  have hEel : IsElemAbelian 5 (E'.comap e.toMonoidHom) :=
    ggSporKRestL11s_isElemAbelian_comap e hE'el
  have hEcard : Nat.card ↥(E'.comap e.toMonoidHom) = 25 :=
    ggSporKRestL11s_card_comap e E' 25 hE'card
  obtain ⟨S', hS'⟩ := hSyl'
  obtain ⟨S, hScoe⟩ := ggSporKRestL11s_sylow_comap e S'
  have hYne : Y'.comap e.toMonoidHom ≠ ⊤ := ggSporKRestL11s_ne_top_comap e hY'ne
  have hSyl : ∃ S : Sylow 5 K, (S : Subgroup K) ≤ Y'.comap e.toMonoidHom :=
    ⟨S, by rw [hScoe]; exact Subgroup.comap_mono hS'⟩
  have hCtrl : SporKRestControls (E'.comap e.toMonoidHom) (Y'.comap e.toMonoidHom) :=
    ggSporKRestL11s_controls_comap e hCtrl'
  have hcomp : IsComponentOf (C'.comap e.toMonoidHom) (Y'.comap e.toMonoidHom) := by
    have hc := isComponentOf_map_mulEquiv' e.symm hcomp'
    rw [ggSporKRestL11s_comap_eq_map_symm e C', ggSporKRestL11s_comap_eq_map_symm e Y']
    exact hc
  have hLie : LieModel
      (↥(C'.comap e.toMonoidHom) ⧸ Subgroup.center ↥(C'.comap e.toMonoidHom))
      .POmegaPlus 4 2 1 :=
    h (E'.comap e.toMonoidHom) hEel hEcard (Y'.comap e.toMonoidHom) hYne hSyl hCtrl
      (C'.comap e.toMonoidHom) hcomp
  have hcenter : Subgroup.map
        (ggSporKRestL11s_comapMulEquiv e C').toMonoidHom
        (Subgroup.center ↥(C'.comap e.toMonoidHom)) =
      Subgroup.center ↥C' :=
    Subgroup.map_center_eq (ggSporKRestL11s_comapMulEquiv e C')
  let eqi : (↥(C'.comap e.toMonoidHom) ⧸
        Subgroup.center ↥(C'.comap e.toMonoidHom)) ≃*
      (↥C' ⧸ Subgroup.center ↥C') :=
    QuotientGroup.congr _ _ (ggSporKRestL11s_comapMulEquiv e C') hcenter
  exact LieModel.of_mulEquiv eqi hLie

end CFSG.StandardType.SporadicShape
