module

public import CFSG.Timmesfeld.ARS.CaseOADegSpCent
public import CFSG.Timmesfeld.ARS.CaseOADegGraph
public import CFSG.Timmesfeld.ARS.CaseOANSLAssembleC
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
public import CFSG.Fischer.Assembly
public import CFSG.Fischer.Classification.Milestone
public import CFSG.Fischer.NoF25.Local
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Timmesfeld.ARS.Sec12MeetsLines
public import CFSG.Timmesfeld.ARS.Sec12Three

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Matrix Transvection CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
  CaseM CaseOANSL Transvection.Pres

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOADeg

section Graph

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_graphHom_rootGroup_single_zero :
    (Symplectic.rootGroup 2 K (Pi.single 0 1)).map graphHom =
      Symplectic.rootGroup 2 K (Pi.single 1 1) := by
  ext x
  rw [mem_rootGroup_iff_sp (mem_roots_single 1)]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_sp (mem_roots_single 0)).1 hy
    exact ⟨c, by rw [graphHom_x_single_zero,
      x_eq_spElt (a := Sum.inl 1) (b := Sum.inl 1) (by decide) (by decide)]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Sp.x 2 K (Pi.single 0 1) c, (mem_rootGroup_iff_sp (mem_roots_single 0)).2 ⟨c, rfl⟩,
      by rw [graphHom_x_single_zero,
        x_eq_spElt (a := Sum.inl 1) (b := Sum.inl 1) (by decide) (by decide)]⟩

theorem map_graphHom_rootGroup_neg_single_zero :
    (Symplectic.rootGroup 2 K (-Pi.single 0 1)).map graphHom =
      Symplectic.rootGroup 2 K (-Pi.single 1 1) := by
  have hn : ∀ i : Fin 2, (-Pi.single i 1 : Fin 2 → ℤ) ∈
      RootSystem.roots (isFiniteType_cartanC 2) ∅ := fun i =>
    (RootSystem.ofCartan (isFiniteType_cartanC 2) ∅).neg_mem _ (mem_roots_single i)
  ext x
  rw [mem_rootGroup_iff_sp (hn 1)]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_sp (hn 0)).1 hy
    exact ⟨c, by rw [graphHom_x_neg_single_zero,
      x_eq_spElt (a := Sum.inr 1) (b := Sum.inr 1) (by decide) (by decide)]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Sp.x 2 K (-Pi.single 0 1) c, (mem_rootGroup_iff_sp (hn 0)).2 ⟨c, rfl⟩,
      by rw [graphHom_x_neg_single_zero,
        x_eq_spElt (a := Sum.inr 1) (b := Sum.inr 1) (by decide) (by decide)]⟩

theorem exists_graphHom_eq_spElt {p q : Fin 2 ⊕ Fin 2} (hpq : q ≠ Sum.swap p) (c : K) :
    ∃ y, graphHom y = spElt p q c := by
  have hsq : sqrtF (c ^ 2) = c := by
    rw [sqrtF, ← frobenius_def, frobeniusEquiv_symm_apply_frobenius]
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp at hpq
  · exact ⟨spElt (.inl 0) (.inl 1) c, by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair]⟩
  · exact ⟨spElt (.inl 0) (.inl 0) (c ^ 2), by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair, hsq]⟩
  · exact ⟨spElt (.inl 0) (.inl 0) (c ^ 2), by
      rw [graphHom_spElt (by decide)]
      simp [graphElt, graphPair, hsq,
        spElt_comm (n := 2) (a := .inl 0) (b := .inl 1) (by decide) c]⟩
  · exact ⟨spElt (.inl 0) (.inr 1) c, by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair]⟩
  · exact ⟨spElt (.inl 1) (.inl 1) (c ^ 2), by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair, hsq]⟩
  · exact ⟨spElt (.inr 1) (.inr 1) (c ^ 2), by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair, hsq]⟩
  · exact ⟨spElt (.inr 1) (.inr 1) (c ^ 2), by
      rw [graphHom_spElt (by decide)]
      simp [graphElt, graphPair, hsq,
        spElt_comm (n := 2) (a := .inl 1) (b := .inr 0) (by decide) c]⟩
  · exact ⟨spElt (.inl 1) (.inl 1) (c ^ 2), by
      rw [graphHom_spElt (by decide)]
      simp [graphElt, graphPair, hsq,
        spElt_comm (n := 2) (a := .inl 0) (b := .inr 1) (by decide) c]⟩
  · exact ⟨spElt (.inr 0) (.inr 1) c, by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair]⟩
  · exact ⟨spElt (.inr 0) (.inr 0) (c ^ 2), by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair, hsq]⟩
  · exact ⟨spElt (.inr 0) (.inr 0) (c ^ 2), by
      rw [graphHom_spElt (by decide)]
      simp [graphElt, graphPair, hsq,
        spElt_comm (n := 2) (a := .inr 0) (b := .inr 1) (by decide) c]⟩
  · exact ⟨spElt (.inl 1) (.inr 0) c, by
      rw [graphHom_spElt (by decide)]; simp [graphElt, graphPair]⟩

theorem graphHom_surjective : Function.Surjective (graphHom (K := K)) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro g _
  have hg : g ∈ ⨆ γ ∈ RootSystem.roots (isFiniteType_cartanC 2) ∅, Symplectic.rootGroup 2 K γ := by
    rw [(Symplectic.isCTGroupDatum 2 K).iSup_eq_top]
    exact Subgroup.mem_top g
  have hle : (⨆ γ ∈ RootSystem.roots (isFiniteType_cartanC 2) ∅, Symplectic.rootGroup 2 K γ) ≤
      graphHom.range := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hγ
    have hγe : toStd 2 γ = rt (sp r).1 (sp r).2 := by rw [rt_sp, hr]
    rw [show Symplectic.rootGroup 2 K γ = (rootDatum 2 K).rootGroup γ from rfl,
      rootGroup_eq_range_spEltHom (sp_ne r) hγe]
    rintro _ ⟨c, rfl⟩
    obtain ⟨y, hy⟩ := exists_graphHom_eq_spElt (sp_ne r) (Multiplicative.toAdd c)
    exact ⟨y, hy.trans (spEltHom_apply _ _ c).symm⟩
  exact hle hg

theorem graphHom_bijective : Function.Bijective (graphHom (K := K)) :=
  have : Finite (StatedSp 2 K) := Subtype.finite
  ⟨Finite.injective_iff_surjective.2 graphHom_surjective, graphHom_surjective⟩

end Graph

namespace DegOA

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)} (hD : DegOA R A A₀ Δ₁ Δ₂)
include hD

theorem output_sp {f : ℕ} (hf : 1 ≤ f) (hcard : ∀ X ∈ Δ₁, Nat.card X = 2 ^ f)
    (Φ : StatedSp 2 (GaloisField 2 f) →* G) (hΦ : Function.Injective Φ)
    (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g, X = (conjSub ((Symplectic.rootDatum 2
      (GaloisField 2 f)).rootGroup (Pi.single (1 : Fin 2) 1)) g).map Φ) :
    Output G R := by
  set GF := GaloisField 2 f
  have := hD.hyp.finite
  have hR := hD.hyp.root
  have hiso := hD.hyp.noIsolated
  have hGF : Nat.card GF = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨E, C, P, Q, hfr, h0, h1, h2⟩ := hD.exists_subframe
  obtain ⟨g, hg⟩ := exists_aligned_sp₂ Φ hΦ (P := ![P 2, P 1]) (Q := ![Q 2, Q 1])
    (fun i => by fin_cases i; exacts [(hΔ _).1 h2.1, (hΔ _).1 h1.1])
    (fun i => by fin_cases i; exacts [(hΔ _).1 h2.2, (hΔ _).1 h1.2])
    (fun i => by
      fin_cases i
      exacts [(hfr.opposite 2).not_commuting (hR.ne_bot _ (hfr.memP 2).1.1.1),
        (hfr.opposite 1).not_commuting (hR.ne_bot _ (hfr.memP 1).1.1.1)])
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exacts [hfr.commuting 2 1 (by decide), hfr.commuting 1 2 (by decide)])
  set Φ' := Φ.comp (MulAut.conj g).toMonoidHom with hΦ'def
  have hΦ' : Function.Injective Φ' := hΦ.comp (MulAut.conj g).injective
  have hrange' : Φ'.range = gen Δ₁ := by
    rw [hΦ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj g).surjective,
      ← MonoidHom.range_eq_map, hrange]
  have hΔ' : ∀ X : Subgroup G, X ∈ Δ₁ ↔
      ∃ g', X = (conjSub (Symplectic.rootGroup 2 GF (Pi.single 1 1)) g').map Φ' := by
    have e : ∀ (X₀ : Subgroup (StatedSp 2 GF)) (g' : StatedSp 2 GF),
        (conjSub X₀ g').map Φ' = (conjSub X₀ (g * g')).map Φ := fun X₀ g' => by
      rw [hΦ'def, ← Subgroup.map_map, conjSub_mul]
    intro X
    refine ⟨fun hX => ?_, fun ⟨g', hg'⟩ => (hΔ X).2 ⟨g * g', by rw [hg', e]; rfl⟩⟩
    obtain ⟨g'', rfl⟩ := (hΔ X).1 hX
    exact ⟨g⁻¹ * g'', by rw [e, mul_inv_cancel_left]; rfl⟩
  have hP' : ∀ i, (Symplectic.rootGroup 2 GF (longC2 i)).map Φ' = ![P 2, P 1] i :=
    fun i => (hg i).1
  have hQ' : ∀ i, (Symplectic.rootGroup 2 GF (-longC2 i)).map Φ' = ![Q 2, Q 1] i :=
    fun i => (hg i).2
  set Θ : StatedSp (1 + 1) GF →* G := Φ'.comp graphHom with hΘ
  have hΘrange : Θ.range = gen Δ₁ := by
    rw [hΘ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 graphHom_surjective,
      ← MonoidHom.range_eq_map, hrange']
  obtain ⟨hF', hEF, hcfg⟩ := hfr.isConfig hD.sec12
  have e0 := hcfg.edge 0 1 (by decide)
  have e1 := hcfg.edge 1 2 (by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at e0 e1
  obtain ⟨φr, hφinj, hφU, hφL⟩ := Sp.rankOne (n := 2) (F := GF) ⟨0, by omega⟩
  set ρX := Θ.comp φr with hρX
  have hρXinj : Function.Injective ρX :=
    hΦ'.comp (graphHom_bijective.1.comp hφinj)
  have hρXU : (upperUnipotent GF).map ρX = P 1 := by
    rw [hρX, ← Subgroup.map_map, map_upper_eq_rootGroup hφU, hΘ, ← Subgroup.map_map]
    erw [map_graphHom_rootGroup_single_zero]
    rw [← longC2_one, hP' 1]
    rfl
  have hρXL : (lowerUnipotent GF).map ρX = Q 1 := by
    rw [hρX, ← Subgroup.map_map, map_lower_eq_rootGroup hφL, hΘ, ← Subgroup.map_map]
    erw [map_graphHom_rootGroup_neg_single_zero]
    rw [← longC2_one, hQ' 1]
    rfl
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) => hD.mem_leviSet₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) => hD.mem_leviSet₂ hX
  obtain ⟨ρ, hρ2, hρ, hedge⟩ := Linear.exists_chain hR hiso (m := 3)
    (A := ![P 0, E, P 1]) (B := ![Q 0, ⁅A₀, C⁆, Q 1])
    (fun i => by fin_cases i; exacts [(hl₂ h0.1).1.1, hfr.memE.1.1.1, (hl₁ h1.1).1.1])
    (fun i => by fin_cases i; exacts [(hl₂ h0.2).1.1, hF'.1.1.1, (hl₁ h1.2).1.1])
    (fun i => by fin_cases i; exacts [hfr.opposite 0, hEF, hfr.opposite 1])
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exacts [e0, e1])
    (k₀ := 2) (hcard _ h1.1) hρXinj hρXU hρXL
  obtain ⟨φ₀, hφ₀⟩ := hedge 0 1 rfl
  obtain ⟨φ₁, hφ₁⟩ := hedge 1 2 rfl
  have hρ0 : (ρ 0).range = P 0 ⊔ Q 0 := range_eq_sup_of_map (hρ 0).2.1 (hρ 0).2.2
  have hρ1 : (ρ 1).range = E ⊔ ⁅A₀, C⁆ := range_eq_sup_of_map (hρ 1).2.1 (hρ 1).2.2
  have hP0Q0 : P 0 ≠ Q 0 := (hfr.opposite 0).1
  have hgen₂ : gen Δ₂ = P 0 ⊔ Q 0 :=
    ((hD.sl2.opposite_of_ne hR hD.subset_R₂ h0.1 h0.2 hP0Q0).2).symm
  have hcentJ : ∀ d : GF, (Θ (Sp.x 2 GF (Pi.single 1 1) d) ∈ Subgroup.centralizer (E : Set G) ∧
        Θ (Sp.x 2 GF (Pi.single 1 1) d) ∈ Subgroup.centralizer (C : Set G)) ∧
      (Θ (Sp.x 2 GF (-Pi.single 1 1) d) ∈ Subgroup.centralizer (E : Set G) ∧
        Θ (Sp.x 2 GF (-Pi.single 1 1) d) ∈ Subgroup.centralizer (C : Set G)) := by
    intro d
    have hx1 : Θ (Sp.x 2 GF (Pi.single 1 1) d) =
        Φ' (spElt (Sum.inl 0) (Sum.inr 1) (sqrtF d)) := by
      rw [hΘ, MonoidHom.comp_apply, graphHom_x_single_one]
    have hx2 : Θ (Sp.x 2 GF (-Pi.single 1 1) d) =
        Φ' (spElt (Sum.inl 1) (Sum.inr 0) (sqrtF d)) := by
      rw [hΘ, MonoidHom.comp_apply, graphHom_x_neg_single_one]
    obtain ⟨hE1, hC1⟩ := hD.commute_short hfr h0 hΦ' hrange' hΔ' hP' hQ'
      (Or.inl ⟨rfl, rfl⟩) (sqrtF d)
    obtain ⟨hE2, hC2⟩ := hD.commute_short hfr h0 hΦ' hrange' hΔ' hP' hQ'
      (Or.inr ⟨rfl, rfl⟩) (sqrtF d)
    rw [hx1, hx2]
    exact ⟨⟨Subgroup.mem_centralizer_iff.2 fun e he => (hE1 e he).symm.eq,
        Subgroup.mem_centralizer_iff.2 fun x hx => (hC1 x hx).symm.eq⟩,
      ⟨Subgroup.mem_centralizer_iff.2 fun e he => (hE2 e he).symm.eq,
        Subgroup.mem_centralizer_iff.2 fun x hx => (hC2 x hx).symm.eq⟩⟩
  have hV₁A₀ : ∀ k, Θ k ∈ Subgroup.centralizer (A₀ : Set G) := fun k =>
    levi_le_centralizer_right A A₀ (hD.gen₁_le_levi (hΘrange ▸ ⟨k, rfl⟩))
  have hg0 : ∀ g, ρ 0 g ∈ gen Δ₂ := fun g => by
    have : ρ 0 g ∈ (ρ 0).range := ⟨g, rfl⟩
    rw [hρ0] at this
    exact sup_le (le_gen h0.1) (le_gen h0.2) this
  have key : ∀ g, ∀ y : G, y ∈ Subgroup.centralizer (E : Set G) →
      y ∈ Subgroup.centralizer (C : Set G) → y ∈ Subgroup.centralizer (A₀ : Set G) →
        Commute (ρ 1 g) y := by
    intro g y hyE hyC hyA
    have hle : E ⊔ ⁅A₀, C⁆ ≤ Subgroup.centralizer ({y} : Set G) :=
      sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hyE b hb))
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (mem_centralizer_commutator hyA hyC) z hz))
    have hg : ρ 1 g ∈ E ⊔ ⁅A₀, C⁆ := by
      rw [← hρ1]
      exact ⟨g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  have H : FrameHyp (n := 1) Θ (RingEquiv.refl GF) φ₀ φ₁ (ρ 0) (ρ 1) :=
    { φ₀01 := fun c => (hφ₀ c).1
      φ₀10 := fun c => (hφ₀ c).2.1
      φ₀12 := fun c => (hφ₀ c).2.2.1
      φ₀21 := fun c => (hφ₀ c).2.2.2
      φ₁01 := fun c => (hφ₁ c).1
      φ₁10 := fun c => (hφ₁ c).2.1
      φ₁12 := fun c => by
        rw [(hφ₁ c).2.2.1, hρ2, hρX, MonoidHom.comp_apply, LevisExtras.tv01_eq_sl2Upper, hφU]
        rfl
      φ₁21 := fun c => by
        rw [(hφ₁ c).2.2.2, hρ2, hρX, MonoidHom.comp_apply, LevisExtras.tv10_eq_sl2Lower, hφL]
        rfl
      V := fun g b => (hD.commuting_gen _ (hΘrange ▸ ⟨b, rfl⟩) (ρ 0 g) (hg0 g)).symm
      E := fun j hj g d => by
        have hj1 : j = 1 := by
          fin_cases j
          · simp at hj
          · rfl
        subst hj1
        exact ⟨key g _ (hcentJ d).1.1 (hcentJ d).1.2 (hV₁A₀ _),
          key g _ (hcentJ d).2.1 (hcentJ d).2.2 (hV₁A₀ _)⟩ }
  have htop : levi R A A₀ ⊔ E ⊔ ⁅A₀, C⁆ = ⊤ :=
    CaseOA.levi_sup_sup_eq_top hD.hyp hD.mem hD.ne hD.max hD.opp hfr.memE hF'
  rw [CaseOA.levi_eq_sup hD.hyp hD.mem hD.ne hD.opp hD.card_comps hD.comp₁ hD.comp₂
    hD.comp_ne] at htop
  have hgen : (ρ 0).range ⊔ (ρ 1).range ⊔ Θ.range = ⊤ := by
    rw [hρ0, hρ1, hΘrange, ← hgen₂, eq_top_iff, ← htop]
    exact sup_le (sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_left.trans (le_sup_right.trans le_sup_left)))
      (le_sup_right.trans (le_sup_right.trans le_sup_left))
  have hnt : ρ 0 (tv 0 1 1) ≠ 1 := by
    intro h1'
    have h1'' := (hρ 0).1 (h1'.trans (map_one (ρ 0)).symm)
    rw [LevisExtras.tv01_eq_sl2Upper] at h1''
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) GF =>
      (M : Matrix (Fin 2) (Fin 2) GF) 0 1) h1''
    simp [sl2Upper] at this
  have hframe := (H.isCNFrame le_rfl hgen hnt).isCTFrame
  have hadm : StatedLieAdmissible .PSp (1 + 3) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun e' => absurd (congrArg Prod.fst e') (by omega)⟩
  have hCT := CurtisTits.curtisTitsConclusion_symplectic (n := 1 + 3) (F := GF) hadm hGF
    (by omega)
  have hL := leviConePresented_symplectic (1 + 3) GF
  refine Output.of_nonSimplyLaced
    (.inl ⟨1 + 3, f, by omega, hf, hframe.lieModel hCT hL hD.hyp.center⟩) ?_
  refine .inr (hframe.nslFrame hCT hL (Symplectic.isCTGroupDatum _ _)
    (Symplectic.steinbergExtras _ _) rfl (NSLType.symplecticDatum (by omega) _)
    (fun _ hγ => RankTwo.isPGroup_of_param Sp.isParametrization hγ)
    NSLFrameData.comm_symplecticDatum (hl₂ h0.1).1.1 ?_ ?_ (hfr.opposite 0))
  · have e' : oaPsi Θ (RingEquiv.refl GF) φ₀ φ₁ (a0 1) = fun c => ρ 0 (tv 0 1 c) :=
      funext H.v_a0
    refine Eq.symm ((RankTwo.range_phiOf Sp.isParametrization _ (mem_roots_single _)).trans ?_)
    show Set.range (oaPsi Θ (RingEquiv.refl GF) φ₀ φ₁ (a0 1)) = _
    rw [e', Linear.range_tv_upper, (hρ 0).2.1]
    rfl
  · have e' : oaPsi Θ (RingEquiv.refl GF) φ₀ φ₁ (-a0 1) = fun c => ρ 0 (tv 1 0 c) :=
      funext H.v_na0
    refine Eq.symm ((RankTwo.range_phiOf Sp.isParametrization _
      ((RootSystem.ofCartan (isFiniteType_cartanC (1 + 3)) ∅).neg_mem _
        (mem_roots_single _))).trans ?_)
    show Set.range (oaPsi Θ (RingEquiv.refl GF) φ₀ φ₁ (-a0 1)) = _
    rw [e', Linear.range_tv_lower, (hρ 0).2.2]
    rfl

end DegOA

end CaseOADeg

end CFSG.Timmesfeld.ARS
