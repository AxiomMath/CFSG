module

public import CFSG.Quasithin.Background.SimsF5Mark

public section

namespace CFSG.Quasithin.RonanF438

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix CFSG.Open CFSG.Fischer CFSG.Fischer.Classification.Beta U42F431
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.Quasithin.SimsF5
open CFSG.Quasithin.H13.F431.U42 (lineSet L0S)
open scoped Pointwise

theorem exists_markIso_nofb {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} [Gp.Normal] (hcent : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hne : Gp ≠ ⊤) {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 4) {σ : K →+* K}
    (hσ : ∀ x, σ x = x ^ 2) (m : ↥Gp ≃* StatedProj (StatedSU 4 2 K))
    (point plane : Submodule K (Fin 4 → K)) (hp1 : Module.finrank K point = 1)
    (hp2 : Module.finrank K plane = 2) (hpp : point ≤ plane)
    (hiso : ∀ v ∈ plane, ∀ w ∈ plane, U42Hermitian K v w = 0)
    (hpar1 : U42ParabolicAt Gp (Gp ⊓ M₁) m point) (hpar2 : U42ParabolicAt Gp (Gp ⊓ M₂) m plane) :
    ∃ Θ : E ≃* CFSG.Quasithin.H13.F431.U42Aut.Ah,
      (∀ x : E, Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.Yh ↔ x ∈ Gp) ∧
      (∀ x : E, x ∈ Gp → (Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P1h ↔ x ∈ M₁)) ∧
      (∀ x : E, x ∈ Gp → (Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P2h ↔ x ∈ M₂)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hKcard, F4.card]
  let φ : K ≃+* F4 := FiniteField.ringEquivOfCardEq hcardK
  have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [hσ, hσ]; exact mk_K_sq_sq φ x
  have hGp : Nat.card ↥Gp = 25920 := by
    have h := CFSG.ComponentClassification.UnbalancingLocal.card_psu_four_two (K := K)
      (by rw [hKcard]; norm_num)
    rw [Nat.card_congr m.toEquiv]
    exact h
  have htau := mk_exists_rho_tau φ hσ hσσ m
  obtain ⟨hρrange, hρinj⟩ := mk_range_eq hGp (mkRho φ m) htau
  let ρ₀ : ↥Gp ≃* ↥QP45.originalSubgroup :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  have hisopt : ∀ v ∈ point, U42Hermitian K v v = 0 := fun v hv => hiso v (hpp hv) v (hpp hv)
  obtain ⟨j₀, hj₀⟩ := mk_point_set φ hp1 hisopt
  obtain ⟨a, b, hab, hort, hplane⟩ := mk_plane_set φ hp2 hiso
  obtain ⟨m₀, hm₀⟩ := mk_line_set hab hort
  have hSpoint := mk_S_point φ hj₀
  have hSplane : {k : Fin 45 | uPt k ∈ mkV φ plane} = lineSet (lnTab.getD m₀ []) := by
    ext k
    exact (hplane (uPt k)).trans (hm₀ k)
  have hj₀line : j₀.val ∈ lnTab.getD m₀ [] := by
    have h1 : j₀ ∈ {k : Fin 45 | uPt k ∈ mkV φ plane} := hpp ((hj₀ _).2 ⟨1, by simp⟩)
    rw [hSplane] at h1
    exact h1
  obtain ⟨r, hr⟩ := mk_mem_line m₀ j₀ hj₀line
  obtain ⟨δ, hδP, hδ0, hδL⟩ := mk_flag_move m₀ r
  have hδj : (δ : Equiv.Perm (Fin 45)) 0 = j₀ := by
    rw [hδ0]
    exact hr
  have hδL' : ((δ⁻¹ : Equiv.Perm (Fin 45)) : Fin 45 → Fin 45) '' lineSet (lnTab.getD m₀ []) =
      L0S := by
    rw [← hδL, ← Set.image_comp]
    have h1 : ((δ⁻¹ : Equiv.Perm (Fin 45)) : Fin 45 → Fin 45) ∘ (δ : Fin 45 → Fin 45) = id := by
      funext x
      simp
    rw [h1, Set.image_id]
  have hδinvP : δ⁻¹ ∈ QP45.originalSubgroup := QP45.originalSubgroup.inv_mem hδP
  let y : ↥QP45.originalSubgroup := ⟨δ⁻¹, hδinvP⟩
  let ψ : ↥Gp ≃* ↥QP45.originalSubgroup := ρ₀.trans (MulAut.conj y)
  have hψ : ∀ g : ↥Gp, ((ψ g : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) =
      δ⁻¹ * mkRho φ m g * δ⁻¹⁻¹ := fun g => rfl
  obtain ⟨Θ, -, hΘagree, hΘP⟩ := mk_exists_theta hcent hne hGp ψ
  refine ⟨Θ, fun x => (Subgroup.mem_subgroupOf).trans (hΘP x), ?_, ?_⟩
  ·
    intro x hx
    have hg := hΘagree ⟨x, hx⟩
    have h1 : x ∈ M₁ ↔ mkRho φ m ⟨x, hx⟩ j₀ = j₀ := by
      have h2 := hpar1.2 ⟨x, hx⟩
      have h3 : x ∈ M₁ ↔ x ∈ Gp ⊓ M₁ := ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
      refine h3.trans (h2.trans ?_)
      obtain ⟨M₀, hM₀⟩ := QuotientGroup.mk_surjective (m ⟨x, hx⟩)
      constructor
      · rintro ⟨M, hM, hst⟩
        have h4 := (mk_par_equiv φ m point hisopt ⟨x, hx⟩ M hM).1 hst
        rw [hSpoint] at h4
        simpa using h4
      · intro h
        refine ⟨M₀, hM₀.symm, ?_⟩
        apply (mk_par_equiv φ m point hisopt ⟨x, hx⟩ M₀ hM₀.symm).2
        rw [hSpoint]
        simpa using h
    have h2 : Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P1h ↔
        ((Θ x : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) 0 = 0 :=
      MulAction.mem_stabilizer_iff
    rw [h2, h1, hg, hψ]
    have hδinv : δ⁻¹ j₀ = 0 := Equiv.Perm.inv_eq_iff_eq.2 hδj.symm
    have h3 : δ⁻¹⁻¹ 0 = j₀ := by rw [inv_inv]; exact hδj
    show δ⁻¹ ((mkRho φ m ⟨x, hx⟩) (δ⁻¹⁻¹ 0)) = 0 ↔ _
    rw [h3]
    constructor
    · intro h
      exact δ⁻¹.injective (h.trans hδinv.symm)
    · intro h
      rw [h]
      exact hδinv
  ·
    intro x hx
    have hg := hΘagree ⟨x, hx⟩
    have hisop : ∀ v ∈ plane, U42Hermitian K v v = 0 := fun v hv => hiso v hv v hv
    have h1 : x ∈ M₂ ↔ (mkRho φ m ⟨x, hx⟩ : Equiv.Perm (Fin 45)) ''
        lineSet (lnTab.getD m₀ []) = lineSet (lnTab.getD m₀ []) := by
      have h2 := hpar2.2 ⟨x, hx⟩
      have h3 : x ∈ M₂ ↔ x ∈ Gp ⊓ M₂ := ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
      refine h3.trans (h2.trans ?_)
      obtain ⟨M₀, hM₀⟩ := QuotientGroup.mk_surjective (m ⟨x, hx⟩)
      constructor
      · rintro ⟨M, hM, hst⟩
        have h4 := (mk_par_equiv φ m plane hisop ⟨x, hx⟩ M hM).1 hst
        rw [hSplane] at h4
        exact h4
      · intro h
        refine ⟨M₀, hM₀.symm, ?_⟩
        apply (mk_par_equiv φ m plane hisop ⟨x, hx⟩ M₀ hM₀.symm).2
        rw [hSplane]
        exact h
    have h2 : Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P2h ↔
        ((Θ x : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) '' L0S = L0S :=
      MulAction.mem_stabilizer_iff.trans (by rw [mk_smul_set_eq])
    rw [h2, h1, hg, hψ]
    have h3 : (δ⁻¹⁻¹ : Equiv.Perm (Fin 45)) '' L0S = lineSet (lnTab.getD m₀ []) := by
      rw [inv_inv]
      exact hδL
    simp only [Equiv.Perm.coe_mul, Set.image_comp]
    rw [h3, ← hδL']
    exact Set.image_eq_image δ⁻¹.injective

end CFSG.Quasithin.RonanF438
