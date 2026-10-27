module

public import CFSG.RankThree.GF2n.Smith81.S81NBridge
public import CFSG.RankThree.GF2n.Smith81.S81NModel1
public import CFSG.RankThree.GF2n.Smith81.S81NModel2
public import CFSG.RankThree.GF2n.Smith81.S81NModel3
public import CFSG.RankThree.GF2n.Smith81.S81NInvol
public import CFSG.RankThree.GF2n.Smith81.S81NCond
public import CFSG.RankThree.GF2n.Smith81.S81BNForm
public import CFSG.RankThree.GF2n.Smith81.S81BElem
public import CFSG.RankThree.GF2n.Smith81.S81BTacit

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge

section Transport

variable {G : Type} [Group G] {M Q Z B : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)}

theorem EGeom.EUniData.transport (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    {g : GL (Fin 6) K} (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) :
    EUniData M Q Z B M₀ (ψ.trans (rhoEquiv K g))
      ((MulAut.conj (rhoEquiv K g)).toMonoidHom.comp φ) (Gam K) (p0 K) (U0 K) := by
  have hcΓ : rhoEquiv K g ∈ Gam K :=
    Subgroup.mem_map_of_mem _ (CFSG.Open.StatedAPI.mem_statedSL_of_det hg)
  generalize rhoEquiv K g = c at hcΓ ⊢
  refine ⟨?_, ?_, d.le_normalizer, ?_, ?_⟩
  · rw [MonoidHom.range_comp, d.range]
    ext v
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mul_mem (mul_mem hcΓ ha) (inv_mem hcΓ)
    · intro hv
      exact ⟨c⁻¹ * v * c, mul_mem (mul_mem (inv_mem hcΓ) hv) hcΓ, by group⟩
  · intro s
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← d.ker s]
    constructor
    · intro h
      have h1 : c * φ s = c := mul_inv_eq_one.mp h
      exact mul_left_cancel (h1.trans (mul_one c).symm)
    · intro h
      rw [h]
      group
  · intro s x hx
    have h := d.equivariant s x hx
    simp only [LinearEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.coe_coe]
    rw [h]
    simp
  · intro A hA hAQ hAZ
    obtain ⟨g₀, hg₀, himg, hU⟩ := d.point A hA hAQ hAZ
    refine ⟨c * g₀, mul_mem hcΓ hg₀, ?_, ?_⟩
    · ext v
      simp only [Set.mem_image, SetLike.mem_coe, LinearEquiv.trans_apply]
      constructor
      · rintro ⟨a, haA, rfl⟩
        have : ψ (M₀.π a) ∈ (fun a : G => ψ (M₀.π a)) '' (A : Set G) := ⟨a, haA, rfl⟩
        rw [himg] at this
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp this
        refine Submodule.mem_span_singleton.mpr ⟨s, ?_⟩
        rw [← hs]
        simp
      · intro hv
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
        have : s • g₀ (p0 K) ∈ (fun a : G => ψ (M₀.π a)) '' (A : Set G) := by
          rw [himg]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        obtain ⟨a, haA, ha⟩ := this
        refine ⟨a, haA, ?_⟩
        rw [show ψ (M₀.π a) = s • g₀ (p0 K) from ha]
        simp
    · intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := EGeom.mem_conjSub.mp hu
      obtain ⟨s, hsQ, hsφ⟩ := hU (g₀ * u₀ * g₀⁻¹) (EGeom.mem_conjSub.mpr ⟨u₀, hu₀, rfl⟩)
      refine ⟨s, hsQ, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hsφ]
      group

end Transport

section Main

theorem e3l28Cond_of_uniform
    (hFE1 : Smith24E3LUniformStatement) : E3L28CondStatement := by
  intro G _ _ M Q Z B IH hc h3L X x hs hQX
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have h12 := smith_1_12 hs
  obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3L K γ M₀ hD
  have hXle : X ≤ H0 M Z := h12.1
  have hX2 : IsPGroup 2 X := fun y => ⟨1, Subtype.ext (by
    have := hs.X_sq y y.2
    simpa [pow_two] using this)⟩
  have hNQ := normQuotE3L_of_uniform hFE1 G M Q Z B IH hc h3L X hXle hX2
  have hcardX : Nat.card X = Nat.card Z := IsZConjugate.card_eq hs.conj
  have hcard4 : 4 ≤ Nat.card X := hcardX ▸ H.q4
  have hone : 1 < Nat.card ↥(X ⊓ Lgen M (LB M Q B)) := by omega
  obtain ⟨x₀, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hone)
  obtain ⟨hx₀X, hx₀L⟩ := Subgroup.mem_inf.mp x₀.2
  have hx₀1' : (x₀ : G) ≠ 1 := fun h => hx₀1 (Subtype.ext (h.trans (Subgroup.coe_one _).symm))
  have hx₀M : (x₀ : G) ∈ M := (Subgroup.mem_inf.mp (h12.1 hx₀X)).1
  have hx₀Q : (x₀ : G) ∉ Q := fun h => by
    have : (x₀ : G) ∈ X ⊓ Q := ⟨hx₀X, h⟩
    rw [h12.2, Subgroup.mem_bot] at this
    exact hx₀1' this
  have hs₀ : Sit M Q Z X (x₀ : G) := ⟨H, hs.conj, hx₀X, hx₀1', hx₀M, hx₀Q⟩
  have hmem : φ ⟨(x₀ : G), hx₀L⟩ ∈ Gam K := by
    rw [← d.range]
    exact ⟨_, rfl⟩
  obtain ⟨t, htS, htφ⟩ := Subgroup.mem_map.mp hmem
  have hdet : (t : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp htS
  have hsq : rhoEquiv K t * rhoEquiv K t = 1 := by
    rw [htφ, ← map_mul]
    have : (⟨(x₀ : G), hx₀L⟩ : Lgen M (LB M Q B)) * ⟨(x₀ : G), hx₀L⟩ = 1 :=
      Subtype.ext hs₀.x_sq
    rw [this, map_one]
  have h2 : rho K t * rho K t = 1 := by
    refine LinearMap.ext fun ξ => ?_
    exact congrArg (fun e : Cube K ≃ₗ[K] Cube K => e ξ) hsq
  have h1 : rho K t ≠ 1 := by
    intro h
    have : rhoEquiv K t = 1 := LinearEquiv.ext fun ξ =>
      congrArg (fun f : Cube K →ₗ[K] Cube K => f ξ) h
    exact hx₀Q ((d.ker ⟨(x₀ : G), hx₀L⟩).mp (by rw [← htφ, this]))
  obtain ⟨t', g, hdet', hρ', hdetg, hk⟩ := exists_conj_tInv hdet h2 h1
  have d' := d.transport hdetg
  have hform := smith24E3LFormStatement_holds G M Q Z B IH hc.toRemCfg h3L K γ M₀ hD _ _ d'
  have hφ' : ((MulAut.conj (rhoEquiv K g)).toMonoidHom.comp φ) ⟨(x₀ : G), hx₀L⟩ =
      rhoEquiv K (g * t' * g⁻¹) := by
    have ht' : rhoEquiv K t' = rhoEquiv K t := LinearEquiv.ext fun ξ => by
      simpa only [rhoEquiv_apply] using congrArg (fun f : Cube K →ₗ[K] Cube K => f ξ) hρ'
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← htφ, map_mul,
      map_mul, map_inv, ht']
  have hq4 : 4 ≤ Nat.card K := hD.card ▸ H.q4
  have key : ∃ v : G, IsConj (x₀ : G) v ∧ v ∈ Q ∧ v ∈ QB X := by
    rcases hk with hk | hk | hk
    · rw [hk] at hφ'
      exact e3l28_of_involModel12 hc.ctx hD d' hform hs₀ hx₀L hφ' (involModel12_t1 hq4) hQX
    · rw [hk] at hφ'
      exact e3l28_of_involModel12 hc.ctx hD d' hform hs₀ hx₀L hφ' (involModel12_t2 hq4) hQX
    · rw [hk] at hφ'
      exact e3l28_of_involModel3 hD d' hform hs₀ hx₀L hφ' involModel3_t3 hQX
  have hxx₀ : IsConj x (x₀ : G) := by
    obtain ⟨g₁, hg₁⟩ := hs.conj
    have hxZ : g₁⁻¹ * x * g₁ ∈ Z := mem_conjSubgroup.mp (hg₁ ▸ hs.mem)
    have hx₀Z : g₁⁻¹ * (x₀ : G) * g₁ ∈ Z := mem_conjSubgroup.mp (hg₁ ▸ hx₀X)
    have hz1 : g₁⁻¹ * x * g₁ ≠ 1 := fun h => hs.ne_one (by
      have := congrArg (fun y => g₁ * y * g₁⁻¹) h
      simpa [mul_assoc] using this)
    have hz₀1 : g₁⁻¹ * (x₀ : G) * g₁ ≠ 1 := fun h => hx₀1' (by
      have := congrArg (fun y => g₁ * y * g₁⁻¹) h
      simpa [mul_assoc] using this)
    obtain ⟨m, -, hm⟩ := Z_isConj H hxZ hz1 hx₀Z hz₀1
    refine isConj_iff.mpr ⟨g₁ * m * g₁⁻¹, ?_⟩
    have e1 : (x₀ : G) = g₁ * (m * (g₁⁻¹ * x * g₁) * m⁻¹) * g₁⁻¹ := by
      rw [hm]; group
    rw [e1]
    group
  obtain ⟨v, hv, hvQ, hvX⟩ := key
  exact ⟨v, hxx₀.trans hv, hvQ, hvX⟩

theorem smith212ENonfusedE3L_of_fe1
    (hFE1 : Smith24E3LUniformStatement) (h34 : Stroth34Statement) :
    Smith212ENonfusedE3LStatement :=
  smith212ENonfusedE3L_of_cond hFE1 (eTacitE3L_of_uniform hFE1) h34
    (smith28aE3L_of_normQuot (normQuotE3L_of_uniform hFE1) (elemBoundE3L_of_uniform hFE1))
    (e3l28Cond_of_uniform hFE1)

end Main

end CFSG.RankThree.GF2n.Smith81
