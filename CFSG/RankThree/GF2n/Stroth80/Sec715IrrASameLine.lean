module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAFix

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714
open scoped Matrix commutatorElement

theorem exists_eq_smul_of_pureT_eq_smul {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    {f f'' : Fin 2 → K} {y y'' : L} {a : K} (hf'' : f'' ≠ 0) (hy'' : y'' ≠ 0)
    (h : pureT f'' y'' = a • pureT f y) : ∃ c : K, f'' = c • f := by
  obtain ⟨i, hi⟩ : ∃ i, f'' i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hf'' (funext hh)
  have hcomp : ∀ j, f'' j • y'' = (a * f j) • y := fun j => by
    have := congrFun h j
    rwa [pureT_apply, Pi.smul_apply, pureT_apply, smul_smul] at this
  have hafi : a * f i ≠ 0 := by
    intro h0
    have := hcomp i
    rw [h0, zero_smul] at this
    exact hy'' ((smul_eq_zero.mp this).resolve_left hi)
  have hy : y ≠ 0 := by
    intro h0
    have := hcomp i
    rw [h0, smul_zero] at this
    exact hy'' ((smul_eq_zero.mp this).resolve_left hi)
  have hfi : f i ≠ 0 := right_ne_zero_of_mul hafi
  have ha : a ≠ 0 := left_ne_zero_of_mul hafi
  refine ⟨f'' i / f i, funext fun j => ?_⟩
  have e1 : (f'' i * (a * f j)) • y = (f'' j * (a * f i)) • y := by
    rw [← smul_smul, ← hcomp j, ← smul_smul, ← hcomp i, smul_smul, smul_smul, mul_comm]
  have e2 : f'' i * (a * f j) = f'' j * (a * f i) := by
    have := sub_eq_zero.mpr e1
    rw [← sub_smul] at this
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hy)
  have e3 : a * (f'' j * f i - f'' i * f j) = 0 := by linear_combination -e2
  have e4 := (mul_eq_zero.mp e3).resolve_left ha
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination e4

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E} {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
  {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem ConfigAData.exists_eM_dmap_eq_pureT (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCRW : Sec7CRWStatement)
    (hZcard : Sec7ZCardStatement) {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (hp : OmegaPlusNat hc t 4) (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    (T : TrialityFacts q₃ q₄ μ) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {g : G} (hgM : g ∈ M) (hV' : conjSubgroup g Z0 ≤ hc.CN t) (hne : conjSubgroup g Z0 ≠ Z0)
    {f : Fin 2 → K} {y : L₄} (hL : HasLine hS t eN Z0 g f y) {v : Mbar M Q}
    (hv : v ∈ bar M Q (conjSubgroup g Z0)) (e : M₀.E) (hW : dmap ρ v e ∈ wsub hS t) :
    ∃ k : L₃, eM (Submodule.Quotient.mk ⟨dmap ρ v e, hW⟩) = pureT (ψ *ᵥ f) k := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  obtain ⟨u, huZ, huQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  let gm : ↥M := ⟨g, hgM⟩
  let um : ↥M := ⟨u, hc.centre_le_M t hZ0 huZ⟩
  set gb : Mbar M Q := QuotientGroup.mk gm with hgb
  set ub : Mbar M Q := QuotientGroup.mk um with hubdef
  have hub : ub ∈ bar M Q Z0 := mk_mem_bar um huZ
  have hub1 : ub ≠ 1 := by
    intro h
    exact huQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff um).mp h))
  have hv₀ : gb * ub * gb⁻¹ ∈ bar M Q (conjSubgroup g Z0) := by
    refine mk_mem_bar (gm * um * gm⁻¹) (mem_conjSubgroup.mpr ?_)
    show g⁻¹ * (g * u * g⁻¹) * g ∈ Z0
    rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact huZ
  have hv₀N := bar_mono' hV' hv₀
  have hΔ0 : delta hS t (gb * ub * gb⁻¹) (mem_bar_H0_of_CN hv₀N) ≠ 0 := by
    intro h0
    have hR := bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) hv₀N
    have hZ := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hR).mp h0
    have hZ' : g * u * g⁻¹ ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 (gm * um * gm⁻¹)).mp hZ
    exact hne (conjSubgroup_eq_self_iff.mpr (hTI g hgM u huZ huQ hZ'))
  obtain ⟨f'', y'', hf'', hy'', hqy'', hxy''⟩ :=
    D.exists_pureT_of_conj h310chi h52a hMp hs hr hp T hZ0 hgM hv₀ hv₀N hΔ0
  obtain ⟨a, ha⟩ := hL _ hv₀ hv₀N
  obtain ⟨c, hc''⟩ := exists_eq_smul_of_pureT_eq_smul hf'' hy'' (hxy''.symm.trans ha)
  have hvN : v ∈ bar M Q (hc.CN t) := bar_mono' hV' hv
  have hvH := mem_bar_H0_of_CN hvN
  obtain ⟨v', hv', rfl⟩ := exists_of_mem_bar hv
  have hu' : g⁻¹ * (v' : G) * g ∈ Z0 := mem_conjSubgroup.mp hv'
  have hu'M : g⁻¹ * (v' : G) * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) v'.2) hgM
  let um' : ↥M := ⟨g⁻¹ * (v' : G) * g, hu'M⟩
  have hvm : v' = gm * um' * gm⁻¹ := Subtype.ext (by
    show (v' : G) = g * (g⁻¹ * (v' : G) * g) * g⁻¹
    group)
  have hub' : (QuotientGroup.mk um' : Mbar M Q) ∈ bar M Q Z0 := mk_mem_bar um' hu'
  have hvb : (QuotientGroup.mk v' : Mbar M Q) = gb * QuotientGroup.mk um' * gb⁻¹ := by
    rw [hvm]; rfl
  by_cases hub'1 : (QuotientGroup.mk um' : Mbar M Q) = 1
  ·
    refine ⟨0, ?_⟩
    have e1 : (QuotientGroup.mk v' : Mbar M Q) = 1 := by
      rw [hvb, hub'1, mul_one, mul_inv_cancel]
    have h0 : (⟨dmap ρ (QuotientGroup.mk v') e, hW⟩ : ↥(wsub hS t)) = 0 := by
      refine Subtype.ext ?_
      show dmap ρ (QuotientGroup.mk v') e = 0
      rw [e1]
      exact dmap_one e
    rw [h0, Submodule.Quotient.mk_zero, map_zero, map_zero]
  ·
    have hgu' : gb * QuotientGroup.mk um' * gb⁻¹ ∈ bar M Q (H0 M Z) := by
      rw [← hvb]; exact hvH
    have h1 : dmap ρ (QuotientGroup.mk v') e ∈ LinearMap.range (dlin hS _ hvH) := ⟨e, rfl⟩
    rw [range_dlin_congr hS hvb hvH hgu'] at h1
    have h2 := (mem_range_dlin_conj_iff h310chi h52a hMp hS hs hr hZ0 gb hub' hub'1 hgu' _).mp h1
    have hmem := (mem_range_dlin_conj_iff h310chi h52a hMp hS hs hr hZ0 gb hub hub1
      (mem_bar_H0_of_CN hv₀N) _).mpr h2
    have hsup : ((⟨dmap ρ (QuotientGroup.mk v') e, hW⟩ : ↥(wsub hS t)) : M₀.E) ∈
        LinearMap.range (dlin hS (gb * ub * gb⁻¹) (mem_bar_H0_of_CN hv₀N)) ⊔
          hc.VtSub hS.model t := Submodule.mem_sup_left hmem
    obtain ⟨k, -, hk⟩ := Submodule.mem_map.mp
      ((D.mem_range_sup_iff h310chi h52a hs hr T hv₀N hf'' hy'' hqy'' hxy'' _).mp hsup)
    refine ⟨c • k, ?_⟩
    rw [← hk, hc'']
    funext i
    simp only [pureT_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
    rw [mul_comm]

theorem sameLineOrthProp_of (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCRW : Sec7CRWStatement) (hZcard : Sec7ZCardStatement)
    {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) (T : TrialityFacts q₃ q₄ μ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hiso : ∀ (g : G) (f : Fin 2 → K) (y : L₄), IsSymNbr hc t Z0 g → f ≠ 0 → y ≠ 0 →
      HasLine hS t eN Z0 g f y → f ⬝ᵥ (ψ *ᵥ f) = 0) :
    SameLineOrthProp hS t eN Z0 := by
  intro g₁ g₂ f₁ f₂ y₁ y₂ hN₁ hN₂ hf₁ hf₂ hy₁ hy₂ hL₁ hL₂ hdet v₁ hv₁ v₂ hv₂ e e'
  have hv₁N : v₁ ∈ bar M Q (hc.CN t) := bar_mono' hN₁.2.1 hv₁
  have hv₂N : v₂ ∈ bar M Q (hc.CN t) := bar_mono' hN₂.2.1 hv₂
  obtain ⟨-, -, hW₁⟩ := dmap_CN_facts h310chi h52a hS hs hr hv₁N
  obtain ⟨-, -, hW₂⟩ := dmap_CN_facts h310chi h52a hS hs hr hv₂N
  obtain ⟨k₁, hk₁⟩ := D.exists_eM_dmap_eq_pureT h310chi h52a hMp hCRW hZcard hs hr hp T hZ0 hTI
    hN₁.1 hN₁.2.1 hN₁.2.2.1 hL₁ hv₁ e (hW₁ e)
  obtain ⟨k₂, hk₂⟩ := D.exists_eM_dmap_eq_pureT h310chi h52a hMp hCRW hZcard hs hr hp T hZ0 hTI
    hN₂.1 hN₂.2.1 hN₂.2.2.1 hL₂ hv₂ e' (hW₂ e')
  obtain ⟨c, hc₂⟩ : ∃ c : K, f₂ = c • f₁ := by
    unfold det2 at hdet
    by_cases h0 : f₁ 0 = 0
    · have h1 : f₁ 1 ≠ 0 := fun h1 => hf₁ (funext fun i => by fin_cases i <;> simp [h0, h1])
      have h20 : f₂ 0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at hdet
        exact (mul_eq_zero.mp hdet).resolve_left h1
      refine ⟨f₂ 1 / f₁ 1, funext fun i => ?_⟩
      fin_cases i
      · simp [h0, h20]
      · simp [div_mul_cancel₀ _ h1]
    · refine ⟨f₂ 0 / f₁ 0, funext fun i => ?_⟩
      fin_cases i
      · simp [div_mul_cancel₀ _ h0]
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination hdet
  have hB := D.form ⟨dmap ρ v₁ e, hW₁ e⟩ ⟨dmap ρ v₂ e', hW₂ e'⟩
  rw [hk₁, hk₂] at hB
  have e1 := formT_pureT_pureT (QuadraticMap.polarBilin q₃) φ (ψ *ᵥ f₁) (ψ *ᵥ f₂) k₁ k₂
  rw [formT_apply] at e1
  simp only [QuadraticMap.polarBilin_apply_apply] at e1
  show M₀.B (dmap ρ v₁ e) (dmap ρ v₂ e') = 0
  rw [show M₀.B (dmap ρ v₁ e) (dmap ρ v₂ e') = _ from hB, e1, Matrix.mulVec_mulVec, D.φψ,
    Matrix.one_mulVec, hc₂, dotProduct_smul, dotProduct_comm,
    hiso g₁ f₁ y₁ hN₁ hf₁ hy₁ hL₁, smul_zero, zero_mul]

end CFSG.RankThree.GF2n.Stroth80.S715L
