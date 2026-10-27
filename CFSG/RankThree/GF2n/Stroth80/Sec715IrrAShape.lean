module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAIface
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAForm
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrARank
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrConfigC

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem range_dlin_congr (hS : IsTensorSetup hc n M₀ ρ b) {g g' : Mbar M Q} (h : g = g')
    (hg : g ∈ bar M Q (H0 M Z)) (hg' : g' ∈ bar M Q (H0 M Z)) :
    LinearMap.range (dlin hS g hg) = LinearMap.range (dlin hS g' hg') := by
  subst h
  rfl

theorem mem_range_dlin_conj_iff (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (g : Mbar M Q) {u : Mbar M Q}
    (hu : u ∈ bar M Q Z0) (hu1 : u ≠ 1) (hgu : g * u * g⁻¹ ∈ bar M Q (H0 M Z)) (x : M₀.E) :
    x ∈ LinearMap.range (dlin hS (g * u * g⁻¹) hgu) ↔
      (ρ g⁻¹).toAdd x ∈ hc.VtSub hS.model t := by
  obtain ⟨hψV, hψsurj, -⟩ := psi_facts_tbar h310chi hS hs
  obtain ⟨-, -, htH⟩ := tbar_mem hc hs
  have hc0 : cscal hc ρ hs.toSec5.mem u ≠ 0 := fun h =>
    hu1 ((cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0 hu).mp h)
  have hgg : ∀ e, (ρ g).toAdd ((ρ g⁻¹).toAdd e) = e := fun e => by
    rw [← act_mul_apply, mul_inv_cancel]
    exact act_one_apply _
  have hgg' : ∀ e, (ρ g⁻¹).toAdd ((ρ g).toAdd e) = e := fun e => by
    rw [← act_mul_apply, inv_mul_cancel]
    exact act_one_apply _
  have hdu : ∀ e, dmap ρ u e =
      cscal hc ρ hs.toSec5.mem u • dmap ρ (tbar hc hs.toSec5.mem) e := fun e => by
    have h1 := act_eq_cscal h310chi h52a hMp hS hs hr hZ0 hu e
    rw [act_eq_add_dmap] at h1
    exact add_left_cancel h1
  constructor
  · rintro ⟨e, rfl⟩
    rw [dlin_apply, dmap_conj, hgg', hdu]
    exact Submodule.smul_mem _ _ (hψV _)
  · intro hx
    obtain ⟨e₀, he₀⟩ := hψsurj _ hx
    refine ⟨(ρ g).toAdd ((cscal hc ρ hs.toSec5.mem u)⁻¹ • e₀), ?_⟩
    rw [dlin_apply, dmap_conj, hgg', hdu, dmap_smul hS htH, smul_smul, mul_inv_cancel₀ hc0,
      one_smul, he₀, hgg]

section Coord

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {ht : t ∈ LB M Q B} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
  {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem ConfigAData.delta_eq_betaMu (D : ConfigAData hS ht ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    {v : Mbar M Q} (hv : v ∈ bar M Q (hc.CN t)) (w : ↥(wsub hS t)) :
    delta hS t v (mem_bar_H0_of_CN hv) w =
      ((betaMu μ (eN ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩)
        (eM (Submodule.Quotient.mk w)) : ↥(hc.VtSub hS.model t)) : M₀.E) := by
  have h := D.pair w ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩
  rw [Fin.sum_univ_two] at h
  rw [betaMu_apply]
  exact h

theorem ConfigAData.dlin_eq_zero_iff (D : ConfigAData hS ht ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    {v : Mbar M Q} (hv : v ∈ bar M Q (hc.CN t)) (w : ↥(wsub hS t)) :
    dlin hS v (mem_bar_H0_of_CN hv) (w : M₀.E) = 0 ↔
      betaMu μ (eN ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩)
        (eM (Submodule.Quotient.mk w)) = 0 := by
  have h := D.delta_eq_betaMu hv w
  rw [delta_apply] at h
  rw [dlin_apply, h, Submodule.coe_eq_zero]

theorem ConfigAData.finrank_range_delta (D : ConfigAData hS ht ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    {v : Mbar M Q} (hv : v ∈ bar M Q (hc.CN t)) :
    Module.finrank K (LinearMap.range (delta hS t v (mem_bar_H0_of_CN hv))) =
      Module.finrank K (LinearMap.range
        (betaMu μ (eN ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩))) := by
  set x := eN ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩ with hx
  have hcomp : delta hS t v (mem_bar_H0_of_CN hv) = (hc.VtSub hS.model t).subtype ∘ₗ
      (betaMu μ x ∘ₗ ((eM : wvQ hS t →ₗ[K] (Fin 2 → L₃)) ∘ₗ (vInW hS t).mkQ)) :=
    LinearMap.ext fun w => D.delta_eq_betaMu hv w
  have hsurj : Function.Surjective
      ((eM : wvQ hS t →ₗ[K] (Fin 2 → L₃)) ∘ₗ (vInW hS t).mkQ) :=
    eM.surjective.comp (Submodule.mkQ_surjective _)
  rw [hcomp, LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj,
    Submodule.map_top, Submodule.finrank_map_subtype_eq]

theorem exists_eM_eq (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (m : Fin 2 → L₃) :
    ∃ w : ↥(wsub hS t), eM (Submodule.Quotient.mk w) = m := by
  obtain ⟨q, rfl⟩ := eM.surjective m
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨w, rfl⟩

theorem ConfigAData.mem_range_sup_iff (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (D : ConfigAData hS ht ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) (T : TrialityFacts q₃ q₄ μ)
    {v : Mbar M Q} (hv : v ∈ bar M Q (hc.CN t)) {f : Fin 2 → K} {y : L₄} (hf : f ≠ 0)
    (hy : y ≠ 0) (hqy : q₄ y = 0)
    (hx : eN ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩ = pureT f y)
    (w : ↥(wsub hS t)) :
    (w : M₀.E) ∈ LinearMap.range (dlin hS v (mem_bar_H0_of_CN hv)) ⊔ hc.VtSub hS.model t ↔
      eM (Submodule.Quotient.mk w) ∈ (LinearMap.ker (μ.flip y)).map (pureT (ψ *ᵥ f)) := by
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : FiniteDimensional K L₃ := Module.finite_of_finrank_pos (by rw [D.finrank₃]; norm_num)
  have hvH := mem_bar_H0_of_CN hv
  obtain ⟨-, hDW, hDE⟩ := dmap_CN_facts h310chi h52a hS hs hr hv
  obtain ⟨hnd, hrefl⟩ := bilin_nondegenerate_isRefl (M₀ := M₀)
  have hW : wsub hS t = M₀.B.orthogonal (hc.VtSub hS.model t) := wsub_eq_orthogonal hS t
  have hadj : ∀ x, ∀ w ∈ wsub hS t,
      M₀.B (dlin hS v hvH x) w = -M₀.B x (dlin hS v hvH w) := fun x w hw =>
    bilin_D_right (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t)
      (D := dlin hS v hvH) (dmap_iso hS hvH) (fun x => hDE x) (fun w hw => hDW w hw)
      (fun w hw v hv => bilin_wsub_vsub hS t hw hv) x hw
  have hP : ∀ a : L₃, (∀ a', QuadraticMap.polarBilin q₃ a a' = 0) → a = 0 := fun a h =>
    D.q₃_nd a fun a' => h a'
  have hSS := T.orthogonal_ker_iff D.finrank₃ D.q₃_nd hy hqy
  rw [range_sup_eq_orthogonal hnd hrefl hW hadj, LinearMap.BilinForm.mem_orthogonal_iff,
    ← orthogonal_comap_contr hP D.φψ hf hSS, ← ker_betaMu_pureT,
    LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h m hm
    obtain ⟨u, rfl⟩ := exists_eM_eq eM m
    have hu : (u : M₀.E) ∈ wsub hS t ⊓ LinearMap.ker (dlin hS v hvH) := by
      refine ⟨u.2, LinearMap.mem_ker.mpr ((D.dlin_eq_zero_iff hv u).mpr ?_)⟩
      rw [hx]
      exact LinearMap.mem_ker.mp hm
    have h1 := h _ hu
    rw [D.form] at h1
    exact h1
  · intro h u hu
    have hm : eM (Submodule.Quotient.mk (⟨u, hu.1⟩ : ↥(wsub hS t))) ∈
        LinearMap.ker (betaMu μ (pureT f y)) := by
      rw [LinearMap.mem_ker, ← hx]
      exact (D.dlin_eq_zero_iff hv ⟨u, hu.1⟩).mp (LinearMap.mem_ker.mp hu.2)
    have h1 := h _ hm
    have h2 := D.form ⟨u, hu.1⟩ w
    rw [h2]
    exact h1

end Coord

section Shape

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]

variable (hS) in
theorem finrank_range_delta_conj_le (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) {n' : ℕ} {r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hgM : g ∈ M)
    {v : Mbar M Q} (hv : v ∈ bar M Q (conjSubgroup g Z0)) (hvN : v ∈ bar M Q (hc.CN t)) :
    Module.finrank K (LinearMap.range (delta hS t v (mem_bar_H0_of_CN hvN))) ≤ 4 := by
  classical
  obtain ⟨v', hv', rfl⟩ := exists_of_mem_bar hv
  have hu : g⁻¹ * (v' : G) * g ∈ Z0 := mem_conjSubgroup.mp hv'
  have huM : g⁻¹ * (v' : G) * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) v'.2) hgM
  let gm : ↥M := ⟨g, hgM⟩
  let um : ↥M := ⟨g⁻¹ * (v' : G) * g, huM⟩
  have hvm : v' = gm * um * gm⁻¹ := Subtype.ext (by
    show (v' : G) = g * (g⁻¹ * (v' : G) * g) * g⁻¹
    group)
  have hub : (QuotientGroup.mk um : Mbar M Q) ∈ bar M Q Z0 := mk_mem_bar um hu
  have hvb : (QuotientGroup.mk v' : Mbar M Q) =
      QuotientGroup.mk gm * QuotientGroup.mk um * (QuotientGroup.mk gm)⁻¹ := by
    rw [hvm]; rfl
  have h1 := two_mul_finrank_range_delta_le h310chi h52a hS hs hr hvN
  have h2 := finrank_range_dlin_conj_le h310chi h52a hMp hS hs hr hZ0 (QuotientGroup.mk gm)
    hub (by rw [← hvb]; exact mem_bar_H0_of_CN hvN)
  rw [range_dlin_congr hS hvb.symm _ (mem_bar_H0_of_CN hvN),
    finrank_vtSub hS hs.toSec5.mem hp] at h2
  omega

variable {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem ConfigAData.exists_pureT_of_conj (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) {n' : ℕ} {r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) (T : TrialityFacts q₃ q₄ μ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hgM : g ∈ M)
    {v : Mbar M Q} (hv : v ∈ bar M Q (conjSubgroup g Z0)) (hvN : v ∈ bar M Q (hc.CN t))
    (h0 : delta hS t v (mem_bar_H0_of_CN hvN) ≠ 0) :
    ∃ (f : Fin 2 → K) (y : L₄), f ≠ 0 ∧ y ≠ 0 ∧ q₄ y = 0 ∧
      eN ⟨delta hS t v (mem_bar_H0_of_CN hvN), delta_mem_deltaSub hS hvN⟩ = pureT f y := by
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : FiniteDimensional K L₃ := Module.finite_of_finrank_pos (by rw [D.finrank₃]; norm_num)
  have hrk := finrank_range_delta_conj_le hS h310chi h52a hMp hs hr hp hZ0 hgM hv hvN
  rw [D.finrank_range_delta hvN] at hrk
  refine T.exists_eq_pureT D.finrank₃ ?_ hrk
  intro hx
  apply h0
  have h1 : (⟨delta hS t v (mem_bar_H0_of_CN hvN), delta_mem_deltaSub hS hvN⟩ :
      ↥(deltaSub hS t)) = 0 := eN.map_eq_zero_iff.mp hx
  exact congrArg Subtype.val h1

theorem hasLineProp_of (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCRW : Sec7CRWStatement) (hZcard : Sec7ZCardStatement)
    {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) (T : TrialityFacts q₃ q₄ μ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) :
    HasLineProp hS t eN q₄ Z0 := by
  classical
  haveI : FiniteDimensional K L₃ := Module.finite_of_finrank_pos (by rw [D.finrank₃]; norm_num)
  intro g hgM hV' hne
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
  obtain ⟨f, y, hf, hy, hqy, hxy⟩ :=
    D.exists_pureT_of_conj h310chi h52a hMp hs hr hp T hZ0 hgM hv₀ hv₀N hΔ0
  refine ⟨f, y, hf, hy, hqy, fun v hv hvN => ?_⟩
  by_cases h0 : delta hS t v (mem_bar_H0_of_CN hvN) = 0
  · refine ⟨0, ?_⟩
    have h1 : (⟨delta hS t v (mem_bar_H0_of_CN hvN), delta_mem_deltaSub hS hvN⟩ :
        ↥(deltaSub hS t)) = 0 := Subtype.ext h0
    rw [h1, map_zero, zero_smul]
  obtain ⟨f', y', hf', hy', hqy', hx'⟩ :=
    D.exists_pureT_of_conj h310chi h52a hMp hs hr hp T hZ0 hgM hv hvN h0
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
  have hub'1 : (QuotientGroup.mk um' : Mbar M Q) ≠ 1 := by
    intro h1
    apply h0
    have e1 : (QuotientGroup.mk v' : Mbar M Q) = 1 := by rw [hvb, h1, mul_one, mul_inv_cancel]
    refine LinearMap.ext fun w => ?_
    rw [delta_apply, LinearMap.zero_apply, e1, dmap, act_one_apply, sub_self]
  have hrange : LinearMap.range (dlin hS (QuotientGroup.mk v') (mem_bar_H0_of_CN hvN)) =
      LinearMap.range (dlin hS (gb * ub * gb⁻¹) (mem_bar_H0_of_CN hv₀N)) := by
    have hgu' : gb * QuotientGroup.mk um' * gb⁻¹ ∈ bar M Q (H0 M Z) := by
      rw [← hvb]; exact mem_bar_H0_of_CN hvN
    rw [range_dlin_congr hS hvb _ hgu']
    ext x
    rw [mem_range_dlin_conj_iff h310chi h52a hMp hS hs hr hZ0 gb hub' hub'1 hgu' x,
      mem_range_dlin_conj_iff h310chi h52a hMp hS hs hr hZ0 gb hub hub1 _ x]
  have hsub : (LinearMap.ker (μ.flip y)).map (pureT (ψ *ᵥ f)) =
      (LinearMap.ker (μ.flip y')).map (pureT (ψ *ᵥ f')) := by
    ext m
    obtain ⟨w, rfl⟩ := exists_eM_eq eM m
    rw [← D.mem_range_sup_iff h310chi h52a hs hr T hv₀N hf hy hqy hxy w,
      ← D.mem_range_sup_iff h310chi h52a hs hr T hvN hf' hy' hqy' hx' w, hrange]
  obtain ⟨c, hc⟩ := T.eq_smul_of_map_eq D.finrank₃ D.φψ hf hf' hy hy' hqy hqy' hsub
  exact ⟨c, by rw [hx', hc]⟩

end Shape

end CFSG.RankThree.GF2n.Stroth80.S715L
