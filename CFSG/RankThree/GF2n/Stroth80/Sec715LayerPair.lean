module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec712Normalizes

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

section V

variable (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)

@[expose] def vActLin (x : ↥(bar M Q (Rt M (LB M Q B) t))) :
    ↥(hc.VtSub hS.model t) →ₗ[K] ↥(hc.VtSub hS.model t) where
  toFun w := ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS ht _ x.2 _ w.2⟩
  map_add' v w := Subtype.ext (map_add (ρ (x : Mbar M Q)).toAdd (v : M₀.E) w)
  map_smul' c w := Subtype.ext (hS.lin _ (S714.mem_bar_H0_of_Rt hc x.2) c w)

theorem vActLin_mul (x y : ↥(bar M Q (Rt M (LB M Q B) t))) :
    vActLin hS ht (x * y) = (vActLin hS ht x).comp (vActLin hS ht y) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  show (ρ ((x * y : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q)).toAdd w =
    (ρ (x : Mbar M Q)).toAdd ((ρ (y : Mbar M Q)).toAdd w)
  rw [Subgroup.coe_mul]
  exact act_mul_apply ρ _ _ _

theorem vActLin_one : vActLin hS ht 1 = LinearMap.id := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  show (ρ ((1 : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q)).toAdd w = w
  rw [Subgroup.coe_one]
  exact act_one_apply _

@[expose] def vAct :
    ↥(bar M Q (Rt M (LB M Q B) t)) →* (↥(hc.VtSub hS.model t) ≃ₗ[K] ↥(hc.VtSub hS.model t)) where
  toFun x := LinearEquiv.ofLinear (vActLin hS ht x) (vActLin hS ht x⁻¹)
    (by rw [← vActLin_mul, mul_inv_cancel, vActLin_one])
    (by rw [← vActLin_mul, inv_mul_cancel, vActLin_one])
  map_one' := LinearEquiv.ext fun w => by
    show vActLin hS ht 1 w = w
    rw [vActLin_one, LinearMap.id_apply]
  map_mul' x y := LinearEquiv.ext fun w => by
    show vActLin hS ht (x * y) w = vActLin hS ht x (vActLin hS ht y w)
    rw [vActLin_mul, LinearMap.comp_apply]

theorem vAct_apply (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)) :
    ((vAct hS ht x w : ↥(hc.VtSub hS.model t)) : M₀.E) = (ρ (x : Mbar M Q)).toAdd w := rfl

end V

section Pair

variable (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
  (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)

include h310chi h52a hs hr in
theorem deltaSub_facts {f : ↥(S714.wsub hS t) →ₗ[K] M₀.E} (hf : f ∈ deltaSub hS t) :
    (∀ w, f w ∈ hc.VtSub hS.model t) ∧
      ∀ w : ↥(S714.wsub hS t), (w : M₀.E) ∈ hc.VtSub hS.model t → f w = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, hg, rfl⟩ := hf
    obtain ⟨g1, g2, -⟩ := S714.dmap_CN_facts h310chi h52a hS hs hr hg
    exact ⟨fun w => g2 _ w.2, fun w hw => g1 _ hw⟩
  | zero => exact ⟨fun _ => Submodule.zero_mem _, fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    exact ⟨fun w => Submodule.add_mem _ (hf.1 w) (hg.1 w), fun w hw => by
      rw [LinearMap.add_apply, hf.2 w hw, hg.2 w hw, add_zero]⟩
  | smul c f _ hf =>
    exact ⟨fun w => Submodule.smul_mem _ c (hf.1 w), fun w hw => by
      rw [LinearMap.smul_apply, hf.2 w hw, smul_zero]⟩

@[expose] def betaW : ↥(S714.wsub hS t) →ₗ[K] ↥(deltaSub hS t) →ₗ[K] ↥(hc.VtSub hS.model t) :=
  LinearMap.mk₂ K
    (fun w f => ⟨(f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w,
      (deltaSub_facts h310chi h52a hS hs hr f.2).1 w⟩)
    (fun w w' f => Subtype.ext (map_add _ _ _))
    (fun c w f => Subtype.ext (map_smul _ _ _))
    (fun w f f' => Subtype.ext rfl)
    (fun c w f => Subtype.ext rfl)

theorem vInW_le_ker_betaW : vInW hS t ≤ LinearMap.ker (betaW h310chi h52a hS hs hr) := by
  intro w hw
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun f => Subtype.ext ?_
  exact (deltaSub_facts h310chi h52a hS hs hr f.2).2 w hw

@[expose] def betaQ : wvQ hS t →ₗ[K] ↥(deltaSub hS t) →ₗ[K] ↥(hc.VtSub hS.model t) :=
  (vInW hS t).liftQ (betaW h310chi h52a hS hs hr) (vInW_le_ker_betaW h310chi h52a hS hs hr)

theorem coe_betaQ_mk (w : ↥(S714.wsub hS t)) (f : ↥(deltaSub hS t)) :
    ((betaQ h310chi h52a hS hs hr (Submodule.Quotient.mk w) f : ↥(hc.VtSub hS.model t)) :
      M₀.E) = (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w := rfl

theorem betaQ_equivariant (x : ↥(bar M Q (Rt M (LB M Q B) t))) (m : wvQ hS t)
    (f : ↥(deltaSub hS t)) :
    betaQ h310chi h52a hS hs hr (wvAct hS hs.toSec5.mem x m) (deltaAct hS hs.toSec5.mem x f) =
      vAct hS hs.toSec5.mem x (betaQ h310chi h52a hS hs hr m f) := by
  induction m using Submodule.Quotient.induction_on with
  | H w =>
    refine Subtype.ext ?_
    rw [wvAct_mk, coe_betaQ_mk, vAct_apply, coe_betaQ_mk, coe_deltaAct, conjHom_apply]
    congr 2
    refine Subtype.ext ?_
    rw [wAct_apply, wAct_apply]
    show (ρ ((x⁻¹ : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q)).toAdd
      ((ρ (x : Mbar M Q)).toAdd w) = w
    rw [← act_mul_apply, Subgroup.coe_inv, inv_mul_cancel]
    exact act_one_apply _

theorem betaQ_eq_zero_right {f : ↥(deltaSub hS t)}
    (h : ∀ m, betaQ h310chi h52a hS hs hr m f = 0) : f = 0 := by
  refine Subtype.ext (LinearMap.ext fun w => ?_)
  have := congrArg Subtype.val (h (Submodule.Quotient.mk w))
  rw [coe_betaQ_mk] at this
  exact this

include h310chi h52a hs hr in
theorem betaQ_eq_zero_left (hCV : Sec7CVStatement) {m : wvQ hS t}
    (h : ∀ f, betaQ h310chi h52a hS hs hr m f = 0) : m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | H w =>
    rw [Submodule.Quotient.mk_eq_zero, mem_vInW, hc.mem_VtSub hS.model t]
    obtain ⟨x, hxW, hxQ, hxw⟩ := M₀.mem_img.mp ((S714.mem_wsub hS t).mp w.2)
    rw [← hxw]
    refine M₀.pi_mem_img ((hCV G M Q Z B hc n' t hs x hxQ).mpr fun y hy => ?_) hxQ
    have hyN : y ∈ hc.CN t := hy.2
    have hyM : y ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hyN).1
    have hf := h ⟨S714.delta hS t (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))
      (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hyN)),
      delta_mem_deltaSub hS (S714.mk_mem_bar _ hyN)⟩
    have h0 := congrArg Subtype.val hf
    rw [coe_betaQ_mk, S714.delta_apply] at h0
    have h1 : S714.dmap ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M)) (M₀.π x) = 0 := by
      rw [hxw]
      exact h0
    rw [S714.dmap_pi hS ⟨y, hyM⟩ hxQ] at h1
    have hcQ : ⁅y, x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) x).mp hxQ)
        (Q.inv_mem hxQ)
    exact (M₀.π_ker _ hcQ).mp h1

end Pair

section Stab

variable (hS : IsTensorSetup hc n M₀ ρ b) {t : G}

@[expose] def wStab (g : Mbar M Q) (hg : g ∈ bar M Q (H0 M Z))
    (hgW : ∀ w ∈ S714.wsub hS t, (ρ g).toAdd w ∈ S714.wsub hS t) :
    ↥(S714.wsub hS t) →ₗ[K] ↥(S714.wsub hS t) where
  toFun w := ⟨(ρ g).toAdd w, hgW _ w.2⟩
  map_add' v w := Subtype.ext (map_add (ρ g).toAdd (v : M₀.E) w)
  map_smul' c w := Subtype.ext (hS.lin _ hg c w)

@[expose] def conjE (g : Mbar M Q) (hg : g ∈ bar M Q (H0 M Z))
    (hgW' : ∀ w ∈ S714.wsub hS t, (ρ g⁻¹).toAdd w ∈ S714.wsub hS t) :
    (↥(S714.wsub hS t) →ₗ[K] M₀.E) →ₗ[K] (↥(S714.wsub hS t) →ₗ[K] M₀.E) where
  toFun f := ((actE hS g hg : M₀.E →ₗ[K] M₀.E).comp f).comp
    (wStab hS g⁻¹ (Subgroup.inv_mem _ hg) hgW')
  map_add' f f' := by
    ext w
    simp
  map_smul' c f := by
    ext w
    simp

theorem conjE_apply (g : Mbar M Q) (hg : g ∈ bar M Q (H0 M Z))
    (hgW' : ∀ w ∈ S714.wsub hS t, (ρ g⁻¹).toAdd w ∈ S714.wsub hS t)
    (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) (w : ↥(S714.wsub hS t)) :
    conjE hS g hg hgW' f w = (ρ g).toAdd (f ⟨(ρ g⁻¹).toAdd w, hgW' _ w.2⟩) := rfl

theorem delta_conj_of_stab (g : Mbar M Q) (hg : g ∈ bar M Q (H0 M Z))
    (hgW' : ∀ w ∈ S714.wsub hS t, (ρ g⁻¹).toAdd w ∈ S714.wsub hS t) {x : Mbar M Q}
    (hx : x ∈ bar M Q (H0 M Z)) :
    S714.delta hS t (g * x * g⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx)
      (Subgroup.inv_mem _ hg)) = conjE hS g hg hgW' (S714.delta hS t x hx) := by
  refine LinearMap.ext fun w => ?_
  rw [conjE_apply, S714.delta_apply, S714.delta_apply]
  have hinv : (ρ g).toAdd ((ρ g⁻¹).toAdd (w : M₀.E)) = w := by
    rw [← act_mul_apply, mul_inv_cancel]
    exact act_one_apply _
  simp only [S714.dmap]
  rw [act_mul_apply, act_mul_apply, map_sub, hinv]

variable [(Q.subgroupOf M).Normal] in
theorem stab_wsub_of_mem_NormH0 (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    {n' : ℕ} (hs : Sec7Hyp hc n' t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ NormH0 M Z Z0) :
    ∀ w ∈ S714.wsub hS t, (ρ (QuotientGroup.mk (⟨g, hg.1.1⟩ : ↥M))).toAdd w ∈ S714.wsub hS t := by
  intro w hw
  obtain ⟨-, hV⟩ := sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hg
  obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((S714.mem_wsub hS t).mp hw)
  rw [← hS.conj ⟨g, hg.1.1⟩ x hxQ]
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hg.1.1
  have hgV : g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have : g * v * g⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
        mem_conjSubgroup.mpr (by simpa [mul_assoc] using hv)
      rwa [hV] at this
    · intro hv
      rw [← hV] at hv
      have := mem_conjSubgroup.mp hv
      simpa [mul_assoc] using this
  have hW := conj_mem_Wt hgQ hgV hxW
  exact (S714.mem_wsub hS t).mpr (M₀.pi_mem_img hW hW.1)

end Stab

end CFSG.RankThree.GF2n.Stroth80.S715L
