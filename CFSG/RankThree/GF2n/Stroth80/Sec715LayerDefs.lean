module

public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelStable

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

omit [Group G] [Finite G] [(Q.subgroupOf M).Normal] [Finite K] in
theorem linEquiv_one_apply {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] (x : V) :
    (1 : V ≃ₗ[R] V) x = x := rfl

omit [Finite G] [Finite K] in
theorem act_one_apply (v : M₀.E) : (ρ 1).toAdd v = v := by
  rw [map_one]
  rfl

@[expose] def actE (hS : IsTensorSetup hc n M₀ ρ b) (g : Mbar M Q) (hg : g ∈ bar M Q (H0 M Z)) :
    M₀.E ≃ₗ[K] M₀.E :=
  AddEquiv.toLinearEquiv (ρ g).toAdd (hS.lin g hg)

@[expose] def hAct (hS : IsTensorSetup hc n M₀ ρ b) :
    ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E) where
  toFun g := actE hS g g.2
  map_one' := LinearEquiv.ext fun e => by
    show (ρ ((1 : ↥(bar M Q (H0 M Z))) : Mbar M Q)).toAdd e = e
    rw [Subgroup.coe_one]
    exact act_one_apply e
  map_mul' g h := LinearEquiv.ext fun e => by
    show (ρ ((g * h : ↥(bar M Q (H0 M Z))) : Mbar M Q)).toAdd e =
      (ρ (g : Mbar M Q)).toAdd ((ρ (h : Mbar M Q)).toAdd e)
    rw [Subgroup.coe_mul]
    exact act_mul_apply ρ _ _ _

theorem hAct_apply (hS : IsTensorSetup hc n M₀ ρ b) (g : ↥(bar M Q (H0 M Z))) (e : M₀.E) :
    hAct hS g e = (ρ (g : Mbar M Q)).toAdd e := rfl

theorem hAct_compat (hS : IsTensorSetup hc n M₀ ρ b) (y : ↥M)
    (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G) (hx : x ∈ Q) :
    M₀.π ((y : G) * x * (y : G)⁻¹) =
      hAct hS ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x) :=
  hS.conj y x hx

section W

variable (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)

@[expose] def wActLin (x : ↥(bar M Q (Rt M (LB M Q B) t))) :
    ↥(S714.wsub hS t) →ₗ[K] ↥(S714.wsub hS t) where
  toFun w := ⟨(ρ (x : Mbar M Q)).toAdd w, S714.act_mem_wsub hS ht x.2 w.2⟩
  map_add' v w := Subtype.ext (map_add (ρ (x : Mbar M Q)).toAdd (v : M₀.E) w)
  map_smul' c w := Subtype.ext (hS.lin _ (S714.mem_bar_H0_of_Rt hc x.2) c w)

theorem wActLin_apply (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(S714.wsub hS t)) :
    ((wActLin hS ht x w : ↥(S714.wsub hS t)) : M₀.E) = (ρ (x : Mbar M Q)).toAdd w := rfl

theorem wActLin_mul (x y : ↥(bar M Q (Rt M (LB M Q B) t))) :
    wActLin hS ht (x * y) = (wActLin hS ht x).comp (wActLin hS ht y) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  simp only [wActLin_apply, LinearMap.comp_apply, Subgroup.coe_mul]
  exact act_mul_apply ρ _ _ _

theorem wActLin_one : wActLin hS ht 1 = LinearMap.id := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  simp only [wActLin_apply, Subgroup.coe_one, LinearMap.id_apply]
  exact act_one_apply _

@[expose] def wAct : ↥(bar M Q (Rt M (LB M Q B) t)) →* (↥(S714.wsub hS t) ≃ₗ[K] ↥(S714.wsub hS t))
    where
  toFun x := LinearEquiv.ofLinear (wActLin hS ht x) (wActLin hS ht x⁻¹)
    (by rw [← wActLin_mul, mul_inv_cancel, wActLin_one])
    (by rw [← wActLin_mul, inv_mul_cancel, wActLin_one])
  map_one' := LinearEquiv.ext fun w => by
    show wActLin hS ht 1 w = w
    rw [wActLin_one, LinearMap.id_apply]
  map_mul' x y := LinearEquiv.ext fun w => by
    show wActLin hS ht (x * y) w = wActLin hS ht x (wActLin hS ht y w)
    rw [wActLin_mul, LinearMap.comp_apply]

theorem wAct_apply (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(S714.wsub hS t)) :
    ((wAct hS ht x w : ↥(S714.wsub hS t)) : M₀.E) = (ρ (x : Mbar M Q)).toAdd w := rfl

end W

section WV

variable (hS : IsTensorSetup hc n M₀ ρ b) (t : G)

@[expose] def vInW : Submodule K ↥(S714.wsub hS t) :=
  (hc.VtSub hS.model t).comap (S714.wsub hS t).subtype

theorem mem_vInW {w : ↥(S714.wsub hS t)} : w ∈ vInW hS t ↔ (w : M₀.E) ∈ hc.VtSub hS.model t :=
  Iff.rfl

abbrev wvQ : Type := ↥(S714.wsub hS t) ⧸ vInW hS t

variable {t}

theorem map_wAct_vInW (ht : t ∈ LB M Q B) (x : ↥(bar M Q (Rt M (LB M Q B) t))) :
    (vInW hS t).map (wAct hS ht x : ↥(S714.wsub hS t) →ₗ[K] ↥(S714.wsub hS t)) = vInW hS t := by
  have hle : ∀ y : ↥(bar M Q (Rt M (LB M Q B) t)),
      (vInW hS t).map (wAct hS ht y : ↥(S714.wsub hS t) →ₗ[K] ↥(S714.wsub hS t)) ≤ vInW hS t := by
    rintro y _ ⟨w, hw, rfl⟩
    exact hc.act_mem_VtSub hS ht _ y.2 _ hw
  refine le_antisymm (hle x) fun w hw => ?_
  refine ⟨wAct hS ht x⁻¹ w, hle x⁻¹ ⟨w, hw, rfl⟩, ?_⟩
  show (wAct hS ht x) ((wAct hS ht x⁻¹) w) = w
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, linEquiv_one_apply]

@[expose] def wvAct (ht : t ∈ LB M Q B) :
    ↥(bar M Q (Rt M (LB M Q B) t)) →* (wvQ hS t ≃ₗ[K] wvQ hS t) where
  toFun x := Submodule.Quotient.equiv (vInW hS t) (vInW hS t) (wAct hS ht x)
    (map_wAct_vInW hS ht x)
  map_one' := LinearEquiv.ext fun w => Submodule.Quotient.induction_on _ w fun w => by
    show Submodule.Quotient.mk (wAct hS ht 1 w) = Submodule.Quotient.mk w
    rw [map_one, linEquiv_one_apply]
  map_mul' x y := LinearEquiv.ext fun w => Submodule.Quotient.induction_on _ w fun w => by
    show Submodule.Quotient.mk (wAct hS ht (x * y) w) =
      Submodule.Quotient.mk (wAct hS ht x (wAct hS ht y w))
    rw [map_mul, LinearEquiv.mul_apply]

theorem wvAct_mk (ht : t ∈ LB M Q B) (x : ↥(bar M Q (Rt M (LB M Q B) t)))
    (w : ↥(S714.wsub hS t)) :
    wvAct hS ht x (Submodule.Quotient.mk w) = Submodule.Quotient.mk (wAct hS ht x w) := rfl

end WV

section Conj

variable (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)

@[expose] def conjLin (x : ↥(bar M Q (Rt M (LB M Q B) t))) :
    (↥(S714.wsub hS t) →ₗ[K] M₀.E) →ₗ[K] (↥(S714.wsub hS t) →ₗ[K] M₀.E) where
  toFun f := ((actE hS _ (S714.mem_bar_H0_of_Rt hc x.2) : M₀.E →ₗ[K] M₀.E).comp f).comp
    (wAct hS ht x⁻¹ : ↥(S714.wsub hS t) →ₗ[K] ↥(S714.wsub hS t))
  map_add' f g := by
    ext w
    simp
  map_smul' c f := by
    ext w
    simp

theorem conjLin_apply (x : ↥(bar M Q (Rt M (LB M Q B) t))) (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E)
    (w : ↥(S714.wsub hS t)) :
    conjLin hS ht x f w = (ρ (x : Mbar M Q)).toAdd (f (wAct hS ht x⁻¹ w)) := rfl

theorem conjLin_mul (x y : ↥(bar M Q (Rt M (LB M Q B) t))) :
    conjLin hS ht (x * y) = (conjLin hS ht x).comp (conjLin hS ht y) := by
  refine LinearMap.ext fun f => LinearMap.ext fun w => ?_
  rw [LinearMap.comp_apply, conjLin_apply, conjLin_apply, conjLin_apply, mul_inv_rev, map_mul,
    LinearEquiv.mul_apply, Subgroup.coe_mul, act_mul_apply]

theorem conjLin_one : conjLin hS ht 1 = LinearMap.id := by
  refine LinearMap.ext fun f => LinearMap.ext fun w => ?_
  rw [conjLin_apply, LinearMap.id_apply, inv_one, map_one, linEquiv_one_apply,
    Subgroup.coe_one, act_one_apply]

@[expose] def conjHom :
    ↥(bar M Q (Rt M (LB M Q B) t)) →* ((↥(S714.wsub hS t) →ₗ[K] M₀.E) ≃ₗ[K]
      (↥(S714.wsub hS t) →ₗ[K] M₀.E)) where
  toFun x := LinearEquiv.ofLinear (conjLin hS ht x) (conjLin hS ht x⁻¹)
    (by rw [← conjLin_mul, mul_inv_cancel, conjLin_one])
    (by rw [← conjLin_mul, inv_mul_cancel, conjLin_one])
  map_one' := LinearEquiv.ext fun f => by
    show conjLin hS ht 1 f = f
    rw [conjLin_one, LinearMap.id_apply]
  map_mul' x y := LinearEquiv.ext fun f => by
    show conjLin hS ht (x * y) f = conjLin hS ht x (conjLin hS ht y f)
    rw [conjLin_mul, LinearMap.comp_apply]

theorem conjHom_apply (x : ↥(bar M Q (Rt M (LB M Q B) t))) (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E)
    (w : ↥(S714.wsub hS t)) :
    conjHom hS ht x f w = (ρ (x : Mbar M Q)).toAdd (f (wAct hS ht x⁻¹ w)) := rfl

variable (t) in
@[expose] def deltaSub : Submodule K (↥(S714.wsub hS t) →ₗ[K] M₀.E) :=
  Submodule.span K {f | ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
    S714.delta hS t g (S714.mem_bar_H0_of_CN hg) = f}

theorem delta_mem_deltaSub {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    S714.delta hS t g (S714.mem_bar_H0_of_CN hg) ∈ deltaSub hS t :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem conjHom_delta (x : ↥(bar M Q (Rt M (LB M Q B) t))) {g : Mbar M Q}
    (hg : g ∈ bar M Q (H0 M Z)) :
    conjHom hS ht x (S714.delta hS t g hg) =
      S714.delta hS t ((x : Mbar M Q) * g * (x : Mbar M Q)⁻¹)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (S714.mem_bar_H0_of_Rt hc x.2) hg)
          (Subgroup.inv_mem _ (S714.mem_bar_H0_of_Rt hc x.2))) := by
  refine LinearMap.ext fun w => ?_
  rw [S714.delta_conj hS ht x.2 hg w, conjHom_apply]
  rfl

theorem conjHom_map_deltaSub (x : ↥(bar M Q (Rt M (LB M Q B) t))) :
    (deltaSub hS t).map ((conjHom hS ht x : _ ≃ₗ[K] _) : (↥(S714.wsub hS t) →ₗ[K] M₀.E) →ₗ[K]
      (↥(S714.wsub hS t) →ₗ[K] M₀.E)) = deltaSub hS t := by
  have hle : ∀ y : ↥(bar M Q (Rt M (LB M Q B) t)),
      (deltaSub hS t).map ((conjHom hS ht y : _ ≃ₗ[K] _) :
        (↥(S714.wsub hS t) →ₗ[K] M₀.E) →ₗ[K] (↥(S714.wsub hS t) →ₗ[K] M₀.E)) ≤ deltaSub hS t := by
    intro y
    rw [deltaSub, Submodule.map_span_le]
    rintro f ⟨g, hg, rfl⟩
    rw [LinearEquiv.coe_coe, conjHom_delta]
    exact delta_mem_deltaSub hS (hc.bar_CN_conj_mem ht y.2 hg)
  refine le_antisymm (hle x) fun f hf => ?_
  refine ⟨conjHom hS ht x⁻¹ f, hle x⁻¹ ⟨f, hf, rfl⟩, ?_⟩
  show (conjHom hS ht x) ((conjHom hS ht x⁻¹) f) = f
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, linEquiv_one_apply]

@[expose] def deltaAct :
    ↥(bar M Q (Rt M (LB M Q B) t)) →* (↥(deltaSub hS t) ≃ₗ[K] ↥(deltaSub hS t)) where
  toFun x := (conjHom hS ht x).ofSubmodules (deltaSub hS t) (deltaSub hS t)
    (conjHom_map_deltaSub hS ht x)
  map_one' := LinearEquiv.ext fun f => Subtype.ext (by
    show conjHom hS ht 1 (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) = f
    rw [map_one, linEquiv_one_apply])
  map_mul' x y := LinearEquiv.ext fun f => Subtype.ext (by
    show conjHom hS ht (x * y) (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) =
      conjHom hS ht x (conjHom hS ht y f)
    rw [map_mul, LinearEquiv.mul_apply])

theorem coe_deltaAct (x : ↥(bar M Q (Rt M (LB M Q B) t))) (f : ↥(deltaSub hS t)) :
    ((deltaAct hS ht x f : ↥(deltaSub hS t)) : ↥(S714.wsub hS t) →ₗ[K] M₀.E) =
      conjHom hS ht x f := rfl

theorem deltaAct_delta (x : ↥(bar M Q (Rt M (LB M Q B) t))) {g : Mbar M Q}
    (hg : g ∈ bar M Q (hc.CN t)) :
    deltaAct hS ht x ⟨S714.delta hS t g (S714.mem_bar_H0_of_CN hg), delta_mem_deltaSub hS hg⟩ =
      ⟨S714.delta hS t ((x : Mbar M Q) * g * (x : Mbar M Q)⁻¹)
        (S714.mem_bar_H0_of_CN (hc.bar_CN_conj_mem ht x.2 hg)),
        delta_mem_deltaSub hS (hc.bar_CN_conj_mem ht x.2 hg)⟩ :=
  Subtype.ext (conjHom_delta hS ht x _)

end Conj

section Trivial

variable (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
  (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)

include h310chi h52a hs hr in
theorem wvAct_of_mem_CN (x : ↥(bar M Q (Rt M (LB M Q B) t)))
    (hx : (x : Mbar M Q) ∈ bar M Q (hc.CN t)) : wvAct hS hs.toSec5.mem x = 1 := by
  refine LinearEquiv.ext fun w => ?_
  induction w using Submodule.Quotient.induction_on with
  | H w =>
    rw [wvAct_mk, linEquiv_one_apply, Submodule.Quotient.eq]
    obtain ⟨-, h2, -⟩ := S714.dmap_CN_facts h310chi h52a hS hs hr hx
    show ((wAct hS hs.toSec5.mem x w - w : ↥(S714.wsub hS t)) : M₀.E) ∈ hc.VtSub hS.model t
    rw [Submodule.coe_sub, wAct_apply]
    exact h2 w w.2

include h310chi h52a hs hr in
theorem conjHom_eq_self_of_mem_CN (x : ↥(bar M Q (Rt M (LB M Q B) t)))
    (hx : (x : Mbar M Q) ∈ bar M Q (hc.CN t)) (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E)
    (hfV : ∀ w : ↥(S714.wsub hS t), (w : M₀.E) ∈ hc.VtSub hS.model t → f w = 0)
    (hfW : ∀ w, f w ∈ hc.VtSub hS.model t) :
    conjHom hS hs.toSec5.mem x f = f := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxi : (x⁻¹ : ↥(bar M Q (Rt M (LB M Q B) t))).1 ∈ bar M Q (hc.CN t) := by
    rw [Subgroup.coe_inv]
    exact Subgroup.inv_mem _ hx
  obtain ⟨h1, -, -⟩ := S714.dmap_CN_facts h310chi h52a hS hs hr hx
  obtain ⟨-, h2, -⟩ := S714.dmap_CN_facts h310chi h52a hS hs hr hxi
  refine LinearMap.ext fun w => ?_
  rw [conjHom_apply]
  have hd : wAct hS ht x⁻¹ w - w ∈ vInW hS t := by
    show ((wAct hS ht x⁻¹ w - w : ↥(S714.wsub hS t)) : M₀.E) ∈ hc.VtSub hS.model t
    rw [Submodule.coe_sub, wAct_apply]
    exact h2 w w.2
  have hfw : f (wAct hS ht x⁻¹ w) = f w := by
    have h0 := hfV _ ((mem_vInW hS t).mp hd)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  rw [hfw]
  have h3 := h1 (f w) (hfW w)
  rw [S714.dmap, sub_eq_zero] at h3
  exact h3

include h310chi h52a hs hr in
theorem deltaAct_of_mem_CN (x : ↥(bar M Q (Rt M (LB M Q B) t)))
    (hx : (x : Mbar M Q) ∈ bar M Q (hc.CN t)) : deltaAct hS hs.toSec5.mem x = 1 := by
  have key : ∀ f ∈ deltaSub hS t, conjHom hS hs.toSec5.mem x f = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      obtain ⟨g1, g2, g3⟩ := S714.dmap_CN_facts h310chi h52a hS hs hr hg
      refine conjHom_eq_self_of_mem_CN h310chi h52a hS hs hr x hx _ (fun w hw => ?_)
        (fun w => ?_)
      · rw [S714.delta_apply]
        exact g1 _ hw
      · rw [S714.delta_apply]
        exact g2 _ w.2
    | zero => exact map_zero _
    | add f g _ _ hf hg => rw [map_add, hf, hg]
    | smul c f _ hf => rw [map_smul, hf]
  exact LinearEquiv.ext fun f => Subtype.ext (key f f.2)

end Trivial

section Mem

variable (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
  (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
  (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
  (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b)
  {t r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)

include h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hs hr in
theorem mem_deltaSub_iff {f : ↥(S714.wsub hS t) →ₗ[K] M₀.E} :
    f ∈ deltaSub hS t ↔ ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = S714.delta hS t g (S714.mem_bar_H0_of_CN hg) := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      exact ⟨g, hg, rfl⟩
    | zero =>
      refine ⟨1, Subgroup.one_mem _, LinearMap.ext fun w => ?_⟩
      rw [S714.delta_apply, S714.dmap_one, LinearMap.zero_apply]
    | add f g _ _ hf hg =>
      obtain ⟨g₁, hg₁, rfl⟩ := hf
      obtain ⟨g₂, hg₂, rfl⟩ := hg
      exact ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂,
        (S714.delta_mul h310chi h52a hS hs hr hg₁ hg₂).symm⟩
    | smul c f _ hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      obtain ⟨g', hg', h⟩ := S714.exists_delta_smul h34 hRoot h310chi h51 h52a h52b hNO hZc
        hCRW hMp hS hs hr hg c
      exact ⟨g', hg', h.symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact delta_mem_deltaSub hS hg

end Mem

end CFSG.RankThree.GF2n.Stroth80.S715L
