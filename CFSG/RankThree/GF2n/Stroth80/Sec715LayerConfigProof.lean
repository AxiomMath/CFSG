module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerConfigStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerConfigTri
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplit

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Module
open CFSG.RankThree.GF2n.Stroth80.S714
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

section Form

variable (hS : IsTensorSetup hc n M₀ ρ b) (t : G)

@[expose] noncomputable def wvForm : wvQ hS t →ₗ[K] wvQ hS t →ₗ[K] K :=
  LinearMap.liftQ₂ (vInW hS t) (vInW hS t) (M₀.B.compl₁₂ (wsub hS t).subtype (wsub hS t).subtype)
    (fun a ha => LinearMap.mem_ker.mpr (LinearMap.ext fun a' =>
      bilin_vsub_wsub hS t ((mem_vInW hS t).mp ha) a'.2))
    (fun a ha => LinearMap.mem_ker.mpr (LinearMap.ext fun a' =>
      bilin_wsub_vsub hS t a'.2 ((mem_vInW hS t).mp ha)))

theorem wvForm_mk (a a' : ↥(wsub hS t)) :
    wvForm hS t (Submodule.Quotient.mk a) (Submodule.Quotient.mk a') =
      M₀.B (a : M₀.E) (a' : M₀.E) := rfl

theorem wvForm_comm (m m' : wvQ hS t) : wvForm hS t m m' = -wvForm hS t m' m := by
  induction m using Submodule.Quotient.induction_on with
  | H a =>
    induction m' using Submodule.Quotient.induction_on with
    | H a' =>
      rw [wvForm_mk, wvForm_mk]
      exact Tim79.QuadModel.B_comm _ _

theorem wvForm_nondeg (m : wvQ hS t) (hm : ∀ m', wvForm hS t m m' = 0) : m = 0 := by
  haveI : Module.Finite K M₀.E := M₀.fin
  obtain ⟨hnd, hrefl⟩ := bilin_nondegenerate_isRefl (M₀ := M₀)
  induction m using Submodule.Quotient.induction_on with
  | H a =>
    refine (Submodule.Quotient.mk_eq_zero _).mpr ((mem_vInW hS t).mpr ?_)
    have hWW : M₀.B.orthogonal (wsub hS t) = hc.VtSub hS.model t := by
      rw [wsub_eq_orthogonal hS t]
      exact LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl _
    rw [← hWW, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have h1 := hm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [wvForm_mk] at h1
    show M₀.B y a = 0
    rw [Tim79.QuadModel.B_comm, h1, neg_zero]

variable {t} in
theorem wvForm_act (ht : t ∈ LB M Q B) (x : ↥(bar M Q (Rt M (LB M Q B) t))) (m m' : wvQ hS t) :
    wvForm hS t (wvAct hS ht x m) (wvAct hS ht x m') = wvForm hS t m m' := by
  induction m using Submodule.Quotient.induction_on with
  | H a =>
    induction m' using Submodule.Quotient.induction_on with
    | H a' =>
      rw [wvAct_mk, wvAct_mk, wvForm_mk, wvForm_mk, wAct_apply, wAct_apply]
      exact hS.iso _ (mem_bar_H0_of_Rt hc x.2) _ _

end Form

section Pair

variable (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
  (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
  (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))

@[expose] noncomputable def betaK8 : wvQ hS t →ₗ[K] ↥(deltaSub hS t) →ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  (betaQ h310chi h52a hS hs hr).compr₂ (e : ↥(hc.VtSub hS.model t) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))

theorem betaK8_apply (m : wvQ hS t) (f : ↥(deltaSub hS t)) :
    betaK8 h310chi h52a hS hs hr e m f = e (betaQ h310chi h52a hS hs hr m f) := rfl

theorem finrank_range_betaK8_flip (F : ↥(deltaSub hS t)) :
    finrank K (LinearMap.range ((betaK8 h310chi h52a hS hs hr e).flip F)) =
      finrank K (LinearMap.range (F : ↥(wsub hS t) →ₗ[K] M₀.E)) := by
  have h1 : (betaK8 h310chi h52a hS hs hr e).flip F =
      (e : ↥(hc.VtSub hS.model t) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∘ₗ
        (betaQ h310chi h52a hS hs hr).flip F := rfl
  have h2 : (F : ↥(wsub hS t) →ₗ[K] M₀.E) = (hc.VtSub hS.model t).subtype ∘ₗ
      ((betaQ h310chi h52a hS hs hr).flip F ∘ₗ (vInW hS t).mkQ) :=
    LinearMap.ext fun w => (coe_betaQ_mk h310chi h52a hS hs hr w F).symm
  rw [h1, h2, LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
    (Submodule.range_mkQ _), LinearEquiv.finrank_map_eq, Submodule.finrank_map_subtype_eq]

end Pair

section ConfigC

variable (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
  (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
  (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
  {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
  (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
    f = delta hS t g (mem_bar_H0_of_CN hg))
  (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))

include hMp hCommN hZ0 hSΔ in
theorem isLayerConfigC_of_pair
    (hC : IsPairConfigC (wvAct hS hs.toSec5.mem) (deltaAct hS hs.toSec5.mem)
      (betaK8 h310chi h52a hS hs hr e)) :
    IsLayerConfigC hS hs.toSec5.mem := by
  obtain ⟨M₃, M₄, N₄, N₃, hM, hN, h₄, h₃, hT2, hP3, hβ3, hβ4, hP5, hT⟩ := hC
  have hβ0 : ∀ (w : ↥(wsub hS t)) (f : ↥(deltaSub hS t)),
      betaK8 h310chi h52a hS hs hr e (Submodule.Quotient.mk w) f = 0 →
        (f : ↥(wsub hS t) →ₗ[K] M₀.E) w = 0 := fun w f h => by
    rw [betaK8_apply, LinearEquiv.map_eq_zero_iff] at h
    rw [← coe_betaQ_mk h310chi h52a hS hs hr w f, h]
    rfl
  refine ⟨M₃, M₄, N₄, N₃, hM, hN, h₄, h₃, hT2, fun w w' hw hw' => ?_, fun w f => ⟨fun hw hf =>
    hβ0 w f (hβ3 _ hw f hf), fun hw hf => hβ0 w f (hβ4 _ hw f hf)⟩, fun g hg h hh hg4 hh3 => ?_,
    fun f hf f' hf' hf0 hf'0 => ?_⟩
  · exact hP3 (wvForm hS t) (wvForm_act hS hs.toSec5.mem) _ hw _ hw'
  · have h0 := hP5 (bForm h310chi h52a hMp hCommN hS hs hr hZ0 (deltaSub hS t) hSΔ)
      (bForm_deltaAct h310chi h52a hMp hCommN hS hs hr hZ0 hSΔ) _ hg4 _ hh3
    rw [bForm_apply] at h0
    change bN hS hs.toSec5.mem (delta hS t g _) (delta hS t h _) = 0 at h0
    rw [bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 hg hh] at h0
    have h1 := (cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0
      (comm_mem_bar_Z0 hCommN hs hZ0 hg hh)).mp h0
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · rw [← finrank_range_betaK8_flip h310chi h52a hS hs hr e]
    exact hT f hf f' hf' hf0 hf'0

end ConfigC

section ConfigA

variable (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
  (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement) (hCRW : Sec7CRWStatement)
  (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
  {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
  (hZN : IsCentrePre Z0 (hc.CN t) Q)
  (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
    f = delta hS t g (mem_bar_H0_of_CN hg))
  {φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K}
  (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
  (he : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
    e (vAct hS hs.toSec5.mem x w) = (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e w)

private noncomputable def adjW (f : ↥(deltaSub hS t)) (u : M₀.E) : wvQ hS t :=
  Submodule.Quotient.mk ⟨dmap ρ (deltaLift hS t f) u,
    (dmap_CN_facts h310chi h52a hS hs hr (deltaLift_mem hS t f)).2.2 u⟩

include hSΔ in
private theorem wvForm_adjW (f : ↥(deltaSub hS t)) (u : M₀.E) (m : wvQ hS t) :
    wvForm hS t (adjW h310chi h52a hS hs hr f u) m =
      -M₀.B u ((betaQ h310chi h52a hS hs hr m f : ↥(hc.VtSub hS.model t)) : M₀.E) := by
  induction m using Submodule.Quotient.induction_on with
  | H w =>
    have hgH := mem_bar_H0_of_CN (deltaLift_mem hS t (f : ↥(wsub hS t) →ₗ[K] M₀.E))
    obtain ⟨-, hgW, hgE⟩ := dmap_CN_facts h310chi h52a hS hs hr
      (deltaLift_mem hS t (f : ↥(wsub hS t) →ₗ[K] M₀.E))
    have hadj := bilin_D_right (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t)
      (D := dlin hS _ hgH) (dmap_iso hS hgH) (fun x => hgE x) (fun w hw => hgW w hw)
      (fun w hw v hv => bilin_wsub_vsub hS t hw hv) u w.2
    rw [coe_betaQ_mk, ← dmap_deltaLift hS t (hSΔ _ f.2) w.2]
    exact hadj

include hMp hCommN hCRW hZ0 hZN hSΔ he in
theorem isLayerConfigA_of_pair [CharP K 2]
    (hA : IsPairConfigA φ₈ (wvAct hS hs.toSec5.mem) (deltaAct hS hs.toSec5.mem)
      (betaK8 h310chi h52a hS hs hr e)) :
    IsLayerConfigA hS hs.toSec5.mem := by
  obtain ⟨L₃, L₄, i₁, i₂, i₃, i₄, ρ₃, ρ₄, eM, eN, μ, q₃, q₄, hd₃, hd₄, hirr₃, hirr₄, heM, heN,
    hβ, hμ, hμ0, hq₃, hq₃nd, hq₄, hq₄nd, hPM, hPN⟩ := hA
  haveI : FiniteDimensional K L₃ := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K L₄ := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial L₃ := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  haveI : Nontrivial L₄ := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let μV : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t) :=
    μ.compr₂ (e.symm : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] ↥(hc.VtSub hS.model t))
  have hμV : ∀ a c, μV a c = e.symm (μ a c) := fun _ _ => rfl
  have hβQ : ∀ m f, betaQ h310chi h52a hS hs hr m f = ∑ i, μV (eM m i) (eN f i) := by
    intro m f
    apply e.injective
    rw [map_sum]
    simp only [hμV, LinearEquiv.apply_symm_apply]
    exact hβ m f
  obtain ⟨φ, hφ⟩ := hPM (wvForm hS t) (wvForm_act hS hs.toSec5.mem)
  obtain ⟨hφs, hφu⟩ := matrix_symm_isUnit_of_form q₃ hq₃nd (exists_ne 0) eM (wvForm hS t) φ hφ
    (fun m m' => by rw [wvForm_comm, CharTwo.neg_eq]) (wvForm_nondeg hS t)
  have hφψ : φ * φ⁻¹ = 1 := Matrix.mul_nonsing_inv φ hφu
  obtain ⟨Φ', hΦ'⟩ := hPN (bForm h310chi h52a hMp hCommN hS hs hr hZ0 (deltaSub hS t) hSΔ)
    (bForm_deltaAct h310chi h52a hMp hCommN hS hs hr hZ0 hSΔ)
  have hbN : ∀ (f f' : ↥(deltaSub hS t)) (u u' : M₀.E),
      bN hS hs.toSec5.mem (f : ↥(wsub hS t) →ₗ[K] M₀.E) f' *
          M₀.B (dmap ρ (tbar hc hs.toSec5.mem) u) u' =
        wvForm hS t (adjW h310chi h52a hS hs hr f u) (adjW h310chi h52a hS hs hr f' u') -
          wvForm hS t (adjW h310chi h52a hS hs hr f' u) (adjW h310chi h52a hS hs hr f u') :=
    fun f f' u u' => by
      have hb : bN hS hs.toSec5.mem (f : ↥(wsub hS t) →ₗ[K] M₀.E) f' =
          cscal hc ρ hs.toSec5.mem ⁅deltaLift hS t (f : ↥(wsub hS t) →ₗ[K] M₀.E),
            deltaLift hS t (f' : ↥(wsub hS t) →ₗ[K] M₀.E)⁆ := by
        conv_lhs => rw [← delta_deltaLift hS t (hSΔ _ f.2), ← delta_deltaLift hS t (hSΔ _ f'.2)]
        exact bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 (deltaLift_mem hS t _)
          (deltaLift_mem hS t _)
      rw [hb]
      exact cscal_comm_mul_bilin h310chi h52a hMp hCommN hS hs hr hZ0
        (deltaLift_mem hS t _) (deltaLift_mem hS t _) u u'
  have hq₄' : ∃ c c' : L₄, QuadraticMap.polar q₄ c c' ≠ 0 := by
    obtain ⟨c, hc⟩ := exists_ne (0 : L₄)
    by_contra hcon
    exact hc (hq₄nd c fun c' => by
      by_contra h
      exact hcon ⟨c, c', h⟩)
  obtain ⟨κ, hκ⟩ := exists_kappa_of_adjoint q₃ hq₃nd q₄ eM eN hφs hφψ (wvForm hS t) hφ μV
    (betaQ h310chi h52a hS hs hr) hβQ (M₀.B.compl₂ (hc.VtSub hS.model t).subtype)
    (adjW h310chi h52a hS hs hr) (wvForm_adjW h310chi h52a hS hs hr hSΔ)
    (fun f f' => bN hS hs.toSec5.mem (f : ↥(wsub hS t) →ₗ[K] M₀.E) f')
    (fun u u' => M₀.B (dmap ρ (tbar hc hs.toSec5.mem) u) u') hbN
    (fun f f' => by rw [← bForm_apply h310chi h52a hMp hCommN hS hs hr hZ0 _ hSΔ, hΦ'])
    (exists_bilin_dmap_tbar_ne_zero h310chi hS hs) hq₄'
  have hC7 : ∀ f f' : ↥(deltaSub hS t), bN hS hs.toSec5.mem (f : ↥(wsub hS t) →ₗ[K] M₀.E) f' =
      κ * ∑ i, ∑ j, φ⁻¹ i j * QuadraticMap.polar q₄ (eN f i) (eN f' j) := by
    intro f f'
    rw [← bForm_apply h310chi h52a hMp hCommN hS hs hr hZ0 _ hSΔ, hΦ', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hκ]
    ring
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ := exists_ne (0 : L₄)
    obtain ⟨g, hg, hfg⟩ := hSΔ _ (eN.symm fun _ => c).2
    have hker : (⟨delta hS t g (mem_bar_H0_of_CN hg), delta_mem_deltaSub hS hg⟩ :
        ↥(deltaSub hS t)) ∈ LinearMap.ker
          (bForm h310chi h52a hMp hCommN hS hs hr hZ0 (deltaSub hS t) hSΔ) := by
      refine LinearMap.mem_ker.mpr (LinearMap.ext fun f' => ?_)
      rw [bForm_apply, LinearMap.zero_apply]
      have := hC7 ⟨delta hS t g (mem_bar_H0_of_CN hg), delta_mem_deltaSub hS hg⟩ f'
      rwa [zero_mul] at this
    have hgZ := (mem_ker_bForm_iff h310chi h52a hMp hCommN hS hs hr hZ0 (deltaSub hS t) hSΔ
      (fun g hg => delta_mem_deltaSub hS hg) hZN hg).mp hker
    have hgR : g ∈ bar M Q (Rt M (LB M Q B) t) := by
      obtain ⟨m, hm, rfl⟩ := exists_of_mem_bar hg
      exact mk_mem_bar m (Ctx.mem_CN.mp hm).1
    have h0 := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hgR).mpr hgZ
    have h1 : (eN.symm fun _ => c) = 0 := Subtype.ext (hfg.trans h0)
    have h2 := congrFun (eN.symm.injective (h1.trans (map_zero _).symm)) 0
    exact hc h2
  refine ⟨L₃, L₄, i₁, i₂, i₃, i₄, ρ₃, ρ₄, eM, eN, μV, q₃, q₄, φ, φ⁻¹, κ, hd₃, hd₄, hirr₃, hirr₄,
    heM, heN, fun w f => ?_, fun x a c => ?_, fun h0 => hμ0 ?_, hq₃, hq₃nd, hq₄, hq₄nd, hφs, hφψ,
    fun w w' => (wvForm_mk hS t w w').symm.trans (hφ _ _), hκ0, hC7⟩
  · rw [← coe_betaQ_mk h310chi h52a hS hs hr w f, hβQ]
  · apply e.injective
    rw [hμV, LinearEquiv.apply_symm_apply, he, hμV, LinearEquiv.apply_symm_apply]
    exact hμ x a c
  · refine LinearMap.ext fun a => LinearMap.ext fun c => e.symm.injective ?_
    have := LinearMap.congr_fun (LinearMap.congr_fun h0 a) c
    rw [hμV] at this
    rw [this]
    simp

end ConfigA

theorem sec715LayerConfig_of (hSplit : Sec715LayerSplitStatement)
    (hTri : Omega8TrialityStatement) (hEnd : Omega8EndScalarStatement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement)
    (hZc : Sec7ZCardStatement) (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    (hCommN : Sec7CommNStatement) (hCV : Sec7CVStatement) (hA : Sec7AExistsStatement) :
    Sec715LayerConfigStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp hn Z0 hZ0 hZN K _ _ γ M₀ ρ b hS φ₈ hφ hφker e he
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨k, -, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  have hq : 4 ≤ Nat.card K := by
    rw [hS.card]
    exact hc.hyp.q4
  have P := isPairing_layers h34 h310chi h52a hCV hS hs hr φ₈ hφker e he
  obtain ⟨⟨Y₁, Y₂, hY, hY₁, hY₂, hdY₁, hdY₂, -, -⟩, ⟨Z₁, Z₂, hZ, hZ₁, hZ₂, hdZ₁, hdZ₂, -, -⟩⟩ :=
    hSplit G M Q Z B hc n t hs hp hn Z0 hZ0 hZN K γ M₀ ρ b hS φ₈ hφ hφker e he
  have hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg) := fun f hf =>
    (mem_deltaSub_iff h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hS hs hr).mp hf
  have hPS : PairSplitHyp φ₈ (wvAct hS hs.toSec5.mem) (deltaAct hS hs.toSec5.mem)
      (betaK8 h310chi h52a hS hs hr e) Y₁ Y₂ Z₁ Z₂ :=
    { kerM := P.kerM
      kerN := P.kerN
      eqv := fun x m f => by rw [betaK8_apply, betaK8_apply, P.equiv, P.he]
      sepL := fun m hm => P.left m fun f => e.injective ((hm f).trans (map_zero e).symm)
      sepR := fun f hf => P.right f fun m => e.injective ((hf m).trans (map_zero e).symm)
      complY := hY
      complZ := hZ
      irrY₁ := hY₁
      irrY₂ := hY₂
      irrZ₁ := hZ₁
      irrZ₂ := hZ₂
      dimY₁ := hdY₁
      dimY₂ := hdY₂
      dimZ₁ := hdZ₁
      dimZ₂ := hdZ₂ }
  rcases isPairConfigA_or_isPairConfigC hTri hEnd hq hφ hPS with hA' | hC'
  · exact Or.inl (isLayerConfigA_of_pair h310chi h52a hMp hCommN hCRW hS hs hr hZ0 hZN hSΔ e
      P.he hA')
  · exact Or.inr (isLayerConfigC_of_pair h310chi h52a hMp hCommN hS hs hr hZ0 hSΔ e hC')

end CFSG.RankThree.GF2n.Stroth80.S715L
