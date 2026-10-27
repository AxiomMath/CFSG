module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerDim
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommTrans
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

variable (hc) in
@[expose] def rbar (t : G) (r : ↥(Rt M (LB M Q B) t)) : ↥(bar M Q (Rt M (LB M Q B) t)) :=
  ⟨QuotientGroup.mk (⟨r, hc.Rt_le_M t r.2⟩ : ↥M), S714.mk_mem_bar _ r.2⟩

theorem rbar_surj (t : G) (x : ↥(bar M Q (Rt M (LB M Q B) t))) : ∃ r, rbar hc t r = x := by
  obtain ⟨m, hm, hmx⟩ := S714.exists_of_mem_bar x.2
  exact ⟨⟨m, hm⟩, Subtype.ext hmx⟩

section WV

variable (hS : IsTensorSetup hc n M₀ ρ b) (t : G)

@[expose] noncomputable def fWV (x : G) : wvQ hS t :=
  haveI := Classical.propDecidable (x ∈ Wt Q (Vt M (LB M Q B) B Z t))
  if hx : x ∈ Wt Q (Vt M (LB M Q B) B Z t) then
    Submodule.Quotient.mk ⟨M₀.π x, (S714.mem_wsub hS t).mpr (M₀.pi_mem_img hx hx.1)⟩
  else 0

theorem fWV_of_mem {x : G} (hx : x ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    fWV hS t x = Submodule.Quotient.mk ⟨M₀.π x, (S714.mem_wsub hS t).mpr (M₀.pi_mem_img hx hx.1)⟩ :=
  by rw [fWV, dif_pos hx]

variable {t}

theorem isLayerBridge_wv (h34 : Stroth34Statement) {n' : ℕ} (hs : Sec7Hyp hc n' t) :
    IsLayerBridge (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) (Rt M (LB M Q B) t)
      (wvAct hS hs.toSec5.mem) (fWV hS t) (rbar hc t) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := le_sup_left
  refine ⟨HS6.Vt_le_Wt h34 hc hs.toSec5, fun x hx y hy => ?_, fun v => ?_, fun x hx => ?_,
    fun r x hx => ?_, fun r x hx => ?_, rbar_surj t⟩
  · rw [fWV_of_mem hS t hx, fWV_of_mem hS t hy, fWV_of_mem hS t ((Wt Q _).mul_mem hx hy),
      ← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (M₀.π_mul x hx.1 y hy.1)
  · obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (vInW hS t) v
    obtain ⟨x, hxW, hxQ, hxw⟩ := M₀.mem_img.mp ((S714.mem_wsub hS t).mp w.2)
    refine ⟨x, hxW, ?_⟩
    rw [fWV_of_mem hS t hxW]
    congr 1
    exact Subtype.ext hxw
  · rw [fWV_of_mem hS t hx, Submodule.Quotient.mk_eq_zero, mem_vInW]
    show M₀.π x ∈ hc.VtSub hS.model t ↔ _
    rw [hc.mem_VtSub hS.model t]
    exact M₀.mem_img_iff hZV hx.1
  · have hrM : (r : G) ∈ M := hc.Rt_le_M t r.2
    exact conj_mem_Wt (hc.hyp.Q_normal.2 hrM) (hc.Rt_normalizes_Vt ht r.2) hx
  · have hrM : (r : G) ∈ M := hc.Rt_le_M t r.2
    have hx' : (r : G) * x * (r : G)⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
      conj_mem_Wt (hc.hyp.Q_normal.2 hrM) (hc.Rt_normalizes_Vt ht r.2) hx
    rw [fWV_of_mem hS t hx', fWV_of_mem hS t hx, wvAct_mk]
    congr 1
    refine Subtype.ext ?_
    rw [wAct_apply]
    exact hS.conj ⟨r, hrM⟩ x hx.1

end WV

section Delta

variable (hS : IsTensorSetup hc n M₀ ρ b) (t : G)

theorem mem_M_of_mem_CN {x : G} (hx : x ∈ hc.CN t) : x ∈ M :=
  hc.Rt_le_M t (Ctx.mem_CN.mp hx).1

@[expose] noncomputable def fDelta (x : G) : ↥(deltaSub hS t) :=
  haveI := Classical.propDecidable (x ∈ hc.CN t)
  if hx : x ∈ hc.CN t then
    ⟨S714.delta hS t (QuotientGroup.mk (⟨x, mem_M_of_mem_CN t hx⟩ : ↥M))
        (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hx)),
      delta_mem_deltaSub hS (S714.mk_mem_bar _ hx)⟩
  else 0

theorem coe_fDelta_of_mem {x : G} (hx : x ∈ hc.CN t) :
    (fDelta hS t x : ↥(S714.wsub hS t) →ₗ[K] M₀.E) =
      S714.delta hS t (QuotientGroup.mk (⟨x, mem_M_of_mem_CN t hx⟩ : ↥M))
        (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hx)) := by
  rw [fDelta, dif_pos hx]

variable {t}

theorem isLayerBridge_delta (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) {r : G} (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q) :
    IsLayerBridge Z0 (hc.CN t) (Rt M (LB M Q B) t) (deltaAct hS hs.toSec5.mem) (fDelta hS t)
      (rbar hc t) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  refine ⟨fun x hx => ((hZN x).mp hx).1, fun x hx y hy => ?_, fun v => ?_, fun x hx => ?_,
    fun s x hx => hc.CN_conj_mem ht s.2 hx, fun s x hx => ?_, rbar_surj t⟩
  · refine Subtype.ext ?_
    rw [Submodule.coe_add, coe_fDelta_of_mem hS t hx, coe_fDelta_of_mem hS t hy,
      coe_fDelta_of_mem hS t ((hc.CN t).mul_mem hx hy)]
    rw [← S714.delta_mul h310chi h52a hS hs hr (S714.mk_mem_bar _ hx) (S714.mk_mem_bar _ hy)]
    rfl
  · obtain ⟨g, hg, hgv⟩ := (mem_deltaSub_iff h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp
      hS hs hr).mp v.2
    obtain ⟨m, hm, rfl⟩ := S714.exists_of_mem_bar hg
    refine ⟨m, hm, Subtype.ext ?_⟩
    rw [coe_fDelta_of_mem hS t hm, hgv]
  · have hxR : x ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hx).1
    have h0 := S714.delta_eq_zero_iff hCRW hMp hS hs hZ0
      (S714.mk_mem_bar (⟨x, mem_M_of_mem_CN t hx⟩ : ↥M) hxR)
    constructor
    · intro h
      have h' : S714.delta hS t (QuotientGroup.mk (⟨x, mem_M_of_mem_CN t hx⟩ : ↥M))
          (S714.mem_bar_H0_of_Rt hc (S714.mk_mem_bar _ hxR)) = 0 := by
        rw [← coe_fDelta_of_mem hS t hx, h]
        rfl
      exact (Tim37.mk_mem_bar_iff' hQZ0 ⟨x, mem_M_of_mem_CN t hx⟩).mp (h0.mp h')
    · intro h
      refine Subtype.ext ?_
      rw [coe_fDelta_of_mem hS t hx]
      have := h0.mpr ((Tim37.mk_mem_bar_iff' hQZ0 ⟨x, mem_M_of_mem_CN t hx⟩).mpr h)
      exact (S714.delta_congr hS t rfl _ _).trans this
  · have hsx : (s : G) * x * (s : G)⁻¹ ∈ hc.CN t := hc.CN_conj_mem ht s.2 hx
    refine Subtype.ext ?_
    rw [coe_fDelta_of_mem hS t hsx, coe_deltaAct]
    have hfx : (fDelta hS t x : ↥(S714.wsub hS t) →ₗ[K] M₀.E) =
        S714.delta hS t (QuotientGroup.mk (⟨x, mem_M_of_mem_CN t hx⟩ : ↥M))
          (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hx)) := coe_fDelta_of_mem hS t hx
    rw [hfx, conjHom_delta]
    refine S714.delta_congr hS t ?_ _ _
    simp only [rbar, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rfl

end Delta

section Apply

variable (hS : IsTensorSetup hc n M₀ ρ b) {t : G}

theorem vtSub_le_wsub (h34 : Stroth34Statement) {n' : ℕ} (hs : Sec7Hyp hc n' t) :
    hc.VtSub hS.model t ≤ S714.wsub hS t := fun e he =>
  (S714.mem_wsub hS t).mpr (M₀.img_mono (HS6.Vt_le_Wt h34 hc hs.toSec5) ((hc.mem_VtSub hS.model t).mp he))

theorem finrank_wvQ (h34 : Stroth34Statement) {n' : ℕ} (hs : Sec7Hyp hc n' t)
    (hp : OmegaPlusNat hc t 4) (hn : n = 16) : Module.finrank K (wvQ hS t) = 16 := by
  have h1 := (vInW hS t).finrank_quotient_add_finrank
  have h2 : Module.finrank K ↥(vInW hS t) = 8 := by
    rw [vInW, (Submodule.comapSubtypeEquivOfLe (vtSub_le_wsub hS h34 hs)).finrank_eq]
    exact finrank_vtSub hS hs.toSec5.mem hp
  rw [h2, finrank_wsub hS hs.toSec5.mem hp hn] at h1
  show Module.finrank K (↥(S714.wsub hS t) ⧸ vInW hS t) = 16
  omega

omit [Finite G] [(Q.subgroupOf M).Normal] in
theorem card_submodule_eq (hK : Nat.card K = Nat.card Z) {X : Type} [AddCommGroup X]
    [Module K X] [FiniteDimensional K X] (U : Submodule K X) :
    Nat.card U = Nat.card Z ^ Module.finrank K U := by
  rw [Module.natCard_eq_pow_finrank (K := K), hK]

theorem minDim_wv (h34 : Stroth34Statement) (hWV : Sec7WVMinOrderStatement) {n' : ℕ}
    (hs : Sec7Hyp hc n' t) (hp : OmegaPlusNat hc t 4) (U : Submodule K (wvQ hS t))
    (hU : IsInvSub (wvAct hS hs.toSec5.mem) U) (hU0 : U ≠ ⊥) : 8 ≤ Module.finrank K U := by
  have hB := isLayerBridge_wv hS h34 hs
  have hle := (hWV G M Q Z B hc n' t hs (hB.pre U) (hB.V_le_pre U) (hB.pre_le_W U)
    (fun r hr => hB.conj_pre hU r hr) (hB.pre_ne_of_ne_bot hU0) 4 (by norm_num)).2 hp (by norm_num)
  rw [hB.card_pre U, card_submodule_eq hS.card U] at hle
  have hpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  have h' : Nat.card Z ^ 8 ≤ Nat.card Z ^ Module.finrank K U := by
    have := Nat.le_of_mul_le_mul_left hle hpos
    simpa using this
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  exact (Nat.pow_le_pow_iff_right hq).mp h'

theorem proj_wv (h34 : Stroth34Statement) (hExt : Ext1VanishingD4Statement) (hs : Sec7Hyp hc n t)
    (hp : OmegaPlusNat hc t 4) (hn : n = 16) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (U : Submodule K (wvQ hS t)) (hU : IsInvSub (wvAct hS hs.toSec5.mem) U) :
    ∃ p : wvQ hS t →+ wvQ hS t, (∀ v, p v ∈ U) ∧ (∀ u ∈ U, p u = u) ∧
      ∀ h v, p (wvAct hS hs.toSec5.mem h v) = wvAct hS hs.toSec5.mem h (p v) := by
  have hB := isLayerBridge_wv hS h34 hs
  obtain ⟨A', hVA', hA'W, hA'R, hsup, hinf⟩ := (hExt G M Q Z B hc n t hs hp hn Z0 hZ0 hZN).2
    (hB.pre U) (hB.V_le_pre U) (hB.pre_le_W U) (fun r hr => hB.conj_pre hU r hr)
  exact hB.exists_proj hU A' hA'W hA'R hsup hinf

theorem finrank_deltaSub (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) {r : G} (hs : Sec7Hyp hc n t)
    (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) (hn : n = 16) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : IsCentrePre Z0 (hc.CN t) Q) :
    Module.finrank K ↥(deltaSub hS t) = 16 := by
  have hB := isLayerBridge_delta hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hs hr hZ0
    hZN
  have htop : hB.pre ⊤ = hc.CN t := le_antisymm (hB.pre_le_W ⊤) fun x hx => ⟨hx, trivial⟩
  have hc1 := hB.card_pre ⊤
  rw [htop, card_submodule_eq hS.card ⊤, finrank_top] at hc1
  have hNO' := hNO G M Q Z B hc n t hs 4 (by norm_num) (Or.inl hp)
  have hZ0c := hZc G M Q Z B hc n t hs Z0 hZ0
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
  rw [hn] at hw
  rw [hc1, hZ0c, hw] at hNO'
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have hq0 : 0 < Nat.card Z := by omega
  have key : Nat.card Z ^ (34 + Module.finrank K ↥(deltaSub hS t) + 16) = Nat.card Z ^ 66 := by
    have e1 : Nat.card Z ^ (34 + Module.finrank K ↥(deltaSub hS t) + 16) =
        Nat.card Z ^ (2 * 16 + 1) * Nat.card Z * Nat.card Z ^ Module.finrank K ↥(deltaSub hS t) *
          Nat.card Z ^ (4 * 4) := by ring
    rw [e1, hNO']
    ring
  have := Nat.pow_right_injective (by omega : 2 ≤ Nat.card Z) key
  omega

theorem minDim_delta (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (h79 : Sec79MinOrderStatement)
    {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q) (U : Submodule K ↥(deltaSub hS t))
    (hU : IsInvSub (deltaAct hS hs.toSec5.mem) U) (hU0 : U ≠ ⊥) : 8 ≤ Module.finrank K U := by
  have hB := isLayerBridge_delta hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hs hr hZ0
    hZN
  have hle := (h79 G M Q Z B hc n t hs Z0 hZ0 (hB.pre U) (hB.V_le_pre U) (hB.pre_le_W U)
    (fun r hr => hB.conj_pre hU r hr) (hB.pre_ne_of_ne_bot hU0) 4 (by norm_num)).2 hp
    (by norm_num)
  rw [hB.card_pre U, card_submodule_eq hS.card U] at hle
  have hpos : 0 < Nat.card ↥Z0 := Nat.card_pos
  have h' : Nat.card Z ^ 8 ≤ Nat.card Z ^ Module.finrank K U := by
    have := Nat.le_of_mul_le_mul_left hle hpos
    simpa using this
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  exact (Nat.pow_le_pow_iff_right hq).mp h'

theorem proj_delta (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hExt : Ext1VanishingD4Statement)
    {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) (hn : n = 16)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q) (U : Submodule K ↥(deltaSub hS t))
    (hU : IsInvSub (deltaAct hS hs.toSec5.mem) U) :
    ∃ p : ↥(deltaSub hS t) →+ ↥(deltaSub hS t), (∀ v, p v ∈ U) ∧ (∀ u ∈ U, p u = u) ∧
      ∀ h v, p (deltaAct hS hs.toSec5.mem h v) = deltaAct hS hs.toSec5.mem h (p v) := by
  have hB := isLayerBridge_delta hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hs hr hZ0
    hZN
  obtain ⟨A', -, hA'N, hA'R, hsup, hinf⟩ := (hExt G M Q Z B hc n t hs hp hn Z0 hZ0 hZN).1
    (hB.pre U) (hB.V_le_pre U) (hB.pre_le_W U) (fun r hr => hB.conj_pre hU r hr)
  exact hB.exists_proj hU A' hA'N hA'R hsup hinf

end Apply

end CFSG.RankThree.GF2n.Stroth80.S715L
