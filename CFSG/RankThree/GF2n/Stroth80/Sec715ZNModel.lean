module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerForms
public import CFSG.RankThree.GF2n.Stroth80.Sec715ZNParts
public import CFSG.RankThree.GF2n.Stroth80.Sec715ZNQuot
public import CFSG.RankThree.GF2n.Stroth80.QuadSpaceScalars
public import CFSG.RankThree.GF2n.Stroth80.Step715ZNReduction
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommTrans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


theorem sec715ZNModel_of_setup (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h711 : Stroth711StrongStatement) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {K' : Type} [Field K'] [Finite K']
    {γ' : G → K'} {M₀' : Tim79.QuadModel Q Z K' γ'}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀'.E)} {b : M₀'.E}
    (hS : IsTensorSetup hc 16 M₀' ρ b) {t r : G} (hs : Sec7Hyp hc 16 t) (hr : Sec7A hc t r)
    (hp4 : OmegaPlusNat hc t 4) {Z0 Zn Y : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZn : IsCentrePre Zn (hc.CN t) Q)
    (hne : Zn ≠ Z0) (hYZ0 : Y ⊓ Z0 = Q) (hYsup : Y ⊔ Z0 = Zn)
    (hcsurj : ∀ s : K', ∃ a ∈ bar M Q Z0, S715L.cscal hc ρ hs.toSec5.mem a = s)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {H : Type} [Group H]
    (θ : ↥(Rt M (LB M Q B) t) →* H) (hθ : Function.Surjective θ)
    (hθker : θ.ker = Y.subgroupOf (Rt M (LB M Q B) t)) :
    ∃ (γ : H → K) (M₀ : Tim79.QuadModel
        (((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ)
        ((Z0.subgroupOf (Rt M (LB M Q B) t)).map θ) K γ)
      (ψ : H →* (M₀.E ≃ₗ[K] M₀.E)),
      Tim79.GammaReg (((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ)
        ((Z0.subgroupOf (Rt M (LB M Q B) t)).map θ) γ ∧ CharP K 2 ∧
      Module.finrank K M₀.E = 8 ∧
      (∀ g : H, ∀ x ∈ ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ,
        M₀.π (g * x * g⁻¹) = ψ g (M₀.π x)) ∧
      (∀ g : H, ∀ v, M₀.Qf (ψ g v) = M₀.Qf v) ∧
      (∀ g : H, ψ g = 1 ↔ g ∈ ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).map θ) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hNM : ∀ x ∈ hc.CN t, x ∈ M := fun x hx => hRM (hNR hx)
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hZnN : Zn ≤ hc.CN t := fun x hx => ((hZn x).mp hx).1
  have hYZn : Y ≤ Zn := hYsup ▸ le_sup_left
  have hQY : Q ≤ Y := hYZ0 ▸ inf_le_left
  have hQZn : Q ≤ Zn := hQY.trans hYZn
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZ0N
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hNsq : ∀ x ∈ hc.CN t, x ^ 2 ∈ Z0 := hopp.2.2.2.2.2.2.2.1
  obtain ⟨f₀, -, hf₀, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hf₀)
  have hsplit : ∀ z ∈ Zn, ∃ y ∈ Y, ∃ z₀ ∈ Z0, z = y * z₀ := by
    intro z hz
    haveI : (Y.subgroupOf (Rt M (LB M Q B) t)).Normal := by
      rw [← hθker]
      exact θ.normal_ker
    have hYR : Y ≤ Rt M (LB M Q B) t := (hYZn.trans hZnN).trans hNR
    have hZR : Z0 ≤ Rt M (LB M Q B) t := hZ0N.trans hNR
    have hzR : z ∈ Rt M (LB M Q B) t := hNR (hZnN hz)
    have h1 : (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)) ∈
        Y.subgroupOf (Rt M (LB M Q B) t) ⊔ Z0.subgroupOf (Rt M (LB M Q B) t) := by
      rw [← Subgroup.subgroupOf_sup hYR hZR, hYsup, Subgroup.mem_subgroupOf]
      exact hz
    have h2 : (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)) ∈
        ((Y.subgroupOf (Rt M (LB M Q B) t) ⊔ Z0.subgroupOf (Rt M (LB M Q B) t) :
          Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) := h1
    rw [Subgroup.normal_mul] at h2
    obtain ⟨a, ha, c, hc', hac⟩ := Set.mem_mul.mp h2
    refine ⟨a, Subgroup.mem_subgroupOf.mp ha, c, Subgroup.mem_subgroupOf.mp hc', ?_⟩
    have h3 := congrArg Subtype.val hac
    rw [Subgroup.coe_mul] at h3
    exact h3.symm
  have hSΔ : ∀ f ∈ S715L.deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = S714.delta hS t g (S714.mem_bar_H0_of_CN hg) := fun f hf =>
    (S715L.mem_deltaSub_iff h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hS hs hr).mp hf
  have hΔS : ∀ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      S714.delta hS t g (S714.mem_bar_H0_of_CN hg) ∈ S715L.deltaSub hS t := fun g hg =>
    S715L.delta_mem_deltaSub hS hg
  let B₀ := S715L.bForm h310chi h52a hMp hCommN hS hs hr hZ0 (S715L.deltaSub hS t) hSΔ
  let Qf₀ : ↥(S715L.deltaSub hS t) → K' := fun f => S715L.qN hS ht f
  have hrad : ∀ f : ↥(S715L.deltaSub hS t), (∀ f', B₀ f f' = 0) → Qf₀ f = 0 := by
    intro f hf
    obtain ⟨g, hg, hfg⟩ := hSΔ f f.2
    have hf' : f = ⟨S714.delta hS t g (S714.mem_bar_H0_of_CN hg), hΔS g hg⟩ := Subtype.ext hfg
    rw [hf'] at hf
    have hgZ := (S715L.forall_bForm_eq_zero_iff h310chi h52a hMp hCommN hS hs hr hZ0
      (S715L.deltaSub hS t) hSΔ hΔS hZn hg).mp hf
    obtain ⟨z, hz, rfl⟩ := S714.exists_of_mem_bar hgZ
    obtain ⟨y, hy, z₀, hz₀, hyz⟩ := hsplit z hz
    have hyN : y ∈ hc.CN t := hYZn.trans hZnN hy
    have hyM : y ∈ M := hNM y hyN
    have hz₀M : z₀ ∈ M := hNM z₀ (hZ0N hz₀)
    have hyb : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
      S714.mk_mem_bar _ hyN
    have hz₀b : (QuotientGroup.mk (⟨z₀, hz₀M⟩ : ↥M) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
      S714.mk_mem_bar _ (hZ0N hz₀)
    have hzeq : (QuotientGroup.mk z : Mbar M Q) =
        QuotientGroup.mk (⟨y, hyM⟩ : ↥M) * QuotientGroup.mk (⟨z₀, hz₀M⟩ : ↥M) := by
      rw [← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hyz
    have hΔz₀ : S714.delta hS t (QuotientGroup.mk (⟨z₀, hz₀M⟩ : ↥M))
        (S714.mem_bar_H0_of_CN hz₀b) = 0 := by
      have h1 := (S714.delta_eq_zero_iff hCRW hMp hS hs hZ0
        (S714.mk_mem_bar (S := Rt M (LB M Q B) t) ⟨z₀, hz₀M⟩ (hNR (hZ0N hz₀)))).mpr
        (S714.mk_mem_bar ⟨z₀, hz₀M⟩ hz₀)
      exact h1
    have hΔ : S714.delta hS t (QuotientGroup.mk z) (S714.mem_bar_H0_of_CN hg) =
        S714.delta hS t (QuotientGroup.mk (⟨y, hyM⟩ : ↥M)) (S714.mem_bar_H0_of_CN hyb) := by
      rw [S714.delta_congr hS t hzeq _ (Subgroup.mul_mem _ (S714.mem_bar_H0_of_CN hyb)
        (S714.mem_bar_H0_of_CN hz₀b)), S714.delta_mul h310chi h52a hS hs hr hyb hz₀b, hΔz₀,
        add_zero]
    show S715L.qN hS ht (f : ↥(S714.wsub hS t) →ₗ[K'] M₀'.E) = 0
    rw [hfg, hΔ, S715L.qN_delta h310chi h51 h52a hMp hCommN hS hs hr hZ0 hyb]
    have hy2Z : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) ^ 2 ∈ bar M Q Z0 :=
      S715L.sq_mem_bar_Z0 h51 hs hr hZ0 hyb
    refine (S715L.cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0 hy2Z).mpr ?_
    have hy2Q : y ^ 2 ∈ Q := by
      rw [← hYZ0]
      exact Subgroup.mem_inf.mpr ⟨Y.pow_mem hy 2, hNsq y hyN⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hy2Q
  obtain ⟨E₁, iE₁, iM₁, iF₁, p, B₁, Qf₁, ρ₁, hpsurj, hpker, -, hB₁, hQf₁, hρ₁, hρ₁Q, halt₁, hnd₁,
    hsmul₁, hadd₁⟩ := exists_quotient_quadSpace B₀ Qf₀
      (S715L.bForm_self h310chi h52a hMp hCommN hS hs hr hZ0 (S715L.deltaSub hS t) hSΔ)
      (fun a f => S715L.qN_smul h310chi h51 h52a hMp hCommN hS hs hr hZ0
        (S715L.deltaSub hS t) hSΔ a f)
      (fun f f' => S715L.qN_add h310chi h51 h52a hMp hCommN hS hs hr hZ0
        (S715L.deltaSub hS t) hSΔ f f') hrad (S715L.deltaAct hS ht)
      (fun x f => S715L.qN_deltaAct h310chi h51 h52a hMp hCommN hS hs hr hZ0 hSΔ x f)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  let σ : K ≃+* K' := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK, hS.card])
  obtain ⟨E, iE, iM, iF, j, B', Qf', ρ', -, hBj, hQj, hρj, hρ'Q, halt, hnd, hsmul, hadd, -⟩ :=
    exists_quadSpace_ringEquiv σ B₁ Qf₁ halt₁ hnd₁ hsmul₁ hadd₁ ρ₁ hρ₁Q
  let cls : G → ↥(S715L.deltaSub hS t) := fun x =>
    if hx : x ∈ hc.CN t then
      ⟨S714.delta hS t (QuotientGroup.mk (⟨x, hNM x hx⟩ : ↥M))
        (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hx)), hΔS _ (S714.mk_mem_bar _ hx)⟩
    else 0
  have hcls : ∀ x (hx : x ∈ hc.CN t), cls x =
      ⟨S714.delta hS t (QuotientGroup.mk (⟨x, hNM x hx⟩ : ↥M))
        (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hx)), hΔS _ (S714.mk_mem_bar _ hx)⟩ :=
    fun x hx => dif_pos hx
  let πG : G → E := fun x => j (p (cls x))
  let cG : G → K := fun x =>
    if hx : x ∈ M then σ.symm (S715L.cscal hc ρ ht (QuotientGroup.mk (⟨x, hx⟩ : ↥M))) else 0
  have hcG : ∀ x (hx : x ∈ M),
      cG x = σ.symm (S715L.cscal hc ρ ht (QuotientGroup.mk (⟨x, hx⟩ : ↥M))) :=
    fun x hx => dif_pos hx
  let barR : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (Rt M (LB M Q B) t)) :=
    { toFun := fun x => ⟨QuotientGroup.mk (⟨x, hRM x.2⟩ : ↥M), S714.mk_mem_bar _ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ρG : ↥(Rt M (LB M Q B) t) →* (E ≃ₗ[K] E) := ρ'.comp barR
  have hπmul : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, πG (x * y) = πG x + πG y := by
    intro x hx y hy
    show j (p (cls (x * y))) = j (p (cls x)) + j (p (cls y))
    rw [← map_add, ← map_add, hcls _ (Subgroup.mul_mem _ hx hy), hcls _ hx, hcls _ hy]
    congr 2
    refine Subtype.ext ?_
    rw [Submodule.coe_add, ← S714.delta_mul h310chi h52a hS hs hr (S714.mk_mem_bar _ hx)
      (S714.mk_mem_bar _ hy)]
    exact S714.delta_congr hS t rfl _ _
  have hπsurj : ∀ e, ∃ x ∈ hc.CN t, πG x = e := by
    intro e
    obtain ⟨e₁, rfl⟩ := j.surjective e
    obtain ⟨f, rfl⟩ := hpsurj e₁
    obtain ⟨g, hg, hfg⟩ := hSΔ f f.2
    obtain ⟨x, hx, rfl⟩ := S714.exists_of_mem_bar hg
    refine ⟨(x : G), hx, ?_⟩
    show j (p (cls x)) = j (p f)
    rw [hcls _ hx]
    congr 2
    refine Subtype.ext ?_
    rw [hfg]
  have hπker : ∀ x ∈ hc.CN t, πG x = 0 ↔ x ∈ Zn := by
    intro x hx
    show j (p (cls x)) = 0 ↔ x ∈ Zn
    rw [map_eq_zero_iff j j.injective, hpker, hcls _ hx,
      S715L.forall_bForm_eq_zero_iff h310chi h52a hMp hCommN hS hs hr hZ0 (S715L.deltaSub hS t)
        hSΔ hΔS hZn (S714.mk_mem_bar _ hx)]
    exact Tim37.mk_mem_bar_iff' hQZn (⟨x, hNM x hx⟩ : ↥M)
  have hcadd : ∀ a ∈ Z0, ∀ c ∈ Z0, cG (a * c) = cG a + cG c := by
    intro a ha c hc'
    have haM : a ∈ M := hNM a (hZ0N ha)
    have hcM : c ∈ M := hNM c (hZ0N hc')
    rw [hcG _ (M.mul_mem haM hcM), hcG _ haM, hcG _ hcM, ← map_add]
    congr 1
    exact S715L.cscal_mul h310chi h52a hMp hS hs hr hZ0 (S714.mk_mem_bar ⟨a, haM⟩ ha)
      (S714.mk_mem_bar ⟨c, hcM⟩ hc')
  have hcker : ∀ a ∈ Z0, cG a = 0 ↔ a ∈ Q := by
    intro a ha
    have haM : a ∈ M := hNM a (hZ0N ha)
    rw [hcG _ haM, map_eq_zero_iff _ σ.symm.injective,
      S715L.cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0 (S714.mk_mem_bar ⟨a, haM⟩ ha),
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcsurjG : ∀ s : K, ∃ a ∈ Z0, cG a = s := by
    intro s
    obtain ⟨a, ha, has⟩ := hcsurj (σ s)
    obtain ⟨x, hx, rfl⟩ := S714.exists_of_mem_bar ha
    refine ⟨(x : G), hx, ?_⟩
    rw [hcG _ x.2]
    show σ.symm (S715L.cscal hc ρ ht (QuotientGroup.mk x)) = s
    rw [has, RingEquiv.symm_apply_apply]
  have hcomm_eq : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, cG ⁅x, y⁆ = B' (πG x) (πG y) := by
    intro x hx y hy
    have hxyM : ⁅x, y⁆ ∈ M := hNM _ (hZ0N (hNcomm x hx y hy))
    show cG ⁅x, y⁆ = B' (j (p (cls x))) (j (p (cls y)))
    rw [hcG _ hxyM, hBj, hB₁, hcls _ hx, hcls _ hy]
    show σ.symm (S715L.cscal hc ρ ht (QuotientGroup.mk (⟨⁅x, y⁆, hxyM⟩ : ↥M))) =
      σ.symm (S715L.bForm h310chi h52a hMp hCommN hS hs hr hZ0 (S715L.deltaSub hS t) hSΔ _ _)
    rw [S715L.bForm_apply]
    show σ.symm (S715L.cscal hc ρ ht (QuotientGroup.mk (⟨⁅x, y⁆, hxyM⟩ : ↥M))) =
      σ.symm (S715L.bN hS ht (S714.delta hS t _ (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hx)))
        (S714.delta hS t _ (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hy))))
    rw [S715L.bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 (S714.mk_mem_bar _ hx)
      (S714.mk_mem_bar _ hy)]
    rfl
  have hsq_eq : ∀ x ∈ hc.CN t, cG (x ^ 2) = Qf' (πG x) := by
    intro x hx
    have hx2M : x ^ 2 ∈ M := hNM _ (hZ0N (hNsq x hx))
    show cG (x ^ 2) = Qf' (j (p (cls x)))
    rw [hcG _ hx2M, hQj, hQf₁, hcls _ hx]
    show σ.symm (S715L.cscal hc ρ ht (QuotientGroup.mk (⟨x ^ 2, hx2M⟩ : ↥M))) =
      σ.symm (S715L.qN hS ht
        (S714.delta hS t _ (S714.mem_bar_H0_of_CN (S714.mk_mem_bar _ hx))))
    rw [S715L.qN_delta h310chi h51 h52a hMp hCommN hS hs hr hZ0 (S714.mk_mem_bar _ hx)]
    congr 2
  have hρπ : ∀ (r' : ↥(Rt M (LB M Q B) t)), ∀ x ∈ hc.CN t,
      πG ((r' : G) * x * (r' : G)⁻¹) = ρG r' (πG x) := by
    intro r' x hx
    have hrx : (r' : G) * x * (r' : G)⁻¹ ∈ hc.CN t := S714.conj_mem_CN hc ht r'.2 hx
    show j (p (cls ((r' : G) * x * (r' : G)⁻¹))) = ρ' (barR r') (j (p (cls x)))
    rw [hρj, hρ₁, hcls _ hrx, hcls _ hx, S715L.deltaAct_delta hS ht (barR r')
      (S714.mk_mem_bar _ hx)]
    congr 2
  have hρQ : ∀ (r' : ↥(Rt M (LB M Q B) t)) e, Qf' (ρG r' e) = Qf' e := fun r' e =>
    hρ'Q (barR r') e
  have hcommN : ∀ (r' : ↥(Rt M (LB M Q B) t)), ∀ x ∈ hc.CN t,
      πG ((r' : G) * x * (r' : G)⁻¹) = πG ⁅(r' : G), x⁆ + πG x := by
    intro r' x hx
    have hrx : (r' : G) * x * (r' : G)⁻¹ ∈ hc.CN t := S714.conj_mem_CN hc ht r'.2 hx
    have hcm : ⁅(r' : G), x⁆ ∈ hc.CN t := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ hrx (Subgroup.inv_mem _ hx)
    rw [← hπmul _ hcm _ hx, commutatorElement_def, inv_mul_cancel_right]
  have hρker : ∀ r' : ↥(Rt M (LB M Q B) t), ρG r' = 1 ↔ (r' : G) ∈ hc.CN t := by
    intro r'
    rw [← sec715_comm_mem_Zn_iff h51 hA hPts h711 hc hs hp4 hZ0 hZn (r' : G) r'.2]
    constructor
    · intro h1 x hx
      have hcm : ⁅(r' : G), x⁆ ∈ hc.CN t := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (S714.conj_mem_CN hc ht r'.2 hx) (Subgroup.inv_mem _ hx)
      have h2 := hρπ r' x hx
      rw [h1, hcommN r' x hx] at h2
      have h3 : πG ⁅(r' : G), x⁆ = 0 := by
        have h4 : πG ⁅(r' : G), x⁆ + πG x = 0 + πG x := by
          rw [h2, zero_add]
          rfl
        exact add_right_cancel h4
      exact (hπker _ hcm).mp h3
    · intro h1
      refine LinearEquiv.ext fun e => ?_
      obtain ⟨x, hx, rfl⟩ := hπsurj e
      have hcm : ⁅(r' : G), x⁆ ∈ hc.CN t := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (S714.conj_mem_CN hc ht r'.2 hx) (Subgroup.inv_mem _ hx)
      rw [← hρπ r' x hx, hcommN r' x hx, (hπker _ hcm).mpr (h1 x hx), zero_add]
      rfl
  obtain ⟨γ, M₀, ψ, hreg, hdimE, hcomp, hiso, hker⟩ :=
    exists_quadModel_of_surjective πG cG B' Qf' hπmul hπsurj hπker hcadd hcker hcsurjG hNcomm hNsq
      hcomm_eq hsq_eq halt hnd hsmul hadd ρG hρπ hρQ hρker hNR hZ0N hZnN hYZ0 hYsup θ hθ hθker
  refine ⟨γ, M₀, ψ, hreg, inferInstance, ?_, hcomp, hiso, hker⟩
  rw [hdimE]
  let φN : ↥(hc.CN t) →* Multiplicative E :=
    { toFun := fun x => Multiplicative.ofAdd (πG x)
      map_one' := by
        show Multiplicative.ofAdd (πG 1) = 1
        rw [(hπker 1 (Subgroup.one_mem _)).mpr (Subgroup.one_mem _), ofAdd_zero]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (πG ((x : G) * y)) =
          Multiplicative.ofAdd (πG x) * Multiplicative.ofAdd (πG y)
        rw [hπmul _ x.2 _ y.2, ofAdd_add] }
  have hφsurj : Function.Surjective φN := by
    intro e
    obtain ⟨x, hx, hxe⟩ := hπsurj (Multiplicative.toAdd e)
    exact ⟨⟨x, hx⟩, by show Multiplicative.ofAdd (πG x) = e; rw [hxe]; rfl⟩
  have hφker : φN.ker = Zn.subgroupOf (hc.CN t) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hπker _ x.2]
    show Multiplicative.ofAdd (πG x) = 1 ↔ πG x = 0
    exact ofAdd_eq_one
  have hcardE := Subgroup.card_ker_mul_card_of_surjective hφsurj
  rw [hφker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZnN).toEquiv,
    Nat.card_congr Multiplicative.toAdd] at hcardE
  obtain ⟨-, hNZn⟩ := sec715_card_Zn h51 hA hPts hNO h711 hc hs hp4 hZ0 hZn hne
  have hZnpos : 0 < Nat.card ↥Zn := Nat.card_pos
  have hE8 : Nat.card E = Nat.card ↥Z ^ 8 := by
    apply Nat.eq_of_mul_eq_mul_left hZnpos
    rw [hcardE, hNZn]
  have hdim := Module.natCard_eq_pow_finrank (K := K) (V := E)
  rw [hE8, ← hK] at hdim
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  exact (Nat.pow_right_injective hK2 hdim).symm

theorem sec715ZNModel_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h711 : Stroth711StrongStatement) : Sec715ZNModelStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp4 hn16 Z0 Zn Y hZ0 hZn hne _ _ hYZ0 hYsup K _ _ hK H _ θ hθ
    hθker
  subst hn16
  obtain ⟨r, hr⟩ := hA G M Q Z B hc 16 t hs
  obtain ⟨K', _, _, γ', M₀', ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc 16 hs.toSec5.width
    hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  exact sec715ZNModel_of_setup h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hCommN hA hPts
    h711 hS hs hr hp4 hZ0 hZn hne hYZ0 hYsup
    (fun k => S715L.cscal_surj h310chi h52a hMp hZc hS hs hr hZ0 k) hK θ hθ hθker

end CFSG.RankThree.GF2n.Stroth80
