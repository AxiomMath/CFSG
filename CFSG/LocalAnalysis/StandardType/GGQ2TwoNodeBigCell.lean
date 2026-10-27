module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeRestDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoNode
public import CFSG.LocalAnalysis.StandardType.GGQ2PmHeartA
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemmaH4
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeI1Rank
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBig
import CFSG.LocalAnalysis.StandardType.GGQ2ReflMovesLineWeyl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentreRefl
import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp
import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2tnBig_zpowers_subtype_iff {G : Type} [Group G] {Bs : Subgroup G} {x : G}
    (hx : x ∈ Bs) (b : ↥Bs) :
    (b : G) ∈ Subgroup.zpowers x ↔ b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem ggQ2tnBig_zpow_mem_span {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {x : G} (hx : x ∈ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {b : ↥Bs} (hb : b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    ι (Additive.ofMul b) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} : Set V) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hk, ofMul_zpow, map_zsmul]
  exact Submodule.mem_span_singleton.mpr
    ⟨(k : ZMod p), Int.cast_smul_eq_zsmul (R := ZMod p) k _⟩

private theorem ggQ2tnBig_model_span_iff {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {x : G} (M : GGQ2LDatum 3 Bs L x) {y : G} (hy : y ∈ Bs) (b : ↥Bs) :
    M.model (Additive.ofMul b) ∈
        Submodule.span (ZMod 3) {M.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} ↔
      b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have h1 : c.val • M.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) =
        M.model (Additive.ofMul b) := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 3) c.val, ZMod.natCast_zmod_val]
      exact hc
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Additive.ofMul.injective
    apply M.model.injective
    rw [ofMul_pow]
    exact ((M.model.toAddMonoidHom).map_nsmul c.val _).trans h1
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hk]
    have h1 : M.model (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ k)) =
        k • M.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
      rw [ofMul_zpow]
      exact (M.model.toAddMonoidHom).map_zsmul k (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
    rw [h1, ← Int.cast_smul_eq_zsmul (R := ZMod 3) k]
    exact Submodule.smul_mem _ (k : ZMod 3) (Submodule.mem_span_singleton_self _)

private theorem ggQ2tnBig_sub_mem_coSpan {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {w : MulAut ↥Bs} (hw : w ∈ ggAutomizer L Bs) (v : M.V) :
    ggLin (p := 3) M.model w v - v ∈ M.coSpan := by
  rw [M.automizer_L] at hw
  revert v
  refine Subgroup.closure_induction (p := fun w _ =>
    ∀ v : M.V, ggLin (p := 3) M.model w v - v ∈ M.coSpan) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨i, rfl⟩ v
    rw [M.simple_apply i]
    have h : v - M.root i v • M.coroot i - v = -(M.root i v • M.coroot i) := by abel
    rw [h]
    exact M.coSpan.neg_mem (M.coSpan.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  · intro v
    simp
  · intro a b _ _ ha hb v
    rw [map_mul, LinearEquiv.mul_apply]
    have h : ggLin (p := 3) M.model a (ggLin (p := 3) M.model b v) - v =
        (ggLin (p := 3) M.model a (ggLin (p := 3) M.model b v) -
          ggLin (p := 3) M.model b v) + (ggLin (p := 3) M.model b v - v) := by abel
    rw [h]
    exact M.coSpan.add_mem (ha _) (hb v)
  · intro a _ ha v
    rw [map_inv]
    have h : v - (ggLin (p := 3) M.model a)⁻¹ v ∈ M.coSpan := by
      have h0 := ha (ggLin (p := 3) M.model a⁻¹ v)
      simpa [map_inv] using h0
    simpa [neg_sub] using M.coSpan.neg_mem h

theorem ggQ2_heartA_stab {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) {r : ℕ} (hr : 4 ≤ r) (e : Fin r ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j) (hB : M.ShapeB)
    (hnorm : ∀ φ ∈ ggAutomizer ⊤ Bs, φ ⟨u, M.hx⟩ ∈ Subgroup.zpowers (⟨u, M.hx⟩ : ↥Bs) →
      φ ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs))) :
    ∀ g ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model), g M.xV = M.xV →
      ∃ w ∈ Subgroup.closure (Set.range fun i : Fin r => ggLin (p := 3) M.model (M.simple (e i))),
        ∃ ε : ZMod 3, ∀ h ∈ Submodule.span (ZMod 3) (Set.range fun i : Fin r => M.coroot (e i)),
          g h = ε • w h := by
  set s : Fin r → (M.V ≃ₗ[ZMod 3] M.V) := fun i => ggLin (p := 3) M.model (M.simple (e i))
  set c : Fin r → M.V := fun i => M.coroot (e i)
  have hcoSpan : M.coSpan = Submodule.span (ZMod 3) (Set.range c) := by
    rw [GGQ2LDatum.coSpan]
    congr 1
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by
        change M.coroot (e (e.symm j)) = M.coroot j
        rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
  have hinf : M.coSpan ⊓ Submodule.span (ZMod 3) {M.xV} = ⊥ :=
    disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem hB.2.2.1)
  have hrange : Set.range s = ggLin (p := 3) M.model '' Set.range M.simple := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple (e i), ⟨e i, rfl⟩, rfl⟩
    · rintro ⟨ψ, ⟨k, rfl⟩, rfl⟩
      refine ⟨e.symm k, ?_⟩
      change ggLin (p := 3) M.model (M.simple (e (e.symm k))) =
        ggLin (p := 3) M.model (M.simple k)
      rw [Equiv.apply_symm_apply]
  have hW : Subgroup.closure (Set.range s) =
      (ggAutomizer X Bs).map (ggLin (p := 3) M.model) := by
    rw [hrange, M.automizer_L, MonoidHom.map_closure]
  intro g hgA hgx
  obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hgA
  have hψx : ψ ⟨u, M.hx⟩ = ⟨u, M.hx⟩ := by
    apply Additive.ofMul.injective
    apply M.model.injective
    rw [← ggLin_apply_ofMul (p := 3) M.model ψ ⟨u, M.hx⟩]
    simpa only [GGQ2LDatum.xV] using hgx
  have hψxzp : ψ ⟨u, M.hx⟩ ∈ Subgroup.zpowers (⟨u, M.hx⟩ : ↥Bs) := by
    rw [hψx]
    exact Subgroup.mem_zpowers _
  have hψN : ψ ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs)) :=
    hnorm ψ hψA hψxzp
  obtain ⟨w₀, hw₀, ε, hε, hwε⟩ := ggQ2_pm_heartA M e hC (by omega) hB ψ hψN
  let w₁ : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model w₀
  have hw₁ : w₁ ∈ Subgroup.closure (Set.range s) := by
    rw [hW]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) hw₀
  have hw₁inv : w₁⁻¹ = ggLin (p := 3) M.model w₀⁻¹ := by
    rw [show w₁ = ggLin (p := 3) M.model w₀ from rfl]
    exact (map_inv (ggLin (p := 3) M.model) w₀).symm
  refine ⟨w₁⁻¹, Subgroup.inv_mem _ hw₁, ε, ?_⟩
  intro h hh
  have hhM : h ∈ M.coSpan := by
    rw [hcoSpan]
    exact hh
  have hg : ggLin (p := 3) M.model ψ h ∈ M.coSpan :=
    ggQ2_coSpan_of_mem_normalizer M hψN h hhM
  have hwsub : w₁⁻¹ h ∈ M.coSpan := by
    have h1 : ggLin (p := 3) M.model w₀⁻¹ h - h ∈ M.coSpan :=
      ggQ2tnBig_sub_mem_coSpan M (Subgroup.inv_mem _ hw₀) h
    rw [hw₁inv]
    have h2 : ggLin (p := 3) M.model w₀⁻¹ h =
        h + (ggLin (p := 3) M.model w₀⁻¹ h - h) := by abel
    rw [h2]
    exact M.coSpan.add_mem hhM h1
  have hcomp : ggLin (p := 3) M.model (ψ * w₀) (w₁⁻¹ h) =
      ggLin (p := 3) M.model ψ h := by
    rw [map_mul, LinearEquiv.mul_apply, hw₁inv,
      show ggLin (p := 3) M.model w₀⁻¹ = (ggLin (p := 3) M.model w₀)⁻¹ from
        map_inv (ggLin (p := 3) M.model) w₀]
    change (ggLin (p := 3) M.model) ψ
      ((ggLin (p := 3) M.model) w₀ ((ggLin (p := 3) M.model w₀).symm h)) =
        (ggLin (p := 3) M.model) ψ h
    rw [LinearEquiv.apply_symm_apply]
  have hdiff : ggLin (p := 3) M.model ψ h - ε • w₁⁻¹ h ∈
      Submodule.span (ZMod 3) {M.xV} := by
    have h := hwε (w₁⁻¹ h)
    rwa [hcomp] at h
  have hco : ggLin (p := 3) M.model ψ h - ε • w₁⁻¹ h ∈ M.coSpan :=
    M.coSpan.sub_mem hg (M.coSpan.smul_mem ε hwsub)
  have hmem : ggLin (p := 3) M.model ψ h - ε • w₁⁻¹ h ∈
      M.coSpan ⊓ Submodule.span (ZMod 3) {M.xV} :=
    Submodule.mem_inf.mpr ⟨hco, hdiff⟩
  have hzero : ggLin (p := 3) M.model ψ h - ε • w₁⁻¹ h = 0 := by
    rw [hinf] at hmem
    simpa using hmem
  exact sub_eq_zero.mp hzero

theorem ggQ2_tnBig_core (hK : GGReflClassOmegaLarge) {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {u : G} (hNT : GGNoTransvection 3 Bs) (M : GGQ2LDatum 3 Bs X u) {r : ℕ}
    (hr : 11 ≤ r) (h3 : 3 ∣ r + 1) (e : Fin r ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j) (hB : M.ShapeB)
    (hnorm : ∀ φ ∈ ggAutomizer ⊤ Bs, φ ⟨u, M.hx⟩ ∈ Subgroup.zpowers (⟨u, M.hx⟩ : ↥Bs) →
      φ ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs)))
    (hmove : ∃ φ ∈ ggAutomizer ⊤ Bs, GGIsReflection 3 φ ∧ GGQ2MovesLine Bs u φ) : False := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  let A : Subgroup (M.V ≃ₗ[ZMod 3] M.V) := (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
  let c : Fin r → M.V := fun i => M.coroot (e i)
  let α : Fin r → Module.Dual (ZMod 3) M.V := fun i => M.root (e i)
  let s : Fin r → (M.V ≃ₗ[ZMod 3] M.V) := fun i => ggLin (p := 3) M.model (M.simple (e i))
  have hHdim : Module.finrank (ZMod 3) M.coSpan + 1 = Fintype.card M.Λ := hB.2.1
  have hxHcoSpan : M.xV ∉ M.coSpan := hB.2.2.1
  have hsup : M.coSpan ⊔ Submodule.span (ZMod 3) {M.xV} = ⊤ := hB.2.2.2
  have hcoSpan : M.coSpan = Submodule.span (ZMod 3) (Set.range c) := by
    rw [GGQ2LDatum.coSpan]
    congr 1
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by
        change M.coroot (e (e.symm j)) = M.coroot j
        rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
  have hxH : M.xV ∉ Submodule.span (ZMod 3) (Set.range c) := by
    rw [← hcoSpan]
    exact hxHcoSpan
  have hxV0 : M.xV ≠ 0 := by
    intro h
    exact hxHcoSpan (by rw [h]; exact M.coSpan.zero_mem)
  have hinf : M.coSpan ⊓ Submodule.span (ZMod 3) {M.xV} = ⊥ :=
    disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem hxHcoSpan)
  have hcardΛ : Fintype.card M.Λ = r := by
    simpa using Fintype.card_congr e.symm
  have hdim : Module.finrank (ZMod 3) M.V = r := by
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 3) M.coSpan
      (Submodule.span (ZMod 3) {M.xV})
    rw [hsup, hinf, finrank_top, finrank_bot, finrank_span_singleton hxV0] at hfr
    omega
  have hpair : ∀ i j : Fin r, α i (c j) = (CartanMatrix.A r i j : ZMod 3) := by
    intro i j
    rw [M.pairing (e i) (e j), hC i j]
  have hs : ∀ i : Fin r, ∀ v, s i v = v - α i v • c i := fun i => M.simple_apply (e i)
  have hsA : ∀ i : Fin r, s i ∈ A := fun i =>
    Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (GGQ2LDatum.simple_mem_top M (e i))
  have hxfix : ∀ i : Fin r, α i M.xV = 0 := fun i => GGQ2LDatum.root_xV M (e i)
  have hTF : TransvectionFree A := ggQ2P3P_transvectionFree M.model hNT
  have hRx : ¬ ∀ r' ∈ reflGp A, r' M.xV ∈ Submodule.span (ZMod 3) {M.xV} := by
    intro hforall
    obtain ⟨φ, hφA, hφrefl, hφmove⟩ := hmove
    have hφlin : ggLin (p := 3) M.model φ ∈ reflGp A := by
      rw [show reflGp A = (ggReflGp 3 Bs).map (ggLin (p := 3) M.model) from
        ggQ2P3P_reflGp_map M.model (by decide)]
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨hφA, hφrefl⟩)
    have hxVspan : ggLin (p := 3) M.model φ M.xV ∈
        Submodule.span (ZMod 3) {M.xV} := hforall _ hφlin
    obtain ⟨b, hbzp, hbmove⟩ := hφmove
    have hbsub : b ∈ Subgroup.zpowers (⟨u, M.hx⟩ : ↥Bs) :=
      (ggQ2tnBig_zpowers_subtype_iff M.hx b).mp hbzp
    have hbvec : M.model (Additive.ofMul b) ∈ Submodule.span (ZMod 3) {M.xV} := by
      simpa only [GGQ2LDatum.xV] using ggQ2tnBig_zpow_mem_span M.hx M.model hbsub
    have hφbvec : M.model (Additive.ofMul (φ b)) ∈
        Submodule.span (ZMod 3) {M.xV} := by
      rw [← ggLin_apply_ofMul (p := 3) M.model φ b]
      obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hbvec
      rw [← hcc, map_smul]
      exact Submodule.smul_mem _ cc hxVspan
    have hφbsub : φ b ∈ Subgroup.zpowers (⟨u, M.hx⟩ : ↥Bs) := by
      refine (ggQ2tnBig_model_span_iff M M.hx (φ b)).mp ?_
      simpa only [GGQ2LDatum.xV] using hφbvec
    exact hbmove ((ggQ2tnBig_zpowers_subtype_iff M.hx (φ b)).mpr hφbsub)
  have hStab : ∀ g ∈ A, g M.xV = M.xV → ∃ w ∈ Subgroup.closure (Set.range s),
      ∃ ε : ZMod 3, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), g h = ε • w h :=
    ggQ2_heartA_stab M (by omega) e hC hB hnorm
  exact ggQ2TN_big_false (V := M.V) hK A hTF hr h3 hdim c α hpair s hs hsA M.xV hxH
    hxfix hRx hStab


private theorem ggQ2tnBig_automizer_ne_bot {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {u : G} (M : GGQ2LDatum 3 Bs X u) {r : ℕ} (e : Fin r ≃ M.Λ) (hr : 0 < r) :
    ggAutomizer X Bs ≠ ⊥ := by
  intro hbot
  let i : M.Λ := e ⟨0, hr⟩
  have hfx : M.root i (M.coroot i) = 2 := GGQ2LDatum.root_coroot_two M i
  have hrefl : GGIsReflection 3 (M.simple i) :=
    ggIsReflection_of_eq_reflection (p := 3) (by decide) M.model hfx
      (ggLin_eq_reflection (p := 3) M.model hfx (M.simple_apply i))
  have hmem : M.simple i ∈ ggAutomizer X Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hrefl.ne_one Nat.prime_three hmem

theorem ggQ2_tnBig_false (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput) (hdLab : GGCoxeterLabelInput)
    (hWA : GGTBFixNbrXInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hRG : GGReflGenerated p (ggAutomizer K Bs)) (hsel : GGQ2TNBigSel p Bs L x) : False := by
  subst hp
  obtain ⟨M, r, hr, h3, e, hC, hB⟩ := hsel
  have hcfg := hS.1.1
  obtain ⟨-, hBs, hx, hLx, -⟩ := hcfg.tableB_facts
  have hSW : GGScalarsOrWeyl' 3 B Bs x D J := Or.inl (ggScalarsPmOne_of_prime_three hcfg rfl)
  have hW := hdLab G 3 B Bs x L D J hcfg hS.1.2.1 hS.1.2.2.1 hS.1.2.2.2.1 y K hnb hRG hSW
  have hWG : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hWu : ¬ ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ ⟨x, hx⟩ = ⟨x, hx⟩ := fun h =>
    hcfg.1.2.2.2.2.2.2.1.2.2.1 (hWA G 3 B Bs x L D J hcfg hS.1.2.1 hS.1.2.2.1 hS.1.2.2.2.1 y K
      hnb hRG hSW ⟨x, hx⟩ (Subgroup.mem_zpowers x) fun φ hφ => h φ (Subgroup.mem_sup_right hφ))
  obtain ⟨φ, hφW, hφrefl, hφmove⟩ :=
    ggQ2_refl_movesLine_of_weylGroup hBs hS.1.2.2.2.1 hx hWG hW le_sup_left
      (ggQ2tnBig_automizer_ne_bot M e (by omega))
      (fun φ hφ => ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hx⟩) hLx hφ) hWu
  exact ggQ2_tnBig_core hK.1 hS.1.2.2.2.1 M hr h3 e hC hB
    (fun ψ hψA hψx => ggQ2_lineStab_normalizes_L hLB hP hS.1 (ggQ2_ajOfSetting hP h5 hS) M.hx
      hψA hψx)
    ⟨φ, hWG hφW, hφrefl, hφmove⟩

private theorem ggQ2tnBig_nbr_not_mem_zpowers {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hnbr : GGNbr p B x D J y K) : y ∉ Subgroup.zpowers x := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hDab : IsElemAbelian p D := hcfg.2.2.1.2.1
  intro hy
  have hD_le : D ≤ Subgroup.zpowers x := by
    rw [hnbr.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_zpowers _
    · exact hy
  have hD_eq : D = Subgroup.zpowers x := le_antisymm hD_le (Subgroup.zpowers_le.mpr hxD)
  have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hDab.2 x hxD)
  have horder : orderOf x = p ^ 2 := by
    rw [← Nat.card_zpowers, ← hD_eq, hDcard]
  have hp2le : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos (horder ▸ hdvd)
  nlinarith [hp.two_le]

theorem ggQ2_tnBigK_false (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput) (hdLab : GGCoxeterLabelInput)
    (hTBF : GGTBFixInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hRG : GGReflGenerated p (ggAutomizer K Bs))
    (hsel : GGQ2TNBigSel p Bs K y) : False := by
  subst hp
  obtain ⟨MK, r, hr, h3, e, hC, hB⟩ := hsel
  have hcfg := hS.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hy : y ∈ Bs := MK.hx
  have hSW : GGScalarsOrWeyl' 3 B Bs x D J := Or.inl (ggScalarsPmOne_of_prime_three hcfg rfl)
  have hW := hdLab G 3 B Bs x L D J hcfg hS.1.2.1 hS.1.2.2.1 hS.1.2.2.2.1 y K hnb hRG hSW
  have hWG : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hWu : ¬ ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ ⟨y, hy⟩ = ⟨y, hy⟩ := fun h =>
    ggQ2tnBig_nbr_not_mem_zpowers hcfg hnb (hTBF G 3 B Bs x L D J hcfg hS.1.2.1 hS.1.2.2.1
      hS.1.2.2.2.1 y K hnb hRG hSW ⟨y, hy⟩ fun φ hφ => h φ (Subgroup.mem_sup_left hφ))
  obtain ⟨φ, hφW, hφrefl, hφmove⟩ :=
    ggQ2_refl_movesLine_of_weylGroup hBs hS.1.2.2.2.1 hy hWG hW le_sup_right
      (ggQ2tnBig_automizer_ne_bot MK e (by omega))
      (fun φ hφ => ggAutomizer_apply_eq_of_le_centralizer (x := ⟨y, hy⟩)
        (fun _ hk => hnb.1.2.2.2.1 hk) hφ) hWu
  exact ggQ2_tnBig_core hK.1 hS.1.2.2.2.1 MK hr h3 e hC hB
    (fun ψ hψA hψy => ggQ2_nbrLineStab_normalizes hLB hP hS.1 (ggQ2_ajOfSetting hP h5 hS)
      (ggQ2_K1_of_I1 hLB hP hS.1 hI1) hnb MK.hx hψA hψy)
    ⟨φ, hWG hφW, hφrefl, hφmove⟩

@[expose] def GGQ2TwAHeartDatumInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {X : Subgroup G} {u : G}, (X = L ∧ u = x) ∨ GGNbr p B x D J u X →
      ∀ {N : ℕ}, 7 ≤ N → GGQ2S08RowTwA p N X J → u ∉ X →
        ∃ M : GGQ2LDatum p Bs X u, ∃ e : Fin (N - 1) ≃ M.Λ,
          (∀ i j, M.cartan (e i) (e j) = CartanMatrix.A (N - 1) i j) ∧ (M.ShapeB ∨ M.ShapeC)

theorem ggQ2s08_noNbrBig_of_heartDatum
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput) (hdLab : GGCoxeterLabelInput)
    (hWA : GGTBFixNbrXInput) (hTBF : GGTBFixInput)
    (hRGq : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G} {y : G} {K : Subgroup G}, GGQTwoSetting p B Bs x L D J →
        GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs))
    (hH : GGQ2TwAHeartDatumInput) : GGQ2S08NoNbrCell GGQ2S08PosTwABig := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow
  have hcfg := hS.1.1
  have hIDA := hS.1.2.2.1
  rcases hrow with ⟨⟨N, hN, hr⟩, hx⟩ | ⟨⟨N, hN, hr⟩, hy⟩
  · obtain ⟨M, e, hC, hBC⟩ := hH hp hS hI1 (Or.inl ⟨rfl, rfl⟩) (by omega) hr hx
    exact ggQ2_tnBig_false hLB hP h5 hK hdLab hWA hp hS hnb (hRGq hS hnb)
      (ggQ2_tnBigSel_of_shapeBC hRig hLB hp hcfg hIDA hI1 (Or.inl rfl) hN hr M e hC hBC)
  · obtain ⟨M, e, hC, hBC⟩ := hH hp hS hI1 (Or.inr hnb) (by omega) hr hy
    exact ggQ2_tnBigK_false hLB hP h5 hK hdLab hTBF hp hS hI1 hnb (hRGq hS hnb)
      (ggQ2_tnBigSel_of_shapeBC hRig hLB hp hcfg hIDA hI1 (Or.inr ⟨y, hnb⟩) hN hr M e hC hBC)

end CFSG.StandardType

end
