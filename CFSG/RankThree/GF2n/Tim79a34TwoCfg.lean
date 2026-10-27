module

public import CFSG.RankThree.GF2n.Tim79a34QEIn
public import CFSG.RankThree.GF2n.Tim79a34Lemma13
public import CFSG.RankThree.GF2n.Tim79a34GammaComm
public import CFSG.RankThree.GF2n.Tim79a34TwoKernel
public import CFSG.RankThree.GF2n.Tim79a34TwoModel
public import CFSG.RankThree.GF2n.Tim79a34TwoSpace
public import CFSG.RankThree.GF2n.Tim79a34TwoGame
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.Row
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.LargeExtraspecial.S12Basic
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.RankThree.GF2n.Tim78a.GriessSpMultiplier
public import CFSG.RankThree.GF2n.Tim79a34C8Group
public import CFSG.RankThree.GF2n.Tim79a34CaseV
public import CFSG.RankThree.GF2n.Tim79a34CentreSmall
public import CFSG.RankThree.GF2n.Tim79a34QPConfig
public import CFSG.RankThree.GF2n.Tim79a34StrothSimple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic CFSG.RankThree.GF2n.Tim79a
  CFSG.RankThree.GF2n.Tim79a.Gamma
open Matrix
open scoped commutatorElement

structure Lem : Prop where
  h11a : Lemma11aStatement
  h11b : Lemma11bStatement
  h11c : Lemma11cStatement
  h12 : Lemma12Statement
  h13 : Lemma13Statement

theorem lem_holds : Lem := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h11c : Lemma11cStatement := lemma11c_holds spRadFactsStatement_holds h11a
  exact ⟨h11a, h11b, h11c, lemma12Statement_holds, lemma13_holds hN h11b h11c⟩

theorem exists_cfg {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hiso : Nonempty (↥(StatedSp 2 (GaloisField 2 1)) ≃* XbarZ V H)) :
    ∃ (Φ : ↥(StatedSp 2 (GaloisField 2 1)) ≃* Xbar V H)
      (ψ : (Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
      (a : Fin 2 ⊕ Fin 2 → GaloisField 2 1)
      (T : Subgroup ↥(StatedSp 2 (GaloisField 2 1))), Nonempty (GCfg M V Q P H Φ ψ a T) := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have hIW : Sec34IWStatement :=
    sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hZ
  obtain ⟨n, Φ, ψ, hn2, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ
  obtain ⟨e⟩ := hiso
  have hnn : n = 2 := by
    let e2 : Xbar V H ≃* XbarZ V H := MulEquiv.ofBijective (projZ V H) (iw_projZ_bijective hZ)
    exact statedSp_gf2_rank_eq (Φ.trans (e2.trans e.symm))
  subst hnn
  refine ⟨Φ, ψ, a, T, ⟨?_⟩⟩
  exact
    { hyp := hH
      centre := hZ
      iw := hcP
      nat := ⟨hequiv, hpoint⟩
      ne := ha
      trans := hT
      point := hTV
      two_le := hn2 }

section Cfg

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
  {Φ : ↥(StatedSp 2 (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin 2 ⊕ Fin 2 → GaloisField 2 1} {T : Subgroup ↥(StatedSp 2 (GaloisField 2 1))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem tiData_of_cfg (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T)
    {β : Fin 2 ⊕ Fin 2 → GaloisField 2 1} (hβ : spForm a β = 1) {v₀ : G} (hv₀ : v₀ ∈ V)
    (hv₀W : v₀ ∉ wOf V H) :
    TwoGame.TIData V Q P M (ψG a) v₀ (ψG β) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hZ := cfg.centre
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have haV : ψG a ∈ V := (Subgroup.mem_inf.mp haK).1
  have haW : ψG a ∈ wOf V H := (Subgroup.mem_inf.mp haK).2
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    elemAbelian_mul_comm hc.elemAb hx hy
  have hVsq : ∀ x ∈ V, x * x = 1 := fun x hx => elemAbelian_mul_self hc.elemAb hx
  have hv1 : v₀ ≠ 1 := fun h => hv₀W (by rw [h]; exact (wOf V H).one_mem)
  have hvz : ψG a ≠ v₀ := fun h => hv₀W (by rw [← h]; exact haW)
  have hvz1 : v₀ * ψG a ≠ 1 := by
    intro h
    apply hvz
    calc ψG a = v₀ * (v₀ * ψG a) := by rw [← mul_assoc, hVsq v₀ hv₀, one_mul]
      _ = v₀ := by rw [h, mul_one]
  have hV4 := sh_V_four (card_V cfg) haV hv₀ haG1 hv1 hvz hvz1
  have hMQ : Q = inSubgroup (pCore 2) M := hc.hQ
  have hQM : Q ≤ M := by rw [hMQ]; exact (inSubgroup_pCore_two M).2.1
  have hcentM : Subgroup.centralizer ({ψG a} : Set G) = M :=
    (L.h12 G M V Q P H cfg.hyp hZ Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hcommβ : ⁅v₀, ψG β⁆ = ψG a :=
    (L.h11c G M V Q P H cfg.hyp hZ cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point β hβ).1
      v₀ hv₀ hv₀W
  have hβM : ψG β ∈ M := wOf_le_M cfg (Additive.toMul (ψ β)).2
  refine
    { a_mem := haV
      v_mem := hv₀
      V_enum := fun x hx => by
        rcases hV4 x hx with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (by rw [h]; exact hVcomm _ hv₀ _ haV)))
      a_ne := haG1
      a_sq := hVsq _ haV
      v_sq := hVsq _ hv₀
      av_comm := hVcomm _ haV _ hv₀
      ti := hc.ti
      M_norm := fun g => by rw [← hc.normalizer_eq]
      M_cent := fun g => by rw [← hcentM, Subgroup.mem_centralizer_singleton_iff]
      cent_v := fun g hg => by
        have h13 := (L.h13 G M V Q P H cfg.hyp hZ cfg.iw v₀ hv₀ hv₀W).1
        have : g ∈ Subgroup.centralizer ({v₀} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hg
        rw [h13] at this
        exact (Subgroup.mem_inf.mp this).1
      b_mem := hβM
      b_swap := by
        have hv₀i : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right (hVsq v₀ hv₀)
        have h2 : v₀ * ψG β * v₀ * (ψG β)⁻¹ = ψG a := by
          have := hcommβ
          rw [commutatorElement_def, hv₀i] at this
          exact this
        calc ψG β * v₀ * (ψG β)⁻¹ = (v₀ * v₀) * (ψG β * v₀ * (ψG β)⁻¹) := by
              rw [hVsq v₀ hv₀, one_mul]
          _ = v₀ * (v₀ * ψG β * v₀ * (ψG β)⁻¹) := by simp only [mul_assoc]
          _ = v₀ * ψG a := by rw [h2]
          _ = ψG a * v₀ := hVcomm _ hv₀ _ haV
      Q_le := hQM
      Q_norm := fun m hm q hq => by
        rw [hMQ] at hq ⊢
        exact (Subgroup.mem_normalizer_iff.mp ((inSubgroup_pCore_two M).2.2 hm) q).mp hq
      P_le := hc.P_le_Q
      P_cent := fun p hp z hz => by
        have := (Subgroup.mem_inf.mp (hc.hP ▸ hp : p ∈ Q ⊓ Subgroup.centralizer (V : Set G))).2
        exact (Subgroup.mem_centralizer_iff.mp this z hz).symm
      P_norm := fun m hm p hp => (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hm) p).mp hp
      QP := fun q hq p hp => ((tim79a34_mem_Q_iff cfg.hyp hZ q).mp hq).2 p hp
      QV := fun q hq h => by
        rw [hc.hP]
        exact Subgroup.mem_inf.mpr
          ⟨hq, Subgroup.mem_centralizer_iff.mpr fun v hv => (h v hv).symm⟩ }

omit [Finite G] in
theorem exists_perp_pair {n : ℕ} {a y : Fin n ⊕ Fin n → GaloisField 2 1} (ha : a ≠ 0)
    (hy : y ≠ 0) (hya : y ≠ a) : ∃ w, spForm a w = 0 ∧ spForm y w = 1 := by
  obtain ⟨v₂, hv₂⟩ := exists_spForm_ne_zero hy
  have hay : a + y ≠ 0 := fun h => hya (by
    have h1 : a + a = 0 := gf2_vec_add_self a
    calc y = (a + a) + y := by rw [h1, zero_add]
      _ = a + (a + y) := by rw [add_assoc]
      _ = a := by rw [h, add_zero])
  obtain ⟨v₃, hv₃⟩ := exists_spForm_ne_zero hay
  have h2 : spForm y v₂ = 1 := (twl_gf2 _).resolve_left hv₂
  have h3 : spForm a v₃ + spForm y v₃ = 1 := by
    rw [← spForm_add_left]
    exact (twl_gf2 _).resolve_left hv₃
  rcases twl_gf2 (spForm a v₂) with h4 | h4
  · exact ⟨v₂, h4, h2⟩
  · rcases twl_gf2 (spForm a v₃) with h5 | h5
    · refine ⟨v₃, h5, ?_⟩
      rw [h5, zero_add] at h3
      exact h3
    · refine ⟨v₂ + v₃, ?_, ?_⟩
      · rw [spForm_add_right, h4, h5]
        exact gf2_add_self 1
      · rw [spForm_add_right, h2]
        rw [h5] at h3
        have h6 : spForm y v₃ = 0 := by
          have : (1 : GaloisField 2 1) + spForm y v₃ = 1 + 0 := by rw [h3, add_zero]
          exact add_left_cancel this
        rw [h6, add_zero]

theorem exists_root_conj (cfg : GCfg M V Q P H Φ ψ a T) {y : Fin 2 ⊕ Fin 2 → GaloisField 2 1}
    (hy0 : y ≠ 0) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀W : v₀ ∉ wOf V H) :
    ∃ x : G, x ∈ xOf V H ∧ x * ψG a * x⁻¹ = ψG y ∧
      ∀ w, (x * v₀ * x⁻¹) * ψG w * (x * v₀ * x⁻¹)⁻¹ = ψG (w + spForm y w • y) := by
  have hy1 : ψG y ≠ 1 := fun h => hy0 (psi_injective (h.trans psi_zero.symm))
  obtain ⟨x, hx⟩ := exists_conj_aG_eq cfg (psi_mem_W y) hy1
  exact ⟨x, x.2, hx, conj_act_eq_trans cfg x hv₀ hv₀W hx.symm⟩

theorem trans_not_mem_P (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T)
    {y : Fin 2 ⊕ Fin 2 → GaloisField 2 1} (hy0 : y ≠ 0) (hya : y ≠ a) {g : G} (hg : g ∈ P) :
    ¬ ∀ w, g * ψG w * g⁻¹ = ψG (w + spForm y w • y) := by
  intro h
  obtain ⟨u, hu, c, hgu⟩ := exists_param_of_mem_P L.h11a cfg.hyp cfg.centre cfg.iw cfg.nat
    cfg.ne cfg.trans cfg.point hg
  obtain ⟨w₀, hw₀a, hw₀y⟩ := exists_perp_pair cfg.ne hy0 hya
  have h1 := h w₀
  rw [hgu w₀, hw₀a, hw₀y, zero_smul, add_zero, mul_zero, zero_smul, add_zero, one_smul] at h1
  have h2 := psi_injective h1
  have h3 : y = spForm u w₀ • a := by
    have h4 : w₀ + spForm u w₀ • a = w₀ + y := h2
    exact (add_left_cancel h4).symm
  rcases twl_gf2 (spForm u w₀) with h5 | h5
  · rw [h5, zero_smul] at h3
    exact hy0 h3
  · rw [h5, one_smul] at h3
    exact hya h3

end Cfg

section Coord

open CFSG.RankThree.GF2n.Tim79a.TwoModel CFSG.RankThree.GF2n.Tim79a.TwoSpace

variable {G : Type} [Group G]

structure Coord (P V M F : Subgroup G) (t0 t1 : G) : Type where
  θ : P → Vec4
  coords : PCoords P V θ
  F_to : ∀ p : P, (p : G) ∈ F → inFt (θ p)
  F_of : ∀ x, inFt x → ∃ p : P, (p : G) ∈ F ∧ θ p = x
  θ_t0 : ∀ h : t0 ∈ P, θ ⟨t0, h⟩ = e0
  θ_t1 : ∀ h : t1 ∈ P, θ ⟨t1, h⟩ = e1
  act : M →* Equiv.Perm Vec4
  act_isom : ∀ m : M, IsIsom4 (act m)
  act_spec : ∀ (m : M) (p : P) (hp : (m : G) * p * (m : G)⁻¹ ∈ P),
    θ ⟨(m : G) * p * (m : G)⁻¹, hp⟩ = act m (θ p)

namespace Coord

variable {P V M F : Subgroup G} {t0 t1 : G} (K : Coord P V M F t0 t1)

theorem θ_one : K.θ 1 = 0 := by
  have h := K.coords.add 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem θ_inv (p : P) : K.θ p⁻¹ = K.θ p := by
  have h := K.coords.add p p⁻¹
  rw [mul_inv_cancel, K.θ_one] at h
  funext i
  have h1 := congrFun h i
  have key : ∀ a b : ZMod 2, 0 = a + b → b = a := by decide
  exact key _ _ h1

theorem θ_comm (m : M) (p : P) (hp : (m : G) * p * (m : G)⁻¹ ∈ P)
    (hc : ⁅(m : G), (p : G)⁆ ∈ P) :
    K.θ ⟨⁅(m : G), (p : G)⁆, hc⟩ = K.act m (K.θ p) + K.θ p := by
  have e : (⟨⁅(m : G), (p : G)⁆, hc⟩ : P) = ⟨(m : G) * p * (m : G)⁻¹, hp⟩ * p⁻¹ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, K.coords.add, K.act_spec m p hp, K.θ_inv]

end Coord

end Coord

section RootPair

open CFSG.RankThree.GF2n.Tim79a.TwoModel CFSG.RankThree.GF2n.Tim79a.TwoSpace

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
  {Φ : ↥(StatedSp 2 (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin 2 ⊕ Fin 2 → GaloisField 2 1} {T : Subgroup ↥(StatedSp 2 (GaloisField 2 1))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem P_norm_of_cfg (cfg : GCfg M V Q P H Φ ψ a T) :
    ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P := fun m hm p hp =>
  (Subgroup.mem_normalizer_iff.mp (cfg.hyp.setup.mc.toMinCex.M_le_normalizer_P hm) p).mp hp

theorem V_norm_of_cfg (cfg : GCfg M V Q P H Φ ψ a T) :
    ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V := fun m hm z hz => by
  have hN : m ∈ Subgroup.normalizer (V : Set G) := by
    rw [cfg.hyp.setup.mc.toMinCex.normalizer_eq]
    exact hm
  exact (Subgroup.mem_normalizer_iff.mp hN z).mp hz

theorem Q_le_normalizer_W (cfg : GCfg M V Q P H Φ ψ a T) :
    Q ≤ Subgroup.normalizer (wOf V H : Set G) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨C, hCQ, hPCQ, -, hCW, -, -⟩ := Gamma.sec34GammaStatement_holds G M V Q P H cfg.hyp
    cfg.centre
  rw [← hPCQ]
  refine sup_le ?_ ?_
  · intro p hp
    exact H_le_normalizer_wOf V H (hc.PleH hp)
  · intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h1 := hCW c hc' w hw
      rw [h1, mul_inv_cancel_right]
      exact hw
    · intro hw
      have h1 := hCW c⁻¹ (C.inv_mem hc') _ hw
      have h2 : c⁻¹ * (c * w * c⁻¹) * c = w := by group
      rw [← h2, h1]
      simpa using hw

end RootPair

end CFSG.RankThree.GF2n.Tim79a.TwoRoot
