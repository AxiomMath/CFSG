module

public import CFSG.Milestones.ASVolI.F45.G2dHex
public import CFSG.Milestones.ASVolI.F45.BN
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.LieType.HighestRoot.CentIsogeny
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin

section BN

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

variable {X : Type} [Group X] [Finite X] {p : ℕ} (D : RankTwoSystem X 6)

theorem burnsideF45_g2d_bn_adj (i : Bool) : (Γ D).Adj (v D i) (v D (!i)) := by
  cases i
  · exact (adj_v D).symm
  · exact adj_v D

theorem burnsideF45_g2d_bn_edge (i : Bool) :
    MulAction.stabilizer X (v D i) ⊓ MulAction.stabilizer X (v D (!i)) = D.B := by
  rw [stabilizer_v_eq, stabilizer_v_eq]
  cases i
  · rw [inf_comm]
    exact P₁_inf_P₂ D
  · exact P₁_inf_P₂ D

theorem burnsideF45_g2d_bn_faithful (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤)
    (hB : IsPGroup p ↥D.B) (i : Bool) : burnsideF45_FaithfulAt (Γ D) X (v D i) := by
  intro w hw t htv htw hta
  have MB := burnsideF45_bn_modelBase D hp hU i
  have hedge : IsPGroup p ↥(MulAction.stabilizer X (v D i) ⊓ MulAction.stabilizer X (v D (!i))) := by
    rw [burnsideF45_g2d_bn_edge D i]
    exact hB
  have hker := burnsideF45_g2dKer_le_pCoreOf (burnsideF45_g2d_bn_adj D i) hedge
  exact MB.Qfree w hw t (hker ⟨htv, hta⟩) htw

theorem burnsideF45_g2d_bn_two (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    burnsideF45_TwoAt (Γ D) X (v D i) := by
  intro w hw a c a' c' ha hc hac ha' hc' hac'
  have MB := burnsideF45_bn_modelBase D hp hU i
  obtain ⟨g, hgv, hga, hgc⟩ := MB.two a c a' c' ha hc hac ha' hc' hac'
  have hgw : (Γ D).dist (v D i) (g • w) = 6 := by
    have := GPath.dist_smul D.polyHyp.connected g (v D i) w
    rw [hgv] at this
    rw [this]
    exact hw
  obtain ⟨q, hq, hqw⟩ := MB.Qtrans (g • w) w hgw hw
  have hqv : q • v D i = v D i :=
    MulAction.mem_stabilizer_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le p _ hq)
  refine ⟨q * g, by rw [mul_smul, hgv, hqv], by rw [mul_smul, hqw], ?_, ?_⟩
  · rw [mul_smul, hga]
    exact MB.Qfix a' ha' q hq
  · rw [mul_smul, hgc]
    exact MB.Qfix c' hc' q hq

theorem burnsideF45_g2d_bn_trans (hp : p.Prime) (hU : ChF.IsSylowOf p D.U ⊤) (i : Bool) :
    burnsideF45_TransAt (Γ D) X (v D i) := by
  intro w w' hw hw'
  obtain ⟨q, hq, hqw⟩ := (burnsideF45_bn_modelBase D hp hU i).Qtrans w w' hw hw'
  exact ⟨q, MulAction.mem_stabilizer_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le p _ hq), hqw⟩

omit [Finite X] in
theorem burnsideF45_g2d_bn_opp (m₁ m₂ : D.N) (hm₁ : (m₁ : D.Weyl) = D.w₁)
    (hm₂ : (m₂ : D.Weyl) = D.w₂) (first : Bool) :
    (Γ D).dist (v D (!first)) (D.vv m₁ m₂ first 6) = 6 ∧
      ∀ g ∈ D.root (jIdx 6 first 0), g • v D (!first) = v D (!first) ∧
        g • D.vv m₁ m₂ first 6 = D.vv m₁ m₂ first 6 := by
  have hv0 : D.vv m₁ m₂ first 0 = v D (!first) := by
    rw [D.vv_zero, v_eq_vt]
    rfl
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← hv0]
    exact D.polyHyp.dist_eq_of_path (D.basePath_isGLSPath m₁ m₂ hm₁ hm₂ first)
      (D.basePath_head m₁ m₂ first) (by simp [RankTwoSystem.basePath, List.range_succ])
      (D.basePath_length m₁ m₂ first)
  · have hfix := D.basePath_fix m₁ m₂ hm₁ hm₂ first hg
    have h1 : D.vv m₁ m₂ first 1 ∈ interiorVertices (D.basePath m₁ m₂ first) := by
      simp [interiorVertices, RankTwoSystem.basePath, List.range_succ]
    have h5 : D.vv m₁ m₂ first 5 ∈ interiorVertices (D.basePath m₁ m₂ first) := by
      simp [interiorVertices, RankTwoSystem.basePath, List.range_succ]
    refine ⟨?_, ?_⟩
    · rw [← hv0]
      exact hfix _ h1 _ (D.vv_adj m₁ m₂ hm₁ hm₂ first 0).symm
    · exact hfix _ h5 _ (D.vv_adj m₁ m₂ hm₁ hm₂ first 5)

end BN

section Transport

variable {W V : Type} {ΓW : SimpleGraph W} {ΓV : SimpleGraph V} {X : Type} [Group X]
  [MulAction X V]

@[expose, instance_reducible] def burnsideF45_transAct (e : W ≃ V) : MulAction X W where
  smul x w := e.symm (x • e w)
  one_smul w := by
    show e.symm ((1 : X) • e w) = w
    rw [one_smul, Equiv.symm_apply_apply]
  mul_smul x y w := by
    show e.symm ((x * y) • e w) = e.symm (x • e (e.symm (y • e w)))
    rw [Equiv.apply_symm_apply, mul_smul]

theorem burnsideF45_transAct_graph [GraphAction X ΓV] (e : W ≃ V)
    (he : ∀ a b, ΓW.Adj a b ↔ ΓV.Adj (e a) (e b)) :
    @GraphAction W X _ (burnsideF45_transAct e) ΓW := by
  letI := burnsideF45_transAct (X := X) e
  refine ⟨fun x a b => ?_⟩
  show ΓW.Adj (e.symm (x • e a)) (e.symm (x • e b)) ↔ ΓW.Adj a b
  rw [he, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, GraphAction.adj_smul]

theorem burnsideF45_hexModel_transport (e : W ≃ V) (he : ∀ a b, ΓW.Adj a b ↔ ΓV.Adj (e a) (e b))
    {R : Subgroup X} {x₀ l₀ : V} (M : burnsideF45_HexModel ΓV X R x₀ l₀) :
    @burnsideF45_HexModel W ΓW X _ (burnsideF45_transAct e) R (e.symm x₀) (e.symm l₀) := by
  letI := burnsideF45_transAct (X := X) e
  have hsm : ∀ (x : X) (w : W), x • w = e.symm (x • e w) := fun _ _ => rfl
  have hfix : ∀ (x : X) (w : W), x • w = w ↔ x • e w = e w := by
    intro x w
    rw [hsm, Equiv.symm_apply_eq]
  let iso : ΓW ≃g ΓV := ⟨e, fun {a b} => (he a b).symm⟩
  have hdist : ∀ a b : W, ΓW.dist a b = ΓV.dist (e a) (e b) := fun a b =>
    (CFSG.Quasithin.H13.F431.F45.iso_dist iso a b).symm
  have hstab : ∀ v : V, MulAction.stabilizer X (e.symm v) = MulAction.stabilizer X v := by
    intro v
    ext x
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, hfix, Equiv.apply_symm_apply]
  have hd : ∀ (b : V) (w : W), ΓW.dist (e.symm b) w = ΓV.dist b (e w) := fun b w => by
    rw [hdist, Equiv.apply_symm_apply]
  have faith : ∀ b : V, burnsideF45_FaithfulAt ΓV X b → burnsideF45_FaithfulAt ΓW X (e.symm b) := by
    intro b hb w hw t htb htw hta
    refine hb (e w) (by rw [← hd]; exact hw) t
      (by have := (hfix t _).1 htb; rwa [Equiv.apply_symm_apply] at this) ((hfix t w).1 htw) ?_
    intro a ha
    have ha' : ΓW.Adj (e.symm b) (e.symm a) := by rw [he]; simpa using ha
    have := (hfix t _).1 (hta _ ha')
    rwa [Equiv.apply_symm_apply] at this
  have two : ∀ b : V, burnsideF45_TwoAt ΓV X b → burnsideF45_TwoAt ΓW X (e.symm b) := by
    intro b hb w hw a c a' c' ha hc hac ha' hc' hac'
    have hw' : ΓV.dist b (e w) = 6 := by
      have := hdist (e.symm b) w
      rw [Equiv.apply_symm_apply] at this
      rw [← this]
      exact hw
    have hadj : ∀ z, ΓW.Adj (e.symm b) z → ΓV.Adj b (e z) := fun z hz => by
      have := (he _ _).1 hz
      rwa [Equiv.apply_symm_apply] at this
    obtain ⟨t, htb, htw, hta, htc⟩ := hb (e w) hw' (e a) (e c) (e a') (e c') (hadj a ha) (hadj c hc)
      (e.injective.ne hac) (hadj a' ha') (hadj c' hc') (e.injective.ne hac')
    refine ⟨t, ?_, (hfix t w).2 htw, ?_, ?_⟩
    · rw [hsm, Equiv.apply_symm_apply, htb]
    · rw [hsm, hta, Equiv.symm_apply_apply]
    · rw [hsm, htc, Equiv.symm_apply_apply]
  have trans : ∀ b : V, burnsideF45_TransAt ΓV X b → burnsideF45_TransAt ΓW X (e.symm b) := by
    intro b hb w w' hw hw'
    have h1 : ∀ z, ΓW.dist (e.symm b) z = 6 → ΓV.dist b (e z) = 6 := fun z hz => by
      have := hdist (e.symm b) z
      rw [Equiv.apply_symm_apply] at this
      rw [← this]
      exact hz
    obtain ⟨t, htb, htw⟩ := hb (e w) (e w') (h1 w hw) (h1 w' hw')
    refine ⟨t, ?_, ?_⟩
    · rw [hsm, Equiv.apply_symm_apply, htb]
    · rw [hsm, htw, Equiv.symm_apply_apply]
  refine ⟨?_, faith _ M.faithx, faith _ M.faithl, two _ M.twox, two _ M.twol, trans _ M.transx,
    trans _ M.transl, ?_, ?_, ?_⟩
  · rw [hstab, hstab]
    exact M.edge
  · obtain ⟨w, hw, y, hyx, hyw, hyR⟩ := M.signx
    refine ⟨e.symm w, by rw [hd, Equiv.apply_symm_apply]; exact hw, y, ?_, ?_, hyR⟩
    · rw [hsm, Equiv.apply_symm_apply, hyx]
    · rw [hsm, Equiv.apply_symm_apply, hyw]
  · obtain ⟨w, hw, y, hyl, hyw, hy1, hyy, hyR⟩ := M.signl
    refine ⟨e.symm w, by rw [hd, Equiv.apply_symm_apply]; exact hw, y, ?_, ?_, hy1, hyy, hyR⟩
    · rw [hsm, Equiv.apply_symm_apply, hyl]
    · rw [hsm, Equiv.apply_symm_apply, hyw]
  · obtain ⟨y, hyx, hyl, hyR⟩ := M.outer
    refine ⟨y, ?_, ?_, hyR⟩
    · rw [hsm, Equiv.apply_symm_apply, hyx]
    · rw [hsm, Equiv.apply_symm_apply, hyl]

end Transport

section G2

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage4.Hex CFSG.LieType.Steinberg.Adjoint CFSG.ASVolI.ChF
open CFSG.Quasithin (g2Hom g2Rho g2L g2L_zero g2L_one g2L_zero_eq_img g2Img_mem_range
  g2_derived_eq_range two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two u33El g2IndexTwoData
  g2HomC g2RhoC)


variable {K : Type} [Field K] [Finite K]

theorem burnsideF45_g2d_x0_mem_derived (hK : Nat.card K = 2) :
    xUnit Tag.G2 K ⟨0, by decide⟩ 1 ∈ ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  rw [← g2L_zero, g2L_zero_eq_img, g2_derived_eq_range h2 hk2]
  exact g2Img_mem_range h2 2

theorem burnsideF45_g2d_x1_not_mem_derived (hK : Nat.card K = 2) :
    xUnit Tag.G2 K ⟨1, by decide⟩ 1 ∉ ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  rw [← g2L_one, g2_derived_eq_range h2 hk2]
  rintro ⟨u, hu⟩
  apply (g2IndexTwoData h2 hk2).rho_not_mem
  refine ⟨(u33El "asy")⁻¹ * u, Subtype.ext ?_⟩
  show g2Hom h2 ((u33El "asy")⁻¹ * u) = g2Rho h2
  rw [map_mul, map_inv, hu]
  rfl

theorem burnsideF45_g2d_mem_range_iff (hK : Nat.card K = 2) (q : G2Native.Parent K) :
    (q : G2Native.FullModel K) ∈ (burnsideF4h_g2_incl K hK).range ↔
      (q : ModGL Tag.G2 K) ∈ ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ := by
  constructor
  · rintro ⟨s, hs⟩
    induction s using QuotientGroup.induction_on with
    | H d =>
      rw [burnsideF4h_g2_incl_mk] at hs
      have hP : Subgroup.center (G2Native.Parent K) = ⊥ := center_adjointGroup_eq_bot
      have h1 := QuotientGroup.eq.1 hs
      rw [hP, Subgroup.mem_bot] at h1
      have h2 : G2Native.derivedInclusion K d = q := inv_mul_eq_one.1 h1
      rw [← h2]
      exact d.2
  · intro hq
    exact ⟨((⟨q.1, hq⟩ : G2Native.Derived K) : G2Native.SmallModel K), by
      rw [burnsideF4h_g2_incl_mk]
      rfl⟩

theorem burnsideF45_g2d_hexPos_one : hexPos 1 = Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 := by
  funext k
  fin_cases k <;> decide

theorem burnsideF45_g2d_hexPos_six : hexPos 6 = Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 := by
  funext k
  fin_cases k <;> decide

theorem burnsideF45_g2d_root_mem (i : Fin Tag.G2.rank) (j : ℤ)
    (hj : hexPos j = Pi.single i 1) :
    ((⟨xUnit Tag.G2 K i 1, xUnit_mem_adjointGroup i 1⟩ : G2Native.Parent K) :
      G2Native.FullModel K) ∈ (burnsideF4h_g2_sys K).root j := by
  show _ ∈ (hexGroup (g2Roots K) j).map (hexProj _)
  refine ⟨⟨xUnit Tag.G2 K i 1, xUnit_mem_adjointGroup i 1⟩, ?_, rfl⟩
  show _ ∈ rootGroup (rootOperatorFamily .G2) K (hexPos j)
  rw [hj, CFSG.LieType.HighestRoot.rootGroup_eq_subgroupOf (isRoot_single Tag.G2 i)]
  exact Subgroup.mem_subgroupOf.2 (mem_rootSubgroup.2 ⟨1, pinnedX_single Tag.G2 K i 1⟩)

theorem burnsideF45_g2d_hexModel (hK : Nat.card K = 2) :
    burnsideF45_HexModel (Γ (burnsideF4h_g2_sys K)) (G2Native.FullModel K)
      (burnsideF4h_g2_incl K hK).range (v (burnsideF4h_g2_sys K) true)
      (v (burnsideF4h_g2_sys K) false) := by
  set D := burnsideF4h_g2_sys K with hD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK')
  haveI : Finite (G2Native.Parent K) := CFSG.Quasithin.finite_g2Group
  haveI : Finite (G2Native.FullModel K) := inferInstance
  have hU : ChF.IsSylowOf 2 D.U ⊤ := burnsideF4h_g2_sys_U_sylow 2
  have hBcard : Nat.card ↥D.B = 64 := by
    rw [hD, ← burnsideF4h_g2_fullLocal_borel]
    exact burnsideF4h_g2_card_fullBorel hK
  have hB : IsPGroup 2 ↥D.B := IsPGroup.of_card (n := 6) (by rw [hBcard]; norm_num)
  have hP : Subgroup.center (G2Native.Parent K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center (G2Native.Parent K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hP]
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective D.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective D.w₂
  obtain ⟨hdx, hfx⟩ : (Γ D).dist (v D true) (D.vv m₁ m₂ false 6) = 6 ∧
      ∀ g ∈ D.root (CFSG.GH74.BNPair.jIdx 6 false 0), g • v D true = v D true ∧
        g • D.vv m₁ m₂ false 6 = D.vv m₁ m₂ false 6 :=
    burnsideF45_g2d_bn_opp D m₁ m₂ hm₁ hm₂ false
  obtain ⟨hdl, hfl⟩ : (Γ D).dist (v D false) (D.vv m₁ m₂ true 6) = 6 ∧
      ∀ g ∈ D.root (CFSG.GH74.BNPair.jIdx 6 true 0), g • v D false = v D false ∧
        g • D.vv m₁ m₂ true 6 = D.vv m₁ m₂ true 6 :=
    burnsideF45_g2d_bn_opp D m₁ m₂ hm₁ hm₂ true
  have hj1 : CFSG.GH74.BNPair.jIdx 6 false 0 = 1 := by
    simp [CFSG.GH74.BNPair.jIdx, CFSG.GH74.BNPair.stType]
  have hj6 : CFSG.GH74.BNPair.jIdx 6 true 0 = 6 := by
    simp [CFSG.GH74.BNPair.jIdx, CFSG.GH74.BNPair.stType]
  have hx1 := burnsideF45_g2d_root_mem (K := K) ⟨1, by decide⟩ 1 burnsideF45_g2d_hexPos_one
  have hx0 := burnsideF45_g2d_root_mem (K := K) ⟨0, by decide⟩ 6 burnsideF45_g2d_hexPos_six
  rw [← hj1] at hx1
  rw [← hj6] at hx0
  refine ⟨?_, burnsideF45_g2d_bn_faithful D Nat.prime_two hU hB true,
    burnsideF45_g2d_bn_faithful D Nat.prime_two hU hB false,
    burnsideF45_g2d_bn_two D Nat.prime_two hU true, burnsideF45_g2d_bn_two D Nat.prime_two hU false,
    burnsideF45_g2d_bn_trans D Nat.prime_two hU true,
    burnsideF45_g2d_bn_trans D Nat.prime_two hU false, ?_, ?_, ?_⟩
  · have he : MulAction.stabilizer (G2Native.FullModel K) (v D true) ⊓
        MulAction.stabilizer (G2Native.FullModel K) (v D false) = D.B :=
      burnsideF45_g2d_bn_edge D true
    rw [he]
    exact hB
  · refine ⟨D.vv m₁ m₂ false 6, hdx, _, (hfx _ hx1).1, (hfx _ hx1).2, ?_⟩
    rw [burnsideF45_g2d_mem_range_iff hK]
    exact burnsideF45_g2d_x1_not_mem_derived hK
  · refine ⟨D.vv m₁ m₂ true 6, hdl, _, (hfl _ hx0).1, (hfl _ hx0).2, ?_, ?_, ?_⟩
    · intro h
      have h' : (⟨xUnit Tag.G2 K ⟨0, by decide⟩ 1, xUnit_mem_adjointGroup _ 1⟩ :
          G2Native.Parent K) = 1 := hinj (by rw [map_one]; exact h)
      have h'' : pinnedX Tag.G2 K (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) 1 =
          pinnedX Tag.G2 K (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) 0 := by
        rw [pinnedX_single, pinnedX_zero]
        exact congrArg Subtype.val h'
      exact one_ne_zero (pinnedX_injective Tag.G2 K _ h'')
    · rw [← QuotientGroup.mk_mul]
      have h2 := two_eq_zero_of_card_two hK
      have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
      have e : (⟨xUnit Tag.G2 K ⟨0, by decide⟩ 1, xUnit_mem_adjointGroup _ 1⟩ *
          ⟨xUnit Tag.G2 K ⟨0, by decide⟩ 1, xUnit_mem_adjointGroup _ 1⟩ : G2Native.Parent K) = 1 := by
        apply Subtype.ext
        show xUnit Tag.G2 K ⟨0, by decide⟩ 1 * xUnit Tag.G2 K ⟨0, by decide⟩ 1 = 1
        rw [← pinnedX_single, ← pinnedX_add, h11, pinnedX_zero]
      rw [e]
      rfl
    · rw [burnsideF45_g2d_mem_range_iff hK]
      exact burnsideF45_g2d_x0_mem_derived hK
  · have hBR : ¬ D.B ≤ (burnsideF4h_g2_incl K hK).range := by
      rw [hD, ← burnsideF4h_g2_fullLocal_borel]
      exact burnsideF4h_g2_borel_not_le_range hK
    obtain ⟨y, hyB, hyR⟩ := SetLike.not_le_iff_exists.1 hBR
    exact ⟨y, smul_v_of_mem_B D true hyB, smul_v_of_mem_B D false hyB, hyR⟩

end G2

end CFSG.ASVolI
