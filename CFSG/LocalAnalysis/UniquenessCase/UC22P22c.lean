module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.RankThree.FFModules.ChiefFactors

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22c_layer_le (H : Subgroup G) : rankThreeLayer H ≤ H := by
  refine sSup_le ?_
  rintro L ⟨hL, _⟩
  exact hL

theorem uc22p22c_hyp612_of_sigma2 (hS : Standing G) (S : Setup G) :
    ∀ p ∈ (PartTwo.Three.dataOfSetup hS S).sig2, ∃ P P₀ : Subgroup G,
      UC6.Hyp612 (PartTwo.Three.dataOfSetup hS S) p P P₀ := by
  intro p hp
  have hp' := hp
  obtain ⟨hpA, Q, hw, hB⟩ := hp
  have hprime := (PartTwo.Three.prime_of_mem_rankThreeSigmaA hpA).1
  haveI : Fact p.Prime := ⟨hprime⟩
  have hQM : (Q : Subgroup G) ≤ S.M := hw.sylow_le hS hpA
  obtain ⟨_, _, P₀, hP₀Q, hcard, _, _, hnl, _⟩ := hB
  refine ⟨(Q : Subgroup G), P₀, hp', ?_, hP₀Q, hcard, ?_⟩
  · refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hQM, Q.isPGroup', ?_⟩
    intro hdvd
    exact Q.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hQM))
  · intro hle
    exact hnl ((uc22p22c_layer_le _).trans hle)

theorem uc22p22c_layerFour_le (H : Subgroup G) : uniqueFourLayer H ≤ H := by
  refine sSup_le ?_
  rintro L ⟨hL, _⟩
  exact hL

theorem uc22p22c_hyp612_of_sigma2_four (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) :
    ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig2, ∃ P P₀ : Subgroup G,
      UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀ := by
  intro p hp
  have hp' := hp
  obtain ⟨hpσ, hβ, M', hM', hpσ', P', hP'M', -, -, -, -, P₀', hcl⟩ := hp
  haveI : Fact p.Prime := ⟨hβ.1⟩
  obtain ⟨PM, hPM, -⟩ := UC6.exists_sylow_le_of_sigma hU S.maxLocal hpσ
  obtain ⟨g, hg⟩ := UC6.exists_le_uniqueFourConj_sylow PM.isPGroup' P'
  have hPMN : (PM : Subgroup G) ≤ uniqueFourConj g M' :=
    hg.trans (UC6.uniqueFourConj_mono hP'M' g)
  have hN : IsMaxTwoLocalSubgroup (uniqueFourConj g M') := UC6.isMaxTwoLocal_conj hM' g
  have hpN : p ∈ uniqueFourSigma (uniqueFourConj g M') := UC6.mem_uniqueFourSigma_conj hpσ' g
  have h4 : 2 ≤ CFSG.Open.pRank p (PM : Subgroup G) :=
    (by norm_num : 2 ≤ 4).trans (UC6.four_le_pRank_sylow hβ PM)
  have hle : S.M ≤ uniqueFourConj g M' := UC6.sec61 hU hN hpN hPMN h4 S.maxLocal.1 hPM
  have heq : uniqueFourConj g M' = S.M := S.maxLocal.2 _ hN.1 hle
  obtain ⟨hP₀P, hP₀card, -, -, hnl, -⟩ := hcl
  refine ⟨uniqueFourConj g P', uniqueFourConj g P₀', hp', ?_, UC6.uniqueFourConj_mono hP₀P g, ?_, ?_⟩
  · have hPle : uniqueFourConj g (P' : Subgroup G) ≤ S.M :=
      heq ▸ UC6.uniqueFourConj_mono hP'M' g
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨hPle, UC6.isPGroup_uniqueFourConj P'.isPGroup' g, ?_⟩
    intro hdvd
    have h1 : (uniqueFourConj g (P' : Subgroup G)).index = (P' : Subgroup G).index := by
      have e1 := Subgroup.card_mul_index (uniqueFourConj g (P' : Subgroup G))
      have e2 := Subgroup.card_mul_index (P' : Subgroup G)
      rw [UC6.card_uniqueFourConj] at e1
      have hpos : 0 < Nat.card (P' : Subgroup G) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
    exact P'.not_dvd_index (h1 ▸ hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPle))
  · rw [UC6.card_uniqueFourConj]
    exact hP₀card
  · intro hC
    apply hnl
    refine (uc22p22c_layerFour_le _).trans ?_
    intro x hx
    have hxC : g⁻¹ * x * g ∈ centralizer (uniqueFourConj g P₀' : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : g * y * g⁻¹ ∈ P₀' := UC6.mem_uniqueFourConj_iff.1 hy
      have h := mem_centralizer_iff.1 hx (g * y * g⁻¹) hy'
      calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * x * g * y := by group
    have hM : g⁻¹ * x * g ∈ uniqueFourConj g M' := heq ▸ hC hxC
    have := UC6.mem_uniqueFourConj_iff.1 hM
    simpa [mul_assoc] using this

theorem uc22p22c_mem_Z {D : Data G} {x : G} :
    x ∈ D.Z ↔ x ∈ D.T ∧ (∀ k ∈ D.T, k * x = x * k) ∧ x ^ 2 = 1 :=
  CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff

theorem uc22p22c_elem_mono {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F :=
  ⟨⟨⟨fun a b => by
    have h := hE.1.is_comm.comm (⟨a, hFE a.2⟩ : E) ⟨b, hFE b.2⟩
    have h2 := congrArg Subtype.val h
    exact Subtype.ext h2⟩⟩, fun x hx => hE.2 x (hFE hx)⟩

theorem uc22p22c_isPGroup_of_elem {E : Subgroup G} (hE : IsElemAbelian 2 E) : IsPGroup 2 E := by
  intro g
  refine ⟨1, ?_⟩
  have := hE.2 (g : G) g.2
  exact Subtype.ext (by simpa using this)

theorem uc22p22c_U_facts (D : Data G) :
    D.U ≤ pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ∧ IsElemAbelian 2 D.U :=
  uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM

theorem uc22p22c_pCoreOf_le_T (D : Data G) : pCoreOf 2 D.M ≤ D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  have h := CFSG.fitting_pCore_le_sylow S
  rw [hS] at h
  exact Subgroup.map_le_iff_le_comap.2 h

theorem uc22p22c_normalizer_V (D : Data G) {V : Subgroup G} (hVne : V ≠ ⊥)
    (hel : IsElemAbelian 2 V) (hVM : D.M ≤ normalizer (V : Set G)) :
    normalizer (V : Set G) = D.M :=
  normalizer_eq_of_isMaxTwoLocal D.maxLocal hVne (uc22p22c_isPGroup_of_elem hel) hVM

theorem uc22p22c_exists_fixed {V T : Subgroup G} (hV : IsPGroup 2 V) (hVne : V ≠ ⊥)
    (hT : IsPGroup 2 T) (hTV : T ≤ normalizer (V : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ t ∈ T, t * v * t⁻¹ = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).2 hVne
  let φ : ↥T →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hTV)
  letI : MulAction ↥T ↥V := MulAction.compHom ↥V φ
  have hdvd : 2 ∣ Nat.card V := by
    obtain ⟨n, hn0, hn⟩ := hV.nontrivial_iff_card.1 inferInstance
    rw [hn]
    exact dvd_pow_self 2 hn0.ne'
  have h1 : (1 : ↥V) ∈ MulAction.fixedPoints ↥T ↥V := fun t => map_one (φ t)
  obtain ⟨b, hb, hb1⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥V hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun t ht => ?_⟩
  have := hb ⟨t, ht⟩
  exact congrArg Subtype.val this

theorem uc22p22c_not_isTI (D : Data G) {V : Subgroup G} (hVne : V ≠ ⊥) (hel : IsElemAbelian 2 V)
    (hVM : D.M ≤ normalizer (V : Set G)) (hVT : V ≤ D.T)
    (hC : ¬ centralizer (D.Z : Set G) ≤ D.M) : ¬ CFSG.CGT.Timmesfeld75.IsTI V := by
  intro hTI
  have hTM : D.T ≤ normalizer (V : Set G) := D.sylowM.le.trans hVM
  obtain ⟨v, hvV, hv1, hvT⟩ :=
    uc22p22c_exists_fixed (uc22p22c_isPGroup_of_elem hel) hVne D.sylowM.isPGroup hTM
  have hvZ : v ∈ D.Z := by
    refine uc22p22c_mem_Z.2 ⟨hVT hvV, fun k hk => ?_, hel.2 v hvV⟩
    have := hvT k hk
    calc k * v = (k * v * k⁻¹) * k := by group
      _ = v * k := by rw [this]
  obtain ⟨g, hgC, hgM⟩ := SetLike.not_le_iff_exists.1 hC
  have hcomm : v * g = g * v := mem_centralizer_iff.1 hgC v hvZ
  have hvc : v ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V := by
    refine ⟨hvV, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.2 ?_⟩
    have : g⁻¹ * v * g = v := by
      calc g⁻¹ * v * g = g⁻¹ * (v * g) := by group
        _ = v := by rw [hcomm]; group
    rw [this]
    exact hvV
  rcases hTI g with h | h
  · rw [h] at hvc
    exact hv1 (Subgroup.mem_bot.1 hvc)
  · have hle : V ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g V := inf_eq_left.1 h
    have hcard : Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup g V) ≤ Nat.card V := by
      unfold CFSG.CGT.Timmesfeld75.conjSubgroup
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have heq : V = CFSG.CGT.Timmesfeld75.conjSubgroup g V :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    have hgN : g ∈ normalizer (V : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 heq.symm
    rw [uc22p22c_normalizer_V D hVne hel hVM] at hgN
    exact hgM hgN

theorem uc22p22c_odd_normal_eq_bot {Y Vm : Type} [Group Y] [Finite Y] [AddCommGroup Vm]
    [Module (ZMod 2) Vm] [Finite Vm] (ρ : Representation (ZMod 2) Y Vm)
    (hρ : Function.Injective ρ) {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hfix : ∀ v : Vm, (∀ t ∈ T, ρ t v = v) → ∀ y : Y, ρ y v = v)
    (N : Subgroup Y) [hN : N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  set e : Module.End (ZMod 2) Vm := ∑ n : N, ρ (n : Y) with he
  have he1 : ∀ m : N, ρ (m : Y) * e = e := by
    intro m
    rw [he, Finset.mul_sum]
    simp only [← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft m) _ _ (fun n => by simp)
  have he2 : ∀ y : Y, ρ y * e = e * ρ y := by
    intro y
    rw [he, Finset.mul_sum, Finset.sum_mul]
    simp only [← map_mul]
    refine Fintype.sum_equiv (MulAut.conjNormal y).toEquiv _ _ (fun n => ?_)
    show ρ (y * n) = ρ (((MulAut.conjNormal y n : N) : Y) * y)
    congr 1
    simp [mul_assoc]
  have hcard : ((Nat.card N : ℕ) : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2]
    ring
  have hesum : ∀ w : Vm, e w = ∑ n : N, ρ (n : Y) w := fun w => by
    rw [he]; exact LinearMap.sum_apply _ _ _
  have he3 : ∀ v : Vm, e (e v) = e v := by
    intro v
    have h1 : e (e v) = ∑ n : N, ρ (n : Y) (e v) := hesum (e v)
    have h2 : ∀ n : N, ρ (n : Y) (e v) = e v := fun n => by
      have := he1 n
      exact congrArg (fun f => f v) this
    rw [h1]
    simp only [h2, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), Fintype.card_eq_nat_card, hcard, one_smul]
  have hfixe : ∀ w : Vm, (∀ y : Y, ρ y w = w) → e w = w := by
    intro w hw
    rw [hesum]
    simp only [hw, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), Fintype.card_eq_nat_card, hcard, one_smul]
  let K : Subrepresentation ρ :=
    ⟨LinearMap.ker e, fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have := congrArg (fun f => f v) (he2 g)
      simp only [Module.End.mul_apply] at this
      rw [← this, hv, map_zero]⟩
  have hK : K.toSubmodule = ⊥ := by
    by_contra hne
    haveI : Nontrivial K.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hne
    obtain ⟨x, hx0, hx⟩ :=
      CFSG.RankThree.FFModules.exists_fixed_ne_zero_of_isPGroup (K.toRepresentation) hT
    have hxT : ∀ t ∈ T, ρ t (x : Vm) = (x : Vm) := fun t ht => by
      have := hx t ht
      exact (Subrepresentation.toRepresentation_apply_coe).1 this
    have hxY := hfix _ hxT
    have hex : e (x : Vm) = (x : Vm) := hfixe _ hxY
    have hxK : e (x : Vm) = 0 := LinearMap.mem_ker.1 x.2
    exact hx0 (Subtype.ext (by rw [← hex, hxK]; rfl))
  have hid : ∀ v : Vm, e v = v := by
    intro v
    have h1 : v - e v ∈ K.toSubmodule := by
      show v - e v ∈ LinearMap.ker e
      rw [LinearMap.mem_ker, map_sub, he3, sub_self]
    rw [hK, Submodule.mem_bot] at h1
    exact (sub_eq_zero.1 h1).symm
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply hρ
  rw [map_one]
  ext v
  have h1 := he1 ⟨n, hn⟩
  have h2 := congrArg (fun f => f v) h1
  simp only [Module.End.mul_apply, hid] at h2
  simpa using h2

theorem uc22p22c_centralizer_pCore_le {Y Vm : Type} [Group Y] [Finite Y] [AddCommGroup Vm]
    [Module (ZMod 2) Vm] [Finite Vm] (hsolv : Group.IsSolvable Y)
    (ρ : Representation (ZMod 2) Y Vm) (hρ : Function.Injective ρ) {T : Subgroup Y}
    (hT : IsPGroup 2 T) (hfix : ∀ v : Vm, (∀ t ∈ T, ρ t v = v) → ∀ y : Y, ρ y v = v) :
    Subgroup.centralizer (CFSG.pCore 2 Y : Set Y) ≤ CFSG.pCore 2 Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : CFSG.pPrimeCore 2 Y = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hcop
    haveI := hK
    exact uc22p22c_odd_normal_eq_bot ρ hρ hT hfix K (Nat.coprime_two_left.1 hcop)
  have hF := CFSG.Fitting_eq_pcore Y 2 hP
  have h := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  rw [hF] at h
  exact h

theorem uc22p22c_core (D : Data G) {V : Subgroup G} (hel : IsElemAbelian 2 V) (hVT : V ≤ D.T)
    (hVM : D.M ≤ normalizer (V : Set G))
    (hker : D.M ⊓ centralizer (V : Set G) = pCoreOf 2 D.M) (hsolv : Group.IsSolvable D.M)
    {b : G} (hbM : b ∈ D.M) (hbZ : b ∈ centralizer (D.Z : Set G)) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hT : ∀ R : Subgroup (MBar D.M V), IsPGroup 2 ↥R → ∀ a : MBar D.M V,
      a ∈ normalizer (R : Set (MBar D.M V)) → Odd (orderOf a) → ¬ 3 ∣ orderOf a →
        ∀ x ∈ R, a * x * a⁻¹ = x) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Vmod, _, _, _, e, ρ, hc⟩ := uc22br4_exists_conjModule D.M V hVM hel
  have hρ : Function.Injective ρ := uc22br4_injective D.M V hVM e ρ hc
  let bm : ↥D.M := ⟨b, hbM⟩
  let bb : MBar D.M V := (QuotientGroup.mk bm : MBar D.M V)
  let Tb : Subgroup (MBar D.M V) := mbarImage D.M V D.T
  let X : Subgroup (MBar D.M V) := Subgroup.zpowers bb ⊔ Tb
  have hTb2 : IsPGroup 2 ↥Tb := by
    have h1 : IsPGroup 2 ↥(D.T.subgroupOf D.M) := D.sylowM.isPGroup.comap_subtype
    exact h1.map (QuotientGroup.mk' (kerAct D.M V).normalCore)
  haveI : Group.IsSolvable ↥D.M := hsolv
  haveI : Group.IsSolvable (MBar D.M V) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (kerAct D.M V).normalCore)
      (QuotientGroup.mk'_surjective _)
  let ρY : Representation (ZMod 2) ↥X Vmod := ρ.comp X.subtype
  have hρY : Function.Injective ρY := hρ.comp (Subgroup.subtype_injective X)
  let T' : Subgroup ↥X := Tb.subgroupOf X
  have hT' : IsPGroup 2 ↥T' := hTb2.comap_subtype
  have hfix : ∀ v : Vmod, (∀ t ∈ T', ρY t v = v) → ∀ y : ↥X, ρY y v = v := by
    intro v hv
    let w : ↥V := e.symm (Multiplicative.ofAdd v)
    have hw : Multiplicative.toAdd (e w) = v := by simp [w]
    have hTw : ∀ t₀ ∈ D.T, t₀ * (w : G) * t₀⁻¹ = (w : G) := by
      intro t₀ ht₀
      have hm : t₀ ∈ D.M := D.sylowM.le ht₀
      let tm : ↥D.M := ⟨t₀, hm⟩
      have htT : (QuotientGroup.mk tm : MBar D.M V) ∈ Tb := ⟨tm, ht₀, rfl⟩
      have hX : (QuotientGroup.mk tm : MBar D.M V) ∈ X := Subgroup.mem_sup_right htT
      have h1 : ρ (QuotientGroup.mk tm) v = v := hv ⟨_, hX⟩ htT
      have h2 : ρ (QuotientGroup.mk tm) (Multiplicative.toAdd (e w)) =
          Multiplicative.toAdd (e w) := by rw [hw]; exact h1
      exact (uc22br_gt_conj_iff D.M V hVM e ρ hc tm w).2 h2
    have hwZ : (w : G) ∈ D.Z := by
      refine uc22p22c_mem_Z.2 ⟨hVT w.2, fun k hk => ?_, hel.2 (w : G) w.2⟩
      have := hTw k hk
      calc k * (w : G) = (k * (w : G) * k⁻¹) * k := by group
        _ = (w : G) * k := by rw [this]
    have hbw : b * (w : G) * b⁻¹ = (w : G) := by
      have h := mem_centralizer_iff.1 hbZ (w : G) hwZ
      calc b * (w : G) * b⁻¹ = (b * (w : G)) * b⁻¹ := rfl
        _ = ((w : G) * b) * b⁻¹ := by rw [h]
        _ = (w : G) := by group
    have hbv : ρ bb v = v := by
      have := (uc22br_gt_conj_iff D.M V hVM e ρ hc bm w).1 hbw
      rwa [hw] at this
    let S : Subgroup (MBar D.M V) :=
      { carrier := {x | ρ x v = v}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          show ρ (x * y) v = v
          rw [map_mul, Module.End.mul_apply, show ρ y v = v from hy, show ρ x v = v from hx]
        inv_mem' := fun {x} hx => by
          show ρ x⁻¹ v = v
          have hx' : ρ x v = v := hx
          calc ρ x⁻¹ v = ρ x⁻¹ (ρ x v) := by rw [hx']
            _ = v := by
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply] }
    have hXS : X ≤ S := sup_le (Subgroup.zpowers_le.2 hbv) (fun t ht =>
      show ρ t v = v from hv ⟨t, Subgroup.mem_sup_right ht⟩ ht)
    intro y
    exact hXS y.2
  have hcentr := uc22p22c_centralizer_pCore_le (Y := ↥X) inferInstance ρY hρY hT' hfix
  let R : Subgroup (MBar D.M V) := (CFSG.pCore 2 ↥X).map X.subtype
  have hR : IsPGroup 2 ↥R := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
  have hbX : bb ∈ X := Subgroup.mem_sup_left (Subgroup.mem_zpowers bb)
  let a' : ↥X := ⟨bb, hbX⟩
  have hord : orderOf bb ∣ r := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (kerAct D.M V).normalCore) bm
    rwa [← Subgroup.orderOf_coe bm, show (bm : G) = b from rfl, hbr] at h
  have hodd : Odd (orderOf bb) ∧ ¬ 3 ∣ orderOf bb := by
    rcases (Nat.dvd_prime hr).1 hord with h | h
    · rw [h]
      exact ⟨odd_one, by norm_num⟩
    · rw [h]
      refine ⟨hr.odd_of_ne_two (by omega), fun h3 => ?_⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h3
      omega
  have hnorm : bb ∈ normalizer (R : Set (MBar D.M V)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨a' * y * a'⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem y hy a', ?_⟩
      rfl
    · rintro ⟨z, hz, hzx⟩
      have hz' : a'⁻¹ * z * a' ∈ CFSG.pCore 2 ↥X := by
        have := (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem z hz a'⁻¹
        simpa using this
      refine ⟨a'⁻¹ * z * a', hz', ?_⟩
      have h1 : bb * x * bb⁻¹ = (z : MBar D.M V) := hzx.symm
      show bb⁻¹ * (z : MBar D.M V) * bb = x
      rw [← h1]
      group
  have hcomm := hT R hR bb hnorm hodd.1 hodd.2
  have hbc : a' ∈ centralizer (CFSG.pCore 2 ↥X : Set ↥X) := by
    rw [mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have h := hcomm (y : MBar D.M V) ⟨y, hy, rfl⟩
    show (y : MBar D.M V) * bb = bb * (y : MBar D.M V)
    calc (y : MBar D.M V) * bb = (bb * (y : MBar D.M V) * bb⁻¹) * bb := by rw [h]
      _ = bb * (y : MBar D.M V) := by group
  have hapc : a' ∈ CFSG.pCore 2 ↥X := hcentr hbc
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨a', hapc⟩
  have hbk : bb ^ (2 ^ k) = 1 := by
    have h := congrArg (fun z : ↥(CFSG.pCore 2 ↥X) => ((z : ↥X) : MBar D.M V)) hk
    simpa [a'] using h
  have hbb1 : bb = 1 := by
    rcases (Nat.dvd_prime hr).1 hord with h | h
    · exact orderOf_eq_one_iff.1 h
    · exfalso
      have h1 : r ∣ 2 ^ k := h ▸ orderOf_dvd_of_pow_eq_one hbk
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h1
      have := Nat.le_of_dvd (by norm_num) h2
      omega
  have hbC : (bm : G) ∈ centralizer (V : Set G) := (uc22br_gt_mk_eq_one_iff hVM bm).1 hbb1
  have hbO : b ∈ pCoreOf 2 D.M := by
    rw [← hker]
    exact ⟨hbM, hbC⟩
  obtain ⟨x, hx, hxb⟩ := hbO
  obtain ⟨k', hk'⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)) ⟨x, hx⟩
  have hbk' : b ^ (2 ^ k') = 1 := by
    have h := congrArg (fun z : ↥(CFSG.pCore 2 ↥D.M) => (((z : ↥D.M)) : G)) hk'
    simpa [← hxb] using h
  have h1 : r ∣ 2 ^ k' := hbr ▸ orderOf_dvd_of_pow_eq_one hbk'
  have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem uc22p22c_hyp11 (D : Data G) {V : Subgroup G} (hW : InCalW D.M D.T V)
    (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V) : F11.Hyp11 D ⊥ V :=
  ⟨Or.inr ⟨rfl, hW⟩, hTI, fun h => absurd h (by rw [Subgroup.card_bot]; omega)⟩

theorem uc22p22c_cTilde_bot (M V : Subgroup G) :
    F11.CTilde M ⊥ V = M ⊓ centralizer (V : Set G) := by
  ext x
  simp only [F11.CTilde, Subgroup.mem_iInf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨(h 1 V.one_mem).1, mem_centralizer_iff.2 fun v hv => ?_⟩
    have h2 : x * v * x⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := (h v hv).2.2
    rw [Subgroup.mem_bot] at h2
    calc v * x = (x * v * x⁻¹ * v⁻¹) * (v * x) := by rw [h2]; group
      _ = x * v := by group
  · rintro ⟨hxM, hxC⟩ v hv
    refine ⟨hxM, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      simp [Subgroup.mem_bot]
    · have h := mem_centralizer_iff.1 hxC v hv
      rw [Subgroup.mem_bot]
      calc x * v * x⁻¹ * v⁻¹ = (x * v) * x⁻¹ * v⁻¹ := rfl
        _ = (v * x) * x⁻¹ * v⁻¹ := by rw [← h]
        _ = 1 := by group

theorem uc22p22c_isSubnormal_le {H K : Subgroup G} (h : CFSG.Open.IsSubnormal H K) : H ≤ K := by
  induction h with
  | refl H => exact le_rfl
  | step hHM _ _ ih => exact hHM.trans ih

theorem uc22p22c_exists_prime_ge_five {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ n - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 8 * 2 ^ m :=
    ⟨n - 3, by rw [show n = 3 + (n - 3) by omega, pow_add]; norm_num⟩
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  by_contra hcon
  push Not at hcon
  have hpos : 2 ^ n - 1 ≠ 0 := by omega
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ n - 1 → d = 3 := by
    intro d hd hdvd
    have hd5 : d < 5 := by
      by_contra h
      exact hcon d hd (by omega) hdvd
    have hodd : ¬ 2 ∣ 2 ^ n - 1 := by omega
    interval_cases d
    · exact absurd hd Nat.not_prime_zero
    · exact absurd hd Nat.not_prime_one
    · exact absurd hdvd hodd
    · rfl
    · exact absurd hd (by norm_num)
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos hall
  have hmod : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
    intro k
    induction k with
    | zero => left; rfl
    | succ k ih => rw [pow_succ]; omega
  have h := hmod (2 ^ n - 1).primeFactorsList.length
  rw [← hpow] at h
  omega

@[expose] def R613Rank (D : Data G) : Prop :=
  ∀ V : Subgroup G, D.M ≤ normalizer (V : Set G) → D.M ⊓ centralizer (V : Set G) = pCoreOf 2 D.M →
    ∀ (p : ℕ) (P P₀ : Subgroup G), UC6.Hyp612 D p P P₀ →
      ∀ R : Subgroup (MBar D.M V), IsPGroup 2 ↥R → ∀ a : MBar D.M V,
        a ∈ normalizer (R : Set (MBar D.M V)) → Odd (orderOf a) → ¬ 3 ∣ orderOf a →
          ∀ x ∈ R, a * x * a⁻¹ = x

theorem s22_8_of (D : Data G) (Ch : Choice2011 G) (h111 : F11.R111 D) (hV : S22_V D Ch)
    (h112 : F11.R112 D) (hhyp612 : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀)
    (h613 : UC6.R6_13 D) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) (hT : R613Rank D) :
    S22_8 D Ch := by
  intro h1930 c
  obtain ⟨hVU1, hVU2⟩ := uc22p22c_U_facts D
  have hVO : c.V ≤ pCoreOf 2 D.M := c.hVU.trans (hVU1.trans inf_le_left)
  have hel : IsElemAbelian 2 c.V := uc22p22c_elem_mono hVU2 c.hVU
  have hVT : c.V ≤ D.T := hVO.trans (uc22p22c_pCoreOf_le_T D)
  have hTI := uc22p22c_not_isTI D c.hVne hel c.hVM hVT c.hC
  have hH11 := uc22p22c_hyp11 D (hV h1930 c).1 hTI
  have hsig3 : D.sig3 = ∅ := h111 ⊥ c.V hH11
  refine Set.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
  · rw [D.sig_sub] at hp
    rcases hp with (h | h) | h
    · exact h
    · exfalso
      obtain ⟨P, P₀, hP⟩ := hhyp612 p h
      have hsolv : Group.IsSolvable D.M := (h613 p P P₀ hP).1.2.1
      have hker := h112 ⊥ c.V hH11 ⟨p, h⟩
      rw [uc22p22c_cTilde_bot] at hker
      obtain ⟨r, hr, hr5, hrdvd⟩ := uc22p22c_exists_prime_ge_five (hn3 c)
      have hrπ : r ∈ piSet c.B0 := by
        rw [c.hpi]
        exact ⟨hr, hrdvd⟩
      haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hrπ.2
      have hbB : (x : G) ∈ c.B0 := x.2
      have hbr : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
      have hbM : (x : G) ∈ D.M := c.hBM hbB
      have hLC : c.L ≤ centralizer (D.Z : Set G) := uc22p22c_isSubnormal_le c.hL.2
      have hbZ : (x : G) ∈ centralizer (D.Z : Set G) := hLC (c.hLge (c.hB0.1 hbB))
      exact uc22p22c_core D hel hVT c.hVM hker hsolv hbM hbZ hr hr5 hbr
        (hT c.V c.hVM hker p P P₀ hP)
    · rw [hsig3] at h
      exact absurd h (Set.notMem_empty p)
  · rw [D.sig_sub]
    exact Or.inl (Or.inl hp)

end CFSG.LocalAnalysis.UniquenessCase.UC22
