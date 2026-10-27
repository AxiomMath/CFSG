module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Sec
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreE
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalGroups.F2Fixed
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

section Vec

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_ne_zero_perp_two (u₁ u₂ : Fin 2 ⊕ Fin 2 → K) :
    ∃ w : Fin 2 ⊕ Fin 2 → K, w ≠ 0 ∧ polar (quadPlus 2 K) u₁ w = 0 ∧
      polar (quadPlus 2 K) u₂ w = 0 := by
  classical
  let f : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K × K :=
    LinearMap.prod (polarBilin (quadPlus 2 K) u₁) (polarBilin (quadPlus 2 K) u₂)
  have hdim : Module.finrank K (K × K) < Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨w, hw0, ?_, ?_⟩
  · have := congrArg Prod.fst (LinearMap.mem_ker.mp hw)
    simpa [f] using this
  · have := congrArg Prod.snd (LinearMap.mem_ker.mp hw)
    simpa [f] using this

theorem exists_nonsingular_perp91 {u u' : Fin 2 ⊕ Fin 2 → K}
    (hQ : (polarBilin (quadPlus 2 K)).Nondegenerate)
    (hu : quadPlus 2 K u = 0) (hu' : quadPlus 2 K u' = 0)
    (huu' : polar (quadPlus 2 K) u u' ≠ 0) :
    ∃ a : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) u a = 0 ∧ polar (quadPlus 2 K) u' a = 0 ∧
      quadPlus 2 K a ≠ 0 := by
  obtain ⟨w, hw0, hwu, hwu'⟩ := exists_ne_zero_perp_two (K := K) u u'
  by_contra hcon
  push Not at hcon
  have hW : ∀ a : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) u a = 0 →
      polar (quadPlus 2 K) u' a = 0 → quadPlus 2 K a = 0 := fun a h1 h2 => hcon a h1 h2
  have hp := huu'
  set p := polar (quadPlus 2 K) u u' with hpdef
  apply hw0
  apply hQ.1 w
  intro v
  show polar (quadPlus 2 K) w v = 0
  set z : Fin 2 ⊕ Fin 2 → K := v - (polar (quadPlus 2 K) v u' / p) • u -
    (polar (quadPlus 2 K) v u / p) • u' with hz
  have hzu : polar (quadPlus 2 K) u z = 0 := by
    rw [hz, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_eq_zero hu, ← hpdef, polar_comm (quadPlus 2 K) u v]
    field_simp
    ring
  have hzu' : polar (quadPlus 2 K) u' z = 0 := by
    rw [hz, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_eq_zero hu', polar_comm (quadPlus 2 K) u' u, ← hpdef,
      polar_comm (quadPlus 2 K) u' v]
    field_simp
    ring
  have hzz : polar (quadPlus 2 K) w z = 0 := by
    have h1 := hW (w + z) (by rw [polar_add_right, hwu, hzu, add_zero])
      (by rw [polar_add_right, hwu', hzu', add_zero])
    have h2 := hW w hwu hwu'
    have h3 := hW z hzu hzu'
    have := QuadraticMap.map_add (quadPlus 2 K) w z
    rw [h1, h2, h3] at this
    linear_combination -this
  have hv : v = (polar (quadPlus 2 K) v u' / p) • u + (polar (quadPlus 2 K) v u / p) • u' + z := by
    rw [hz]; abel
  rw [hv, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_comm (quadPlus 2 K) w u, polar_comm (quadPlus 2 K) w u', hwu, hwu', hzz]
  ring

end Vec

section Mod

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem exists_X_eichler91 (E : ElemMatrixIso Q X) {u w : ι → K} (hw : polar Q u w = 0) :
    ∃ A : ↥X, E.equiv A = eichlerG Q u w ∧ (A : GL ι K) ∈ E.LomGL u ∧
      ∀ v, ((A : GL ι K) : Matrix ι ι K) *ᵥ v = eichler Q u w v := by
  have happ : ∀ v, (((E.equiv.symm (eichlerG Q u w) : ↥X) : GL ι K) : Matrix ι ι K) *ᵥ v =
      eichler Q u w v := fun v => by
    rw [← E.app, MulEquiv.apply_symm_apply]
    rfl
  exact ⟨E.equiv.symm (eichlerG Q u w), MulEquiv.apply_symm_apply _ _,
    (Om10.mem_LomGL_iff_eichler E).mpr ⟨(E.equiv.symm (eichlerG Q u w)).2, w, hw, happ⟩, happ⟩

end Mod

theorem polar_eichler_ne_zero91 {V K : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {u u' w : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (hp : polar Q u u' ≠ 0) (hw : polar Q u' w = 0) (hwu : polar Q u w = 0) (hQw : Q w ≠ 0) :
    polar Q u (eichler Q u' w u) ≠ 0 := by
  have h1 : polar Q u (eichler Q u' w u) = -(Q w * polar Q u u' * polar Q u u') := by
    rw [eichler_apply hu' hw u, polar_sub_right, polar_add_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_self_eq_zero hu, hwu]
    ring
  rw [h1]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hQw hp) hp)

section Main

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_sec_two_pow91 {R N I L₁ L₂ A₁ A₂ : Subgroup G}
    {X : Subgroup (GL (Fin 2 ⊕ Fin 2) K)} (E : ElemMatrixIso (quadPlus 2 K) X)
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K) (hφ : φ.range = X) (hNφ : φ.ker = N.subgroupOf R)
    (hQ : (polarBilin (quadPlus 2 K)).Nondegenerate) {u u' : Fin 2 ⊕ Fin 2 → K}
    (hu : quadPlus 2 K u = 0) (hu' : quadPlus 2 K u' = 0)
    (huu' : polar (quadPlus 2 K) u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u')
    (h₁ : L₁ ≤ R) (h₂ : L₂ ≤ R)
    (hP : ∀ r ∈ R, ∀ x ∈ N, r * x * r⁻¹ ∈ N) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hd : IsOppDecomp N I L₁ L₂ A₁ A₂) {e : ℕ} (he : Nat.card K = 2 ^ e) :
    ∃ N₁ : ℕ, Nat.card N = Nat.card I * 2 ^ N₁ ∧ 2 * e ∣ N₁ := by
  classical
  have hd0 := hd
  obtain ⟨hIA₁, hA₁N, hIA₂, hA₂N, hsup, hinf, hcomm, hsq, -, -⟩ := hd0
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hcomm
  haveI : Finite M := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂
  have hcardN : Nat.card N = Nat.card I * Nat.card M :=
    natCard_eq_of_isSecMod (hIA₁.trans hA₁N) hκ
  obtain ⟨N₁, hN₁⟩ := exists_card_eq_two_pow hκ.two
  refine ⟨N₁, by rw [hcardN, hN₁], ?_⟩
  have h4 : 4 ≤ Fintype.card (Fin 2 ⊕ Fin 2) := by simp
  have he1 : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [he, this] at h1
    simp at h1
  obtain ⟨a, ha, ha', hc⟩ := exists_nonsingular_perp91 hQ hu hu' huu'
  have hu'u : polar (quadPlus 2 K) u' u ≠ 0 := by rw [polar_comm]; exact huu'
  refine dvd_of_forall_prime_dvd (k := 2 * e) (by omega) fun r hr hrk => ?_
  have hrq : r ∣ Nat.card K ^ 2 - 1 := by
    have : Nat.card K ^ 2 = 2 ^ (2 * e) := by rw [he, ← pow_mul, mul_comm]
    rw [this]; exact hrk
  obtain ⟨κ', hκ'0, hpow⟩ := exists_eichler_pair_order91 hQ hu hu' huu' ha ha' hc hr hrq
  have hw' : polar (quadPlus 2 K) u' (κ' • a) = 0 := by
    rw [polar_smul_right_eq, ha', mul_zero]
  have hwu : polar (quadPlus 2 K) u (κ' • a) = 0 := by
    rw [polar_smul_right_eq, ha, mul_zero]
  have hQw : quadPlus 2 K (κ' • a) ≠ 0 := by
    rw [map_smul_eq_sq]
    exact mul_ne_zero (pow_ne_zero 2 hκ'0) hc
  letI : DistribMulAction (Gom (quadPlus 2 K)) M := descendAction (viaMatrix X E.equiv φ hφ)
    (viaMatrix_surjective φ hφ) (fun y hy a => by
      rw [ker_viaMatrix] at hy
      exact hker y hy a)
  have hdec' : IsCompl (fixedSub M (Lom (quadPlus 2 K) u : Set (Gom (quadPlus 2 K))))
      (fixedSub M (Lom (quadPlus 2 K) u' : Set (Gom (quadPlus 2 K)))) := by
    rw [fixedSub_descend_Lom E φ hφ hker hL₁, fixedSub_descend_Lom E φ hφ hker hL₂]
    exact hdec
  have h4' : 4 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]; simpa using h4
  have hcard := card_fixedSub_Lom_eq (M := M) hQ h4' hu hu' huu'
  have hx := (stroth_2_1_ii_omega_fixed_of_card hQ hκ.two hu hu' huu' hdec' hcard
    (x := eichlerG (quadPlus 2 K) u' (κ' • a)) (eichlerG_mem_Lom hw')
    ⟨u, polar_eichler_ne_zero91 hu hu' huu' hw' hwu hQw⟩).1
  have hy := (stroth_2_1_ii_omega_fixed_of_card hQ hκ.two hu' hu hu'u hdec'.symm hcard.symm
    (x := eichlerG (quadPlus 2 K) u a) (eichlerG_mem_Lom ha)
    ⟨u', polar_eichler_ne_zero91 hu' hu hu'u ha ha' hc⟩).1
  have hinf' : fixedSub M ({eichlerG (quadPlus 2 K) u' (κ' • a)} : Set (Gom (quadPlus 2 K))) ⊓
      fixedSub M ({eichlerG (quadPlus 2 K) u a} : Set (Gom (quadPlus 2 K))) = ⊥ := by
    rw [hx, hy]
    exact hdec'.symm.inf_eq_bot
  have hfp := fixedSub_mul_eq_bot hκ.two (eichlerG_mul_self hw') (eichlerG_mul_self ha) hinf'
  have hpowG : (eichlerG (quadPlus 2 K) u' (κ' • a) * eichlerG (quadPlus 2 K) u a) ^ r = 1 :=
    Subtype.ext (by simpa [eichlerG] using hpow)
  have hdvd := dvd_card_sub_one_of_fixedSub_eq_bot hr hpowG hfp
  rw [hN₁] at hdvd
  exact hdvd

end Main

end HS9

end CFSG.RankThree.GF2n.Stroth80
