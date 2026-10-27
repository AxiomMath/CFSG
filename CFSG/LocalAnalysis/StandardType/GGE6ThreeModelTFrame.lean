module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTSpec
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftT
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

include hn hK hσ in
theorem tFrame_center : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ := by
  exact center_graphFixedRootGroup_eq_bot σ.surjective

theorem tFrame_faithful (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.Faithful := by
  intro x y hxy
  have hdiag : D.ad (Multiplicative.toAdd x) = D.ad (Multiplicative.toAdd y) := by
    rw [FrameData.ad, FrameData.ad, ofAdd_toAdd, ofAdd_toAdd]
    exact hxy
  obtain ⟨hxa, hxaeq⟩ := hD.diag_eq (Multiplicative.toAdd x)
  obtain ⟨hyb, hybeq⟩ := hD.diag_eq (Multiplicative.toAdd y)
  have hΦeq : rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hxa⟩ =
      rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hyb⟩ := by
    rw [← hxaeq, ← hybeq]; exact hdiag
  have hsub : (⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹, hxa⟩ :
      ↥(TwistedDiag.Rgrp Ω Fr)) =
      ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹, hyb⟩ :=
    rgrpConjAut_injective (L := Ω) hn hK σ hσ Fr hFr hΦeq
  have hd : rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) := by
    have hval : (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹ :
        ModGL Tag.E6 Ω) =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹ :=
      congrArg Subtype.val hsub
    have key : ∀ z : ModGL Tag.E6 Ω, g⁻¹ * (g * z * g⁻¹) * g = z := fun z => by group
    have h1 : g⁻¹ * (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹) * g =
        g⁻¹ * (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹) * g :=
      congrArg (fun z : ModGL Tag.E6 Ω => g⁻¹ * z * g) hval
    rw [key (rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x))),
      key (rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)))] at h1
    exact h1
  have hxy' := zetaVec_injective (τ := Tag.E6) (p := 3) hζo hζ (rootDiagUnit_injective hd)
  exact Multiplicative.ext hxy'

theorem tFrame_torus (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.TorusOK := by
  have hcommT : ∀ s ∈ D.Tor, ∀ t ∈ D.Tor, s * t = t * s := by
    intro s hs t ht
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K Ω)
    change baseChangeGL (algebraMap K Ω) ((s : ModGL TwistTag.E6.tag K) * (t : ModGL TwistTag.E6.tag K)) =
      baseChangeGL (algebraMap K Ω) ((t : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K))
    obtain ⟨s₀, hs₀, hs₀eq⟩ := Subgroup.mem_map.1 ((hD.tor_eq s).1 hs)
    obtain ⟨t₀, ht₀, ht₀eq⟩ := Subgroup.mem_map.1 ((hD.tor_eq t).1 ht)
    have hs0 : baseChangeGL (algebraMap K Ω) (s : ModGL TwistTag.E6.tag K) = g * s₀ * g⁻¹ :=
      hs₀eq.symm
    have ht0 : baseChangeGL (algebraMap K Ω) (t : ModGL TwistTag.E6.tag K) = g * t₀ * g⁻¹ :=
      ht₀eq.symm
    rw [map_mul, map_mul, hs0, ht0]
    have hst : s₀ * t₀ = t₀ * s₀ := by
      obtain ⟨s₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs₀
      exact rootDiagUnit_mul_comm_of_mem_torusGroup s₁ ht₀
    calc (g * s₀ * g⁻¹) * (g * t₀ * g⁻¹) = g * (s₀ * t₀) * g⁻¹ := by group
      _ = g * (t₀ * s₀) * g⁻¹ := by rw [hst]
      _ = (g * t₀ * g⁻¹) * (g * s₀ * g⁻¹) := by group
  have hoddT : ∀ t ∈ D.Tor, Odd (orderOf t) := by
    intro t ht
    obtain ⟨t₀, ht₀, ht₀eq⟩ := Subgroup.mem_map.1 ((hD.tor_eq t).1 ht)
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀
    have hbase : baseChangeGL (algebraMap K Ω) (t : ModGL TwistTag.E6.tag K) =
        g * rootDiagUnit Tag.E6 b * g⁻¹ := ht₀eq.symm
    have hmemC : baseChangeGL (algebraMap K Ω) (t : ModGL TwistTag.E6.tag K) ∈
        TwistedDiag.Cgrp K σ.toRingHom Ω := ⟨(t : ModGL TwistTag.E6.tag K), t.2, rfl⟩
    obtain ⟨-, hCR, -, -, -⟩ := TwistedDiag.cgrp_facts hn K hK σ.toRingHom hσ h3 Ω Fr hFr
    have hR : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
      rw [← hbase]; exact hCR hmemC
    have hθ : rootDiagUnit Tag.E6 b ∈ TwistedDiag.thetaFixed Fr :=
      (TwistedDiag.mem_thetaFixed_iff_conj Fr hL.1 hL.2 _).2 hR
    have hbq : ∀ i, b i ^ (2 ^ n + 1) = 1 :=
      (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr b).1 hθ.2
    have hpowb : (rootDiagUnit Tag.E6 b) ^ (2 ^ n + 1) = 1 := by
      rw [rootDiagUnit_pow]
      have hb1 : b ^ (2 ^ n + 1) = 1 := funext fun i => hbq i
      rw [hb1, rootDiagUnit_one]
    have hpowconj : (g * rootDiagUnit Tag.E6 b * g⁻¹) ^ (2 ^ n + 1) = 1 := by
      rw [conj_pow, hpowb, mul_one, mul_inv_cancel]
    have hpbase : (baseChangeGL (algebraMap K Ω) (t : ModGL TwistTag.E6.tag K)) ^ (2 ^ n + 1) = 1 := by
      rw [hbase]; exact hpowconj
    have hpT : t ^ (2 ^ n + 1) = 1 := by
      apply Subtype.ext
      exact baseChangeGL_injective (algebraMap K Ω) (by
        change baseChangeGL (algebraMap K Ω) ((t : ModGL TwistTag.E6.tag K) ^ (2 ^ n + 1)) =
          baseChangeGL (algebraMap K Ω) 1
        rw [map_pow, map_one]
        exact hpbase)
    have hoddq : Odd (2 ^ n + 1) := by
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 2 * m :=
        ⟨2 ^ (n - 1), by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]⟩
      exact ⟨m, by rw [hm]⟩
    have hdvd : orderOf t ∣ 2 ^ n + 1 := orderOf_dvd_of_pow_eq_one hpT
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hoddq
    rw [← Nat.not_even_iff_odd]
    intro hEven
    exact (Nat.not_even_iff_odd.2 hoddq) (hEven.mul_right k)
  have hfixT : ∀ (x : Fin Tag.E6.rank → ZMod 3)
      (t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)), t ∈ D.Tor → D.ad x t = t := by
    intro x t ht
    obtain ⟨hx, hxaeq⟩ := hD.diag_eq x
    let z : ↥(TwistedDiag.Rgrp Ω Fr) :=
      ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hx⟩
    let w : ↥(RecipeExcLang.twInndiagGroup K σ) :=
      (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm z
    obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.1 ((hD.tor_eq t).1 ht)
    have hbaseT : baseChangeGL (algebraMap K Ω) (t : ModGL TwistTag.E6.tag K) = g * s * g⁻¹ :=
      hseq.symm
    have hbcw : baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ := by
      have h := twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    apply Subtype.ext
    rw [hxaeq]
    change ((RecipeExcLang.twConj K σ w) t : ModGL TwistTag.E6.tag K) =
      (t : ModGL TwistTag.E6.tag K)
    rw [RecipeExcLang.coe_twConj]
    apply baseChangeGL_injective (algebraMap K Ω)
    change baseChangeGL (algebraMap K Ω)
        ((w : ModGL TwistTag.E6.tag K) * (t : ModGL TwistTag.E6.tag K) *
          (w : ModGL TwistTag.E6.tag K)⁻¹) =
      baseChangeGL (algebraMap K Ω) (t : ModGL TwistTag.E6.tag K)
    rw [map_mul, map_mul, map_inv, hbcw, hbaseT]
    have hcomm : rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * s =
        s * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) :=
      rootDiagUnit_mul_comm_of_mem_torusGroup (zetaVec ζ hζ x) hs
    calc (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) * (g * s * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹)⁻¹
        = g * (rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * s *
            (rootDiagUnit Tag.E6 (zetaVec ζ hζ x))⁻¹) * g⁻¹ := by group
      _ = g * s * g⁻¹ := by rw [hcomm]; group
  exact ⟨hcommT, hoddT, hfixT⟩

theorem torusElt_mem_Cgrp (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) (i : Fin Tag.E6.rank) (s : Ωˣ) (hs : s ^ (2 ^ n + 1) = 1) :
    g * torusElt Tag.E6 Ω i s * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set b : Fin Tag.E6.rank → Ωˣ := Pi.mulSingle i s⁻¹ with hb
  have hbq : ∀ j, b j ^ (2 ^ n + 1) = 1 := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [hb, Pi.mulSingle_eq_same, inv_pow, hs, inv_one]
    · rw [hb, Pi.mulSingle_eq_of_ne hj, one_pow]
  have hdθ : rootDiagUnit Tag.E6 b ∈ TwistedDiag.thetaFixed Fr := by
    rw [TwistedDiag.mem_thetaFixed]
    exact ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b),
      (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr b).2 hbq⟩
  have huR : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr :=
    (TwistedDiag.mem_thetaFixed_iff_conj Fr hL.1 hL.2 (rootDiagUnit Tag.E6 b)).1 hdθ
  have hnC : g * weylElt Tag.E6 Ω i 1 * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω :=
    ⟨(D.nb i : ModGL TwistTag.E6.tag K), (D.nb i).2, hD.nb_eq i⟩
  obtain ⟨-, hCR, hCnorm, -, -⟩ := TwistedDiag.cgrp_facts hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  have hnuC : (⟨g * rootDiagUnit Tag.E6 b * g⁻¹, huR⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) *
      (⟨g * weylElt Tag.E6 Ω i 1 * g⁻¹, hCR hnC⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) *
      (⟨g * rootDiagUnit Tag.E6 b * g⁻¹, huR⟩ : ↥(TwistedDiag.Rgrp Ω Fr))⁻¹ ∈
      (TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr) :=
    hCnorm.conj_mem (⟨g * weylElt Tag.E6 Ω i 1 * g⁻¹, hCR hnC⟩ : ↥(TwistedDiag.Rgrp Ω Fr))
      (Subgroup.mem_subgroupOf.2 hnC) ⟨g * rootDiagUnit Tag.E6 b * g⁻¹, huR⟩
  have htarget : (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
      (g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
        (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹)⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω :=
    (TwistedDiag.Cgrp K σ.toRingHom Ω).mul_mem hnC
      ((TwistedDiag.Cgrp K σ.toRingHom Ω).inv_mem (Subgroup.mem_subgroupOf.1 hnuC))
  have hmid : weylElt Tag.E6 Ω i 1 * rootDiagUnit Tag.E6 b * (weylElt Tag.E6 Ω i 1)⁻¹ *
      (rootDiagUnit Tag.E6 b)⁻¹ = torusElt Tag.E6 Ω i s := by
    rw [torusElt_eq_rootDiagUnit, weylElt_conj_rootDiagUnit b i, rootDiagUnit_inv,
      ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [hb, Pi.mulSingle_eq_same,
      mul_comm ((Pi.mulSingle i s⁻¹ : Fin Tag.E6.rank → Ωˣ) j)
        ((s⁻¹) ^ (-Tag.E6.cartan i j)),
      mul_assoc, mul_inv_cancel, mul_one, inv_zpow, zpow_neg, inv_inv]
  have hident : (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
      (g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
        (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹)⁻¹ =
      g * torusElt Tag.E6 Ω i s * g⁻¹ := by
    rw [show (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
        (g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
          (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹)⁻¹ =
        g * (weylElt Tag.E6 Ω i 1 * rootDiagUnit Tag.E6 b * (weylElt Tag.E6 Ω i 1)⁻¹ *
          (rootDiagUnit Tag.E6 b)⁻¹) * g⁻¹ by group]
    rw [hmid]
  rwa [hident] at htarget

theorem tFrame_inner_point (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) :
    ∀ v ∈ NoOffRest.hypE6, ∃ r ∈ D.Tor, r ^ 3 = 1 ∧ MulAut.conj r = D.ad v ∧
      baseChangeGL (algebraMap K Ω) (r : ModGL TwistTag.E6.tag K) =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  intro v hv
  obtain ⟨y, hy⟩ := CFSG.StandardType.NoOffE6Three.zetaVec_eq_cartanChar_of_mem_hyp ζ hζ hv
  have hd_eq : rootDiagUnit Tag.E6 (zetaVec ζ hζ v) =
      ((List.finRange Tag.E6.rank).map fun j => torusElt Tag.E6 Ω j (zetaVec ζ hζ y j)).prod := by
    rw [hy, list_prod_torusElt_eq_rootDiagUnit]
  have hyq : ∀ j, zetaVec ζ hζ y j ^ (2 ^ n + 1) = 1 := by
    intro j
    rw [zetaVec_apply]
    obtain ⟨m, hm⟩ := h3
    rw [hm, ← pow_mul, show (y j).val * (3 * m) = 3 * ((y j).val * m) by ring, pow_mul, hζ,
      one_pow]
  have hXvC : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ ∈
      TwistedDiag.Cgrp K σ.toRingHom Ω := by
    have hf' : ((List.finRange Tag.E6.rank).map fun j =>
          g * torusElt Tag.E6 Ω j (zetaVec ζ hζ y j) * g⁻¹) =
        ((List.finRange Tag.E6.rank).map fun j =>
          torusElt Tag.E6 Ω j (zetaVec ζ hζ y j)).map (MulAut.conj g) := by
      rw [List.map_map]
      exact List.map_congr_left fun j _ => (MulAut.conj_apply g _).symm
    have hmap : g * ((List.finRange Tag.E6.rank).map fun j =>
          torusElt Tag.E6 Ω j (zetaVec ζ hζ y j)).prod * g⁻¹ =
        ((List.finRange Tag.E6.rank).map fun j =>
          g * torusElt Tag.E6 Ω j (zetaVec ζ hζ y j) * g⁻¹).prod := by
      rw [hf', ← map_list_prod, MulAut.conj_apply]
    rw [hd_eq, hmap]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact torusElt_mem_Cgrp hn hK σ hσ Fr hFr h3 hL hζ hD j _ (hyq j)
  obtain ⟨r, hrF, hr_eq⟩ := Subgroup.mem_map.1 hXvC
  let r' : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := ⟨r, hrF⟩
  have hr_eq' : baseChangeGL (algebraMap K Ω) (r' : ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ := hr_eq
  obtain ⟨hx, hxeq⟩ := hD.diag_eq v
  have hzeta3 : (zetaVec ζ hζ v) ^ 3 = 1 := by
    funext j
    rw [Pi.pow_apply, Pi.one_apply, zetaVec_apply, ← pow_mul,
      show (v j).val * 3 = 3 * (v j).val by ring, pow_mul, hζ, one_pow]
  have hd3 : (rootDiagUnit Tag.E6 (zetaVec ζ hζ v)) ^ 3 = 1 := by
    rw [rootDiagUnit_pow, hzeta3, rootDiagUnit_one]
  refine ⟨r', ?_, ?_, ?_, hr_eq'⟩
  · refine (hD.tor_eq r').2 ⟨rootDiagUnit Tag.E6 (zetaVec ζ hζ v),
      rootDiagUnit_mem_torusGroup _, ?_⟩
    show g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ =
      baseChangeGL (algebraMap K Ω) (r' : ModGL TwistTag.E6.tag K)
    rw [hr_eq']
  · apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K Ω)
    change baseChangeGL (algebraMap K Ω) (((r' : ModGL TwistTag.E6.tag K)) ^ 3) =
      baseChangeGL (algebraMap K Ω) (1 : ModGL TwistTag.E6.tag K)
    rw [map_pow, map_one, hr_eq']
    calc (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹) ^ 3
        = g * (rootDiagUnit Tag.E6 (zetaVec ζ hζ v)) ^ 3 * g⁻¹ :=
          @conj_pow (ModGL Tag.E6 Ω) _ 3 g (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))
      _ = 1 := by rw [hd3]; group
  · rw [hxeq]
    have hrconj : rgrpConjAut hn hK σ hσ Fr hFr
        ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹, hx⟩ = MulAut.conj r' := by
      have hcΓ : (r' : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup K σ :=
        RecipeExcLang.graphFixedRootGroup_le_twInndiag σ r'.2
      have h1 : twInndiagEquivRgrp hn hK σ hσ Fr hFr ⟨r', hcΓ⟩ =
          ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹, hx⟩ := by
        refine Subtype.ext ?_
        rw [twInndiagEquivRgrp_apply]
        exact hr_eq'
      rw [← h1, rgrpConjAut_apply_baseChange]
      exact RecipeExcLang.twConj_of_mem_C0 σ r'
    exact hrconj.symm

theorem tFrame_inner (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.InnerPts := by
  intro v hv
  obtain ⟨r, hr, hr3, hrconj, -⟩ :=
    tFrame_inner_point hn hK σ hσ Fr hFr h3 hL hζ hζo hD v hv
  exact ⟨r, hr, hr3, hrconj⟩

private theorem langCube_le_diag_range {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) :
    TwE6DD2.langCube hn hK σ hσ Fr hFr g ≤ D.diag.range := by
  intro y hy
  obtain ⟨b, hb, hx, hyeq⟩ := (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).1 hy
  have hb3 : b ^ 3 = 1 := by funext i; simpa using hb i
  obtain ⟨x, hxeq⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3
  obtain ⟨hx', hx'eq⟩ := hD.diag_eq x
  have hval : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ =
      g * rootDiagUnit Tag.E6 b * g⁻¹ := by rw [hxeq]
  have hsub : (⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hx'⟩ :
      ↥(TwistedDiag.Rgrp Ω Fr)) =
      ⟨g * rootDiagUnit Tag.E6 b * g⁻¹, hx⟩ := Subtype.ext hval
  refine ⟨Multiplicative.ofAdd x, ?_⟩
  rw [show D.diag (Multiplicative.ofAdd x) = D.ad x from rfl, hx'eq, hsub, hyeq]

theorem tFrame_shape (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.Shape := by
  intro X hX hXel hX5
  have hXrange : X ≤ (RecipeExcLang.twConj K σ).range := by
    rw [← hD.H_eq]; exact hX
  obtain ⟨g₁, hg₁, hgn₁, hle⟩ :=
    TwE6DD2.exists_cubeTorus_lang hn hK σ hσ h3 Fr hFr hXel hXrange hX5
  obtain ⟨β, hβ, hmap⟩ :=
    TwE6DD2.exists_conj_langCube hn hK σ hσ Fr hFr hg₁ hgn₁ hL.1 hL.2
  refine ⟨β, ?_, ?_⟩
  · rw [hD.H_eq]; exact hβ
  · intro x hx
    have hxβ : β * x * β⁻¹ ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g := by
      have hmem : β * x * β⁻¹ ∈ (TwE6DD2.langCube hn hK σ hσ Fr hFr g₁).map
          (MulAut.conj β).toMonoidHom := ⟨x, hle hx, rfl⟩
      rw [hmap] at hmem
      exact hmem
    exact langCube_le_diag_range hn hK σ hσ Fr hFr hL hζ hζo hD hxβ

theorem tFrame_norm (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.NormOK := by
  intro r S _ hS
  let w₀ : ↥(RecipeExcLang.twInndiagGroup K σ) :=
    ⟨(r : ModGL TwistTag.E6.tag K), RecipeExcLang.graphFixedRootGroup_le_twInndiag σ r.2⟩
  let a : ↥(TwistedDiag.Rgrp Ω Fr) := twInndiagEquivRgrp hn hK σ hσ Fr hFr w₀
  let B : ModGL Tag.E6 Ω := (a : ModGL Tag.E6 Ω)
  have hconj : rgrpConjAut hn hK σ hσ Fr hFr a = MulAut.conj r := by
    change rgrpConjAut hn hK σ hσ Fr hFr
      (twInndiagEquivRgrp hn hK σ hσ Fr hFr w₀) = MulAut.conj r
    rw [rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr w₀]
    exact RecipeExcLang.twConj_of_mem_C0 σ r
  let c : ModGL Tag.E6 Ω := g⁻¹ * B * g
  have hc : c ∈ adjointGroup Tag.E6 Ω := by
    have hb : B ∈ adjointGroup Tag.E6 Ω := (TwistedDiag.mem_Rgrp Fr).1 a.2 |>.1
    exact mul_mem (mul_mem (inv_mem hL.1) hb) hL.1
  have hkeyB : ∀ z : ModGL Tag.E6 Ω,
      g⁻¹ * (B * (g * z * g⁻¹) * B⁻¹) * g = c * z * c⁻¹ :=
    fun z => by simp only [c]; group
  have hkey2 : ∀ z : ModGL Tag.E6 Ω, g⁻¹ * (g * z * g⁻¹) * g = z := fun z => by group
  have hcd : ∀ x y : Fin Tag.E6.rank → ZMod 3,
      MulAut.conj r * D.ad x * (MulAut.conj r)⁻¹ = D.ad y →
      c * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * c⁻¹ =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ y) := by
    intro x y hxy
    obtain ⟨hx, hxaeq⟩ := hD.diag_eq x
    obtain ⟨hy, hybeq⟩ := hD.diag_eq y
    have hz : a * (⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hx⟩ :
        ↥(TwistedDiag.Rgrp Ω Fr)) * a⁻¹ =
        ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ y) * g⁻¹, hy⟩ := by
      apply rgrpConjAut_injective (L := Ω) hn hK σ hσ Fr hFr
      have hmul : rgrpConjAut hn hK σ hσ Fr hFr
            (a * ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hx⟩ * a⁻¹) =
          rgrpConjAut hn hK σ hσ Fr hFr a *
            rgrpConjAut hn hK σ hσ Fr hFr
              (⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hx⟩ :
                ↥(TwistedDiag.Rgrp Ω Fr)) *
            (rgrpConjAut hn hK σ hσ Fr hFr a)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [hmul, hconj, ← hxaeq, ← hybeq]
      exact hxy
    have hzv : (a : ModGL Tag.E6 Ω) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) *
          (a : ModGL Tag.E6 Ω)⁻¹ =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ y) * g⁻¹ := by
      have := congrArg (fun z : ↥(TwistedDiag.Rgrp Ω Fr) => (z : ModGL Tag.E6 Ω)) hz
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have h2 := congrArg (fun z : ModGL Tag.E6 Ω => g⁻¹ * z * g) hzv
    rw [hkeyB (rootDiagUnit Tag.E6 (zetaVec ζ hζ x)),
      hkey2 (rootDiagUnit Tag.E6 (zetaVec ζ hζ y))] at h2
    exact h2
  let V : Set (ModGL Tag.E6 Ω) := {d | ∃ x ∈ S, d = rootDiagUnit Tag.E6 (zetaVec ζ hζ x)}
  have hVD : ∀ d ∈ V, ∃ b : Fin Tag.E6.rank → Ωˣ, d = rootDiagUnit Tag.E6 b := by
    rintro d ⟨x, -, rfl⟩
    exact ⟨zetaVec ζ hζ x, rfl⟩
  have hgV : ∀ d ∈ V, c * d * c⁻¹ ∈ V := by
    rintro d ⟨x, hxS, rfl⟩
    obtain ⟨y, hyS, hxy⟩ := hS x hxS
    exact ⟨y, hyS, hcd x y hxy⟩
  obtain ⟨w, hw⟩ := NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
    (V := V) hVD hc hgV
  refine ⟨w, fun x hxS => ?_⟩
  obtain ⟨y, hyS, hxy⟩ := hS x hxS
  have h1 : c * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * c⁻¹ =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ y) := hcd x y hxy
  have h2 : c * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * c⁻¹ =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (adAct .E6 3 w x)) := by
    rw [hw _ ⟨x, hxS, rfl⟩, canonicalRep_conj_rootDiagUnit, weylTuple_zetaVec]
  have hyx : y = adAct .E6 3 w x :=
    zetaVec_injective (τ := Tag.E6) (p := 3) hζo hζ
      (rootDiagUnit_injective (h1.symm.trans h2))
  rw [← hyx]
  exact hxy

end CFSG.StandardType.E6ThreeModel
