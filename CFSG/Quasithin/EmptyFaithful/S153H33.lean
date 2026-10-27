module

public import CFSG.Quasithin.EmptyFaithful.S153D33
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input33CharTwoSup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Stage15325 → CtxComp T Mc M V₁ V₂ Yp I t → IsComponentIn L I →
      ∀ L₁ : Subgroup G, L₁ ≤ conjClosure L (Sgp153 T V₁) →
        Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L₁ : Set G) → CharTwo L₁ → ¬ L₁ ≤ M ⊓ I →
          CharTwo (L₁ ⊔ (Yp ⊔ Sgp153 T V₁))

namespace S153H

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem exists_generator_Z (h : Hyp153 G T Mc M) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧
      quasithinOmegaOneCenter T = Subgroup.zpowers z := by
  have h2 := h.lemma_15_3_2_two.2
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.qtfe.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  refine ⟨z, hz, hz1', ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr hz
  · rw [h2, Nat.card_zpowers]
    have h3 : orderOf z ≠ 1 := fun h1 => hz1' (orderOf_eq_one_iff.mp h1)
    have h4 : 0 < orderOf z := orderOf_pos z
    omega

omit [Finite G] in
theorem centralizer_zpowers_eq (z : G) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) = Subgroup.centralizer {z} := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h z (Subgroup.mem_zpowers z)
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left h k).eq

theorem lemma115Hyp_of_ctx (h11 : StageLemma14111) (h113 : StageLemma14113)
    (c : CtxComp T Mc M V₁ V₂ Yp I t) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) (hZ : quasithinOmegaOneCenter T = Subgroup.zpowers z) :
    Lemma115Hyp I (Sgp153 T V₁) Mc z := by
  have hh : Hyp153 G T Mc M := c.hyp.hyp
  have hq := hh.qtfe
  obtain ⟨S₀, hS₀⟩ := hq.exists_sylow
  have hTSyl : IsSylowTwoOf T Mc := by
    have := isSylowTwoOf_of_sylow S₀ (H := Mc) (hS₀ ▸ hq.t_le_mc)
    rwa [hS₀] at this
  obtain ⟨hzT, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hz
  have hV₁T : V₁ ≤ T := c.hyp.decomp.le₁.trans hh.VZ_le_T
  have hzV₁ : z ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hV₁T hzC)
  refine
    { pCore_ne_bot := c.inH.1.2
      sylow := c.facts.sylow
      charTwo := hq.qtke.2.1 Mc hq.mc_max.1 ⟨S₀, hS₀ ▸ hq.t_le_mc⟩
      pCore_M_ne_bot := pCoreOf_ne_bot_of_isTwoLocal hq.mc_max.1
      le := inf_le_left.trans hq.t_le_mc
      centralizer_le := ?_
      centralizer_z_le := ?_
      z_ne_one := hz1
      z_mem := ⟨hzT, hzV₁⟩
      z_central := Subgroup.centralizer_le inf_le_left hzC
      z_sq := hz2 }
  ·
    rintro x ⟨hxO, hxC⟩
    obtain ⟨H, hH⟩ := exists_inM_of_pCoreOf_ne_bot c.inH.1.2
    have hIH : I ≤ H := hH.2
    have hS : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
    have hHplus : IsHPlus Yp (Sgp153 T V₁) M H :=
      ⟨⟨c.inH.1.1.trans hIH, (inH_of_inM hH).2⟩, fun hHM => c.inH.2 (hIH.trans hHM)⟩
    have hSH : IsSylowTwoOf (Sgp153 T V₁) H := c.hyp.lemma_15_3_11_one h11 h113 hHplus
    have hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H := by
      have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
        ⟨pCoreOf 2 H, (inH_of_inM hH).2, pCoreOf_isPGroup 2 H, rfl⟩
      exact hH.1.2 _ hloc (le_normalizer_pCoreOf 2 H)
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hOHS : pCoreOf 2 H ≤ Sgp153 T V₁ :=
      A4.le_of_normal_of_isSylowTwoOf hSH (pCoreOf_le 2 H)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr
          (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
    have hSIM : Sgp153 T V₁ ≤ I ⊓ Mc := le_inf hS (inf_le_left.trans hq.t_le_mc)
    have hOHI : pCoreOf 2 H ≤ pCoreOf 2 (I ⊓ Mc) :=
      le_pCoreOf_of_le_normalizer 2 (hOHS.trans hSIM)
        (fun g hg => le_normalizer_pCoreOf 2 H (hIH hg.1)) (pCoreOf_isPGroup 2 H)
    have hxT : x ∈ T :=
      A4.le_of_normal_of_isSylowTwoOf hTSyl (pCoreOf_le 2 Mc)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 Mc)).mpr
          (le_normalizer_pCoreOf 2 Mc)) (pCoreOf_isPGroup 2 Mc) hxO
    have hxH : x ∈ H := by
      rw [← hNH]
      refine Subgroup.centralizer_le_normalizer _ ?_
      exact Subgroup.centralizer_le (fun y hy => hOHI hy) hxC
    have hTH : T ⊓ H ≤ Sgp153 T V₁ :=
      (A4.isSylowTwoOf_iff_maximal.mp hSH).2.2 (T ⊓ H) inf_le_right
        (hTSyl.2.1.to_le inf_le_left) (le_inf inf_le_left hSH.1)
    exact hS (hTH ⟨hxT, hxH⟩)
  · intro x hx
    have hxC : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hZ] at hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute z x := Subgroup.mem_centralizer_iff.mp hx z rfl
      exact (hcomm.zpow_left k).eq
    show x ∈ Mc
    rw [hh.lemma_15_3_4 h11]
    exact hxC

theorem exists_component (c : CtxComp T Mc M V₁ V₂ Yp I t) : ∃ K : Subgroup G, IsComponentIn K I := by
  by_contra hno
  push Not at hno
  exact c.notCharTwo (DoubleA3.charTwo_of_no_component hno c.oddCore)

theorem not_le_M_of_isComponentIn (c : CtxComp T Mc M V₁ V₂ Yp I t) {K : Subgroup G}
    (hK : IsComponentIn K I) : ¬ K ≤ M := by
  intro hKM
  exact DoubleA3.not_isComponentIn_of_charTwo c.charTwo_MI K
    (BenderBranch.isComponentIn_of_le hK (le_inf hKM hK.1) inf_le_right)

theorem oddCoreIn_le_of_subnormal {K H : Subgroup G} (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal) :
    oddCoreIn K ≤ oddCoreIn H := by
  intro y hy
  have hyK : y ∈ K := oddCoreIn_le K hy
  have hyH : y ∈ H := hKH hyK
  let π : Set Nat.Primes := {q | q.val ≠ 2}
  have h1 : (⟨y, hyK⟩ : K) ∈ CFSG.oddCore ↥K := (mem_oddCoreIn_iff K ⟨y, hyK⟩).mp hy
  rw [CFSG.oddCore_eq_piCore] at h1
  let e : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have h2 : e.symm ⟨y, hyK⟩ ∈ CFSG.piCore π ↥(K.subgroupOf H) := by
    have := CFSG.LocalCores.piCore_map_mulEquiv π e.symm
    rw [← this]
    exact ⟨_, h1, rfl⟩
  have hmem : (⟨y, hyH⟩ : H) ∈ (K.subgroupOf H) ⊓ CFSG.piCore π H := by
    rw [← CFSG.LocalCores.prime_set_core_subnormal_intersection π hsub]
    exact ⟨e.symm ⟨y, hyK⟩, h2, rfl⟩
  have hodd' : (⟨y, hyH⟩ : H) ∈ CFSG.oddCore H := by
    rw [CFSG.oddCore_eq_piCore]
    exact hmem.2
  exact (mem_oddCoreIn_iff H ⟨y, hyH⟩).mpr hodd'

theorem oddCoreIn_le_of_isComponentIn {K H : Subgroup G} (hK : IsComponentIn K H) :
    oddCoreIn K ≤ oddCoreIn H :=
  oddCoreIn_le_of_subnormal hK.1 hK.2.2

theorem charTwo_of_mem_cComp_not_isComponentIn (hI : oddCoreIn I = ⊥) {K : Subgroup G}
    (hK : K ∈ cComp I) (hnc : ¬ IsComponentIn K I) : CharTwo K := by
  have hKI : K ≤ I := le_of_mem_cComp hK
  have hsubK : CFSG.Open.IsSubnormal K I := subnormal_of_mem_cComp hK
  have hE : ∀ K' : Subgroup G, ¬ IsComponentIn K' K := by
    intro K' hK'
    have hq' : CFSG.IsQuasisimple ↥K' := BenderBranch.isQuasisimple_of_isComponentIn hK'
    have hperf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp hq'.1
    have hne : K' ≠ ⊥ := Unc25G2.isComponentIn_ne_bot hK'
    have hsub' : CFSG.Open.IsSubnormal K' K := Id2519.open_isSubnormal_of_subgroupOf hK'.1 hK'.2.2
    have hsubI : CFSG.Open.IsSubnormal K' I := Quasithin.A3.subnormal_trans hsub' hsubK
    have hEq : K' = K := by
      by_contra hne'
      exact not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hK'.1 hne') hne hperf hsubI
    subst hEq
    exact hnc ⟨hKI, CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKI).symm hq',
      Id2519.subgroupOf_isSubnormal_of_open hsubK⟩
  have hodd : oddCoreIn K = ⊥ :=
    le_bot_iff.mp ((oddCoreIn_le_of_subnormal hKI (Id2519.subgroupOf_isSubnormal_of_open hsubK)).trans
      hI.le)
  exact DoubleA3.charTwo_of_no_component hE hodd

theorem centerOf_eq_pCoreOf_of_isComponentIn (hI : oddCoreIn I = ⊥) {K : Subgroup G}
    (hK : IsComponentIn K I) : centerOf K = pCoreOf 2 K := by
  have hq := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hKK : IsComponentIn K K := Id2519.isComponentIn_self hq
  apply le_antisymm
  ·
    have h2 : IsPGroup 2 (centerOf K) := by
      intro x
      have hxK : (x : G) ∈ K := x.2.1
      have hxc : ∀ w ∈ K, w * (x : G) = (x : G) * w := fun w hw =>
        Subgroup.mem_centralizer_iff.mp x.2.2 w hw
      obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd
        (orderOf_pos (x : G)).ne'
      have hy : (x : G) ^ 2 ^ k ∈ oddCoreIn I := by
        refine Unc25G2.mem_oddCoreIn_of_central_odd hK (Subgroup.pow_mem K hxK _)
          (fun w hw => (Commute.pow_right (hxc w hw) _).eq) ?_
        have hdvd : orderOf ((x : G) ^ 2 ^ k) ∣ m := by
          refine orderOf_dvd_of_pow_eq_one ?_
          rw [← pow_mul, ← hord]
          exact pow_orderOf_eq_one _
        exact Odd.of_dvd_nat hm hdvd
      rw [hI, Subgroup.mem_bot] at hy
      exact ⟨k, Subtype.ext (by simpa using hy)⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        normalizer_le_normalizer_centralizer K (Subgroup.le_normalizer hg)⟩) h2
  · intro x hx
    have hcomm := Unc25G2.commutator_pCoreOf_eq_bot hKK
    have hle : K ≤ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    refine Subgroup.mem_inf.mpr ⟨pCoreOf_le 2 K hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) x hx).symm

theorem input15333_of_charTwoSup (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hcs : Input33CharTwoSup) : Input15333 := by
  intro hS25 G _ _ T Mc M V₁ V₂ Yp I t c
  obtain ⟨L, hL⟩ := exists_component c
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  obtain ⟨z, hz, hz1, hZ⟩ := exists_generator_Z c.hyp.hyp
  have h115 := lemma115Hyp_of_ctx h11 h113 c hz hz1 hZ
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  refine ⟨L, ?_⟩
  refine
    { mem := Id2519.mem_cComp_of_isComponentIn hL
      quasisimple := hq
      center_eq := centerOf_eq_pCoreOf_of_isComponentIn c.oddCore hL
      not_le := not_le_M_of_isComponentIn c hL
      inv_le := ?_
      comp_prop := ?_ }
  ·
    intro L₁ hL₁ hN hchar
    by_contra hnle
    have hL₁I : L₁ ≤ I := hL₁.trans (conjClosure_le fun s hs l hl =>
      I.mul_mem (I.mul_mem (hSI hs) (hL.1 hl)) (I.inv_mem (hSI hs)))
    have hCX := hcs G T Mc M V₁ V₂ Yp I L t hS25 c hL L₁ hL₁ hN hchar hnle
    have hV₁ne : ∃ v ∈ V₁, v ≠ 1 := by
      have hV₁b : V₁ ≠ ⊥ := by
        intro hb
        have := c.hyp.decomp.card₁
        rw [hb, Subgroup.card_bot] at this
        omega
      obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₁b
      exact ⟨v, hv, fun h1 => hv1 (Subtype.ext h1)⟩
    have hV₁S : V₁ ≤ Sgp153 T V₁ :=
      le_inf (c.hyp.decomp.le₁.trans c.hyp.hyp.VZ_le_T) Subgroup.le_normalizer
    have hX : IsHPlus Yp (Sgp153 T V₁) M (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) := by
      refine ⟨⟨le_sup_right, ?_⟩, fun hXM => hnle (le_inf (le_sup_left.trans hXM) hL₁I)⟩
      intro hb
      obtain ⟨v, hv, hv1⟩ := hV₁ne
      have hvX : v ∈ L₁ ⊔ (Yp ⊔ Sgp153 T V₁) := Subgroup.mem_sup_right (Subgroup.mem_sup_right (hV₁S hv))
      have h1 : (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) ⊓
          Subgroup.centralizer (pCoreOf 2 (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) : Set G) ≤
          pCoreOf 2 (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) := hCX
      rw [hb] at h1
      refine hv1 (Subgroup.mem_bot.mp (h1 ⟨hvX, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩))
      rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]
    exact hS25 G T Mc M V₁ V₂ Yp t c.hyp _ hX hCX
  ·
    intro K hKc
    obtain ⟨-, hcomm, -, hchar⟩ := h115.component_action hKc
    have hcent : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
        Subgroup.centralizer {z} := by
      rw [hZ]
      exact centralizer_zpowers_eq z
    refine ⟨not_le_M_of_isComponentIn c hKc, ?_, ?_, ?_⟩
    · rw [hZ]
      exact hcomm
    · exact le_bot_iff.mp ((oddCoreIn_le_of_isComponentIn hKc).trans c.oddCore.le)
    · rw [hcent]
      exact hchar

end S153H

end CFSG.Quasithin
