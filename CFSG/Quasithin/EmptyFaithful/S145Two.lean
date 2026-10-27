module

public import CFSG.Quasithin.EmptyFaithful.S145Odd
public import CFSG.Quasithin.EmptyFaithful.S145Cop
public import CFSG.Quasithin.EmptyFaithful.S145Facts
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace S145

section General

variable {G : Type} [Group G]

theorem commutator_le_of_le_normalizer {U P : Subgroup G}
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) : ⁅U, P⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro u hu p hp
  have hu' : p * u⁻¹ * p⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hPU hp) u⁻¹).mp (U.inv_mem hu)
  have : ⁅u, p⁆ = u * (p * u⁻¹ * p⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact U.mul_mem hu hu'

theorem le_normalizer_commutator {A U P : Subgroup G} (hU : A ≤ Subgroup.normalizer (U : Set G))
    (hP : A ≤ Subgroup.normalizer (P : Set G)) :
    A ≤ Subgroup.normalizer ((⁅U, P⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hU hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP hh)]

variable [Finite G]

theorem perfectCore_eq_bot_of_le_pGroup {H K : Subgroup G} (hK : IsPGroup 2 K)
    (hle : perfectCore H ≤ K) : perfectCore H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(perfectCore H) := hK.to_le hle
  have : Group.IsNilpotent ↥(perfectCore H) := hp.isNilpotent
  have : Group.IsPerfect ↥(perfectCore H) := Subgroup.isPerfect_iff.mpr (perfectCore_perfect H)
  by_contra hne
  have : Nontrivial ↥(perfectCore H) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable (G := ↥(perfectCore H)) inferInstance

end General

end S145

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.inf_centralizer_eq_of_commutator_eq_bot (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) (hcomm : ⁅conjClosure (VZ T M) H, pCoreOf 2 H⁆ = ⊥) :
    H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) = pCoreOf 2 H := by
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have h4 : centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H :=
    S.lemma_14_5_15_four hH
  have hQc : ∀ q ∈ pCoreOf 2 H, ∀ u ∈ conjClosure (VZ T M) H, u * q = q * u := by
    intro q hq u hu
    have := Subgroup.commutator_le.mp hcomm.le u hu q hq
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  apply le_antisymm
  · rintro x ⟨hxH, hxc⟩
    rw [← h4]
    refine ⟨hxH, Subgroup.centralizer_le_normalizer _ (hHG hxH), fun u hu => ?_⟩
    have hc : x * u * x⁻¹ * u⁻¹ = 1 := by
      have := Subgroup.mem_centralizer_iff.mp hxc u hu
      calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [this]
        _ = 1 := by group
    rw [hc]
    exact (quasithinOmegaOneCenter T).one_mem
  · intro q hq
    exact ⟨pCoreOf_le 2 H hq, Subgroup.mem_centralizer_iff.mpr fun u hu => hQc q hq u hu⟩

theorem Setting146.isSolvable_of_commutator_eq_bot (h1413 : StageLemma1413) (S : Setting146 G T M)
    {H : Subgroup G} (hH : IsHTM T M H)
    (hcomm : ⁅conjClosure (VZ T M) H, pCoreOf 2 H⁆ = ⊥) : Group.IsSolvable ↥H := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hHcU := S.inf_centralizer_eq_of_commutator_eq_bot hH hcomm
  have h4 : centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H :=
    S.lemma_14_5_15_four hH
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := h91.conjClosure_Vp_le_pCoreOf
  have hQc : ∀ q ∈ pCoreOf 2 H, ∀ u ∈ conjClosure (VZ T M) H, u * q = q * u := by
    intro q hq u hu
    have := Subgroup.commutator_le.mp hcomm.le u hu q hq
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  have hred : IsTwoReducedIn H (conjClosure (VZ T M) H) := by
    refine ⟨hUQ.trans hQH, le_normalizer_conjClosure _ _, S.lemma_14_5_15_two hH, ?_⟩
    intro D hDH hHD hD
    have h1 : D ≤ centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) := by
      refine h91.F92_1_reduced hDH hHD fun d hd => ?_
      obtain ⟨k, hk⟩ := hD d hd
      refine ⟨k, ?_⟩
      rw [h4]
      exact hHcU.le ⟨H.pow_mem (hDH hd) _, hk⟩
    rw [h4] at h1
    intro d hd
    exact Subgroup.mem_centralizer_iff.mpr fun u hu => hQc d (h1 hd) u hu
  have hpc : perfectCore H ≤ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) :=
    h1413 G T S.hyp.simple S.hyp.qtke S.hyp.sylow S.hyp.faithful_empty H hH.1 _ hred
  have hpcQ : perfectCore H ≤ pCoreOf 2 H := (le_inf (perfectCore_le H) hpc).trans hHcU.le
  exact (isSolvable_iff_perfectCore_eq_bot H).mpr
    (S145.perfectCore_eq_bot_of_le_pGroup (pCoreOf_isPGroup 2 H) hpcQ)

theorem Setting146.lemma_14_5_21_two (h1413 : StageLemma1413) (S : Setting146 G T M)
    {H : Subgroup G} (hH : IsHTM T M H) :
    ⁅conjClosure (VZ T M) H, pCoreOf 2 H⁆ = quasithinOmegaOneCenter T := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hle : ⁅conjClosure (VZ T M) H, pCoreOf 2 H⁆ ≤ quasithinOmegaOneCenter T := by
    rw [Subgroup.commutator_le]
    intro u hu q hq
    rw [commutatorElement_def]
    exact h91.commutator_conjClosure_le u hu q hq
  rcases HypF98.eq_bot_or_eq_of_card_eq_two S.card_Z hle with hbot | heq
  swap
  · exact heq
  exfalso
  have hsolv := S.isSolvable_of_commutator_eq_bot h1413 hH hbot
  have hHcU := S.inf_centralizer_eq_of_commutator_eq_bot hH hbot
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := h91.conjClosure_Vp_le_pCoreOf
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hlt : pCoreOf 2 H < H :=
    lt_of_le_of_ne hQH fun heq => hH.2 (heq ▸ hQT.trans hTM)
  obtain ⟨P, hPH, hQP, hHP, hodd⟩ := exists_odd_normal_above_pCoreOf hsolv hlt
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hPU : P ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := hPH.trans hHU
  have hPc : P ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) = pCoreOf 2 H := by
    apply le_antisymm
    · rintro x ⟨hxP, hxc⟩
      exact hHcU.le ⟨hPH hxP, hxc⟩
    · intro q hq
      exact ⟨hQP.le hq, (hHcU.ge hq).2⟩
  have hodd' : Odd ((P ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G)).relIndex P) := by
    rw [hPc]
    exact hodd
  have hWU : ⁅conjClosure (VZ T M) H, P⁆ ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer hPU
  have hWT : ⁅conjClosure (VZ T M) H, P⁆ ≤ T := hWU.trans (hUQ.trans hQT)
  have hTW : T ≤ Subgroup.normalizer ((⁅conjClosure (VZ T M) H, P⁆ : Subgroup G) : Set G) :=
    S145.le_normalizer_commutator (hTH.trans hHU) (hTH.trans hHP)
  have hWne : ⁅conjClosure (VZ T M) H, P⁆ ≠ ⊥ := by
    intro hW
    have hPc' : P ≤ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := Subgroup.commutator_le.mp hW.le u hu p hp
      rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hQP.not_ge ((le_inf le_rfl hPc').trans hPc.le)
  have hTnil : Group.IsNilpotent ↥T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact S.hyp.sylow.1.isNilpotent
  have hWn : ((⁅conjClosure (VZ T M) H, P⁆ : Subgroup G).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWT).mpr hTW
  have hWbot : (⁅conjClosure (VZ T M) H, P⁆ : Subgroup G).subgroupOf T ≠ ⊥ := by
    intro h
    exact hWne ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hWT)
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hWbot
  obtain ⟨⟨x, hxmem⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  obtain ⟨hxW, hxZ⟩ := hxmem
  have hzW : (x : G) ∈ ⁅conjClosure (VZ T M) H, P⁆ := hxW
  have hz1 : (x : G) ≠ 1 := fun h => hxne (Subtype.ext (Subtype.ext h))
  have hzU : (x : G) ∈ conjClosure (VZ T M) H := hWU hzW
  have hz2 : (x : G) ^ 2 = 1 := isElemAbelian_pow_eq_one hUab hzU
  have hzC : (x : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩)
  have hzZ : (x : G) ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨x.2, hzC, hz2⟩
  have hfix : ∀ p ∈ P, p * (x : G) * p⁻¹ = (x : G) := by
    intro p hp
    have h1 : (x : G) * p = p * (x : G) :=
      Subgroup.mem_centralizer_iff.mp (hHG (hPH hp)) _ hzZ
    rw [← h1]
    group
  exact hz1 (eq_one_of_mem_commutator_of_fixed hUab hPU hodd' hzU hzW hfix)

theorem stage14521_two_proof (h1413 : StageLemma1413) :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
      ∀ H : Subgroup G, IsHTM T M H →
        ⁅conjClosure (VZ T M) H, pCoreOf 2 H⁆ = quasithinOmegaOneCenter T :=
  fun _ _ _ _ _ S _ hH => S.lemma_14_5_21_two h1413 hH

end Main

end CFSG.Quasithin
