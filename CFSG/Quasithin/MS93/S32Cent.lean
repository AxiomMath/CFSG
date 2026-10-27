module

public import CFSG.Quasithin.MS93.SkHyp
public import CFSG.Quasithin.MS93.Sec2Two
public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G]

section Perfect

theorem eq_top_of_perfect_of_two {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (D : Subgroup L) [D.Normal] (h2 : ∀ l : L, ∃ d ∈ D, ∃ e : ℕ, (d⁻¹ * l) ^ 2 ^ e = 1) :
    D = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine QuotientGroup.subgroup_eq_top_of_subsingleton D ?_
  have hp : IsPGroup 2 (L ⧸ D) := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨d, hd, e, he⟩ := h2 l
    refine ⟨e, ?_⟩
    have hq : (QuotientGroup.mk l : L ⧸ D) = QuotientGroup.mk (d⁻¹ * l) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (D.inv_mem hd), one_mul]
    rw [hq, ← QuotientGroup.mk_pow, he, QuotientGroup.mk_one]
  rcases subsingleton_or_nontrivial (L ⧸ D) with hs | hs
  · exact hs
  · exact absurd hp.isNilpotent (Group.IsPerfect.not_isNilpotent (L ⧸ D))

end Perfect

section Commutator

variable {M T L : Subgroup G}

theorem isPGroup_pCore_two [Finite G] (L : Subgroup G) : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCore_isPGroup 2

theorem mem_pCoreOf_of_mem_pCore_two {L : Subgroup G} {o : ↥L} (ho : o ∈ CFSG.pCore 2 ↥L) :
    (o : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff o).mpr ho

theorem le_normalizer_pCoreOf_of_le_normalizer {M L : Subgroup G}
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
  hLn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

theorem PUHyp.commutator_inf_le_pCoreOf [Finite G] (h : PUHyp M T L) {N : Subgroup G}
    (hNn : M ≤ Subgroup.normalizer (N : Set G)) (hLN : ¬ L ≤ N) : ⁅N ⊓ L, L⁆ ≤ pCoreOf 2 L := by
  set D : Subgroup ↥L := N.subgroupOf L with hD
  have hDn : D.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hD, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hNn (h.L_le g.2)) n).mp hn
    simpa using this
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hHn : (D.map π).Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple h.quasisimple (D.map π)
    with hc | htop
  · rw [Subgroup.commutator_le]
    intro x hx l hl
    have hxD : (⟨x, hx.2⟩ : ↥L) ∈ D := by
      rw [hD, Subgroup.mem_subgroupOf]
      exact hx.1
    have hcen := hc (Subgroup.mem_map_of_mem π hxD)
    have hk : π ⁅(⟨x, hx.2⟩ : ↥L), (⟨l, hl⟩ : ↥L)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcen _).symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact mem_pCoreOf_of_mem_pCore_two hk
  · exfalso
    apply hLN
    have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
    have htopD : D = ⊤ := by
      refine eq_top_of_perfect_of_two D fun l => ?_
      have hl : π l ∈ D.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨d, hd, hdl⟩ := hl
      refine ⟨d, hd, ?_⟩
      have hmem : d⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdl
        exact hdl
      obtain ⟨e, he⟩ := isPGroup_pCore_two L ⟨d⁻¹ * l, hmem⟩
      exact ⟨e, congrArg Subtype.val he⟩
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ D := by rw [htopD]; exact Subgroup.mem_top _
    rw [hD, Subgroup.mem_subgroupOf] at this
    exact this

theorem PUHyp.commutator_le_pCoreOf_of_not_le [Finite G] (h : PUHyp M T L) {N : Subgroup G}
    (hNM : N ≤ M) (hNn : M ≤ Subgroup.normalizer (N : Set G)) (hLN : ¬ L ≤ N) :
    ⁅N, L⁆ ≤ pCoreOf 2 L := by
  have hP : M ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    le_normalizer_pCoreOf_of_le_normalizer h.le_normalizer
  have hNL : ⁅N, L⁆ ≤ N ⊓ L :=
    le_inf (commutator_le_left_of_le_normalizer (h.L_le.trans hNn))
      (by rw [Subgroup.commutator_comm]
          exact commutator_le_left_of_le_normalizer (hNM.trans h.le_normalizer))
  have h1 : ⁅⁅N, L⁆, L⁆ ≤ pCoreOf 2 L :=
    (Subgroup.commutator_mono hNL le_rfl).trans (h.commutator_inf_le_pCoreOf hNn hLN)
  have h2 : ⁅⁅L, N⁆, L⁆ ≤ pCoreOf 2 L := by rwa [Subgroup.commutator_comm L N]
  have h3 : ⁅⁅L, L⁆, N⁆ ≤ pCoreOf 2 L :=
    three_subgroups_le (h.L_le.trans hP) (h.L_le.trans hP) (hNM.trans hP) h2 h1
  rwa [h.perfect, Subgroup.commutator_comm] at h3

theorem PUHyp.commutator_le_pCoreOf_M [Finite G] (h : PUHyp M T L) {N : Subgroup G} (hNM : N ≤ M)
    (hNn : M ≤ Subgroup.normalizer (N : Set G)) (hLN : ¬ L ≤ N) : ⁅N, L⁆ ≤ pCoreOf 2 M :=
  (h.commutator_le_pCoreOf_of_not_le hNM hNn hLN).trans
    (pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer)

end Commutator

section Centralizer

variable {M T L : Subgroup G}

theorem omegaOneCenterOf_le_Z0q (M T : Subgroup G) (hTM : T ≤ M) :
    omegaOneCenterOf T ≤ Z0q M T :=
  le_normalClosureIn ((PU.omegaOneCenterOf_le T).trans hTM)

variable [Finite G]

theorem PUHyp.pCoreOf_le_centralizer_Z0q (h : PUHyp M T L) :
    pCoreOf 2 M ≤ Subgroup.centralizer (Z0q M T : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  refine h.Z0q_le_Xq.trans ((PU.omegaOneCenterOf_le_centerOf _).trans ?_)
  exact inf_le_right

theorem PUHyp.not_le_centralizer_Z0q (h : PUHyp M T L) :
    ¬ L ≤ Subgroup.centralizer (Z0q M T : Set G) := by
  intro hL
  have hLΩ : L ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G) :=
    hL.trans (Subgroup.centralizer_le (omegaOneCenterOf_le_Z0q M T h.le))
  have hTΩ : T ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact (PU.omegaOneCenterOf_le_centerOf T).trans inf_le_right
  have hM : M ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G) := by
    rw [h.eq_sup]
    exact sup_le hLΩ hTΩ
  exact h.noChar _ (PU.omegaOneCenterOf_le T) (PU.omegaOneCenterOf_ne_bot h.isPGroup h.ne_bot)
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T)
    (hM.trans (Subgroup.centralizer_le_normalizer _))

theorem PUHyp.commutator_Cq_le (h : PUHyp M T L) : ⁅Cq M T, L⁆ ≤ pCoreOf 2 M :=
  h.commutator_le_pCoreOf_M Cq_le le_normalizer_Cq fun hL =>
    h.not_le_centralizer_Z0q (hL.trans inf_le_right)

theorem PUHyp.centralizer_Z0q (h : PUHyp M T L) :
    T ⊓ Subgroup.centralizer (Z0q M T : Set G) = pCoreOf 2 M := by
  refine le_antisymm ?_ (le_inf h.pCore_le h.pCoreOf_le_centralizer_Z0q)
  set C := T ⊓ Subgroup.centralizer (Z0q M T : Set G) with hC
  have hCM : C ≤ M := inf_le_left.trans h.le
  have hCcomm : ⁅C, L⁆ ≤ pCoreOf 2 M :=
    (Subgroup.commutator_mono (le_inf hCM inf_le_right) le_rfl).trans h.commutator_Cq_le
  have hcent : M ≤ Subgroup.normalizer (Subgroup.centralizer (Z0q M T : Set G) : Set G) :=
    le_normalizer_centralizer (le_normalizer_Z0q M T)
  have hTn : T ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (h.le.trans hcent)
  have hLn : L ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    have key : ∀ g ∈ L, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      have hgc : g * c * g⁻¹ * c⁻¹ ∈ pCoreOf 2 M := by
        have := Subgroup.commutator_mem_commutator hc hg
        have h' := (pCoreOf 2 M).inv_mem (hCcomm this)
        simpa [commutatorElement_def, mul_assoc] using h'
      have hgcC : g * c * g⁻¹ ∈ Subgroup.centralizer (Z0q M T : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (hcent (h.L_le hg)) c).mp hc.2
      refine ⟨?_, hgcC⟩
      have e : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
      rw [e]
      exact T.mul_mem (h.pCore_le hgc) hc.1
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key l hl c, fun hc => ?_⟩
    have := key l⁻¹ (L.inv_mem hl) _ hc
    simpa [mul_assoc] using this
  have hMn : M ≤ Subgroup.normalizer (C : Set G) := by
    rw [h.eq_sup]
    exact sup_le hLn hTn
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCM hMn
    (h.isPGroup.to_le inf_le_left)

theorem PUHyp.centHyp (h : PUHyp M T L) : CentHyp (puAmalgam h.le) := by
  refine centHyp_of_edge (puAmalgam h.le) (PU.isMVtx_baseA _) (adj_baseA_baseB _) ?_
  rw [puAmalgam.qv_baseB, puAmalgam.zm_baseA, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup
    h.pCore_le, ← imM_inf_centralizer h.le T (Z0q_le M T), h.centralizer_Z0q]

end Centralizer

end CFSG.Quasithin.MS93
