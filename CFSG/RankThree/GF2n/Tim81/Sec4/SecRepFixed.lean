module

public import CFSG.RankThree.GF2n.Tim81.Sec4.SecRep
public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjH

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.QuotMod
open scoped commutatorElement

variable {G : Type} [Group G] {V H : Subgroup G} {N N₀ : Subgroup G}

namespace SecRepFixed

theorem commutator_mem (hs : QuotMod.Hyp H N N₀) (z : ↥H) (n : ↥N) :
    ⁅(n : G), (z : G)⁆ ∈ N := by
  have h1 : (z : G) * (n : G)⁻¹ * (z : G)⁻¹ ∈ N :=
    hs.conj z z.2 (n : G)⁻¹ (N.inv_mem n.2)
  have h2 : (n : G) * ((z : G) * (n : G)⁻¹ * (z : G)⁻¹) ∈ N :=
    N.mul_mem n.2 h1
  rwa [show (n : G) * ((z : G) * (n : G)⁻¹ * (z : G)⁻¹) =
    ⁅(n : G), (z : G)⁆ by rw [commutatorElement_def]; group] at h2

variable [(N₀.subgroupOf N).Normal] (hs : QuotMod.Hyp H N N₀)
variable [Module (ZMod 2) (SecMod hs)]
variable {X : Type} [Group X] (ψ : HBar V H ≃* X)
variable (hKsec : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀)

theorem repSec_sub_eq_mk (z : ↥H) (n : ↥N) :
    repSec hs hKsec X ψ (ψ (piK V H z)) (SecMod.mk hs n) - SecMod.mk hs n =
      SecMod.mk hs ⟨⁅(n : G), (z : G)⁆⁻¹,
        N.inv_mem (commutator_mem hs z n)⟩ := by
  rw [repSec_apply_piK_mk hs hKsec X ψ z n, sub_eq_add_neg, ← SecMod.mk_inv hs,
    ← SecMod.mk_mul hs]
  refine congrArg (SecMod.mk hs) (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
  group

theorem fixed_iff_commutator_mem (z : ↥H) (n : ↥N) :
    repSec hs hKsec X ψ (ψ (piK V H z)) (SecMod.mk hs n) = SecMod.mk hs n ↔
      ⁅(n : G), (z : G)⁆ ∈ N₀ := by
  have hsub : repSec hs hKsec X ψ (ψ (piK V H z)) (SecMod.mk hs n) = SecMod.mk hs n ↔
      repSec hs hKsec X ψ (ψ (piK V H z)) (SecMod.mk hs n) -
        SecMod.mk hs n = 0 := sub_eq_zero.symm
  rw [hsub, repSec_sub_eq_mk (N := N) (N₀ := N₀) hs ψ hKsec z n,
    SecMod.mk_eq_zero_iff, N₀.inv_mem_iff]

theorem mk_mem_subSec_of_mem {E : Subgroup G} {n : ↥N} (hn : (n : G) ∈ E) :
    SecMod.mk hs n ∈ subSec hs E :=
  (mem_subSec_iff hs).2 ⟨⟨n, ⟨hn, n.2⟩⟩, congrArg (SecMod.mk hs) (Subtype.ext rfl)⟩

end SecRepFixed

namespace RootHyp

open CFSG.CGT.Timmesfeld75

variable {M : Subgroup G} {h₀ : G}
variable [Finite G]

theorem exists_mem_Pc_not_mem_kOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    ∃ x ∈ Pc M V, x ∉ kOf V H := by
  by_contra hcon
  push Not at hcon
  have hbot : imgK V H (Pc M V) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨z, hzP, rfl⟩ := (mem_imgK_iff).mp hy
    exact Subgroup.mem_bot.mpr ((piK_eq_one_iff z).mpr (hcon z hzP))
  exact (imgK_ne_bot_and_ne_of_sup h hPH hH hnM).1 hbot

theorem exists_mem_conj_not_mem_kOf (h : RootHyp M V) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    ∃ y ∈ conjSubgroup h₀ (Pc M V), y ∉ kOf V H := by
  by_contra hcon
  push Not at hcon
  have hK_le_C : kOf V H ≤ Subgroup.centralizer (V : Set G) := by
    have h := kOf_le_centralizer_conjSubgroup_of_mem (V := V) (H := H) (y := 1) H.one_mem
    rwa [conjSubgroup_one] at h
  have hH_le_C : H ≤ Subgroup.centralizer (V : Set G) := by
    rw [hH]
    exact sup_le (inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G))
      (fun y hy => hK_le_C (hcon y hy))
  have hCVleM : Subgroup.centralizer (V : Set G) ≤ M := by
    obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.toHyp.ne_bot
    have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    intro c hc
    have hcv : c * v = v * c := (Subgroup.mem_centralizer_iff.mp hc v hvV).symm
    exact h.toHyp.centralizer_le_M hvV hv1'
      (Subgroup.mem_centralizer_singleton_iff.mpr hcv)
  exact hnM (hH_le_C.trans hCVleM)

end RootHyp

end CFSG.RankThree.GF2n.Tim81
