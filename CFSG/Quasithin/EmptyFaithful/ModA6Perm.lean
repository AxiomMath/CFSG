module

public import CFSG.Quasithin.EmptyFaithful.S14610Q3
public import CFSG.Quasithin.EmptyFaithful.ModA6Core
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6
open scoped commutatorElement IsMulCommutative

section PermFixed

variable {G : Type} [Group G] [Finite G]

private theorem card_isPSL_three_two_of {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

private theorem card_alternating_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem wOf1469_eq_blockU {K : Subgroup G} (hK : IsShort2 K) : wOf1469 K = blockU K := by
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hK.2.2.1.1
  apply le_antisymm
  · have hA : omegaOneCenterOf (pCoreOf 2 K) ≤ pCoreOf 2 K :=
      (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1)
    exact Subgroup.commutator_mono hA le_rfl
  · have hUA : blockU K ≤ omegaOneCenterOf (pCoreOf 2 K) := fun x hx =>
      Subgroup.subset_closure ⟨hUQ hx, hK.2.2.1.2 x hx⟩
    calc blockU K = ⁅blockU K, K⁆ := (C1.commutator_blockU hK).symm
      _ ≤ ⁅omegaOneCenterOf (pCoreOf 2 K), K⁆ := Subgroup.commutator_mono hUA le_rfl

private theorem exists_fixed_of_alt6 (K V : Subgroup G) [IsMulCommutative ↥V]
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, K⁆ = V)
    (hsq : ∀ v ∈ V, v ^ 2 = 1) (hcard : Nat.card V = 32)
    (hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) :
    V ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
  have hne : ¬ K ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    have hbot : ⁅V, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
    rw [hcomm] at hbot
    rw [hbot] at hcard
    simp at hcard
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eA⟩ := H13.nonempty_autOn_mulEquiv_of_simple hKV hO2 hne e
  have hc' := H13.commV_autOn_eq_top hKV hcomm
  have hsq' : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hsq w w.2)
  obtain ⟨Φ, hΦ⟩ := ModA6.exists_core_equiv hsq' hcard (autOn K V) ⟨eA⟩ hc'
  let c₀ : ↥V := Φ.symm ⟨G6.allOnes 6, allOnes_mem_core⟩
  have hΦc : Φ c₀ = ⟨G6.allOnes 6, allOnes_mem_core⟩ := Φ.apply_symm_apply _
  have hfixc : c₀ ∈ fixV (autOn K V) := by
    intro g hg
    obtain ⟨σ, hσ, hσg⟩ := (hΦ g).mp hg
    apply Φ.injective
    rw [hσg c₀, hΦc]
    exact Subtype.ext (CFSG.Quasithin.H13.A6.permAct_allOnes σ)
  rw [H13.fixV_autOn_eq hKV] at hfixc
  intro hbot
  have hmem : (c₀ : G) ∈ V ⊓ Subgroup.centralizer (K : Set G) :=
    ⟨c₀.2, Subgroup.mem_subgroupOf.mp hfixc⟩
  rw [hbot] at hmem
  have h1 : c₀ = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
  have h2 : Φ c₀ = 1 := by rw [h1, map_one]
  rw [hΦc] at h2
  exact allOnes_ne_one (congrArg Subtype.val h2)

end PermFixed

theorem input14610PermFixedA6_holds : Input14610PermFixedA6 := by
  intro G _ _ T M H u I I₂ K _ hK hA hW
  have hblock : IsBlock2 I K := by
    rcases hK.shape with ⟨hL32, -⟩ | ⟨hb, -⟩
    · exfalso
      obtain ⟨e⟩ := hA
      have h1 : Nat.card (OTwoQuot K) = 360 := by
        rw [Nat.card_congr e.toEquiv, card_alternating_six]
      have h2 : Nat.card (OTwoQuot K) = 168 := card_isPSL_three_two_of hL32
      omega
    · exact hb
  have hshort : IsShort2 K := hblock.1
  rw [wOf1469_eq_blockU hshort] at hW ⊢
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hshort.2.2.1.1
  have hUQ' : blockU K ≤ blockQ K := hUQ.trans inf_le_left
  have hcomm' : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hUQ ha).2) b (hUQ' hb)).symm
  have : IsMulCommutative ↥(blockU K) := ⟨⟨fun a b => Subtype.ext (hcomm' a a.2 b b.2)⟩⟩
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (blockU K : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (hUQ hu).2) q hq).symm
  obtain ⟨e⟩ := hA
  exact exists_fixed_of_alt6 K (blockU K) (C1.le_normalizer_blockU K) (C1.commutator_blockU hshort)
    (fun v hv => hshort.2.2.1.2 v hv) (by rw [hW]; norm_num) hO2
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e)

end CFSG.Quasithin
