module

public import CFSG.Quasithin.EmptyFaithful.S14610Q4
public import CFSG.Quasithin.EmptyFaithful.ModA7Core
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

section A7Fixed

variable {G : Type} [Group G] [Finite G]

private theorem card_eq_168_of_isPSL_three_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

private theorem wOf1469_eq_blockU_of_short {K : Subgroup G} (hK : IsShort2 K) :
    wOf1469 K = blockU K := by
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hK.2.2.1.1
  apply le_antisymm
  · have hA : omegaOneCenterOf (pCoreOf 2 K) ≤ pCoreOf 2 K :=
      (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1)
    exact Subgroup.commutator_mono hA le_rfl
  · have hUA : blockU K ≤ omegaOneCenterOf (pCoreOf 2 K) := fun x hx =>
      Subgroup.subset_closure ⟨hUQ hx, hK.2.2.1.2 x hx⟩
    calc blockU K = ⁅blockU K, K⁆ := (C1.commutator_blockU hK).symm
      _ ≤ ⁅omegaOneCenterOf (pCoreOf 2 K), K⁆ := Subgroup.commutator_mono hUA le_rfl

private theorem inf_centralizer_eq_bot_of_alt7 (K V : Subgroup G) [IsMulCommutative ↥V]
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, K⁆ = V)
    (hsq : ∀ v ∈ V, v ^ 2 = 1) (hcard : Nat.card V = 64)
    (hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) :
    V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have hne : ¬ K ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    have hbot : ⁅V, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
    rw [hcomm] at hbot
    rw [hbot] at hcard
    simp at hcard
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eA⟩ := H13.nonempty_autOn_mulEquiv_of_simple hKV hO2 hne e
  have hc' := H13.commV_autOn_eq_top hKV hcomm
  have hsq' : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hsq w w.2)
  let ρ : alternatingGroup (Fin 7) →* MulAut ↥V :=
    (autOn K V).subtype.comp eA.symm.toMonoidHom
  have hρ : ρ.range = autOn K V := by
    ext a
    constructor
    · rintro ⟨σ, rfl⟩
      exact (eA.symm σ).2
    · intro ha
      exact ⟨eA ⟨a, ha⟩, by simp [ρ]⟩
  have hfix := ModA7.fixV_eq_bot_of_a7 hsq' hcard ρ (by rw [hρ]; exact hc')
  rw [hρ] at hfix
  exact (H13.fixV_autOn_eq_bot_iff hKV).mp hfix

end A7Fixed

theorem input14610PermA7Fixed_holds : Input14610PermA7Fixed := by
  intro G _ _ T M H u I I₂ K _ hK hA hW
  have hblock : IsBlock2 I K := by
    rcases hK.shape with ⟨hL32, -⟩ | ⟨hb, -⟩
    · exfalso
      obtain ⟨e⟩ := hA
      have h1 : Nat.card (OTwoQuot K) = 2520 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        simp [Nat.factorial]
      have h2 : Nat.card (OTwoQuot K) = 168 := card_eq_168_of_isPSL_three_two hL32
      omega
    · exact hb
  have hshort : IsShort2 K := hblock.1
  rw [wOf1469_eq_blockU_of_short hshort] at hW ⊢
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hshort.2.2.1.1
  have hUQ' : blockU K ≤ blockQ K := hUQ.trans inf_le_left
  have hcomm' : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hUQ ha).2) b (hUQ' hb)).symm
  have : IsMulCommutative ↥(blockU K) := ⟨⟨fun a b => Subtype.ext (hcomm' a a.2 b b.2)⟩⟩
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (blockU K : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (hUQ hu).2) q hq).symm
  obtain ⟨e⟩ := hA
  exact inf_centralizer_eq_bot_of_alt7 K (blockU K) (C1.le_normalizer_blockU K)
    (C1.commutator_blockU hshort) (fun v hv => hshort.2.2.1.2 v hv) (by rw [hW]; norm_num) hO2
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e)

end CFSG.Quasithin
