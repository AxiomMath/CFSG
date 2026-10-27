module

public import CFSG.Quasithin.Background.E6Gamma
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M V U U₀ : Subgroup G}

theorem exists_cComp_of_le (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h : HypE61 T M V) (hU₀Γ : U₀ ∈ gammaE64 V M) (hU₀U : U₀ ≤ U) (hUV : U ≤ V) {L : Subgroup G}
    (hL : L ∈ cComp (Subgroup.centralizer (U : Set G))) :
    ∃ X ∈ cComp (Subgroup.centralizer (U₀ : Set G)), L ≤ X := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQH₀ : IsSylowTwoOf Q (Subgroup.centralizer (U₀ : Set G)) := e6_5_one h hU₀Γ
  have hQU : Q ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hUV)
  have hLfam : L ∈ lFamily Q := cComp_subset_lFamily hQU hL
  have hLH₀ : L ≤ Subgroup.centralizer (U₀ : Set G) :=
    (le_of_mem_cComp hL).trans (Subgroup.centralizer_le hU₀U)
  have hU₀V : U₀ ≤ V := hU₀U.trans hUV
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hpc : pCoreOf 2 (Subgroup.centralizer (U₀ : Set G)) ≠ ⊥ := by
    intro h0
    apply hU₀Γ.2.1
    refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_ (Subgroup.centralizer_le_normalizer _)
      (h.isPGroup_V.to_le hU₀V))
    exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hU₀V hw') _ (hU₀V hw)
  exact Vol2Native.lemma_1_2_4_exists hq.1 h37 h39 hpc hQH₀ hLH₀ hLfam

end E6

end CFSG.Quasithin
