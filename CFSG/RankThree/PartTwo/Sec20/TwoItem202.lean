module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec19.Item1922Full
import CFSG.RankThree.PartTwo.Sec19.Item1923Uniq
import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofStep202J
import CFSG.RankThree.PartTwo.Sec19.KF1923Small

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem facts1922_of_item1912
    (h1912 : Item1912) : Item1922Facts := by
  intro G _ _ A M N L c h hc
  obtain ⟨hnorm, hNeq, ⟨c₀, hc₀3, hc₀, hA⟩, hsyl, h9, homega, hsup, hLM, hO2, hB⟩ :=
    item1922Full_of_item1912 h1912 G A M N L h
  have hz : Subgroup.zpowers c = Subgroup.zpowers c₀ :=
    SetLike.coe_injective (hc.symm.trans hc₀)
  have h3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers, hz, Nat.card_zpowers, hc₀3]
  exact
    { centralizer_eq := hc
      orderOf_c := h3
      normal := hnorm
      normalizer_eq := hNeq
      eq_sup := by rw [hz]; exact hA
      sylow := hsyl
      card := h9
      omega := homega
      sup_inf_eq := hsup
      not_le_M := hLM
      pCoreOf_le_M := hO2
      normalizer_le_M := hB }


theorem item202Two_of (h1912 : Item1912) (h194 : Sec19.Item194UsedWide3) (h1923 : Item1923) :
    ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G),
      Hyp201 G A M L N c → Hyp1921 G A M N L →
        scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G) = {M} := by
  intro G _ _ A M L N c h hyp
  have hE : IsE27 A := isE27_of_mem_partTwoE hyp.mem_partTwoE
  have hF : Facts1922 G A M N L c := facts1922_of_item1912 h1912 G A M N L c hyp h.centralizer_eq
  obtain ⟨K, hK⟩ := (h194 G hyp.toSec19Std A M N hE hyp.mem_scriptM hyp.mem_scriptM_N hyp.ne).1
  obtain ⟨-, h2, -, -, hcK, hAK, -, hKeq, -⟩ := h1923 G A M N L c hyp h.centralizer_eq K hK
  have huniq : ∀ K' ∈ oTwoComponentsIn M, 3 ∣ Nat.card K' → K' = kTwenty M c := by
    intro K' hK' h3
    rw [item1923_uniqueness kf6_holds hyp hF hK h2 hcK hAK hK' h3, hKeq]
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 h
  have hAM : A ≤ M := le_of_hyp201 h
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨h.mem_scriptM.1, ?_⟩, ?_⟩
  · intro x hx
    exact sup_le hAM hKM hx
  · intro X hX
    by_contra hXM
    have hXA : X ∈ scriptM (A : Set G) := ⟨hX.1, fun a ha => hX.2 (Subgroup.mem_sup_left ha)⟩
    obtain ⟨⟨K₀, hK₀⟩, hlist⟩ := h194 G hyp.toSec19Std A M X hE hyp.mem_scriptM hXA hXM
    have h3 : 3 ∣ Nat.card K₀ :=
      (Sec19.Item19Res5Proof.three_dvd_card_of_wide (hlist K₀ hK₀).1).trans
        (Subgroup.card_quotient_dvd_card _)
    have hK₀X : ¬ K₀ ≤ X := hK₀.2
    rw [huniq K₀ hK₀.1 h3] at hK₀X
    exact hK₀X fun k hk => hX.2 (Subgroup.mem_sup_right hk)

end CFSG.RankThree.PartTwo.Sec20
