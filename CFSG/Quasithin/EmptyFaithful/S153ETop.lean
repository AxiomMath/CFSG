module

public import CFSG.Quasithin.EmptyFaithful.S153EFinal
public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.Quasithin.EmptyFaithful.S153E52H
public import CFSG.Quasithin.EmptyFaithful.S153E54M
public import CFSG.Quasithin.EmptyFaithful.S153E55G
public import CFSG.Quasithin.EmptyFaithful.S153E56Z
public import CFSG.Quasithin.EmptyFaithful.S153E58T
public import CFSG.Quasithin.EmptyFaithful.S153NineB
public import CFSG.Quasithin.EmptyFaithful.S153EB6O
public import CFSG.Quasithin.EmptyFaithful.S153EN8N
public import CFSG.Quasithin.EmptyFaithful.S153EH60F
public import CFSG.Quasithin.EmptyFaithful.S153EO61D
public import CFSG.Quasithin.EmptyFaithful.S153E61Z
public import CFSG.Quasithin.EmptyFaithful.S153E51C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S153E

theorem false_of_nonabelian (h113 : StageLemma14113) (h09 : Input15309Two) (hG64 : G64.LemmaG64)
    (i56 : Input15356J) (i58G93 : Input15358G93)
    {G : Type} [Group G]
    [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G} (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hn : NonabelianVH153 T M Mc) : False := by
  have h51 := lemma_15_3_51 cx hn
  have h52 := lemma_15_3_52 h113 h09 (input15352_of_lemmaG64 hG64) cx h51
  obtain ⟨N₁, N₂, h53one⟩ := lemma_15_3_53_one h113 cx h51 h52
  have h53two := lemma_15_3_53_two cx h51 h52
  have c53 : Chain15353 cx N₁ N₂ := ⟨hn, h51, h52, h53one, h53two⟩
  obtain ⟨g, hgY, hgZ⟩ := exists_15_3_54 h113 cx c53
  obtain ⟨s, h54⟩ := lemma_15_3_54 h113 cx c53 hgY hgZ
  have c54 : Chain15354 cx N₁ N₂ g s := { c53 with hg := hgY, hgZ := hgZ, h54 := h54 }
  have c55 : Chain15355 cx N₁ N₂ g s :=
    { c54 with h55 := lemma_15_3_55 h113 cx c54 }
  obtain ⟨y, t₁, hy, ht₁⟩ := exists_y_t₁ h113 cx c55
  have hJ := i56 G T Mc M V₁ V₂ t cx N₁ N₂ g s c55 y hy
  have h56 := lemma_15_3_56 h113 cx c55 hy ht₁ hJ
  have c56 : Chain15356 cx N₁ N₂ g s y t₁ := { c55 with hy := hy, ht₁ := ht₁, h56 := h56 }
  have c57 : Chain15357 cx N₁ N₂ g s y t₁ :=
    { c56 with h57 := lemma_15_3_57 cx c56 }
  have c58 : Chain15358 cx N₁ N₂ g s y t₁ :=
    { c57 with h58 := lemma_15_3_58 h09 (input15358Two_of_lemmaG64 hG64) i58G93 cx c57 }
  have hD : S153E61.Data61 cx :=
    S153E61.data61_of_core58 h09 (input15358Two_of_lemmaG64 hG64) i58G93 cx c57
  have c59 : Chain15359 cx N₁ N₂ g s y t₁ :=
    { c58 with h59 := { one := S153E59.eq_pCoreOf_Mc cx h113 c58,
                        two := S153E59.isSylowTwoOf_TK cx h113 c58,
                        three := S153E59.relIndex_TK cx h113 c58,
                        four := S153E59.eq_YT cx h113 c58 } }
  obtain ⟨DM, JM, v, z, hN8⟩ := lemma_n8 h113 cx c59
  obtain ⟨t₂, ht₂, hord, hV⟩ := hN8.exists_involution
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨DH, -, hDHle, hDH2, hDHi⟩ :=
    exists_sylow_ge (p := 3) (Q := (⊥ : Subgroup G)) (K := Mc)
      (IsPGroup.of_card (p := 3) (n := 0) (by simp)) bot_le
  have hDH : IsSylowThreeOf153 DH Mc := ⟨hDHle, hDH2, hDHi⟩
  obtain ⟨hDHc, hDHsyl⟩ := lemma_60H cx c59 hDH
  have h60 := lemma_15_3_60 cx c59.h51 c59.h52 hN8 hDH hDHc hDHsyl
  have hUCT := h60.two_UCT t₂ ht₂ hord hV
  have hcent := lemma_61one cx c59 hDH ht₂.1 hord hUCT
  have h61one := lemma_15_3_61_one cx hN8 hDH hDHc h60.one hcent
  exact false_of_closing cx c59.h59 ht₂.1 hord hUCT (h60.two_z t₂ ht₂ hord hV) h61one
    (lemma_61two cx hD c59 hN8)

end S153E

theorem stage15350_of_named_inputs
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hG64 : G64.LemmaG64) (i56 : Input15356J) (i58G93 : Input15358G93) : Stage15350 := by
  have h09 : Input15309Two := fun _ _ _ _ _ _ h => Hyp153.VZ_lt_pCoreOf_Y153 h113 h
  intro G _ _ T Mc M V₁ V₂ t c r45 r46 r47 r49 hF H hH a ha b hb
  by_contra hne
  have hHMc : H ≤ Mc := C1Pack153.le_mc_of_isHTM153 h11 c.hyp hH
  have hnab : NonabelianVH153 T M Mc :=
    ⟨a, conjClosure_mono le_rfl hHMc ha, b, conjClosure_mono le_rfl hHMc hb, hne⟩
  exact S153E.false_of_nonabelian h113 h09 hG64 i56 i58G93
    ⟨c, r45, r46, r47, r49, hF Mc (isHTM153_mc c)⟩ hnab

end CFSG.Quasithin
