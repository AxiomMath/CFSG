module

public import CFSG.Quasithin.EmptyFaithful.T1521SFam
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Nc
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Cen
public import CFSG.Quasithin.EmptyFaithful.T1521SA5U3Wr
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAInv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.U31521
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem isComponentIn_of_isComponentOf_u3 {L X : Subgroup G} (h : IsComponentOf L X) :
    IsComponentIn L X := by
  have h1 := CFSG.Assembly.isComponentOf_iff_open.mpr h
  exact ⟨h.1, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).1
    h1⟩

variable [Finite G]

theorem commutator_conjByElt_eq_bot_u3 {X L : Subgroup G} {t : G} (hc : IsComponentOf L X)
    (htX : t ∈ X) (htn : t ∉ Subgroup.normalizer (L : Set G)) : ⁅L, conjByElt t L⁆ = ⊥ := by
  have hL := isComponentIn_of_isComponentOf_u3 hc
  have hL' : IsComponentIn (conjByElt t L) X := Unc25G2.isComponentIn_map_conj hL htX
  refine (BenderBranch.eq_or_commute_of_isComponentIn hL hL').resolve_left fun h => htn ?_
  exact GoldMLA.mem_normalizer_of_conjByElt_eq h.symm

theorem nrm1521U3_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    Nrm1521U3 := by
  intro G _ _ X S L hStd hco _ ⟨n, hn, hL⟩
  have horb := a3Orbits_of_a37_a38 (G := G) h37 h38 X S L hStd.sqtk hStd.sylow hStd.comp
  have hS2 : IsPGroup 2 ↥S := hStd.sylow.2.1
  rcases horb.2 with hnorm | ⟨t, htS, htN, hpair, -, -, -⟩
  · obtain ⟨B₀, h1, h2, h3, h4⟩ := nc1521U3 hn hL hStd.sylowL hS2 hnorm
    exact ⟨B₀, h1.trans le_conjJoin, h2, h3, fun v hvS _ hvc l hl => h4 v hvS hvc l hl⟩
  · set S₀ : Subgroup G := S ⊓ Subgroup.normalizer (L : Set G) with hS₀
    have hS₀L : S₀ ⊓ L = S ⊓ L := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, Subgroup.le_normalizer hx.2⟩, hx.2⟩⟩
    have hSyl₀ : IsSylowTwoOf (S₀ ⊓ L) L := by
      rw [hS₀L]
      exact hStd.sylowL
    have hS₀2 : IsPGroup 2 ↥S₀ := hS2.to_inf_left
    obtain ⟨Z, hZR, hZea, hZcard, hiff⟩ := exists_center_u3 hn hL hStd.sylowL
    have hq : 3 ≤ 2 ^ n := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hcomm : ⁅L, conjByElt t L⁆ = ⊥ := commutator_conjByElt_eq_bot_u3 hco (hStd.sylow.1 htS) htN
    have hJ : thompsonJ S = thompsonJ S₀ :=
      thompsonJ_eq_inf_normalizer_of_wreath_center hq hZR hZea hZcard
        (fun z hz hc => eq_one_of_central_u3 hn hL hz (fun y hy => (hc y hy).symm))
        (fun g hgL hgR hg2 z hz => centralizes_center_of_sq_mem_centralizer hn hL hStd.sylowL hgL
          hgR hg2 ((hiff z).1 hz).1 ((hiff z).1 hz).2) hpair hcomm
    obtain ⟨B₀, h1, h2, h3, h4⟩ := nc1521U3 hn hL hSyl₀ hS₀2 inf_le_right
    rw [hS₀L] at h1
    exact ⟨B₀, h1.trans le_conjJoin, by rw [hJ]; exact h2, h3,
      fun v hvS hvN hvc l hl => h4 v ⟨hvS, hvN⟩ hvc l hl⟩

end CFSG.Quasithin
