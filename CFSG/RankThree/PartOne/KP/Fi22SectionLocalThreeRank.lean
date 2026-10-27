module

public import CFSG.RankThree.Coprime.LocalPrimeSectionCover
public import CFSG.RankThree.PartOne.KP.Fi22Section

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.Coprime

theorem four_le_twoLocalPrimeRank_three_of_section_fi22
    {G : Type} [Group G] [Finite G] (H : Subgroup G) (K : Subgroup H) [K.Normal]
    (e : (↥H ⧸ K) ≃* Carrier .Fi22) : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  have hle : CFSG.Open.twoLocalPrimeRank 3 G ≤ 3 := by omega
  let q : H →* CFSG.Sporadic.Fi22.J :=
    { toFun := fun h => (e.trans CFSG.Sporadic.Fi22.fi22EquivJ) (QuotientGroup.mk' K h)
      map_one' := by simp
      map_mul' := by intro x y; simp }
  have hq : Function.Surjective q := by
    intro j
    obtain ⟨x, hx⟩ := (e.trans CFSG.Sporadic.Fi22.fi22EquivJ).surjective j
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective K x
    exact ⟨h, hx⟩
  obtain ⟨E, hE, hEc⟩ :=
    CFSG.RankThree.Native.Fi22U.R3E_Fi22_unitary_quotient_elementary_two_rank_nine
  obtain ⟨hE', hEc'⟩ := isElementaryAbelian_map_mulEquiv
    CFSG.RankThree.Native.Fi22U.fi22UnitaryEquiv.symm hE
  obtain ⟨U, hU, hUc⟩ := exists_elementary_two_five _ hE' (hEc'.trans hEc)
  let isoM := CFSG.Sporadic.Fi22.caQuotEquiv.trans statedProjEquivT46.symm
  obtain ⟨hU', hUc'⟩ := isElementaryAbelian_map_mulEquiv isoM.symm hU
  have hS : ∃ U' : Subgroup (CFSG.Sporadic.Fi22.Ca ⧸
      Subgroup.center CFSG.Sporadic.Fi22.Ca), IsElementaryAbelian 2 U' ∧
      Nat.card U' = 2 ^ (3 + 2) :=
    ⟨_, hU', hUc'.trans hUc⟩
  obtain ⟨H₁, π, -, hπ⟩ := exists_surjective_map_comap H q hq CFSG.Sporadic.Fi22.Ca
  obtain ⟨Y, _, _, hYp, φ, hφs, hφZ, hYrank⟩ :=
    exists_central_cover_of_even_center_of_twoLocalPrimeRank_le 3 (r := 3) (by norm_num) hle
      isQuasisimple_Fi22_Ca (by rw [CFSG.Sporadic.Fi22.card_center_Ca]; exact even_two)
      hS H₁ π hπ
  let f := isoM.toMonoidHom.comp φ
  have hf : Function.Surjective f := isoM.surjective.comp hφs
  have hfk : f.ker ≤ Subgroup.center Y := by
    intro y hy
    apply hφZ
    rw [MonoidHom.mem_ker] at hy ⊢
    change isoM (φ y) = 1 at hy
    exact isoM.injective (by simpa using hy)
  obtain ⟨V, hV, hVc⟩ := stated_psu6_central_cover f hf hfk
  have h4 := le_pRank_of_elementaryAbelian (by norm_num : 1 < 3) V hV hVc
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h4
  omega

end CFSG.RankThree.PartOne
