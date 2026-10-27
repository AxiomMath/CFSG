module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item211Proof

section Certs


theorem listJ217_of (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1)
    (h41 : Sec4.Item4_1LargePrime) {G : Type} [Group G] [Finite G] {A J : Subgroup G} {d : G}
    (hst : PartTwoStanding G) (hAS : A ∈ partTwoS G) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hJd : J ∈ thetaComponentsAt 3 d) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hCA : A ⊓ Sec4.thetaQuotCentralizer J = Subgroup.zpowers d) (hJ0 : J ∈ lZeroUnion A) :
    ∃ m : ℕ, Nat.card A = 3 ^ m ∧ List211 A d J := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAS.1.1
  have hA : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hJC : J ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hJd
  have hAC : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩))
  have hq : IsQuasisimple (lBar J) := by
    obtain ⟨L', hL', hLL'⟩ := hJd
    rw [← hLL']
    exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2
  have hΛ : SectionFourHyp ↥(J ⊔ A) := hst.toTheoremFourHyp.sectionFourHyp
    (fun htop => centralizer_ne_top hst.toTheoremFourHyp hd1
      (eq_top_iff.mpr (htop ▸ sup_le hJC hAC)))
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAJ
  have hX : SectionFourHyp (QuotX J A) := sectionFourHyp_quotX h41 hΛ hA hAJ Φ₀ hq
  obtain ⟨eAut⟩ := nonempty_autIn_lOne_equiv hA hAJ
  obtain ⟨eX⟩ := nonempty_quotX_equiv_lBarA hJd hAC hA hAJ
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  obtain ⟨E₀, hE₀, hE₀A, -, U₀, hU₀, hU₀E⟩ := mem_lZeroUnion_iff.mp hJ0
  obtain ⟨hE₁, hE₁A, T, hT, hTc⟩ :=
    exists_eOne hA hAJ (Late.isE27_of_mem_partTwoE hE₀) hE₀A hU₀ hU₀E
  have hc₁ : orderOf (piX J A ⟨d, Subgroup.mem_sup_right hdA⟩) = 3 := by
    have h1 : (piX J A ⟨d, Subgroup.mem_sup_right hdA⟩) =
        ((aEquiv (L := J) hA ⟨d, hdA⟩ : aOne J A) : QuotX J A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 d hdA) hd1
  have hquad : Sec4.IsQuad417 (lOne J A) (aOne J A) ((E₀.subgroupOf (J ⊔ A)).map (piX J A))
      (piX J A ⟨d, Subgroup.mem_sup_right hdA⟩) m :=
    ⟨maximal_aOne hAe hAS.1.2.1,
      by rw [← Nat.card_congr (aEquiv (L := J) hA).toEquiv, hm],
      aOne_inf_centralizer hA hAJ hdA hCA, hc₁, hE₁, hE₁A, T, hT, hTc⟩
  have h417' := h417 (QuotX J A) hX pCore_two_quotX (lOne J A)
    (isComponent_lOne hAJ Φ₀ hq) (quad_le_four h611 hst) (aOne J A)
    ((E₀.subgroupOf (J ⊔ A)).map (piX J A)) (piX J A ⟨d, Subgroup.mem_sup_right hdA⟩) m hquad
  exact ⟨m, hm, list211_of_alt417 hAJ hΦ₀ eAut eX hm h417'⟩

end Certs

end CFSG.RankThree.PartTwo.Sec21
