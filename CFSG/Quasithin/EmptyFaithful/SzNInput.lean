module

public import CFSG.Quasithin.EmptyFaithful.S153H34

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input34SuzukiThreeSQTK : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.SectionRank.IsSQTKCat X → ¬ 3 ∣ Nat.card X → ∃ e : ℕ, IsSz e X

namespace S153H

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

private theorem isSQTKCat_of_le_szn (hLI : L ≤ I) (hI : CFSG.SectionRank.IsSQTKCat ↥I) :
    CFSG.SectionRank.IsSQTKCat ↥L :=
  CFSG.SectionRank.IsSQTKCat.of_le hLI hI

private theorem isPGroup_two_center_szn (hc : centerOf L = pCoreOf 2 L) :
    IsPGroup 2 ↥(Subgroup.center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z
  have hz : ((z : ↥L) : G) ∈ pCoreOf 2 L := by
    rw [← hc]
    refine ⟨(z : ↥L).2, ?_⟩
    show ((z : ↥L) : G) ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨((z : ↥L) : G), hz⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem isSQTKCat_quotient_center (c : CtxComp T Mc M V₁ V₂ Yp I t)
    (hL : Concl15333 T M V₁ Yp I L) :
    CFSG.SectionRank.IsSQTKCat (↥L ⧸ Subgroup.center ↥L) := by
  have hq := c.hyp.hyp.qtfe
  have := hq.simple
  have hI : CFSG.SectionRank.IsSQTKCat ↥I :=
    (qtkeCore_of_cat hq.nonabelian hq.qtke).1 I c.inH.1.2
  have hLI : L ≤ I := le_of_mem_cComp hL.mem
  have hL' := isSQTKCat_of_le_szn hLI hI
  exact ⟨(CFSG.SectionRank.isStronglyQuasithin_quotient_two_group_iff (Subgroup.center ↥L)
      (isPGroup_two_center_szn hL.center_eq)).mpr hL'.1,
    CFSG.SectionRank.IsKGroupCat.quotient hL'.2 (Subgroup.center ↥L)⟩

theorem input15334_of_named_inputs_sqtk (hSz3 : Input34SuzukiThreeSQTK) (hBo : Input34Borel)
    (hCe : Input34Centralizer) : Input15334 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hLI : L ≤ I := le_of_mem_cComp hL.mem
  have hnotSz : ¬ ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L) := by
    intro hsz
    obtain ⟨B, hBL₀, hBor, hBn, hBchar, hBmax⟩ := hBo G T Mc M V₁ V₂ Yp I L t c hL hsz
    have hL₀I := conjClosure_le_I (T := T) (V₁ := V₁) hSI hLI
    have hBM : B ≤ M ⊓ I := hL.inv_le B hBL₀ hBn hBchar
    have hBeq : B = M ⊓ conjClosure L (Sgp153 T V₁) := by
      refine (hBmax (M ⊓ conjClosure L (Sgp153 T V₁)) inf_le_right ?_
        (le_inf (fun x hx => (hBM hx).1) hBL₀) ?_).symm
      ·
        have hSM : Sgp153 T V₁ ≤ Subgroup.normalizer (M : Set G) :=
          (inf_le_left.trans c.hyp.hyp.T_le).trans Subgroup.le_normalizer
        exact fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hSM hg, le_normalizer_conjClosure L (Sgp153 T V₁) hg⟩
      ·
        intro h
        exact hL.not_le ((le_conjClosure L (Sgp153 T V₁)).trans (h.symm.le.trans inf_le_left))
    have hYC := hCe G T Mc M V₁ V₂ Yp I L t c hL hsz B hBor hBn hBeq
    exact hL.not_le (le_M_of_Yp_le_centralizer c hL hYC)
  refine ⟨hnotSz, ?_⟩
  by_contra hr
  have hq : CFSG.IsQuasisimple ↥L := hL.quasisimple
  have h3L : ¬ 3 ∣ Nat.card ↥L := by
    intro hdvd
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 hdvd
    have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
    refine hr (CFSG.Quasithin.le_pRank (by norm_num : Nat.Prime 3)
      (Subgroup.zpowers_le.mpr x.2) (k := 1) ⟨?_, ?_⟩ ?_)
    · exact ⟨⟨fun a b => by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
        apply Subtype.ext
        change (a : G) * b = b * a
        rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]⟩⟩
    · intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxG, pow_orderOf_eq_one,
        one_zpow]
    · rw [Nat.card_zpowers, hxG, pow_one]
  have h3Q : ¬ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    fun hdvd => h3L (hdvd.trans (Subgroup.card_quotient_dvd_card _))
  exact hnotSz (hSz3 _ hq.2.1 hq.2.2 (isSQTKCat_quotient_center c hL) h3Q)

end S153H

end CFSG.Quasithin
