module

public import CFSG.Quasithin.Vol2.Ch11SecO8HC
public import CFSG.Quasithin.Vol2.Ch11SecO8HD
public import CFSG.Quasithin.Vol2.Ch11SecO8HS
public import CFSG.Quasithin.Vol2.Ch11SecD556C
public import CFSG.Quasithin.Vol2.Ch11SecD556I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

namespace O8H

variable {G : Type} [Group G] [Finite G] {T L I V₁ X : Subgroup G} {n : ℕ}

theorem pRank_le_of_le {q : ℕ} (hq : 1 < q) {Y Z : Subgroup G} (h : Y ≤ Z) :
    CFSG.pRank q ↥Y ≤ CFSG.pRank q ↥Z := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective hq (Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

theorem commutator_le_of_quasisimple (hT : FactCCompTorus)
    (h121 : QuasithinUnique.Id2519.Prop121Three) (hT44 : SecE.Facts44) (hCart : CartanFact)
    (hC : SecS.CartanFacts) (hF : SecA.NatFacts) (hTI : PointsTIFact) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) {I' : Subgroup G}
    (hI' : quasithinIsCComponent I' (Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))))
    (hq : CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I')) :
    ⁅I', X⁆ ≤ pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.fsu.simple
  set Y := Subgroup.centralizer (V₁ : Set G) ⊓
    sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) with hYdef
  have hq' : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke
  have hYN : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_le_normalizer_Y L V₁
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := (SecA.IsVi.le_normalizer hV₁).trans hYN
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) :=
    (cartan_le_normalizer_V₁ hF h1102 h hV₁ hX).trans hYN
  have hY2 : pCoreOf 2 Y ≠ ⊥ := fun hb => SecA.IsVi.ne_bot h hV₁ le_rfl
    (le_bot_iff.mp (hb ▸ le_pCoreOf_Y hTI h1102 h1141 h1143 h hV₁))
  obtain ⟨-, V₂, -, -, hV₂, -⟩ := SecA.exists_isVi hF h1102 h
  have hYq : Nat.Coprime (Nat.card Y) (2 ^ n - 1) :=
    stmt11_5_6_one hCart hF h1102 h1141 h1151 h hV₁ hX
  have hXYc : Nat.Coprime (Nat.card X) (Nat.card Y) := coprime_cartan hC hF h1102 h hV₁ hV₂ hX hYq
  have hI'Y : I' ≤ Y := le_of_mem_cComp hI'
  have hXc : ∀ t ∈ T,
      X ≤ Subgroup.normalizer ((I'.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    intro t ht
    have h1 := cComp_map_mulEquiv (MulAut.conj t) hI'
    have hYt : Y.map (MulAut.conj t).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTY ht)
    rw [hYt] at h1
    exact le_normalizer_of_mem_cComp h121 h.fsu.simple h.fsu.nonabelian hq' hXY hX.2.1 hY2 h1
  have hJ₀Y : conjClosure I' T ≤ Y := conjClosure_le fun t ht z hz =>
    (Subgroup.mem_normalizer_iff.mp (hTY ht) z).mp (hI'Y hz)
  have hXJ₀ : X ≤ Subgroup.normalizer (conjClosure I' T : Set G) := le_normalizer_conjClosure_of hXc
  obtain ⟨D, hD⟩ := exists_isHallTwoPrimeOf_inf_normalizer h.fsu.sylow (conjClosure I' T)
  have hDq : Nat.Coprime (Nat.card D) (2 ^ n - 1) :=
    hYq.coprime_dvd_left (Subgroup.card_dvd_of_le ((hD.1.trans inf_le_left).trans hJ₀Y))
  have hDX := exists_conj_centralized_torus hT44 h331 h1102 h1103 h
    (h1141 G T L I n V₁ X h hV₁ hX).1.1 hV₁ hX hJ₀Y hXJ₀ hD hDq
  have hsub : IsSubnormal Y (Y ⊔ T) := isSubnormal_sup hTY
  have hYT2 : pCoreOf 2 (Y ⊔ T) ≠ ⊥ := fun hb =>
    hY2 (le_bot_iff.mp ((A4.pCoreOf_le_of_subnormal 2 hsub).trans hb.le))
  have hSyl : QuasithinUnique.IsSylowTwoOf T (Y ⊔ T) := ⟨le_sup_right, h.fsu.sylow.1,
    fun h2 => h.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hcop : Nat.Coprime (Nat.card X) (2 * Nat.card I') :=
    Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hX.2.1)
      (hXYc.coprime_dvd_right (Subgroup.card_dvd_of_le hI'Y))
  have h3r : CFSG.pRank 3 ↥I' ≤ 1 :=
    (pRank_le_of_le (by norm_num) hI'Y).trans (stmt11_5_6_two h1110 h hV₁)
  have h3 := hT G (Y ⊔ T) T I' X D (hq'.1 (Y ⊔ T) hYT2) hSyl (cComp_mem_of_subnormal hsub hI') hq
    h3r hcop (fun s hs => hXc s⁻¹ (T.inv_mem hs)) hD hDX
  exact h3.trans (A4.pCoreOf_le_of_subnormal 2 hI'.2.2.1)

end O8H

end CFSG.Quasithin.Vol2.Ch11.SecD
