module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSevenL

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem step207Gen_core
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20 G A M L N c T)
    (hN : N = Subgroup.normalizer (L : Set G))
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (hLM : ¬ L ≤ M) (hO2M : CFSG.Open.pCoreOf 2 L ≤ M) (h280 : (L ⊓ M).relIndex L = 280)
    (hBb9 : Nat.card (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 9)
    (hNB : Subgroup.normalizer ((((A ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup _) : Set _) ≤
      ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
    (hTN : T ≤ N) : L ≤ (L ⊓ Subgroup.normalizer (T : Set G)) ⊔ (A ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hLq
  have hO2T : CFSG.Open.pCoreOf 2 L ≤ T := pCoreOf_le_core hT hN hO2M hTN
  have hO2L : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hTM : T ≤ M := hT.sylow.le
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hN ▸ hTN
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ
  set Bb := ((A ⊓ L).subgroupOf L).map φ with hBb
  set Y' := (L ⊓ M).subgroupOf L with hY'
  have hkerY : φ.ker ≤ Y' := by
    rw [hφ, QuotientGroup.ker_mk']
    intro x hx
    rw [hY', Subgroup.mem_subgroupOf]
    exact ⟨x.2, hO2M ((mem_pCore_iff_mem_pCoreOf_two x).mp hx)⟩
  have hYtop : Y'.map φ ≠ ⊤ := by
    intro htop
    apply hLM
    intro x hxL
    have hcomap : (Y'.map φ).comap φ = Y' := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerY]
    have hmem : (⟨x, hxL⟩ : L) ∈ (Y'.map φ).comap φ := by
      rw [Subgroup.mem_comap, htop]
      exact Subgroup.mem_top _
    rw [hcomap, hY', Subgroup.mem_subgroupOf] at hmem
    exact hmem.2
  have hY : Y'.map φ = Subgroup.normalizer (Bb : Set _) :=
    KFacts.L34Max.eq_normalizer_of_normalizer_le e hBb9 hNB hYtop
  set J := (L ⊓ Subgroup.normalizer (T : Set G)) ⊔ (A ⊓ L) with hJ
  set J' := J.subgroupOf L with hJ'
  have hOJ : CFSG.Open.pCoreOf 2 L ≤ J :=
    (le_inf hO2L (hO2T.trans Subgroup.le_normalizer)).trans le_sup_left
  have hkerJ : φ.ker ≤ J' := by
    rw [hφ, QuotientGroup.ker_mk']
    intro x hx
    rw [hJ', Subgroup.mem_subgroupOf]
    exact hOJ ((mem_pCore_iff_mem_pCoreOf_two x).mp hx)
  have hNJ : Subgroup.normalizer (Bb : Set _) ≤ J'.map φ := by
    set Sb := ((T ⊓ (L ⊓ M)).subgroupOf L).map φ with hSb
    set Q := Subgroup.normalizer (Bb : Set (↥L ⧸ CFSG.pCore 2 ↥L)) with hQ
    have hQ72 : Nat.card Q = 72 := KFacts.L34Max.card_normalizer_of_card_eq_nine e hBb9
    have hBQ : Bb ≤ Q := Subgroup.le_normalizer
    have hSQ : Sb ≤ Q := by
      rw [← hY]
      refine Subgroup.map_mono fun x hx => ?_
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hx.2
    have hBidx : Bb.relIndex Q = 8 := by
      have h1 := Subgroup.relIndex_mul_card Bb Q
      rw [inf_eq_left.mpr hBQ, hQ72, hBb9] at h1
      omega
    have hTLsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ (L ⊓ M)) (L ⊓ M) :=
      (hT.sylow.of_le le_sup_left (sup_le hTM inf_le_right)).inf_of_le_normalizer le_sup_right
        (sup_le (fun t ht => mem_normalizer_inf_of_mem (hTL ht) (Subgroup.le_normalizer (hTM ht)))
          Subgroup.le_normalizer)
    obtain ⟨-, -, hodd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hTLsyl
    have hkerS : φ.ker ≤ (T ⊓ (L ⊓ M)).subgroupOf L := by
      rw [hφ, QuotientGroup.ker_mk']
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hx' := (mem_pCore_iff_mem_pCoreOf_two x).mp hx
      exact ⟨hO2T hx', x.2, hO2M hx'⟩
    have hSidx : Sb.relIndex Q = (T ⊓ (L ⊓ M)).relIndex (L ⊓ M) := by
      rw [hSb, ← hY, hY', Subgroup.relIndex_map_map, sup_eq_left.mpr hkerS, sup_eq_left.mpr hkerY,
        Subgroup.relIndex_subgroupOf inf_le_left]
    set R := J'.map φ ⊓ Q with hR
    have hBR : Bb ≤ R := by
      refine le_inf (Subgroup.map_mono fun x hx => ?_) hBQ
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact Subgroup.mem_sup_right hx
    have hSR : Sb ≤ R := by
      refine le_inf (Subgroup.map_mono fun x hx => ?_) hSQ
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact Subgroup.mem_sup_left ⟨x.2, Subgroup.le_normalizer hx.1⟩
    have h8 : R.relIndex Q ∣ 8 := hBidx ▸ Subgroup.relIndex_dvd_of_le_left Q hBR
    have hm : R.relIndex Q ∣ (T ⊓ (L ⊓ M)).relIndex (L ⊓ M) :=
      hSidx ▸ Subgroup.relIndex_dvd_of_le_left Q hSR
    have hcop : Nat.Coprime 8 ((T ⊓ (L ⊓ M)).relIndex (L ⊓ M)) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have h1 : R.relIndex Q = 1 := Nat.eq_one_of_dvd_coprimes hcop h8 hm
    exact (Subgroup.relIndex_eq_one.mp h1).trans inf_le_left
  by_contra hne
  have hJtop : J'.map φ ≠ ⊤ := by
    intro htop
    apply hne
    intro x hxL
    have hcomap : (J'.map φ).comap φ = J' := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerJ]
    have hmem : (⟨x, hxL⟩ : L) ∈ (J'.map φ).comap φ := by
      rw [Subgroup.mem_comap, htop]
      exact Subgroup.mem_top _
    rw [hcomap, hJ', Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hJeq := KFacts.L34Max.eq_normalizer_of_normalizer_le e hBb9 hNJ hJtop
  obtain ⟨x, hx, hxM, -⟩ := exists_two_element_core hT hN h280 hTN
  have hxJ : φ ⟨x, hx.1⟩ ∈ Y'.map φ := by
    rw [hY, ← hJeq]
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    show (⟨x, hx.1⟩ : ↥L) ∈ J.subgroupOf L
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left hx
  obtain ⟨y, hy, hyx⟩ := hxJ
  have hyM : (y : G) ∈ M := (Subgroup.mem_subgroupOf.mp hy).2
  have hker : y⁻¹ * ⟨x, hx.1⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  rw [hφ, QuotientGroup.ker_mk'] at hker
  have hO := (mem_pCore_iff_mem_pCoreOf_two _).mp hker
  apply hxM
  have : x = (y : G) * ((y⁻¹ * ⟨x, hx.1⟩ : ↥L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this]
  exact M.mul_mem hyM (hO2M hO)

section Certificates

theorem step207Gen_of (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) : Step207Gen := by
  intro G _ _ A M L N c T hT hTN
  have h := hT.hyp201One
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_ctx20One hT
  exact step207Gen_core hT.toCtx20 hN (nonempty_quotient_of_hyp201One h184 h)
    (not_le_of_hyp201One h) (pCoreOf_le_of_hyp201One h)
    (relIndex_inf_eq_of_hyp201One h1812 h184 h) (card_map_inf_of_hyp201One h1812 h184 h)
    (normalizer_map_le_of_hyp201One h1812 h184 h) hTN

theorem item207One_of_items_gen (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (h1812 : Sec18.Item181_2)
    (h184 : Sec18.Item184_1) (h206 : Item206One) (hK0 : Step207K0) : Item207One :=
  item207One_of_items h204 h2051 h2053 h189 h321 h1812 h184 h206 (step207Gen_of h1812 h184) hK0

end Certificates

end CFSG.RankThree.PartTwo.Sec20
