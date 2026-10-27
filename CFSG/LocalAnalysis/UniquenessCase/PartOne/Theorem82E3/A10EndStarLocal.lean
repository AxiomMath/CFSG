module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K327Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.GroupTheory.PCore.CommutingBalance
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_zwr_subgroupOf {Q H : Subgroup G}
    (hQZ : Nonempty (↥Q ≃* UC22.InS3.UC326.ZWr 1)) (hQH : Q ≤ H) :
    Nonempty (↥(Q.subgroupOf H) ≃* UC22.InS3.UC326.ZWr 1) := by
  obtain ⟨e⟩ := hQZ
  exact ⟨(Subgroup.subgroupOfEquivOfLe hQH).trans e⟩

theorem hyp327_subgroupOf (hK : CFSG.Open.IsKProper G) {Q A H : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤) (hQZ : Nonempty (↥Q ≃* UC22.InS3.UC326.ZWr 1))
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hAQ : A ≤ Q)
    (hHtop : H ≠ ⊤) (hQH : Q ≤ H) :
    UC22.InS3.UC327.Hyp327 ↥H (Q.subgroupOf H) (A.subgroupOf H) := by
  classical
  let QH : Subgroup ↥H := Q.subgroupOf H
  let AH : Subgroup ↥H := A.subgroupOf H
  have hAHQH : AH ≤ QH := by
    intro x hx
    exact hAQ hx
  have hQH' : CFSG.ABGLocalTools.IsSylowOf 3 Q H := hQ.of_le hQH le_top
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 QH ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := H)).mp ?_
    simpa [QH, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQH,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hQH'
  obtain ⟨eH⟩ := nonempty_mulEquiv_zwr_subgroupOf hQZ hQH
  let E : Subgroup QH := AH.subgroupOf QH
  have hEelem : CFSG.Open.IsElemAbelian 3 E := (hA.subgroupOf H).subgroupOf QH
  have hEcard : Nat.card E = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAHQH).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAQ.trans hQH)).toEquiv, hA27]
  obtain ⟨AP, hET, -, -, huniq, -⟩ := UC22.InS3.UC326.zwr_unique_E27 (n := 1) (by norm_num) eH
  have hE : E = AP := huniq E hEelem hEcard
  have hjA : AH = UC22.InS3.UC326.jOf QH := by
    change AH = (CFSG.elemThompson ↥QH 3).map QH.subtype
    rw [hET, ← hE, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAHQH]
  exact
    { kgroup := CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hK hHtop
      sylow := hsyl
      jA := hjA
      elem := hA.subgroupOf H
      card := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAQ.trans hQH)).toEquiv, hA27]
      shape := Or.inr (nonempty_mulEquiv_zwr_subgroupOf hQZ hQH) }

private theorem map_relPPrimeCore_subgroupOf (p : ℕ) (hp : p.Prime) {B H : Subgroup G}
    (hBH : B ≤ H) :
    (CFSG.Open.relPPrimeCore p (B.subgroupOf H)).map H.subtype =
      CFSG.Open.relPPrimeCore p B := by
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      hp (B.subgroupOf H),
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map hp B,
    CFSG.pPrimeCore_map_subgroupOf p B H hBH]

theorem balance_subgroupOf {A H : Subgroup G} (hAH : A ≤ H)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({a} : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G))) :
    ∀ a ∈ A.subgroupOf H, a ≠ 1 → ∀ W : Subgroup ↥H,
      W ≤ Subgroup.centralizer ({a} : Set ↥H) →
      A.subgroupOf H ≤ Subgroup.normalizer (W : Set ↥H) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set ↥H)) := by
  intro a haA ha1 W hWcent hWnorm hWcop
  classical
  have haA' : (a : G) ∈ A := haA
  have ha1' : (a : G) ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext h)
  have hC : Subgroup.centralizer ({a} : Set ↥H) =
      (H ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf H := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  let W' : Subgroup G := W.map H.subtype
  have hW'H : W' ≤ H := Subgroup.map_subtype_le W
  have hW'C : W' ≤ H ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    refine Subgroup.mem_inf.mpr ⟨hW'H (Subgroup.mem_map_of_mem H.subtype hw), ?_⟩
    have h := hWcent hw
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    exact congrArg Subtype.val h
  have hWcard : Nat.card W' = Nat.card W :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hWcop' : Nat.Coprime (Nat.card W') 3 := by rw [hWcard]; exact hWcop
  have hWnorm' : A ≤ Subgroup.normalizer (W' : Set G) := by
    intro x hx
    have hxH : x ∈ H := hAH hx
    have hxsub : (⟨x, hxH⟩ : ↥H) ∈ (Subgroup.normalizer (W' : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hW'H]
      have hX : W'.subgroupOf H = W := by
        change Subgroup.comap H.subtype (Subgroup.map H.subtype W) = W
        exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective W
      rw [hX]
      exact hWnorm (show (⟨x, hxH⟩ : ↥H) ∈ A.subgroupOf H from hx)
    exact Subgroup.mem_subgroupOf.mp hxsub
  have hmain := hbal (a : G) haA' ha1' W' hW'C hWnorm' hWcop'
  have htrans : (CFSG.Open.relPPrimeCore 3
        (Subgroup.centralizer ({a} : Set ↥H))).map H.subtype =
      CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({(a : G)} : Set G)) := by
    rw [hC]
    exact map_relPPrimeCore_subgroupOf 3 Nat.prime_three inf_le_left
  refine (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp ?_
  rw [htrans]
  exact hmain

theorem le_relPPrimeCore_of_subgroupOf_le {H W : Subgroup G} (hWH : W ≤ H)
    (hW : W.subgroupOf H ≤ CFSG.pPrimeCore 3 ↥H) : W ≤ CFSG.Open.relPPrimeCore 3 H := by
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    Nat.prime_three H]
  calc W = (W.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hWH).symm
    _ ≤ _ := Subgroup.map_mono hW

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen
