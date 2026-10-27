module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem largeEvenPComponent_of_isComponentOf_of_dvd {p : ℕ} (hp : p.Prime)
    {C X : Subgroup G} (hX : IsComponentOf X C) (hpX : p ∣ Nat.card X) :
    LargeEvenPComponent p C X := by
  have : Fact p.Prime := ⟨hp⟩
  have hXO : ¬ X ≤ CFSG.Open.lBalancePrimeCore p C := by
    intro hle
    have hcop : Nat.Coprime p (Nat.card (CFSG.Open.lBalancePrimeCore p C)) := by
      rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map,
        Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop (hpX.trans (Subgroup.card_dvd_of_le hle))
  exact (largeEvenPComponent_iff_lBalance p _ X).mpr
    ⟨hX.1, lBalanceIsPComponent_of_isComponentOf hX hXO⟩

omit [Finite G] in
private theorem map_conj_le_of_le_of_mem {H P : Subgroup G} {w : G} (hHP : H ≤ P) (hw : w ∈ P) :
    H.map (MulAut.conj w).toMonoidHom ≤ P := by
  rintro _ ⟨h, hh, rfl⟩
  simpa [MulAut.conj_apply] using P.mul_mem (P.mul_mem hw (hHP hh)) (P.inv_mem hw)

theorem ggNbr_eq_map_conj_of_isComponentOf {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) {e w : G}
    {X : Subgroup G} (hX : IsComponentOf X (Subgroup.centralizer ({e} : Set G))) (hJX : J ≤ X)
    (hw : w ∈ Subgroup.normalizer (J : Set G))
    (hy : Subgroup.zpowers y = Subgroup.zpowers (w * e * w⁻¹)) :
    K = X.map (MulAut.conj w).toMonoidHom := by
  have hX' : IsComponentOf (X.map (MulAut.conj w).toMonoidHom)
      (Subgroup.centralizer ({y} : Set G)) := by
    rw [centralizer_singleton_eq_of_zpowers_eq hy]
    simpa only [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton] using
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hX w
  have hJX' : J ≤ X.map (MulAut.conj w).toMonoidHom :=
    (map_conj_eq_of_mem_normalizer hw).symm.le.trans (Subgroup.map_mono hJX)
  have hK : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hnbr)).1
  exact ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hX' hK).resolve_right
    fun hcomm => not_le_centralizer_of_ggNbr hI hDJ hnbr
      (hJX'.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm))).symm

theorem ggG0_eq_sup_of_lineCover {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) (hJK : J ≤ K)
    (hcover : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ∃ w ∈ (L ⊔ K) ⊓ Subgroup.normalizer (J : Set G),
        Subgroup.zpowers y' = Subgroup.zpowers (w * y * w⁻¹) ∨
          Subgroup.zpowers y' = Subgroup.zpowers (w * x * w⁻¹)) :
    ggG0 p B x L D J = L ⊔ K := by
  have hKc : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hnbr)).1
  have hLc : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hI.2.2.2.2.2.2.1.2.2.2.1
  have hJL : J ≤ L := fun j hj => (hDJ.1.2.2.2.2.2.1.1 hj).1
  refine le_antisymm ?_ (sup_le (le_ggG0_left p B x L D J) (le_ggG0_of_ggNbr hnbr))
  unfold ggG0
  refine sup_le le_sup_left (iSup_le fun y' => iSup_le fun K' => iSup_le fun h => ?_)
  obtain ⟨w, ⟨hwP, hwJ⟩, hy' | hy'⟩ := hcover y' K' h
  · rw [ggNbr_eq_map_conj_of_isComponentOf hI hDJ h hKc hJK hwJ hy']
    exact map_conj_le_of_le_of_mem le_sup_right hwP
  · rw [ggNbr_eq_map_conj_of_isComponentOf hI hDJ h hLc hJL hwJ hy']
    exact map_conj_le_of_le_of_mem le_sup_left hwP

end CFSG.StandardType
