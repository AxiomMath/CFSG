module

public import CFSG.Quasithin.EmptyFaithful.S146P20
public import CFSG.Quasithin.EmptyFaithful.S146zSPerf

public section

namespace CFSG.Quasithin.GoldS146P

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G]

theorem perfect_le_oTwoFstarIn {X Y : Subgroup G} (h : PerfInLayer (↥X ⧸ CFSG.pCore 2 ↥X))
    (hYX : Y ≤ X) (hY : ⁅Y, Y⁆ = Y) : Y ≤ oTwoFstarIn X := by
  intro y hy
  have hyX : y ∈ X := hYX hy
  have hmapY : (Y.subgroupOf X).map X.subtype = Y := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hYX
  have hY' : ⁅Y.subgroupOf X, Y.subgroupOf X⁆ = Y.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hmapY, hY]
  have hperf : ⁅(Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)),
      (Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))⁆ =
      (Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
    rw [← Subgroup.map_commutator, hY']
  have hle := h _ hperf
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨y, hyX⟩ ∈
      (Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
  have hF : CFSG.layer (↥X ⧸ CFSG.pCore 2 ↥X) ≤ CFSG.generalizedFitting (↥X ⧸ CFSG.pCore 2 ↥X) :=
    le_sup_right
  exact ⟨⟨y, hyX⟩, hF (hle hmem), rfl⟩

theorem perfect_sup_conjSub {K₁ : Subgroup G} (h : ⁅K₁, K₁⁆ = K₁) (s : G) :
    ⁅K₁ ⊔ conjSub s K₁, K₁ ⊔ conjSub s K₁⁆ = K₁ ⊔ conjSub s K₁ := by
  have h2 : ⁅conjSub s K₁, conjSub s K₁⁆ = conjSub s K₁ := by
    unfold conjSub
    rw [← Subgroup.map_commutator, h]
  refine le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_)
  · calc K₁ = ⁅K₁, K₁⁆ := h.symm
      _ ≤ _ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc conjSub s K₁ = ⁅conjSub s K₁, conjSub s K₁⁆ := h2.symm
      _ ≤ _ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem card_multiplicative_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
  exact Nat.card_zmod 2

theorem stage_perfect_data [Finite G] {T H : Subgroup G} {p : ℕ} (hAt : Stage14614At T H p)
    (hK : conjClosure (oTwoUpper H) (mcOf T) ≠ oTwoUpper H) :
    ⁅conjClosure (oTwoUpper H) (mcOf T), conjClosure (oTwoUpper H) (mcOf T)⁆ =
        conjClosure (oTwoUpper H) (mcOf T) ∧ PerfInLayer (OTwoQuot (mcOf T)) := by
  have hQ := card_multiplicative_zmod_two
  rcases hAt with ⟨hEq, -⟩ | ⟨-, hKz, n, hn, ⟨e⟩⟩ | ⟨-, K₁, s, hK₁, -, -, he, hW⟩ |
    ⟨-, K₁, s, hK₁, hsT, -, he, -, hidx, e⟩
  · exact absurd hEq hK
  · exact ⟨perfect_of_mem_cComp hKz, PerfInLayer.of_equiv e (perfInLayer_aut_sl n (by omega))⟩
  · rw [he]
    refine ⟨perfect_sup_conjSub (perfect_of_mem_cComp hK₁) s, ?_⟩
    rcases hW with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact PerfInLayer.of_equiv e (perfInLayer_wreath_perm5 hQ)
    · exact PerfInLayer.of_equiv e (perfInLayer_wreath_sl3 hQ)
  · have hKzN : mcOf T ≤ Subgroup.normalizer ((K₁ ⊔ conjSub s K₁ : Subgroup G) : Set G) := by
      rw [← he]
      exact le_normalizer_conjClosure _ _
    rw [he] at hidx ⊢
    exact ⟨perfect_sup_conjSub (perfect_of_mem_cComp hK₁) s,
      perfInLayer_oTwoQuot_of_L216 hK₁ (le_centralizer_quasithinOmegaOneCenter T hsT) hKzN hidx e⟩

end CFSG.Quasithin.GoldS146P

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

theorem input14617FstarK_holds : Input14617FstarK := by
  intro G _ _ T M S H PQ p hred hmax hAt hK
  obtain ⟨hperf, hlayer⟩ := GoldS146P.stage_perfect_data hAt hK
  have hKG : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans (S.le_mcOf hred.isHTM)
  have hKz : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T :=
    conjClosure_le fun h hh z hz =>
      (mcOf T).mul_mem ((mcOf T).mul_mem hh (hKG hz)) ((mcOf T).inv_mem hh)
  have hlayer' : GoldS146P.PerfInLayer (↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) :=
    GoldS146P.PerfInLayer.of_equiv
      (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥(mcOf T) 2)) hlayer
  exact (le_conjClosure _ _).trans (GoldS146P.perfect_le_oTwoFstarIn hlayer' hKz hperf)

end CFSG.Quasithin
