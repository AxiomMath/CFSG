module

public import CFSG.Sporadic.Recognition.LyonsSimsCover
public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.Sporadic.Ly

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage12.McLRec
  CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly

theorem isConj_of_equiv_of_involutions {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : ∀ u v : L, orderOf u = 2 → orderOf v = 2 → IsConj u v) {u v : K} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : IsConj u v := by
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hv' : orderOf (e v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  obtain ⟨c, hc⟩ := isConj_iff.mp (h _ _ hu' hv')
  refine isConj_iff.mpr ⟨e.symm c, ?_⟩
  apply e.injective
  simp [hc]

theorem ly_isConj_of_involutions
    {u v : Blueprint.NativeSporadic.Ly} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : IsConj u v := by
  refine isConj_of_equiv_of_involutions (K := Blueprint.NativeSporadic.Ly) (L := J)
    (by exact lyEquivJ) ?_ hu hv
  intro a b ha hb
  obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 a ha
  obtain ⟨y, hy⟩ := involution_centralizer_fusion_generator.2 b hb
  refine isConj_iff.mpr ⟨y * x⁻¹, ?_⟩
  rw [← hx, ← hy]
  group

theorem card_lyC :
    Nat.card ↥lyC = 39916800 := by
  rw [← full_involution_centralizer.2]
  exact Nat.card_congr (MulEquiv.subgroupCongr lyC_eq_centralizer).toEquiv

theorem card_centralizer_of_equiv_ly
    {K : Type*} [Group K]
    (hK : Nonempty (K ≃* Blueprint.NativeSporadic.Ly)) {u : K} (hu : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set K)) = 39916800 := by
  obtain ⟨E⟩ := centralizer_equiv_lyC hK u hu
  rw [Nat.card_congr E.toEquiv, card_lyC]

theorem card_ly :
    Nat.card Blueprint.NativeSporadic.Ly = 51765179004000000 := CFSG.Sporadic.Ly.card_Ly

theorem exists_mulEquiv_of_subgroup_ly
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) (hG : OneClassDoubleCover G 11)
    (H : Subgroup G) (e : ↥H ≃* Blueprint.NativeSporadic.Ly) :
    Nonempty (G ≃* Blueprint.NativeSporadic.Ly) := by
  have hcardH : Nat.card H = 51765179004000000 := by
    rw [Nat.card_congr e.toEquiv]; exact card_ly
  have hev : Even (Nat.card H) := by rw [hcardH]; decide
  have hone : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v :=
    fun u v hu hv => isConj_of_equiv_of_involutions (K := ↥H)
      (L := Blueprint.NativeSporadic.Ly) (by exact e) (fun _ _ => ly_isConj_of_involutions) hu hv
  have hcH : ∀ u : H, orderOf u = 2 → Nat.card (centralizer ({u} : Set H)) = 39916800 :=
    fun u hu => card_centralizer_of_equiv_ly ⟨e⟩ hu
  have hH : H = ⊤ := eq_top_of_oneClass_centralizers hs coverFacts_eleven hG H hev hone hcH
  exact ⟨((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr hH.symm)).trans e⟩

@[expose] def LyContains : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    OneClassDoubleCover G 11 → ∃ H : Subgroup G, Nonempty (↥H ≃* Blueprint.NativeSporadic.Ly)

theorem S_Ly_leaf_of_LyContains
    (h : LyContains) : S_Ly_leaf := by
  intro G _ _ hs hnab hG
  obtain ⟨H, ⟨e⟩⟩ := h G hs hnab hG
  obtain ⟨f⟩ := exists_mulEquiv_of_subgroup_ly hs hG H e
  exact ⟨f⟩

theorem LyContains_of_S_Ly_leaf (h : S_Ly_leaf) : LyContains := by
  intro G _ _ hs hnab hG
  obtain ⟨e⟩ := h G hs hnab hG
  exact ⟨⊤, ⟨(Subgroup.topEquiv (G := G)).trans e⟩⟩

theorem lyContains_iff_S_Ly_leaf :
    LyContains ↔ S_Ly_leaf :=
  ⟨S_Ly_leaf_of_LyContains, LyContains_of_S_Ly_leaf⟩

end CFSG.Sporadic.Recognition.LyonsSims
