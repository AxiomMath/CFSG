module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Bar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Product
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.ProductBar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.GraphL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.GraphSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.GraphBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup

namespace RankOneBorel

variable {G : Type} [Group G] [Finite G]

theorem holds_rankOne {T L J : Subgroup G} (hTL : IsSylowIn 2 (T ⊓ L) L) {n : ℕ}
    (h : IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) (hJ1 : T ⊓ L ≤ J)
    (hJ2 : J ≤ L) :
    J ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∨ J = L := by
  have hO : pCoreOf 2 L ≤ J := (pCoreOf_le_inf hTL).trans hJ1
  obtain ⟨S, hS⟩ := exists_sylow_barImage hTL
  have hSJ : barImage L (T ⊓ L) ≤ barImage L J :=
    (barImage_le_barImage_iff hO inf_le_right).2 hJ1
  refine of_bar hTL hJ1 hJ2 ?_
  rw [← hS]
  exact rankOneOver_of_shape h S (barImage L J) (hS ▸ hSJ)

theorem holds_product {T L J L₁ L₂ : Subgroup G} (hTL : IsSylowIn 2 (T ⊓ L) L)
    (h₁ : L₁ ∈ calC L) (h₂ : L₂ ∈ calC L) (hsup : L = L₁ ⊔ L₂) (hne : L₁ ≠ L₂) {t : G}
    (ht : t ∈ T) (hL₂ : L₂ = L₁.map (MulAut.conj t).toMonoidHom) {n : ℕ}
    (hn : ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
      IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3))
    (hJ1 : T ⊓ L ≤ J) (hJ2 : J ≤ L) (hTJ : T ≤ normalizer (J : Set G)) :
    J ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∨ J = L := by
  have hO : pCoreOf 2 L ≤ J := (pCoreOf_le_inf hTL).trans hJ1
  obtain ⟨S, hS⟩ := exists_sylow_barImage hTL
  have hSJ : barImage L (T ⊓ L) ≤ barImage L J :=
    (barImage_le_barImage_iff hO inf_le_right).2 hJ1
  have hL₁ : L₁ ≤ L := le_sup_left.trans hsup.symm.le
  have hL₂le : L₂ ≤ L := le_sup_right.trans hsup.symm.le
  have htJ : J.map (MulAut.conj t).toMonoidHom = J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
  have htJ' : J.map (MulAut.conj t⁻¹).toMonoidHom = J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((normalizer (J : Set G)).inv_mem (hTJ ht))
  have h12 : barImage L L₁ ≤ barImage L J → barImage L L₂ ≤ barImage L J := by
    intro hbar
    rw [barImage_le_barImage_iff hO hL₂le]
    have h1J : L₁ ≤ J := (barImage_le_barImage_iff hO hL₁).mp hbar
    calc L₂ = L₁.map (MulAut.conj t).toMonoidHom := hL₂
      _ ≤ J.map (MulAut.conj t).toMonoidHom := Subgroup.map_mono h1J
      _ = J := htJ
  have h21 : barImage L L₂ ≤ barImage L J → barImage L L₁ ≤ barImage L J := by
    intro hbar
    rw [barImage_le_barImage_iff hO hL₁]
    have h2J : L₂ ≤ J := (barImage_le_barImage_iff hO hL₂le).mp hbar
    have hL₁eq : L₁ = L₂.map (MulAut.conj t⁻¹).toMonoidHom := by
      rw [hL₂, Subgroup.map_map]
      rw [show (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          MonoidHom.id G from by ext x; simp [MulAut.conj_apply]; group,
        Subgroup.map_id]
    calc L₁ = L₂.map (MulAut.conj t⁻¹).toMonoidHom := hL₁eq
      _ ≤ J.map (MulAut.conj t⁻¹).toMonoidHom := Subgroup.map_mono h2J
      _ = J := htJ'
  have hr₁ : RankOneOver ↥(barImage L L₁) := by
    refine rankOneOver_barImage h₁ ?_
    rcases hn L₁ (by simp) with h | h | ⟨-, h⟩
    · exact rankOneOver_of_shape (Or.inl h)
    · exact rankOneOver_of_shape (Or.inr (Or.inl h))
    · exact rankOneOver_of_shape (Or.inr (Or.inr h))
  have hr₂ : RankOneOver ↥(barImage L L₂) := by
    refine rankOneOver_barImage h₂ ?_
    rcases hn L₂ (by simp) with h | h | ⟨-, h⟩
    · exact rankOneOver_of_shape (Or.inl h)
    · exact rankOneOver_of_shape (Or.inr (Or.inl h))
    · exact rankOneOver_of_shape (Or.inr (Or.inr h))
  refine of_bar hTL hJ1 hJ2 ?_
  rw [← hS]
  exact dich_of_product (barImage L L₁) (barImage L L₂)
    (barImage_normal_of_calC h₁ h₂ hsup)
    (barImage_normal_of_calC h₂ h₁ (hsup.trans (sup_comm L₁ L₂)))
    (barImage_sup_eq_top hsup) (barImage_commutator_eq_bot h₁ h₂ hsup hne)
    (barImage_perfect h₁) (barImage_perfect h₂) hr₁ hr₂ S (barImage L J) (hS ▸ hSJ) h12 h21

theorem holds_graph {T L J : Subgroup G} (hTL : IsSylowIn 2 (T ⊓ L) L) (hperf : ⁅L, L⁆ = L)
    {n : ℕ}
    (hsh : IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n) {t : G} (ht : t ∈ T)
    (hact : ActsNontrivOnDiagram L t) (hJ1 : T ⊓ L ≤ J) (hJ2 : J ≤ L)
    (hTJ : T ≤ normalizer (J : Set G)) :
    J ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∨ J = L := by
  obtain ⟨htL, θ, hθ, hnd⟩ := hact
  have hO : pCoreOf 2 L ≤ J := (pCoreOf_le_inf hTL).trans hJ1
  obtain ⟨S, hS⟩ := exists_sylow_barImage hTL
  have hSJ : barImage L (T ⊓ L) ≤ barImage L J :=
    (barImage_le_barImage_iff hO inf_le_right).2 hJ1
  have htTL : t ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := L)
      ⟨Subgroup.le_normalizer ht, htL⟩
  let Z : Subgroup (Bar2 L) := Subgroup.center (Bar2 L)
  let Q : Bar2 L →* Bar2 L ⧸ Z := QuotientGroup.mk' Z
  let SX : Sylow 2 (Bar2 L ⧸ Z) := S.mapSurjective (QuotientGroup.mk'_surjective Z)
  let HX : Subgroup (Bar2 L ⧸ Z) := (barImage L J).map Q
  have hSXcoe : (SX : Subgroup (Bar2 L ⧸ Z)) = (S : Subgroup (Bar2 L)).map Q :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Z) S
  have hSXfix : (SX : Subgroup (Bar2 L ⧸ Z)).map θ.toMonoidHom = SX := by
    rw [hSXcoe, hS]
    exact graph_map_eq htTL htL hθ
  have hHXfix : HX.map θ.toMonoidHom = HX :=
    graph_map_eq (hTJ ht) htL hθ
  have hSXH : (SX : Subgroup (Bar2 L ⧸ Z)) ≤ HX := by
    rw [hSXcoe, hS]
    exact Subgroup.map_mono hSJ
  have hdich : HX ≤ normalizer ((SX : Subgroup (Bar2 L ⧸ Z)) : Set _) ∨ HX = ⊤ := by
    rcases hsh with h3 | h4
    · exact graphL3_dich h3.2 θ hnd SX hSXfix HX hSXH hHXfix
    · exact graphSp4_dich
        (lieModel_quot_center_of_isSp4 h4 (commutator_bar2_eq_top hperf))
        θ hnd SX hSXfix HX hSXH hHXfix
  refine of_bar hTL hJ1 hJ2 ?_
  rw [← hS]
  exact dich_of_map_center (commutator_bar2_eq_top hperf) Z le_rfl S (barImage L J)
    (hS ▸ hSJ) (hSXcoe ▸ hdich)

end RankOneBorel

theorem kRankOneBorel_holds : KRankOneBorel := by
  intro G _ _ T L J _ _ hTL hperf hsh hJ1 hJ2 hTJ
  rcases hsh with ⟨n, h⟩ | ⟨L₁, L₂, h₁, h₂, hsup, hne, ⟨t, ht, hL₂⟩, n, hn⟩ |
    ⟨n, hsh, t, ht, hact⟩
  · exact RankOneBorel.holds_rankOne hTL h hJ1 hJ2
  · exact RankOneBorel.holds_product hTL h₁ h₂ hsup hne ht hL₂ hn hJ1 hJ2 hTJ
  · exact RankOneBorel.holds_graph hTL hperf hsh ht hact hJ1 hJ2 hTJ

end CFSG.LocalAnalysis.UniquenessCase.UC22
