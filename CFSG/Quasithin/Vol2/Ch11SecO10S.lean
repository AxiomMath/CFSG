module

public import CFSG.Quasithin.Vol2.Ch11SecO10Q
public import CFSG.Quasithin.Vol2.Ch11SecO10R
public import CFSG.Quasithin.Vol2.Ch11SecA14Lines
public import CFSG.Quasithin.Vol2.Ch10SecB4Aux
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

omit [Finite G] in
theorem autOn_eq_of_isSimple {K B W : Subgroup G} (hKB : K ≤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hB : IsSimpleGroup ↥(autOn B W))
    (hne : autOn K W ≠ ⊥) : autOn K W = autOn B W := by
  have := SecA.autOn_normal_subgroupOf (V := W) hBK
  exact SecA.eq_of_normal_of_isSimpleGroup (SecA.autOn_mono hKB) hB hne

theorem kz_a7_cases (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (h701 : Stmt7_0_1)
    (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) (hc : Conf11_4_2 T L I n V₁ z) {I' : Subgroup G}
    (hfsu : FSU G T (kz L V₁ z) I')
    (hJ : ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T))
    (hA7 : IsAlt 7 (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
      IsHat (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ↥(alternatingGroup (Fin 7))) :
    (I' = fsuV T I' ∧ Nonempty (↥(autOn (kz L V₁ z) (fsuV T I')) ≃* alternatingGroup (Fin 7)) ∧
      ∃ _ : IsMulCommutative ↥(fsuV T I'),
        AlternatingNatural (V := ↥(fsuV T I')) (autOn (kz L V₁ z) (fsuV T I')) ⊤ ⊥ 7) ∨
    (I' = fsuV T I' ∧
      Nonempty (↥(autOn (kz L V₁ z ⊔ T) (fsuV T I')) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥(fsuV T I') = 2 ^ 4) ∨
    (I' ⊓ Subgroup.centralizer (kz L V₁ z : Set G) = ⊥ ∧
      Nonempty (↥(autOn (kz L V₁ z) (fsuV T I')) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥I' = 2 ^ 4 ∧ (∃ t ∈ T, t ∉ Subgroup.normalizer (I' : Set G)) ∧
      ∀ t ∈ T, t ∉ Subgroup.normalizer (I' : Set G) →
        fsuV T I' = I' ⊔ CFSG.conjugate I' t ∧ I' ⊓ CFSG.conjugate I' t = ⊥ ∧
          ¬ IsXSectionIso₂ (kz L V₁ z) I' ⊥ (CFSG.conjugate I' t) ⊥) := by
  set K := kz L V₁ z with hKdef
  obtain ⟨-, hq, -, hTK, -⟩ := kz_setting hF hS hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨hKV, hTV, hO, hne⟩ := fsuV_spec h701 hfsu hTK
  have : Finite (MulAut ↥(fsuV T I')) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨π, hπs, hπk⟩ := exists_central_epi_autOn hq hKV hO hne
  have hY : IsA7Order ↥(autOn K (fsuV T I')) := card_of_central_quot hA7 π hπs hπk
  have hne1 : autOn K (fsuV T I') ≠ ⊥ := by
    intro h0
    have h1 := hY
    rw [h0] at h1
    rcases h1 with h1 | h1 <;> rw [Subgroup.card_bot] at h1 <;> omega
  have hL0 : conjClosure K T = K := Ch10.SecB.conjClosure_eq_self hTK
  have hKT : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hsimple : ∀ {X : Type} [Group X], IsSimpleGroup X →
      Nonempty (↥(autOn (K ⊔ T) (fsuV T I')) ≃* X) →
      Nonempty (↥(autOn K (fsuV T I')) ≃* X) := by
    intro X _ hX ⟨e⟩
    have : IsSimpleGroup ↥(autOn (K ⊔ T) (fsuV T I')) := e.isSimpleGroup
    rw [autOn_eq_of_isSimple le_sup_left hKT this hne1]
    exact ⟨e⟩
  obtain ⟨-, -, h3⟩ := h325 G T K I' hfsu hL0.symm
  rcases h3 with ⟨hI, -⟩ | ⟨hI, -⟩ | ⟨hcv, hlist, hT', hswap⟩
  rotate_right
  ·
    rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, hcard⟩
    · exact (not_sl3 hY hF e).elim
    · exact (not_sp4 hY hF e).elim
    · exact (not_alt_five_six hY (Or.inr rfl) e).elim
    · exact (not_sl_zmod_two hY (Or.inl rfl) e).elim
    · exact (not_sl_zmod_two hY (Or.inr rfl) e).elim
    · exact Or.inr (Or.inr ⟨hcv, ⟨e⟩, hcard, hT', fun t ht hnt =>
        ⟨(hswap t ht hnt).2.1, (hswap t ht hnt).2.2.1, (hswap t ht hnt).2.2.2⟩⟩)
  all_goals
    have hfsu' : FSU G T K (conjClosure I' T) := by
      rw [← hI]
      exact hfsu
    have hVc : conjClosure I' T = conjClosure (conjClosure I' T) T :=
      (Ch10.SecB.conjClosure_eq_self hTV).symm
    obtain ⟨_, h8⟩ := h328 G T K (conjClosure I' T) hfsu' hL0.symm hVc
      (isFFModule_fsuV_kz hF hS hF43 h701 h1102 h1110 h1111 h1141 hc hfsu hJ)
    rcases h8 with ⟨m, -, F, _, _, hF, π', hπ'⟩ | (⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩) |
        ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | (⟨⟨e⟩, -⟩ | ⟨⟨e⟩, hnat⟩) |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, hcard⟩ | ⟨-, hcz, ⟨e⟩, -⟩ | ⟨m, hm, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ'
      exact (not_sl2 hY hF ((MulEquiv.ofBijective π' ⟨hinj, hπ'.1⟩).symm.trans
        (specialLinearGroupEquivStatedSL 2 F).symm)).elim
    · exact (not_sl3 hY hF e).elim
    · exact (not_sl3 hY (a := 1) (by rw [Nat.card_zmod]; norm_num) e).elim
    · exact (not_sp4 hY hF e).elim
    · exact (not_g2 hY hF e).elim
    · exact (not_alt_five_six hY (Or.inl rfl) e).elim
    · exact Or.inl ⟨hI, ⟨e⟩, inferInstance, hnat⟩
    · exact (not_alt_five_six hY (Or.inr rfl) e).elim
    · exact Or.inr (Or.inl ⟨hI, ⟨e⟩, hcard⟩)
    · exact (not_threeA6 hY hcz e).elim
    · obtain ⟨e'⟩ := hsimple (SecA.isSimpleGroup_SL_zmod_two (by omega)) ⟨e⟩
      exact (not_sl_zmod_two hY hm e').elim
    · exact (not_sl_zmod_two hY (Or.inl rfl) e).elim
    · obtain ⟨e'⟩ := hsimple (SecA.isSimpleGroup_SL_zmod_two (by norm_num)) ⟨e⟩
      exact (not_sl_zmod_two hY (Or.inr rfl) e').elim

end CFSG.Quasithin.Vol2.Ch11.O10
