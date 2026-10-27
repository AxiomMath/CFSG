module

public import CFSG.Quasithin.Vol2.Ch11SecGOdd2
public import CFSG.Quasithin.Vol2.Ch11SecDFacts2
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecD551D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem centralizer_V₃_le (hCard : SecD.CardVFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1) (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n)
    {V₁ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) :
    Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hn := h.one_lt
  rcases h1151 G T L I n h with hSL3 | hSp4
  · rw [((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).1 hSL3]
    exact Subgroup.centralizer_le_normalizer _
  · intro x hx
    by_contra hxN
    have hC : ¬ Subgroup.centralizer (V₃ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
      fun hle => hxN (hle hx)
    have hr := E3.rParam_le_mQuot (SecA.IsVi.le_fsuV hV₃) hC
    have hVcard := (hCard G T L I n hset).2 hSp4
    have hV₃card : Nat.card V₃ = 2 ^ (3 * n) := by
      have h1 := SecA.IsVi.relIndex_eq hV₃
      rw [hset.cV, Subgroup.relIndex_bot_left] at h1
      rw [h1, mul_comm]
    have hsplit := E3.card_eq_two_pow_mul (SecA.isPGroup_fsuV h) (SecA.IsVi.le_fsuV hV₃)
    rw [hVcard, hV₃card, ← pow_add] at hsplit
    have hm : E3.mQuot (fsuV T I) V₃ = n := by
      have := Nat.pow_right_injective (le_refl 2) hsplit
      omega
    rw [hm] at hr
    obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
    by_cases hG2 : KindG2 L (fsuV T I) n
    · rcases (h1122 G T L I n (2 * n) V₁ V₂ h hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.1 with h3 | h3
      · have h4 : ((2 * n : ℕ) : ℕ∞) < (n : ℕ∞) := lt_of_lt_of_le h3 hr
        have h5 : 2 * n < n := by exact_mod_cast h4
        omega
      · exact SecA.kind_not_SL3_Sp4 (by omega) h3.1 hSp4
    · rcases (h1122 G T L I n n V₁ V₂ h hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)).2.2.1 with h3 | h3
      · exact absurd (lt_of_lt_of_le h3 hr) (lt_irrefl _)
      · exact SecA.kind_not_SL3_Sp4 (by omega) h3.1 hSp4

theorem inf_centralizer_le_of_le (hCard : SecD.CardVFact) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1)
    (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n) {V₁ V₃ Y : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₃ : IsVi T L I n 3 V₃) (hY : V₃ ≤ Y) :
    KOf L V₁ V₁ ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (LOf L V₁ : Set G) := by
  intro x hx
  have hxV₃ : x ∈ Subgroup.centralizer (V₃ : Set G) := Subgroup.centralizer_le hY hx.2
  have hxV := centralizer_V₃_le hCard h1102 h1110 h1122 h1141 h1151 h hV₁ hV₃ hxV₃
  exact SecD.mem_normalizer_lOf (SecA.normalizer_fsuV_le h331 h hxV)
    (SecD.kOf_le_normalizer (SecD.lOf_le_normalizer L V₁) hx.1)

theorem inf_centralizer_UH_le (hCard : SecD.CardVFact) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1) (h1151 : Stmt11_5_1)
    (h : Hyp11 G T L I n) {V₁ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₃ : IsVi T L I n 3 V₃) :
    KOf L V₁ V₁ ⊓ Subgroup.centralizer (conjClosure V₃ (KOf L V₁ V₁ ⊔ T) : Set G) ≤
      Subgroup.normalizer (LOf L V₁ : Set G) :=
  inf_centralizer_le_of_le hCard h331 h1102 h1110 h1122 h1141 h1151 h hV₁ hV₃ (le_conjClosure _ _)

theorem conjClosure_lOf_kOf (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    conjClosure (LOf L V₁) (KOf L V₁ V₁) = KOf L V₁ V₁ := by
  have hK := SecD.kOf_cComp h1110 h1112 h hV₁
  set K := KOf L V₁ V₁ with hKdef
  have hLK : LOf L V₁ ≤ K := le_conjClosure _ _
  have hK'le : conjClosure (LOf L V₁) K ≤ K :=
    conjClosure_le fun g hg x hx => K.mul_mem (K.mul_mem hg (hLK hx)) (K.inv_mem hg)
  have hsub : IsSubnormal (conjClosure (LOf L V₁) K) (Subgroup.normalizer (V₁ : Set G)) :=
    IsSubnormal.step hK'le ((Subgroup.normal_subgroupOf_iff_le_normalizer hK'le).mpr
      (le_normalizer_conjClosure _ _)) hK.2.2.1
  have hK'1 : conjClosure (LOf L V₁) K ≠ ⊥ := fun h0 =>
    SecD.lOf_ne_bot h1110 h hV₁ (le_bot_iff.mp (h0 ▸ le_conjClosure _ _))
  by_contra hne
  exact hK.2.2.2 _ (lt_of_le_of_ne hK'le hne) hK'1
    (SecD.conjClosure_perfect (perfectCore_perfect _)) hsub

theorem false_of_transv_kt (hTrans : FactTransv11_5_8) (hCard : SecD.CardVFact)
    (hTI : SecD.PointsTIFact) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1112 : Stmt11_1_2) (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1151 : Stmt11_5_1) (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n)
    {V₁ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃)
    (hne : KOf L V₁ V₁ ≠ LOf L V₁) {A : Subgroup G} (hAH : A ≤ KOf L V₁ V₁ ⊔ T)
    (hA2 : IsPGroup 2 A) (hAO : ¬ A ≤ pCoreOf 2 (KOf L V₁ V₁ ⊔ T))
    (hAY : E3.mQuot (conjClosure V₃ (KOf L V₁ V₁ ⊔ T))
      (conjClosure V₃ (KOf L V₁ V₁ ⊔ T) ⊓ Subgroup.centralizer (A : Set G)) ≤ 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set H₁ := K ⊔ T with hH₁def
  set UH := conjClosure V₃ H₁ with hUHdef
  have hV₃V := SecA.IsVi.le_fsuV hV₃
  have hY : IsElemAbelian 2 UH :=
    F7.isElemAbelian_mono (isElemAbelian_U h1157 h hV₁) (conjClosure_mono hV₃V le_rfl)
  have hYH : UH ≤ H₁ := conjClosure_le fun x hx v hv =>
    H₁.mul_mem (H₁.mul_mem hx ((hV₃V.trans ((SecA.fsuV_le_T h).trans le_sup_right)) hv))
      (H₁.inv_mem hx)
  have hCY := inf_centralizer_UH_le hCard h331 h1102 h1110 h1122 h1141 h1151 h hV₁ hV₃
  have hsimple : IsSimpleGroup G := h.fsu.simple
  have hloc := (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  have hsq : CFSG.SectionRank.IsSQTKCat ↥H₁ := hloc H₁ (inH_kt h hV₁).2
  have hHK : H₁ ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer
    ((SecA.IsVi.le_normalizer hV₁).trans (SecD.normalizer_le_normalizer_kOf L V₁ V₁))
  have hT := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (le_sup_right : T ≤ H₁)
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hn2 : n = 2 := by
    obtain ⟨K'', hLK'', hK'', hNK'', -, hor⟩ :=
      h1112 G T L I n 1 V₁ V₁ V₂ X h (Or.inl rfl) hV₁ hV₁ hV₂ hX
    have hKK'' := SecD.kOf_eq_of_cComp hLK'' hK'' hNK'' (SecD.lOf_ne_bot h1110 h hV₁)
    rcases hor with heq | ⟨-, hn2, -⟩
    · exact absurd (hKK''.trans heq.symm) hne
    · exact hn2
  have hTN := SecA.IsVi.le_normalizer hV₁
  have hsylN : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
      (Subgroup.normalizer (V₁ : Set G)) := by
    rw [inf_eq_left.mpr hTN]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
  obtain ⟨K', hLK', hK', hNK', hcase'⟩ := h1111 G T L I n 1 V₁ V₁ h hV₁
    (Or.inl ⟨rfl, SecA.IsVi.ne_bot h hV₁ le_rfl, le_rfl, hsylN⟩)
  have hKK' : K = K' := SecD.kOf_eq_of_cComp hLK' hK' hNK' (SecD.lOf_ne_bot h1110 h hV₁)
  rw [← hKK'] at hcase'
  have hlist : List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) 2 ∨
      List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hcase' with heq | h2 | h3
    · exact absurd heq.symm hne
    · exact Or.inl (hn2 ▸ h2)
    · exact Or.inr h3.2
  have hlt : LOf L V₁ < K := lt_of_le_of_ne (le_conjClosure _ _) (Ne.symm hne)
  have hcase : Case11_1_2One K ∨
      ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases (h1141 G T L I n V₁ X h hV₁ hX).2.1 K
        (SecD.kOf_cComp_centralizer hTI h1102 h1110 h1112 h1141 h1143 h hV₁) hlt with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1.1
  have hL₁q : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(LOf L V₁) ⧸ CFSG.pCore 2 ↥(LOf L V₁) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, hF, hFf, hFc, he⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
    exact ⟨F, hF, hFf, by rw [hFc, hn2]; norm_num, he⟩
  exact hTrans G H₁ K T (LOf L V₁) UH A hsq le_sup_left hHK hT rfl
    (SecD.kOf_cComp h1110 h1112 h hV₁).2.1 hlist hcase (le_conjClosure _ _)
    (perfectCore_perfect _) hL₁q (conjClosure_lOf_kOf h1110 h1112 h hV₁) hYH
    (le_normalizer_conjClosure _ _) hY hCY hAH hA2 hAO hAY

theorem false_of_odd (hCor : R1CorankFact) (h331 : Stmt3_3_1)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1) (h1151 : Stmt11_5_1) (h1155 : Stmt11_5_5)
    (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ V₃ H₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) (hinH : InH (LOf L V₁ ⊔ T) H₁)
    (hHM : ¬ H₁ ≤ Subgroup.normalizer (L : Set G))
    (hHN : H₁ ≤ Subgroup.normalizer (V₁ : Set G))
    (hsix : ∀ A : Subgroup G, A ≤ ROf T L V₁ → IsElemAbelian 2 A →
      E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 1)
    (hbotH : ∀ g : G, ¬ fsuV T I ≤ conjSub g (pCoreOf 2 H₁) →
      (∃ k ∈ H₁, conjClosure (fsuV T I) H₁ ≤ conjSub (g * k) (ROf T L V₁)) →
        V₁ ⊓ conjSub g V₁ = ⊥)
    (hlast : ∀ A : Subgroup G, A ≤ H₁ → IsPGroup 2 A → ¬ A ≤ pCoreOf 2 H₁ →
      E3.mQuot (conjClosure V₃ H₁)
        (conjClosure V₃ H₁ ⊓ Subgroup.centralizer (A : Set G)) ≤ 1 → False)
    (hb : Odd (critDist (L ⊔ T ⊔ H₁) (L ⊔ T) H₁ (fsuV T I))) :
    False := by
  set V := fsuV T I with hVdef
  have hamal := amalgamHypV_of_inH h331 h3228 h hinH hHM
  have hV := SecA.fsuV_ne_bot h
  have hTH : T ≤ H₁ := le_sup_right.trans hinH.1
  have hb2 := two_le_critDist_of_le_pCoreOf hamal hV
    (fsuV_le_pCoreOf_of_le h1157 h hV₁ hTH hHN)
  obtain ⟨g, hgH, hgO, ⟨k, hk, hUg⟩, ⟨k', hk', hU⟩⟩ := exists_odd_data hamal hV hb hb2
  have hR := pCoreOf_inf_le_ROf_of_le h hinH.1
  have hU' : ∃ k ∈ H₁, conjClosure V H₁ ≤ conjSub (g * k) (ROf T L V₁) :=
    ⟨k', hk', hU.trans (conjSub_mono _ hR)⟩
  obtain ⟨hDV, hidx⟩ := le_centralizer_D hCor h1102 h1110 h1122 h1141 h1151 h1155 h1157 h
    hV₁ hV₃ hinH hHM hHN hsix (hbotH g hgO hU') ⟨k, hk, hUg.trans (conjSub_mono _ hR)⟩ hU'
  set UH := conjClosure V₃ H₁ with hUHdef
  set A := conjSub g⁻¹ V with hAdef
  have hAH : A ≤ H₁ := by
    rw [hAdef, conjSub_le_iff, inv_inv]
    exact hgH
  have hAO : ¬ A ≤ pCoreOf 2 H₁ := by
    rw [hAdef, conjSub_le_iff, inv_inv]
    exact hgO
  have hA2 : IsPGroup 2 A := F7.isPGroup_conjSub (SecA.isPGroup_fsuV h)
  have hAY : E3.mQuot UH (UH ⊓ Subgroup.centralizer (A : Set G)) ≤ 1 := by
    have h1 : UH ⊓ conjSub g⁻¹ (pCoreOf 2 H₁) ≤ UH ⊓ Subgroup.centralizer (A : Set G) := by
      have h2 := conjSub_mono g⁻¹ hDV
      rw [conjSub_inf, conjSub_conjSub_inv, ← conjSub_centralizer] at h2
      exact le_inf inf_le_left h2
    refine (E3.mQuot_mono h1).trans ?_
    have h3 := mQuot_conjSub g⁻¹ (conjSub g UH) (conjSub g UH ⊓ pCoreOf 2 H₁)
    rw [conjSub_inf, conjSub_conjSub_inv] at h3
    rw [h3]
    exact hidx
  exact hlast A hAH hA2 hAO hAY

end CFSG.Quasithin.Vol2.Ch11.SecG
