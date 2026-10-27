module

public import CFSG.Quasithin.Vol2.Ch12Sec9Statements
public import CFSG.Quasithin.Vol2.Ch12Sec5Statements
public import CFSG.RankThree.PartTwo.Sec4.Census.Blocks46
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

theorem not_lieModel_psl_six_of_evenRank {G : Type} [Group G] [Finite G]
    (he : CFSG.Assembly.evenRank G ≤ 2) : ¬ LieModel G .PSL 6 2 1 := by
  intro h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK2])
  let e' : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 6) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 6 K).symm
  have h3 := CFSG.RankThree.PartTwo.Sec4.Census.three_le_localRank_PSL_of_six_le (K := K)
    (n := 6) le_rfl
  have h4 := CFSG.RankThree.PartTwo.Census.localRank_le_of_mulEquiv e'.symm Nat.prime_three
  have h5 := CFSG.RankThree.OddKernel.localRank_le_evenRank (G := G) Nat.prime_three
    (by norm_num)
  omega

theorem natural_of_modules12_2_2 (h1251 : Stmt12_5_1) (h12634 : Stmt12_6_34)
    {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {n : ℕ} (hH : Hyp1223 G T L V)
    (hn : n = 4 ∨ n = 5)
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    [IsMulCommutative ↥V] (hmod : Modules12_2_2 L V) :
    ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1 := by
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := Nat.card_congr e.toEquiv
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    center_eq_bot_of_mulEquiv_sl (by omega) e
  have hcardn : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160 ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 9999360 := by
    rcases hn with rfl | rfl
    · exact Or.inl (hQ.trans card_sl_four_zmod_two)
    · exact Or.inr (hQ.trans card_sl_five_zmod_two)
  rcases hmod with ⟨n', hn', ⟨e'⟩, hnat⟩ | ⟨⟨e'⟩, -, -⟩ | ⟨⟨e'⟩, -, -⟩ |
      ⟨m, hm5, hm8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, -⟩ | ⟨hU, -⟩ | ⟨-, hZ3, -, -⟩
  · have hnn : n' = n := by
      have h := hQ.symm.trans (Nat.card_congr e'.toEquiv)
      rcases hn' with rfl | rfl | rfl <;> rcases hn with rfl | rfl
      · rw [card_sl_four_zmod_two, card_sl_three_zmod_two] at h
        omega
      · rw [card_sl_five_zmod_two, card_sl_three_zmod_two] at h
        omega
      · rfl
      · rw [card_sl_five_zmod_two, card_sl_four_zmod_two] at h
        omega
      · rw [card_sl_four_zmod_two, card_sl_five_zmod_two] at h
        omega
      · rfl
    subst hnn
    exact ⟨inferInstance, hnat⟩
  · exfalso
    have hQ' := Nat.card_congr e'.toEquiv
    rw [card_sl_three_zmod_two] at hQ'
    omega
  · rcases hn with rfl | rfl
    · exfalso
      have hQ' := Nat.card_congr e'.toEquiv
      rw [card_sl_five_zmod_two] at hQ'
      rw [card_sl_four_zmod_two] at hQ
      omega
    · exact h1251 G T L V hH ⟨e'⟩
  · have hc := card_eq_of_surjective_alternating hH.quasisimple hZ hm5 φ hφ
    rcases hn with rfl | rfl
    · have hm : m = 8 := eq_eight_of_card_alternating hm5 hm8 (by
        rw [← hc, hQ, card_sl_four_zmod_two])
      subst hm
      obtain ⟨α⟩ := nonempty_mulEquiv_sl_two_of_lieModel
        ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
          (alternatingGroup (Fin 8))).2 ⟨MulEquiv.refl _⟩)
      have hφ' : Function.Surjective (α.toMonoidHom.comp φ) := α.surjective.comp hφ
      have hker' :
          (α.toMonoidHom.comp φ).ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
        rw [← hker]
        ext x
        simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
          Function.comp_apply, map_eq_one_iff _ α.injective]
      obtain ⟨-, -, -, hnat⟩ := (stmt12_6_34_iff.mp h12634) G T L V hH ⟨_, hφ', hker'⟩
      exact hnat
    · exact (card_alternating_ne_five hm5 hm8 (by rw [← hc, hQ, card_sl_five_zmod_two])).elim
  · exfalso
    have hc := card_eq_of_surjective_alternating hH.quasisimple hZ (by norm_num) φ hφ
    rw [nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    omega
  · exfalso
    have hc := card_of_lieModel_psu_three_three hU
    omega
  · exfalso
    rw [hZ, Subgroup.card_bot] at hZ3
    omega

theorem exists_cx1291 (h1222 : Stmt12_2_2) (h1251 : Stmt12_5_1) (h12634 : Stmt12_6_34)
    {G : Type} [Group G] [Finite G] {T L : Subgroup G} {n : ℕ} (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : QuasithinUnique.quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hex : ¬ QT13Excluded G) (hmax : quasithinIsMaximalLocal T L)
    (hf : quasithinIsFaithfulLocal T L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hn : n = 4 ∨ n = 5) (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL n 2 1)
    (hsel : n = 4 → ¬ ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧
      quasithinIsFaithfulLocal T K ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 5 2 1) :
    ∃ V : Subgroup G, Cx1291 G T L V n := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel hlin
  have hnotAlt : ¬ Alt12_2_2 G := fun h => hex (qt13Excluded_of_alt12_2_2 h)
  rcases h1222 G T hsimple hnonab hqtke hT with hA | h3
  · exact absurd hA hnotAlt
  obtain ⟨hTL, ⟨V, hV⟩, hall⟩ := h3 L hmax hf hq
  have hH : Hyp1223 G T L V := ⟨hsimple, hnonab, hqtke, hT, hnotAlt, hmax, hf, hq, hTL, hV⟩
  obtain ⟨-, -, -, hc, hmod⟩ := hall V hV
  refine ⟨V, ⟨hH, by omega, ⟨e⟩, natural_of_modules12_2_2 h1251 h12634 hH hn e hmod, ?_,
    fun h => hex (Or.inr (Or.inr (Or.inl h))),
    fun h => hex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))⟩, hn, ?_⟩
  · rcases hn with rfl | rfl
    · exact fun h => hex (Or.inr (Or.inl (Or.inr h)))
    · exact not_lieModel_psl_six_of_evenRank hqtke.2.2
  · rintro h4 ⟨K, hKmax, hKf, hKq, ⟨eK⟩⟩
    exact hsel h4 ⟨K, hKmax, hKf, hKq, lieModel_psl_of_mulEquiv_sl_zmod_two (by norm_num) eK⟩

end CFSG.Quasithin.H13
