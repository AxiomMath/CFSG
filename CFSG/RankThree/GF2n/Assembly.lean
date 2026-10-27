module

public import CFSG.RankThree.GF2n.Statements
import CFSG.RankThree.GF2n.QTwo
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.NormalizedElementarySubgroup
public import CFSG.CGT.Timmesfeld75.Statements

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {G : Type} [Group G]

theorem catalog_of_statedClassicalModel {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : Catalog G :=
  Or.inr (Or.inr (Or.inl ⟨t, n, p, f, h⟩))

theorem catalog_of_alternating {k : ℕ} (hk : 5 ≤ k)
    (h : Nonempty (G ≃* alternatingGroup (Fin k))) : Catalog G :=
  Or.inr (Or.inl ⟨k, hk, h⟩)

theorem catalog_of_isSporadic {s : TauCeti.SporadicName} (h : NativeSporadic.IsSporadic G s) :
    Catalog G :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨s, h⟩)))

theorem catalog_of_gf2TypeList (h : GF2TypeList G) : Catalog G := by
  rcases h with ⟨n, -, h⟩ | ⟨n, -, h⟩ | ⟨s, n, -, -, h⟩ | ⟨s, -, h⟩ | ⟨p, f, m, -, -, -, -, -, h⟩ |
    ⟨s, n, -, h⟩ | ⟨k, hk, h⟩ | ⟨s, -, h⟩
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · refine catalog_of_alternating ?_ h
    rcases hk with rfl | rfl | rfl <;> norm_num
  · exact catalog_of_isSporadic h

theorem catalog_of_listGroup (h : ListGroup G) : Catalog G := by
  rcases h with ⟨m, s, -, -, h⟩ | ⟨s, -, h⟩ | ⟨s, -, -, h⟩ | ⟨k, hk, -, h⟩ | h | h | h
  · exact catalog_of_statedClassicalModel h
  · exact catalog_of_statedClassicalModel h
  · exact lieModel_catalog G _ _ _ _ h
  · exact catalog_of_alternating (by omega) h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h
  · exact catalog_of_isSporadic h

theorem catalog_of_strothSmithList {f : ℕ} (h : StrothSmithList G f) : Catalog G := by
  rcases h with h | ⟨s, m, -, -, h⟩ | ⟨s, -, h⟩
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h

theorem catalog_of_gf2nTypeConclusion {M B : Subgroup G} (h : GF2nTypeConclusion M B) :
    Catalog G := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, ⟨-, f, m, -, -, h⟩ | ⟨-, h⟩⟩ | ⟨-, -, -, f, -, h⟩
  · exact catalog_of_gf2TypeList h
  · exact catalog_of_statedClassicalModel h
  · exact catalog_of_listGroup h
  · exact catalog_of_strothSmithList h

variable [Finite G]

theorem ne_bot_of_maximal {M B : Subgroup G} (hM : IsPLocal 2 M)
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B) : B ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP1, hP2, rfl⟩ := hM
  set Z : Subgroup G := (Subgroup.center P).map P.subtype with hZdef
  have hZc : IsMulCommutative Z := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    apply Subtype.ext
    have := Subgroup.mem_center_iff.mp hx' y'
    simpa using congrArg Subtype.val this.symm
  have hNZ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G) := fun g hg =>
    mem_normalizer_map_subtype_of_characteristic hg (Subgroup.center P)
  set E := RankThree.PartTwo.Source.omegaSubgroup Z hZc 2 with hEdef
  have hEab : Assembly.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hx.2⟩
    have h := hZc.is_comm.comm (⟨x, x.2.1⟩ : Z) ⟨y, y.2.1⟩
    rw [Subtype.ext_iff] at h
    exact h
  have hEN : E ≤ Subgroup.normalizer (P : Set G) := fun x hx =>
    Subgroup.le_normalizer (Subgroup.map_subtype_le _ hx.1)
  have hNE : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (E : Set G) := fun g hg =>
    RankThree.PartTwo.Source.mem_normalizer_omegaSubgroup hZc 2 (hNZ hg)
  have hPnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have hZnt : Nontrivial (Subgroup.center P) := hP2.center_nontrivial
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 (by
    obtain ⟨k, hk⟩ := (hP2.to_subgroup (Subgroup.center P)).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hk
    rw [hk]
    exact dvd_pow_self 2 hk0)
  have hcE : ((c : P) : G) ∈ E := by
    refine ⟨Subgroup.mem_map_of_mem P.subtype c.2, ?_⟩
    have : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    simpa using congrArg (fun t : Subgroup.center P => ((t : P) : G)) this
  have hc1 : ((c : P) : G) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hE1 : E ≠ ⊥ := fun h => hc1 (by rw [h] at hcE; exact (Subgroup.mem_bot.mp hcE))
  intro hB1
  have hEB : E ≤ B := hB.le_of_ge ⟨hEN, hNE, hEab⟩ (hB1 ▸ bot_le)
  exact hE1 (le_bot_iff.mp (hB1 ▸ hEB))

theorem card_eq_two_or_four_le {M B : Subgroup G} (hM : IsPLocal 2 M)
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B) : Nat.card B = 2 ∨ 4 ≤ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB1 := ne_bot_of_maximal hM hB
  obtain ⟨k, hk⟩ := (PartTwo.Sec5.isPGroup_of_isElemAbelian hB.prop.2.2).exists_card_eq
  have hlt : 1 < Nat.card B := (Subgroup.one_lt_card_iff_ne_bot B).mpr hB1
  rw [hk] at hlt ⊢
  rcases k with _ | _ | k
  · simp at hlt
  · left; norm_num
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Finite G] in
theorem normalizer_eq_of_maximal {M B : Subgroup G} (hM : IsMaximalTwoLocal M) (hB1 : B ≠ ⊥)
    (hB2 : IsPGroup 2 B) (hMB : M ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup.normalizer (B : Set G) = M := by
  by_contra hne
  exact hM.2 _ (lt_of_le_of_ne hMB (Ne.symm hne)) ⟨B, hB1, hB2, rfl⟩

@[expose] def GF2TypeStatementKP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ t : G, orderOf t = 2 →
      CFSG.Open.GLASymplecticType
        (inSubgroup generalizedFitting (Subgroup.centralizer ({t} : Set G))) →
      GF2TypeList G

theorem gf2TypeList_of_card_eq_two_at
    (hGF2 : ∀ t : G, orderOf t = 2 →
      CFSG.Open.GLASymplecticType
        (inSubgroup generalizedFitting (Subgroup.centralizer ({t} : Set G))) → GF2TypeList G)
    (hchar : IsCharacteristicPType G 2) {M B : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B) (hB2 : Nat.card B = 2) :
    CFSG.Open.GLASymplecticType (inSubgroup (pCore 2) M) ∧ GF2TypeList G := by
  obtain ⟨z, hzo, hBz, hMz⟩ := exists_eq_centralizer_of_card_eq_two hM hB hB2
  have hsymp := glaSymplecticType_of_card_eq_two hB hB2 hBz hMz.le
  refine ⟨hsymp, hGF2 z hzo ?_⟩
  have hF : generalizedFitting M = pCore 2 M := generalizedFitting_eq_pCore hchar hM.1
  have hFG : inSubgroup generalizedFitting M = inSubgroup (pCore 2) M := by
    unfold inSubgroup
    rw [hF]
  rw [← hMz, hFG]
  exact hsymp

theorem gf2nType_of_inputs_KP (hGF2 : GF2TypeStatementKP) (hTim75 : NodeStatement)
    (hTim81 : Tim81UnitaryStatement) (hSS : StrothSmithStatement)
    (hTri : Tim78TrichotomyStatement) : GF2nTypeStatement := by
  intro G _ _ _ hnonab hK hchar M hM B hB hTI
  have hconc : GF2nTypeConclusion M B := by
    rcases card_eq_two_or_four_le hM.1 hB with h2 | h4
    · exact Or.inl ⟨h2, gf2TypeList_of_card_eq_two_at (hGF2 G hnonab hK hchar) hchar hM hB h2⟩
    · rcases hTri G hnonab hchar M hM B hB hTI h4 with hWQ | ⟨hgen, hspec⟩
      · by_cases hWM : WeaklyClosedIn B M
        · have hB1 := ne_bot_of_maximal hM.1 hB
          have hN : Subgroup.normalizer (B : Set G) = M := normalizer_eq_of_maximal hM hB1
            (PartTwo.Sec5.isPGroup_of_isElemAbelian hB.prop.2.2) hB.prop.2.1
          have hlist : ListGroup G := hTim75 G hnonab B hB.prop.2.2 h4 (fun g => hTI g⁻¹)
            (fun g hg => hWM.2 g⁻¹ (hg.trans hN.le))
          exact Or.inr (Or.inl ⟨h4, hWQ, Or.inr ⟨hWM, hlist⟩⟩)
        · obtain ⟨f, hf, -, m, hm, hmod⟩ := hTim81 G hnonab hK hchar M hM B hB hTI h4 hWQ hWM
          exact Or.inr (Or.inl ⟨h4, hWQ, Or.inl ⟨hWM, f, m, hf, hm, hmod⟩⟩)
      · obtain ⟨f, hf, -, hlist⟩ := hSS G hnonab hK M hM (generalizedFitting_eq_pCore hchar hM.1)
          B hB hTI h4 hgen hspec
        exact Or.inr (Or.inr ⟨h4, hgen, hspec, f, hf, hlist⟩)
  exact ⟨hconc, catalog_of_gf2nTypeConclusion hconc⟩

end CFSG.RankThree.GF2n
