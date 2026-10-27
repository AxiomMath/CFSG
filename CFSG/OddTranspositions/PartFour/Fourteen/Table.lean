module

public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
import CFSG.OddTranspositions.PartFour.Fourteen.ModelWreath
import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Plus
import CFSG.OddTranspositions.PartFour.Fourteen.TableSp
import CFSG.OddTranspositions.PartFour.Fourteen.TableMeetsSq
import CFSG.OddTranspositions.PartFour.Fourteen.TableE1
import CFSG.OddTranspositions.PartFour.Fourteen.TableWreath
import CFSG.OddTranspositions.BenderMeetsSq
import CFSG.Quasithin.Recognition.Stroth.BenderNoFF

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

theorem isBenderGroup_of_isSz {X : Type} [Group X] {f : ℕ} (h : CFSG.Quasithin.IsSz f X) :
    CFSG.BenderSuzuki.IsBenderGroup X := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  exact .isSuzuki a ha (e.trans ((CFSG.Quasithin.Stroth.suzukiGroupEquivSz a K hK).trans
    (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm)))

theorem ascListTable_of_rows
    (hP : ∀ (G : Type) [Group G] (D : Set G), QZ.IsO4Minus5Pair G D →
      CFSG.RankThree.GF2n.Tim79a.NoSqE1 D)
    (h5 : ∀ (G : Type) [Group G] [Finite G] (D : Set G) (n : ℕ), 4 ≤ n →
      ∀ b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5), (∀ x y, b x y = b y x) →
      (∀ x, (∀ y, b x y = 0) → x = 0) →
      CFSG.Open.fischerCentralQuotientModel D
        (Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1) →
      CFSG.RankThree.GF2n.Tim79a.NoSqE1 D) :
    AscListTable := by
  intro G _ _ D hS hrad _ h2 hsq hE1 hL
  have hZ : Subgroup.center G = ⊥ := hrad _ inferInstance (isSolvable_of_comm fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.mp a.2 b).symm))
  have hB : CFSG.BenderSuzuki.IsBenderGroup G → False := fun hB =>
    hsq (bender_meetsSq hB hS.isClass hS.oddT.1)
  rcases hL with h | ⟨s, hs, m, f, -, hf, hsp | hu | ho⟩ | ⟨n, hn, b, hb1, hb2, hb3⟩ |
      ⟨f, n, hf, ⟨e⟩⟩ | ⟨f, hSz⟩ | hBen | hPair
  · exact h
  · exact absurd (Fourteen.meetsSq_of_isSymplecticTransvection hS.isClass hZ hs hf hsp) hsq
  · exact absurd (meetsSq_of_isUnitaryTransvection hS.isClass hZ hs hf hu) hsq
  · exact absurd (noSqE1_of_isOrthReflection hS.isClass hZ hs ho) hE1
  · exact absurd (h5 G D n hn b hb1 hb2 hb3) hE1
  · rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | hn3
    · obtain ⟨s, hs⟩ := hS.nonempty
      exact absurd (eq_one_of_mulEquiv_l2Wreath_zero e s) (hS.oddT.ne_one hs)
    · obtain ⟨e'⟩ := nonempty_mulEquiv_psl2Model_of_l2Wreath_one e
      exact (hB (.isPSL2 f hf e')).elim
    · obtain ⟨s, hs, ho⟩ := exists_isOrthReflection_of_mulEquiv_l2Wreath_two hS hf e
      exact absurd (noSqE1_of_isOrthReflection hS.isClass hZ hs ho) hE1
    · exact absurd h2 (not_isPGroup_quotient_layer_of_l2Wreath hf hn3 e)
  · exact (hB (isBenderGroup_of_isSz hSz)).elim
  · exact (hB hBen).elim
  · exact absurd (hP G D hPair) hE1

end CFSG.OddTranspositions.PartFour
