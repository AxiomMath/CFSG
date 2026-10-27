module

public import CFSG.RankThree.PartTwo.Sec8.Hering611Branch
public import CFSG.RankThree.PartTwo.Sec8.Hering611Fuse
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFU4
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFJ3Aut
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolFinal
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}

@[expose] def KF611A9FuseSym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
    (S K : Subgroup G), Cfg611 G A c L E T d S K →
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* alternatingGroup (Fin 9)) → c ∉ K →
      IsConj c d ∨ IsConj c d⁻¹

theorem false_of_fusion_sym (F : Frame611 G A c L E T d)
    (hrank : ∀ X : Subgroup G, CFSG.Assembly.IsElemAbelian 3 X →
      X ≤ Subgroup.centralizer ({d} : Set G) → Nat.card X ≤ 3 ^ 6)
    {x : G} (hx : x = c ∨ (x ∈ L ∧ x ^ 3 = 1)) (hconj : IsConj x d ∨ IsConj x d⁻¹) : False := by
  rcases hconj with h | h
  · exact false_of_fusion F hrank hx h
  · obtain ⟨B, hBe, hBcard, hxB⟩ := exists_E37_containing F hx
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    set B' := B.map (MulAut.conj g).toMonoidHom with hB'
    have hB'e : CFSG.Assembly.IsElemAbelian 3 B' :=
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ B hBe
    have hdinvB' : d⁻¹ ∈ B' := ⟨x, hxB, by simpa [MulAut.conj_apply] using hg⟩
    have hdB' : d ∈ B' := by simpa using B'.inv_mem hdinvB'
    have hB'd : B' ≤ Subgroup.centralizer ({d} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hB'e.1.is_comm.comm ⟨y, hy⟩ ⟨d, hdB'⟩))
    have h' := hrank B' hB'e hB'd
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj g).injective, hBcard] at h'
    norm_num at h'

theorem item82TwoPSL2NineCore_of_narrow
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9) (h66 : Sec6.Item6_6)
    (h41 : Sec4.Item4_1LargePrime) (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1)
    (hAut : AutJ3CoverRank) (hF : KF611InspectField) (hSp62 : KF611InvolSp62K)
    (hA9 : KF611A9FuseSym) (hJC : KF611J3CoverFuse) (hJ : KF611J3) :
    Item82Proof.Item82TwoPSL2NineCore := by
  have hI : KF611Invol := kF611Invol_of h45 hSp62
  intro G _ _ A c L a h h81 hAN hiso hcard
  obtain ⟨e₁⟩ := hiso
  obtain ⟨E, T, d, S, K, C⟩ := Sec6.Hering611.exists_cfg h45 h48 h49 h h81 hAN e₁ hcard
  have hIfalse : (StatedClassicalModel (K ⧸ aschbacherSolvableCore 3 K) .PSp 3 2 1 ∨
      (Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* alternatingGroup (Fin 9)) ∧ c ∈ K) ∨
      (Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSp 2 (GaloisField 2 3)) ∧
        KFacts.InducesStdKind K c .field)) → False := fun hprem => by
    obtain ⟨t, ht2, hind⟩ := hI G A c L E T d S K C hprem
    exact false_of_field_involution h45 h611 C.toFrame611 ht2 hind
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hdA : d ∈ A := C.mem_E.2 C.d_mem.1
  have hd1 : d ≠ 1 := fun h => C.d_not_mem (h ▸ Subgroup.one_mem _)
  have hnotE : A ∉ partTwoE G := fun hA => by
    have := hA.2.1
    omega
  have hstd : Sec21.Sec21Std G A := ⟨C.standing, C.mem_S, fun hAE => absurd hAE hnotE⟩
  obtain ⟨-, hlist⟩ := Sec21.Item21Late2Proof.list211_of_mem_lZeroStarAt h417 h611 h45 h66 h41
    hstd hdA hd1 C.mem_K
  have h81' : Nat.card A = 3 ^ 4 := by rw [C.card_A]; norm_num
  have h27 : ¬ Nat.card A = 3 ^ 3 := by rw [C.card_A]; norm_num
  rcases hlist with h1 | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨-, h5, -⟩ | ⟨h2, -⟩ | ⟨-, h7, -⟩ |
    ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨-, h12, -⟩ | ⟨-, h13, -⟩
  ·
    rcases hF G A c L E T d S K C h1 with ⟨n, hn, ⟨φK⟩⟩ | ⟨hSp, hcf⟩
    · exact Sec6.Hering611.false_of_L2 h45 C hn φK
    · exact hIfalse (Or.inr (Or.inr ⟨hSp, hcf⟩))
  · exact h27 h2
  · exact h27 h2
  · exact h27 h2
  ·
    obtain ⟨hA9iso⟩ := h5
    by_cases hcK : c ∈ K
    · exact hIfalse (Or.inr (Or.inl ⟨⟨hA9iso⟩, hcK⟩))
    · exact false_of_fusion_sym C.toFrame611
        (fun X hX hXd => kF611RankA9_of h45 G A c L E T d S K C ⟨hA9iso⟩ X hX hXd) (Or.inl rfl)
        (hA9 G A c L E T d S K C ⟨hA9iso⟩ hcK)
  · exact h27 h2
  ·
    rcases h7 with hJiso | hJcov
    ·
      obtain ⟨U, hU1, hU2, hAU⟩ := hJ G A c L E T d S K C hJiso
      have hle := Sec5.card_le_of_le_normalizer C.standing.evenRank_eq hU1 hU2 hAe hAU
      rw [C.card_A] at hle
      omega
    · obtain ⟨a, haA, haL, -, hconj⟩ := hJC G A c L E T d S K C hJcov
      exact false_of_fusion C.toFrame611
        (fun X hX hXd => kF611RankJ3Cover_of h45 hAut G A c L E T d S K C hJcov
          X hX hXd)
        (Or.inr ⟨haL, hAe.2 a haA⟩) hconj
  · exact h27 h2
  · exact h27 h2
  · exact h27 h2
  · exact h27 h2
  ·
    exact kF611InspectU4_of h45 G A c L E T d S K C h12
  ·
    exact hIfalse (Or.inl h13)

theorem item82TwoPSL2NineCore_of_narrow_cert
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9) (h66 : Sec6.Item6_6)
    (h41 : Sec4.Item4_1LargePrime) (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1)
    (hF : KF611InspectField) (hSp62 : KF611InvolSp62K)
    (hA9 : KF611A9FuseSym) (hJC : KF611J3CoverFuse) (hJ : KF611J3) :
    Item82Proof.Item82TwoPSL2NineCore :=
  item82TwoPSL2NineCore_of_narrow h45 h48 h49 h66 h41 h417 h611 autJ3CoverRank_holds hF hSp62 hA9
    hJC hJ

end CFSG.RankThree.PartTwo.Sec8.Hering611
