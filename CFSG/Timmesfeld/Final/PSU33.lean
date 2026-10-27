module

public import CFSG.Open.Catalog
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_4
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.BenderSuzuki.MatrixGroups

namespace CFSG.Timmesfeld

namespace Final

local notation "𝔽₉" => GaloisField 3 (2 * 1)

local notation "σ₉" => frobeniusEquiv (GaloisField 3 (2 * 1)) 3

namespace GF9

theorem card : Nat.card 𝔽₉ = (3 ^ 1) ^ 2 := by
  rw [GaloisField.card 3 (2 * 1) (by norm_num)]
  norm_num

theorem frobenius_apply (x : 𝔽₉) : σ₉ x = x ^ 3 ^ 1 := by
  rw [pow_one, frobeniusEquiv_def]

theorem frobenius_involutive : Function.Involutive σ₉ := by
  intro x
  have := Fintype.ofFinite 𝔽₉
  have h : Fintype.card 𝔽₉ = 3 ^ 1 * 3 ^ 1 := by
    rw [← Nat.card_eq_fintype_card, card]
    ring
  rw [frobenius_apply, frobenius_apply, ← pow_mul, ← h, FiniteField.pow_card]

theorem card_fixed_frobenius : Nat.card {x : 𝔽₉ // σ₉ x = x} = 3 ^ 1 := by
  have h2 : (2 : 𝔽₉) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff 𝔽₉ 3 2).mp (by exact_mod_cast h)
    norm_num at this
  have hset : {x : 𝔽₉ | σ₉ x = x} = {0, 1, -1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, frobenius_apply,
      pow_one]
    constructor
    · intro h
      have h' : x * (x - 1) * (x + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h' | h'
      · rcases mul_eq_zero.mp h' with h' | h'
        · exact .inl h'
        · exact .inr (.inl (sub_eq_zero.mp h'))
      · exact .inr (.inr (eq_neg_of_add_eq_zero_left h'))
    · rintro (rfl | rfl | rfl) <;> ring
  have h01 : (0 : 𝔽₉) ≠ 1 := zero_ne_one
  have h1n : (1 : 𝔽₉) ≠ -1 := fun h => h2 (by linear_combination h)
  have h0n : (0 : 𝔽₉) ∉ ({1, -1} : Set 𝔽₉) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h01, fun h => h01 (by linear_combination -h)⟩
  change Nat.card ↥{x : 𝔽₉ | σ₉ x = x} = _
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem h0n, Set.ncard_pair h1n, pow_one]

end GF9

local notation "J₉" => RankTwoShapes.antidiagonalHermitianForm σ₉ GF9.frobenius_involutive

local notation "I₉" => RankTwoShapes.identityHermitianForm σ₉ GF9.frobenius_involutive

theorem projectiveSpecialUnitary_antidiagonal_eq :
    ProjectiveSpecialUnitaryMatrixGroup J₉ = Open.PSU3 3 1 := by
  refine congrArg (Subgroup.map _) ((Subgroup.closure_eq _).symm.trans (congrArg _ ?_))
  ext A
  rw [SetLike.mem_coe, HermitianForm.mem_specialSubgroup_iff, Set.mem_ofPred_eq]
  have hadj : HermitianForm.conjTranspose J₉ (A : Matrix (Fin 3) (Fin 3) 𝔽₉) =
      Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) 𝔽₉) j i ^ (3 ^ 1) := by
    ext i j
    rw [Matrix.of_apply, ← GF9.frobenius_apply]
    rfl
  rw [hadj]
  rfl

theorem nonempty_statedProj_statedSU_equiv_PSU3 :
    Nonempty (StatedProj (StatedSU 3 (3 ^ 1) 𝔽₉) ≃* Open.PSU3 3 1) := by
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_b_standard_hermitian_basis
    I₉ (3 ^ 1) GF9.card GF9.card_fixed_frobenius
  obtain ⟨e⟩ := RankTwoShapes.nonempty_projectiveSpecialUnitary_equiv_of_gram I₉ J₉ P rfl hP
  refine ⟨(RankTwoShapes.statedProjEquivMap _).trans ((MulEquiv.subgroupCongr ?_).trans
    (e.trans (MulEquiv.subgroupCongr projectiveSpecialUnitary_antidiagonal_eq)))⟩
  rw [RankTwoShapes.statedSU_eq_specialSubgroup (3 ^ 1) σ₉ GF9.frobenius_involutive
    GF9.frobenius_apply]

end Final

theorem nonempty_mulEquiv_PSU3_of_lieModel {G : Type} [Group G]
    (h : LieModel G .PSU 3 3 1) : Nonempty (G ≃* Open.PSU3 3 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 3 (2 * 1))
  have hc : Fintype.card K = Fintype.card (GaloisField 3 (2 * 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Final.GF9.card]
  obtain ⟨e'⟩ := Final.nonempty_statedProj_statedSU_equiv_PSU3
  exact ⟨e.trans ((Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 3 (3 ^ 1)).trans e')⟩

end CFSG.Timmesfeld
