module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieGen
public import CFSG.Quasithin.H13.NQCatLieOverRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.Quasithin.H13.FiveNorm.LieSp4

open Matrix CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Field K] [Finite K]

theorem powOver_projSp [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) :
    PowOver (StatedProj (StatedSp 2 K)) (projUnipotent 2 K) (Nat.card K - 1) := by
  intro H hUH hH x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have hN := NQCat.solvOver_projSp hK4 H hUH hH hx
  rw [normalizer_projUnipotent 2 (by norm_num)] at hN
  obtain ⟨b, hb, rfl⟩ := hN
  refine ⟨b ^ (Nat.card K - 1), ?_, map_pow _ _ _⟩
  have h1 : diagHom 2 K (⟨b, hb⟩ ^ (Nat.card K - 1)) = 1 := by
    rw [map_pow]
    funext i
    apply Units.ext
    rw [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (diagHom 2 K ⟨b, hb⟩ i).ne_zero
  have h2 : (⟨b, hb⟩ ^ (Nat.card K - 1) : borelSubgroup 2 K) ∈ (diagHom 2 K).ker := h1
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem fiveInner_noFiveOver_projSp [CharP K 2] (hk : Nat.card K = 4) :
    FiveInner (StatedProj (StatedSp 2 K)) ∧ NoFiveOver (StatedProj (StatedSp 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hk]; norm_num
  obtain ⟨-, hO⟩ := Lin2.sp4OutCyclic K 2 hcard (by norm_num)
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  have hK4 := NQCat.exists_finset_card_four_of_card (k := 2) le_rfl (by rw [hk]; norm_num)
  exact ⟨fiveInner_of_card_outer_coprime (by rw [hO]; norm_num),
    noFiveOver_of_powOver hU (by rw [hk]; norm_num) (powOver_projSp hK4)⟩

theorem fiveRigid_quot_of_isPSp4 {X : Type} [Group X] (hX : CFSG.Quasithin.IsPSp4 2 2 X) :
    FiveRigid (X ⧸ Subgroup.center X) := by
  have hs : IsSimpleGroup X :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 2 2 hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hk : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  obtain ⟨hi, hn⟩ := fiveInner_noFiveOver_projSp hk
  exact fiveRigid_quotCenter_of_mulEquiv e hi hn

end CFSG.Quasithin.H13.FiveNorm.LieSp4
