module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSubline
import CFSG.LocalAnalysis.WeakClosure81.FourteenEightBenderA
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.GH74.Uniqueness.SU.SU0SUS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3 IsL2)

theorem f4data_of_isU3 {G : Type}
    [Group G] [Finite G] (h : IsU3 G 2) (S : Sylow 2 G) :
    Nat.card ↥((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) = 4 ∧
    CentralKData (S : Subgroup G) ((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) ∧
    ((∀ x ∈ (S : Subgroup G), x * x = 1 → x ∈ centralizer ((S : Subgroup G) : Set G)) ∨
      RankTwoParabData (S : Subgroup G)) := by
  classical
  have hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (n := 3) (by norm_num) h
  obtain ⟨e⟩ : Nonempty (G ≃* CFSG.Theory.Comparator.PSU3Model 2) :=
    (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff G 2 le_rfl).1 hM
  have hB : CFSG.GH74.Uniqueness.Bender.BenderType G 2 3
      ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) :=
    CFSG.GH74.Uniqueness.Bender.BenderType.unitary 2 (by norm_num) e
  let Z : Subgroup G := (S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)
  obtain ⟨t, hcore⟩ := hB.exists_benderCore S
  have hcardZ : Nat.card Z = 4 := by
    have hc := hcore.card_center
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    simpa [Z, CFSG.GH74.Uniqueness.Bender.rootCenter] using hc
  have hinv : ∀ x ∈ (S : Subgroup G), x * x = 1 →
      x ∈ centralizer ((S : Subgroup G) : Set G) := by
    intro x hx hxx
    have hxroot : x ∈ CFSG.GH74.Uniqueness.Bender.rootCenter (S : Subgroup G) := by
      by_cases hx1 : x = 1
      · subst hx1
        rw [CFSG.GH74.Uniqueness.Bender.rootCenter]
        exact Subgroup.mem_inf.mpr ⟨S.one_mem, Subgroup.one_mem _⟩
      · refine hcore.center_of_involution x ?_ ?_
        · simpa [CFSG.GH74.Uniqueness.Bender.borel] using Subgroup.le_normalizer hx
        · have hdvd : orderOf x ∣ 2 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hxx)
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
          · exact absurd h1 (by intro hh; exact hx1 (orderOf_eq_one_iff.mp hh))
          · exact h2
    have hxroot' : x ∈ (S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G) := by
      simpa [CFSG.GH74.Uniqueness.Bender.rootCenter] using hxroot
    exact (Subgroup.mem_inf.mp hxroot').2
  obtain ⟨J₀, Q₀, hJ₀e, hQ₀J₀, hQ₀card, hQ₀comm, hQ₀sq⟩ := hB.exists_subline_unitary
  obtain ⟨eJ⟩ := hJ₀e
  have hQe : IsElemAbelian 2 Q₀ := by
    refine ⟨IsMulCommutative.of_comm (fun x y => ?_), fun x hx => ?_⟩
    · exact Subtype.ext (hQ₀comm x x.2 y y.2)
    · rw [pow_two]; exact hQ₀sq x hx
  obtain ⟨S₀, hQ₀eq⟩ := exists_sylow_eq_rootCenter_of_benderType hB hQe hQ₀card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
  have hSmap : (S : Subgroup G) = (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  let K : Subgroup G := (J₀ : Subgroup G).map (MulAut.conj g).toMonoidHom
  have hL2K : IsL2 ↥K 2 := by
    have heq : (J₀ : Subgroup G) ≃* K :=
      Subgroup.equivMapOfInjective J₀ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact CFSG.GH74.GLS.lieModel_psl_two_two_two_of_mulEquiv (heq.symm.trans eJ)
  have hZK : Z ≤ K := by
    have hZmap : Z = (CFSG.GH74.Uniqueness.Bender.rootCenter (S₀ : Subgroup G)).map
        (MulAut.conj g).toMonoidHom := by
      rw [show Z = CFSG.GH74.Uniqueness.Bender.rootCenter
          ((S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom) from by
        rw [← hSmap]; rfl]
      exact CFSG.GH74.Uniqueness.Bender.rootCenter_map (MulAut.conj g) (S₀ : Subgroup G)
    rw [hZmap]
    exact Subgroup.map_mono (hQ₀eq ▸ hQ₀J₀)
  have hN : normalizer ((Z : Subgroup G) : Set G) ≤ normalizer ((S : Subgroup G) : Set G) := by
    simpa [Z, CFSG.GH74.Uniqueness.Bender.rootCenter, CFSG.GH74.Uniqueness.Bender.borel]
      using hcore.normalizer_rootCenter_le
  have hSyl : IsSylowIn 2 (S : Subgroup G) (⊤ : Subgroup G) := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hCKD : CentralKData (S : Subgroup G) Z :=
    centralKData_of_subline hSyl hL2K hcardZ hZK hN
  exact ⟨hcardZ, hCKD, Or.inl hinv⟩

theorem exists_sylow_eq_of_isSylowIn_top {M : Type} [Group M] [Finite M] {S : Subgroup M}
    (hS : IsSylowIn 2 S (⊤ : Subgroup M)) : ∃ P : Sylow 2 M, (P : Subgroup M) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hS.isPGroup.toSylow ?_, IsPGroup.toSylow_coe _ _⟩
  have := hS.not_dvd_relIndex
  rwa [Subgroup.relIndex_top_right] at this

theorem choiceOfKOn_shapeU3 :
    ChoiceOfKOn ShapeU3 :=
  choiceOfKOn_of_top ShapeU3 fun Y _ _ L hL =>
    ⟨↥L, inferInstance, MulEquiv.refl _, choiceOfKTop_of_data _ fun S hS => by
      obtain ⟨P, rfl⟩ := exists_sylow_eq_of_isSylowIn_top hS
      exact f4data_of_isU3 hL.2 P⟩

end CFSG.LocalAnalysis.WeakClosure81

end
