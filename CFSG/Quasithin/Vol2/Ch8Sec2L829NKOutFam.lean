module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Syl
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Base
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Out

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.U31521
open CFSG.ProperTwoGeneratedCore.RootCenter

theorem nk_l3_out (n : ℕ) (hn : 2 ≤ n) (X : Type) [Group X] (hX : IsPSL 3 2 n X) :
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → UOut X (Subgroup.normalizer (S : Set X)) := by
  intro S hS y _ hfix
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hX
  let φ : X ≃* projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let Q : Sylow 2 X := hS.2.1.toSylow hi
  have hQ : (Q : Subgroup X) = S := rfl
  have h1 : y = 1 := by
    refine CFSG.Quasithin.L3Aut.l3ModelAut_holds K n hn hK X φ Q y ?_
    intro z hz _
    rw [hQ] at hz
    exact hfix z hz
  exact ⟨1, by rw [h1, map_one]⟩

theorem nk_u3_out (n : ℕ) (hn : 2 ≤ n) (X : Type) [Group X] (hX : IsPSU 3 2 n X) :
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → UOut X (Subgroup.normalizer (S : Set X)) := by
  intro S hS y _ hfix
  haveI : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let R : Sylow 2 X := hS.2.1.toSylow hi
  have hR : (R : Subgroup X) = S := rfl
  have hSN : S ≤ Subgroup.normalizer (S : Set X) := Subgroup.le_normalizer
  have hRC := rootCenterData_of_isPSU hn hX R
  have hSfix : ∀ x ∈ (R : Subgroup X), y x = x := by
    intro x hx
    rw [hR] at hx
    exact hfix x (hSN hx)
  have hUR : omegaU (R : Subgroup X) ≤ (R : Subgroup X) :=
    fun x hx => ((hRC.center_iff x).1 hx).1
  have hmap : (R : Subgroup X).map y.toMonoidHom = (R : Subgroup X) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hyr : y r = r := hSfix r hr
      show y r ∈ (R : Subgroup X)
      rw [hyr]
      exact hr
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, hSfix x hx⟩
  have hyA : y ∈ rootCenterAut (R : Subgroup X) (omegaU (R : Subgroup X)) :=
    ⟨hmap, fun u hu => hSfix u (hUR hu)⟩
  obtain ⟨z, -, hyz⟩ := hRC.fix_eq y hyA hSfix
  exact ⟨z, hyz⟩

end CFSG.Quasithin.H13.L829NK
