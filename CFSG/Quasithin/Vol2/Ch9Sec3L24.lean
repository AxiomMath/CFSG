module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch9Setup

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem sup_eq_inf_of_hall {H K B : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hHK : H = K ⊔ T) (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hB : Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) (hBK : B ≤ K) :
    B ⊔ (T ⊓ K) = K ⊓ (H ⊓ fsuM T L) := by
  have hfsu := S.hyp.fsu
  set M := fsuM T L with hM
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTM : T ≤ M := Setup.T_le_fsuM
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hTHs : IsSylowTwoOf T H := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
  have hBX : B ≤ K ⊓ (H ⊓ M) := le_inf hBK hB.1
  have hBh' : Lin2.IsHallTwoPrimeOf B (K ⊓ (H ⊓ M)) := by
    obtain ⟨-, hBodd, k, hk⟩ := hB
    refine ⟨hBX, hBodd, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex B (K ⊓ (H ⊓ M)) (H ⊓ M) hBX inf_le_right
    have h3 : B.relIndex (K ⊓ (H ⊓ M)) ∣ 2 ^ k := by
      rw [← hk, ← h1]
      exact dvd_mul_right _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    exact ⟨j, hj⟩
  have hTKs' : IsSylowTwoOf (T ⊓ K) (K ⊓ (H ⊓ M)) :=
    Lin2.isSylowTwoOf_of_le_of_le hTKs
      (le_inf inf_le_right (le_inf (inf_le_left.trans hTH) (inf_le_left.trans hTM))) inf_le_left
  exact sup_eq_of_isHall_isSylow hBh' hTKs'

end Setup

end CFSG.Quasithin.H13.Ch9
