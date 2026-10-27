module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral Sylow subgroups from the D-group quotient clause

An `IsDGroup` supplies cyclic-or-dihedral Sylow two-subgroups.  If one were
cyclic, Burnside transfer would give a normal two-complement and hence a
two-group quotient by the odd core, contradicting `IsDGroupQuotient`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- An `IsDGroup` satisfying the non-two-group quotient clause has dihedral,
rather than cyclic, Sylow two-subgroups. -/
public theorem hasDihedralSylowTwo_of_isDGroup_of_isDGroupQuotient
    {G : Type u} [Group G] [Finite G]
    (hDG : IsDGroup G) (hDQ : IsDGroupQuotient G) :
    HasDihedralSylowTwo G := by
  have hcyclicOrDihedral : HasCyclicOrDihedralSylowTwo G := by
    rcases hDG with ⟨hSylow, _⟩ | ⟨hSylow, _⟩ |
        ⟨hSylow, _K, _hK, _L, _hLn, _hLi, _hLm⟩
    · exact hSylow
    · exact hSylow
    · exact hSylow
  have hnotQ : ¬ IsPGroup 2 (G ⧸ pPrimeCore 2 G) :=
    not_isPGroup_quotient_pPrimeCore_of_isDGroupQuotient hDQ
  intro S
  rcases hcyclicOrDihedral S with hcyclic | hdihedral
  · have hallCyclic : ∀ P : Sylow 2 G, IsCyclic P := by
      intro P
      exact (MulEquiv.isCyclic (Sylow.equiv P S)).mpr hcyclic
    have hcomp : HasNormalPComplement 2 G := by
      classical
      by_cases h2 : 2 ∣ Nat.card G
      · let P : Sylow 2 G := Classical.choice Sylow.nonempty
        have hmin : (Nat.card G).minFac = 2 :=
          (Nat.minFac_eq_two_iff (Nat.card G)).2 h2
        have hNC : Subgroup.normalizer (P : Set G) ≤
            Subgroup.centralizer (P : Set G) :=
          (hallCyclic P).normalizer_le_centralizer hmin
        have hPcenter : (P : Subgroup G) ≤
            centerIn (G := G) (Subgroup.normalizer (P : Set G)) := by
          intro s hs
          refine ⟨Subgroup.le_normalizer hs, ?_⟩
          change s ∈ Subgroup.centralizer
            (Subgroup.normalizer (P : Set G) : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
        exact hasNormalPComplement_of_sylow_le_center_normalizer
          (G := G) 2 P hPcenter
      · have hodd : Odd (Nat.card G) := by
          rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
          exact h2
        refine ⟨⊤, inferInstance, ?_, ?_⟩
        · simpa using hodd.coprime_two_left
        · intro x
          refine ⟨0, ?_⟩
          have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
            QuotientGroup.subsingleton_quotient_top
          simpa using (@Subsingleton.elim _ hsub x 1)
    exact (hnotQ
      (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 G hcomp)).elim
  · exact hdihedral

end CFSG.GorensteinWalter
