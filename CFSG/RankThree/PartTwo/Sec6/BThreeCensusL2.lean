module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open Matrix


theorem three_dvd_card_pgl2 {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0) :
    3 ∣ Nat.card (ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
  rw [CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hm]
  by_cases hp3 : p = 3
  · subst hp3
    exact Dvd.dvd.mul_right (dvd_pow_self 3 hm) _
  · refine Dvd.dvd.mul_left ?_ _
    have hp : p.Prime := Fact.out
    have hpm : p % 3 = 1 ∨ p % 3 = 2 := by
      have h1 : p % 3 ≠ 0 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h)).symm
      omega
    have h2 : p ^ 2 % 3 = 1 := by
      rcases hpm with h | h <;> simp [Nat.pow_mod, h]
    have h3 : p ^ (2 * m) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod, h2, one_pow, Nat.one_mod]
    have hpos : 1 ≤ p ^ (2 * m) := Nat.one_le_pow _ _ hp.pos
    omega

theorem isSolvable_of_not_three_dvd_psl2 {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ f) (H : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) F))
    (h3 : ¬ 3 ∣ Nat.card H) : Group.IsSolvable H := by
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hab | ⟨z, -, -, hcyc⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNab, -, hC, -, -, hNC⟩ | ⟨m, hm, -, ⟨e⟩⟩ | ⟨m, hm, -, ⟨e⟩⟩
  · have : IsMulCommutative H := hab.toIsMulCommutative
    let : CommGroup H := { (inferInstance : Group H) with mul_comm := fun a b => mul_comm' a b }
    infer_instance
  · let : CommGroup H := IsCyclic.commGroup
    infer_instance
  · have : NeZero z := ⟨fun hz0 => by
      rw [hz0, mul_zero] at hz
      exact Nat.card_pos.ne' hz⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exfalso
    exact h3 (by rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; decide)
  · exfalso
    exact h3 (by rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]; decide)
  · exfalso
    exact h3 (by rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; decide)
  ·
    have hNab' : IsMulCommutative N := hNab.toIsMulCommutative
    let : CommGroup N := { (inferInstance : Group N) with mul_comm := fun a b => mul_comm' a b }
    let : CommGroup C := IsCyclic.commGroup
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      intro x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
      have hh : h ∈ ((N ⊔ C : Subgroup H) : Set H) := by rw [hNC]; exact Subgroup.mem_top h
      rw [Subgroup.normal_mul, Set.mem_mul] at hh
      obtain ⟨n, hn, c, hc, rfl⟩ := hh
      refine ⟨⟨c, hc⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    let : CommGroup (H ⧸ N) :=
      { (inferInstance : Group (H ⧸ N)) with
        mul_comm := fun x y => by
          obtain ⟨x', rfl⟩ := hsurj x
          obtain ⟨y', rfl⟩ := hsurj y
          rw [← map_mul, ← map_mul, mul_comm x' y'] }
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  · exfalso
    exact h3 (by rw [Nat.card_congr e.toEquiv]; exact KFacts.three_dvd_card_psl2 _)
  · exfalso
    exact h3 (by rw [Nat.card_congr e.toEquiv]; exact three_dvd_card_pgl2 hm)

theorem threePrimeB3_projSL_two {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) :
    ThreePrimeB3 (CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p e)) := by
  refine threePrimeB3_of_mulEquiv (Sec4.projSLEquivPSLn 2 (GaloisField p e))
    (threePrimeB3_of_isSolvable fun Y hY3 => ?_)
  exact isSolvable_of_not_three_dvd_psl2 (GaloisField.card p e (by omega)) Y hY3

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
