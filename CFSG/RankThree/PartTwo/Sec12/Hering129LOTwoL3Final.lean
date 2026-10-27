module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwo
public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Main
import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Mod
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

theorem ks129OTwoL3_holds :
    KS129OTwoL3 := by
  intro X _ _ hX hperf hex
  obtain ⟨p, e, hp, hp2, he, hiso⟩ := hex
  haveI := hperf
  obtain ⟨hθsol, -, hθ3, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hL : LData (X ⧸ aschbacherSolvableCore 3 X) :=
    ⟨isSimpleGroup_of_isoLThreePi he hp2 hiso, e9Q8_of_isoLThreePi he hiso,
      fourGroup_of_isoLThreePi he hp2 hiso, fun Y' _ _ Z _ hY' hZc hcop ⟨e'⟩ =>
        KFacts.KS14.ks18Mult_lThreePi Y' Z hY' hZc hcop
          ⟨p, e, hp, he, Sec8.Item82OneProof.isoLThreePi_of_mulEquiv e' hiso⟩⟩
  have hker : (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).ker =
      aschbacherSolvableCore 3 X := QuotientGroup.ker_mk' _
  have hle := ker_le_pCore_two_L3 hL (QuotientGroup.mk' (aschbacherSolvableCore 3 X))
    (QuotientGroup.mk'_surjective _) (by rw [hker]; exact hθsol) (by rw [hker]; exact hθ3)
    hX.localRank_lt
  rw [hker] at hle
  exact le_antisymm hle (hθO 2 Nat.prime_two (by norm_num))

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3
