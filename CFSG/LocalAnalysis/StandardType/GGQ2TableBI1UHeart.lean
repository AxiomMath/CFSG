module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Tor
import CFSG.LocalAnalysis.StandardType.GGTDLabels
import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggQ2TableBI1FailOn_unitaryHeart :
    GGQ2TableBI1FailOn fun lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 3 ∣ lab.rank + 1 := by
  refine ggQ2TableBI1FailOn_of_tor ?_ ?_
  · rintro ⟨t, r, n⟩ ⟨ht, h4, hdvd⟩
    subst ht
    exact ⟨Or.inl ⟨rfl, h4⟩, Or.inl ⟨rfl, hdvd⟩⟩
  · rintro ⟨t, r, n⟩ hlab hq ⟨ht, h4, hdvd⟩
    subst ht
    have h4' : 4 ≤ r := by simpa using h4
    have hdvd' : 3 ∣ r + 1 := by simpa using hdvd
    have hn1 : n = 1 := by
      have hnpos : 1 ≤ n := by simpa using hlab.1
      have hq2 : n < 2 := by simpa only [GGLabQTwo] using hq
      omega
    subst hn1
    have h5or8 : r = 5 ∨ 8 ≤ r := by omega
    refine ⟨r, CartanMatrix.A r, CoxeterMatrix.A r, ?_, ?_, ?_, ?_⟩
    · simp only [GGQ2LabelWeyl]
      exact ⟨Equiv.refl _, rfl⟩
    · exact Or.inl ⟨r, Equiv.refl _, by omega, Or.inl rfl⟩
    · exact ggIntCartan_A r
    · rcases h5or8 with rfl | h8
      · have hLift : LargeEvenLabelAll ⟨.twA, 5, 1⟩ fun R _ _ _ =>
            GGTorusLift 3 (ggUnitaryTorusRank 3 (5 + 1)) R :=
          largeEvenLabelAll_torusLift_twA (lab := ⟨.twA, 5, 1⟩) hlab rfl Nat.prime_three
            (by norm_num)
        have hTor : LargeEvenLabelAll ⟨.twA, 5, 1⟩ fun R _ I _ =>
            GGTorusTorW 3 4 (2 ^ 1 + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) R I :=
          ggTorusTorW_uni_six_three_label_all (f := 1) (by norm_num) (by norm_num)
        refine (largeEvenLabelAll_and hLift hTor).mono ?_
        rintro R _ I F ⟨hL, hT⟩
        exact ⟨ggUnitaryTorusRank 3 (5 + 1), 4, by norm_num [ggUnitaryTorusRank], hL, hT⟩
      · have hE : ggTorEnn 3 ⟨.twA, r, 1⟩ = 1 := by
          norm_num [ggTorEnn]
        have hM3 : ggTorM ⟨.twA, r, 1⟩ = 3 := by
          norm_num [ggTorM]
        have hTor := ggTorusTorW_uni_label (p := 3) (n := 1) (l := r) Nat.prime_three hlab h4
          hdvd' (by norm_num [ggTorM]) (by omega)
        have hTor' : LargeEvenLabelAll ⟨.twA, r, 1⟩ fun R _ I _ =>
            GGTorusTorW 3 (r - 2) 3 r (CartanMatrix.A r) (CoxeterMatrix.A r) R I := by
          simpa [hE, hM3, Nat.sub_sub] using hTor
        have hLift : LargeEvenLabelAll ⟨.twA, r, 1⟩ fun R _ _ _ =>
            GGTorusLift 3 (ggUnitaryTorusRank 3 (r + 1)) R :=
          largeEvenLabelAll_torusLift_twA (lab := ⟨.twA, r, 1⟩) hlab rfl Nat.prime_three
            (by norm_num)
        have hE2 : ggUnitaryTorusRank 3 (r + 1) = r - 2 := by
          simp only [ggUnitaryTorusRank, if_pos hdvd']
          omega
        have hLift' : LargeEvenLabelAll ⟨.twA, r, 1⟩ fun R _ _ _ =>
            GGTorusLift 3 (r - 2) R := by
          simpa only [hE2] using hLift
        refine (largeEvenLabelAll_and hLift' hTor').mono ?_
        rintro R _ I F ⟨hL, hT⟩
        exact ⟨r - 2, r - 2, by omega, hL, hT⟩

end CFSG.StandardType

end
