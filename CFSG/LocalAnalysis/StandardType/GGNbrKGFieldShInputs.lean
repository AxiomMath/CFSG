module

public import CFSG.LocalAnalysis.StandardType.GGTorusFieldTransferSh
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGNbrKGF4ThreeAddHolds
import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGMain

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGF4FieldShInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .F4 → 3 ∣ 2 ^ lab.n + 1 →
    3 ∣ lab.n → LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) →
        ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ 3 = 1 → GGFixDataSh 3 3 I x

@[expose] def GGUnitSixFieldShInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twA → lab.rank = 5 →
    3 ∣ 2 ^ lab.n + 1 → 3 ∣ lab.n → LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) →
        ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ 3 = 1 → GGFixDataSh 3 3 I x

theorem ggNbrKGFieldF4_of_sh
    (hpc : GGRawPCyclicOn GGNotD4Three) (hF4 : GGF4FieldShInput) : GGNbrKGFieldF4 := by
  intro p lab hp hp2 hlab ⟨htag, hp3, hpq⟩ hpn
  subst hp3
  have hnot : GGNotD4Three 3 lab := by
    rintro ⟨h, -⟩
    rw [htag] at h
    exact absurd h (by decide)
  have hInn : LargeEvenLabelAll lab fun R _ I _ => ∀ g : R, MulAut.conj g ∈ I :=
    largeEvenLabelAll_inn_chevalley (Or.inr (Or.inr (Or.inr htag)))
  have hin : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp 3 3 R I :=
    largeEvenLabelAll_noLineComp_F4 ggNbrKGF4ThreeAdd_holds ⟨htag, hpq⟩
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) :=
    (hpc 3 hp hp2 lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hfix : LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ 3 = 1 → GGFixDataSh 3 3 I x :=
    hF4 lab hlab htag hpq hpn
  exact (largeEvenLabelAll_and hInn (largeEvenLabelAll_and hin (largeEvenLabelAll_and hcyc hfix))).mono
    fun R _ I F ⟨hi, hn', hc, hf⟩ hs hna =>
      ggTorusFieldTransferSh Nat.prime_three (by norm_num) hi (hn' hs hna) (hc hs hna) (hf hs hna)

theorem ggNbrKGFieldUnitSix_of_sh
    (hpc : GGRawPCyclicOn GGNotD4Three) (hU : GGUnitSixFieldShInput) : GGNbrKGFieldUnitSix := by
  intro p lab hp hp2 hlab ⟨htag, hrank, hp3, hpq⟩ hpn
  subst hp3
  have hnot : GGNotD4Three 3 lab := by
    rintro ⟨h, -⟩
    rw [htag] at h
    exact absurd h (by decide)
  have hInn : LargeEvenLabelAll lab fun R _ I _ => ∀ g : R, MulAut.conj g ∈ I :=
    largeEvenLabelAll_inn_twA hlab htag
  have hin : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp 3 3 R I :=
    (UnitSixThreeKG.ggNbrKGUnitSixThree_holds lab hlab htag hrank hpq).mono
      fun _ _ _ _ hn' hs hna => ggTorusNoLineComp_of_le Nat.prime_three.pos (Nat.zero_le 3) (hn' hs hna)
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) :=
    (hpc 3 hp hp2 lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hfix : LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ 3 = 1 → GGFixDataSh 3 3 I x :=
    hU lab hlab htag hrank hpq hpn
  exact (largeEvenLabelAll_and hInn (largeEvenLabelAll_and hin (largeEvenLabelAll_and hcyc hfix))).mono
    fun R _ I F ⟨hi, hn', hc, hf⟩ hs hna =>
      ggTorusFieldTransferSh Nat.prime_three (by norm_num) hi (hn' hs hna) (hc hs hna) (hf hs hna)

end CFSG.StandardType
