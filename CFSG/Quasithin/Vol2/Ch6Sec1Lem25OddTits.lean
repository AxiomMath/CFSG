module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddA
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Quasithin.Recognition.CertTitsOvergroup
import CFSG.Quasithin.Vol2.KGFactAutSylowSmall
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.Quasithin.H13.OddSyl

open CFSG.QuasithinUnique CFSG.Quasithin

theorem center_eq_bot_of_simple {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply conj_injective hS hna
  ext y
  rw [MulAut.conj_apply, MulAut.conj_apply, ← Subgroup.mem_center_iff.1 hz y]
  group

theorem oddSylowTits_holds :
    OddSylowTits := by
  intro S _ _ hS hna hm P hP d r hr hr2 hd hdP hx _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 hm
  have hN : Subgroup.normalizer
      ((CFSG.Sporadic.Schreier.Tits.titsSylow : Subgroup ↥CFSG.Sporadic.Schreier.Tits.titsD) :
        Set ↥CFSG.Sporadic.Schreier.Tits.titsD) =
      (CFSG.Sporadic.Schreier.Tits.titsSylow : Subgroup ↥CFSG.Sporadic.Schreier.Tits.titsD) := by
    rw [CFSG.Sporadic.Schreier.Tits.coe_titsSylow]
    exact le_antisymm CFSG.Quasithin.titsSD_normalizer_le Subgroup.le_normalizer
  have hsn : AutSylowSelfNorm S :=
    KGAutSyl.autSylowSelfNorm_of (center_eq_bot_of_simple hS hna)
      (CFSG.LieType.SteinbergBR.OddSylow.exists_selfNormalizing_of_equiv e _ hN)
      (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 hm).1
  exact false_of_autOddNormCent hS hna hsn.autOddNormCent hP hr hr2 hd hdP hx

end CFSG.Quasithin.H13.OddSyl
