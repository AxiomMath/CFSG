module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.Quasithin.Vol2.F134Orders
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroupHolds
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.EvenBN.GMSK (not_three_dvd_card_of_lieModel_twistedB2)

variable {G : Type} [Group G] [Finite G]

theorem five_dvd_card_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz X n) :
    5 ∣ Nat.card X := by
  obtain ⟨a, rfl⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 h
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_of_isSz_two_pow h]
  apply Dvd.dvd.mul_left
  have h16 : (16 : ℕ) ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have e : ((2 : ℕ) ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  rw [e]
  omega

theorem three_dvd_card_of_lieModel_psl_two {X : Type} [Group X] {ℓ f : ℕ}
    (h : LieModel X .PSL 2 ℓ f) : 3 ∣ Nat.card X :=
  CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_two
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem not_lieModel_psl_two_of_isSz {X : Type} [Group X] {n ℓ f : ℕ} (h : IsSz X n) :
    ¬ LieModel X .PSL 2 ℓ f := fun h' =>
  not_three_dvd_card_of_lieModel_twistedB2 h (three_dvd_card_of_lieModel_psl_two h')

theorem not_isSU3_of_isSz {X : Type} [Group X] [Finite X] {n m : ℕ} (h : IsSz X n) :
    ¬ IsSU3 X m := by
  rintro ⟨-, hU3⟩
  have h3 : 3 ∣ Nat.card (X ⧸ Subgroup.center X) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel_PSU3 hU3
  exact not_three_dvd_card_of_lieModel_twistedB2 h (h3.trans (Subgroup.card_quotient_dvd_card _))

theorem center_eq_bot_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz X n) :
    Subgroup.center X = ⊥ := by
  have : IsSimpleGroup X :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hbot | htop
  · exact hbot
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h
    exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)

omit [Finite G] in
theorem isSz_bar2_map_conj {L : Subgroup G} {n : ℕ} (h : IsSz (Bar2 L) n) (g : G) :
    IsSz (Bar2 (L.map (MulAut.conj g).toMonoidHom)) n := by
  unfold IsSz at h ⊢
  let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.bar2Equiv e) h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
