module

public import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof
import CFSG.RankThree.PartOne.KFOUT3.CycCent
import CFSG.RankThree.PartOne.KFOUT3.CycMono
import CFSG.RankThree.PartOne.KFOUT3.SLCard
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.RankThree.PartOne.KFOUT3 (krylov)

@[expose] def cycMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cycPerm : Equiv.Perm (Fin 3) := finRotate 3

theorem cycPerm_pow_three : cycPerm ^ 3 = 1 := by decide

theorem cycPerm_ne_one : cycPerm ≠ 1 := by decide

theorem cycMat_monomial (K : Type) [Field K] :
    ∀ i k, k ≠ cycPerm i → cycMat K k i = 0 := by
  intro i k hk
  fin_cases i <;> fin_cases k <;> simp_all [cycMat, cycPerm]

theorem cycMat_det (K : Type) [Field K] : (cycMat K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [cycMat]

theorem cycMat_pow_three (K : Type) [Field K] : cycMat K ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def cycGL (K : Type) [Field K] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (cycMat K) (by rw [cycMat_det]; exact one_ne_zero)

theorem cycGL_pow_three (K : Type) [Field K] : cycGL K ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact cycMat_pow_three K

theorem units_eq_one_of_pow_three_pow {K : Type} [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K - 1) {u : Kˣ} {k : ℕ} (hu : u ^ (3 ^ k) = 1) : u = 1 := by
  have hd1 : orderOf u ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hu
  have hd2 : orderOf u ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard u
  have hcop : Nat.Coprime (3 ^ k) (Nat.card K - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact orderOf_eq_one_iff.mp this

theorem card_le_three_of_isElemAbelian {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : Nat.card K % 3 = 2) {E : Subgroup (GL (Fin 3) K)} (hES : E ≤ StatedSL 3 K)
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by
    have : 2 ≤ Nat.card K := by omega
    omega
  have hdet : IsUnit (cycGL K : Matrix (Fin 3) (Fin 3) K).det := by
    change IsUnit (cycMat K).det
    rw [cycMat_det]
    exact isUnit_one
  have hkr : IsUnit (krylov (cycGL K : Matrix (Fin 3) (Fin 3) K) (Pi.single 0 (1 : K))).det :=
    CFSG.RankThree.PartOne.KFOUT3.isUnit_det_krylov_of_monomial cycPerm_pow_three cycPerm_ne_one
      (cycMat_monomial K) hdet
  obtain ⟨-, U, hU, hUcyc, hUcard⟩ :=
    CFSG.RankThree.PartOne.KFOUT3.exists_cyc_threeElts h3 (cycGL_pow_three K) hkr
  have hUS : U ≤ StatedSL 3 K := by
    intro u hu
    obtain ⟨-, k, hk⟩ := (hU u).mp hu
    rw [CFSG.RankThree.PartOne.statedSL_eq_det_ker, MonoidHom.mem_ker]
    apply units_eq_one_of_pow_three_pow h3 (k := k)
    rw [← map_pow, hk, map_one]
  have hcardS : Nat.card (StatedSL 3 K) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) :=
    (Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toEquiv).symm
  have hUsyl : CFSG.ABGLocalTools.IsSylowOf 3 U (StatedSL 3 K) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hUS ?_
    rw [hUcard, hcardS, CFSG.RankThree.PartOne.KFOUT3.factorization_card_SL3 hq]
  have hE3 : IsPGroup 3 E := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hE.2 x hx
  obtain ⟨P, hP, hEP⟩ := exists_isSylowOf_le hE3 hES
  obtain ⟨g, -, rfl⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hUsyl hP
  have hPcyc : IsCyclic (U.map (MulAut.conj g).toMonoidHom) :=
    isCyclic_of_surjective (U.equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom
      (MulEquiv.surjective _)
  have hEcyc : IsCyclic E :=
    Subgroup.isCyclic_of_le hEP
  obtain ⟨x, hx⟩ := hEcyc.exists_generator
  have hcard : Nat.card E = orderOf x := by
    rw [← Nat.card_zpowers]
    have : Subgroup.zpowers x = ⊤ := by
      rw [eq_top_iff]
      intro y _
      exact hx y
    rw [this, Subgroup.card_top]
  have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hE.2 x x.2)
  rw [hcard]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)

theorem kFactL3OddThreeRank : KFactL3OddThreeRank := by
  intro n hn X _ _ ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n
  have hq : Nat.card F % 3 = 2 := by
    rw [GaloisField.card 2 n hn.pos.ne']
    exact two_pow_mod_three_of_odd hn
  set e' : X ≃* ↥(StatedSL 3 F) := e.trans (projSLEquivStatedSL hn)
  have hbot : CFSG.Open.IsElemAbelian 3 (⊥ : Subgroup X) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  refine csSup_le ⟨0, ⊥, bot_le, hbot, by rw [Subgroup.card_bot, pow_zero]⟩ ?_
  rintro k ⟨E, -, hEab, hEc⟩
  set E' : Subgroup (GL (Fin 3) F) := (E.map e'.toMonoidHom).map (StatedSL 3 F).subtype
  have hE'S : E' ≤ StatedSL 3 F := Subgroup.map_subtype_le _
  have hE'ab : CFSG.Open.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩⟩ := a
      obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩⟩ := b
      apply Subtype.ext
      change ((e' u : StatedSL 3 F) : GL (Fin 3) F) * e' v = e' v * e' u
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
        show u * v = v * u from congrArg Subtype.val (hEab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)]
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      change (((e' u : StatedSL 3 F) : GL (Fin 3) F)) ^ 3 = 1
      rw [← Subgroup.coe_pow, ← map_pow, hEab.2 u hu, map_one, Subgroup.coe_one]
  have hcard : Nat.card E' = 3 ^ k := by
    rw [Subgroup.card_map_of_injective (StatedSL 3 F).subtype_injective,
      Subgroup.card_map_of_injective e'.injective, hEc]
  have hle := card_le_three_of_isElemAbelian hq hE'S hE'ab
  rw [hcard] at hle
  by_contra hk
  push Not at hk
  have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem step208MSPair_of_bridge (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (h189 : Sec18.Item189) (h204 : Item204One) (h321 : Sec3.Item321Split) (hx : Step208X) :
    Step208MSPair :=
  step208MSPair_of hbridge kFactL3OddThreeRank h189 h204 h321 hx

end CFSG.RankThree.PartTwo.Sec20
