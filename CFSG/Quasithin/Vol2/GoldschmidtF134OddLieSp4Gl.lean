module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5
public import CFSG.Quasithin.Vol2.F134LieSp4Borel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporDef
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.Quasithin.F134.Sp4

variable {K : Type} [Field K]

theorem not_dvd_card_of_charTwo [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card K := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem dvd_pred_of_le_stabilizer_two [Finite K] [CharP K 2] {P : Subgroup (StatedSp 2 K)}
    {p a : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) (hPa : Nat.card P = p ^ a)
    (hexp : ∀ x ∈ P, x ^ p = 1) : p ∣ Nat.card K - 1 := by
  by_contra hq31
  have hq : ¬ p ∣ Nat.card K := not_dvd_card_of_charTwo hp.out hp2
  set Q := P.subgroupOf (stabilizer 2 K (flag 2 K 2))
  let ρ : Q →* GL (Fin 2) K := (blockHom (K := K)).toHomUnits.comp Q.subtype
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq'
    have h1 : blockHom (q : stabilizer 2 K (flag 2 K 2)) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hq')
      simpa [ρ] using this
    have h2 := sq_eq_one_of_blockHom (q : stabilizer 2 K (flag 2 K 2)) h1
    have h3 : ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) ^ p = 1 :=
      hexp _ (Subgroup.mem_subgroupOf.mp q.2)
    have hq1 : ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) = 1 :=
      S5.eq_one_of_sq_eq_one_of_pow_eq_one (j := 1) hp.out hp2 (by rw [← sq]; exact h2)
        (by rw [pow_one]; exact h3)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext hq1)
  have hQa : Nat.card Q = p ^ a := by
    rw [← hPa]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPF).toEquiv
  have hRa : Nat.card ρ.range = p ^ a := by
    rw [← hQa]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hRexp : ∀ x ∈ ρ.range, x ^ p = 1 := by
    rintro _ ⟨q, rfl⟩
    rw [← map_pow]
    have : q ^ p = 1 := Subtype.ext (Subtype.ext (hexp _ (Subgroup.mem_subgroupOf.mp q.2)))
    rw [this, map_one]
  have hR : IsPGroup p ρ.range := IsPGroup.of_card (n := a) hRa
  exact not_isCyclic_of_card_pow ha hRa hRexp (isCyclic_of_isPGroup_GL_two hq hq31 hR)

end CFSG.Quasithin.H13.NQCore.Psp4
