module

public import CFSG.RankThree.PartOne.SRC.Centralizer
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.RankThree.PartOne.SRC

open CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists


theorem rankFourCover_psu3 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 4 ≤ e) :
    RankFourCover p (StatedProj (StatedSU 3 (p ^ e) (GaloisField p (2 * e)))) := by
  classical
  have hp : p.Prime := Fact.out
  set K := GaloisField p (2 * e) with hKdef
  have hK : Nat.card K = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 : (2 : K) ≠ 0 := by
    have : ringChar K = p := ringChar.eq K p
    exact Ring.two_ne_zero (by rw [this]; exact hp2)
  obtain ⟨e₁⟩ := nonempty_sl2_mulEquiv_statedSU_two (r := p) (f := e) hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_leviPSU3 (K := K) (p ^ e) hodd.pos
  let ι : Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield K p e) →*
      StatedProj (StatedSU 3 (p ^ e) K) :=
    (leviPSU3 (K := K) (p ^ e)).subtype.comp (e₂.toMonoidHom.comp e₁.toMonoidHom)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (e₂.injective.comp e₁.injective)
  have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p e) = p ^ e :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  exact rankFourCover_of_SL2 hF hp2 he ι hι
    (orderOf_eq_prime (negDiagPSU3_sq (K := K) hodd) (negDiagPSU3_ne_one h2 hodd))
    fun g => leviPSU3_commute hodd (ι g) (e₂ (e₁ g)).2

end CFSG.RankThree.PartOne.SRC
