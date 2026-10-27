module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem recipeUnitary_rootGenAvoidKG
    {d n p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hn : 2 ≤ n) (hd : 3 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK (by omega)).charP
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 0,
    TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := d) (f := n) (K := K)
      (by omega)),
    ggTorusRootGenAvoidKG_unitaryCoprime hK hn hd hp hpq hpd 0⟩

theorem ggRootGenKGAvoidOn_unitaryCoprime :
    GGRootGenKGAvoidOn fun p lab => GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨h, hn⟩
  dsimp only at hn
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl2 : 2 ≤ l := hlab.2.1
    exact recipeUnitary_rootGenAvoidKG hp hpn hn (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    refine recipeUnitary_rootGenAvoidKG hp hpn hn (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

end CFSG.StandardType

end
