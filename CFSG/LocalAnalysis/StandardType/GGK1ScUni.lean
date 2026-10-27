module

public import CFSG.LocalAnalysis.StandardType.GGK1ScCore
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSU
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem ggCenterPrime_unitary_gcd
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ (p ∣ d ∧ p ∣ 2 ^ n + 1)) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFD := TableBU.unitaryFieldData_of_card hK hn
  haveI : CharP K 2 := hFD.charP
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* LargeEvenSUGroup (Fin d) K (2 ^ n)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSUGroup (Fin d) K (2 ^ n) →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen hC
    by_cases he : Even d
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
        (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn hd he hdq hπ hcen
  haveI : Finite (LargeEvenSUGroup (Fin d) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin d) K (2 ^ n) =>
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  refine ggCenterPrime_of_coprime_card_ker
    (q := LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (QuotientGroup.mk'_surjective _) (TableBUE.center_proj_eq_bot hK hd hdq) hsplit hp hp2 ?_
  let Z0 := (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ n))
  have hker_eq : (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))).ker = Z0 :=
    QuotientGroup.ker_mk' _
  rw [hker_eq]
  have hdivN : Nat.card Z0 ∣ d :=
    CFSG.QuasithinUnique.Ch1.card_scalars_dvd_dim (n := d) (p := 2) (f := n) (by omega)
      (Or.inr ⟨hK, rfl⟩)
  have hdivQ : Nat.card Z0 ∣ 2 ^ n + 1 :=
    CFSG.StandardType.SporadicShape.card_statedScalars_subgroupOf_statedSU_dvd d (2 ^ n) hK
  have hdiv : Nat.card Z0 ∣ Nat.gcd d (2 ^ n + 1) := Nat.dvd_gcd hdivN hdivQ
  have hpg : Nat.Coprime p (Nat.gcd d (2 ^ n + 1)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd'
    exact hpd ⟨hd'.trans (Nat.gcd_dvd_left _ _), hd'.trans (Nat.gcd_dvd_right _ _)⟩
  exact (Nat.Coprime.of_dvd_right hdiv hpg).symm

end CFSG.StandardType

end
