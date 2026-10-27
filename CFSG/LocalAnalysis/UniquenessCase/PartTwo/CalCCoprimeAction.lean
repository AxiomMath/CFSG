module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem acts_trivially_of_isPGroup_of_not_dvd_card_mulAut {L W : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hdiv : ¬ p ∣ Nat.card (MulAut (Bar2 L)))
    (hW : IsPGroup p W) (hWn : W ≤ normalizer (L : Set G)) :
    ∀ w ∈ W, ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  intro w hw l hl
  haveI : Fact p.Prime := ⟨hp⟩
  let N := normalizer (L : Set G)
  let m : ↥N := ⟨w, hWn hw⟩
  let ρ := UC6S846.rhoL L
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have hk' : w ^ (p ^ k) = 1 := by simpa using hk
  have hmk : m ^ (p ^ k) = 1 := by
    apply Subtype.ext
    simpa [m] using hk'
  have hρk : (ρ m) ^ (p ^ k) = 1 := by
    rw [← map_pow, hmk, map_one]
  have hordp : orderOf (ρ m) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hρk
  have hordAut : orderOf (ρ m) ∣ Nat.card (MulAut (Bar2 L)) :=
    orderOf_dvd_natCard (ρ m)
  have hcop : Nat.Coprime (p ^ k) (Nat.card (MulAut (Bar2 L))) :=
    Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).2 hdiv)
  have hord1 : orderOf (ρ m) = 1 := by
    apply Nat.dvd_one.mp
    have h := Nat.dvd_gcd hordp hordAut
    rwa [hcop.gcd_eq_one] at h
  have hρ1 : ρ m = 1 := orderOf_eq_one_iff.mp hord1
  rw [← UC6S846.rhoL_fix_iff L m ⟨l, hl⟩]
  rw [hρ1]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
