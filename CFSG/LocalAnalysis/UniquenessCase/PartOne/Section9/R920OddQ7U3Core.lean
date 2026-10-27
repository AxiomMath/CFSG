module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Iso
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Levi
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Max
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Seven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem exists_unit_orderOf_three (hF : Nat.card F = (p ^ f) ^ 2) (hq2 : 2 ≤ p ^ f)
    (hq3 : p ^ f % 3 = 1) : ∃ ω : Fˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h2 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    have h3 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  exact exists_prime_orderOf_dvd_card' 3 hF3

variable (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem eq_top_of_normA0_le
    [IsSimpleGroup (SU (unitaryInvolution F p f) 3)]
    (hst : CFSG.Open.StatedClassicalModel (SU (unitaryInvolution F p f) 3) .PSU 3 p f)
    (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1) {ω : Fˣ} (hω : orderOf ω = 3)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hNW : normA0 hF ω ≤ W)
    {a d : SU (unitaryInvolution F p f) 3} (haW : a ∈ W) (ha7 : orderOf a = 7)
    (hdA : d ∈ Subgroup.zpowers (tSU hF ω)) (hd3 : orderOf d = 3) (hda : d * a * d⁻¹ = a ^ 2)
    (hC : ∀ x ∈ Subgroup.centralizer ({a} : Set (SU (unitaryInvolution F p f) 3)),
      Nat.Coprime (orderOf x) 7 → x ∈ W)
    (hns : ¬ Group.IsSolvable W) : W = ⊤ := by
  have hU : rootU hF ≤ W → W = ⊤ := fun hUW => by
    by_contra hne
    exact hns (isSolvable_of_rootU_le hF hst hUW hne)
  by_cases hp7 : p = 7
  · exact hU (rootU_le_of_seven hF hp2 hq3 hp7 hω hNW haW ha7 hdA hd3 hda hC)
  have hq2 := two_le_prime_pow_of_card hF
  have hf0 : f ≠ 0 := fun h0 => by
    rw [h0, pow_zero] at hq2
    omega
  have hq7 : p ^ f ≠ 7 := fun h => hp7 (by
    have : p ∣ 7 := h ▸ dvd_pow_self p hf0
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).1 this)
  have hq13 : 13 ≤ p ^ f := by
    obtain ⟨m, hm⟩ := odd_prime_pow (p := p) (f := f) hp2
    omega
  have h7 : (7 : F) ≠ 0 := by
    intro h
    have h' : ((7 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp7 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).1 h')
  have hTW : (tSU hF).range ≤ W := (range_tSU_le_normA0 hF hω hq3).trans hNW
  by_cases hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω
  · exact absurd (isSolvable_of_centralizer_le hF hp2 hω hq3 hNW hbad) hns
  push Not at hbad
  obtain ⟨x, hxW, hxz, hxN⟩ := hbad
  have hLW := range_embSU_le_of_not_bad hF hp2 hq3 hq13 hω hNW hxW hxz hxN
  have hCW : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) ≤ W := by
    rw [centralizer_zSU hF hp2]
    exact sup_le hLW hTW
  have hdT : d ∈ (tSU hF).range :=
    Subgroup.zpowers_le.2 (MonoidHom.mem_range.2 ⟨ω, rfl⟩ : tSU hF ω ∈ (tSU hF).range) hdA
  have hdW : d ∈ W := hTW hdT
  have ha7' : a ^ 7 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha7] at this
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha7
    omega
  exact eq_top_of_centralizer_le hF hp2 hq3 h7 hCW hU haW hdW ha7' ha1 hda

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
