module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Exp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
  {X : Subgroup (MulAut T)}

theorem s16t_w3_isPOnePlusTwo_sup (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {f : MulAut T} (hfX : f ∈ X) (hf3 : f ^ 3 = 1)
    (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) :
    IsPOnePlusTwo 3 ↥(S ⊔ Subgroup.zpowers f) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS9 := s16t_w3_card_S h hS hSc
  have hfS : f ∉ S := fun hf => by
    obtain ⟨i, hi⟩ := hfm
    exact hi (((hS f).1 hf).2.1 i)
  have hof : orderOf f = 3 := orderOf_eq_prime hf3 fun h1 => hfS (h1 ▸ S.one_mem)
  have hnorm : f ∈ Subgroup.normalizer (S : Set (MulAut T)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨s16t_w3_conj_mem h hS hfX, fun hx => ?_⟩
    have h1 := s16t_w3_conj_mem h hS (X.inv_mem hfX) hx
    rwa [show f⁻¹ * (f * x * f⁻¹) * f⁻¹⁻¹ = x by group] at h1
  have hinf : S ⊓ Subgroup.zpowers f = ⊥ := by
    have h1 : Nat.card ↥(S ⊓ Subgroup.zpowers f) ∣ 3 := by
      have h2 := Subgroup.card_dvd_of_le
        (inf_le_right : S ⊓ Subgroup.zpowers f ≤ Subgroup.zpowers f)
      rwa [Nat.card_zpowers, hof] at h2
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h2 | h2
    · exact Subgroup.card_eq_one.1 h2
    · exfalso
      have h3 : S ⊓ Subgroup.zpowers f = Subgroup.zpowers f :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, Nat.card_zpowers, hof])
      have h4 : f ∈ S ⊓ Subgroup.zpowers f := by
        rw [h3]
        exact Subgroup.mem_zpowers f
      exact hfS h4.1
  have hcard : Nat.card ↥(S ⊔ Subgroup.zpowers f) = 27 := by
    rw [SBd19F.card_sup_zpowers_of_mem_normalizer hnorm hinf, hS9, Nat.card_zpowers, hof]
  have hA3 : ∀ a ∈ S, a ^ 3 = 1 := fun a ha => ((hS a).1 ha).2.2
  have hf1 := s16t_w3_mul_pow_three hSc hA3 hS9 (fun a ha => s16t_w3_conj_mem h hS hfX ha) hf3
  have hf2 := s16t_w3_mul_pow_three hSc hA3 hS9
    (fun a ha => s16t_w3_conj_mem h hS (X.pow_mem hfX 2) ha)
    (by rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hf3, one_pow])
  have hexp : ∀ x ∈ S ⊔ Subgroup.zpowers f, x ^ 3 = 1 := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left S _
      (Subgroup.zpowers_le.2 hnorm)] at hx
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    show (s * f ^ k) ^ 3 = 1
    rw [zpow_eq_zpow_emod' k hf3]
    have h3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
      omega
    rcases h3 with h0 | h1 | h2
    · rw [h0, zpow_zero, mul_one]
      exact hA3 s hs
    · rw [h1, zpow_one]
      exact hf1 s hs
    · rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact hf2 s hs
  have hnc : ¬ IsMulCommutative ↥(S ⊔ Subgroup.zpowers f) := by
    intro hc
    have hle : S ⊔ Subgroup.zpowers f ≤ X :=
      sup_le (fun s hs => ((hS s).1 hs).1) (Subgroup.zpowers_le.2 hfX)
    exact h.not_three_le_pRank (CFSG.SectionRank.le_pRank (by norm_num) hle ⟨hc, hexp⟩
      (by rw [hcard]; norm_num))
  exact SBd19F.isPOnePlusTwo_of_card_twentySeven hcard
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow]; exact hexp x.1 x.2)) hnc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
