module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Four
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveH

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_embed {L E K : Subgroup G} (hLE : L ≤ normalizer (E : Set G))
    (hK : ∀ x ∈ L, x ∈ K ↔ ∀ e ∈ E, x * e = e * x) {w w' : G} (hw : w ∈ L) (hw' : w' ∈ L)
    (hww : w * w = 1) (hw'w' : w' * w' = 1) {n : ℕ} (hn : ∀ j : ℕ, (w * w') ^ j ∈ K ↔ n ∣ j) :
    ∃ a b : MulAut ↥E, a * a = 1 ∧ b * b = 1 ∧ orderOf (a * b) = n := by
  let ψ : ↥L →* MulAut ↥E := (E.normalizerMonoidHom).comp (Subgroup.inclusion hLE)
  have hψ : ∀ (x : ↥L) (a : ↥E),
      ((ψ x) a : G) = (x : G) * (a : G) * (x : G)⁻¹ := by
    intro x a
    exact E.normalizerMonoidHom_apply_apply_coe ((Subgroup.inclusion hLE) x) a
  have hker : ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ K := by
    intro x
    rw [hK (x : G) x.2]
    constructor
    · intro hx e he
      have h2 : ((ψ x) ⟨e, he⟩ : G) = e := by rw [hx]; rfl
      rw [hψ] at h2
      calc (x : G) * e = ((x : G) * e * (x : G)⁻¹) * (x : G) := by group
        _ = e * (x : G) := by rw [h2]
    · intro hxcent
      ext a
      rw [hψ]
      have h1 : (x : G) * (a : G) = (a : G) * (x : G) := hxcent (a : G) a.2
      calc (x : G) * (a : G) * (x : G)⁻¹ = (a : G) * (x : G) * (x : G)⁻¹ := by rw [h1]
        _ = (a : G) := by group
        _ = ((1 : MulAut ↥E) a : G) := rfl
  refine ⟨ψ ⟨w, hw⟩, ψ ⟨w', hw'⟩, ?_, ?_, ?_⟩
  · have h1 : (⟨w, hw⟩ : ↥L) * ⟨w, hw⟩ = 1 := Subtype.ext (by simpa using hww)
    rw [← map_mul, h1, map_one]
  · have h1 : (⟨w', hw'⟩ : ↥L) * ⟨w', hw'⟩ = 1 := Subtype.ext (by simpa using hw'w')
    rw [← map_mul, h1, map_one]
  · have hiff : ∀ j : ℕ, (ψ ⟨w, hw⟩ * ψ ⟨w', hw'⟩) ^ j = 1 ↔ n ∣ j := by
      intro j
      rw [← map_mul, ← map_pow, hker ((⟨w, hw⟩ * ⟨w', hw'⟩) ^ j)]
      simpa using hn j
    refine Nat.dvd_antisymm ?_ ?_
    · exact (orderOf_dvd_iff_pow_eq_one).2 ((hiff n).2 (dvd_refl n))
    · exact (hiff _).1 (pow_orderOf_eq_one _)

theorem s16c1_G47_card_L0_le {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp65 n M V₀ V g)
    (hsmall : mSub V₀ ≤ 2) : Nat.card ↥(L0Of M V₀ g) ≤ 16 := by
  have hV₀ : IsElemAbelian 2 V₀ := h.elemAbelian.mono h.le
  have hpow : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub (IsElemAbelian.isPGroup hV₀)
  have hV0 : Nat.card V₀ ≤ 4 := by
    rw [hpow]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hsmall
      _ = 4 := by norm_num
  have hZ : Nat.card (Z0Of M V₀ g) ≤ 4 :=
    (Subgroup.card_le_of_le inf_le_left).trans hV0
  have hYcard : Nat.card (conjSubgroup V₀ g) = Nat.card V₀ :=
    CFSG.Quasithin.E3.card_conjSubgroup V₀ g
  have hY : Nat.card (YOf M V₀ g) ≤ 4 :=
    (Subgroup.card_le_of_le (inf_le_left : YOf M V₀ g ≤ conjSubgroup V₀ g)).trans
      (by rw [hYcard]; exact hV0)
  let f : ↥(Z0Of M V₀ g) × ↥(YOf M V₀ g) → ↥(L0Of M V₀ g) := fun p =>
    ⟨p.1.1 * p.2.1, Subgroup.mul_mem _
      (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (L0Of M V₀ g : Set G) := hx
    rw [Hyp65.L0_coe_eq_mul h] at hx'
    obtain ⟨z, hz, y, hy, rfl⟩ := hx'
    exact ⟨(⟨z, hz⟩, ⟨y, hy⟩), Subtype.ext rfl⟩
  have hcard : Nat.card (L0Of M V₀ g) ≤
      Nat.card (↥(Z0Of M V₀ g) × ↥(YOf M V₀ g)) :=
    Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_prod] at hcard
  have hcd : Nat.card (Z0Of M V₀ g) * Nat.card (YOf M V₀ g) ≤ 4 * 4 := Nat.mul_le_mul hZ hY
  omega

theorem s16c1_G47_ne_bot_ord
    {M V₀ V K : Subgroup G} {g : G} (h : Hyp65 1 M V₀ V g) (hsmall : mSub V₀ ≤ 2)
    (hK : (K : Set G) = ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) *
      ((V ⊓ conjSubgroup M g : Subgroup G) : Set G)) {w w' : G} (hw : w ∈ V)
    (hw' : w' ∈ conjSubgroup V g) (hww : w * w = 1) (hw'w' : w' * w' = 1) {n : ℕ}
    (hodd : Odd n) (hn1 : n ≠ 1) (hn : ∀ j : ℕ, (w * w') ^ j ∈ K ↔ n ∣ j) :
    n = 3 ∨ n = 5 := by
  have hK' : K = KOf M V g := by
    apply SetLike.coe_injective
    rw [hK, Hyp65.K_coe_eq_mul h]
    rfl
  rw [hK'] at hn
  have hCK : ∀ x ∈ LOf V g, x ∈ KOf M V g ↔
      ∀ e ∈ L0Of M V₀ g, x * e = e * x := by
    intro x hx
    rw [← Hyp65.C_eq_K h]
    simp only [COf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hcent⟩ e he
      exact (hcent e he).symm
    · intro hcent
      exact ⟨hx, fun e he => (hcent e he).symm⟩
  obtain ⟨a, b, haa, hbb, hab⟩ := s16c1_G47_embed (L := LOf V g) (E := L0Of M V₀ g)
    (K := KOf M V g) (Hyp65.L_le_normalizer_L0 h) hCK (Subgroup.mem_sup_left hw)
    (Subgroup.mem_sup_right hw') hww hw'w' hn
  have hL0 : IsElemAbelian 2 (L0Of M V₀ g) := Hyp65.L0_isElemAbelian h
  rcases s16c1_G47_g4 (E := ↥(L0Of M V₀ g))
    (fun x y => hL0.1.is_comm.comm x y)
    (fun x => Subtype.ext (by simpa [pow_two] using hL0.2 x x.2))
    (s16c1_G47_card_L0_le h hsmall) haa hbb (by rw [hab]; exact hodd) with h1 | h3 | h5
  · exact absurd (hab ▸ h1) hn1
  · exact Or.inl (hab ▸ h3)
  · exact Or.inr (hab ▸ h5)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
