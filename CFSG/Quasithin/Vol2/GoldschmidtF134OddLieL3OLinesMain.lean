module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLinesDef
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OFix

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Basic

variable {K : Type} [Field K]

theorem lineDiag_injective : Function.Injective (lineDiag K) := fun _ _ h => congrArg Prod.fst h

theorem lineSnd_injective : Function.Injective (lineSnd K) := fun _ _ h => congrArg Prod.fst h

theorem lineFst_injective : Function.Injective (lineFst K) := fun _ _ h => congrArg Prod.snd h

theorem dv_lineSnd (a : Kˣ) : dv (lineSnd K a) 0 = dv (lineSnd K a) 2 := by
  show a = (a * (a * a)⁻¹)⁻¹
  group

theorem dv_lineFst (a : Kˣ) : dv (lineFst K a) 1 = dv (lineFst K a) 2 := by
  show a = ((a * a)⁻¹ * a)⁻¹
  group

end Basic

section Cases

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem mem_lineSet_cases (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    {U : Subgroup (projectiveSL 3 K)} (hU : U ∈ lineSet K p) :
    U = lineP K p (lineDiag K) ∨ U = lineP K p (lineSnd K) ∨ U = lineP K p (lineFst K) := by
  obtain ⟨hUE, hUc, hUC⟩ := hU
  have hnt : Nontrivial U := Finite.one_lt_card_iff_nontrivial.1 (by rw [hUc]; exact hp.out.one_lt)
  obtain ⟨⟨x, hxU⟩, hx1⟩ := exists_ne (1 : U)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_torusP.1 (hUE hxU)
  by_cases h01 : a = b
  · subst h01
    exact Or.inl (eq_of_card_eq_prime hUc (card_lineP hp5 hpq lineDiag_injective) hxU
      (mem_lineP.2 ⟨a, ha, rfl⟩) hx1')
  by_cases h02 : a = (a * b)⁻¹
  · have hb' : b = (a * a)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [mul_assoc]; exact eq_inv_iff_mul_eq_one.1 h02)
    subst hb'
    exact Or.inr (Or.inl (eq_of_card_eq_prime hUc (card_lineP hp5 hpq lineSnd_injective) hxU
      (mem_lineP.2 ⟨a, ha, rfl⟩) hx1'))
  by_cases h12 : b = (a * b)⁻¹
  · have ha' : a = (b * b)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_left_comm]; exact eq_inv_iff_mul_eq_one.1 h12)
    subst ha'
    exact Or.inr (Or.inr (eq_of_card_eq_prime hUc (card_lineP hp5 hpq lineFst_injective) hxU
      (mem_lineP.2 ⟨b, hb, rfl⟩) hx1'))
  exfalso
  refine hUC (le_antisymm (fun g hg => ?_) (Subgroup.centralizer_le hUE))
  rw [Subgroup.mem_centralizer_iff] at hg
  exact centralizer_le_of_regular (by omega) ha hb (isRegular_iff.2 ⟨h01, h02, h12⟩) (hg _ hxU)

omit [Finite K] in
theorem ne_inv_sq (hp5 : 5 ≤ p) {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) : ζ ≠ (ζ * ζ)⁻¹ := by
  intro h
  have h3 : ζ ^ 3 = 1 := by
    calc ζ ^ 3 = ζ * (ζ * ζ) := pow_three ζ
      _ = 1 := eq_inv_iff_mul_eq_one.1 h
  exact hζ1 (eq_one_of_pow_eq_one_of_prime Nat.prime_three (by omega) hζ h3)

theorem lineSet_eq (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    lineSet K p = {lineP K p (lineDiag K), lineP K p (lineSnd K), lineP K p (lineFst K)} := by
  ext U
  constructor
  · intro hU
    rcases mem_lineSet_cases hp5 hpq hU with h | h | h <;> simp [h]
  · rintro (rfl | rfl | rfl)
    · exact lineP_mem_lineSet hp5 hpq lineDiag_injective 0 1 (by decide) fun a => rfl
    · exact lineP_mem_lineSet hp5 hpq lineSnd_injective 0 2 (by decide) dv_lineSnd
    · exact lineP_mem_lineSet hp5 hpq lineFst_injective 1 2 (by decide) dv_lineFst

theorem oddInvariantSet_torusP (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    OddInvariantSet p (torusP K p) := by
  obtain ⟨ζ, hζ, hζ1⟩ := exists_ne_one hpq
  have hne := ne_inv_sq hp5 hζ hζ1
  have hne2 : dv (lineFst K ζ) 0 ≠ dv (lineFst K ζ) 2 := by
    intro h
    have e : dv (lineFst K ζ) 2 = ζ := by
      show ((ζ * ζ)⁻¹ * ζ)⁻¹ = ζ
      group
    rw [e] at h
    exact hne.symm h
  have h01 : lineP K p (lineDiag K) ≠ lineP K p (lineSnd K) :=
    lineP_ne (by omega) 0 1 (by decide) (fun a => rfl) hζ hne
  have h02 : lineP K p (lineDiag K) ≠ lineP K p (lineFst K) :=
    lineP_ne (by omega) 0 1 (by decide) (fun a => rfl) hζ hne.symm
  have h12 : lineP K p (lineSnd K) ≠ lineP K p (lineFst K) :=
    lineP_ne (by omega) 0 2 (by decide) dv_lineSnd hζ hne2
  have hX := lineSet_eq hp5 hpq
  refine ⟨lineSet K p, ?_, ?_, fun U hU => ⟨hU.1, hU.2.1⟩, ?_⟩
  · rw [hX]
    exact Set.toFinite _
  · rw [hX, Set.ncard_eq_three.2 ⟨_, _, _, h01, h02, h12, rfl⟩]
    decide
  · intro φ hφ U hU
    obtain ⟨hUE, hUc, hUC⟩ := hU
    refine ⟨(Subgroup.map_mono hUE).trans hφ.le, ?_, fun h => hUC ?_⟩
    · rw [Subgroup.card_map_of_injective φ.injective]
      exact hUc
    · rw [centralizer_map_equiv] at h
      have h2 : Subgroup.centralizer (torusP K p : Set (projectiveSL 3 K)) =
          (Subgroup.centralizer (torusP K p : Set (projectiveSL 3 K))).map φ.toMonoidHom := by
        rw [← centralizer_map_equiv, hφ]
      exact Subgroup.map_injective φ.injective (h.trans h2)

end Cases

end CFSG.Quasithin.H13.NQCore.L3Odd
