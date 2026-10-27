module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNotDvd
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith

public noncomputable section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal CFSG.StandardType.TableCRes CFSG.Assembly CFSG.Open

theorem exists_liftHom_PSU_of_not_dvd
    {X : Type} [Group X] {n g p : ℕ}
    (ψ : ↥(Unitary.SU (PSUσ g) n) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    (hadm : StatedLieAdmissible .PSU n 2 (g + 1)) (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup X) (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF g) n) ψ b)
    (h4 : p ^ 4 ≤ Nat.card B) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) :
    ∃ ℓ : B →* ↥(Unitary.SU (PSUσ g) n),
      (∀ (b : B) (u : ↥(Unitary.SU (PSUσ g) n)),
        (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ b * u * (ℓ b)⁻¹)) ∧
      ∀ b : B, ℓ b ^ p = 1 := by
  classical
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 1 ≤ n := by omega
  have hex : ∀ b : B, ∃ s : GL (Fin n) (PSUF g), s ∈ GUsub (PSUσ g) n ∧
      IsGLLift (PSUj n g) ψ s (b : X) ∧ s ^ p = 1 := by
    intro b
    obtain ⟨s, hsU, hsl⟩ := exists_isGLLift_PSU (card_PSUF g) n hn3 ψ hψ
      (hBN b.property) (hdiag b b.property)
    exact exists_isGLLift_pow_eq_one_PSU hn hψ hp hpq hsU (hB.2 b b.property) hsl
  choose s hsU hsl hsp using hex
  have hone : s 1 = 1 :=
    eq_of_isGLLift_pow_eq_one_PSU hn hψ hp hpq (hsU 1) (Subgroup.one_mem _) (hsp 1)
      (one_pow p) (hsl 1) (by simpa using (isGLLift_one : IsGLLift (PSUj n g) ψ 1 1))
  have hmul : ∀ b b' : B, s (b * b') = s b * s b' := by
    intro b b'
    have hc := isGLLift_commute_PSU (card_PSUF g) n ψ hψ hadm hp hp2 hBN hdiag hB h4
      (fun h => (hpq h).elim) b.property b'.property (hsl b) (hsl b')
    apply eq_of_isGLLift_pow_eq_one_PSU hn hψ hp hpq (hsU (b * b'))
      (Subgroup.mul_mem _ (hsU b) (hsU b')) (hsp (b * b'))
    · rw [hc.mul_pow, hsp b, hsp b', one_mul]
    · exact hsl (b * b')
    · rw [hc.eq]
      exact (hsl b).mul (hsl b')
  let ℓg : B →* GL (Fin n) (PSUF g) :=
    { toFun := s, map_one' := hone, map_mul' := hmul }
  let ℓ : B →* ↥(Unitary.SU (PSUσ g) n) := ℓg.codRestrict _
    (fun b => mem_SU_of_mem_GUsub_of_pow_eq_one hp hpq (hsU b) (hsp b))
  refine ⟨ℓ, ?_, ?_⟩
  · intro b u
    obtain ⟨u', hu', hψu'⟩ := hsl b u
    have hu : u' = ℓ b * u * (ℓ b)⁻¹ := by
      apply Subtype.ext
      exact hu'
    simpa only [hu] using hψu'
  · intro b
    apply Subtype.ext
    exact hsp b

theorem map_ker_liftHom_PSU_eq
    {X : Type} [Group X] {n g p : ℕ} (hn : 1 ≤ n)
    (ψ : ↥(Unitary.SU (PSUσ g) n) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    (B : Subgroup X) (ℓ : B →* ↥(Unitary.SU (PSUσ g) n))
    (hℓ : ∀ (b : B) (u : ↥(Unitary.SU (PSUσ g) n)),
      (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hpow : ∀ b : B, ℓ b ^ p = 1) :
    ℓ.ker.map B.subtype = B ⊓ Subgroup.centralizer (ψ.range : Set X) := by
  have hker (b : B) : ℓ b = 1 ↔ (b : X) ∈ Subgroup.centralizer (ψ.range : Set X) := by
    constructor
    · intro hb
      rw [Subgroup.mem_centralizer_iff]
      rintro z ⟨u, rfl⟩
      have h := hℓ b u
      rw [hb, inv_one, one_mul, mul_one] at h
      have h' := congrArg (fun z : X => (b : X) * z) h
      simpa only [mul_assoc, mul_inv_cancel_left] using h'
    · intro hb
      have hsl : IsGLLift (PSUj n g) ψ (ℓ b : GL (Fin n) (PSUF g)) (b : X) := by
        intro u
        exact ⟨ℓ b * u * (ℓ b)⁻¹, rfl, hℓ b u⟩
      have hsl1 : IsGLLift (PSUj n g) ψ 1 (b : X) := by
        intro u
        refine ⟨u, by simp, ?_⟩
        have hc := Subgroup.mem_centralizer_iff.mp hb (ψ u) ⟨u, rfl⟩
        calc (b : X)⁻¹ * ψ u * (b : X) = (b : X)⁻¹ * (ψ u * (b : X)) := by group
          _ = (b : X)⁻¹ * ((b : X) * ψ u) := by rw [hc]
          _ = ψ u := by group
      have hpg : (ℓ b : GL (Fin n) (PSUF g)) ^ p = 1 := by
        exact congrArg (fun z : ↥(Unitary.SU (PSUσ g) n) => (z : GL (Fin n) (PSUF g))) (hpow b)
      apply Subtype.ext
      exact eq_of_isGLLift_pow_eq_one_PSU hn hψ hp hpq (ℓ b).property.2 (Subgroup.one_mem _)
        hpg (one_pow p) hsl hsl1
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.property, (hker b).mp (MonoidHom.mem_ker.mp hb)⟩
  · rintro ⟨hb, hc⟩
    exact ⟨⟨x, hb⟩, MonoidHom.mem_ker.mpr ((hker ⟨x, hb⟩).mpr hc), rfl⟩

theorem exists_unitary_lift_kernel_rank
    {X : Type} [Group X] [Finite X] {n g p r : ℕ}
    (ψ : ↥(Unitary.SU (PSUσ g) n) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    (hadm : StatedLieAdmissible .PSU n 2 (g + 1)) (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup X) (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF g) n) ψ b)
    (h4 : p ^ 4 ≤ Nat.card B) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    (hrank : p ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (ψ.range : Set X)) ≤ Nat.card B) :
    ∃ ℓ : B →* ↥(Unitary.SU (PSUσ g) n),
      (∀ (b : B) (u : ↥(Unitary.SU (PSUσ g) n)),
        (b : X)⁻¹ * ψ u * (b : X) = ψ (ℓ b * u * (ℓ b)⁻¹)) ∧
      ℓ.ker.map B.subtype = B ⊓ Subgroup.centralizer (ψ.range : Set X) ∧
      (∀ b : B, ℓ b ^ p = 1) ∧ p ^ r ≤ Nat.card ℓ.range := by
  obtain ⟨ℓ, hℓ, hpow⟩ := exists_liftHom_PSU_of_not_dvd ψ hψ hadm hp hp2 B hB hBN hdiag h4 hpq
  have hn : 1 ≤ n := by have := hadm.2.2.1; omega
  have hmap := map_ker_liftHom_PSU_eq hn ψ hψ hp hpq B ℓ hℓ hpow
  have hcard : Nat.card ℓ.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (ψ.range : Set X)) := by
    rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective]
  have hmul := Subgroup.card_ker_mul_card_range ℓ
  rw [hcard] at hmul
  have hpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (ψ.range : Set X)) := Nat.card_pos
  exact ⟨ℓ, hℓ, hmap, hpow, by nlinarith⟩

end CFSG.StandardType.ClassicalPosition
