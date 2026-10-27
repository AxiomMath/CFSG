module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKacRA (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  (lab.tag = .A ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twA ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGRegimeA24RA : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ labX => GGRegimeA24 p n labJ labX ∧ GGKacRA labX p

@[expose] def GGRegimeFieldTwoRA : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ labX => GGRegimeFieldTwo p n labJ labX ∧ GGKacRA labX p

private theorem ggKacRA_not_two_dvd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) :
    ¬ 2 ∣ 2 ^ n - 1 := by
  have hodd : Odd (2 ^ n - 1) := by
    have h : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.odd_iff]
    omega
  exact hodd.not_two_dvd_nat

private theorem ggKacRA_not_two_dvd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) :
    ¬ 2 ∣ 2 ^ n + 1 := by
  have hodd : Odd (2 ^ n + 1) := by
    have h : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.odd_iff]
    omega
  exact hodd.not_two_dvd_nat

private theorem eq_of_ggLabelIso_of_ggKacRA {p : ℕ} (hp : p.Prime)
    {lab labX : LargeEvenLabel} (hΛX : LargeEvenInLambda2 labX) (hRA : GGKacRA labX p)
    (h : GGLabelIso lab labX) : lab = labX := by
  unfold GGLabelIso at h
  have htagX : labX.tag = .A ∨ labX.tag = .twA := by
    rcases hRA with ⟨hA, -, -⟩ | ⟨hA, -, -⟩
    · exact Or.inl hA
    · exact Or.inr hA
  rcases h with heq | h | h | h | h | h | h | h
  · exact heq
  ·
    obtain ⟨-, hBC, -⟩ := h
    rcases htagX with hA | hA <;> rw [hA] at hBC <;>
      rcases hBC with hBC | hBC <;> cases hBC
  ·
    obtain ⟨-, hX⟩ := h
    rw [hX] at hRA hΛX
    rcases hRA with ⟨-, hdvd, hq⟩ | ⟨hA, -⟩
    · have hp2 : p = 2 :=
        Nat.prime_eq_prime_of_dvd_pow (m := 2) hp Nat.prime_two (by simpa using hdvd)
      have hn : 1 ≤ lab.n := by simpa using hΛX.1
      rw [hp2] at hq
      exact absurd hq (ggKacRA_not_two_dvd_two_pow_sub_one hn)
    · cases hA
  ·
    obtain ⟨-, hX⟩ := h
    rw [hX] at htagX
    rcases htagX with hA | hA <;> cases hA
  ·
    obtain ⟨-, hX⟩ := h
    rw [hX] at hRA hΛX
    rcases hRA with ⟨hA, -⟩ | ⟨-, hdvd, hq⟩
    · cases hA
    · have hp2 : p = 2 :=
        Nat.prime_eq_prime_of_dvd_pow (m := 2) hp Nat.prime_two (by simpa using hdvd)
      have hn : 1 ≤ lab.n := by simpa using hΛX.1
      rw [hp2] at hq
      exact absurd hq (ggKacRA_not_two_dvd_two_pow_add_one hn)
  ·
    obtain ⟨-, hX⟩ := h
    rw [hX] at htagX
    rcases htagX with hA | hA <;> cases hA
  ·
    obtain ⟨-, hX⟩ := h
    rw [hX] at hRA hΛX
    rcases hRA with ⟨-, hdvd, hq⟩ | ⟨hA, -⟩
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (by simpa using hdvd)
      have hn : 1 ≤ 2 * lab.n := by simpa using hΛX.1
      rw [hp2] at hq
      exact absurd hq (ggKacRA_not_two_dvd_two_pow_sub_one hn)
    · cases hA
  ·
    obtain ⟨hX, -⟩ := h
    rw [hX] at htagX
    rcases htagX with hA | hA <;> cases hA

theorem ggTPNMarked_eq_of_ggKacRA (hrig : GGLabelRigidInput) {p : ℕ} (hp : p.Prime)
    {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] {A : Subgroup (MulAut X)}
    (hm : GGTPNMarked p S A) {labX : LargeEvenLabel} (hΛX : LargeEvenInLambda2 labX)
    (hRA : GGKacRA labX p) (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    GGTPNMarked p (fun _ lab => lab = labX) A := by
  obtain ⟨hcomm, lab₁, hlab₁, hraw⟩ := hm
  have h₁ : GGHasLabel lab₁ (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  have hiso : GGLabelIso lab₁ labX :=
    hrig lab₁ labX (X ⧸ Subgroup.center X) hlab₁ hΛX h₁ hhX
  have heq : lab₁ = labX := eq_of_ggLabelIso_of_ggKacRA hp hΛX hRA hiso
  rw [heq] at hraw hlab₁
  exact ⟨hcomm, labX, hlab₁, largeEvenRawDatum_mono (fun R _ I F hQ => by
    obtain ⟨hs, hna, θ, -, h2, h3⟩ := hQ
    exact ⟨hs, hna, θ, rfl, h2, h3⟩) hraw⟩

end CFSG.StandardType

end
