module

public import CFSG.RankThree.PartOne.Q1327S.Witness

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne

variable {Q : Type} [Group Q]

theorem centralizer_le_of_sylow_equiv {Γ : Type} [Group Γ] [Finite Γ] (f : Q ≃* Γ) {p : ℕ}
    [Fact p.Prime] {Ē : Subgroup Q} {S₀ : Subgroup Γ}
    (hE : Nat.card Ē = p ^ (Nat.card Γ).factorization p)
    (hS₀ : Nat.card S₀ = p ^ (Nat.card Γ).factorization p)
    (hC : Subgroup.centralizer (S₀ : Set Γ) ≤ S₀) :
    Subgroup.centralizer (Ē : Set Q) ≤ Ē := by
  have hE' : Nat.card (Ē.map f.toMonoidHom) = p ^ (Nat.card Γ).factorization p := by
    rw [Subgroup.card_map_of_injective f.injective, hE]
  obtain ⟨g, hg⟩ := exists_conj_of_card hE' hS₀
  intro y hy
  have hyc := Subgroup.mem_centralizer_iff.1 hy
  have hmem : g⁻¹ * f y * g ∈ Subgroup.centralizer (S₀ : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : g * s * g⁻¹ ∈ Ē.map f.toMonoidHom := by
      rw [hg]
      simpa [mul_assoc] using hs
    obtain ⟨e, he, hef⟩ := h1
    have h2 := hyc e he
    have h3 : f y * (g * s * g⁻¹) = (g * s * g⁻¹) * f y := by
      rw [← hef]
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, h2]
    calc s * (g⁻¹ * f y * g) = g⁻¹ * ((g * s * g⁻¹) * f y) * g := by group
      _ = g⁻¹ * (f y * (g * s * g⁻¹)) * g := by rw [h3]
      _ = (g⁻¹ * f y * g) * s := by group
  have h4 := hC hmem
  have h5 : f y ∈ Ē.map f.toMonoidHom := by
    rw [hg]
    exact h4
  obtain ⟨z, hz, hzy⟩ := h5
  have : z = y := f.injective hzy
  rwa [← this]

theorem not_perm3_of_sylow_count {p : ℕ} [Fact p.Prime] [Finite Q] {Ē : Subgroup Q}
    (hEcard : Nat.card Ē = p ^ 2) (hQ : ¬ p ^ 3 ∣ Nat.card Q)
    (hC : Subgroup.centralizer (Ē : Set Q) ≤ Ē)
    (hmod : ∀ n : ℕ, Nat.card Q = n * (6 * p ^ 2) → ¬ n ≡ 1 [MOD p]) :
    ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨φ⟩
  have hX0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hdvd : p ^ 2 ∣ Nat.card Q := hEcard ▸ Subgroup.card_subgroup_dvd_card Ē
  have hfac : (Nat.card Q).factorization p = 2 :=
    factorization_eq_two (Fact.out : p.Prime) hX0 hdvd hQ
  have hEp : IsPGroup p Ē := IsPGroup.of_card hEcard
  have hcomm' : IsMulCommutative Ē := IsPGroup.isMulCommutative_of_card_eq_prime_sq hEcard
  have hcomm : ∀ a b : Ē, a * b = b * a := fun a b => hcomm'.is_comm.comm a b
  have hEC : Ē ≤ Subgroup.centralizer (Ē : Set Q) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun f hf => congrArg Subtype.val (hcomm ⟨f, hf⟩ ⟨e, he⟩)
  have hCc : Nat.card (Subgroup.centralizer (Ē : Set Q)) = p ^ 2 :=
    le_antisymm (by rw [← hEcard]; exact Subgroup.card_le_of_le hC)
      (by rw [← hEcard]; exact Subgroup.card_le_of_le hEC)
  have hN : Nat.card (Subgroup.normalizer (Ē : Set Q)) = 6 * p ^ 2 := by
    have := card_torusImage_top_mul Ē
    rwa [card_eq_six_of_perm3 φ, hCc, eq_comm] at this
  let S : Sylow p Q := Sylow.ofCard Ē (by rw [hfac, hEcard])
  have h1 : Nat.card (Sylow p Q) ≡ 1 [MOD p] := card_sylow_modEq_one p Q
  have h2 : Nat.card (Sylow p Q) = (Subgroup.normalizer (Ē : Set Q)).index :=
    S.card_eq_index_normalizer
  have h3 : (Subgroup.normalizer (Ē : Set Q)).index *
      Nat.card (Subgroup.normalizer (Ē : Set Q)) = Nat.card Q := Subgroup.index_mul_card _
  rw [hN, ← h2] at h3
  exact hmod _ h3.symm h1

end CFSG.RankThree.PartOne.Q1327S
