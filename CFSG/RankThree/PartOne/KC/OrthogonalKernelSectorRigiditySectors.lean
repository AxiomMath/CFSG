module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedCentralizer

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module TensorProduct CFSG.RankThree.Classical CFSG.RankThree.Classical2

section Characters

variable {Γ : Type*} [Group Γ] {p : ℕ}

theorem inf_eq_bot_of_card_eq_prime (hp : p.Prime) {M N : Subgroup Γ} (hM : Nat.card M = p)
    (hN : Nat.card N = p) (hMN : M ≠ N) : M ⊓ N = ⊥ := by
  have hfM : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hp.ne_zero)
  have hfN : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; exact hp.ne_zero)
  have hdvd : Nat.card (M ⊓ N : Subgroup Γ) ∣ p := by
    rw [← hM]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    apply hMN
    have h2 : M ⊓ N = M := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hM])
    have h3 : M ⊓ N = N := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hN])
    rw [← h2, h3]

theorem exists_ne_one_char_eq (hp : p.Prime) (hΓ : Nat.card Γ = p ^ 2)
    (χ ψ : Additive Γ →+ ZMod p) :
    ∃ a : Γ, a ≠ 1 ∧ χ (Additive.ofMul a) = ψ (Additive.ofMul a) := by
  let φ : Γ →* Multiplicative (ZMod p) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (χ (Additive.ofMul g) - ψ (Additive.ofMul g)))
      (fun a b => by
        rw [← ofAdd_add, ofMul_mul, map_add, map_add]
        congr 1
        abel)
  obtain ⟨a, ha1, ha⟩ := exists_ne_one_mem_ker hp hΓ φ
  refine ⟨a, ha1, sub_eq_zero.mp ?_⟩
  have := congrArg Multiplicative.toAdd ha
  simpa [φ] using this

theorem pow_val_ne_one {L : Type*} [Field L] {ζ : L} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    {k : ZMod p} (hk : k ≠ 0) : ζ ^ k.val ≠ 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro h
  rw [hζ.pow_eq_one_iff_dvd] at h
  exact hk ((ZMod.val_eq_zero k).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt k)))

end Characters

section Eigen

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {Ã : Subgroup (orthDerived Q)} {p : ℕ} (L : Type) [Field L] [Algebra K L]

theorem exists_char_of_active [FiniteDimensional K V] {ζ : L}
    (hlines : ∀ M : Subgroup Ã, Nat.card M = p → (lineSpace M).baseChange L =
      ⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M), charSpace (bcRep L Ã) ζ χ)
    {M : Subgroup Ã} (hM : Nat.card M = p) (hMa : lineSpace M ≠ ⊥) :
    ∃ χ : Additive Ã →+ ZMod p, χ ≠ 0 ∧ charKer χ = M ∧ charSpace (bcRep L Ã) ζ χ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply hMa
  have h1 : (lineSpace M).baseChange L = ⊥ := by
    rw [hlines M hM]
    exact iSup₂_eq_bot.mpr fun χ hχ => hcon χ hχ.1 hχ.2
  have h2 := finrank_submodule_baseChange L (lineSpace M)
  rw [h1, finrank_bot] at h2
  exact Submodule.finrank_eq_zero.mp h2.symm

theorem exists_eigenvector_of_char {ζ : L}
    (hlines : ∀ M : Subgroup Ã, Nat.card M = p → (lineSpace M).baseChange L =
      ⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M), charSpace (bcRep L Ã) ζ χ)
    {M : Subgroup Ã} (hM : Nat.card M = p) {χ : Additive Ã →+ ZMod p} (hχ : χ ≠ 0)
    (hχM : charKer χ = M) (hne : charSpace (bcRep L Ã) ζ χ ≠ ⊥) :
    ∃ s ∈ (lineSpace M).baseChange L, s ≠ 0 ∧
      ∀ g : Ã, bcRep L Ã g s = ζ ^ (χ (Additive.ofMul g)).val • s := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨s, ?_, hs0, mem_charSpace.mp hs⟩
  rw [hlines M hM]
  exact le_iSup₂_of_le (f := fun (ψ : Additive Ã →+ ZMod p) (_ : ψ ≠ 0 ∧ charKer ψ = M) =>
    charSpace (bcRep L Ã) ζ ψ) χ ⟨hχ, hχM⟩ le_rfl hs

theorem exists_common_eigenvalue [FiniteDimensional K V] (hp : p.Prime)
    (hΓ : Nat.card Ã = p ^ 2) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (hlines : ∀ M : Subgroup Ã, Nat.card M = p → (lineSpace M).baseChange L =
      ⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M), charSpace (bcRep L Ã) ζ χ)
    {M N : Subgroup Ã} (hM : Nat.card M = p) (hN : Nat.card N = p) (hMN : M ≠ N)
    (hMa : lineSpace M ≠ ⊥) (hNa : lineSpace N ≠ ⊥) :
    ∃ a : Ã, a ≠ 1 ∧ ∃ μ : L, μ ≠ 1 ∧ μ ^ p = 1 ∧
      (∃ s ∈ (lineSpace M).baseChange L, s ≠ 0 ∧ bcRep L Ã a s = μ • s) ∧
      (∃ s ∈ (lineSpace N).baseChange L, s ≠ 0 ∧ bcRep L Ã a s = μ • s) := by
  obtain ⟨χ, hχ0, hχM, hχne⟩ := exists_char_of_active L hlines hM hMa
  obtain ⟨ψ, hψ0, hψN, hψne⟩ := exists_char_of_active L hlines hN hNa
  obtain ⟨a, ha1, hχψ⟩ := exists_ne_one_char_eq hp hΓ χ ψ
  have hχa : χ (Additive.ofMul a) ≠ 0 := by
    intro h0
    have haM : a ∈ M := by rw [← hχM]; exact mem_charKer.mpr h0
    have haN : a ∈ N := by rw [← hψN]; exact mem_charKer.mpr (hχψ ▸ h0)
    have : a ∈ M ⊓ N := ⟨haM, haN⟩
    rw [inf_eq_bot_of_card_eq_prime hp hM hN hMN, Subgroup.mem_bot] at this
    exact ha1 this
  refine ⟨a, ha1, ζ ^ (χ (Additive.ofMul a)).val, pow_val_ne_one hp hζ hχa, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · obtain ⟨s, hs, hs0, hseig⟩ := exists_eigenvector_of_char L hlines hM hχ0 hχM hχne
    exact ⟨s, hs, hs0, hseig a⟩
  · obtain ⟨s, hs, hs0, hseig⟩ := exists_eigenvector_of_char L hlines hN hψ0 hψN hψne
    refine ⟨s, hs, hs0, ?_⟩
    rw [hseig a, ← hχψ]

end Eigen

end CFSG.RankThree.PartOne.KCOrthogonal
