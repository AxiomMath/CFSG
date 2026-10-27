module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne

section Galois

variable {K : Type} [Field K]

@[expose] def fixingAut (k : Subfield K) : Subgroup (K ≃+* K) where
  carrier := {ψ | ∀ t ∈ k, ψ t = t}
  mul_mem' {ψ χ} hψ hχ t ht := by
    show ψ (χ t) = t
    rw [hχ t ht, hψ t ht]
  one_mem' _ _ := rfl
  inv_mem' {ψ} hψ t ht := by
    show ψ.symm t = t
    conv_lhs => rw [← hψ t ht]
    exact ψ.symm_apply_apply t

theorem mem_fixingAut {k : Subfield K} {ψ : K ≃+* K} : ψ ∈ fixingAut k ↔ ∀ t ∈ k, ψ t = t :=
  Iff.rfl

theorem card_descentField {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (descentField σ) = ℓ ^ (f / p) := by
  obtain ⟨-, -, -, -, -, hfix⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hcard : Nat.card (Subgroup.zpowers σ) = p := by rw [Nat.card_zpowers, hσ]
  obtain ⟨hdvd, S, hS, hcardS⟩ := hfix (Subgroup.zpowers σ)
  rw [hcard] at hdvd hcardS
  refine ⟨hdvd, ?_⟩
  rw [← hcardS]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_descentField, ← SetLike.mem_coe, hS]
  constructor
  · intro hc τ hτ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    have : ∀ m : ℕ, (σ ^ m) c = c := by
      intro m
      induction m with
      | zero => rw [pow_zero, RingAut.one_apply]
      | succ m ih => rw [pow_succ', RingAut.mul_apply, ih, hc]
    rcases n with n | n
    · simpa using this n
    · have h1 := this (n + 1)
      rw [zpow_negSucc]
      conv_lhs => rw [← h1]
      exact (σ ^ (n + 1)).symm_apply_apply c
  · intro hc
    exact hc σ (Subgroup.mem_zpowers σ)

theorem mem_zpowers_of_forall_fixed_prime {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hK : Nat.card K = ℓ ^ f) {σ : K ≃+* K} (hσ : orderOf σ = p) {τ : K ≃+* K}
    (hτ : ∀ t ∈ descentField σ, τ t = t) : τ ∈ Subgroup.zpowers σ := by
  obtain ⟨hpf, hcardk⟩ := card_descentField hℓ hf hK hσ
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨-, -, -, -, -, hfix⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : Finite (K ≃+* K) := Finite.of_injective (fun ψ : K ≃+* K => (ψ : K → K))
    fun ψ χ h => RingEquiv.ext (congrFun h)
  set A : Subgroup (K ≃+* K) := fixingAut (descentField σ) with hA
  have hσA : Subgroup.zpowers σ ≤ A := by
    rw [Subgroup.zpowers_le]
    exact fun t ht => mem_descentField.mp ht
  obtain ⟨hAdvd, S, hS, hcardS⟩ := hfix A
  have hkS : Nat.card (descentField σ) ≤ Nat.card S := by
    refine Nat.card_mono (Set.toFinite _) fun t ht => ?_
    rw [hS]
    exact fun τ' hτ' => hτ' t ht
  rw [hcardk, hcardS] at hkS
  have hle := (Nat.pow_le_pow_iff_right hℓ.one_lt).mp hkS
  obtain ⟨c, hc⟩ := hAdvd
  obtain ⟨d, hd⟩ := hpf
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc
      omega
    · exact h0
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero] at hd
      omega
    · exact h0
  have hdiv : f / Nat.card A = c := by
    rw [hc, Nat.mul_div_cancel_left _ hApos]
  have hdiv' : f / p = d := by
    rw [hd, Nat.mul_div_cancel_left _ hp.pos]
  rw [hdiv, hdiv'] at hle
  have hAp : Nat.card A ≤ p := by
    by_contra hlt
    push Not at hlt
    have h1 : d * p < d * Nat.card A := Nat.mul_lt_mul_of_pos_left hlt hdpos
    have h2 : d * Nat.card A ≤ c * Nat.card A := Nat.mul_le_mul_right _ hle
    have h3 : f = d * p := by rw [hd, mul_comm]
    have h4 : f = Nat.card A * c := hc
    nlinarith
  have hσcard : Nat.card (Subgroup.zpowers σ) = p := by rw [Nat.card_zpowers, hσ]
  have hAeq : Subgroup.zpowers σ = A :=
    Subgroup.eq_of_le_of_card_ge hσA (by rw [hσcard]; exact hAp)
  rw [hAeq]
  exact hτ

end Galois

section Assembly

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem centralizer_fixedGroup_eq_zpowers_of_inputs {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) {σ : K ≃+* K}
    (hσ : orderOf σ = p)
    (hE : ∀ β : MulAut (StatedProj (StatedSp r K)),
      (∀ g : StatedSp r (descentField σ), β (proj r K (subfieldSpHom r (descentField σ) g)) =
        proj r K (subfieldSpHom r (descentField σ) g)) → β ∈ spSemilinearAutGroup r K)
    (hsemi : ∀ α ∈ spSemilinearAutGroup r K,
      (∀ g : StatedSp r (descentField σ), α (proj r K (subfieldSpHom r (descentField σ) g)) =
        proj r K (subfieldSpHom r (descentField σ) g)) →
      ∃ τ : K ≃+* K, (∀ c ∈ descentField σ, τ c = c) ∧ α = fieldAut r K τ) :
    Subgroup.centralizer (((spFixedGroup (fieldAut r K σ)).map
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) :
        Subgroup (MulAut (StatedProj (StatedSp r K)))) :
          Set (MulAut (StatedProj (StatedSp r K)))) = Subgroup.zpowers (fieldAut r K σ) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hpf, -⟩ := card_descentField hℓ hf hK hσ
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    have hfp : p ≤ f := Nat.le_of_dvd (by omega) hpf
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
      _ ≤ ℓ ^ p := Nat.pow_le_pow_left hℓ.two_le p
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hfp
  have hinj := KCSymplectic.conj_injective_statedProj_statedSp (r := r) (K := K) hr hq4
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  apply le_antisymm
  · intro β hβ
    have hfix : ∀ x ∈ spFixedGroup (fieldAut r K σ), β x = x := by
      intro x hx
      have h1 := Subgroup.mem_centralizer_iff.mp hβ (MulAut.conj x) ⟨x, hx, rfl⟩
      have h2 : β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := mulAut_conj_apply_conj β x
      have h3 : MulAut.conj (β x) = (MulAut.conj x : MulAut (StatedProj (StatedSp r K))) := by
        rw [← h2, ← h1]
        group
      exact hinj h3
    have hβg : ∀ g : StatedSp r (descentField σ),
        β (proj r K (subfieldSpHom r (descentField σ) g)) =
          proj r K (subfieldSpHom r (descentField σ) g) := fun g => by
      refine hfix _ ?_
      rw [spFixedGroup_fieldAut_eq_range hodd hσp]
      exact ⟨g, rfl⟩
    have hβE : β ∈ spSemilinearAutGroup r K := hE β hβg
    obtain ⟨τ, hτk, rfl⟩ := hsemi β hβE hβg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_forall_fixed_prime hℓ hf hp hK hσ hτk)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [map_zpow]⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h1 := mulAut_conj_apply_conj (fieldAut r K σ) x
    rw [(hx : fieldAut r K σ x = x)] at h1
    show MulAut.conj x * fieldAut r K σ = fieldAut r K σ * MulAut.conj x
    calc MulAut.conj x * fieldAut r K σ
        = (fieldAut r K σ * MulAut.conj x * (fieldAut r K σ)⁻¹) * fieldAut r K σ := by rw [h1]
      _ = fieldAut r K σ * MulAut.conj x := by group

end Assembly

end CFSG.RankThree.PartOne.KCSpComm
