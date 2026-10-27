module

public import CFSG.RankThree.PartOne.S11d.PSURational

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.OddIso CFSG.RankThree.Classical CFSG.LieType.Chevalley

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

theorem isom_of_subfieldGL {e : ℕ} (k : Subfield K) (h₀ : UnitaryFieldData 2 e k)
    (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {g₀ : GL (Fin n) k}
    (hiso : ∀ v w, idForm h n (linOf (subfieldGL k n g₀) v) (linOf (subfieldGL k n g₀) w) =
      idForm h n v w) (v w : Fin n → k) :
    idForm h₀ n (linOf g₀ v) (linOf g₀ w) = idForm h₀ n v w := by
  apply Subtype.val_injective
  rw [← idForm_embVec k h₀ hbar, ← idForm_embVec k h₀ hbar, ← linOf_subfieldGL,
    ← linOf_subfieldGL]
  exact hiso (embVec k v) (embVec k w)

theorem exists_rational_unitary_pair_of_isom [Finite K] {σ : K ≃+* K} (hp : p.Prime)
    (hp2 : p ≠ 2) (hσ : orderOf σ = p) {A : GL (Fin n) K}
    (hAiso : ∀ v w, idForm h n (linOf A v) (linOf A w) = idForm h n v w) (hAp : A ^ p = 1)
    (hσA : glAut σ A = A) (hm : 2 ≤ Module.finrank K (LinearMap.ker (linOf A - 1))) :
    ∃ a b : Fin n → K, a ∈ LinearMap.ker (linOf A - 1) ∧ b ∈ LinearMap.ker (linOf A - 1) ∧
      σ ∘ a = a ∧ σ ∘ b = b ∧ idForm h n a a = 0 ∧ idForm h n b b = 0 ∧
      idForm h n a b ≠ 0 := by
  have hfin := h.finite
  have hKc : CharP K 2 := h.charP
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨A₀, hA₀⟩ := exists_subfieldGL_eq_of_fixed n hσA
  have h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hkc : CharP (fixSubfield σ) 2 := h₀.charP
  have hA₀p : A₀ ^ p = 1 := by
    apply subfieldGL_injective (fixSubfield σ) n
    rw [map_pow, hA₀, hAp, map_one]
  have hÂ₀p : linOf A₀ ^ p = 1 := by rw [← linOf_pow, hA₀p, linOf_one]
  subst hA₀
  have hÂp : linOf (subfieldGL (fixSubfield σ) n A₀) ^ p = 1 := by
    rw [← linOf_pow, hAp, linOf_one]
  have hAB₀ := isom_of_subfieldGL h (fixSubfield σ) h₀ hbar (g₀ := A₀) hAiso
  have hB₀ := idForm_isSymm h₀ n
  have hBl₀ := idForm_separatingLeft h₀ n
  have hsymm₀ := fixSpace_isSymm (A := linOf A₀) hB₀
  have hsep₀ := fixSpace_sep hBl₀ hAB₀ hodd hÂ₀p
  have hdim : 2 ≤ Module.finrank (fixSubfield σ) (LinearMap.ker (linOf A₀ - 1)) :=
    hm.trans (finrank_fix_le hodd hÂ₀p hÂp)
  obtain ⟨e, he⟩ := h₀.exists_orthonormal_basis hsymm₀ hsep₀
  have hn : ∀ i j, idForm h₀ n ((e i : LinearMap.ker (linOf A₀ - 1)) : Fin n → fixSubfield σ)
      ((e j : LinearMap.ker (linOf A₀ - 1)) : Fin n → fixSubfield σ) = if i = j then 1 else 0 := by
    intro i j
    exact he i j
  let i0 : Fin (Module.finrank (fixSubfield σ) (LinearMap.ker (linOf A₀ - 1))) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank (fixSubfield σ) (LinearMap.ker (linOf A₀ - 1))) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun e => by simpa [i0, i1] using congrArg Fin.val e
  set w₁ : Fin n → fixSubfield σ := ((e i0 : LinearMap.ker (linOf A₀ - 1)) : Fin n → fixSubfield σ)
    with hw₁
  set w₂ : Fin n → fixSubfield σ := ((e i1 : LinearMap.ker (linOf A₀ - 1)) : Fin n → fixSubfield σ)
    with hw₂
  have hfixM : ∀ i, linOf A₀ ((e i : LinearMap.ker (linOf A₀ - 1)) : Fin n → fixSubfield σ) =
      ((e i : LinearMap.ker (linOf A₀ - 1)) : Fin n → fixSubfield σ) := fun i => by
    have := LinearMap.mem_ker.mp (e i).2
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  have hn11 : idForm h₀ n w₁ w₁ = 1 := by rw [hw₁, hn i0 i0]; simp
  have hn22 : idForm h₀ n w₂ w₂ = 1 := by rw [hw₂, hn i1 i1]; simp
  have hn12 : idForm h₀ n w₁ w₂ = 0 := by rw [hw₁, hw₂, hn i0 i1]; simp [h01]
  have hn21 : idForm h₀ n w₂ w₁ = 0 := by rw [hw₁, hw₂, hn i1 i0]; simp [Ne.symm h01]
  have hF : Nat.card (fixSubfield σ) = (2 ^ (F / p)) ^ 2 := h₀.card_eq_sq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (fixSubfield σ) := Finite.of_injective (fixSubfield σ).subtype Subtype.val_injective
  obtain ⟨ζ, hζ1, hζ2⟩ := CFSG.LieType.Universal.Unitary.exists_norm_eq_one_ne_one
    (F := fixSubfield σ) (p := 2) (f := F / p) hF
  have hζ1' : h₀.bar ζ * ζ = 1 := by
    have e1 : CFSG.LieType.BorelTits.unitaryInvolution (fixSubfield σ) 2 (F / p) ζ = h₀.bar ζ := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, UnitaryFieldData.bar_apply]
    rw [e1] at hζ1
    exact hζ1
  have h2 : (2 : fixSubfield σ) = 0 := CharP.cast_eq_zero (fixSubfield σ) 2
  have hdouble : ∀ x : fixSubfield σ, x + x = 0 := fun x => by
    rw [← two_mul, h2, zero_mul]
  have hW1 : idForm h₀ n (w₁ + w₂) (w₁ + w₂) = 0 := by
    simp only [map_add, LinearMap.add_apply, hn11, hn22, hn12, hn21, add_zero, zero_add]
    exact hdouble 1
  have hW2 : idForm h₀ n (w₁ + ζ • w₂) (w₁ + ζ • w₂) = 0 := by
    have key : idForm h₀ n (w₁ + ζ • w₂) (w₁ + ζ • w₂) = 1 + h₀.bar ζ * ζ := by
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hn11, hn22, hn12, hn21, RingHom.id_apply]
      ring
    rw [key, hζ1']
    exact hdouble 1
  have hW3 : idForm h₀ n (w₁ + w₂) (w₁ + ζ • w₂) = 1 + ζ := by
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, smul_eq_mul, hn11, hn22, hn12, hn21,
      RingHom.id_apply]
    ring
  have hW3' : idForm h₀ n (w₁ + w₂) (w₁ + ζ • w₂) ≠ 0 := by
    rw [hW3]
    intro h0
    apply hζ2
    have : ζ = -1 := by linear_combination h0
    rw [this, neg_eq_iff_add_eq_zero]
    exact hdouble 1
  have hfixv : ∀ w : Fin n → fixSubfield σ, linOf A₀ w = w →
      embVec (fixSubfield σ) w ∈ LinearMap.ker (linOf (subfieldGL (fixSubfield σ) n A₀) - 1) := by
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, linOf_subfieldGL, hw,
      sub_self]
  have hσv : ∀ w : Fin n → fixSubfield σ, σ ∘ embVec (fixSubfield σ) w = embVec (fixSubfield σ) w :=
    fun w => funext fun i => (w i).2
  have hw₁f := hfixM i0
  have hw₂f := hfixM i1
  refine ⟨embVec (fixSubfield σ) (w₁ + w₂), embVec (fixSubfield σ) (w₁ + ζ • w₂),
    hfixv _ ?_, hfixv _ ?_, hσv _, hσv _, ?_, ?_, ?_⟩
  · rw [map_add]
    exact congrArg₂ (· + ·) hw₁f hw₂f
  · rw [map_add, map_smul]
    exact congrArg₂ (· + ·) hw₁f (congrArg (ζ • ·) hw₂f)
  · rw [idForm_embVec (fixSubfield σ) h₀ hbar, hW1]; rfl
  · rw [idForm_embVec (fixSubfield σ) h₀ hbar, hW2]; rfl
  · rw [idForm_embVec (fixSubfield σ) h₀ hbar]
    intro hc
    exact hW3' (Subtype.ext hc)

end CFSG.RankThree.PartOne
