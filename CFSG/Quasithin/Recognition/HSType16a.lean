module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Recognition.HSType15a
import CFSG.Quasithin.Recognition.HSType16aPack

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Permutation.FinPack CFSG.Quasithin.H13.L32A.C.Alt7Pack
  CFSG.Quasithin.HSType.Pack16a

@[expose] def ιS : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 5 * Equiv.swap 3 4

@[expose] def NormLamS (ρ : Equiv.Perm (Fin 6)) : Prop :=
  ρ * αS * ρ⁻¹ ∈ lamS ∧ ρ * βS * ρ⁻¹ ∈ lamS

instance : DecidablePred NormLamS := fun ρ =>
  inferInstanceAs (Decidable (ρ * αS * ρ⁻¹ ∈ lamS ∧ ρ * βS * ρ⁻¹ ∈ lamS))

theorem normLamS_iff {ρ : Equiv.Perm (Fin 6)} :
    NormLamS ρ ↔ ∀ x ∈ lamS, ρ * x * ρ⁻¹ ∈ lamS := by
  constructor
  · rintro ⟨hα, hβ⟩ x hx
    rw [← closure_αS_βS] at hx
    have hle : Subgroup.closure {αS, βS} ≤ lamS.comap (MulAut.conj ρ).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact hα
      · exact hβ
    exact hle hx
  · intro h
    exact ⟨h _ αS_mem, h _ βS_mem⟩

theorem ιS_conj : ιS * σS0 * ιS⁻¹ ∈ Subgroup.zpowers σS0 := by
  rw [show ιS * σS0 * ιS⁻¹ = σS0 ^ (2 : ℤ) by decide]
  exact Subgroup.zpow_mem_zpowers _ _

theorem ιS_facts : ∀ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))),
    σ * ιS ∈ stabS ∧ σ * ιS ∉ lamS ∧ σ * ιS ∉ fixS ∧ (∀ x, (σ * ιS) x ≠ x) ∧
      (σ * ιS) * (σ * ιS) = 1 ∧ (σ * ιS) * σS0 * (σ * ιS)⁻¹ = σS0⁻¹ ∧ NormLamS (σ * ιS) := by
  intro σ hσ
  have hE : ([1, σS0, σS0 * σS0].map fun s => enc (s * ιS)) = iotaC := by decide +kernel
  have hm : σ ∈ [1, σS0, σS0 * σS0] := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hσ
  have h := allK_iff.1 q7_ok _ (hE ▸ List.mem_map_of_mem (f := fun s => enc (s * ιS)) hm)
  exact facts_of_q7 _ h

theorem sign_of_stabS : ∀ ρ : Equiv.Perm (Fin 6), ρ ∈ stabS → ρ ∉ lam0 → ¬ NormLamS ρ →
    ρ ^ 3 ∉ fixS → Equiv.Perm.sign ρ = 1 := by
  intro ρ h1 h2 h3 h4
  have h := allK_iff.1 q1_ok _ (memK_iff.1 ((mem_stabS_K ρ).1 h1))
  rw [q1, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact absurd ((mem_lam0_K ρ).2 h) h2
  · exact absurd ((normK_iff ρ).2 h) h3
  · rw [← enc_one6, ← enc_pow h6, ← mem_fixS_K] at h
    exact absurd h h4
  · exact (sign_eq_one_iff_evenK h6 ρ).2 h

theorem mem_alt_of_stabS {ρ : Equiv.Perm (Fin 6)} (h1 : ρ ∈ stabS) (h2 : ρ ∉ lam0)
    (h3 : ¬ NormLamS ρ) (h4 : ρ ^ 3 ∉ fixS) : ρ ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (sign_of_stabS ρ h1 h2 h3 h4)

@[expose] def ρS0 : Equiv.Perm (Fin 6) := Equiv.swap 2 4 * Equiv.swap 3 5

theorem mul_ρS0_inv_mem_lam0' : ∀ ρ : Equiv.Perm (Fin 6), ρ ∈ stabS →
    Equiv.Perm.sign ρ = 1 → ρ ∉ lamS → ρ * ρS0⁻¹ ∈ lam0 := by
  intro ρ h1 h2 h3
  have hr : enc ρS0⁻¹ = 3298320 := by decide +kernel
  have h := allK_iff.1 q2_ok _ (memK_iff.1 ((mem_stabS_K ρ).1 h1))
  rw [q2, Bool.or_eq_true, Bool.or_eq_true, (sign_eq_one_iff_evenK h6 ρ).1 h2, Bool.not_true,
    ← mem_lamS_K, ← hr, ← enc_mul h6, ← mem_lam0_K] at h
  rcases h with (h | h) | h
  · exact absurd h Bool.false_ne_true
  · exact absurd h h3
  · exact h

theorem mul_ρS0_inv_mem_lam0 {ρ : Equiv.Perm (Fin 6)} (h1 : ρ ∈ stabS)
    (h2 : ρ ∈ alternatingGroup (Fin 6)) (h3 : ρ ∉ lamS) : ρ * ρS0⁻¹ ∈ lam0 :=
  mul_ρS0_inv_mem_lam0' ρ h1 (Equiv.Perm.mem_alternatingGroup.mp h2) h3

@[expose] def cosetB : List (Equiv.Perm (Fin 6)) :=
  [1, Equiv.swap 1 2 * Equiv.swap 3 4, Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 5 *
    Equiv.swap 5 3, Equiv.swap 1 4 * Equiv.swap 3 5,
    Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 3 2 * Equiv.swap 2 5]

theorem cosetB_mem : ∀ b ∈ cosetB, b ∈ lamS := by
  intro b hb
  have hE : (cosetB.map enc == cosetC) = true := by decide +kernel
  rw [beq_iff_eq] at hE
  have h := allK_iff.1 cosetC_ok _ (hE ▸ List.mem_map_of_mem (f := enc) hb)
  exact (mem_lamS_K b).2 h

theorem alt_eq_union' : ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
    σ ∈ lamS ∨ ∃ b ∈ cosetB, σ * (ρS0 * b)⁻¹ ∈ lamS := by
  intro σ hσ
  have hB : ((cosetB.map fun b => enc (ρS0 * b)⁻¹) == cosetBC) = true := by decide +kernel
  rw [beq_iff_eq] at hB
  have h := walkK_sound q3_ok σ
  rw [q3, Bool.or_eq_true, Bool.or_eq_true, (sign_eq_one_iff_evenK h6 σ).1 hσ, Bool.not_true,
    ← mem_lamS_K, anyK_iff, ← hB] at h
  rcases h with (h | h) | ⟨d, hd, h⟩
  · exact absurd h Bool.false_ne_true
  · exact Or.inl h
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hd
    rw [← enc_mul h6, ← mem_lamS_K] at h
    exact Or.inr ⟨b, hb, h⟩

theorem alt_eq_union {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    σ ∈ lamS ∨ ∃ b ∈ cosetB, σ * (ρS0 * b)⁻¹ ∈ lamS :=
  alt_eq_union' σ (Equiv.Perm.mem_alternatingGroup.mp hσ)

theorem lamS_le_alt : lamS ≤ alternatingGroup (Fin 6) := by
  rw [← closure_αS_βS, Subgroup.closure_le]
  rintro x (rfl | rfl) <;> exact Equiv.Perm.mem_alternatingGroup.mpr (by decide)

@[expose] def evenInv : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap 2 4 * Equiv.swap 3 5, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 4 * Equiv.swap 1 5]

@[expose] def jInv : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap 1 5 * Equiv.swap 2 4, Equiv.swap 0 2 * Equiv.swap 3 5,
    Equiv.swap 0 4 * Equiv.swap 1 3]

theorem mem_evenInv' : ∀ ρ : Equiv.Perm (Fin 6), ρ ∈ stabS → Equiv.Perm.sign ρ = 1 →
    ρ * ρ = 1 → ρ * σS0 * ρ⁻¹ = σS0⁻¹ → ρ ∈ evenInv := by
  intro ρ h1 h2 h3 h4
  have hE : (evenInv.map enc == evenInvC) = true := by decide +kernel
  rw [beq_iff_eq] at hE
  have h := allK_iff.1 q4_ok _ (memK_iff.1 ((mem_stabS_K ρ).1 h1))
  rw [q4, (sign_eq_one_iff_evenK h6 ρ).1 h2, involK_of ρ h3, invertsK_of ρ h4] at h
  simp only [Bool.not_true, Bool.false_or] at h
  rw [mem_iff_enc h6, hE]
  exact memK_iff.1 h

theorem mem_evenInv {ρ : Equiv.Perm (Fin 6)} (h1 : ρ ∈ stabS) (h2 : ρ ∈ alternatingGroup (Fin 6))
    (h3 : ρ * ρ = 1) (h4 : ρ * σS0 * ρ⁻¹ = σS0⁻¹) : ρ ∈ evenInv :=
  mem_evenInv' ρ h1 (Equiv.Perm.mem_alternatingGroup.mp h2) h3 h4

theorem mem_jInv : ∀ ψ : Equiv.Perm (Fin 6), ψ ∈ lamS → ψ ∉ lam0 → ψ * ψ = 1 →
    ψ * σS0 * ψ⁻¹ = σS0⁻¹ → ψ ∈ jInv := by
  intro ψ h1 h2 h3 h4
  have hE : (jInv.map enc == jInvC) = true := by decide +kernel
  rw [beq_iff_eq] at hE
  have h := allK_iff.1 q5_ok _ (memK_iff.1 ((mem_lamS_K ψ).1 h1))
  rw [q5, involK_of ψ h3, invertsK_of ψ h4] at h
  simp only [Bool.not_true, Bool.or_false, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (Subgroup.mem_inf.2 ⟨h1, (mem_stabS_K ψ).2 h⟩) h2
  · rw [mem_iff_enc h6, hE]
    exact memK_iff.1 h

theorem evenInv_mul_jInv_pow_three : ∀ ρ ∈ evenInv, ∀ ψ ∈ jInv, (ρ * ψ) ^ 3 = 1 := by
  intro ρ hρ ψ hψ
  have hE : (evenInv.map enc == evenInvC) = true := by decide +kernel
  have hJ : (jInv.map enc == jInvC) = true := by decide +kernel
  rw [beq_iff_eq] at hE hJ
  have h := allK_iff.1 (allK_iff.1 evenInvC_jInvC_ok _ (hE ▸ List.mem_map_of_mem (f := enc) hρ)) _
    (hJ ▸ List.mem_map_of_mem (f := enc) hψ)
  rw [← enc_mul h6, ← enc_one6, ← enc_pow h6, beq_enc_iff h6] at h
  exact h

@[expose] def ellList : List (Equiv.Perm (Fin 6)) :=
  [1, Equiv.swap 0 5 * Equiv.swap 5 3 * Equiv.swap 1 4 * Equiv.swap 4 2,
    Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 1 5 * Equiv.swap 5 2,
    Equiv.swap 0 1 * Equiv.swap 4 5, Equiv.swap 0 5 * Equiv.swap 1 4 * Equiv.swap 2 3,
    Equiv.swap 2 5 * Equiv.swap 5 3 * Equiv.swap 3 4,
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5,
    Equiv.swap 0 1 * Equiv.swap 2 4 * Equiv.swap 3 5]

theorem ellList_facts : ∀ ℓ ∈ ellList, ℓ ∈ stabS ∧ NormLamS ℓ ∧ NormLamS ℓ⁻¹ := by
  intro ℓ hℓ
  have hE : (ellList.map enc == ellC) = true := by decide +kernel
  rw [beq_iff_eq] at hE
  have h := allK_iff.1 ellC_ok _ (hE ▸ List.mem_map_of_mem (f := enc) hℓ)
  rw [Bool.and_eq_true, Bool.and_eq_true, ← enc_inv_invCK h6] at h
  exact ⟨(mem_stabS_K ℓ).2 h.1.1, (normK_iff ℓ).2 h.1.2, (normK_iff ℓ⁻¹).2 h.2⟩

theorem exists_ell : ∀ τ : Equiv.Perm (Fin 6), τ ∈ stabS → τ ^ 3 = 1 → τ ≠ 1 →
    ∃ ℓ ∈ ellList, ℓ * τ * ℓ⁻¹ = σS0 := by
  intro τ h1 h2 h3
  have hE : (ellList.map enc == ellC) = true := by decide +kernel
  rw [beq_iff_eq] at hE
  have h := allK_iff.1 q6_ok _ (memK_iff.1 ((mem_stabS_K τ).1 h1))
  have h1' : Nat.beq (enc τ) one6 = false := by
    rw [← enc_one6]
    exact beq_enc_false h6 h3
  rw [q6, pow3K_of τ h2, h1'] at h
  simp only [Bool.not_true, Bool.false_or] at h
  obtain ⟨d, hd, h⟩ := anyK_iff.1 h
  rw [← hE] at hd
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hd
  rw [← enc_inv_invCK h6, ← enc_mul h6, ← enc_mul h6, ← enc_σS0, beq_enc_iff h6] at h
  exact ⟨ℓ, hℓ, h⟩

end CFSG.Quasithin.HSType
