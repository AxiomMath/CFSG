module

public import CFSG.Milestones.ASVolI.H13

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code

@[expose] def id24 : Array ℕ := Array.ofFn fun i : Fin 24 => (i : ℕ)

@[expose] def comp24 (a b : Array ℕ) : Array ℕ := Array.ofFn fun i : Fin 24 => a[b[(i : ℕ)]!]!

@[expose] def conj24 (a t : Array ℕ) : Array ℕ := comp24 (comp24 a t) (invArr a)

theorem getElem!_id24 {i : ℕ} (hi : i < 24) : id24[i]! = i := by
  rw [id24, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem getElem!_comp24 (a b : Array ℕ) {i : ℕ} (hi : i < 24) :
    (comp24 a b)[i]! = a[b[i]!]! := by
  rw [comp24, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem hasArr_one : HasArr (1 : S24) id24 := fun i => by
  rw [getElem!_id24 i.2]
  rfl

theorem hasArr_mul {σ τ : S24} {a b : Array ℕ} (hσ : HasArr σ a) (hτ : HasArr τ b) :
    HasArr (σ * τ) (comp24 a b) := fun i => by
  rw [getElem!_comp24 a b i.2, Equiv.Perm.mul_apply, hσ, hτ]

theorem hasArr_unique {σ τ : S24} {a : Array ℕ} (hσ : HasArr σ a) (hτ : HasArr τ a) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ i).trans (hτ i).symm)

theorem hasArr_inv_of_inAutOK {σ : S24} {a : Array ℕ} (hσ : HasArr σ a)
    (h : inAutOK a = true) : HasArr σ⁻¹ (invArr a) := by
  simp only [inAutOK, Bool.and_eq_true] at h
  have hperm : σ = permOfArr 24 a (invArr a) h.1 := hasArr_unique hσ (hasArr_permOfArr h.1)
  rw [hperm]
  exact hasArr_permOfArr_inv h.1

theorem hasArr_conj {σ τ : S24} {a t : Array ℕ} (hσ : HasArr σ a) (h : inAutOK a = true)
    (hτ : HasArr τ t) : HasArr (σ * τ * σ⁻¹) (conj24 a t) :=
  hasArr_mul (hasArr_mul hσ hτ) (hasArr_inv_of_inAutOK hσ h)

theorem mem_M24g_of_arr {σ : S24} {a : Array ℕ} (hσ : HasArr σ a) (h : inAutOK a = true) :
    σ ∈ M24g := by
  obtain ⟨σ', hσ', harr⟩ := exists_of_inAutOK h
  rw [hasArr_unique hσ harr]
  exact hσ'

theorem mem_M23g_of_arr {σ : S24} {a : Array ℕ} (hσ : HasArr σ a) (h : inAutOK a = true)
    (k : Fin 24) (hk : a[(k : ℕ)]! = k) : σ ∈ M23g k := by
  rw [CFSG.ASVolI.mem_M23g_iff]
  exact ⟨mem_M24g_of_arr hσ h, Fin.ext ((hσ k).trans hk)⟩

@[expose] noncomputable def permOfArrD (a : Array ℕ) : S24 :=
  if h : InvPairOK 24 a (invArr a) = true then permOfArr 24 a (invArr a) h else 1

theorem hasArr_permOfArrD {a : Array ℕ} (h : inAutOK a = true) : HasArr (permOfArrD a) a := by
  simp only [inAutOK, Bool.and_eq_true] at h
  rw [permOfArrD, dif_pos h.1]
  exact hasArr_permOfArr h.1

theorem permOfArrD_mem_M24g {a : Array ℕ} (h : inAutOK a = true) : permOfArrD a ∈ M24g :=
  mem_M24g_of_arr (hasArr_permOfArrD h) h

end CFSG.Quasithin.AppendixH.H14
