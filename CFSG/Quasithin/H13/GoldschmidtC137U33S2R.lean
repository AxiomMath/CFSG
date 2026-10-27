module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Ppt

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat CFSG.LieType.BorelTits

@[expose] def Rsub : Subgroup Gam where
  carrier := {g | ∃ k < 32, g = sEltG (2 * k)}
  mul_mem' := by
    rintro _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
    obtain ⟨m, hm, h⟩ := r₀_checks.1 k hk l hl
    refine ⟨m, hm, eq_of_code ?_⟩
    simp only [matCode_mulG, matCode_sEltG (by omega : 2 * k < 64),
      matCode_sEltG (by omega : 2 * l < 64), matCode_sEltG (by omega : 2 * m < 64)]
    exact h
  one_mem' := ⟨0, by norm_num, by rw [Nat.mul_zero, sEltG_zero]⟩
  inv_mem' := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨l, hl, h⟩ := r₀_checks.2.1 k hk
    refine ⟨l, hl, inv_eq_of_mul_eq_one_right (eq_of_code ?_)⟩
    simp only [matCode_mulG, matCode_sEltG (by omega : 2 * k < 64),
      matCode_sEltG (by omega : 2 * l < 64)]
    exact h.trans matCode_one.symm

theorem Rsub_le_S : Rsub ≤ sSubG := by
  rintro _ ⟨k, hk, rfl⟩
  exact mem_sSubG.2 ⟨2 * k, by omega, rfl⟩

theorem S_norm_R {s r : Gam} (hs : s ∈ sSubG) (hr : r ∈ Rsub) : s * r * s⁻¹ ∈ Rsub := by
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hs
  obtain ⟨k, hk, rfl⟩ := hr
  obtain ⟨l, hl, h⟩ := r₀_checks.2.2.1 i hi k hk
  refine ⟨l, hl, ?_⟩
  have h1 : sEltG i * sEltG (2 * k) = sEltG (2 * l) * sEltG i := eq_of_code (by
    simp only [matCode_mulG, matCode_sEltG hi, matCode_sEltG (by omega : 2 * k < 64),
      matCode_sEltG (by omega : 2 * l < 64)]
    exact h)
  rw [h1]
  group

theorem b_norm_R {r : Gam} (hr : r ∈ Rsub) : b₀ * r * b₀⁻¹ ∈ Rsub := by
  obtain ⟨k, hk, rfl⟩ := hr
  obtain ⟨l, hl, h⟩ := r₀_checks.2.2.2 k hk
  refine ⟨l, hl, ?_⟩
  have h1 : b₀ * sEltG (2 * k) = sEltG (2 * l) * b₀ := eq_of_code (by
    simp only [matCode_mulG, matCode_b₀, matCode_sEltG (by omega : 2 * k < 64),
      matCode_sEltG (by omega : 2 * l < 64)]
    exact h)
  rw [h1]
  group

theorem Ppt_conj_R {g r : Gam} (hg : g ∈ Ppt) (hr : r ∈ Rsub) : g * r * g⁻¹ ∈ Rsub := by
  rcases mem_Ppt_iff.1 hg with h | ⟨s₁, hs₁, s₂, hs₂, rfl⟩
  · exact S_norm_R h hr
  · have h1 := S_norm_R hs₂ hr
    have h2 := b_norm_R h1
    have h3 := S_norm_R hs₁ h2
    simpa [mul_assoc] using h3

theorem Ppt_le_normalizer_R : Ppt ≤ normalizer (Rsub : Set Gam) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact Ppt_conj_R hg
  · intro h
    have := Ppt_conj_R (inv_mem hg) h
    simpa [mul_assoc] using this

theorem isPGroup_S : IsPGroup 2 ↥sSubG := sylowSub.isPGroup'

theorem isPGroup_R : IsPGroup 2 ↥Rsub := isPGroup_S.to_le Rsub_le_S

theorem isSylowTwoOf_S_Ppt : CFSG.QuasithinUnique.IsSylowTwoOf sSubG Ppt := by
  refine ⟨sSubG_le_Ppt, isPGroup_S, ?_⟩
  have h := Subgroup.card_mul_index (sSubG.subgroupOf Ppt)
  have hc : Nat.card (sSubG.subgroupOf Ppt) = 64 := by
    rw [← card_sSubG]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe sSubG_le_Ppt).toEquiv
  rw [hc, show Nat.card ↥Ppt = 192 from card_Ppt] at h
  rw [show (sSubG.subgroupOf Ppt).index = 3 by omega]
  decide

theorem even_of_conj : ∀ i < 64, (∃ l < 64, mmul (mmul (mmul bCode bCode) (sM i)) bCode = sM l) →
    ∃ k < 32, i = 2 * k := by
  decide +kernel

theorem pCoreOf_Ppt : pCoreOf 2 Ppt = Rsub := by
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 (Rsub_le_S.trans sSubG_le_Ppt)
    Ppt_le_normalizer_R isPGroup_R)
  intro x hx
  have hxS : x ∈ sSubG := pCoreOf_two_le_of_sylowIn
    isSylowTwoOf_S_Ppt.1 isSylowTwoOf_S_Ppt.2.1 isSylowTwoOf_S_Ppt.2.2 hx
  have hconj : b₀⁻¹ * x * b₀ ∈ pCoreOf 2 Ppt := by
    have := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 Ppt (inv_mem b₀_mem_Ppt)) x
    simpa using this.1 hx
  have hconjS : b₀⁻¹ * x * b₀ ∈ sSubG := pCoreOf_two_le_of_sylowIn
    isSylowTwoOf_S_Ppt.1 isSylowTwoOf_S_Ppt.2.1 isSylowTwoOf_S_Ppt.2.2 hconj
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hxS
  obtain ⟨l, hl, hle⟩ := mem_sSubG.1 hconjS
  obtain ⟨k, hk, hik⟩ := even_of_conj i hi ⟨l, hl, by
    have := congrArg (fun g : Gam => matCode g.1) hle
    simp only [matCode_mulG, matCode_sEltG hi, matCode_sEltG hl, b₀_inv, matCode_b₀] at this
    exact this.symm⟩
  exact ⟨k, hk, by rw [← hik]⟩

@[expose] def Alist : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14]

theorem A_mul : ∀ i ∈ Alist, ∀ j ∈ Alist, ∃ k ∈ Alist, mmul (sM i) (sM j) = sM k := by
  decide +kernel

theorem A_sq : ∀ i ∈ Alist, mmul (sM i) (sM i) = idMat := by
  decide +kernel

theorem A_comm : ∀ i ∈ Alist, ∀ j ∈ Alist, mmul (sM i) (sM j) = mmul (sM j) (sM i) := by
  decide +kernel

theorem A_lt : ∀ i ∈ Alist, i < 64 := by
  decide

theorem A_even : ∀ i ∈ Alist, ∃ k < 32, i = 2 * k := by
  decide

@[expose] def Asub : Subgroup Gam where
  carrier := {g | ∃ i ∈ Alist, g = sEltG i}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    obtain ⟨k, hk, h⟩ := A_mul i hi j hj
    exact ⟨k, hk, eq_of_code (by
      simp only [matCode_mulG, matCode_sEltG (A_lt i hi), matCode_sEltG (A_lt j hj),
        matCode_sEltG (A_lt k hk)]
      exact h)⟩
  one_mem' := ⟨0, by decide, sEltG_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨i, hi, inv_eq_of_mul_eq_one_right (eq_of_code ?_)⟩
    simp only [matCode_mulG, matCode_sEltG (A_lt i hi)]
    exact (A_sq i hi).trans matCode_one.symm

theorem Asub_le_Rsub : Asub ≤ Rsub := by
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨k, hk, rfl⟩ := A_even i hi
  exact ⟨k, hk, rfl⟩

theorem Asub_le_S : Asub ≤ sSubG := Asub_le_Rsub.trans Rsub_le_S

theorem mem_idx_Asub {i : ℕ} : i ∈ idx Asub ↔ i ∈ Alist := by
  rw [mem_idx]
  constructor
  · rintro ⟨hi, j, hj, h⟩
    rwa [sEltG_injective hi (A_lt j hj) h]
  · intro hi
    exact ⟨A_lt i hi, i, hi, rfl⟩

theorem card_Asub : Nat.card Asub = 8 := by
  rw [card_eq_idx Asub_le_S]
  have : idx Asub = Alist.toFinset := by
    ext i
    rw [mem_idx_Asub, List.mem_toFinset]
  rw [this]
  decide

end CFSG.Quasithin.H13.U3.GC137.S2
