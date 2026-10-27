module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Phan

theorem blockMat_apply_of_forall_ne {F : Type*} [Field F] {m i k : ℕ}
    (A : Matrix (Fin k) (Fin k) F) (a b : Fin m)
    (hab : (∀ j : Fin k, (a : ℕ) ≠ i + j) ∨ ∀ j : Fin k, (b : ℕ) ≠ i + j) :
    CFSG.ClassicalInvolution.Phan.blockMat m i A a b = (1 : Matrix (Fin m) (Fin m) F) a b := by
  unfold CFSG.ClassicalInvolution.Phan.blockMat
  rw [Matrix.add_apply, add_eq_left]
  rcases hab with ha | hb
  · have hrow : ∀ j, CFSG.ClassicalInvolution.Phan.blockSel F m k i a j = 0 := fun j => by
      rw [CFSG.ClassicalInvolution.Phan.blockSel_apply]
      simp [ha j]
    simp [Matrix.mul_apply, hrow]
  · have hcol : ∀ j, CFSG.ClassicalInvolution.Phan.blockSel F m k i b j = 0 := fun j => by
      rw [CFSG.ClassicalInvolution.Phan.blockSel_apply]
      simp [hb j]
    simp [Matrix.mul_apply, Matrix.transpose_apply, hcol]

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem iSup_unitaryBlock_pair_eq_top (hf : 2 ≤ f) (m : ℕ) :
    ⨆ i : Fin m, unitaryBlock h ({i.castSucc, i.succ} : Finset (Fin (m + 1))) = ⊤ := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hq : 2 ^ f ≠ 2 := by
    intro h2
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hPhan := CFSG.ClassicalInvolution.Phan.iSup_range_blockEmb2 (K := K) (p := 2) (f := f) hK
    hq m
  have hSU : CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution K 2 f)
      (m + 1) = unitarySU 2 f K (m + 1) :=
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK (m + 1)
  set φ := (MulEquiv.subgroupCongr hSU).toMonoidHom with hφ
  have hmap : (⨆ i : Fin m, (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 f m i).range).map φ ≤
      ⨆ i : Fin m, unitaryBlock h ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
    rw [Subgroup.map_iSup]
    refine iSup_mono fun i => ?_
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    rw [mem_unitaryBlock]
    intro a b hab
    refine blockMat_apply_of_forall_ne _ a b ?_
    have hout : ∀ c : Fin (m + 1), c ∉ ({i.castSucc, i.succ} : Finset (Fin (m + 1))) →
        ∀ j : Fin 2, (c : ℕ) ≠ (i : ℕ) + j := by
      intro c hc j hcj
      apply hc
      have hj := j.isLt
      rcases Nat.lt_or_ge (j : ℕ) 1 with hj1 | hj1
      · have : (c : ℕ) = i := by omega
        exact Finset.mem_insert.2 (Or.inl (Fin.ext (by simpa using this)))
      · have : (c : ℕ) = i + 1 := by omega
        exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (Fin.ext (by simpa using this))))
    rcases hab with ha | hb
    · exact Or.inl (hout a ha)
    · exact Or.inr (hout b hb)
  rw [eq_top_iff]
  intro x _
  have hx : (MulEquiv.subgroupCongr hSU).symm x ∈
      ⨆ i : Fin m, (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 f m i).range := hPhan ▸ mem_top _
  have := hmap ⟨_, hx, rfl⟩
  rwa [hφ, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this

end Phan

section Perm

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem permSU_mem_of_swap_mem {H : Subgroup (unitarySU 2 f K n)} (a₀ : Fin n)
    (hswap : ∀ y, permSU h (Equiv.swap a₀ y) ∈ H) (σ : Equiv.Perm (Fin n)) : permSU h σ ∈ H := by
  set M : Subgroup (Equiv.Perm (Fin n)) := H.comap (permSUHom h) with hM
  have hM0 : ∀ y, Equiv.swap a₀ y ∈ M := fun y => by
    rw [hM, mem_comap, permSUHom_apply, Equiv.swap_inv]
    exact hswap y
  have hall : ∀ a b : Fin n, Equiv.swap a b ∈ M := fun a b =>
    SubmonoidClass.swap_mem_trans M (by rw [Equiv.swap_comm]; exact hM0 a) (hM0 b)
  have htop : M = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, closure_le]
    rintro _ ⟨a, b, -, rfl⟩
    exact hall a b
  have hσ : σ⁻¹ ∈ M := htop ▸ mem_top _
  rw [hM, mem_comap, permSUHom_apply, inv_inv] at hσ
  exact hσ

theorem unitaryBlock_le_of_permSU_mem {H : Subgroup (unitarySU 2 f K n)}
    (hperm : ∀ σ : Equiv.Perm (Fin n), permSU h σ ∈ H) {I J : Finset (Fin n)}
    (hIJ : I.card = J.card) (hI : unitaryBlock h I ≤ H) : unitaryBlock h J ≤ H := by
  obtain ⟨ρ, hρ⟩ := exists_perm_map_eq_of_card_eq hIJ
  rw [← hρ, ← map_conj_permSU_unitaryBlock h ρ I]
  rintro _ ⟨x, hx, rfl⟩
  have hP : permSU h ρ.symm ∈ H := hperm ρ.symm
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact H.mul_mem (H.mul_mem hP (hI hx)) (H.inv_mem hP)

end Perm

section Sunflower

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem iSup_unitaryBlock_insert_eq_top {A : Finset (Fin n)} (hA2 : 2 ≤ A.card)
    (hAn : A.card < n) (hcase : 3 ≤ A.card ∨ 2 ≤ f) :
    ⨆ x : {x : Fin n // x ∉ A}, unitaryBlock h (insert (x : Fin n) A) = ⊤ := by
  set H := ⨆ x : {x : Fin n // x ∉ A}, unitaryBlock h (insert (x : Fin n) A) with hH
  obtain ⟨x₀, -, hx₀⟩ : ∃ x ∈ (Finset.univ : Finset (Fin n)), x ∉ A :=
    Finset.exists_mem_notMem_of_card_lt_card (by simpa using hAn)
  have hle : ∀ x : {x : Fin n // x ∉ A}, unitaryBlock h (insert (x : Fin n) A) ≤ H := fun x =>
    le_iSup (fun x : {x : Fin n // x ∉ A} => unitaryBlock h (insert (x : Fin n) A)) x
  obtain ⟨a₀, ha₀⟩ : A.Nonempty := Finset.card_pos.1 (by omega)
  have hswap : ∀ y, permSU h (Equiv.swap a₀ y) ∈ H := by
    intro y
    by_cases hy : y ∈ A
    · refine hle ⟨x₀, hx₀⟩ (unitaryBlock_mono h ?_ (permSU_swap_mem_unitaryBlock h a₀ y))
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact Finset.mem_insert_of_mem ha₀
      · rw [Finset.mem_singleton.1 hz]
        exact Finset.mem_insert_of_mem hy
    · refine hle ⟨y, hy⟩ (unitaryBlock_mono h ?_ (permSU_swap_mem_unitaryBlock h a₀ y))
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact Finset.mem_insert_of_mem ha₀
      · rw [Finset.mem_singleton.1 hz]
        exact Finset.mem_insert_self _ _
  have hperm := permSU_mem_of_swap_mem h a₀ hswap
  have hcard : (insert x₀ A).card = A.card + 1 := Finset.card_insert_of_notMem hx₀
  rcases hcase with h3 | hf
  ·
    rw [eq_top_iff, ← iSup_unitaryBlock_card_eq_top h (m := A.card + 1) (by omega) (by omega)]
    refine iSup₂_le fun J hJ => ?_
    exact unitaryBlock_le_of_permSU_mem h hperm (hcard.trans hJ.symm) (hle ⟨x₀, hx₀⟩)
  ·
    obtain ⟨a₁, ha₁, ha₁₀⟩ : ∃ a₁ ∈ A, a₁ ≠ a₀ := by
      by_contra hne
      push Not at hne
      have : A ⊆ {a₀} := fun z hz => Finset.mem_singleton.2 (hne z hz)
      have := Finset.card_le_card this
      rw [Finset.card_singleton] at this
      omega
    have hpair : unitaryBlock h ({a₀, a₁} : Finset (Fin n)) ≤ H := by
      refine (unitaryBlock_mono h ?_).trans (hle ⟨x₀, hx₀⟩)
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact Finset.mem_insert_of_mem ha₀
      · rw [Finset.mem_singleton.1 hz]
        exact Finset.mem_insert_of_mem ha₁
    have hpair2 : ({a₀, a₁} : Finset (Fin n)).card = 2 := Finset.card_pair ha₁₀.symm
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [eq_top_iff, ← iSup_unitaryBlock_pair_eq_top h hf m]
    refine iSup_le fun i => ?_
    refine unitaryBlock_le_of_permSU_mem h hperm ?_ hpair
    rw [hpair2, Finset.card_pair (Fin.castSucc_lt_succ (i := i)).ne]

theorem iSup_blockSU_insert_eq_top {A : Finset (Fin n)} (hA2 : 2 ≤ A.card) (hAn : A.card < n)
    (hcase : 3 ≤ A.card ∨ 2 ≤ f) :
    ⨆ x : {x : Fin n // x ∉ A}, blockSU h (insert (x : Fin n) A) = ⊤ := by
  have h1 := congrArg (Subgroup.map (unitaryProj h n))
    (iSup_unitaryBlock_insert_eq_top h hA2 hAn hcase)
  rw [Subgroup.map_top_of_surjective _ (unitaryProj_surjective h n), Subgroup.map_iSup] at h1
  exact h1

end Sunflower

end CFSG.SeitzReduction.UnitaryPilot
