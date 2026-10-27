module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwo
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem exists_perm_map_eq_of_card_eq {α : Type*} [DecidableEq α] [Fintype α]
    {I J : Finset α} (hIJ : I.card = J.card) : ∃ ρ : Equiv.Perm α, I.map ρ.toEmbedding = J := by
  classical
  let e : I ≃ J := Finset.equivOfCardEq hIJ
  refine ⟨e.extendSubtype, Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_map, hIJ])⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
  exact Equiv.extendSubtype_mem e x hx

section Perm

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

@[expose] noncomputable def permSUHom : Equiv.Perm (Fin n) →* unitarySU 2 f K n where
  toFun σ := permSU h σ⁻¹
  map_one' := Subtype.ext (Units.ext (by
    change (((1 : Equiv.Perm (Fin n))⁻¹).permMatrix K) = 1
    rw [inv_one, Matrix.permMatrix_one]))
  map_mul' σ τ := Subtype.ext (Units.ext (by
    change ((σ * τ)⁻¹.permMatrix K) = σ⁻¹.permMatrix K * τ⁻¹.permMatrix K
    rw [_root_.mul_inv_rev, Matrix.permMatrix_mul]))

theorem permSUHom_apply (σ : Equiv.Perm (Fin n)) : permSUHom h σ = permSU h σ⁻¹ :=
  rfl

theorem permSU_swap_mem_unitaryBlock (a b : Fin n) :
    permSU h (Equiv.swap a b) ∈ unitaryBlock h {a, b} := by
  rw [mem_unitaryBlock]
  intro i j hij
  rw [coe_permSU]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  rcases hij with hi | hj
  · have hia : i ≠ a := fun e => hi (by simp [e])
    have hib : i ≠ b := fun e => hi (by simp [e])
    rw [Equiv.swap_apply_of_ne_of_ne hia hib, one_apply]
  · have hja : j ≠ a := fun e => hj (by simp [e])
    have hjb : j ≠ b := fun e => hj (by simp [e])
    by_cases hij' : i = j
    · subst hij'
      rw [Equiv.swap_apply_of_ne_of_ne hja hjb, one_apply_eq, ite_eq_left_iff]
      exact fun h' => absurd rfl h'
    · rw [one_apply_ne hij', ite_eq_right_iff]
      intro e
      exfalso
      rcases eq_or_ne i a with hia | hia
      · rw [hia, Equiv.swap_apply_left] at e
        exact hjb e.symm
      · rcases eq_or_ne i b with hib | hib
        · rw [hib, Equiv.swap_apply_right] at e
          exact hja e.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hia hib] at e
          exact hij' e

end Perm

section Adjacent

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem iSup_unitaryBlock_eq_top_of_adjacent {m : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) {ι : Type*}
    [Nonempty ι] (W : ι → Finset (Fin n)) (hW : ∀ i, (W i).card = m)
    (hadj : ∀ a b : Fin n, b.val = a.val + 1 → ∃ i, a ∈ W i ∧ b ∈ W i) :
    ⨆ i, unitaryBlock h (W i) = ⊤ := by
  set H := ⨆ i, unitaryBlock h (W i) with hH
  have hperm : ∀ σ : Equiv.Perm (Fin n), permSUHom h σ ∈ H := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hle : Submonoid.closure (Set.range fun k : Fin n' => Equiv.swap k.castSucc k.succ) ≤
        (H.comap (permSUHom h)).toSubmonoid := by
      rw [Submonoid.closure_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨i, hai, hbi⟩ := hadj k.castSucc k.succ (by simp)
      show permSUHom h (Equiv.swap k.castSucc k.succ) ∈ H
      rw [permSUHom_apply, Equiv.swap_inv]
      refine le_iSup (fun i => unitaryBlock h (W i)) i (unitaryBlock_mono h ?_
        (permSU_swap_mem_unitaryBlock h _ _))
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hai
      · rw [Finset.mem_singleton.1 hx]
        exact hbi
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hle
    intro σ
    exact hle (Submonoid.mem_top σ)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hblock : ∀ I : Finset (Fin n), I.card = m → unitaryBlock h I ≤ H := by
    intro I hI
    obtain ⟨ρ, hρ⟩ := exists_perm_map_eq_of_card_eq ((hW i₀).trans hI.symm)
    rw [← hρ, ← map_conj_permSU_unitaryBlock h ρ (W i₀)]
    rintro _ ⟨x, hx, rfl⟩
    have hP : permSU h ρ.symm ∈ H := hperm ρ
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem hP (le_iSup (fun i => unitaryBlock h (W i)) i₀ hx))
      (H.inv_mem hP)
  rw [eq_top_iff, ← iSup_unitaryBlock_card_eq_top h hm hmn]
  exact iSup₂_le fun I hI => hblock I hI

@[expose] def window4 (i : Fin (n - 3)) : Finset (Fin n) :=
  Finset.Icc ⟨i, by omega⟩ ⟨i + 3, by omega⟩

omit [Field K] in
theorem mem_window4 {i : Fin (n - 3)} {j : Fin n} :
    j ∈ window4 i ↔ (i : ℕ) ≤ j ∧ (j : ℕ) ≤ i + 3 := by
  rw [window4, Finset.mem_Icc, Fin.le_def, Fin.le_def]

omit [Field K] in
theorem card_window4 (i : Fin (n - 3)) : (window4 i).card = 4 := by
  rw [window4, Fin.card_Icc]
  simp only
  omega

theorem iSup_unitaryBlock_Icc_eq_top (hn : 4 ≤ n) :
    ⨆ i : Fin (n - 3), unitaryBlock h (window4 i) = ⊤ := by
  have : Nonempty (Fin (n - 3)) := ⟨⟨0, by omega⟩⟩
  refine iSup_unitaryBlock_eq_top_of_adjacent h le_rfl hn window4 card_window4 fun a b hab => ?_
  refine ⟨⟨min a (n - 4), by omega⟩, ?_, ?_⟩ <;> rw [mem_window4] <;> simp only <;> omega

theorem iSup_blockSU_Icc_eq_top (hn : 4 ≤ n) :
    ⨆ i : Fin (n - 3), blockSU h (window4 i) = ⊤ := by
  have h1 := congrArg (Subgroup.map (unitaryProj h n)) (iSup_unitaryBlock_Icc_eq_top h hn)
  rw [Subgroup.map_top_of_surjective _ (unitaryProj_surjective h n), Subgroup.map_iSup] at h1
  exact h1

theorem eq_of_eqOn_blockSU_Icc {M : Type*} [Monoid M] (hn : 4 ≤ n)
    {φ₁ φ₂ : unitaryPSU h n →* M}
    (hφ : ∀ i : Fin (n - 3), ∀ x ∈ blockSU h (window4 i), φ₁ x = φ₂ x) : φ₁ = φ₂ := by
  have hle : (⨆ i : Fin (n - 3), blockSU h (window4 i)) ≤ φ₁.eqLocus φ₂ :=
    iSup_le fun i x hx => hφ i x hx
  rw [iSup_blockSU_Icc_eq_top h hn] at hle
  exact MonoidHom.ext fun x => hle (mem_top x)

end Adjacent

end CFSG.SeitzReduction.UnitaryPilot
