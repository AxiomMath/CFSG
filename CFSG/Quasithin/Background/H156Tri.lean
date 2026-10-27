module

public import CFSG.Quasithin.Background.H158UTrio

public section

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Monster.Code CFSG.Quasithin
open scoped Pointwise

@[expose] def VA (A : Finset (Fin 24)) : Subgroup W11 :=
  Subgroup.closure {x | ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ x = cocodeCoords.κ (pairVec i j)}

theorem rho_mem_VA (g : ↥AutPerm) {A : Finset (Fin 24)} {x : W11} (hx : x ∈ VA A) :
    rhoM24 g x ∈ VA ((g : Equiv.Perm (Fin 24)) • A) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, hj, hij, rfl⟩ := hy
    rw [rhoM24, rho11_pairVec]
    refine Subgroup.subset_closure ⟨(g : Equiv.Perm (Fin 24)) i, ?_,
      (g : Equiv.Perm (Fin 24)) j, ?_,
      (g : Equiv.Perm (Fin 24)).injective.ne hij, rfl⟩
    · exact Finset.mem_smul_finset.2 ⟨i, hi, rfl⟩
    · exact Finset.mem_smul_finset.2 ⟨j, hj, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ ihx ihy => rw [map_mul]; exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih => rw [map_inv]; exact Subgroup.inv_mem _ ih

@[expose] def vaBasis (p : List ℕ) : List ℕ := p.tail.map fun a => pairImg11 (p.headD 0) a

theorem vaBasis_lt (p : List ℕ) : ∀ a ∈ vaBasis p, a < 2 ^ 11 := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  exact actM_lt ccECols_lt _

theorem VA_le_maskSub {A : Finset (Fin 24)} {p : List ℕ} (hA : ∀ x : Fin 24, x ∈ A ↔ (x : ℕ) ∈ p)
    (h1 : ∀ i ∈ p, ∀ j ∈ p, i ≠ j → pairImg11 i j ∈ combos (vaBasis p)) :
    VA A ≤ maskSub 11 (vaBasis p) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, j, hj, hij, rfl⟩
  rw [kappa11_pairVec_mask i j hij]
  exact toW_mem_maskSub (h1 i ((hA i).1 hi) j ((hA j).1 hj) (fun h => hij (Fin.ext h)))

theorem maskSub_le_VA {A : Finset (Fin 24)} {p : List ℕ} (hA : ∀ x : Fin 24, x ∈ A ↔ (x : ℕ) ∈ p)
    (h0 : p.headD 0 ∈ p) (h24 : ∀ a ∈ p, a < 24) (hne : ∀ a ∈ p.tail, a ≠ p.headD 0) :
    maskSub 11 (vaBasis p) ≤ VA A := by
  rintro _ ⟨m, hm, rfl⟩
  refine (MaskCoords.std 11).vm_mem_of_combos (VA A) (l := vaBasis p) ?_ m hm
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
  have ha' : a ∈ p := List.mem_of_mem_tail ha
  have hne' : (⟨p.headD 0, h24 _ h0⟩ : Fin 24) ≠ ⟨a, h24 _ ha'⟩ := fun h =>
    hne a ha (by simpa using (congrArg Fin.val h).symm)
  have e : (MaskCoords.std 11).vm (pairImg11 (p.headD 0) a) =
      cocodeCoords.κ (pairVec ⟨p.headD 0, h24 _ h0⟩ ⟨a, h24 _ ha'⟩) :=
    (kappa11_pairVec_mask _ _ hne').symm
  rw [e]
  exact Subgroup.subset_closure ⟨⟨p.headD 0, h24 _ h0⟩, (hA _).2 h0, ⟨a, h24 _ ha'⟩, (hA _).2 ha',
    hne', rfl⟩

theorem mem_UT_of_inter {p q : List ℕ}
    (h : ∀ m ∈ combos (vaBasis p), m ∈ combos (vaBasis q) → m ∈ uTMasks) {x : W11}
    (hp : x ∈ maskSub 11 (vaBasis p)) (hq : x ∈ maskSub 11 (vaBasis q)) : x ∈ UT := by
  obtain ⟨m, hm, rfl⟩ := hp
  obtain ⟨m', hm', hmm⟩ := hq
  have e : m' = m := toW_inj (combos_lt (vaBasis_lt q) m' hm') (combos_lt (vaBasis_lt p) m hm) hmm
  subst e
  exact (toW_mem_UT_iff (combos_lt (vaBasis_lt p) m' hm)).2 (h m' hm hm')

theorem UT_le_maskSub {p : List ℕ} (h : ∀ m ∈ uTMasks, m ∈ combos (vaBasis p)) {x : W11}
    (hx : x ∈ UT) : x ∈ maskSub 11 (vaBasis p) := by
  obtain ⟨m, hm, rfl⟩ := hx
  have hlt : m < 2 ^ 11 := combos_lt uTBasis_lt m hm
  exact ⟨m, h m ((uT_combos m hlt).1 hm), rfl⟩

theorem vaBasis_o0 : ∀ i ∈ o0L, ∀ j ∈ o0L, i ≠ j → pairImg11 i j ∈ combos (vaBasis o0L) := by
  decide +kernel

theorem vaBasis_o1 : ∀ i ∈ o1L, ∀ j ∈ o1L, i ≠ j → pairImg11 i j ∈ combos (vaBasis o1L) := by
  decide +kernel

theorem vaBasis_o2 : ∀ i ∈ o2L, ∀ j ∈ o2L, i ≠ j → pairImg11 i j ∈ combos (vaBasis o2L) := by
  decide +kernel

theorem inter_01 : ∀ m ∈ combos (vaBasis o0L), m ∈ combos (vaBasis o1L) → m ∈ uTMasks := by
  decide +kernel

theorem inter_02 : ∀ m ∈ combos (vaBasis o0L), m ∈ combos (vaBasis o2L) → m ∈ uTMasks := by
  decide +kernel

theorem inter_12 : ∀ m ∈ combos (vaBasis o1L), m ∈ combos (vaBasis o2L) → m ∈ uTMasks := by
  decide +kernel

theorem UT_o0 : ∀ m ∈ uTMasks, m ∈ combos (vaBasis o0L) := by decide +kernel

theorem UT_o1 : ∀ m ∈ uTMasks, m ∈ combos (vaBasis o1L) := by decide +kernel

theorem UT_o2 : ∀ m ∈ uTMasks, m ∈ combos (vaBasis o2L) := by decide +kernel

theorem o0L_head : o0L.headD 0 ∈ o0L := by decide +kernel

theorem o1L_head : o1L.headD 0 ∈ o1L := by decide +kernel

theorem o2L_head : o2L.headD 0 ∈ o2L := by decide +kernel

theorem o0L_lt : ∀ a ∈ o0L, a < 24 := by decide +kernel

theorem o1L_lt : ∀ a ∈ o1L, a < 24 := by decide +kernel

theorem o2L_lt : ∀ a ∈ o2L, a < 24 := by decide +kernel

theorem o0L_ne : ∀ a ∈ o0L.tail, a ≠ o0L.headD 0 := by decide +kernel

theorem o1L_ne : ∀ a ∈ o1L.tail, a ≠ o1L.headD 0 := by decide +kernel

theorem o2L_ne : ∀ a ∈ o2L.tail, a ≠ o2L.headD 0 := by decide +kernel

theorem VA_o0 : VA o0F = maskSub 11 (vaBasis o0L) :=
  le_antisymm (VA_le_maskSub mem_o0F vaBasis_o0)
    (maskSub_le_VA mem_o0F o0L_head o0L_lt o0L_ne)

theorem VA_o1 : VA o1F = maskSub 11 (vaBasis o1L) :=
  le_antisymm (VA_le_maskSub mem_o1F vaBasis_o1)
    (maskSub_le_VA mem_o1F o1L_head o1L_lt o1L_ne)

theorem VA_o2 : VA o2F = maskSub 11 (vaBasis o2L) :=
  le_antisymm (VA_le_maskSub mem_o2F vaBasis_o2)
    (maskSub_le_VA mem_o2F o2L_head o2L_lt o2L_ne)

theorem UT_le_VA : ∀ A ∈ labTrio, ∀ x ∈ UT, x ∈ VA A := by
  intro A hA x hx
  simp only [labTrio, Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl
  · rw [VA_o0]; exact UT_le_maskSub UT_o0 hx
  · rw [VA_o1]; exact UT_le_maskSub UT_o1 hx
  · rw [VA_o2]; exact UT_le_maskSub UT_o2 hx

theorem o0F_ne_o1F : o0F ≠ o1F := by
  intro h
  have : (0 : Fin 24) ∈ o1F := h ▸ (by rw [mem_o0F]; decide)
  rw [mem_o1F] at this
  exact absurd this (by decide)

theorem inter_UT : ∀ A ∈ labTrio, ∀ A' ∈ labTrio, A ≠ A' → ∀ x : W11, x ∈ VA A → x ∈ VA A' →
    x ∈ UT := by
  intro A hA A' hA' hne x hx hx'
  simp only [labTrio, Finset.mem_insert, Finset.mem_singleton] at hA hA'
  rcases hA with rfl | rfl | rfl <;> rcases hA' with rfl | rfl | rfl
  · exact absurd rfl hne
  · rw [VA_o0] at hx; rw [VA_o1] at hx'; exact mem_UT_of_inter inter_01 hx hx'
  · rw [VA_o0] at hx; rw [VA_o2] at hx'; exact mem_UT_of_inter inter_02 hx hx'
  · rw [VA_o1] at hx; rw [VA_o0] at hx'; exact mem_UT_of_inter inter_01 hx' hx
  · exact absurd rfl hne
  · rw [VA_o1] at hx; rw [VA_o2] at hx'; exact mem_UT_of_inter inter_12 hx hx'
  · rw [VA_o2] at hx; rw [VA_o0] at hx'; exact mem_UT_of_inter inter_02 hx' hx
  · rw [VA_o2] at hx; rw [VA_o1] at hx'; exact mem_UT_of_inter inter_12 hx' hx
  · exact absurd rfl hne

theorem rho_UT_le {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) (h : σ • labTrio = labTrio) :
    ∀ u ∈ UT, rhoM24 ⟨σ, hσ⟩ u ∈ UT := by
  intro u hu
  have hmem : ∀ A ∈ labTrio, σ • A ∈ labTrio := fun A hA => by
    rw [← h]
    exact Finset.mem_smul_finset.2 ⟨A, hA, rfl⟩
  have h0 : o0F ∈ labTrio := by simp [labTrio]
  have h1 : o1F ∈ labTrio := by simp [labTrio]
  refine inter_UT (σ • o0F) (hmem _ h0) (σ • o1F) (hmem _ h1)
    (fun e => o0F_ne_o1F (MulAction.injective σ e)) _ ?_ ?_
  · exact rho_mem_VA ⟨σ, hσ⟩ (UT_le_VA o0F h0 u hu)
  · exact rho_mem_VA ⟨σ, hσ⟩ (UT_le_VA o1F h1 u hu)

theorem stab_labTrio_le {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) (h : σ • labTrio = labTrio) :
    σ ∈ stabUTP := by
  refine mem_stabUTP hσ (mem_stabSub_UT (rho_UT_le hσ h) ?_)
  have hσ' : σ⁻¹ ∈ AutPerm := AutPerm.inv_mem hσ
  have h' : σ⁻¹ • labTrio = labTrio := by
    rw [inv_smul_eq_iff]
    exact h.symm
  intro u hu
  have := rho_UT_le hσ' h' u hu
  have e : (rhoM24 ⟨σ, hσ⟩)⁻¹ = rhoM24 ⟨σ⁻¹, hσ'⟩ := by
    rw [← map_inv]
    rfl
  rw [e]
  exact this

theorem stabUTP_eq :
    stabUTP = AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) labTrio := by
  obtain ⟨-, hSP, -⟩ := CFSG.Quasithin.H158U.stab_facts
  refine le_antisymm ?_ ?_
  · intro σ hσ
    exact ⟨stabUTP_le_autPerm hσ, MulAction.mem_stabilizer_iff.2 (smul_labTrio (hSP hσ))⟩
  · intro σ hσ
    exact stab_labTrio_le hσ.1 (MulAction.mem_stabilizer_iff.1 hσ.2)

end CFSG.Quasithin.H156
