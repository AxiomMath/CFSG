module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eFacts
public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs2
public import CFSG.Milestones.ASVolI.F48.Rest.Perm
public import Certificates.Certificate7774
public import Certificates.Certificate7775
public import Certificates.Certificate7776
public import Certificates.Certificate7778

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.CosetTable CFSG.Quasithin

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr burnsideF48t_u52eF

@[expose] def burnsideF48t_u52eK' (j : ℕ) : Subgroup (Equiv.Perm (Fin 462)) :=
  arrGen 462 (burnsideF48t_u52eKG j ())

@[expose] noncomputable def burnsideF48t_u52eκ (j m : ℕ) : Equiv.Perm (Fin 462) :=
  burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) ((burnsideF48t_u52eKhW.getD j []).getD m [])

@[expose] def burnsideF48t_u52eKGen (s : ℕ) : ℕ := [1, 3, 9].getD s 0

section Classes

theorem burnsideF48t_u52e_kh {j : ℕ} (hj : j < 4) :
    (burnsideF48t_u52eKL j ()).length = 18 ∧
      burnsideF48t_closedL 462 (burnsideF48t_u52eKG j ()) (burnsideF48t_u52eKL j ()) = true := by
  have h := burnsideF48t_u52e_cert.2.2.2.1
  simp only [burnsideF48t_u52eKhOK, Bool.and_eq_true, beq_iff_eq] at h
  have h' := allBelowN_spec h.2 hj
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  exact ⟨h'.1.1.1.1, h'.1.1.1.2⟩

theorem burnsideF48t_u52e_klok {j : ℕ} (hj : j < 4) :
    (∀ k ∈ burnsideF48t_u52KL (),
      peq 462 k ((burnsideF48t_u52eKL j ()).getD 9 (pid 462)) = false) ∧
    ∀ m < 9, peq 462 ((burnsideF48t_u52eKL j ()).getD m (pid 462))
        ((burnsideF48t_u52KL ()).getD m (pid 462)) = true ∧
      peq 462 ((burnsideF48t_u52eKL j ()).getD (m + 9) (pid 462))
        (pcomp 462 ((burnsideF48t_u52eKL j ()).getD 9 (pid 462))
          ((burnsideF48t_u52KL ()).getD m (pid 462))) = true := by
  have h := allBelowN_spec Certificates.certificate7778 hj
  simp only [Bool.and_eq_true] at h
  refine ⟨fun k hk => ?_, fun m hm => ?_⟩
  · have := List.all_eq_true.1 h.1 k hk
    simpa using this
  · have := allBelowN_spec h.2 hm
    simp only [Bool.and_eq_true] at this
    exact this

theorem burnsideF48t_u52e_KhW_length {j : ℕ} (hj : j < 4) :
    (burnsideF48t_u52eKhW.getD j []).length = 18 := by
  have := (burnsideF48t_u52e_kh hj).1
  simpa [burnsideF48t_u52eKL] using this

theorem burnsideF48t_u52e_prep_κ {j m : ℕ} (hj : j < 4) (hm : m < 18) :
    PRep 462 ((burnsideF48t_u52eKL j ()).getD m (pid 462)) (burnsideF48t_u52eκ j m) := by
  have hm' : m < (burnsideF48t_u52eKhW.getD j []).length := by
    rw [burnsideF48t_u52e_KhW_length hj]
    exact hm
  have := burnsideF48t_prep_evA burnsideF48t_u52e_recL ((burnsideF48t_u52eKhW.getD j []).getD m [])
  simp only [burnsideF48t_u52eKL]
  rw [List.getD_eq_getElem _ _ (by simpa using hm'), List.getElem_map]
  unfold burnsideF48t_u52eκ
  rw [List.getD_eq_getElem _ _ hm'] at this ⊢
  exact this

theorem burnsideF48t_u52e_KG_size (j : ℕ) : (burnsideF48t_u52eKG j ()).size = 3 := by
  unfold burnsideF48t_u52eKG
  simp

theorem burnsideF48t_u52e_KRep {j : ℕ} (hj : j < 4) : ∀ s < (burnsideF48t_u52eKG j ()).size,
    PRep 462 (burnsideF48t_u52eKG j ())[s]! (burnsideF48t_u52eκ j (burnsideF48t_u52eKGen s)) := by
  intro s hs
  rw [burnsideF48t_u52e_KG_size] at hs
  have e : (burnsideF48t_u52eKG j ())[s]! =
      (burnsideF48t_u52eKL j ()).getD (burnsideF48t_u52eKGen s) (pid 462) := by
    interval_cases s <;> rfl
  rw [e]
  exact burnsideF48t_u52e_prep_κ hj (by interval_cases s <;> decide)

theorem burnsideF48t_u52e_K'_eq {j : ℕ} (hj : j < 4) : burnsideF48t_u52eK' j =
    Subgroup.closure (Set.range fun s : Fin (burnsideF48t_u52eKG j ()).size =>
      burnsideF48t_u52eκ j (burnsideF48t_u52eKGen s)) :=
  arrGen_eq (σ := fun s => burnsideF48t_u52eκ j (burnsideF48t_u52eKGen s)) (burnsideF48t_u52e_KRep hj)

theorem burnsideF48t_u52e_gen_mem {j : ℕ} (hj : j < 4) {s : ℕ} (hs : s < 3) :
    burnsideF48t_u52eκ j (burnsideF48t_u52eKGen s) ∈ burnsideF48t_u52eK' j := by
  rw [burnsideF48t_u52e_K'_eq hj]
  exact Subgroup.subset_closure ⟨⟨s, by rw [burnsideF48t_u52e_KG_size]; exact hs⟩, rfl⟩

theorem burnsideF48t_u52e_KL_of_mem {j : ℕ} (hj : j < 4) {c : Equiv.Perm (Fin 462)}
    (hc : c ∈ burnsideF48t_u52eK' j) : burnsideF48t_arr c ∈ burnsideF48t_u52eKL j () := by
  rw [burnsideF48t_u52e_K'_eq hj] at hc
  exact burnsideF48t_mem_of_closedL (burnsideF48t_u52e_KRep hj) (burnsideF48t_u52e_kh hj).2 c hc

theorem burnsideF48t_u52e_KL_cases {j : ℕ} (hj : j < 4) {c : Equiv.Perm (Fin 462)}
    (hc : burnsideF48t_arr c ∈ burnsideF48t_u52eKL j ()) : ∃ m < 18, c = burnsideF48t_u52eκ j m := by
  obtain ⟨m, hm, he⟩ := List.mem_iff_getElem.1 hc
  have hm18 : m < 18 := by rw [(burnsideF48t_u52e_kh hj).1] at hm; exact hm
  refine ⟨m, hm18, ?_⟩
  have hp := burnsideF48t_u52e_prep_κ hj hm18
  rw [List.getD_eq_getElem _ _ hm, he] at hp
  exact (burnsideF48t_prep_arr c).unique hp

theorem burnsideF48t_u52e_κ_eq {j m : ℕ} (hj : j < 4) (hm : m < 9) :
    burnsideF48t_u52eκ j m = burnsideF48t_u52κ m :=
  eq_of_peq (burnsideF48t_u52e_prep_κ hj (by omega)) (burnsideF48t_u52_prep_κ hm)
    ((burnsideF48t_u52e_klok hj).2 m hm).1

theorem burnsideF48t_u52e_κ_eq' {j m : ℕ} (hj : j < 4) (hm : m < 9) :
    burnsideF48t_u52eκ j (m + 9) = burnsideF48t_u52eκ j 9 * burnsideF48t_u52κ m :=
  eq_of_peq (burnsideF48t_u52e_prep_κ hj (by omega))
    (prep_pcomp (burnsideF48t_u52e_prep_κ hj (by norm_num)) (burnsideF48t_u52_prep_κ hm))
    ((burnsideF48t_u52e_klok hj).2 m hm).2

theorem burnsideF48t_u52e_K'_le {j : ℕ} (hj : j < 4) : burnsideF48t_u52K' ≤ burnsideF48t_u52eK' j := by
  rw [burnsideF48t_u52_K'_eq, Subgroup.closure_le]
  rintro _ ⟨⟨s, hs⟩, rfl⟩
  have hs2 : s < 2 := burnsideF48t_u52_KArr_size ▸ hs
  interval_cases s
  · have := burnsideF48t_u52e_gen_mem hj (s := 0) (by norm_num)
    rw [show burnsideF48t_u52eKGen 0 = 1 from rfl, burnsideF48t_u52e_κ_eq hj (by norm_num)] at this
    exact this
  · have := burnsideF48t_u52e_gen_mem hj (s := 1) (by norm_num)
    rw [show burnsideF48t_u52eKGen 1 = 3 from rfl, burnsideF48t_u52e_κ_eq hj (by norm_num)] at this
    exact this

theorem burnsideF48t_u52e_t_mem {j : ℕ} (hj : j < 4) : burnsideF48t_u52eκ j 9 ∈ burnsideF48t_u52eK' j :=
  burnsideF48t_u52e_gen_mem hj (s := 2) (by norm_num)

theorem burnsideF48t_u52e_t_not_mem {j : ℕ} (hj : j < 4) : burnsideF48t_u52eκ j 9 ∉ burnsideF48t_u52K' := by
  intro h
  obtain ⟨m, hm, he⟩ := burnsideF48t_u52_K'_cases h
  have hk : (burnsideF48t_u52KL ()).getD m (pid 462) ∈ burnsideF48t_u52KL () := by
    rw [List.getD_eq_getElem _ _ (by simpa [burnsideF48t_u52KL, burnsideF48t_u52_KW_length] using hm)]
    exact List.getElem_mem _
  have h1 := (burnsideF48t_u52e_klok hj).1 _ hk
  have h2 : peq 462 ((burnsideF48t_u52KL ()).getD m (pid 462))
      ((burnsideF48t_u52eKL j ()).getD 9 (pid 462)) = true :=
    (peq_iff (burnsideF48t_u52_prep_κ hm) (burnsideF48t_u52e_prep_κ hj (by norm_num))).2 he.symm
  rw [h1] at h2
  exact absurd h2 (by decide)

theorem burnsideF48t_u52e_κ_mem {j m : ℕ} (hj : j < 4) (hm : m < 18) :
    burnsideF48t_u52eκ j m ∈ burnsideF48t_u52eK' j := by
  by_cases h9 : m < 9
  · rw [burnsideF48t_u52e_κ_eq hj h9]
    exact burnsideF48t_u52e_K'_le hj (burnsideF48t_u52_κ_mem h9)
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 9 := ⟨m - 9, by omega⟩
    rw [burnsideF48t_u52e_κ_eq' hj (by omega)]
    exact (burnsideF48t_u52eK' j).mul_mem (burnsideF48t_u52e_t_mem hj)
      (burnsideF48t_u52e_K'_le hj (burnsideF48t_u52_κ_mem (by omega)))

theorem burnsideF48t_u52e_card_K' {j : ℕ} (hj : j < 4) : Nat.card ↥(burnsideF48t_u52eK' j) = 18 := by
  have hle : Nat.card ↥(burnsideF48t_u52eK' j) ≤ 18 := by
    let G : Fin 18 → ↥(burnsideF48t_u52eK' j) := fun m =>
      ⟨burnsideF48t_u52eκ j m, burnsideF48t_u52e_κ_mem hj m.2⟩
    have hG : Function.Surjective G := by
      rintro ⟨c, hc⟩
      obtain ⟨m, hm, rfl⟩ := burnsideF48t_u52e_KL_cases hj (burnsideF48t_u52e_KL_of_mem hj hc)
      exact ⟨⟨m, hm⟩, rfl⟩
    have h1 := Nat.card_le_card_of_surjective G hG
    rwa [Nat.card_eq_fintype_card (α := Fin 18), Fintype.card_fin] at h1
  have hK := burnsideF48t_u52e_K'_le hj
  have hdvd := Subgroup.card_dvd_of_le hK
  rw [burnsideF48t_u52_card_K'] at hdvd
  have hne : Nat.card ↥(burnsideF48t_u52eK' j) ≠ 9 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hK (by rw [h, burnsideF48t_u52_card_K'])
    exact burnsideF48t_u52e_t_not_mem hj (this ▸ burnsideF48t_u52e_t_mem hj)
  have hpos : 0 < Nat.card ↥(burnsideF48t_u52eK' j) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hle hne hpos ⊢
  have hk2 : k ≤ 2 := by omega
  interval_cases k <;> omega

end Classes

section Enum

theorem burnsideF48t_u52e_cases_P1 {x : Equiv.Perm (Fin 462)} (hx : x ∈ burnsideF48t_u52Xh)
    (h0 : x burnsideF48t_u52pA = burnsideF48t_u52pA) :
    x ∈ burnsideF48t_u52P1' ∨ burnsideF48t_u52f * x ∈ burnsideF48t_u52P1' := by
  rw [burnsideF48t_u52_P1'_eq]
  rcases (burnsideF48t_u52e_mem_Xh x).1 hx with h | h
  · exact Or.inl ⟨h, MulAction.mem_stabilizer_iff.2 h0⟩
  · refine Or.inr ⟨h, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, h0, burnsideF48t_u52e_f_pA]

theorem burnsideF48t_u52e_cases_P2 {x : Equiv.Perm (Fin 462)} (hx : x ∈ burnsideF48t_u52Xh)
    (h0 : x burnsideF48t_u52pB = burnsideF48t_u52pB) :
    x ∈ burnsideF48t_u52P2' ∨ burnsideF48t_u52f * x ∈ burnsideF48t_u52P2' := by
  rw [burnsideF48t_u52_P2'_eq]
  rcases (burnsideF48t_u52e_mem_Xh x).1 hx with h | h
  · exact Or.inl ⟨h, MulAction.mem_stabilizer_iff.2 h0⟩
  · refine Or.inr ⟨h, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, h0, burnsideF48t_u52e_f_pB]

theorem burnsideF48t_u52e_ffx (x : Equiv.Perm (Fin 462)) :
    burnsideF48t_u52f * (burnsideF48t_u52f * x) = x := by
  rw [← mul_assoc, burnsideF48t_u52e_f_mul_self, one_mul]

theorem burnsideF48t_u52e_tests1 {x : Equiv.Perm (Fin 462)} (hx : x ∈ burnsideF48t_u52Xh)
    (h0 : x burnsideF48t_u52pA = burnsideF48t_u52pA) (hB : x burnsideF48t_u52pB ≠ burnsideF48t_u52pB) :
    (∀ j, (j = 0 ∨ j = 1) → (∀ k ∈ burnsideF48t_u52eK' j, x * k * x⁻¹ ∈ burnsideF48t_u52eK' j) →
      x * x ∉ burnsideF48t_u52eK' j) ∧
    ((∀ k ∈ burnsideF48t_u52eK' 2, x * k * x⁻¹ ∈ burnsideF48t_u52eK' 2) →
      x * x ∈ burnsideF48t_u52eK' 2 → ∃ w ∈ burnsideF48t_u52eXW,
        (burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) w)⁻¹ * x ∈ burnsideF48t_u52eK' 2) := by
  rcases burnsideF48t_u52e_cases_P1 hx h0 with hp | hp
  · exact Certificates.certificate7774 x hp x (Or.inl rfl) hB
  · exact Certificates.certificate7774 _ hp x (Or.inr (burnsideF48t_u52e_ffx x).symm) hB

end Enum

section Enum2

theorem burnsideF48t_u52e_tests2 {y : Equiv.Perm (Fin 462)} (hy : y ∈ burnsideF48t_u52Xh)
    (h0 : y burnsideF48t_u52pB = burnsideF48t_u52pB) (hA : y burnsideF48t_u52pA ≠ burnsideF48t_u52pA) :
    ((∀ k ∈ burnsideF48t_u52eK' 2, y * k * y⁻¹ ∈ burnsideF48t_u52eK' 2) →
      y * y ∈ burnsideF48t_u52eK' 2 → ∃ w ∈ burnsideF48t_u52eYW,
        (burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) w)⁻¹ * y ∈ burnsideF48t_u52eK' 2) ∧
    ((∀ k ∈ burnsideF48t_u52eK' 3, y * k * y⁻¹ ∈ burnsideF48t_u52eK' 3) →
      y * y ∉ burnsideF48t_u52eK' 3) := by
  rcases burnsideF48t_u52e_cases_P2 hy h0 with hp | hp
  · exact Certificates.certificate7775 y hp y (Or.inl rfl) hA
  · exact Certificates.certificate7775 _ hp y (Or.inr (burnsideF48t_u52e_ffx y).symm) hA

end Enum2

section Class

theorem burnsideF48t_u52e_testB {β : Equiv.Perm (Fin 462)} (hβ : β ∈ burnsideF48t_u52B')
    (hβK : ∀ k ∈ burnsideF48t_u52K', β * k * β⁻¹ ∈ burnsideF48t_u52K') (hββ : β * β ∈ burnsideF48t_u52K')
    (hnot : β ∉ burnsideF48t_u52K') :
    ∃ k ∈ burnsideF48t_u52K', β * k ∈ burnsideF48t_u52S0' ∧ β * k ≠ 1 :=
  Certificates.certificate7776.1 β hβ hβK hββ hnot

theorem burnsideF48t_u52e_testF {β : Equiv.Perm (Fin 462)}
    (hβ : β ∈ burnsideF48t_u52B')
    (htK : ∀ k ∈ burnsideF48t_u52K', (burnsideF48t_u52f * β) * k * (burnsideF48t_u52f * β)⁻¹ ∈
      burnsideF48t_u52K')
    (htt : (burnsideF48t_u52f * β) * (burnsideF48t_u52f * β) ∈ burnsideF48t_u52K') :
    ∃ j < 4, burnsideF48t_u52f * β ∈ burnsideF48t_u52eK' j :=
  Certificates.certificate7776.2 β hβ htK htt

end Class

end CFSG.ASVolI
