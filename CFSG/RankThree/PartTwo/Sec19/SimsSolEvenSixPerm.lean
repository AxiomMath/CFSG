module

public import CFSG.CGT.PushingUpLit.SolK.FourPerm
public import CFSG.CGT.PushingUpLit.SolK.PermCore

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Six

open CFSG.CGT.PushingUpLit.SolK CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

theorem eq_or_eq_of_notMem_of_card {J : Finset (Fin 6)} (hJ : J.card = 4) {y b x : Fin 6}
    (hyJ : y ∉ J) (hbJ : b ∉ J) (hyb : y ≠ b) (hxJ : x ∉ J) : x = y ∨ x = b := by
  by_contra hne
  rw [not_or] at hne
  have hsub : ({y, b, x} : Finset (Fin 6)) ⊆ Jᶜ := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h | h | h <;> rw [h] <;> exact Finset.mem_compl.2 ‹_›
  have h3 : ({y, b, x} : Finset (Fin 6)).card = 3 :=
    Finset.card_eq_three.2 ⟨y, b, x, hyb, Ne.symm hne.1, Ne.symm hne.2, rfl⟩
  have := Finset.card_le_card hsub
  rw [h3, Finset.card_compl, Fintype.card_fin, hJ] at this
  omega

theorem moved_outside {J : Finset (Fin 6)} (hJ : J.card = 4) {σ : Perm (Fin 6)}
    (hσ : ∀ x, σ x ∈ J ↔ x ∈ J) {y b : Fin 6} (hyJ : y ∉ J) (hσy : σ y = b) (hby : b ≠ y) :
    b ∉ J ∧ σ b = y ∧ ∀ x, x ∉ J → x = y ∨ x = b := by
  have hbJ : b ∉ J := fun h => hyJ ((hσ y).1 (hσy ▸ h))
  have hout : ∀ x, x ∉ J → x = y ∨ x = b := fun x hx =>
    eq_or_eq_of_notMem_of_card hJ hyJ hbJ (Ne.symm hby) hx
  have hσbJ : σ b ∉ J := fun h => hbJ ((hσ b).1 h)
  refine ⟨hbJ, ?_, hout⟩
  rcases hout _ hσbJ with h | h
  · exact h
  · exact absurd (σ.injective (h.trans hσy.symm)) hby

theorem fourGroup_inf_stabilizer {N : Subgroup (Perm (Fin 6))} {J : Finset (Fin 6)}
    (hN2 : IsPGroup 2 N) (hNJ : N ≤ setStab J) (hA : ∀ τ ∈ altOn J, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    {y b : Fin 6} (hyJ : y ∉ J) (hbJ : b ∉ J) (hyb : y ≠ b)
    (hout : ∀ x, x ∉ J → x = y ∨ x = b) :
    FourGroup J (N ⊓ MulAction.stabilizer (Perm (Fin 6)) y) := by
  have hmem : ∀ τ : Perm (Fin 6), τ ∈ N ⊓ MulAction.stabilizer (Perm (Fin 6)) y ↔
      τ ∈ N ∧ τ y = y := fun τ => by
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def]
  refine ⟨hN2.to_le inf_le_left, fun τ hτ => hNJ ((hmem τ).1 hτ).1, fun τ hτ x hx => ?_, ?_⟩
  · obtain ⟨hτN, hτy⟩ := (hmem τ).1 hτ
    rcases hout x hx with h | h
    · rw [h]
      exact hτy
    · rw [h]
      have hτbJ : τ b ∉ J := fun h' => hbJ ((mem_setStab.1 (hNJ hτN) b).1 h')
      rcases hout _ hτbJ with h' | h'
      · exact absurd (τ.injective (h'.trans hτy.symm)) (Ne.symm hyb)
      · exact h'
  · intro τ hτ ρ hρ
    obtain ⟨hρN, hρy⟩ := (hmem ρ).1 hρ
    refine (hmem _).2 ⟨hA τ hτ ρ hρN, ?_⟩
    have hτy : τ y = y := (mem_altOn.1 hτ).1 y hyJ
    have hτy' : τ⁻¹ y = y := by
      rw [Perm.inv_eq_iff_eq]
      exact hτy.symm
    simp [Perm.mul_apply, hτy', hρy, hτy]

theorem commutator_dichotomy {N : Subgroup (Perm (Fin 6))} {J : Finset (Fin 6)}
    (hJ : J.card = 4) (hN2 : IsPGroup 2 N) (hNJ : N ≤ setStab J)
    (hA : ∀ τ ∈ altOn J, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) {σ : Perm (Fin 6)} (hσ : σ ∈ N)
    {y b : Fin 6} (hyJ : y ∉ J) (hbJ : b ∉ J) (hyb : y ≠ b) (hσb : σ b = y)
    (hout : ∀ x, x ∉ J → x = y ∨ x = b) {c : Perm (Fin 6)} (hc : c ∈ altOn J) :
    σ * c * σ⁻¹ * c⁻¹ = 1 ∨ ∀ p ∈ J, (σ * c * σ⁻¹ * c⁻¹) p ≠ p := by
  have hF := fourGroup_inf_stabilizer hN2 hNJ hA hyJ hbJ hyb hout
  have hρN : σ * c * σ⁻¹ * c⁻¹ ∈ N := by
    have := N.mul_mem hσ (hA c hc σ⁻¹ (N.inv_mem hσ))
    simpa [mul_assoc] using this
  have hcy : c y = y := (mem_altOn.1 hc).1 y hyJ
  have hcb : c b = b := (mem_altOn.1 hc).1 b hbJ
  have hρy : (σ * c * σ⁻¹ * c⁻¹) y = y := by
    have h1 : c⁻¹ y = y := by
      rw [Perm.inv_eq_iff_eq]
      exact hcy.symm
    have h2 : σ⁻¹ y = b := by
      rw [Perm.inv_eq_iff_eq]
      exact hσb.symm
    simp [Perm.mul_apply, h1, h2, hcb, hσb]
  have hρ : σ * c * σ⁻¹ * c⁻¹ ∈ N ⊓ MulAction.stabilizer (Perm (Fin 6)) y := by
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def]
    exact ⟨hρN, hρy⟩
  by_cases h1 : σ * c * σ⁻¹ * c⁻¹ = 1
  · exact Or.inl h1
  · exact Or.inr (hF.free hJ hρ h1)

theorem fixes_of_fixed_point {J : Finset (Fin 6)} (hJ : J.card = 4) {σ : Perm (Fin 6)}
    (h2 : ∃ j : ℕ, σ ^ (2 ^ j) = 1) (hpres : ∀ x, σ x ∈ J ↔ x ∈ J) {s : Fin 6} (hs : s ∈ J)
    (hσs : σ s = s)
    (hdich : ∀ c ∈ altOn J, σ * c * σ⁻¹ * c⁻¹ = 1 ∨ ∀ p ∈ J, (σ * c * σ⁻¹ * c⁻¹) p ≠ p) :
    ∀ a ∈ J, σ a = a := by
  have hB : (J.erase s).card = 3 := by rw [Finset.card_erase_of_mem hs, hJ]
  have h1 : ∀ a, σ a = s ↔ a = s := fun a =>
    ⟨fun h => σ.injective (h.trans hσs.symm), fun h => by rw [h]; exact hσs⟩
  have hσB : ∀ a, σ a ∈ J.erase s ↔ a ∈ J.erase s := fun a => by
    rw [Finset.mem_erase, Finset.mem_erase, hpres a, ne_eq, ne_eq, h1 a]
  have hc : ∀ τ ∈ altOn (J.erase s), σ * τ = τ * σ := by
    intro τ hτ
    obtain ⟨hτ1, hτ2⟩ := mem_altOn.1 hτ
    have hτJ : τ ∈ altOn J :=
      mem_altOn.2 ⟨fun x hx => hτ1 x fun h => hx (Finset.mem_of_mem_erase h), hτ2⟩
    have hτs : τ s = s := hτ1 s (Finset.notMem_erase s J)
    have hτs' : τ⁻¹ s = s := by
      rw [Perm.inv_eq_iff_eq]
      exact hτs.symm
    have hσs' : σ⁻¹ s = s := by
      rw [Perm.inv_eq_iff_eq]
      exact hσs.symm
    have hfix : (σ * τ * σ⁻¹ * τ⁻¹) s = s := by simp [Perm.mul_apply, hτs, hτs', hσs, hσs']
    rcases hdich τ hτJ with h | h
    · exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)
    · exact absurd hfix (h s hs)
  have hfixB := fixes_of_commute (Or.inr hB) h2 hσB hc
  intro a ha
  by_cases has : a = s
  · rw [has]
    exact hσs
  · exact hfixB a (Finset.mem_erase.2 ⟨has, ha⟩)

theorem eq_swap_of_fixes {J : Finset (Fin 6)} {σ : Perm (Fin 6)} {y b : Fin 6} (hyJ : y ∉ J)
    (hbJ : b ∉ J) (hout : ∀ x, x ∉ J → x = y ∨ x = b) (hσy : σ y = b) (hσb : σ b = y)
    (hfix : ∀ a ∈ J, σ a = a) : σ = swap y b := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ J
  · rw [hfix x hx, swap_apply_of_ne_of_ne]
    · rintro rfl
      exact hyJ hx
    · rintro rfl
      exact hbJ hx
  · rcases hout x hx with h | h
    · rw [h, swap_apply_left, hσy]
    · rw [h, swap_apply_right, hσb]

theorem sign_eq_neg_one_of_fixed_point_free {σ : Perm (Fin 6)} (h2 : σ * σ = 1)
    (hfpf : ∀ x, σ x ≠ x) : Equiv.Perm.sign σ = -1 := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two]; exact h2
  have h0 : Fintype.card (Function.fixedPoints σ) = 0 :=
    Fintype.card_eq_zero_iff.2 ⟨fun ⟨x, hx⟩ => hfpf x hx⟩
  rw [sign_of_pow_two_eq_one hpow, h0, Fintype.card_fin]
  decide

theorem false_of_free_sq {J : Finset (Fin 6)} (hJ : J.card = 4) {σ : Perm (Fin 6)}
    (h2 : ∃ j : ℕ, σ ^ (2 ^ j) = 1) (hpres : ∀ x, σ x ∈ J ↔ x ∈ J)
    (hfpf : ∀ p ∈ J, σ p ≠ p) (hsq : ∀ p ∈ J, (σ * σ) p ≠ p)
    (hdich : ∀ c ∈ altOn J, σ * c * σ⁻¹ * c⁻¹ = 1 ∨ ∀ p ∈ J, (σ * c * σ⁻¹ * c⁻¹) p ≠ p) :
    False := by
  obtain ⟨p, hp⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨q, hσp⟩ : ∃ q, σ p = q := ⟨_, rfl⟩
  have hq : q ∈ J := hσp ▸ (hpres p).2 hp
  obtain ⟨r, hσq⟩ : ∃ r, σ q = r := ⟨_, rfl⟩
  have hr : r ∈ J := hσq ▸ (hpres q).2 hq
  obtain ⟨s, hσr⟩ : ∃ s, σ r = s := ⟨_, rfl⟩
  have hpq : p ≠ q := fun h => hfpf p hp (hσp.trans h.symm)
  have hqr : q ≠ r := fun h => hfpf q hq (hσq.trans h.symm)
  have hpr : p ≠ r := fun h => hsq p hp (by rw [Perm.mul_apply, hσp, hσq, h])
  have hsp : s ≠ p := by
    intro h
    have h3 : (σ ^ 3) p = p := by simp [pow_succ, Perm.mul_apply, hσp, hσq, hσr, h]
    exact hfpf p hp (apply_eq_of_pow_odd h2 (by decide) h3)
  have hc : cyc p r q ∈ altOn J := cyc_mem_altOn_of_mem hp hr hq hpr hpq (Ne.symm hqr)
  have hcp : cyc p r q p = q := cyc_apply_first hpq (Ne.symm hqr)
  have hcq : cyc p r q q = r := cyc_apply_third p r q
  have hcr : cyc p r q r = p := cyc_apply_second hpr (Ne.symm hqr)
  have hci_r : (cyc p r q)⁻¹ r = q := by
    rw [Perm.inv_eq_iff_eq]
    exact hcq.symm
  have hci_p : (cyc p r q)⁻¹ p = r := by
    rw [Perm.inv_eq_iff_eq]
    exact hcr.symm
  have hsi_q : σ⁻¹ q = p := by
    rw [Perm.inv_eq_iff_eq]
    exact hσp.symm
  have hsi_r : σ⁻¹ r = q := by
    rw [Perm.inv_eq_iff_eq]
    exact hσq.symm
  have hρr : (σ * cyc p r q * σ⁻¹ * (cyc p r q)⁻¹) r = r := by
    simp [Perm.mul_apply, hci_r, hsi_q, hcp, hσq]
  have hρp : (σ * cyc p r q * σ⁻¹ * (cyc p r q)⁻¹) p = s := by
    simp [Perm.mul_apply, hci_p, hsi_r, hcq, hσr]
  rcases hdich _ hc with h | h
  · rw [h] at hρp
    exact hsp (hρp.symm.trans rfl)
  · exact h r hr hρr

theorem fix_compl_of_even {N : Subgroup (Perm (Fin 6))} {J : Finset (Fin 6)} (hJ : J.card = 4)
    (hN2 : IsPGroup 2 N) (hNJ : N ≤ setStab J)
    (hA : ∀ τ ∈ altOn J, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (heven : ∀ σ ∈ N, Equiv.Perm.sign σ = 1) :
    ∀ σ ∈ N, ∀ y, y ∉ J → σ y = y := by
  intro σ hσ y hyJ
  by_contra hσy
  obtain ⟨b, hb⟩ : ∃ b, σ y = b := ⟨_, rfl⟩
  have hby : b ≠ y := fun h => hσy (hb.trans h)
  have hpres : ∀ x, σ x ∈ J ↔ x ∈ J := mem_setStab.1 (hNJ hσ)
  obtain ⟨hbJ, hσb, hout⟩ := moved_outside hJ hpres hyJ hb hby
  have hdich : ∀ c ∈ altOn J, σ * c * σ⁻¹ * c⁻¹ = 1 ∨ ∀ p ∈ J, (σ * c * σ⁻¹ * c⁻¹) p ≠ p :=
    fun c hc => commutator_dichotomy hJ hN2 hNJ hA hσ hyJ hbJ hby.symm hσb hout hc
  have h2 := exists_pow_two_pow_eq_one hN2 hσ
  have hodd : Equiv.Perm.sign σ = -1 → False := fun h => by
    have h1 := heven σ hσ
    rw [h] at h1
    exact absurd h1 (by decide)
  by_cases hex : ∃ s ∈ J, σ s = s
  · obtain ⟨s, hs, hσs⟩ := hex
    have hfixJ := fixes_of_fixed_point hJ h2 hpres hs hσs hdich
    have hswap := eq_swap_of_fixes hyJ hbJ hout hb hσb hfixJ
    exact hodd (by rw [hswap]; exact Equiv.Perm.sign_swap hby.symm)
  · push Not at hex
    by_cases hsq : σ * σ = 1
    · have hfpf : ∀ x, σ x ≠ x := by
        intro x
        by_cases hx : x ∈ J
        · exact hex x hx
        · rcases hout x hx with h | h
          · rw [h]
            exact hσy
          · rw [h, hσb]
            exact hby.symm
      exact hodd (sign_eq_neg_one_of_fixed_point_free hsq hfpf)
    · have hF := fourGroup_inf_stabilizer hN2 hNJ hA hyJ hbJ hby.symm hout
      have hsqmem : σ * σ ∈ N ⊓ MulAction.stabilizer (Perm (Fin 6)) y := by
        rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def]
        exact ⟨N.mul_mem hσ hσ, by rw [Perm.mul_apply, hb, hσb]⟩
      exact false_of_free_sq hJ h2 hpres hex (hF.free hJ hsqmem hsq) hdich

theorem fourGroup_of_even {N : Subgroup (Perm (Fin 6))} {J : Finset (Fin 6)} (hJ : J.card = 4)
    (hN2 : IsPGroup 2 N) (hNJ : N ≤ setStab J)
    (hA : ∀ τ ∈ altOn J, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (heven : ∀ σ ∈ N, Equiv.Perm.sign σ = 1) : FourGroup J N :=
  ⟨hN2, hNJ, fix_compl_of_even hJ hN2 hNJ hA heven, hA⟩

end CFSG.RankThree.PartTwo.Sec19.SolEven.Six
