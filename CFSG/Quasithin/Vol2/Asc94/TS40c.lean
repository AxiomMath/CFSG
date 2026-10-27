module

public import CFSG.Quasithin.Vol2.Asc94.TS40b

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame4.Γ_nonempty (F : Frame4 G z) (i : Fin 6) : (F.Γ i).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by rw [F.Γ_card i]; fin_cases i <;> simp)

theorem Frame4.dichΓ (F : Frame4 G z) (i : Fin 6) : F.Γ i ⊆ F.Gz ∨ Disjoint (F.Γ i) F.Gz := by
  by_cases h : ∃ a, a ∈ F.Γ i ∧ a ∈ F.Gz
  · left
    obtain ⟨a, haΓ, haS⟩ := h
    intro b hb
    obtain ⟨x, hx, rfl⟩ := F.Γ_trans i a haΓ b hb
    exact F.conj_mem_Gz_T haS hx
  · right
    rw [Set.disjoint_left]
    intro a ha haS
    exact h ⟨a, ha, haS⟩

theorem Frame4.Γ0_sub (F : Frame4 G z) : F.Γ 0 ⊆ F.Gz := by
  intro s hs
  rw [F.Γ0] at hs
  rw [Set.mem_singleton_iff.1 hs]
  exact ⟨F.z_mem_B, F.z_ne_one, 1, by simp⟩

theorem Frame4.Γ1_sub (F : Frame4 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u) : F.Γ 1 ⊆ F.Gz := by
  intro s hs
  rw [F.Γ1] at hs
  obtain ⟨h1, h2⟩ := hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h2
  exact ⟨(Subgroup.mem_inf.1 h1).1, h2.1, hU1 _ (Subgroup.mem_inf.1 h1).2 h2.1⟩

theorem Frame4.Γ2_sub (F : Frame4 G z) (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) : F.Γ 2 ⊆ F.Gz := by
  intro s hs
  rw [F.Γ2] at hs
  obtain ⟨h1, h2⟩ := hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h2
  exact ⟨(Subgroup.mem_inf.1 h1).1, h2.1, hU2 _ (Subgroup.mem_inf.1 h1).2 h2.1⟩

theorem Frame4.not_Γ3_sub (F : Frame4 G z) : ¬ F.Γ 3 ⊆ F.Gz := by
  intro hsub
  obtain ⟨a, ha⟩ := F.Γ_nonempty 3
  have ha' := ha
  rw [F.Γ3] at ha'
  obtain ⟨haA, haA', haQ, ha1, haU, haU2⟩ := ha'
  have hsq : a * a = 1 := by
    rw [← sq]
    exact F.A_elem.2 a haA
  obtain ⟨-, -, g, hg⟩ := hsub ha
  rcases F.Q_inv a haQ hsq ha1 with h | ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact haU (h ▸ F.toFrame1.toFrame0.z_mem_U)
  · exact haU h
  · exact haU2 h
  · exact s39_4 F.toFrame1 a h g hg.symm

theorem Frame4.sum_Gz (F : Frame4 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) :
    F.Gz.ncard = 5 + (open Classical in if F.Γ 4 ⊆ F.Gz then 4 else 0) +
      (open Classical in if F.Γ 5 ⊆ F.Gz then 4 else 0) := by
  classical
  have hS : F.Gz ⊆ ⋃ i, F.Γ i := by
    intro a ha
    rw [F.Γ_union]
    exact ⟨ha.1, ha.2.1⟩
  have hsum := ncard_eq_sum_of_dich F.Γ F.Γ_disj F.Gz hS F.dichΓ F.Γ_nonempty
  rw [Fin.sum_univ_six, if_pos F.Γ0_sub, if_pos (F.Γ1_sub hU1), if_pos (F.Γ2_sub hU2),
    if_neg F.not_Γ3_sub] at hsum
  have c0 : (F.Γ 0).ncard = 1 := by simpa using F.Γ_card 0
  have c1 : (F.Γ 1).ncard = 2 := by simpa using F.Γ_card 1
  have c2 : (F.Γ 2).ncard = 2 := by simpa using F.Γ_card 2
  have c4 : (F.Γ 4).ncard = 4 := by simpa using F.Γ_card 4
  have c5 : (F.Γ 5).ncard = 4 := by simpa using F.Γ_card 5
  rw [c0, c1, c2, c4, c5] at hsum
  rw [hsum]

theorem hcong16_13 : ∀ c : ℕ, c ∣ 16 → Nat.ModEq 13 16 c → c = 16 := by
  intro c hc hmod
  have key : ∀ c ∈ Nat.divisors 16, c % 13 = 16 % 13 → c = 16 := by decide
  exact key c (Nat.mem_divisors.2 ⟨hc, by norm_num⟩) hmod.symm

theorem Frame4.false_of_card_Gz_5 (F : Frame4 G z) (h5 : F.Gz.ncard = 5)
    (h4 : ¬ F.Γ 4 ⊆ F.Gz) (h5' : ¬ F.Γ 5 ⊆ F.Gz) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard := F.card_normalizer_J
  rw [h5] at hcard
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer (F.J : Set G))) 5 (by rw [hcard]; exact dvd_mul_right 5 1024)
  set y : G := (x : G) with hy
  have hyo : orderOf y = 5 := by rw [hy, Subgroup.orderOf_coe]; exact hx
  have hyN : y ∈ Subgroup.normalizer (F.J : Set G) := x.2
  have hyiN : y⁻¹ ∈ Subgroup.normalizer (F.J : Set G) := Subgroup.inv_mem _ hyN
  have hdisj : ∀ i : Fin 6, ¬ F.Γ i ⊆ F.Gz → Disjoint (F.Γ i) F.Gz := fun i hi =>
    (F.dichΓ i).resolve_left hi
  have hGzB : ∀ a ∈ F.Gz, a ∈ F.Bsub := by
    intro a ha
    have haU : a ∈ ⋃ i, F.Γ i := by
      rw [F.Γ_union]
      exact ⟨ha.1, ha.2.1⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 haU
    have hfin6 : ∀ i : Fin 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
    rcases hfin6 i with rfl | rfl | rfl | rfl | rfl | rfl
    · exact F.Γ012_le_Bsub 0 (by decide) a hi
    · exact F.Γ012_le_Bsub 1 (by decide) a hi
    · exact F.Γ012_le_Bsub 2 (by decide) a hi
    · exact absurd ha (Set.disjoint_left.1 (hdisj 3 F.not_Γ3_sub) hi)
    · exact absurd ha (Set.disjoint_left.1 (hdisj 4 h4) hi)
    · exact absurd ha (Set.disjoint_left.1 (hdisj 5 h5') hi)
  set C : Subgroup G := Subgroup.closure F.Gz with hC
  have hCB : C ≤ F.Bsub := (Subgroup.closure_le F.Bsub).2 hGzB
  have hCdvd : Nat.card C ∣ 8 := by
    rw [← F.card_Bsub]
    exact Subgroup.card_dvd_of_le hCB
  have hC6 : 6 ≤ Nat.card C := by
    have hsub : insert (1 : G) F.Gz ⊆ (C : Set G) := by
      intro a ha
      rcases ha with rfl | ha
      · exact C.one_mem
      · exact Subgroup.subset_closure ha
    have h1 : (insert (1 : G) F.Gz).ncard = 6 := by
      rw [Set.ncard_insert_of_notMem (fun h => h.2.1 rfl), h5]
    have := Set.ncard_le_ncard hsub
    rw [h1, ← Nat.card_coe_set_eq] at this
    exact this
  have hC8 : Nat.card C = 8 := by
    have hmem : Nat.card C ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hCdvd, by norm_num⟩
    have hdiv8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv8] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hconj : ∀ g ∈ F.Gz, y * g * y⁻¹ ∈ F.Gz := by
    intro g hg
    have := F.conj_mem_Gz_J hg hyiN
    simpa using this
  have hconj' : ∀ g ∈ F.Gz, y⁻¹ * g * y ∈ F.Gz := fun g hg => F.conj_mem_Gz_J hg hyN
  have hyC : y ∈ Subgroup.normalizer (C : Set G) := by
    rw [Gen.mem_normalizer_iff_cj]
    show C.map (MulAut.conj y).toMonoidHom = C
    rw [hC, MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hconj g' hg'
    · intro hg
      exact ⟨y⁻¹ * g * y, hconj' g hg, by simp [MulAut.conj_apply]; group⟩
  have hmod := Gen.card_modEq_card_centralizer_inf hyo hyC
  have hdvdc : Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 8 := by
    rw [← hC8]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [hC8] at hmod
  have hc : Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set G)) = 8 := by
    have hmem : Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set G)) ∈ Nat.divisors 8 :=
      Nat.mem_divisors.2 ⟨hdvdc, by norm_num⟩
    have hdiv8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv8] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hm : 8 % 5 = Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set G)) % 5 := hmod
    omega
  have hle : C ≤ Subgroup.centralizer ({y} : Set G) := by
    have heq : C ⊓ Subgroup.centralizer ({y} : Set G) = C :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hC8])
    exact inf_eq_left.1 heq
  have hzC : z ∈ C := Subgroup.subset_closure (⟨F.z_mem_B, F.z_ne_one, 1, by simp⟩ : z ∈ F.Gz)
  have hyH : y ∈ Cz z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hzC)
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  exact F.toFrame2.not_mem_H_of_order 5 (by norm_num) hyo hyH

end CFSG.Quasithin.A94
