module

public import CFSG.RankThree.PartTwo.Sec15.F153A10KWit
public import CFSG.RankThree.PartTwo.Sec15.F153A10KInv
public import CFSG.RankThree.PartTwo.Sec15.F153A10KClass

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

open Equiv

private theorem a10kp_conj_comp (σ g : Perm (Fin 10)) :
    ((MulAut.conj σ⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom).comp
        (MulAut.conj σ).toMonoidHom =
      (MulAut.conj (σ⁻¹ * g * σ)).toMonoidHom := by
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
  group

private theorem a10kp_map_conj_inv (K : Subgroup (Perm (Fin 10))) (σ : Perm (Fin 10)) :
    (K.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj σ⁻¹).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj σ⁻¹).toMonoidHom.comp (MulAut.conj σ).toMonoidHom = MonoidHom.id _ := by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply, mul_inv_rev, inv_inv]
    group
  rw [h, Subgroup.map_id]

private theorem a10kp_map_conj_map (E : Subgroup (Perm (Fin 10))) (σ g : Perm (Fin 10)) :
    ((E.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj σ⁻¹).toMonoidHom =
      E.map (MulAut.conj (σ⁻¹ * g * σ)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, a10kp_conj_comp]

theorem sup_conj_eq_map {E : Subgroup (Perm (Fin 10))} (σ g : Perm (Fin 10)) :
    E ⊔ E.map (MulAut.conj (σ⁻¹ * g * σ)).toMonoidHom =
      ((E.map (MulAut.conj σ).toMonoidHom) ⊔
        (E.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj σ⁻¹).toMonoidHom := by
  rw [Subgroup.map_sup, a10kp_map_conj_inv E σ, a10kp_map_conj_map E σ g]

theorem sup_conj_eq_map₂ {E : Subgroup (Perm (Fin 10))} (σ g h : Perm (Fin 10)) :
    E ⊔ E.map (MulAut.conj (σ⁻¹ * g * σ)).toMonoidHom ⊔ E.map (MulAut.conj (σ⁻¹ * h * σ)).toMonoidHom =
      ((E.map (MulAut.conj σ).toMonoidHom) ⊔
        (E.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj g).toMonoidHom ⊔
        (E.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj h).toMonoidHom).map
        (MulAut.conj σ⁻¹).toMonoidHom := by
  rw [Subgroup.map_sup, Subgroup.map_sup, a10kp_map_conj_inv E σ, a10kp_map_conj_map E σ g,
    a10kp_map_conj_map E σ h]

private theorem a10kp_swap_conj_all : ∀ x y : Fin 10, 4 ≤ x.val → 4 ≤ y.val → x ≠ y →
    (swap 5 (swap 4 x y) * swap 4 x) * tZero * (swap 5 (swap 4 x y) * swap 4 x)⁻¹ = tZero ∧
      (swap 5 (swap 4 x y) * swap 4 x) * (swap 0 1 * swap x y) *
        (swap 5 (swap 4 x y) * swap 4 x)⁻¹ = tbB := by
  unfold tZero tbB
  decide +kernel

theorem exists_swap_conj (x y : Fin 10) (hx : 4 ≤ x.val) (hy : 4 ≤ y.val) (hxy : x ≠ y) :
    ∃ τ : Perm (Fin 10), τ * tZero * τ⁻¹ = tZero ∧ τ * (swap 0 1 * swap x y) * τ⁻¹ = tbB :=
  ⟨_, a10kp_swap_conj_all x y hx hy hxy⟩

private theorem a10kp_card_map (K : Subgroup (Perm (Fin 10))) (σ : Perm (Fin 10)) :
    Nat.card ↥(K.map (MulAut.conj σ).toMonoidHom) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj σ).injective

private theorem a10kp_conj_mem_alt {a σ : Perm (Fin 10)} (ha : a ∈ alternatingGroup (Fin 10)) :
    σ⁻¹ * a * σ ∈ alternatingGroup (Fin 10) := by
  have h := (inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem a ha σ⁻¹
  simpa using h

private theorem a10kp_mem_map_conj {E : Subgroup (Perm (Fin 10))} {x σ : Perm (Fin 10)}
    (hx : x ∈ E) : σ * x * σ⁻¹ ∈ E.map (MulAut.conj σ).toMonoidHom :=
  Subgroup.mem_map_of_mem _ hx

private theorem a10kp_exists_ne_one {E : Subgroup (Perm (Fin 10))} (h : Nat.card E = 2) :
    ∃ t ∈ E, t ≠ 1 := by
  by_contra hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 fun t ht => by
    by_contra ht1
    exact hcon ⟨t, ht, ht1⟩
  rw [hbot, Subgroup.card_bot] at h
  norm_num at h

private theorem a10kp_sq_eq_one {E : Subgroup (Perm (Fin 10))} (h : Nat.card E = 2)
    {a : Perm (Fin 10)} (ha : a ∈ E) : a ^ 2 = 1 := by
  have h1 : (⟨a, ha⟩ : E) ^ Nat.card E = 1 := pow_card_eq_one'
  rw [h] at h1
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem p2Stmt_holds : P2Stmt := by
  intro E hEA hcard
  obtain ⟨t, htE, ht1⟩ := a10kp_exists_ne_one hcard
  have ht2 : t ^ 2 = 1 := a10kp_sq_eq_one hcard htE
  have htA : t ∈ alternatingGroup (Fin 10) := hEA htE
  rcases card_support_of_involution htA ht2 ht1 with h4 | h8
  · obtain ⟨σ, hσ⟩ := exists_conj_eq_tZero ht2 h4
    have hmem : tZero ∈ E.map (MulAut.conj σ).toMonoidHom := by
      rw [← hσ]
      exact a10kp_mem_map_conj htE
    refine ⟨σ⁻¹ * gZero * σ, a10kp_conj_mem_alt gZero_mem, ?_⟩
    rw [sup_conj_eq_map σ gZero, a10kp_card_map]
    exact five_dvd_of_tZero_mem hmem
  · obtain ⟨σ, hσ⟩ := exists_conj_eq_tOne ht2 h8
    have hmem : tOne ∈ E.map (MulAut.conj σ).toMonoidHom := by
      rw [← hσ]
      exact a10kp_mem_map_conj htE
    refine ⟨σ⁻¹ * gOne * σ, a10kp_conj_mem_alt gOne_mem, ?_⟩
    rw [sup_conj_eq_map σ gOne, a10kp_card_map]
    exact five_dvd_of_tOne_mem hmem

private theorem a10kp_inv_of_sq {x : Perm (Fin 10)} (hx : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)

private theorem a10kp_comm_of_sq {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hy)
  have hxy' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hxy)
  rw [mul_inv_rev, hx', hy'] at hxy'
  exact hxy'.symm

private theorem a10kp_transport {a c σ : Perm (Fin 10)} {x y : Fin 10} (hx : 4 ≤ x.val)
    (hy : 4 ≤ y.val) (hxy : x ≠ y) (ha : σ * a * σ⁻¹ = tZero)
    (hc : σ * c * σ⁻¹ = swap 0 1 * swap x y) :
    ∃ σ' : Perm (Fin 10), σ' * a * σ'⁻¹ = tZero ∧ σ' * c * σ'⁻¹ = tbB := by
  obtain ⟨τ, hτ1, hτ2⟩ := exists_swap_conj x y hx hy hxy
  refine ⟨τ * σ, ?_, ?_⟩
  · rw [show τ * σ * a * (τ * σ)⁻¹ = τ * (σ * a * σ⁻¹) * τ⁻¹ by group, ha, hτ1]
  · rw [show τ * σ * c * (τ * σ)⁻¹ = τ * (σ * c * σ⁻¹) * τ⁻¹ by group, hc, hτ2]

theorem klein_normal_form {E : Subgroup (Perm (Fin 10))} (hEA : E ≤ alternatingGroup (Fin 10))
    (hE2 : ∀ a ∈ E, a ^ 2 = 1) (h4 : Nat.card E = 4) :
    (∃ x ∈ E, x.support.card = 8) ∨
      ∃ σ : Perm (Fin 10), ∃ a ∈ E, ∃ b ∈ E,
        (σ * a * σ⁻¹ = tZero ∧ σ * b * σ⁻¹ = taA) ∨ (σ * a * σ⁻¹ = tZero ∧ σ * b * σ⁻¹ = tbB) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    a10kp_comm_of_sq (hE2 x hx) (hE2 y hy) (hE2 _ (mul_mem hx hy))
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 fun t ht => by
      by_contra ht1
      exact hcon ⟨t, ht, ht1⟩
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  have ha2 : a ^ 2 = 1 := hE2 a ha
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  obtain ⟨b, hb, hbz⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    have hle : E ≤ Subgroup.zpowers a := by
      intro b hb
      by_contra hbz
      exact hcon ⟨b, hb, hbz⟩
    have hc := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord, h4] at hc
    norm_num at hc
  have hb1 : b ≠ 1 := fun h => hbz (by rw [h]; simp)
  have hba : b ≠ a := fun h => hbz (by rw [h]; exact Subgroup.mem_zpowers a)
  have hab : a * b ∈ E := mul_mem ha hb
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    rw [eq_inv_of_mul_eq_one_right h, a10kp_inv_of_sq ha2]
  have hAs := card_support_of_involution (hEA ha) ha2 ha1
  have hBs := card_support_of_involution (hEA hb) (hE2 b hb) hb1
  have hABs := card_support_of_involution (hEA hab) (hE2 _ hab) hab1
  by_cases hA8 : a.support.card = 8
  · exact Or.inl ⟨a, ha, hA8⟩
  by_cases hB8 : b.support.card = 8
  · exact Or.inl ⟨b, hb, hB8⟩
  by_cases hAB8 : (a * b).support.card = 8
  · exact Or.inl ⟨a * b, hab, hAB8⟩
  have hB4 : b.support.card = 4 := hBs.resolve_right hB8
  have hAB4 : (a * b).support.card = 4 := hABs.resolve_right hAB8
  obtain ⟨σ, hσa⟩ := exists_conj_eq_tZero ha2 (hAs.resolve_right hA8)
  have hb'2 : (σ * b * σ⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hE2 b hb]
    simp
  have hbc : σ * b * σ⁻¹ * tZero = tZero * (σ * b * σ⁻¹) := by
    rw [← hσa, show σ * b * σ⁻¹ * (σ * a * σ⁻¹) = σ * (b * a) * σ⁻¹ by group,
      show σ * a * σ⁻¹ * (σ * b * σ⁻¹) = σ * (a * b) * σ⁻¹ by group, hcomm b hb a ha]
  have hb'4 : (σ * b * σ⁻¹).support.card = 4 := by
    rw [Equiv.Perm.card_support_conj, hB4]
  have htb'4 : (tZero * (σ * b * σ⁻¹)).support.card = 4 := by
    rw [← hσa, show σ * a * σ⁻¹ * (σ * b * σ⁻¹) = σ * (a * b) * σ⁻¹ by group,
      Equiv.Perm.card_support_conj, hAB4]
  have hb'ne : σ * b * σ⁻¹ ≠ tZero := by
    intro h
    apply hba
    have h' : σ * b * σ⁻¹ = σ * a * σ⁻¹ := h.trans hσa.symm
    exact mul_left_cancel (mul_right_cancel h')
  rcases classify_comm_tZero hb'2 hbc hb'4 htb'4 hb'ne with hc | hc |
    ⟨x, y, hx, hy, hxy, hc | hc⟩
  · exact Or.inr ⟨σ, a, ha, b, hb, Or.inl ⟨hσa, hc⟩⟩
  · have hab' : σ * (a * b) * σ⁻¹ = taA := by
      rw [show σ * (a * b) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * b * σ⁻¹) by group, hσa, hc]
      unfold tZero taA
      decide +kernel
    exact Or.inr ⟨σ, a, ha, a * b, hab, Or.inl ⟨hσa, hab'⟩⟩
  · obtain ⟨σ', h1, h2⟩ := a10kp_transport hx hy hxy hσa hc
    exact Or.inr ⟨σ', a, ha, b, hb, Or.inr ⟨h1, h2⟩⟩
  · have hab' : σ * (a * b) * σ⁻¹ = swap 0 1 * swap x y := by
      rw [show σ * (a * b) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * b * σ⁻¹) by group, hσa, hc]
      unfold tZero
      simp only [mul_assoc, swap_mul_self_mul]
    obtain ⟨σ', h1, h2⟩ := a10kp_transport hx hy hxy hσa hab'
    exact Or.inr ⟨σ', a, ha, a * b, hab, Or.inr ⟨h1, h2⟩⟩

theorem p4Stmt_holds : P4Stmt := by
  intro E hEA hE2 h4
  rcases klein_normal_form hEA hE2 h4 with ⟨x, hx, hx8⟩ | ⟨σ, a, ha, b, hb, hAB⟩
  · obtain ⟨σ, hσ⟩ := exists_conj_eq_tOne (hE2 x hx) hx8
    have hmem : tOne ∈ E.map (MulAut.conj σ).toMonoidHom := by
      rw [← hσ]
      exact a10kp_mem_map_conj hx
    refine ⟨σ⁻¹ * gOne * σ, a10kp_conj_mem_alt gOne_mem, σ⁻¹ * hOne * σ,
      a10kp_conj_mem_alt hOne_mem, ?_⟩
    rw [sup_conj_eq_map₂ σ gOne hOne, a10kp_card_map]
    exact twentyfive_dvd_of_tOne_mem hmem
  · rcases hAB with ⟨hAσ, hBσ⟩ | ⟨hAσ, hBσ⟩
    · have h1 : tZero ∈ E.map (MulAut.conj σ).toMonoidHom := by
        rw [← hAσ]
        exact a10kp_mem_map_conj ha
      have h2 : taA ∈ E.map (MulAut.conj σ).toMonoidHom := by
        rw [← hBσ]
        exact a10kp_mem_map_conj hb
      refine ⟨σ⁻¹ * gA * σ, a10kp_conj_mem_alt gA_mem, σ⁻¹ * hA * σ,
        a10kp_conj_mem_alt hA_mem, ?_⟩
      rw [sup_conj_eq_map₂ σ gA hA, a10kp_card_map]
      exact twentyfive_dvd_of_A_mem h1 h2
    · have h1 : tZero ∈ E.map (MulAut.conj σ).toMonoidHom := by
        rw [← hAσ]
        exact a10kp_mem_map_conj ha
      have h2 : tbB ∈ E.map (MulAut.conj σ).toMonoidHom := by
        rw [← hBσ]
        exact a10kp_mem_map_conj hb
      refine ⟨σ⁻¹ * gB * σ, a10kp_conj_mem_alt gB_mem, σ⁻¹ * hB * σ,
        a10kp_conj_mem_alt hB_mem, ?_⟩
      rw [sup_conj_eq_map₂ σ gB hB, a10kp_card_map]
      exact twentyfive_dvd_of_B_mem h1 h2

end CFSG.RankThree.PartTwo.Sec15.F153A10K
