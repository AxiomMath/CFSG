module

public import CFSG.Milestones.ASVolI.F48.D43.EFacts

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem burnsideF48dE_σ_mem (j : ℕ) : burnsideF48dE_σ j ∈ burnsideF48dE_Xh := by
  by_cases h2 : j = 2
  · rw [h2, burnsideF48dE_σ_two]
    exact burnsideF48dE_frob_mem
  · exact burnsideF48dE_X_le (burnsideF48dE_σ_mem_X h2)

@[expose] noncomputable def burnsideF48dE_L (j : Fin 18) : ↥burnsideF48dE_Xh :=
  ⟨burnsideF48dE_σ j, burnsideF48dE_σ_mem j⟩

theorem burnsideF48dE_coe_ev (w : List (Fin 18 × Bool)) :
    ((burnsideF48s_ev burnsideF48dE_L w : ↥burnsideF48dE_Xh) : Equiv.Perm (Fin 26572)) =
      burnsideF48s_ev (fun j : Fin 18 => burnsideF48dE_σ j) w :=
  (burnsideF48s_ev_map burnsideF48dE_Xh.subtype burnsideF48dE_L w).symm

theorem burnsideF48dE_L_two : burnsideF48dE_L 2 = burnsideF48dE_F :=
  Subtype.ext burnsideF48dE_σ_two

@[expose] def burnsideF48dE_sh (i : Fin 17) : Fin 18 :=
  if (i : ℕ) < 2 then ⟨i, by omega⟩ else ⟨i + 1, by omega⟩

theorem burnsideF48dE_σ_sh (i : Fin 17) :
    burnsideF48dE_σ (burnsideF48dE_sh i) = burnsideF48d_σ i := by
  unfold burnsideF48dE_sh
  split_ifs with h
  · rw [burnsideF48dE_σ_ne (show ((⟨i, by omega⟩ : Fin 18) : ℕ) ≠ 2 by simp only; omega)]
    simp only [h, if_true]
  · rw [burnsideF48dE_σ_ne (show ((⟨i + 1, by omega⟩ : Fin 18) : ℕ) ≠ 2 by simp only; omega)]
    simp only [show ¬((i : ℕ) + 1 < 2) by omega, if_false, Nat.add_sub_cancel]

theorem burnsideF48dE_ι_L (i : Fin 17) :
    burnsideF48dE_ι (burnsideF48d_L i) = burnsideF48dE_L (burnsideF48dE_sh i) :=
  Subtype.ext (burnsideF48dE_σ_sh i).symm

theorem burnsideF48dE_sh_ne_one {i : Fin 17} (hi : i ≠ 1) : burnsideF48dE_sh i ≠ 1 := by
  intro h
  apply hi
  have h' := congrArg Fin.val h
  unfold burnsideF48dE_sh at h'
  split_ifs at h' with hlt
  · exact Fin.ext h'
  · simp only [Fin.val_one] at h'
    omega

theorem burnsideF48dE_sh_ne_zero {i : Fin 17} (hi : i ≠ 0) : burnsideF48dE_sh i ≠ 0 := by
  intro h
  apply hi
  have h' := congrArg Fin.val h
  unfold burnsideF48dE_sh at h'
  split_ifs at h' with hlt
  · exact Fin.ext h'
  · simp only [Fin.val_zero] at h'
    omega

theorem burnsideF48dE_L_zero : burnsideF48dE_L 0 = burnsideF48dE_ι (burnsideF48d_L 0) := by
  rw [burnsideF48dE_ι_L]
  rfl

theorem burnsideF48dE_L_one : burnsideF48dE_L 1 = burnsideF48dE_ι (burnsideF48d_L 1) := by
  rw [burnsideF48dE_ι_L]
  rfl

abbrev burnsideF48dE_LS1 : Set (Fin 18) := {j | j ≠ 1}

abbrev burnsideF48dE_LS2 : Set (Fin 18) := {j | j ≠ 0}

@[expose] noncomputable def burnsideF48dE_P1 : Subgroup ↥burnsideF48dE_Xh :=
  Subgroup.closure (burnsideF48dE_L '' burnsideF48dE_LS1)

@[expose] noncomputable def burnsideF48dE_P2 : Subgroup ↥burnsideF48dE_Xh :=
  Subgroup.closure (burnsideF48dE_L '' burnsideF48dE_LS2)

theorem burnsideF48dE_F_mem_P1 : burnsideF48dE_F ∈ burnsideF48dE_P1 := by
  rw [← burnsideF48dE_L_two]
  exact Subgroup.subset_closure ⟨2, by decide, rfl⟩

theorem burnsideF48dE_F_mem_P2 : burnsideF48dE_F ∈ burnsideF48dE_P2 := by
  rw [← burnsideF48dE_L_two]
  exact Subgroup.subset_closure ⟨2, by decide, rfl⟩

theorem burnsideF48dE_ι_P1 {z : ↥burnsideF48d_X} (hz : z ∈ burnsideF48d_P1) :
    burnsideF48dE_ι z ∈ burnsideF48dE_P1 := by
  have hle : burnsideF48d_P1 ≤ burnsideF48dE_P1.comap burnsideF48dE_ι := by
    rw [burnsideF48d_P1, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, burnsideF48dE_ι_L]
    exact Subgroup.subset_closure ⟨_, burnsideF48dE_sh_ne_one hi, rfl⟩
  exact hle hz

theorem burnsideF48dE_ι_P2 {z : ↥burnsideF48d_X} (hz : z ∈ burnsideF48d_P2) :
    burnsideF48dE_ι z ∈ burnsideF48dE_P2 := by
  have hle : burnsideF48d_P2 ≤ burnsideF48dE_P2.comap burnsideF48dE_ι := by
    rw [burnsideF48d_P2, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, burnsideF48dE_ι_L]
    exact Subgroup.subset_closure ⟨_, burnsideF48dE_sh_ne_zero hi, rfl⟩
  exact hle hz

theorem burnsideF48dE_inv_apply_self (g : Equiv.Perm (Fin 26572)) (x : Fin 26572) : g⁻¹ (g x) = x :=
  Equiv.Perm.inv_eq_iff_eq.2 rfl

@[expose] def burnsideF48dE_setStab (S : Finset (Fin 26572)) :
    Subgroup (Equiv.Perm (Fin 26572)) where
  carrier := {g | ∀ p ∈ S, g p ∈ S}
  mul_mem' := fun {_ _} ha hb p hp => ha _ (hb p hp)
  one_mem' := fun _ hp => hp
  inv_mem' := fun {g} hg p hp => by
    have himg : S.image g = S := Finset.eq_of_subset_of_card_le
      (fun q hq => by
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
        exact hg r hr)
      (by rw [Finset.card_image_of_injective _ g.injective])
    rw [← himg] at hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
    rw [burnsideF48dE_inv_apply_self]
    exact hr

theorem burnsideF48dE_mem_setStab {S : Finset (Fin 26572)} {g : Equiv.Perm (Fin 26572)} :
    g ∈ burnsideF48dE_setStab S ↔ ∀ p ∈ S, g p ∈ S := Iff.rfl

section Par


theorem burnsideF48dE_coe_dec (x : ↥burnsideF48d_X) (e : ℕ) :
    ((burnsideF48dE_ι x * burnsideF48dE_F ^ e : ↥burnsideF48dE_Xh) : Equiv.Perm (Fin 26572)) =
      (x : Equiv.Perm (Fin 26572)) * burnsideF48d_frob ^ e := by
  rw [Subgroup.coe_mul, SubgroupClass.coe_pow]
  rfl

theorem burnsideF48dE_σ_fix0 (hM : burnsideF48d_ModelFacts) {j : Fin 18} (hj : j ≠ 1) :
    burnsideF48dE_σ j 0 = 0 := by
  by_cases h2 : (j : ℕ) = 2
  · rw [h2, burnsideF48dE_σ_two]
    exact burnsideF48dE_frob_apt hM 0 ((burnsideF48dE_mem_aptF_iff 0).2 (by decide))
  · rw [burnsideF48dE_σ_ne h2]
    have hj1 : (j : ℕ) ≠ 1 := fun h => hj (Fin.ext h)
    have hi : (if (j : ℕ) < 2 then (j : ℕ) else (j : ℕ) - 1) < 17 := by
      have := j.2
      split_ifs <;> omega
    have hi1 : (⟨_, hi⟩ : Fin 17) ≠ 1 := by
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_one] at h'
      split_ifs at h' <;> omega
    exact (hM.mem_P1 (burnsideF48d_L ⟨_, hi⟩)).1 (Subgroup.subset_closure ⟨_, hi1, rfl⟩)

theorem burnsideF48dE_σ_line (hM : burnsideF48d_ModelFacts) {j : Fin 18} (hj : j ≠ 0) :
    burnsideF48dE_σ j ∈ burnsideF48dE_setStab burnsideF48d_line := by
  by_cases h2 : (j : ℕ) = 2
  · rw [h2, burnsideF48dE_σ_two]
    exact burnsideF48dE_frob_line hM
  · rw [burnsideF48dE_σ_ne h2]
    have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    have hi : (if (j : ℕ) < 2 then (j : ℕ) else (j : ℕ) - 1) < 17 := by
      have := j.2
      split_ifs <;> omega
    have hi0 : (⟨_, hi⟩ : Fin 17) ≠ 0 := by
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_zero] at h'
      split_ifs at h' <;> omega
    exact (hM.mem_P2 (burnsideF48d_L ⟨_, hi⟩)).1 (Subgroup.subset_closure ⟨_, hi0, rfl⟩)

theorem burnsideF48dE_mem_P1 (hM : burnsideF48d_ModelFacts) (z : ↥burnsideF48dE_Xh) :
    z ∈ burnsideF48dE_P1 ↔ (z : Equiv.Perm (Fin 26572)) 0 = 0 := by
  constructor
  · intro hz
    have hle : burnsideF48dE_P1 ≤ MulAction.stabilizer ↥burnsideF48dE_Xh (0 : Fin 26572) := by
      rw [burnsideF48dE_P1, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      exact burnsideF48dE_σ_fix0 hM hj
    exact MulAction.mem_stabilizer_iff.1 (hle hz)
  · intro hz
    obtain ⟨e, -, x, rfl⟩ := burnsideF48dE_dec hM z
    have hx0 : (x : Equiv.Perm (Fin 26572)) 0 = 0 := by
      have h := hz
      rw [burnsideF48dE_coe_dec, Equiv.Perm.mul_apply,
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
          (burnsideF48dE_frob_apt hM 0 ((burnsideF48dE_mem_aptF_iff 0).2 (by decide)))] at h
      exact h
    exact burnsideF48dE_P1.mul_mem (burnsideF48dE_ι_P1 ((hM.mem_P1 x).2 hx0))
      (burnsideF48dE_P1.pow_mem burnsideF48dE_F_mem_P1 e)

theorem burnsideF48dE_mem_P2 (hM : burnsideF48d_ModelFacts) (z : ↥burnsideF48dE_Xh) :
    z ∈ burnsideF48dE_P2 ↔ ∀ p ∈ burnsideF48d_line,
      (z : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line := by
  constructor
  · intro hz
    have hle : burnsideF48dE_P2 ≤
        (burnsideF48dE_setStab burnsideF48d_line).comap burnsideF48dE_Xh.subtype := by
      rw [burnsideF48dE_P2, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact burnsideF48dE_σ_line hM hj
    exact hle hz
  · intro hz
    obtain ⟨e, -, x, rfl⟩ := burnsideF48dE_dec hM z
    have hz' : (x : Equiv.Perm (Fin 26572)) * burnsideF48d_frob ^ e ∈
        burnsideF48dE_setStab burnsideF48d_line := by
      rw [← burnsideF48dE_coe_dec]
      exact hz
    have hf : burnsideF48d_frob ^ e ∈ burnsideF48dE_setStab burnsideF48d_line :=
      Subgroup.pow_mem (burnsideF48dE_setStab burnsideF48d_line)
        (burnsideF48dE_mem_setStab.2 (burnsideF48dE_frob_line hM)) e
    have hx : (x : Equiv.Perm (Fin 26572)) ∈ burnsideF48dE_setStab burnsideF48d_line := by
      have := Subgroup.mul_mem _ hz' (Subgroup.inv_mem _ hf)
      rwa [mul_inv_cancel_right] at this
    exact burnsideF48dE_P2.mul_mem (burnsideF48dE_ι_P2 ((hM.mem_P2 x).2 hx))
      (burnsideF48dE_P2.pow_mem burnsideF48dE_F_mem_P2 e)

theorem burnsideF48dE_mem_B (hM : burnsideF48d_ModelFacts) {z : ↥burnsideF48dE_Xh}
    (hz : z ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2)
    (hzX : (z : Equiv.Perm (Fin 26572)) ∈ burnsideF48d_X) :
    (⟨z, hzX⟩ : ↥burnsideF48d_X) ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2 :=
  ⟨(hM.mem_P1 _).2 ((burnsideF48dE_mem_P1 hM z).1 hz.1),
    (hM.mem_P2 _).2 ((burnsideF48dE_mem_P2 hM z).1 hz.2)⟩

theorem burnsideF48dE_ι_B {b : ↥burnsideF48d_X} (hb : b ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2) :
    burnsideF48dE_ι b ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 :=
  ⟨burnsideF48dE_ι_P1 hb.1, burnsideF48dE_ι_P2 hb.2⟩

theorem burnsideF48dE_F_mem_B : burnsideF48dE_F ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 :=
  ⟨burnsideF48dE_F_mem_P1, burnsideF48dE_F_mem_P2⟩

theorem burnsideF48dE_F_cube (hM : burnsideF48d_ModelFacts) : burnsideF48dE_F ^ 3 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact burnsideF48dE_frob_cube hM)

theorem burnsideF48dE_F_not_mem_map (hM : burnsideF48d_ModelFacts) (Q : Subgroup ↥burnsideF48d_X) :
    burnsideF48dE_F ∉ Q.map burnsideF48dE_ι := fun h =>
  burnsideF48dE_frob_not_mem hM ((burnsideF48dE_mem_map_ι _).1 h).1

theorem burnsideF48dE_card_Bh (hM : burnsideF48d_ModelFacts) :
    Nat.card ↥(burnsideF48dE_P1 ⊓ burnsideF48dE_P2) = 82904796 := by
  have hAH : (burnsideF48d_P1 ⊓ burnsideF48d_P2).map burnsideF48dE_ι ≤
      burnsideF48dE_P1 ⊓ burnsideF48dE_P2 := by
    rintro _ ⟨b, hb, rfl⟩
    exact burnsideF48dE_ι_B hb
  have hdec : ∀ z ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2, ∃ e < 3,
      ∃ x ∈ (burnsideF48d_P1 ⊓ burnsideF48d_P2).map burnsideF48dE_ι,
        z = x * burnsideF48dE_F ^ e := by
    intro z hz
    obtain ⟨e, he, x, rfl⟩ := burnsideF48dE_dec hM z
    refine ⟨e, he, _, ⟨x, ?_, rfl⟩, rfl⟩
    have hxB : burnsideF48dE_ι x ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 := by
      have := (burnsideF48dE_P1 ⊓ burnsideF48dE_P2).mul_mem hz
        ((burnsideF48dE_P1 ⊓ burnsideF48dE_P2).inv_mem
          ((burnsideF48dE_P1 ⊓ burnsideF48dE_P2).pow_mem burnsideF48dE_F_mem_B e))
      rwa [mul_inv_cancel_right] at this
    exact burnsideF48dE_mem_B hM hxB x.2
  rw [burnsideF48dE_card_three hAH burnsideF48dE_F_mem_B (burnsideF48dE_F_cube hM)
    (burnsideF48dE_F_not_mem_map hM _) hdec,
    Subgroup.card_map_of_injective (Subgroup.inclusion_injective _), hM.card_B]

@[expose] noncomputable def burnsideF48dE_Th : Subgroup ↥burnsideF48dE_Xh :=
  burnsideF48d_T.map burnsideF48dE_ι

@[expose] noncomputable def burnsideF48dE_Uh : Subgroup ↥burnsideF48dE_Xh :=
  burnsideF48d_U.map burnsideF48dE_ι

@[expose] noncomputable def burnsideF48dE_K : Subgroup ↥burnsideF48dE_Xh :=
  burnsideF48dE_Th ⊔ Subgroup.zpowers burnsideF48dE_F

theorem burnsideF48dE_mem_Th (hM : burnsideF48d_ModelFacts) (z : ↥burnsideF48dE_Xh) :
    z ∈ burnsideF48dE_Th ↔ (z : Equiv.Perm (Fin 26572)) ∈ burnsideF48d_X ∧
      ∀ p ∈ burnsideF48d_aptF, (z : Equiv.Perm (Fin 26572)) p = p := by
  rw [burnsideF48dE_Th, burnsideF48dE_mem_map_ι]
  constructor
  · rintro ⟨h, hT⟩
    exact ⟨h, (hM.mem_T _).1 hT⟩
  · rintro ⟨h, hT⟩
    exact ⟨h, (hM.mem_T _).2 hT⟩

theorem burnsideF48dE_frob_inv_apt (hM : burnsideF48d_ModelFacts) :
    ∀ p ∈ burnsideF48d_aptF, burnsideF48d_frob⁻¹ p = p := fun p hp => by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (burnsideF48dE_frob_apt hM p hp).symm

theorem burnsideF48dE_F_normalizer (hM : burnsideF48d_ModelFacts) :
    burnsideF48dE_F ∈ Subgroup.normalizer (burnsideF48dE_Th : Set ↥burnsideF48dE_Xh) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [burnsideF48dE_mem_Th hM, burnsideF48dE_mem_Th hM]
  have hc : ((burnsideF48dE_F * h * burnsideF48dE_F⁻¹ : ↥burnsideF48dE_Xh) :
      Equiv.Perm (Fin 26572)) = burnsideF48d_frob * h * burnsideF48d_frob⁻¹ := rfl
  rw [hc]
  constructor
  · rintro ⟨hX, hfix⟩
    refine ⟨burnsideF48dE_frob_conj_mem' hM hX, fun p hp => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, burnsideF48dE_frob_inv_apt hM p hp,
      hfix p hp, burnsideF48dE_frob_apt hM p hp]
  · rintro ⟨hX, hfix⟩
    have hX' := burnsideF48dE_frob_conj_mem hM hX
    have e : burnsideF48d_frob⁻¹ * (burnsideF48d_frob * (h : Equiv.Perm (Fin 26572)) *
        burnsideF48d_frob⁻¹) * burnsideF48d_frob = h := by group
    rw [e] at hX'
    refine ⟨hX', fun p hp => ?_⟩
    have h1 := hfix p hp
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, burnsideF48dE_frob_inv_apt hM p hp] at h1
    have h2 := congrArg (fun q => burnsideF48d_frob⁻¹ q) h1
    simp only [burnsideF48dE_inv_apply_self] at h2
    rw [h2, burnsideF48dE_frob_inv_apt hM p hp]

theorem burnsideF48dE_mem_K (hM : burnsideF48d_ModelFacts) (z : ↥burnsideF48dE_Xh) :
    z ∈ burnsideF48dE_K ↔ ∃ e < 3, ∃ t ∈ burnsideF48dE_Th, z = t * burnsideF48dE_F ^ e :=
  burnsideF48dE_mem_sup_iff (burnsideF48dE_F_cube hM) (burnsideF48dE_F_normalizer hM) z

theorem burnsideF48dE_Th_le_K : burnsideF48dE_Th ≤ burnsideF48dE_K := le_sup_left

theorem burnsideF48dE_F_mem_K : burnsideF48dE_F ∈ burnsideF48dE_K :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem burnsideF48dE_card_K (hM : burnsideF48d_ModelFacts) : Nat.card ↥burnsideF48dE_K = 156 := by
  rw [burnsideF48dE_card_three burnsideF48dE_Th_le_K burnsideF48dE_F_mem_K (burnsideF48dE_F_cube hM)
    (burnsideF48dE_F_not_mem_map hM _) fun z hz => (burnsideF48dE_mem_K hM z).1 hz,
    burnsideF48dE_Th, Subgroup.card_map_of_injective (Subgroup.inclusion_injective _), hM.card_T]

theorem burnsideF48dE_Th_le (hM : burnsideF48d_ModelFacts) :
    burnsideF48dE_Th ≤ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 := by
  rintro _ ⟨t, ht, rfl⟩
  exact burnsideF48dE_ι_B (hM.T_le ht)

theorem burnsideF48dE_K_le (hM : burnsideF48d_ModelFacts) :
    burnsideF48dE_K ≤ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 :=
  sup_le (burnsideF48dE_Th_le hM) (Subgroup.zpowers_le.2 burnsideF48dE_F_mem_B)

theorem burnsideF48dE_K_inf_X (hM : burnsideF48d_ModelFacts) {z : ↥burnsideF48dE_Xh}
    (hz : z ∈ burnsideF48dE_K) (hzX : (z : Equiv.Perm (Fin 26572)) ∈ burnsideF48d_X) :
    z ∈ burnsideF48dE_Th := by
  obtain ⟨e, he, t, ht, rfl⟩ := (burnsideF48dE_mem_K hM z).1 hz
  have htX : (t : Equiv.Perm (Fin 26572)) ∈ burnsideF48d_X := ((burnsideF48dE_mem_Th hM t).1 ht).1
  by_cases he0 : e = 0
  · rw [he0, pow_zero, mul_one]
    exact ht
  · exfalso
    have hF : burnsideF48dE_F ^ e ∈ burnsideF48dE_Xs := by
      have h1 : t ∈ burnsideF48dE_Xs := htX
      have h2 : t * burnsideF48dE_F ^ e ∈ burnsideF48dE_Xs := hzX
      have := burnsideF48dE_Xs.mul_mem (burnsideF48dE_Xs.inv_mem h1) h2
      rwa [inv_mul_cancel_left] at this
    exact burnsideF48dE_pow_not_mem (burnsideF48dE_F_cube hM)
      (fun h => burnsideF48dE_frob_not_mem hM h) (n := e) (by omega) hF

end Par

end CFSG.ASVolI
