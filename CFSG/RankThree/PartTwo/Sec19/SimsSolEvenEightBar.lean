module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenComb10

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Eight

section Restr

variable {d : ℕ}

@[expose] def stabPerm (I : Finset (Fin d)) : ↥(setStab I) →* Perm ↥I where
  toFun σ := (σ : Perm (Fin d)).subtypePerm (fun x => mem_setStab.1 σ.2 x)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def restrHom (I : Finset (Fin d)) : ↥(setStab I) →* Perm (Fin d) :=
  (Perm.ofSubtype : Perm ↥I →* Perm (Fin d)).comp (stabPerm I)

theorem restrHom_apply_of_mem {I : Finset (Fin d)} (σ : ↥(setStab I)) {x : Fin d} (hx : x ∈ I) :
    restrHom I σ x = (σ : Perm (Fin d)) x :=
  Perm.ofSubtype_subtypePerm_of_mem (p := fun y => y ∈ I) (fun y => mem_setStab.1 σ.2 y) hx

theorem restrHom_apply_of_not_mem {I : Finset (Fin d)} (σ : ↥(setStab I)) {x : Fin d}
    (hx : x ∉ I) : restrHom I σ x = x :=
  Perm.ofSubtype_subtypePerm_of_not_mem (p := fun y => y ∈ I) (fun y => mem_setStab.1 σ.2 y) hx

theorem setStab_le_compl (I : Finset (Fin d)) : setStab I ≤ setStab Iᶜ := fun σ hσ x => by
  have := mem_setStab.1 hσ x
  simp only [Finset.mem_compl]
  exact not_iff_not.2 this

theorem restrHom_mem_setStab {I : Finset (Fin d)} (σ : ↥(setStab I)) :
    restrHom I σ ∈ setStab I := fun x => by
  by_cases hx : x ∈ I
  · rw [restrHom_apply_of_mem σ hx]
    exact iff_of_true ((mem_setStab.1 σ.2 x).2 hx) hx
  · rw [restrHom_apply_of_not_mem σ hx]

theorem restrHom_mul_restrHom_compl {I : Finset (Fin d)} (σ : ↥(setStab I)) :
    restrHom I σ * restrHom Iᶜ ⟨σ, setStab_le_compl I σ.2⟩ = σ := by
  ext x
  rw [Perm.mul_apply]
  by_cases hx : x ∈ I
  · have hx' : x ∉ Iᶜ := fun h => (Finset.mem_compl.1 h) hx
    rw [restrHom_apply_of_not_mem _ hx', restrHom_apply_of_mem σ hx]
  · have hx' : x ∈ Iᶜ := Finset.mem_compl.2 hx
    have hσx : (σ : Perm (Fin d)) x ∉ I := fun h => hx ((mem_setStab.1 σ.2 x).1 h)
    rw [restrHom_apply_of_mem _ hx', restrHom_apply_of_not_mem σ hσx]

theorem restrHom_eq_self {I : Finset (Fin d)} (σ : ↥(setStab I)) (h : ∀ x, x ∉ I → σ.1 x = x) :
    restrHom I σ = σ := by
  ext x
  by_cases hx : x ∈ I
  · rw [restrHom_apply_of_mem σ hx]
  · rw [restrHom_apply_of_not_mem σ hx, h x hx]

theorem fourGroup_restr {I : Finset (Fin d)} {N : Subgroup (Perm (Fin d))} (hN2 : IsPGroup 2 N)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) :
    FourGroup I ((N.subgroupOf (setStab I)).map (restrHom I)) where
  two := by
    have h : IsPGroup 2 ↥(N.subgroupOf (setStab I)) := by
      intro g
      obtain ⟨k, hk⟩ := hN2 ⟨((g : ↥(setStab I)) : Perm (Fin d)), g.2⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    exact h.map _
  stab := by
    rintro _ ⟨σ, -, rfl⟩
    exact restrHom_mem_setStab σ
  fix := by
    rintro _ ⟨σ, -, rfl⟩ x hx
    exact restrHom_apply_of_not_mem σ hx
  norm := by
    rintro τ hτ _ ⟨σ, hσ, rfl⟩
    have hτS : τ ∈ setStab I := altOn_le_setStab I hτ
    have hfixτ : ∀ x, x ∉ I → τ x = x := (mem_altOn.1 hτ).1
    refine ⟨⟨τ, hτS⟩ * σ * ⟨τ, hτS⟩⁻¹, ?_, ?_⟩
    · have hσ' : (σ : Perm (Fin d)) ∈ N := hσ
      show τ * (σ : Perm (Fin d)) * τ⁻¹ ∈ N
      exact hA τ hτ _ hσ'
    · rw [map_mul, map_mul, map_inv, restrHom_eq_self ⟨τ, hτS⟩ hfixτ]

theorem card_le_sixteen {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {N : Subgroup (Perm (Fin d))} (hN2 : IsPGroup 2 N) (hNI : N ≤ setStab I)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) : Nat.card N ≤ 16 := by
  set N₁ := (N.subgroupOf (setStab I)).map (restrHom I) with hN₁
  set N₂ := (N.subgroupOf (setStab Iᶜ)).map (restrHom Iᶜ) with hN₂
  have h1 : Nat.card N₁ ≤ 4 := (fourGroup_restr hN2 hA).card_le_four hI
  have h2 : Nat.card N₂ ≤ 4 := (fourGroup_restr hN2 hA').card_le_four hIc
  let f : ↥N → ↥N₁ × ↥N₂ := fun σ =>
    (⟨restrHom I ⟨σ, hNI σ.2⟩, ⟨⟨σ, hNI σ.2⟩, σ.2, rfl⟩⟩,
      ⟨restrHom Iᶜ ⟨σ, setStab_le_compl I (hNI σ.2)⟩,
        ⟨⟨σ, setStab_le_compl I (hNI σ.2)⟩, σ.2, rfl⟩⟩)
  have hf : Function.Injective f := by
    intro σ τ h
    have h1 := congrArg (fun p => (p.1 : Perm (Fin d))) h
    have h2 := congrArg (fun p => (p.2 : Perm (Fin d))) h
    simp only [f] at h1 h2
    have e1 := restrHom_mul_restrHom_compl (I := I) ⟨σ, hNI σ.2⟩
    have e2 := restrHom_mul_restrHom_compl (I := I) ⟨τ, hNI τ.2⟩
    refine Subtype.ext ?_
    rw [← e1, ← e2, h1]
    exact congrArg _ h2
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at this
  calc Nat.card N ≤ Nat.card N₁ * Nat.card N₂ := this
    _ ≤ 4 * 4 := Nat.mul_le_mul h1 h2

end Restr

section Swap

variable {d : ℕ}

theorem not_swap_of_normalized {I : Finset (Fin d)} (hI : 3 ≤ I.card)
    {N : Subgroup (Perm (Fin d))} (hN2 : IsPGroup 2 N)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) {σ : Perm (Fin d)} (hσ : σ ∈ N)
    (hswap : ∀ x, σ x ∈ I ↔ x ∉ I) : False := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 (by omega : 2 < I.card)
  set τ : Perm (Fin d) := cyc a b c with hτ
  have hτA : τ ∈ altOn I := cyc_mem_altOn_of_mem ha hb hc hab hac hbc
  have hτfix : ∀ x, x ∉ I → τ x = x := (mem_altOn.1 hτA).1
  have hτ3 : τ ^ 3 = 1 := (cyc_isThreeCycle hab hac hbc).orderOf ▸ pow_orderOf_eq_one τ
  set τ' : Perm (Fin d) := σ * τ⁻¹ * σ⁻¹ with hτ'
  have hτ'fix : ∀ x, x ∈ I → τ' x = x := by
    intro x hx
    have hσx : σ⁻¹ x ∉ I := by
      intro h
      have := (hswap (σ⁻¹ x)).1
      rw [perm_apply_inv_self] at this
      exact this hx h
    simp only [hτ', Perm.mul_apply]
    have : τ⁻¹ (σ⁻¹ x) = σ⁻¹ x := by
      rw [Perm.inv_eq_iff_eq]
      exact (hτfix _ hσx).symm
    rw [this, perm_apply_inv_self]
  have hdisj : Perm.Disjoint τ τ' := fun x => by
    by_cases hx : x ∈ I
    · exact Or.inr (hτ'fix x hx)
    · exact Or.inl (hτfix x hx)
  have hρN : τ * τ' ∈ N := by
    have : τ * τ' = τ * σ * τ⁻¹ * σ⁻¹ := by simp only [hτ']; group
    rw [this]
    exact N.mul_mem (hA τ hτA σ hσ) (N.inv_mem hσ)
  have hτ'3 : τ' ^ 3 = 1 := by
    simp only [hτ', conj_pow, inv_pow, hτ3, inv_one, mul_one, mul_inv_cancel]
  have hρ3 : (τ * τ') ^ 3 = 1 := by
    rw [hdisj.commute.mul_pow, hτ3, hτ'3, one_mul]
  obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one hN2 hρN
  have hρ1 : τ * τ' = 1 := eq_one_of_pow_odd (by decide : Odd 3) hρ3 hj
  have h := congrArg (fun f : Perm (Fin d) => f a) hρ1
  simp only [Perm.mul_apply, Perm.one_apply, hτ'fix a ha] at h
  rw [hτ, cyc_apply_first hac hbc] at h
  exact hac h.symm

end Swap

section Klein8

variable {d : ℕ}

@[expose] noncomputable def klein8 (I : Finset (Fin d)) : Subgroup (Perm (Fin d)) :=
  klein4 I ⊔ klein4 Iᶜ

theorem klein4_fix {I : Finset (Fin d)} (hI : I.card = 4) {σ : Perm (Fin d)} (hσ : σ ∈ klein4 I)
    {x : Fin d} (hx : x ∉ I) : σ x = x :=
  (klein4_fourGroup hI).fix σ hσ x hx

theorem klein4_disjoint {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {σ₁ σ₂ : Perm (Fin d)} (h₁ : σ₁ ∈ klein4 I) (h₂ : σ₂ ∈ klein4 Iᶜ) : Perm.Disjoint σ₁ σ₂ :=
  fun x => by
    by_cases hx : x ∈ I
    · exact Or.inr (klein4_fix hIc h₂ (fun h => (Finset.mem_compl.1 h) hx))
    · exact Or.inl (klein4_fix hI h₁ hx)

theorem mem_klein8_iff {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {σ : Perm (Fin d)} : σ ∈ klein8 I ↔ ∃ σ₁ ∈ klein4 I, ∃ σ₂ ∈ klein4 Iᶜ, σ₁ * σ₂ = σ := by
  have hle : klein4 I ≤ Subgroup.normalizer ((klein4 Iᶜ : Subgroup (Perm (Fin d))) :
      Set (Perm (Fin d))) := fun σ₁ h₁ => by
    rw [Subgroup.mem_normalizer_iff]
    intro σ₂
    constructor
    · intro h₂
      rw [(klein4_disjoint hI hIc h₁ h₂).commute.eq, mul_inv_cancel_right]
      exact h₂
    · intro h₂
      have hd := klein4_disjoint hI hIc h₁ h₂
      have e : σ₂ = σ₁⁻¹ * (σ₁ * σ₂ * σ₁⁻¹) * σ₁ := by group
      rw [e]
      have hd' := klein4_disjoint hI hIc ((klein4 I).inv_mem h₁) h₂
      rw [hd'.commute.eq, inv_mul_cancel_right] at *
      · simpa [mul_assoc] using h₂
  unfold klein8
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul]
  rfl

theorem klein4_le_klein8 (I : Finset (Fin d)) : klein4 I ≤ klein8 I := le_sup_left

theorem klein4_compl_le_klein8 (I : Finset (Fin d)) : klein4 Iᶜ ≤ klein8 I := le_sup_right

theorem eq_one_of_mem_klein4_both {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {σ : Perm (Fin d)} (h₁ : σ ∈ klein4 I) (h₂ : σ ∈ klein4 Iᶜ) : σ = 1 := by
  refine Equiv.ext fun x => ?_
  show σ x = x
  by_cases hx : x ∈ I
  · exact klein4_fix hIc h₂ (fun h => (Finset.mem_compl.1 h) hx)
  · exact klein4_fix hI h₁ hx

theorem card_klein8 {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4) :
    Nat.card (klein8 I) = 16 := by
  let f : ↥(klein4 I) × ↥(klein4 Iᶜ) → ↥(klein8 I) := fun p =>
    ⟨p.1 * p.2, (mem_klein8_iff hI hIc).2 ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun σ => ?_⟩
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
      obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := q
      have h' : a * b = a' * b' := congrArg Subtype.val h
      have e : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      have h1 := eq_one_of_mem_klein4_both hI hIc
        ((klein4 I).mul_mem ((klein4 I).inv_mem ha') ha)
        (e ▸ (klein4 Iᶜ).mul_mem hb' ((klein4 Iᶜ).inv_mem hb))
      have hp1 : a = a' := by
        have := congrArg (fun t => a' * t) h1
        simpa using this
      subst hp1
      have hp2 : b = b' := mul_left_cancel h'
      subst hp2
      rfl
    · obtain ⟨σ₁, h₁, σ₂, h₂, e⟩ := (mem_klein8_iff hI hIc).1 σ.2
      exact ⟨(⟨σ₁, h₁⟩, ⟨σ₂, h₂⟩), Subtype.ext e⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_klein4 hI, card_klein4 hIc]

theorem klein8_le_setStab {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4) :
    klein8 I ≤ setStab I := by
  intro σ hσ
  obtain ⟨σ₁, h₁, σ₂, h₂, rfl⟩ := (mem_klein8_iff hI hIc).1 hσ
  exact (setStab I).mul_mem ((klein4_fourGroup hI).stab h₁)
    (setStab_compl_le I ((klein4_fourGroup hIc).stab h₂))

theorem klein4_conj_mem_image {I : Finset (Fin d)} (hI : I.card = 4) (τ : Perm (Fin d))
    {σ : Perm (Fin d)} (hσ : σ ∈ klein4 I) : τ * σ * τ⁻¹ ∈ klein4 (I.image τ) := by
  have hI' : (I.image τ).card = 4 := by rw [card_image_perm, hI]
  obtain ⟨hA, hsq⟩ := (mem_klein4_iff hI).1 hσ
  refine (mem_klein4_iff hI').2 ⟨?_, ?_⟩
  · rw [mem_altOn] at hA ⊢
    refine ⟨fun x hx => ?_, by simp [hA.2]⟩
    have h1 : τ⁻¹ x ∉ I := fun h => hx (Finset.mem_image.2 ⟨τ⁻¹ x, h, by simp⟩)
    simp only [Perm.mul_apply]
    rw [hA.1 _ h1, perm_apply_inv_self]
  · calc τ * σ * τ⁻¹ * (τ * σ * τ⁻¹) = τ * (σ * σ) * τ⁻¹ := by group
      _ = 1 := by rw [hsq]; group

theorem klein8_conj_mem {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {τ : Perm (Fin d)} (hτ : τ ∈ setStab I ∨ ∀ x, τ x ∈ I ↔ x ∉ I) {σ : Perm (Fin d)}
    (hσ : σ ∈ klein8 I) : τ * σ * τ⁻¹ ∈ klein8 I := by
  obtain ⟨σ₁, h₁, σ₂, h₂, rfl⟩ := (mem_klein8_iff hI hIc).1 hσ
  have e : τ * (σ₁ * σ₂) * τ⁻¹ = (τ * σ₁ * τ⁻¹) * (τ * σ₂ * τ⁻¹) := by group
  rw [e]
  have h1 := klein4_conj_mem_image hI τ h₁
  have h2 := klein4_conj_mem_image hIc τ h₂
  rcases hτ with hs | hsw
  · have hτI : I.image τ = I := (image_eq_iff_mem_setStab τ I).2 hs
    have hτIc : Iᶜ.image τ = Iᶜ := (image_eq_iff_mem_setStab τ Iᶜ).2 (setStab_le_compl I hs)
    rw [hτI] at h1
    rw [hτIc] at h2
    exact (klein8 I).mul_mem (klein4_le_klein8 I h1) (klein4_compl_le_klein8 I h2)
  · have hτI : I.image τ = Iᶜ := by
      ext y
      simp only [Finset.mem_image, Finset.mem_compl]
      constructor
      · rintro ⟨x, hx, rfl⟩ h
        exact (hsw x).1 h hx
      · intro hy
        refine ⟨τ⁻¹ y, ?_, perm_apply_inv_self τ y⟩
        by_contra h
        have := (hsw (τ⁻¹ y)).2 h
        rw [perm_apply_inv_self] at this
        exact hy this
    have hτIc : Iᶜ.image τ = I := by
      ext y
      simp only [Finset.mem_image, Finset.mem_compl]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hsw x).2 hx
      · intro hy
        refine ⟨τ⁻¹ y, fun h => ?_, perm_apply_inv_self τ y⟩
        have := (hsw (τ⁻¹ y)).1
        rw [perm_apply_inv_self] at this
        exact this hy h
    rw [hτI] at h1
    rw [hτIc] at h2
    rw [← (klein4_disjoint hI hIc h2 h1).commute.eq]
    exact (klein8 I).mul_mem (klein4_le_klein8 I h2) (klein4_compl_le_klein8 I h1)

theorem klein4_le_of_inf {J : Finset (Fin d)} (hJ : J.card = 4) {N : Subgroup (Perm (Fin d))}
    (hA : ∀ τ ∈ altOn J, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) (hne : N ⊓ klein4 J ≠ ⊥) :
    klein4 J ≤ N := by
  have h := (klein4_fourGroup hJ).eq_of_le hJ (N' := N ⊓ klein4 J) inf_le_right hne
    (fun τ hτ σ hσ => ⟨hA τ hτ σ hσ.1,
      (klein4_fourGroup hJ).norm τ hτ σ hσ.2⟩)
  rw [← h]
  exact inf_le_left

theorem klein4_le_of_normalized {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {N : Subgroup (Perm (Fin d))} (hN : N ≤ klein8 I) (hN1 : N ≠ ⊥)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) :
    klein4 I ≤ N ∨ klein4 Iᶜ ≤ N := by
  obtain ⟨⟨σ, hσN⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN1
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  obtain ⟨σ₁, h₁, σ₂, h₂, rfl⟩ := (mem_klein8_iff hI hIc).1 (hN hσN)
  have key : ∀ (J : Finset (Fin d)) (hJ : J.card = 4) (ρ ρ' : Perm (Fin d)),
      ρ ∈ klein4 J → ρ ≠ 1 → (∀ τ ∈ altOn J, τ * ρ' = ρ' * τ) →
      (∀ τ ∈ altOn J, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) → ρ * ρ' ∈ N → klein4 J ≤ N := by
    intro J hJ ρ ρ' hρ hρ1 hcomm hAJ hρN
    refine klein4_le_of_inf hJ hAJ fun hbot => ?_
    have hc : ∀ τ ∈ altOn J, τ * ρ * τ⁻¹ = ρ := by
      intro τ hτ
      have hc' : Commute τ ρ' := hcomm τ hτ
      have hm : τ * (ρ * ρ') * τ⁻¹ * (ρ * ρ')⁻¹ ∈ N ⊓ klein4 J := by
        refine ⟨N.mul_mem (hAJ τ hτ _ hρN) (N.inv_mem hρN), ?_⟩
        have e : τ * (ρ * ρ') * τ⁻¹ * (ρ * ρ')⁻¹ = (τ * ρ * τ⁻¹) * ρ⁻¹ := by
          calc τ * (ρ * ρ') * τ⁻¹ * (ρ * ρ')⁻¹ = τ * ρ * (ρ' * τ⁻¹) * ρ'⁻¹ * ρ⁻¹ := by group
            _ = τ * ρ * (τ⁻¹ * ρ') * ρ'⁻¹ * ρ⁻¹ := by rw [← hc'.inv_left.eq]
            _ = τ * ρ * τ⁻¹ * ρ⁻¹ := by group
        rw [e]
        exact (klein4 J).mul_mem ((klein4_fourGroup hJ).norm τ hτ ρ hρ) ((klein4 J).inv_mem hρ)
      rw [hbot, Subgroup.mem_bot] at hm
      have h1 : τ * (ρ * ρ') * τ⁻¹ = ρ * ρ' := mul_inv_eq_one.1 hm
      have h4 : τ * ρ'⁻¹ * τ⁻¹ = ρ'⁻¹ := by
        rw [hc'.inv_right.eq, mul_inv_cancel_right]
      calc τ * ρ * τ⁻¹ = τ * (ρ * ρ') * τ⁻¹ * (τ * ρ'⁻¹ * τ⁻¹) := by group
        _ = ρ := by rw [h1, h4, mul_inv_cancel_right]
    have hz := (klein4_fourGroup hJ).eq_of_le hJ (N' := Subgroup.zpowers ρ)
      (Subgroup.zpowers_le.2 hρ) (fun h => hρ1 (Subgroup.zpowers_eq_bot.1 h))
      (fun τ hτ σ hσ => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
        rw [← conj_zpow, hc τ hτ]
        exact Subgroup.zpow_mem_zpowers ρ k)
    have hsq : ρ * ρ = 1 := ((mem_klein4_iff hJ).1 hρ).2
    have hord : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have hcard : Nat.card (Subgroup.zpowers ρ) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) hord
    rw [hz, card_klein4 hJ] at hcard
    omega
  by_cases hs1 : σ₁ = 1
  · subst hs1
    rw [one_mul] at hσ1' hσN
    right
    refine key Iᶜ hIc σ₂ 1 h₂ hσ1' (fun τ _ => by rw [mul_one, one_mul]) hA' (by simpa using hσN)
  · left
    refine key I hI σ₁ σ₂ h₁ hs1 (fun τ hτ => ?_) hA hσN
    have hτ' : τ ∈ klein4 I ∨ True := Or.inr trivial
    clear hτ'
    have hd : Perm.Disjoint τ σ₂ := fun x => by
      by_cases hx : x ∈ I
      · exact Or.inr (klein4_fix hIc h₂ (fun h => (Finset.mem_compl.1 h) hx))
      · exact Or.inl ((mem_altOn.1 hτ).1 x hx)
    exact hd.commute.eq

end Klein8

section Qbar

variable {n : ℕ}

@[expose] noncomputable def barParOn (I : Finset (Fin n)) : permBar n →+ ZMod 2 :=
  if hI : Even I.card then
    QuotientAddGroup.lift _
      { toFun := fun x => ∑ i ∈ I, x i
        map_zero' := by simp
        map_add' := fun x y => by simp [Finset.sum_add_distrib] } (by
      intro z hz
      rw [AddMonoidHom.mem_ker]
      rcases (mem_zmultiples_allOnes_iff z).1 hz with rfl | rfl
      · simp
      · show ∑ i ∈ I, allOnes n i = 0
        simp only [allOnes, Finset.sum_const, nsmul_eq_mul, mul_one]
        exact (ZMod.natCast_eq_zero_iff_even).2 hI)
  else 0

theorem barParOn_mk {I : Finset (Fin n)} (hI : Even I.card) (x : Fin n → ZMod 2) :
    barParOn I (x : permBar n) = ∑ i ∈ I, x i := by
  unfold barParOn
  rw [dif_pos hI]
  rfl

@[expose] noncomputable def qbar0 (I : Finset (Fin n)) : AddSubgroup (permBar n) :=
  (barParOn I).ker ⊓ (barParOn Iᶜ).ker

theorem mem_qbar0_mk {I : Finset (Fin n)} (hI : Even I.card) (hIc : Even Iᶜ.card)
    (x : Fin n → ZMod 2) :
    (x : permBar n) ∈ qbar0 I ↔ ∑ i ∈ I, x i = 0 ∧ ∑ i ∈ Iᶜ, x i = 0 := by
  unfold qbar0
  rw [AddSubgroup.mem_inf, AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, barParOn_mk hI,
    barParOn_mk hIc]

theorem qbar0_compl (I : Finset (Fin n)) : qbar0 Iᶜ = qbar0 I := by
  unfold qbar0
  rw [compl_compl, inf_comm]

theorem qbar0_le_heart {I : Finset (Fin n)} (hI : Even I.card) (hIc : Even Iᶜ.card) :
    qbar0 I ≤ (heartToBar : altHeart n →+ permBar n).range := by
  intro v hv
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨h1, h2⟩ := (mem_qbar0_mk hI hIc x).1 hv
  have h : ∑ i, x i = 0 := by
    rw [← Finset.sum_add_sum_compl I, h1, h2, add_zero]
  obtain ⟨u, hu⟩ := mk_mem_range_heartToBar h
  exact ⟨u, hu⟩

theorem sum_four {J : Finset (Fin n)} (hJ : J.card = 4) {a b c e : Fin n} (ha : a ∈ J)
    (hb : b ∈ J) (hc : c ∈ J) (he : e ∈ J) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (x : Fin n → ZMod 2) :
    ∑ k ∈ J, x k = x a + x b + x c + x e := by
  have hsub : ({a, b, c, e} : Finset (Fin n)) ⊆ J := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, e} : Finset (Fin n)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hce]
    · simp [hbc, hbe]
    · simp [hab, hac, hae]
  have hJeq : ({a, b, c, e} : Finset (Fin n)) = J :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hJ, hcard])
  rw [← hJeq, Finset.sum_insert (by simp [hab, hac, hae]), Finset.sum_insert (by simp [hbc, hbe]),
    Finset.sum_pair hce]
  ring

theorem klein4_mul_self {J : Finset (Fin n)} (hJ : J.card = 4) {ρ : Perm (Fin n)}
    (hρ : ρ ∈ klein4 J) : ρ * ρ = 1 := ((mem_klein4_iff hJ).1 hρ).2

theorem klein4_apply_apply {J : Finset (Fin n)} (hJ : J.card = 4) {ρ : Perm (Fin n)}
    (hρ : ρ ∈ klein4 J) (i : Fin n) : ρ (ρ i) = i := by
  have := congrArg (fun f : Perm (Fin n) => f i) (klein4_mul_self hJ hρ)
  simpa [Perm.mul_apply] using this

theorem klein4_inv {J : Finset (Fin n)} (hJ : J.card = 4) {ρ : Perm (Fin n)}
    (hρ : ρ ∈ klein4 J) : ρ⁻¹ = ρ :=
  inv_eq_of_mul_eq_one_right (klein4_mul_self hJ hρ)

private theorem zmod2_double : ∀ a b : ZMod 2, a + a = b + b := by decide

private theorem zmod2_double_one : ∀ a b : ZMod 2, a + 1 + a = b + 1 + b := by decide

private theorem zmod2_cancel : ∀ a b : ZMod 2, a = b + (a + b) := by decide

private theorem zmod2_four_eq : ∀ a b c e : ZMod 2, a + b + c + e = 0 → b + a = e + c := by
  decide

private theorem zmod2_four_ne : ∀ a b c e : ZMod 2, a + b + c + e = 1 → b + a ≠ e + c := by
  decide

theorem pair_sum_eq {J : Finset (Fin n)} (hJ : J.card = 4) {ρ : Perm (Fin n)} (hρ : ρ ∈ klein4 J)
    {x : Fin n → ZMod 2} (hx : ∑ k ∈ J, x k = 0) {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J) :
    x (ρ i) + x i = x (ρ j) + x j := by
  by_cases hρ1 : ρ = 1
  · subst hρ1
    rw [Perm.one_apply, Perm.one_apply]
    exact zmod2_double _ _
  have hF := klein4_fourGroup hJ
  have hfree := hF.free hJ hρ hρ1
  have hst : ∀ k, ρ k ∈ J ↔ k ∈ J := mem_setStab.1 (hF.stab hρ)
  by_cases hji : j = i
  · subst hji
    rfl
  by_cases hjr : j = ρ i
  · subst hjr
    rw [klein4_apply_apply hJ hρ, add_comm]
  have h1 : i ≠ ρ i := fun h => hfree i hi h.symm
  have h2 : i ≠ ρ j := fun h => hjr (by rw [h, klein4_apply_apply hJ hρ])
  have h3 : ρ i ≠ j := fun h => hjr h.symm
  have h4 : ρ i ≠ ρ j := fun h => hji (ρ.injective h).symm
  have h5 : j ≠ ρ j := fun h => hfree j hj h.symm
  have hs := sum_four hJ hi ((hst i).2 hi) hj ((hst j).2 hj) h1 (Ne.symm hji) h2 h3 h4 h5 x
  rw [hx] at hs
  exact zmod2_four_eq _ _ _ _ hs.symm

theorem pair_sum_ne {J : Finset (Fin n)} (hJ : J.card = 4) {ρ : Perm (Fin n)} (hρ : ρ ∈ klein4 J)
    (hρ1 : ρ ≠ 1) {x : Fin n → ZMod 2} (hx : ∑ k ∈ J, x k = 1) {i : Fin n} (hi : i ∈ J) :
    ∃ j ∈ J, x (ρ i) + x i ≠ x (ρ j) + x j := by
  have hF := klein4_fourGroup hJ
  have hfree := hF.free hJ hρ hρ1
  have hst : ∀ k, ρ k ∈ J ↔ k ∈ J := mem_setStab.1 (hF.stab hρ)
  obtain ⟨j, hj, hjs⟩ := exists_fourth hJ {i, ρ i} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjs
  obtain ⟨hji, hjr⟩ := hjs
  refine ⟨j, hj, ?_⟩
  have h1 : i ≠ ρ i := fun h => hfree i hi h.symm
  have h2 : i ≠ ρ j := fun h => hjr (by rw [h, klein4_apply_apply hJ hρ])
  have h3 : ρ i ≠ j := fun h => hjr h.symm
  have h4 : ρ i ≠ ρ j := fun h => hji (ρ.injective h).symm
  have h5 : j ≠ ρ j := fun h => hfree j hj h.symm
  have hs := sum_four hJ hi ((hst i).2 hi) hj ((hst j).2 hj) h1 (Ne.symm hji) h2 h3 h4 h5 x
  rw [hx] at hs
  exact zmod2_four_ne _ _ _ _ hs.symm

variable {I : Finset (Fin n)}

theorem klein8_inv_apply (hI : I.card = 4) (hIc : Iᶜ.card = 4) {σ₁ σ₂ : Perm (Fin n)}
    (h₁ : σ₁ ∈ klein4 I) (h₂ : σ₂ ∈ klein4 Iᶜ) (k : Fin n) :
    (σ₁ * σ₂)⁻¹ k = if k ∈ I then σ₁ k else σ₂ k := by
  rw [mul_inv_rev, klein4_inv hI h₁, klein4_inv hIc h₂, Perm.mul_apply]
  by_cases hk : k ∈ I
  · rw [if_pos hk]
    have hk' : σ₁ k ∈ I := (mem_setStab.1 ((klein4_fourGroup hI).stab h₁) k).2 hk
    exact klein4_fix hIc h₂ (fun h => (Finset.mem_compl.1 h) hk')
  · rw [if_neg hk, klein4_fix hI h₁ hk]

theorem exists_nontrivial_part (hI : I.card = 4) (hIc : Iᶜ.card = 4) {σ : Perm (Fin n)}
    (hσ : σ ∈ klein8 I) (hσ1 : σ ≠ 1) :
    ∃ J : Finset (Fin n), (J = I ∨ J = Iᶜ) ∧ ∃ ρ₁ ∈ klein4 J, ρ₁ ≠ 1 ∧ ∃ ρ₂ ∈ klein4 Jᶜ,
      ρ₁ * ρ₂ = σ := by
  obtain ⟨σ₁, h₁, σ₂, h₂, rfl⟩ := (mem_klein8_iff hI hIc).1 hσ
  by_cases hs : σ₁ = 1
  · subst hs
    rw [one_mul] at hσ1 ⊢
    exact ⟨Iᶜ, Or.inr rfl, σ₂, h₂, hσ1, 1, (klein4 Iᶜᶜ).one_mem, mul_one _⟩
  · exact ⟨I, Or.inl rfl, σ₁, h₁, hs, σ₂, h₂, rfl⟩

theorem barAct_mk_eq_self_iff {σ : Perm (Fin n)} {x : Fin n → ZMod 2} :
    barAct σ (x : permBar n) = (x : permBar n) ↔
      (∀ k, x (σ⁻¹ k) = x k) ∨ (∀ k, x (σ⁻¹ k) = x k + 1) := by
  rw [barAct_mk, eq_comm, bar_mk_eq_iff]
  rfl

theorem barAct_qbar0 (hI : I.card = 4) (hIc : Iᶜ.card = 4) {σ : Perm (Fin n)}
    (hσ : σ ∈ klein8 I) {v : permBar n} (hv : v ∈ qbar0 I) :
    barAct σ v = v ∨ barAct σ v = v + barInd I := by
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨hx1, hx2⟩ := (mem_qbar0_mk hIe hIce x).1 hv
  obtain ⟨σ₁, h₁, σ₂, h₂, rfl⟩ := (mem_klein8_iff hI hIc).1 hσ
  obtain ⟨i₀, hi₀⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨k₀, hk₀⟩ : Iᶜ.Nonempty := Finset.card_pos.1 (by omega)
  set a := x (σ₁ i₀) + x i₀ with ha
  set b := x (σ₂ k₀) + x k₀ with hb
  have hy : ∀ k, x ((σ₁ * σ₂)⁻¹ k) = x k + if k ∈ I then a else b := by
    intro k
    rw [klein8_inv_apply hI hIc h₁ h₂]
    by_cases hk : k ∈ I
    · rw [if_pos hk, if_pos hk, ha, pair_sum_eq hI h₁ hx1 hi₀ hk]
      exact zmod2_cancel _ _
    · have hk' : k ∈ Iᶜ := Finset.mem_compl.2 hk
      rw [if_neg hk, if_neg hk, hb, pair_sum_eq hIc h₂ hx2 hk₀ hk']
      exact zmod2_cancel _ _
  rcases zmod_two_cases' a with ha0 | ha1 <;> rcases zmod_two_cases' b with hb0 | hb1
  · left
    rw [barAct_mk_eq_self_iff]
    left
    intro k
    rw [hy k]
    split_ifs <;> simp [ha0, hb0]
  · right
    rw [← barInd_compl, barInd, ← QuotientAddGroup.mk_add, barAct_mk, bar_mk_eq_iff]
    left
    intro k
    rw [vecPerm_apply, hy k]
    by_cases hk : k ∈ I
    · simp [hk, indVec, ha0]
    · simp [hk, indVec, hb1]
  · right
    rw [barInd, ← QuotientAddGroup.mk_add, barAct_mk, bar_mk_eq_iff]
    left
    intro k
    rw [vecPerm_apply, hy k]
    by_cases hk : k ∈ I
    · simp [hk, indVec, ha1]
    · simp [hk, indVec, hb0]
  · left
    rw [barAct_mk_eq_self_iff]
    right
    intro k
    rw [hy k]
    split_ifs <;> simp [ha1, hb1]

theorem barAct_ne_of_odd (hI : I.card = 4) (hIc : Iᶜ.card = 4) {σ : Perm (Fin n)}
    (hσ : σ ∈ klein8 I) (hσ1 : σ ≠ 1) {v : permBar n}
    (hvU : v ∈ (heartToBar : altHeart n →+ permBar n).range) (hv : v ∉ qbar0 I) :
    barAct σ v ≠ v := by
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  have hne : Even n := by
    have := Finset.card_add_card_compl I
    rw [Fintype.card_fin] at this
    rw [← this, hI, hIc]
    decide
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  have hsum : ∑ i, x i = 0 := by
    rw [← Comb.barPar_mk hne, ← Comb.mem_range_heartToBar_iff hne]
    exact hvU
  rw [mem_qbar0_mk hIe hIce] at hv
  have hsplit := Finset.sum_add_sum_compl I x
  rw [hsum] at hsplit
  have hodd : ∀ J : Finset (Fin n), (J = I ∨ J = Iᶜ) → ∑ k ∈ J, x k = 1 := by
    intro J hJ
    have hcases : ∀ p q : ZMod 2, p + q = 0 → ¬ (p = 0 ∧ q = 0) → p = 1 ∧ q = 1 := by decide
    obtain ⟨h1, h2⟩ := hcases _ _ hsplit hv
    rcases hJ with rfl | rfl
    · exact h1
    · exact h2
  obtain ⟨J, hJ, ρ₁, h₁, hρ1, ρ₂, h₂, rfl⟩ := exists_nontrivial_part hI hIc hσ hσ1
  have hJc : J.card = 4 ∧ Jᶜ.card = 4 := by
    rcases hJ with rfl | rfl
    · exact ⟨hI, hIc⟩
    · rw [compl_compl]; exact ⟨hIc, hI⟩
  obtain ⟨i, hi⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨j, hj, hij⟩ := pair_sum_ne hJc.1 h₁ hρ1 (hodd J hJ) hi
  intro heq
  rw [barAct_mk_eq_self_iff] at heq
  have hval : ∀ k ∈ J, x ((ρ₁ * ρ₂)⁻¹ k) = x (ρ₁ k) := fun k hk => by
    rw [klein8_inv_apply hJc.1 hJc.2 h₁ h₂, if_pos hk]
  apply hij
  rcases heq with h | h
  · have e1 := h i
    have e2 := h j
    rw [hval i hi] at e1
    rw [hval j hj] at e2
    rw [e1, e2]
    exact zmod2_double _ _
  · have e1 := h i
    have e2 := h j
    rw [hval i hi] at e1
    rw [hval j hj] at e2
    rw [e1, e2]
    exact zmod2_double_one _ _

theorem exists_moved_qbar0 (hI : I.card = 4) (hIc : Iᶜ.card = 4) {σ : Perm (Fin n)}
    (hσ : σ ∈ klein8 I) (hσ1 : σ ≠ 1) : ∃ v ∈ qbar0 I, barAct σ v ≠ v := by
  obtain ⟨J, hJ, ρ₁, h₁, hρ1, ρ₂, h₂, rfl⟩ := exists_nontrivial_part hI hIc hσ hσ1
  have hJc : J.card = 4 ∧ Jᶜ.card = 4 := by
    rcases hJ with rfl | rfl
    · exact ⟨hI, hIc⟩
    · rw [compl_compl]; exact ⟨hIc, hI⟩
  have hq : qbar0 J = qbar0 I := by
    rcases hJ with rfl | rfl
    · rfl
    · exact qbar0_compl I
  rw [← hq]
  have hJe : Even J.card := by rw [hJc.1]; decide
  have hJce : Even Jᶜ.card := by rw [hJc.2]; decide
  have hF := klein4_fourGroup hJc.1
  obtain ⟨i, hi⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨k, hk⟩ : Jᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hkJ : k ∉ J := Finset.mem_compl.1 hk
  obtain ⟨j, hj, hjs⟩ := exists_fourth hJc.1 {i, ρ₁ i} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjs
  obtain ⟨hji, hjr⟩ := hjs
  set x : Fin n → ZMod 2 := Pi.single i 1 + Pi.single j 1 with hx
  refine ⟨(x : permBar n), ?_, ?_⟩
  · rw [mem_qbar0_mk hJe hJce]
    have hic : i ∉ Jᶜ := fun h => (Finset.mem_compl.1 h) hi
    have hjc : j ∉ Jᶜ := fun h => (Finset.mem_compl.1 h) hj
    constructor
    · simp only [hx, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', if_pos hi,
        if_pos hj]
      decide
    · simp [hx, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', hic, hjc]
  · intro heq
    rw [barAct_mk_eq_self_iff] at heq
    have hfree := hF.free hJc.1 h₁ hρ1
    have hρi : ρ₁ i ≠ i := hfree i hi
    have hρij : ρ₁ i ≠ j := fun h => hjr h.symm
    have hvi : x ((ρ₁ * ρ₂)⁻¹ i) = 0 := by
      rw [klein8_inv_apply hJc.1 hJc.2 h₁ h₂, if_pos hi, hx]
      simp [Pi.single_apply, hρi, hρij]
    have hxi : x i = 1 := by
      simp [hx, Pi.single_apply, Ne.symm hji]
    have hρ₂k : ρ₂ k ∉ J := by
      have := (mem_setStab.1 ((klein4_fourGroup hJc.2).stab h₂) k).2 hk
      exact Finset.mem_compl.1 this
    have hvk : x ((ρ₁ * ρ₂)⁻¹ k) = 0 := by
      rw [klein8_inv_apply hJc.1 hJc.2 h₁ h₂, if_neg hkJ, hx]
      have h1 : ρ₂ k ≠ i := fun h => hρ₂k (h ▸ hi)
      have h2 : ρ₂ k ≠ j := fun h => hρ₂k (h ▸ hj)
      simp [Pi.single_apply, h1, h2]
    have hxk : x k = 0 := by
      have h1 : k ≠ i := fun h => hkJ (h ▸ hi)
      have h2 : k ≠ j := fun h => hkJ (h ▸ hj)
      simp [hx, Pi.single_apply, h1, h2]
    rcases heq with h | h
    · have := h i
      rw [hvi, hxi] at this
      exact zero_ne_one this
    · have := h k
      rw [hvk, hxk, zero_add] at this
      exact zero_ne_one this

theorem exists_heart_not_qbar0 (hI : I.card = 4) (hIc : Iᶜ.card = 4) :
    ∃ v ∈ (heartToBar : altHeart n →+ permBar n).range, v ∉ qbar0 I := by
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  obtain ⟨a, ha⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨b, hb⟩ : Iᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hbI : b ∉ I := Finset.mem_compl.1 hb
  have hab : a ≠ b := fun h => hbI (h ▸ ha)
  set x : Fin n → ZMod 2 := Pi.single a 1 + Pi.single b 1 with hx
  have hsum : ∑ i, x i = 0 := by
    simp only [hx, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      if_true]
    decide
  refine ⟨(x : permBar n), ?_, ?_⟩
  · obtain ⟨u, hu⟩ := mk_mem_range_heartToBar hsum
    exact ⟨u, hu⟩
  · rw [mem_qbar0_mk hIe hIce]
    rintro ⟨h1, -⟩
    simp only [hx, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', if_pos ha,
      if_neg hbI, add_zero] at h1
    exact one_ne_zero h1

theorem barInd_mem_qbar0 (hI : I.card = 4) (hIc : Iᶜ.card = 4) : barInd I ∈ qbar0 I := by
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  rw [barInd, mem_qbar0_mk hIe hIce]
  constructor
  · have h1 : ∀ i ∈ I, indVec I i = 1 := fun i hi => if_pos hi
    rw [Finset.sum_congr rfl h1, Finset.sum_const, hI]
    decide
  · exact Finset.sum_eq_zero (fun i hi => (if_neg (Finset.mem_compl.1 hi) : indVec I i = 0))

end Qbar

section Count

theorem two_mul_card_le_of_lt {G : Type*} [AddGroup G] [Finite G] {H K : AddSubgroup G}
    (hHK : H ≤ K) (hne : H ≠ K) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨k, hk⟩ := AddSubgroup.card_dvd_of_le hHK
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact Nat.card_pos.ne' hk
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne (AddSubgroup.eq_of_le_of_card_ge hHK hk.le)
  rw [hk, mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

theorem card_common_fix_mul_le {α β : Type*} [DecidableEq α] (F : Finset α) (Y C : Finset β)
    (fix : α → β → Prop) [DecidableRel fix] (e : α) (heF : e ∈ F)
    (hC : ∀ y, y ∈ C ↔ y ∈ Y ∧ ∀ f ∈ F, fix f y)
    (hsmall : ∀ f ∈ F, f ≠ e → 2 * (Y.filter (fix f)).card ≤ Y.card)
    (hhalf : ∀ y ∈ Y, F.card ≤ 2 * (F.filter (fun f => fix f y)).card) :
    C.card * F.card ≤ Y.card := by
  classical
  set S : ℕ := ∑ f ∈ F, (Y.filter (fix f)).card with hS
  have hcomm : S = ∑ y ∈ Y, (F.filter (fun f => fix f y)).card := by
    rw [hS]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hup : 2 * S ≤ F.card * Y.card + Y.card := by
    rw [hS, Finset.mul_sum]
    calc ∑ f ∈ F, 2 * (Y.filter (fix f)).card
        ≤ ∑ f ∈ F, (Y.card + if f = e then Y.card else 0) := by
          refine Finset.sum_le_sum fun f hf => ?_
          by_cases hfe : f = e
          · rw [if_pos hfe]
            have := Finset.card_filter_le Y (fix f)
            omega
          · rw [if_neg hfe]
            have := hsmall f hf hfe
            omega
      _ = F.card * Y.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite_eq' F e,
            if_pos heF]
  have hCY : C = Y.filter (fun y => ∀ f ∈ F, fix f y) := by
    ext y
    rw [hC, Finset.mem_filter]
  have hlow : Y.card * F.card + C.card * F.card ≤ 2 * S := by
    rw [hcomm, Finset.mul_sum, hCY, Finset.card_filter, Finset.sum_mul, Finset.card_eq_sum_ones Y,
      Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y hy => ?_
    by_cases hall : ∀ f ∈ F, fix f y
    · rw [if_pos hall, one_mul]
      have : F.filter (fun f => fix f y) = F := Finset.filter_true_of_mem hall
      rw [this]
      omega
    · rw [if_neg hall, zero_mul, add_zero, one_mul]
      exact hhalf y hy
  have hY : Y.card * F.card = F.card * Y.card := Nat.mul_comm _ _
  omega

end Count

section Bound

variable {n : ℕ} {I : Finset (Fin n)}

theorem card_fix_qbar0_mul_le (hI : I.card = 4) (hIc : Iᶜ.card = 4) {F : Subgroup (Perm (Fin n))}
    (hF : F ≤ klein8 I) :
    Nat.card ↥(Comb.fixSub (F : Set (Perm (Fin n))) ⊓ qbar0 I) * Nat.card F ≤
      Nat.card ↥(qbar0 I) := by
  classical
  haveI : Fintype (permBar n) := Fintype.ofFinite _
  set Yf : Finset (permBar n) := Finset.univ.filter (· ∈ qbar0 I) with hYf
  set Ff : Finset (Perm (Fin n)) := Finset.univ.filter (· ∈ F) with hFf
  have hYc : Nat.card ↥(qbar0 I) = Yf.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hFc : Nat.card F = Ff.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set Cf : Finset (permBar n) :=
    Finset.univ.filter (· ∈ Comb.fixSub (F : Set (Perm (Fin n))) ⊓ qbar0 I) with hCf
  have hCc : Nat.card ↥(Comb.fixSub (F : Set (Perm (Fin n))) ⊓ qbar0 I) = Cf.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hYc, hFc, hCc]
  refine card_common_fix_mul_le Ff Yf Cf (fun σ v => barAct σ v = v) 1
    (by simp [hFf, F.one_mem]) (fun v => ?_) ?_ ?_
  · simp only [hCf, hYf, hFf, Finset.mem_filter, Finset.mem_univ, true_and, AddSubgroup.mem_inf,
      Comb.mem_fixSub, SetLike.mem_coe]
    tauto
  ·
    intro σ hσ hσ1
    have hσF : σ ∈ F := (Finset.mem_filter.1 hσ).2
    set H : AddSubgroup (permBar n) := Comb.fixSub ({σ} : Set (Perm (Fin n))) ⊓ qbar0 I with hH
    have hHc : Nat.card H = (Yf.filter (fun v => barAct σ v = v)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hYf, Finset.filter_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hH, AddSubgroup.mem_inf,
        Comb.mem_fixSub, Set.mem_singleton_iff, forall_eq]
      tauto
    have hHne : H ≠ qbar0 I := by
      obtain ⟨v, hv, hmv⟩ := exists_moved_qbar0 hI hIc (hF hσF) hσ1
      intro heq
      have : v ∈ H := heq ▸ hv
      exact hmv ((AddSubgroup.mem_inf.1 this).1 σ rfl)
    have h2 := two_mul_card_le_of_lt (inf_le_right : H ≤ qbar0 I) hHne
    rw [← hHc, ← hYc]
    exact h2
  ·
    intro v hv
    have hvq : v ∈ qbar0 I := (Finset.mem_filter.1 hv).2
    by_cases hall : ∀ σ ∈ Ff, barAct σ v = v
    · have : Ff.filter (fun σ => barAct σ v = v) = Ff := Finset.filter_true_of_mem hall
      rw [this]
      omega
    · push Not at hall
      obtain ⟨σ₀, hσ₀, hσ₀v⟩ := hall
      have hσ₀F : σ₀ ∈ F := (Finset.mem_filter.1 hσ₀).2
      have hmove : barAct σ₀ v = v + barInd I :=
        (barAct_qbar0 hI hIc (hF hσ₀F) hvq).resolve_left hσ₀v
      have hfixI : ∀ σ ∈ F, barAct σ (barInd I) = barInd I := fun σ hσ => by
        rw [barAct_barInd, (image_eq_iff_mem_setStab σ I).2 (klein8_le_setStab hI hIc (hF hσ))]
      have hinj : (Ff.filter (fun σ => ¬ barAct σ v = v)).card ≤
          (Ff.filter (fun σ => barAct σ v = v)).card := by
        refine Finset.card_le_card_of_injOn (fun σ => σ₀ * σ) (fun σ hσ => ?_)
          (fun σ _ τ _ h => mul_left_cancel h)
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hσ ⊢
        obtain ⟨hσF, hσv⟩ := hσ
        have hσF' : σ ∈ F := (Finset.mem_filter.1 hσF).2
        refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, F.mul_mem hσ₀F hσF'⟩, ?_⟩
        have hmσ : barAct σ v = v + barInd I :=
          (barAct_qbar0 hI hIc (hF hσF') hvq).resolve_left hσv
        rw [barAct_mul, hmσ, map_add, hmove, hfixI σ₀ hσ₀F, add_assoc, permBar_add_self,
          add_zero]
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := Ff) (fun σ => barAct σ v = v)
      omega

theorem card_mul_card_lt_add (hI : I.card = 4) (hIc : Iᶜ.card = 4) {F : Subgroup (Perm (Fin n))}
    (hFle : F ≤ klein8 I) (hF1 : F ≠ ⊥) {A Z : AddSubgroup (permBar n)}
    (hA : (heartToBar : altHeart n →+ permBar n).range ≤ A) (hZA : Z ≤ A)
    (hZ : ∀ z ∈ Z, ∀ σ ∈ F, barAct σ z = z) : Nat.card Z * Nat.card F < Nat.card A := by
  classical
  set U := (heartToBar : altHeart n →+ permBar n).range with hU
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  obtain ⟨⟨σ, hσF⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have hZU : Z ⊓ U ≤ Comb.fixSub (F : Set (Perm (Fin n))) ⊓ qbar0 I := by
    intro z hz
    obtain ⟨hzZ, hzU⟩ := AddSubgroup.mem_inf.1 hz
    refine AddSubgroup.mem_inf.2 ⟨fun τ hτ => hZ z hzZ τ hτ, ?_⟩
    by_contra hq
    exact barAct_ne_of_odd hI hIc (hFle hσF) hσ1' hzU hq (hZ z hzZ σ hσF)
  have h1 : Nat.card ↥(Z ⊓ U) * Nat.card F ≤ Nat.card ↥(qbar0 I) :=
    (Nat.mul_le_mul_right _ (AddSubgroup.card_le_of_le hZU)).trans
      (card_fix_qbar0_mul_le hI hIc hFle)
  have h2 : 2 * Nat.card ↥(qbar0 I) ≤ Nat.card U := by
    obtain ⟨v, hvU, hv⟩ := exists_heart_not_qbar0 hI hIc
    exact two_mul_card_le_of_lt (qbar0_le_heart hIe hIce) (fun h => hv (h ▸ hvU))
  have h3 : Nat.card U ≤ Nat.card A := AddSubgroup.card_le_of_le hA
  have hq0 : 0 < Nat.card ↥(qbar0 I) := Nat.card_pos
  by_cases hZsub : Z ≤ U
  · have : Z ⊓ U = Z := inf_eq_left.2 hZsub
    rw [this] at h1
    omega
  ·
    obtain ⟨z₀, hz₀Z, hz₀U⟩ := Set.not_subset.1 hZsub
    have hAU : U ≠ A := fun h => hz₀U (h ▸ hZA hz₀Z)
    have h4 : 2 * Nat.card U ≤ Nat.card A := two_mul_card_le_of_lt hA hAU
    have hmemU : ∀ w : permBar n, w ∈ U ↔ w ∈ Set.range (heartToBar (n := n)) := fun w =>
      AddMonoidHom.mem_range
    let f : ↥Z → ↥(Z ⊓ U) × Bool := fun z =>
      if hz : (z : permBar n) ∈ U then (⟨z, AddSubgroup.mem_inf.2 ⟨z.2, hz⟩⟩, false)
      else (⟨z + z₀, AddSubgroup.mem_inf.2 ⟨Z.add_mem z.2 hz₀Z, (hmemU _).2
        (add_mem_range_heartToBar (fun h => hz ((hmemU _).2 h))
          (fun h => hz₀U ((hmemU _).2 h)))⟩⟩, true)
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : (a : permBar n) ∈ U <;> by_cases hb : (b : permBar n) ∈ U <;>
        simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq, Subtype.mk.injEq,
          reduceCtorEq, and_false, and_true] at hab
      · exact Subtype.ext hab
      · exact Subtype.ext (add_right_cancel hab)
    have h5 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h5
    calc Nat.card Z * Nat.card F ≤ Nat.card ↥(Z ⊓ U) * 2 * Nat.card F :=
          Nat.mul_le_mul_right _ h5
      _ = 2 * (Nat.card ↥(Z ⊓ U) * Nat.card F) := by ring
      _ ≤ 2 * Nat.card ↥(qbar0 I) := Nat.mul_le_mul_left _ h1
      _ ≤ Nat.card U := h2
      _ < 2 * Nat.card U := by
          have : 0 < Nat.card U := Nat.card_pos
          omega
      _ ≤ Nat.card A := h4

theorem card_toAddSubgroup' {A : Type*} [AddGroup A] (S : Subgroup (Multiplicative A)) :
    Nat.card ↥(Subgroup.toAddSubgroup' S) = Nat.card S :=
  Nat.card_congr
    { toFun := fun a => ⟨Multiplicative.ofAdd (a : A), (Subgroup.mem_toAddSubgroup' S _).1 a.2⟩
      invFun := fun s => ⟨Multiplicative.toAdd (s : Multiplicative A),
        (Subgroup.mem_toAddSubgroup' S _).2 s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_mul_card_lt (hI : I.card = 4) (hIc : Iᶜ.card = 4) {F : Subgroup (Perm (Fin n))}
    (hFle : F ≤ klein8 I) (hF1 : F ≠ ⊥) {A Z : Subgroup (Multiplicative (permBar n))}
    (hA : ∀ u : altHeart n, Multiplicative.ofAdd (heartToBar u) ∈ A) (hZA : Z ≤ A)
    (hZ : ∀ z ∈ Z, ∀ σ ∈ F, barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z) :
    Nat.card Z * Nat.card F < Nat.card A := by
  have h := card_mul_card_lt_add hI hIc hFle hF1 (A := Subgroup.toAddSubgroup' A)
    (Z := Subgroup.toAddSubgroup' Z) (by
      rintro _ ⟨u, rfl⟩
      exact (Subgroup.mem_toAddSubgroup' A _).2 (hA u))
    (fun a ha => (Subgroup.mem_toAddSubgroup' A _).2 (hZA ((Subgroup.mem_toAddSubgroup' Z _).1 ha)))
    (fun a ha σ hσ => hZ _ ((Subgroup.mem_toAddSubgroup' Z _).1 ha) σ hσ)
  rwa [card_toAddSubgroup', card_toAddSubgroup'] at h

end Bound

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
