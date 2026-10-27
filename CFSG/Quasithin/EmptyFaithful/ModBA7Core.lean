module

public import CFSG.Quasithin.H13.VolIAltCoverSevenData
public import CFSG.Quasithin.EmptyFaithful.ModBA7Perm

public section

namespace CFSG.Quasithin

namespace ModB

open Equiv Equiv.Perm Subgroup CFSG.Quasithin CFSG.Quasithin.G6

private def iota6 : ↥(alternatingGroup (Fin 6)) →* ↥(alternatingGroup (Fin 7)) where
  toFun σ := ⟨Equiv.Perm.decomposeFin.symm (0, (σ : Perm (Fin 6))), by
    rw [Perm.mem_alternatingGroup, Equiv.Perm.decomposeFin.symm_sign]
    simp only [↓reduceIte, one_mul]
    exact Perm.mem_alternatingGroup.mp σ.2⟩
  map_one' := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem exists_iota6 (τ : ↥(alternatingGroup (Fin 7))) (hτ : (τ : Perm (Fin 7)) 0 = 0) :
    ∃ σ, iota6 σ = τ := by
  obtain ⟨p, e, hpe⟩ : ∃ (p : Fin 7) (e : Perm (Fin 6)),
      (τ : Perm (Fin 7)) = Equiv.Perm.decomposeFin.symm (p, e) :=
    ⟨(Equiv.Perm.decomposeFin (τ : Perm (Fin 7))).1, (Equiv.Perm.decomposeFin (τ : Perm (Fin 7))).2,
      by simp⟩
  have hp : p = 0 := by
    have := congrArg (fun f : Perm (Fin 7) => f 0) hpe
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at this
    rw [← this, hτ]
  subst hp
  have hsign : Perm.sign e = 1 := by
    have h := τ.2
    rw [hpe, Perm.mem_alternatingGroup, Equiv.Perm.decomposeFin.symm_sign] at h
    simpa using h
  exact ⟨⟨e, Perm.mem_alternatingGroup.mpr hsign⟩, Subtype.ext hpe.symm⟩

private theorem exists_alt_pair {a b a' b' : Fin 7} (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) a = a' ∧ (σ : Perm (Fin 7)) b = b' := by
  set τ₀ : Perm (Fin 7) := swap a a' with hτ₀
  have hτ₀a : τ₀ a = a' := swap_apply_left a a'
  have hτ₀b : τ₀ b ≠ a' := fun h => hab (τ₀.injective (h.trans hτ₀a.symm)).symm
  set τ : Perm (Fin 7) := swap (τ₀ b) b' * τ₀ with hτ
  have hτa : τ a = a' := by
    rw [hτ, Perm.mul_apply, hτ₀a]
    exact swap_apply_of_ne_of_ne hτ₀b.symm hab'
  have hτb : τ b = b' := by
    rw [hτ, Perm.mul_apply]
    exact swap_apply_left _ _
  have hex : ∀ x y : Fin 7, x ≠ y → ∃ c d : Fin 7, c ≠ d ∧ c ≠ x ∧ c ≠ y ∧ d ≠ x ∧ d ≠ y := by
    decide
  obtain ⟨c, d, hcd, hcx, hcy, hdx, hdy⟩ := hex a' b' hab'
  by_cases hs : Perm.sign τ = 1
  · exact ⟨⟨τ, Perm.mem_alternatingGroup.mpr hs⟩, hτa, hτb⟩
  · refine ⟨⟨swap c d * τ, ?_⟩, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hcd]
      have : Perm.sign τ = -1 := by
        rcases Int.units_eq_one_or (Perm.sign τ) with h | h
        · exact absurd h hs
        · exact h
      rw [this]
      rfl
    · show (swap c d * τ) a = a'
      rw [Perm.mul_apply, hτa]
      exact swap_apply_of_ne_of_ne hcx.symm hdx.symm
    · show (swap c d * τ) b = b'
      rw [Perm.mul_apply, hτb]
      exact swap_apply_of_ne_of_ne hcy.symm hdy.symm

private theorem exists_index_two_ge {W : Type*} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {N : Subgroup W} (hN : N ≠ ⊤) : ∃ H : Subgroup W, N ≤ H ∧ H.index = 2 := by
  obtain ⟨H, hHc, hNH⟩ := (eq_top_or_exists_le_coatom N).resolve_left hN
  refine ⟨H, hNH, ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, w ∉ H := by
    by_contra h
    push Not at h
    exact hHc.1 (eq_top_iff.2 fun w _ => h w)
  have hlt : H < H ⊔ Subgroup.zpowers w :=
    lt_of_le_of_ne le_sup_left fun h => hw (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have htop : H ⊔ Subgroup.zpowers w = ⊤ := hHc.2 _ hlt
  rw [Subgroup.index_eq_two_iff]
  refine ⟨w, fun b => ?_⟩
  have hb : b ∈ H ⊔ Subgroup.zpowers w := by rw [htop]; trivial
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hw2 : w ^ 2 = 1 := hW2 w
  have hk : w ^ k = 1 ∨ w ^ k = w := by
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, zpow_ofNat, hw2, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, zpow_ofNat, hw2, one_zpow, one_mul, zpow_one]
  rcases hk with hk | hk
  · rw [hk, mul_one]
    right
    refine ⟨hh, fun hhw => hw ?_⟩
    have := mul_mem (inv_mem hh) hhw
    simpa using this
  · rw [hk]
    left
    refine ⟨by rw [mul_assoc, ← sq, hw2, mul_one]; exact hh, fun hhw => hw ?_⟩
    have := mul_mem (inv_mem hh) hhw
    simpa using this

private def pv (a b : Fin 7) : PermMod 7 := Multiplicative.ofAdd (Pi.single a 1 + Pi.single b 1)

private theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

private theorem three_cycle_inv_apply {i j k : Fin 7} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p : Fin 7) :
    ((swap i j * swap j k)⁻¹ : Perm (Fin 7)) p =
      if p = i then k else if p = j then i else if p = k then j else p := by
  rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

private theorem exists_third : ∀ i j : Fin 7, ∃ k : Fin 7, k ≠ i ∧ k ≠ j := by decide

private theorem key7_core {i j k : Fin 7} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : PermMod 7)
    (hi : Multiplicative.toAdd v i = 1) (hj : Multiplicative.toAdd v j = 0) :
    ∃ a b : Fin 7, a ≠ b ∧ permAct 7 (swap i j * swap j k) v * v = pv a b := by
  have hk : Multiplicative.toAdd v k = 0 ∨ Multiplicative.toAdd v k = 1 := by
    generalize Multiplicative.toAdd v k = t
    revert t; decide
  rcases hk with hk | hk
  · refine ⟨i, j, hij, ?_⟩
    apply Multiplicative.toAdd.injective
    funext p
    simp only [toAdd_mul, Pi.add_apply, permAct_apply, three_cycle_inv_apply hij hjk hik, pv,
      toAdd_ofAdd, Pi.single_apply]
    by_cases hpi : p = i
    · subst hpi; simp [hij, hk, hi]
    · by_cases hpj : p = j
      · subst hpj; simp [hij.symm, hi, hj]
      · by_cases hpk : p = k
        · subst hpk; simp [hpi, hpj, hj, hk]
        · simp [hpi, hpj, hpk, zmod_two_add_self]
  · refine ⟨j, k, hjk, ?_⟩
    apply Multiplicative.toAdd.injective
    funext p
    simp only [toAdd_mul, Pi.add_apply, permAct_apply, three_cycle_inv_apply hij hjk hik, pv,
      toAdd_ofAdd, Pi.single_apply]
    by_cases hpi : p = i
    · subst hpi; simp [hij, hik, hk, hi, zmod_two_add_self]
    · by_cases hpj : p = j
      · subst hpj; simp [hij.symm, hi, hj, hjk]
      · by_cases hpk : p = k
        · subst hpk; simp [hpi, hpj, hj, hk]
        · simp [hpi, hpj, hpk, zmod_two_add_self]

private theorem lattice7 (R : Subgroup (PermMod 7))
    (hR : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v ∈ R, permAct 7 σ v ∈ R) :
    (∀ v ∈ R, v = 1 ∨ v = allOnes 7) ∨ ∃ a b : Fin 7, a ≠ b ∧ pv a b ∈ R := by
  by_cases h : ∀ v ∈ R, v = 1 ∨ v = allOnes 7
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨v, hvR, hv1, hvo⟩ := h
    have hzc : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd v i = 1 := by
      by_contra hcon
      push Not at hcon
      apply hv1
      apply Multiplicative.toAdd.injective
      funext i
      exact (hzc _).resolve_right (hcon i)
    obtain ⟨j, hj⟩ : ∃ j, Multiplicative.toAdd v j = 0 := by
      by_contra hcon
      push Not at hcon
      apply hvo
      apply Multiplicative.toAdd.injective
      funext i
      exact (hzc _).resolve_left (hcon i)
    have hij : i ≠ j := by
      rintro rfl
      rw [hi] at hj
      exact one_ne_zero hj
    obtain ⟨k, hki, hkj⟩ := exists_third i j
    have hσ : (swap i j * swap j k : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hij, Perm.sign_swap hkj.symm]
      decide
    obtain ⟨a, b, hab, hv⟩ := key7_core hij hkj.symm hki.symm v hi hj
    exact ⟨a, b, hab, hv ▸ R.mul_mem (hR _ hσ v hvR) hvR⟩

private theorem permAct_pv (σ : Perm (Fin 7)) (a b : Fin 7) : permAct 7 σ (pv a b) = pv (σ a) (σ b) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [permAct_apply, pv, toAdd_ofAdd, Pi.add_apply, Pi.single_apply]
  have h1 : (σ⁻¹ i = a) ↔ (i = σ a) := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  have h2 : (σ⁻¹ i = b) ↔ (i = σ b) := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  simp only [h1, h2]

private theorem eq_prod_pv7 : ∀ x : PermMod 7, ∑ i, Multiplicative.toAdd x i = 0 →
    x = pv 0 1 ^ (Multiplicative.toAdd x 1).val * pv 0 2 ^ (Multiplicative.toAdd x 2).val *
      pv 0 3 ^ (Multiplicative.toAdd x 3).val * pv 0 4 ^ (Multiplicative.toAdd x 4).val *
      pv 0 5 ^ (Multiplicative.toAdd x 5).val * pv 0 6 ^ (Multiplicative.toAdd x 6).val := by
  decide +kernel

private theorem core7_le_of_pv (R : Subgroup (PermMod 7))
    (hR : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v ∈ R, permAct 7 σ v ∈ R)
    {a b : Fin 7} (hab : a ≠ b) (h : pv a b ∈ R) : coreMod 7 ≤ R := by
  have hall : ∀ a' b' : Fin 7, a' ≠ b' → pv a' b' ∈ R := by
    intro a' b' hab'
    obtain ⟨σ, hσa, hσb⟩ := exists_alt_pair hab hab'
    have := hR σ σ.2 _ h
    rwa [permAct_pv, hσa, hσb] at this
  intro c hc
  rw [eq_prod_pv7 c (mem_coreMod.mp hc)]
  have h1 : ∀ j : Fin 7, j ≠ 0 → ∀ k : ℕ, pv 0 j ^ k ∈ R := fun j hj k =>
    R.pow_mem (hall 0 j (Ne.symm hj)) k
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h1 1 (by decide) _) (h1 2 (by decide) _))
    (h1 3 (by decide) _)) (h1 4 (by decide) _)) (h1 5 (by decide) _)) (h1 6 (by decide) _)

@[expose] def NoPerfectSixA6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → Nat.card W = 2 ^ 6 →
    ∀ ρ : ↥(alternatingGroup (Fin 6)) →* MulAut W, commV ρ.range ≠ ⊤

private theorem exists_alt_apply (j : Fin 7) :
    ∃ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 0 = j := by
  by_cases hj : j = 1
  · obtain ⟨σ, h0, -⟩ := exists_alt_pair (a := 0) (b := 1) (a' := j) (b' := 0) (by decide)
      (by rw [hj]; decide)
    exact ⟨σ, h0⟩
  · obtain ⟨σ, h0, -⟩ := exists_alt_pair (a := 0) (b := 1) (a' := j) (b' := 1) (by decide)
      (fun h => hj h)
    exact ⟨σ, h0⟩

theorem a7PerfectSixCore_of_noPerfectSixA6 (h6 : NoPerfectSixA6) : A7PerfectSixCore := by
  intro W _ _ hW2 hcard ρ hcomm
  classical
  have hne : commV (ρ.comp iota6).range ≠ ⊤ := h6 W hW2 hcard (ρ.comp iota6)
  obtain ⟨H₀, hNH, hidx⟩ := exists_index_two_ge hW2 hne
  have hstab : ∀ τ : ↥(alternatingGroup (Fin 7)), (τ : Perm (Fin 7)) 0 = 0 → ∀ w : W,
      ρ τ w ∈ H₀ ↔ w ∈ H₀ := by
    intro τ hτ w
    obtain ⟨σ, rfl⟩ := exists_iota6 τ hτ
    have hmem : (ρ (iota6 σ)) w * w⁻¹ ∈ commV (ρ.comp iota6).range :=
      Subgroup.subset_closure ⟨ρ (iota6 σ), ⟨σ, rfl⟩, w, rfl⟩
    have h1 := hNH hmem
    constructor
    · intro h
      have := mul_mem (inv_mem h1) h
      simpa using this
    · intro h
      have := mul_mem h1 h
      simpa using this
  choose s hs using exists_alt_apply
  let f : Fin 7 → Subgroup W := fun j => H₀.comap ((ρ (s j)⁻¹ : MulAut W) : W →* W)
  have hfmem : ∀ j w, w ∈ f j ↔ ρ (s j)⁻¹ w ∈ H₀ := fun j w => Iff.rfl
  have hf : ∀ (σ : ↥(alternatingGroup (Fin 7))) (j : Fin 7) (w : W),
      w ∈ f ((σ : Perm (Fin 7)) j) ↔ ρ σ⁻¹ w ∈ f j := by
    intro σ j w
    rw [hfmem, hfmem]
    set g : ↥(alternatingGroup (Fin 7)) := (s ((σ : Perm (Fin 7)) j))⁻¹ * (σ * s j) with hg
    have hg0 : (g : Perm (Fin 7)) 0 = 0 := by
      have h1 := hs ((σ : Perm (Fin 7)) j)
      have h2 := hs j
      simp only [hg, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
      rw [h2]
      exact Perm.inv_eq_iff_eq.mpr h1.symm
    have hgi : (g⁻¹ : ↥(alternatingGroup (Fin 7))) = (s j)⁻¹ * σ⁻¹ * s ((σ : Perm (Fin 7)) j) := by
      simp [hg, mul_assoc]
    have hgi0 : ((g⁻¹ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 0 = 0 := by
      rw [Subgroup.coe_inv, Perm.inv_eq_iff_eq]; exact hg0.symm
    have key := hstab g⁻¹ hgi0 (ρ (s ((σ : Perm (Fin 7)) j))⁻¹ w)
    rw [hgi] at key
    have e : ρ ((s j)⁻¹ * σ⁻¹ * s ((σ : Perm (Fin 7)) j)) (ρ (s ((σ : Perm (Fin 7)) j))⁻¹ w) =
        ρ (s j)⁻¹ (ρ σ⁻¹ w) := by
      simp [map_mul, map_inv, MulAut.mul_apply]
    rw [e] at key
    exact key.symm
  have hfidx : ∀ j, (f j).index = 2 := by
    intro j
    show (H₀.comap ((ρ (s j)⁻¹ : MulAut W) : W →* W)).index = 2
    rw [Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _), hidx]
  let Φ₀ : W →* PermMod 7 :=
    { toFun := fun w => Multiplicative.ofAdd (fun j => if w ∈ f j then (0 : ZMod 2) else 1)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext j
        simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        funext j
        have key := Subgroup.mul_mem_iff_of_index_two (hfidx j) (a := a) (b := b)
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        by_cases ha : a ∈ f j <;> by_cases hb : b ∈ f j <;> simp [ha, hb, key, h11] }
  have hΦ : ∀ (w : W) (j : Fin 7),
      Multiplicative.toAdd (Φ₀ w) j = if w ∈ f j then (0 : ZMod 2) else 1 := fun w j => rfl
  have hequiv : ∀ (σ : ↥(alternatingGroup (Fin 7))) (w : W),
      Φ₀ (ρ σ w) = permAct 7 (σ : Perm (Fin 7)) (Φ₀ w) := by
    intro σ w
    apply Multiplicative.toAdd.injective
    funext j
    rw [permAct_apply, hΦ, hΦ]
    have h := hf σ⁻¹ j w
    rw [inv_inv] at h
    have h' : ρ σ w ∈ f j ↔ w ∈ f (((σ : Perm (Fin 7))⁻¹) j) := by
      rw [Subgroup.coe_inv] at h
      exact h.symm
    simp only [h']
  have hinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v ∈ Φ₀.range, permAct 7 σ v ∈ Φ₀.range := by
    rintro σ hσ _ ⟨w, rfl⟩
    exact ⟨ρ ⟨σ, hσ⟩ w, by rw [hequiv ⟨σ, hσ⟩ w]⟩
  rcases lattice7 Φ₀.range hinv with hA | ⟨a, b, hab, hpv⟩
  ·
    exfalso
    have hsame : ∀ w j, w ∈ f j ↔ w ∈ f 0 := by
      intro w j
      rcases hA (Φ₀ w) ⟨w, rfl⟩ with h | h
      · have h0 := congrArg (fun x : PermMod 7 => Multiplicative.toAdd x j) h
        have h1 := congrArg (fun x : PermMod 7 => Multiplicative.toAdd x 0) h
        simp only [hΦ, toAdd_one, Pi.zero_apply] at h0 h1
        constructor
        · intro _; by_contra hn; simp [hn] at h1
        · intro _; by_contra hn; simp [hn] at h0
      · have h0 := congrArg (fun x : PermMod 7 => Multiplicative.toAdd x j) h
        have h1 := congrArg (fun x : PermMod 7 => Multiplicative.toAdd x 0) h
        simp only [hΦ, allOnes, toAdd_ofAdd] at h0 h1
        constructor
        · intro hh; simp [hh] at h0
        · intro hh; simp [hh] at h1
    have hf0 : ∀ w, w ∈ f 0 ↔ w ∈ H₀ := by
      intro w
      rw [hfmem]
      exact hstab (s 0)⁻¹ (by rw [Subgroup.coe_inv, Perm.inv_eq_iff_eq]; exact (hs 0).symm) w
    have hH₀inv : ∀ (σ : ↥(alternatingGroup (Fin 7))) (w : W), ρ σ w ∈ H₀ ↔ w ∈ H₀ := by
      intro σ w
      have h := hf σ⁻¹ 0 w
      rw [inv_inv] at h
      rw [← hf0, ← hf0, ← h, hsame w (((σ⁻¹ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 0)]
    have hle : commV ρ.range ≤ H₀ := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨x, ⟨σ, rfl⟩, v, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
      exact hH₀inv σ v
    rw [hcomm] at hle
    have htop : H₀ = ⊤ := eq_top_iff.mpr hle
    rw [htop, Subgroup.index_top] at hidx
    omega
  · have hle := core7_le_of_pv Φ₀.range hinv hab hpv
    have hc64 : Nat.card (coreMod 7) = 64 := H13.VolI.card_coreMod_seven
    have hrange_le : Nat.card Φ₀.range ≤ Nat.card W :=
      Nat.card_le_card_of_surjective _ Φ₀.rangeRestrict_surjective
    have hge : Nat.card (coreMod 7) ≤ Nat.card Φ₀.range := Subgroup.card_le_of_le hle
    have hr64 : Nat.card Φ₀.range = 64 := by
      rw [hcard] at hrange_le
      omega
    have heq : coreMod 7 = Φ₀.range :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc64, hr64])
    have hker : Nat.card Φ₀.ker = 1 := by
      have := Subgroup.card_ker_mul_card_range Φ₀
      rw [hr64, hcard] at this
      omega
    have hinj : Function.Injective Φ₀ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact Subgroup.eq_bot_of_card_eq _ hker
    have hmemc : ∀ w, Φ₀ w ∈ coreMod 7 := fun w => by rw [heq]; exact ⟨w, rfl⟩
    let Φ' : W →* ↥(coreMod 7) := Φ₀.codRestrict _ hmemc
    have hbij : Function.Bijective Φ' := by
      refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun c => ?_⟩
      obtain ⟨w, hw⟩ := (heq ▸ c.2 : (c : PermMod 7) ∈ Φ₀.range)
      exact ⟨w, Subtype.ext hw⟩
    exact ⟨MulEquiv.ofBijective Φ' hbij, fun σ w => Subtype.ext (hequiv σ w)⟩

end ModB

theorem input14610PermFixedA7_of_noPerfectSixA6 (h6 : ModB.NoPerfectSixA6) : Input14610PermFixedA7 :=
  input14610PermFixedA7_of_core (ModB.a7PerfectSixCore_of_noPerfectSixA6 h6)

end CFSG.Quasithin
