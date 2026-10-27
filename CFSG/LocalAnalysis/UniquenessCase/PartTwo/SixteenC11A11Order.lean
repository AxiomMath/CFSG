module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Fin
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv

theorem s16c11_a11_relIndex_stabilizer (H : Subgroup (Perm (Fin 11))) (p : Fin 11) :
    (H ⊓ MulAction.stabilizer (Perm (Fin 11)) p).relIndex H =
      {q : Fin 11 | ∃ h ∈ H, h p = q}.ncard := by
  have horb : {q : Fin 11 | ∃ h ∈ H, h p = q} = MulAction.orbit ↥H p := by
    ext q
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h.1, h.2, rfl⟩
  change ((H ⊓ MulAction.stabilizer (Perm (Fin 11)) p).subgroupOf H).index =
    {q : Fin 11 | ∃ h ∈ H, h p = q}.ncard
  rw [horb, Subgroup.inf_subgroupOf_left (MulAction.stabilizer (Perm (Fin 11)) p) H,
    MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]

theorem s16c11_a11_card_orbit_mul (H : Subgroup (Perm (Fin 11))) (p : Fin 11) :
    Nat.card ↥H = {q : Fin 11 | ∃ h ∈ H, h p = q}.ncard *
      Nat.card ↥(H ⊓ MulAction.stabilizer (Perm (Fin 11)) p) := by
  have h := Subgroup.relIndex_mul_card (H := H ⊓ MulAction.stabilizer (Perm (Fin 11)) p)
    (K := H)
  rw [show (H ⊓ MulAction.stabilizer (Perm (Fin 11)) p) ⊓ H =
      H ⊓ MulAction.stabilizer (Perm (Fin 11)) p from inf_eq_left.mpr inf_le_left] at h
  rw [s16c11_a11_relIndex_stabilizer H p] at h
  exact h.symm

private lemma s16c11a11_order_ncard_set3 : ({8, 9, 10} : Set (Fin 11)).ncard = 3 := by
  rw [show ({8, 9, 10} : Set (Fin 11)) = ↑({8, 9, 10} : Finset (Fin 11)) by
    ext x; simp]
  rw [Set.ncard_coe_finset]
  decide

private lemma s16c11a11_order_eq_one_or_swap {σ : Perm (Fin 11)}
    (hfix : ∀ x : Fin 11, (x : ℕ) < 8 → σ x = x)
    (hpres_set : ∀ i : Fin 11, ((σ i : Fin 11) : ℕ) < 8 ↔ (i : ℕ) < 8)
    (h10 : σ 10 = 10) : σ = 1 ∨ σ = swap (8 : Fin 11) 9 := by
  have h8 : σ 8 = 8 ∨ σ 8 = 9 := by
    have hge : ¬ (((σ 8 : Fin 11) : ℕ) < 8) := (hpres_set 8).not.2 (by decide)
    have hlt : (((σ 8 : Fin 11) : ℕ)) < 11 := (σ 8).isLt
    have hne : σ 8 ≠ 10 := by
      intro h
      have : σ 8 = σ 10 := by rw [h, h10]
      exact absurd (Equiv.injective σ this) (by decide)
    have hne' : ((σ 8 : Fin 11) : ℕ) ≠ 10 := fun hh => hne (Fin.ext hh)
    have : ((σ 8 : Fin 11) : ℕ) = 8 ∨ ((σ 8 : Fin 11) : ℕ) = 9 := by omega
    rcases this with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases h8 with h8 | h8
  · have h9 : σ 9 = 9 := by
      have hge : ¬ (((σ 9 : Fin 11) : ℕ) < 8) := (hpres_set 9).not.2 (by decide)
      have hlt : (((σ 9 : Fin 11) : ℕ)) < 11 := (σ 9).isLt
      have hne8 : σ 9 ≠ 8 := by
        intro h
        have : σ 9 = σ 8 := by rw [h, h8]
        exact absurd (Equiv.injective σ this) (by decide)
      have hne10 : σ 9 ≠ 10 := by
        intro h
        have : σ 9 = σ 10 := by rw [h, h10]
        exact absurd (Equiv.injective σ this) (by decide)
      have hne8' : ((σ 9 : Fin 11) : ℕ) ≠ 8 := fun hh => hne8 (Fin.ext hh)
      have hne10' : ((σ 9 : Fin 11) : ℕ) ≠ 10 := fun hh => hne10 (Fin.ext hh)
      have : ((σ 9 : Fin 11) : ℕ) = 8 ∨ ((σ 9 : Fin 11) : ℕ) = 9 := by omega
      rcases this with h | h
      · exact absurd (Fin.ext h) hne8
      · exact Fin.ext h
    left
    apply Equiv.ext
    intro x
    by_cases hx : (x : ℕ) < 8
    · simpa using hfix x hx
    · have hx' : (x : ℕ) = 8 ∨ (x : ℕ) = 9 ∨ (x : ℕ) = 10 := by
        have := x.isLt; omega
      rcases hx' with h | h | h
      · have hx : x = (8 : Fin 11) := Fin.ext (by simpa using h)
        rw [hx]; simpa using h8
      · have hx : x = (9 : Fin 11) := Fin.ext (by simpa using h)
        rw [hx]; simpa using h9
      · have hx : x = (10 : Fin 11) := Fin.ext (by simpa using h)
        rw [hx]; simpa using h10
  · have h9 : σ 9 = 8 := by
      have hge : ¬ (((σ 9 : Fin 11) : ℕ) < 8) := (hpres_set 9).not.2 (by decide)
      have hlt : (((σ 9 : Fin 11) : ℕ)) < 11 := (σ 9).isLt
      have hne9 : σ 9 ≠ 9 := by
        intro h
        have : σ 9 = σ 8 := by rw [h, h8]
        exact absurd (Equiv.injective σ this) (by decide)
      have hne10 : σ 9 ≠ 10 := by
        intro h
        have : σ 9 = σ 10 := by rw [h, h10]
        exact absurd (Equiv.injective σ this) (by decide)
      have hne9' : ((σ 9 : Fin 11) : ℕ) ≠ 9 := fun hh => hne9 (Fin.ext hh)
      have hne10' : ((σ 9 : Fin 11) : ℕ) ≠ 10 := fun hh => hne10 (Fin.ext hh)
      have : ((σ 9 : Fin 11) : ℕ) = 8 ∨ ((σ 9 : Fin 11) : ℕ) = 9 := by omega
      rcases this with h | h
      · exact Fin.ext h
      · exact absurd (Fin.ext h) hne9
    right
    apply Equiv.ext
    intro x
    by_cases hx : (x : ℕ) < 8
    · have hx8 : x ≠ (8 : Fin 11) := by
        intro h; rw [h] at hx; norm_num at hx
      have hx9 : x ≠ (9 : Fin 11) := by
        intro h; rw [h] at hx; norm_num at hx
      rw [hfix x hx, Equiv.swap_apply_of_ne_of_ne hx8 hx9]
    · have hx' : (x : ℕ) = 8 ∨ (x : ℕ) = 9 ∨ (x : ℕ) = 10 := by
        have := x.isLt; omega
      rcases hx' with h | h | h
      · have hx : x = (8 : Fin 11) := Fin.ext (by simpa using h)
        rw [hx, h8, Equiv.swap_apply_left]
      · have hx : x = (9 : Fin 11) := Fin.ext (by simpa using h)
        rw [hx, h9, Equiv.swap_apply_right]
      · have hx : x = (10 : Fin 11) := Fin.ext (by simpa using h)
        rw [hx, h10]
        have hx8 : (10 : Fin 11) ≠ 8 := by decide
        have hx9 : (10 : Fin 11) ≠ 9 := by decide
        rw [Equiv.swap_apply_of_ne_of_ne hx8 hx9]

private def s16c11a11_order_resT : ↥s16c11A11T →* Perm (Fin 8) :=
  s16c11A11Res.comp (Subgroup.inclusion (s16c11A11_T_le_Y.trans s16c11A11_Y_le_pres))

private lemma s16c11a11_order_resT_apply (t : ↥s16c11A11T) (x : Fin 8) :
    ((s16c11a11_order_resT t x : Fin 8) : ℕ) =
      ((t.1 (Fin.castLE (by norm_num) x) : Fin 11) : ℕ) :=
  s16c11A11_res_apply _ x

private lemma s16c11a11_order_resT_eq_one {t : ↥s16c11A11T}
    (h : s16c11a11_order_resT t = 1) : t.1 = 1 := by
  have hres : s16c11A11Res
      (Subgroup.inclusion (s16c11A11_T_le_Y.trans s16c11A11_Y_le_pres) t) = 1 := by
    simpa only [s16c11a11_order_resT, MonoidHom.comp_apply] using h
  have htY : t.1 ∈ s16c11A11Y := s16c11A11_T_le_Y t.2
  have hPres : t.1 ∈ s16c11A11Pres := s16c11A11_Y_le_pres htY
  have hT := s16c11A11_mem_T_iff.1 t.2
  have h10 : t.1 10 = 10 := hT.2
  have hsign : Perm.sign t.1 = 1 := hT.1.2
  have hfix : ∀ x : Fin 11, (x : ℕ) < 8 → t.1 x = x := by
    intro x hx
    exact s16c11_a11_res_eq_one
      (σ := Subgroup.inclusion (s16c11A11_T_le_Y.trans s16c11A11_Y_le_pres) t) hres x hx
  have hpres_set : ∀ i : Fin 11, ((t.1 i : Fin 11) : ℕ) < 8 ↔ (i : ℕ) < 8 :=
    s16c11A11_mem_pres_iff.1 hPres
  rcases s16c11a11_order_eq_one_or_swap hfix hpres_set h10 with h1 | hswap
  · exact h1
  · exfalso
    have : Perm.sign t.1 = -1 := by
      rw [hswap, Perm.sign_swap (by decide)]
    rw [hsign] at this
    exact absurd this (by decide)

private def s16c11a11_order_phi (t : ↥s16c11A11T) :
    {w : Perm (Fin 8) // S16C11A11Blk8 w} :=
  ⟨s16c11a11_order_resT t, by
    have htY : t.1 ∈ s16c11A11Y := s16c11A11_T_le_Y t.2
    have hBlk : S16C11A11Blk t.1 := (s16c11A11_mem_Y_iff.1 htY).1.2
    simpa only [s16c11a11_order_resT, MonoidHom.comp_apply] using
      (s16c11_a11_blk_iff_res
        (Subgroup.inclusion (s16c11A11_T_le_Y.trans s16c11A11_Y_le_pres) t)).1 hBlk⟩

private lemma s16c11a11_order_phi_injective : Function.Injective s16c11a11_order_phi := by
  intro s t hst
  have hres : s16c11a11_order_resT s = s16c11a11_order_resT t := by
    have := congrArg Subtype.val hst
    simpa [s16c11a11_order_phi] using this
  have hρres : s16c11a11_order_resT (s⁻¹ * t) = 1 := by
    rw [map_mul, map_inv, hres, inv_mul_cancel]
  have hρ1 : s⁻¹ * t = 1 := Subtype.ext (s16c11a11_order_resT_eq_one hρres)
  exact eq_of_inv_mul_eq_one hρ1

private lemma s16c11a11_order_phi_surjective : Function.Surjective s16c11a11_order_phi := by
  intro w
  obtain ⟨σ₀, hLow, hRes⟩ := s16c11_a11_exists_ext w.1
  have hBlk : S16C11A11Blk σ₀.1 :=
    (s16c11_a11_blk_iff_res σ₀).2 (by rw [hRes]; exact w.2)
  have h8 : σ₀.1 8 = 8 := by
    have h := hLow.1.1
    change σ₀.1 ∈ MulAction.stabilizer (Perm (Fin 11)) (8 : Fin 11) at h
    rwa [MulAction.mem_stabilizer_iff, Perm.smul_def] at h
  have h9 : σ₀.1 9 = 9 := by
    have h := hLow.1.2
    change σ₀.1 ∈ MulAction.stabilizer (Perm (Fin 11)) (9 : Fin 11) at h
    rwa [MulAction.mem_stabilizer_iff, Perm.smul_def] at h
  have h10 : σ₀.1 10 = 10 := by
    have h := hLow.2
    change σ₀.1 ∈ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11) at h
    rwa [MulAction.mem_stabilizer_iff, Perm.smul_def] at h
  by_cases hsign : Perm.sign σ₀.1 = 1
  · have hT : σ₀.1 ∈ s16c11A11T :=
      s16c11A11_mem_T_iff.2 ⟨⟨⟨σ₀.2, hBlk⟩, hsign⟩, h10⟩
    let t : ↥s16c11A11T := ⟨σ₀.1, hT⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change s16c11a11_order_resT t = w.1
    rw [← hRes]
    apply Equiv.ext
    intro x
    apply Fin.ext
    rw [s16c11a11_order_resT_apply]
    have ht1 : t.1 = σ₀.1 := rfl
    rw [ht1, s16c11A11_res_apply]
  · have hsign' : Perm.sign σ₀.1 = -1 := by
      rcases Int.units_eq_one_or (Perm.sign σ₀.1) with h | h
      · exact absurd h hsign
      · exact h
    have hPresτ : swap (8 : Fin 11) 9 ∈ s16c11A11Pres :=
      s16c11A11_mem_pres_iff.2 (by decide)
    have hPres₁ : σ₀.1 * swap (8 : Fin 11) 9 ∈ s16c11A11Pres :=
      s16c11A11Pres.mul_mem σ₀.2 hPresτ
    have hBlk₁ : S16C11A11Blk (σ₀.1 * swap (8 : Fin 11) 9) := by
      intro i j hi hj
      have hi8 : swap (8 : Fin 11) 9 i = i :=
        Equiv.swap_apply_of_ne_of_ne
          (by intro h; rw [h] at hi; norm_num at hi)
          (by intro h; rw [h] at hi; norm_num at hi)
      have hj8 : swap (8 : Fin 11) 9 j = j :=
        Equiv.swap_apply_of_ne_of_ne
          (by intro h; rw [h] at hj; norm_num at hj)
          (by intro h; rw [h] at hj; norm_num at hj)
      simp only [Perm.mul_apply, hi8, hj8]
      exact hBlk i j hi hj
    have hsign₁ : Perm.sign (σ₀.1 * swap (8 : Fin 11) 9) = 1 := by
      rw [Perm.sign_mul, hsign', Perm.sign_swap (by decide)]
      decide
    have h10₁ : (σ₀.1 * swap (8 : Fin 11) 9) 10 = 10 := by
      rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), h10]
    have hT : σ₀.1 * swap (8 : Fin 11) 9 ∈ s16c11A11T :=
      s16c11A11_mem_T_iff.2 ⟨⟨⟨hPres₁, hBlk₁⟩, hsign₁⟩, h10₁⟩
    let t : ↥s16c11A11T := ⟨σ₀.1 * swap (8 : Fin 11) 9, hT⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change s16c11a11_order_resT t = w.1
    rw [← hRes]
    apply Equiv.ext
    intro x
    apply Fin.ext
    rw [s16c11a11_order_resT_apply]
    have ht1 : t.1 = σ₀.1 * swap (8 : Fin 11) 9 := rfl
    rw [ht1, Perm.mul_apply]
    have hx8 : Fin.castLE (by norm_num) x ≠ (8 : Fin 11) := by
      intro h
      have := congrArg Fin.val h
      simp at this
      have := x.isLt
      omega
    have hx9 : Fin.castLE (by norm_num) x ≠ (9 : Fin 11) := by
      intro h
      have := congrArg Fin.val h
      simp at this
      have := x.isLt
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hx8 hx9, s16c11A11_res_apply]

theorem s16c11_a11_card_T : Nat.card ↥s16c11A11T = 128 := by
  have hbij : Function.Bijective s16c11a11_order_phi :=
    ⟨s16c11a11_order_phi_injective, s16c11a11_order_phi_surjective⟩
  have hcard : Nat.card ↥s16c11A11T = Nat.card {w : Perm (Fin 8) // S16C11A11Blk8 w} :=
    Nat.card_congr (Equiv.ofBijective s16c11a11_order_phi hbij)
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact s16c11_a11_card_blk8

theorem s16c11_a11_T_relIndex_Y : s16c11A11T.relIndex s16c11A11Y = 3 := by
  change (s16c11A11Y ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)).relIndex
    s16c11A11Y = 3
  rw [s16c11_a11_relIndex_stabilizer s16c11A11Y (10 : Fin 11)]
  have horb : {q : Fin 11 | ∃ h ∈ s16c11A11Y, h 10 = q} = ({8, 9, 10} : Set (Fin 11)) := by
    ext q
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hPres : h ∈ s16c11A11Pres := s16c11A11_Y_le_pres hh
      have hpres_set := s16c11A11_mem_pres_iff.1 hPres
      have hge : ¬ (((h 10 : Fin 11) : ℕ) < 8) := (hpres_set 10).not.2 (by decide)
      have hlt : (((h 10 : Fin 11) : ℕ)) < 11 := (h 10).isLt
      have : ((h 10 : Fin 11) : ℕ) = 8 ∨ ((h 10 : Fin 11) : ℕ) = 9 ∨
          ((h 10 : Fin 11) : ℕ) = 10 := by omega
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases this with h' | h' | h'
      · left; exact Fin.ext h'
      · right; left; exact Fin.ext h'
      · right; right; exact Fin.ext h'
    · intro hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨s16c11A11c, s16c11A11_c_mem_Y, by decide⟩
      · exact ⟨s16c11A11c * s16c11A11c,
          s16c11A11Y.mul_mem s16c11A11_c_mem_Y s16c11A11_c_mem_Y, by decide⟩
      · exact ⟨1, s16c11A11Y.one_mem, by decide⟩
  rw [horb, s16c11a11_order_ncard_set3]

theorem s16c11_a11_card_K : Nat.card ↥s16c11A11K = 64 := by
  have hK : s16c11A11K =
      s16c11A11T ⊓ MulAction.stabilizer (Perm (Fin 11)) (8 : Fin 11) := by
    ext σ
    constructor
    · intro h
      refine ⟨s16c11A11_K_le_T h, ?_⟩
      change σ ∈ MulAction.stabilizer (Perm (Fin 11)) (8 : Fin 11)
      exact MulAction.mem_stabilizer_iff.2 (by
        simpa only [Perm.smul_def] using (s16c11A11_mem_K_iff.1 h).2.1.1)
    · intro h
      have hT : σ ∈ s16c11A11T := h.1
      have h8 : σ 8 = 8 := by
        have hh := h.2
        change σ ∈ MulAction.stabilizer (Perm (Fin 11)) (8 : Fin 11) at hh
        rwa [MulAction.mem_stabilizer_iff, Perm.smul_def] at hh
      have hY : σ ∈ s16c11A11Y := s16c11A11_T_le_Y hT
      have hPres : σ ∈ s16c11A11Pres := s16c11A11_Y_le_pres hY
      have h10 : σ 10 = 10 := (s16c11A11_mem_T_iff.1 hT).2
      have h9 : σ 9 = 9 := by
        have hpres_set := s16c11A11_mem_pres_iff.1 hPres
        have hge : ¬ (((σ 9 : Fin 11) : ℕ) < 8) := (hpres_set 9).not.2 (by decide)
        have hlt : (((σ 9 : Fin 11) : ℕ)) < 11 := (σ 9).isLt
        have hne8 : σ 9 ≠ 8 := by
          intro hh
          have : σ 9 = σ 8 := by rw [hh, h8]
          exact absurd (Equiv.injective σ this) (by decide)
        have hne10 : σ 9 ≠ 10 := by
          intro hh
          have : σ 9 = σ 10 := by rw [hh, h10]
          exact absurd (Equiv.injective σ this) (by decide)
        have hne8' : ((σ 9 : Fin 11) : ℕ) ≠ 8 := fun hh => hne8 (Fin.ext hh)
        have hne10' : ((σ 9 : Fin 11) : ℕ) ≠ 10 := fun hh => hne10 (Fin.ext hh)
        have : ((σ 9 : Fin 11) : ℕ) = 8 ∨ ((σ 9 : Fin 11) : ℕ) = 9 := by omega
        rcases this with hh | hh
        · exact absurd (Fin.ext hh) hne8
        · exact Fin.ext hh
      exact s16c11A11_mem_K_iff.2 ⟨s16c11A11_mem_Y_iff.1 hY, ⟨⟨h8, h9⟩, h10⟩⟩
  rw [hK]
  have hcard := s16c11_a11_card_orbit_mul s16c11A11T (8 : Fin 11)
  have horb : {q : Fin 11 | ∃ h ∈ s16c11A11T, h 8 = q} = ({8, 9} : Set (Fin 11)) := by
    ext q
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hT' := s16c11A11_mem_T_iff.1 hh
      have h10' : h 10 = 10 := hT'.2
      have hPres' : h ∈ s16c11A11Pres := s16c11A11_Y_le_pres (s16c11A11_T_le_Y hh)
      have hpres_set := s16c11A11_mem_pres_iff.1 hPres'
      have hge : ¬ (((h 8 : Fin 11) : ℕ) < 8) := (hpres_set 8).not.2 (by decide)
      have hlt : (((h 8 : Fin 11) : ℕ)) < 11 := (h 8).isLt
      have hne : h 8 ≠ 10 := by
        intro hh'
        have : h 8 = h 10 := by rw [hh', h10']
        exact absurd (Equiv.injective h this) (by decide)
      have hne' : ((h 8 : Fin 11) : ℕ) ≠ 10 := fun hh' => hne (Fin.ext hh')
      have : ((h 8 : Fin 11) : ℕ) = 8 ∨ ((h 8 : Fin 11) : ℕ) = 9 := by omega
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases this with h' | h'
      · left; exact Fin.ext h'
      · right; exact Fin.ext h'
    · intro hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact ⟨1, s16c11A11T.one_mem, by decide⟩
      · exact ⟨s16c11A11u, s16c11A11_u_mem_T, by decide⟩
  rw [s16c11_a11_card_T, horb, Set.ncard_pair (by decide : (8 : Fin 11) ≠ 9)] at hcard
  omega

theorem s16c11_a11_card_alt : Nat.card ↥(alternatingGroup (Fin 11)) = 128 * 155925 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem s16c11_a11_T_isPGroup :
    IsPGroup 2 ↥(s16c11A11T.subgroupOf (alternatingGroup (Fin 11))) := by
  apply IsPGroup.of_card (n := 7)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe s16c11A11_T_le_alt).toEquiv,
    s16c11_a11_card_T]
  norm_num

theorem s16c11_a11_T_index_odd :
    ¬ 2 ∣ (s16c11A11T.subgroupOf (alternatingGroup (Fin 11))).index := by
  have hcard : Nat.card ↥(s16c11A11T.subgroupOf (alternatingGroup (Fin 11))) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe s16c11A11_T_le_alt).toEquiv,
      s16c11_a11_card_T]
  have hmul := Subgroup.card_mul_index
    (s16c11A11T.subgroupOf (alternatingGroup (Fin 11)))
  rw [hcard, s16c11_a11_card_alt] at hmul
  have hidx : (s16c11A11T.subgroupOf (alternatingGroup (Fin 11))).index = 155925 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 128) hmul
  rw [hidx]
  decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
