module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23AutH
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Zeta
public import CFSG.Quasithin.Vol2.Ch5Sec2M23MX

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.M23Heptad CFSG.Quasithin.Asc94 CFSG.Open
  CFSG.QuasithinUnique CFSG.M23Norm3 CFSG.EvenSmallLie.UnitarySix.MathieuExt
open CFSG.QuasithinUnique.L246.C123 (A7)
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_even_fix3456 (τ : Equiv.Perm (Fin 7)) :
    ∃ σ : A7, ∀ i : Fin 7, 3 ≤ i.val → (σ : Equiv.Perm (Fin 7)) (τ i) = i := by
  by_cases hs : Equiv.Perm.sign τ = 1
  · refine ⟨⟨τ⁻¹, ?_⟩, fun i _ => by simp⟩
    rw [Equiv.Perm.mem_alternatingGroup, map_inv, hs, inv_one]
  · have hs' : Equiv.Perm.sign τ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
      · exact absurd h hs
      · exact h
    refine ⟨⟨Equiv.swap 0 1 * τ⁻¹, ?_⟩, fun i hi => ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs', Equiv.Perm.sign_swap (by decide)]
      decide
    · change Equiv.swap 0 1 (τ⁻¹ (τ i)) = i
      rw [show τ⁻¹ (τ i) = i by simp]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h; rw [h] at hi; exact absurd hi (by decide)
      · intro h; rw [h] at hi; exact absurd hi (by decide)

theorem exists_permEquiv_normalized [Finite G]
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    ∃ (ι : Fin 7 → Fin 23) (ζ : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀)),
      Function.Injective ι ∧ (∀ i, ι i ∈ heptad₀) ∧ IsPermEquiv M2 π ι ζ ∧
      ι 3 = 16 ∧ ι 4 = 19 ∧ ι 5 = 21 ∧ ι 6 = 22 := by
  obtain ⟨ι, ζ, hinj, hιH, hζ⟩ :=
    exists_permEquiv_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  set τf : Fin 7 → Fin 7 := fun i => ιinv (ι i) with hτf
  have hτinj : Function.Injective τf := by
    intro i j h
    apply hinj
    rw [← ιbar_ιinv (hιH i), ← ιbar_ιinv (hιH j)]
    exact congrArg ιbar h
  set τ := Equiv.ofBijective τf (Finite.injective_iff_bijective.mp hτinj) with hτ
  have hιτ : ∀ i, ι i = ιbar (τ i) := fun i => (ιbar_ιinv (hιH i)).symm
  obtain ⟨σ, hσ⟩ := exists_even_fix3456 τ
  set m : ↥M2bar := sbar σ with hm
  have hmσ : ∀ j, ((m : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) (ιbar j) =
      ιbar ((σ : Equiv.Perm (Fin 7)) j) := by
    intro j
    rw [← πbar_apply, hm, πbar_sbar]
  set ζ' : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀) := ζ.trans (MulAut.conj m) with hζ'
  refine ⟨fun i => ((m : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) (ι i), ζ',
    ((m : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)).injective.comp hinj, fun i => ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · dsimp only
    rw [hιτ, hmσ]
    exact ιbar_mem _
  · intro g i
    change ((m * ζ g * m⁻¹ : ↥M2bar) : ↥NativeSporadic.M23) •
      (((m : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) (ι i)) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, m23_smul_eq]
    have := hζ g i
    rw [m23_smul_eq] at this
    simp [this]
  · dsimp only
    rw [hιτ, hmσ, hσ 3 (by decide)]; rfl
  · dsimp only
    rw [hιτ, hmσ, hσ 4 (by decide)]; rfl
  · dsimp only
    rw [hιτ, hmσ, hσ 5 (by decide)]; rfl
  · dsimp only
    rw [hιτ, hmσ, hσ 6 (by decide)]; rfl

section Setting

variable [Finite G] {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}

theorem card_H_of_setting (h526 : Stmt5_2_6)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special)
    (hQ : Stmt5_2_8_Q) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : Nat.card H = 1920 := by
  have hH := eq_setStabIn_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hHM2 : H ≤ M2 := hH ▸ setStabIn_le M2 π _
  have hTs : IsSylowTwoOf T M2 := isSylowTwoOf_of_isSylowTwo hyp.sylow hS.T_le
  have hUH : pCoreOf 2 M2 ≤ H :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTs).trans hyp.hStar.1.1
  have h1 := card_map_mul_card_inf hS.ker_eq hHM2
  rw [inf_of_le_right hUH, hU16] at h1
  have h2 : Nat.card ((H.subgroupOf M2).map π) = 120 := by
    rw [card_eq_card_filter (p := fun σ => Equiv.Perm.sign σ = 1 ∧ Pres56 σ), card_filter_pres56]
    intro σ
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hmH : (m : G) ∈ H := Subgroup.mem_subgroupOf.mp hm
      rw [hH, mem_setStabIn] at hmH
      obtain ⟨_, h56⟩ := hmH
      refine ⟨Equiv.Perm.mem_alternatingGroup.mp (hS.range_eq ▸ ⟨m, rfl⟩), ?_⟩
      rw [smul_pair_set_eq_iff] at h56
      exact h56
    · rintro ⟨hs, h56⟩
      obtain ⟨m, hm⟩ : σ ∈ π.range := hS.range_eq ▸ Equiv.Perm.mem_alternatingGroup.mpr hs
      refine ⟨m, Subgroup.mem_subgroupOf.mpr ?_, hm⟩
      rw [hH, mem_setStabIn]
      exact ⟨m.2, by rw [hm, smul_pair_set_eq_iff]; exact h56⟩
  rw [h2] at h1
  omega

theorem mem_K_of_fix56
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {m : G} (hm : m ∈ M2)
    (h5 : π ⟨m, hm⟩ 5 = 5) (h6 : π ⟨m, hm⟩ 6 = 6) : m ∈ oTwoUpper H := by
  classical
  obtain ⟨-, -, hQeq, -, h60⟩ := setting_K_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hUK : pCoreOf 2 M2 ≤ oTwoUpper H := hQeq ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _
  apply mem_of_map_mem hS.ker_eq hUK hm
  set S := ((oTwoUpper H).subgroupOf M2).map π with hSdef
  set P : Equiv.Perm (Fin 7) → Prop := fun σ => Equiv.Perm.sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6
    with hP
  have hsub : (Finset.univ.filter fun σ => σ ∈ S) ⊆ Finset.univ.filter P := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨k, hk, rfl⟩ := hσ
    have hkK : (k : G) ∈ oTwoUpper H := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨k5, k6⟩ := fix_five_six_of_mem_oTwoUpper h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hkK k.2
    exact ⟨Equiv.Perm.mem_alternatingGroup.mp (hS.range_eq ▸ ⟨k, rfl⟩), k5, k6⟩
  have hc1 : (Finset.univ.filter fun σ => σ ∈ S).card = 60 := by
    rw [← card_eq_card_filter (p := fun σ => σ ∈ S) (fun σ => Iff.rfl), h60]
  have hc2 : (Finset.univ.filter P).card = 60 := a7Count56_eq
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc1, hc2])
  have hmem : π ⟨m, hm⟩ ∈ Finset.univ.filter P := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP]
    exact ⟨Equiv.Perm.mem_alternatingGroup.mp (hS.range_eq ▸ ⟨_, rfl⟩), h5, h6⟩
  rw [← heq] at hmem
  simpa using hmem

theorem inv_mem_456 {σ : Equiv.Perm (Fin 7)} (hσ : ∀ i : Fin 7, 4 ≤ i.val → 4 ≤ (σ i).val)
    {i : Fin 7} (hi : 4 ≤ i.val) : 4 ≤ (σ⁻¹ i).val := by
  have h4 := hσ 4 (by decide)
  have h5 := hσ 5 (by decide)
  have h6 := hσ 6 (by decide)
  have h45 : (σ 4).val ≠ (σ 5).val := fun h => absurd (σ.injective (Fin.ext h)) (by decide)
  have h46 : (σ 4).val ≠ (σ 6).val := fun h => absurd (σ.injective (Fin.ext h)) (by decide)
  have h56 : (σ 5).val ≠ (σ 6).val := fun h => absurd (σ.injective (Fin.ext h)) (by decide)
  have hlt4 := (σ 4).isLt
  have hlt5 := (σ 5).isLt
  have hlt6 := (σ 6).isLt
  have hilt := i.isLt
  rcases (show i.val = (σ 4).val ∨ i.val = (σ 5).val ∨ i.val = (σ 6).val by omega) with
    h | h | h
  · rw [show i = σ 4 from Fin.ext h, Equiv.Perm.inv_def, Equiv.symm_apply_apply]; decide
  · rw [show i = σ 5 from Fin.ext h, Equiv.Perm.inv_def, Equiv.symm_apply_apply]; decide
  · rw [show i = σ 6 from Fin.ext h, Equiv.Perm.inv_def, Equiv.symm_apply_apply]; decide

theorem k4List_facts
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∀ k ∈ k4List, (k 4 = 4 ∧ k 5 = 5 ∧ k 6 = 6) ∧ Equiv.Perm.sign k = 1 ∧ k ^ 4 = 1 := by
  obtain ⟨hTK, -, -, -⟩ := inf_L_facts_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hmap := map_inf_L_eq_k4Sub h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  intro k hk
  have hk' : k ∈ k4Sub := hk
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap] at hk'
    obtain ⟨t, ht, rfl⟩ := hk'
    have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
    have htK : (t : G) ∈ oTwoUpper H := by
      have : (t : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp ht
      rw [hTK] at this
      exact this.2
    have h4' : π t 4 = 4 := by
      have h := (hS.orbits 4 (π t 4)).mp ⟨t, htT, rfl⟩
      revert h
      generalize π t 4 = j
      revert j
      decide
    obtain ⟨h5', h6'⟩ :=
      fix_five_six_of_mem_oTwoUpper h526 h1284 hSz hU4 hsp hQ hyp hM23 hS htK t.2
    exact ⟨h4', h5', h6'⟩
  · rw [← hmap] at hk'
    obtain ⟨t, -, rfl⟩ := hk'
    exact Equiv.Perm.mem_alternatingGroup.mp (hS.range_eq ▸ ⟨t, rfl⟩)
  · have h := pow_card_eq_one' (G := ↥(k4Sub)) (x := ⟨k, hk⟩)
    rw [card_k4Sub] at h
    exact congrArg Subtype.val h

theorem conj_mem_k4List
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {τ : Equiv.Perm (Fin 7)} (hτs : Equiv.Perm.sign τ = 1)
    (hτ : ∀ i : Fin 7, 4 ≤ i.val → 4 ≤ (τ i).val) :
    τ ∈ Subgroup.normalizer (k4Sub : Set (Equiv.Perm (Fin 7))) := by
  have hfacts := k4List_facts h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have key : ∀ σ : Equiv.Perm (Fin 7), Equiv.Perm.sign σ = 1 →
      (∀ i : Fin 7, 4 ≤ i.val → 4 ≤ (σ i).val) → ∀ k ∈ k4List, σ * k * σ⁻¹ ∈ k4List := by
    intro σ hσs hσ k hk
    obtain ⟨⟨k4', k5', k6'⟩, hks, hk4⟩ := hfacts k hk
    have hkfix : ∀ i : Fin 7, 4 ≤ i.val → k i = i := by
      intro i hi
      rcases (show i = 4 ∨ i = 5 ∨ i = 6 by omega) with rfl | rfl | rfl
      · exact k4'
      · exact k5'
      · exact k6'
    have hσinv : ∀ i : Fin 7, 4 ≤ i.val → 4 ≤ (σ⁻¹ i).val := fun i hi => inv_mem_456 hσ hi
    have hfix : ∀ i : Fin 7, 4 ≤ i.val → (σ * k * σ⁻¹) i = i := by
      intro i hi
      simp only [Equiv.Perm.mul_apply]
      rw [hkfix _ (hσinv i hi)]
      simp
    refine mem_k4List_of ?_ ?_ (hfix 4 (by decide)) (hfix 5 (by decide)) (hfix 6 (by decide))
    · rw [map_mul, map_mul, map_inv, hks, hσs]; rfl
    · rw [conj_pow, hk4, mul_one, mul_inv_cancel]
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact key τ hτs hτ k hk
  · intro hk
    have hτinv : ∀ i : Fin 7, 4 ≤ i.val → 4 ≤ (τ⁻¹ i).val := fun i hi => inv_mem_456 hτ hi
    have := key τ⁻¹ (by rw [map_inv, hτs, inv_one]) hτinv _ hk
    rwa [inv_inv, show τ⁻¹ * (τ * k * τ⁻¹) * τ = k by group] at this

theorem mem_L_of_mem_G0_of_normalizes
    (h526 : Stmt5_2_6) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) (hsimple : IsSimpleGroup ↥(m23G0 M L H B D))
    (hcardG0 : Nat.card ↥(m23G0 M L H B D) = 20160) {x : G} (hxG0 : x ∈ m23G0 M L H B D)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) : x ∈ L := by
  set G0 := m23G0 M L H B D with hG0def
  have hLG0 : L ≤ G0 := le_sup_left.trans (le_sup_left.trans le_sup_left)
  obtain ⟨-, -, -, -, hcardL⟩ := setting_L_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hPc : Nat.card ↥(L.subgroupOf G0) = 960 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG0).toEquiv, hcardL]
  have hPX : L.subgroupOf G0 ≤ (Subgroup.normalizer (L : Set G)).subgroupOf G0 := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hy))
  rcases eq_or_eq_top_of_card_eq_960 hcardG0 hPc hPX with h | h
  · have hmem : (⟨x, hxG0⟩ : ↥G0) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf G0 :=
      Subgroup.mem_subgroupOf.mpr hxN
    rw [h] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · exfalso
    have hn : (L.subgroupOf G0).Normal := ⟨fun y hy g => by
      have hg : (g : G) ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.mem_subgroupOf.mp (h ▸ Subgroup.mem_top g)
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy⟩
    rcases hsimple.eq_bot_or_eq_top_of_normal (L.subgroupOf G0) with hb | ht
    · rw [hb, Subgroup.card_bot] at hPc
      norm_num at hPc
    · rw [ht, Subgroup.card_top, hcardG0] at hPc
      norm_num at hPc

theorem mem_L_of_fix456
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) (hsimple : IsSimpleGroup ↥(m23G0 M L H B D))
    (hcardG0 : Nat.card ↥(m23G0 M L H B D) = 20160) {m : G} (hm : m ∈ M2)
    (h4 : π ⟨m, hm⟩ 4 = 4) (h5 : π ⟨m, hm⟩ 5 = 5) (h6 : π ⟨m, hm⟩ 6 = 6) : m ∈ L := by
  have hKG0 : oTwoUpper H ≤ m23G0 M L H B D := le_sup_right.trans le_sup_right
  have hmG0 := hKG0 (mem_K_of_fix56 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hm h5 h6)
  have hσN := conj_mem_k4List h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
    (τ := π ⟨m, hm⟩) (Equiv.Perm.mem_alternatingGroup.mp (hS.range_eq ▸ ⟨_, rfl⟩)) (by
      intro i hi
      rcases (show i = 4 ∨ i = 5 ∨ i = 6 by omega) with rfl | rfl | rfl
      · rw [h4]; decide
      · rw [h5]; decide
      · rw [h6]; decide)
  have hmM : m ∈ M := mem_M_of_mem_normalizer_k4Sub h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
    ⟨m, hm⟩ hσN
  exact mem_L_of_mem_G0_of_normalizes h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hsimple hcardG0 hmG0
    (hyp.normal hmM)

end Setting

theorem apply21_22 {g : ↥NativeSporadic.M23} (hg : g ∈ Gbar) (x : Fin 23)
    (hx : x = 21 ∨ x = 22) :
    (g : Equiv.Perm (Fin 23)) x = 21 ∨ (g : Equiv.Perm (Fin 23)) x = 22 := by
  rcases mem_Gbar_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx with rfl | rfl <;> simp [h1, h2]

theorem conj_mem_fix21_iff {g x : ↥NativeSporadic.M23} (hg : g ∈ Gbar) :
    g⁻¹ * x * g ∈ fix21 ↔ x ∈ fix21 := by
  have key : ∀ {g x : ↥NativeSporadic.M23}, g ∈ Gbar → x ∈ fix21 → g⁻¹ * x * g ∈ fix21 := by
    intro g x hg hx
    obtain ⟨h21, h22⟩ := mem_fix21_iff.mp hx
    have hg' : g⁻¹ ∈ Gbar := Gbar.inv_mem hg
    have hfix : ∀ y : Fin 23, (y = 21 ∨ y = 22) → (x : Equiv.Perm (Fin 23)) y = y := by
      rintro y (rfl | rfl)
      · exact h21
      · exact h22
    rw [mem_fix21_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    constructor
    · rw [hfix _ (apply21_22 hg 21 (Or.inl rfl)), Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    · rw [hfix _ (apply21_22 hg 22 (Or.inr rfl)), Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  constructor
  · intro h
    have := key (Gbar.inv_mem hg) h
    rwa [inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  · exact key hg

theorem conj_mem_Lbar_iff {g x : ↥NativeSporadic.M23} (hg : g ∈ Gbar)
    (h19 : (g : Equiv.Perm (Fin 23)) 19 = 19) : g⁻¹ * x * g ∈ Lbar ↔ x ∈ Lbar := by
  have h19' : ((g⁻¹ : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) 19 = 19 := by
    rw [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq]; exact h19.symm
  have key : ∀ {g x : ↥NativeSporadic.M23}, g ∈ Gbar → (g : Equiv.Perm (Fin 23)) 19 = 19 →
      x ∈ Lbar → g⁻¹ * x * g ∈ Lbar := by
    intro g x hg hg19 hx
    have hfix := mem_Lbar_iff.mp hx
    have hx21 : x ∈ fix21 := mem_fix21_iff.mpr ⟨hfix.2.1, hfix.2.2⟩
    obtain ⟨h21, h22⟩ := mem_fix21_iff.mp ((conj_mem_fix21_iff hg).mpr hx21)
    refine mem_Lbar_iff.mpr ⟨?_, h21, h22⟩
    have hg19' : (g : Equiv.Perm (Fin 23))⁻¹ 19 = 19 := by
      rw [Equiv.Perm.inv_eq_iff_eq]; exact hg19.symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hg19, hfix.1, hg19']
  constructor
  · intro h
    have := key (Gbar.inv_mem hg) h19' h
    rwa [inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  · exact key hg h19

theorem xbar0_eq_pair {ι : Fin 7 → Fin 23} (hι5 : ι 5 = 21) (hι6 : ι 6 = 22)
    (h : ι 5 ≠ ι 6) : xbar0 = pair (ι 5) (ι 6) h := by
  rw [xbar0]
  exact Subtype.ext (by simp [hι5, hι6])

theorem simple_card_G0_of_beta {G : Type} [Group G] {Gx G0 : Subgroup G} (hG0Gx : G0 ≤ Gx)
    (β : ↥Gx ≃* ↥Gbar)
    (hβ : ∀ g : ↥Gx, (g : G) ∈ G0 ↔ (β g : ↥NativeSporadic.M23) ∈ fix21) :
    IsSimpleGroup ↥G0 ∧ Nat.card ↥G0 = 20160 := by
  have hmap : (G0.subgroupOf Gx).map β.toMonoidHom = fix21.subgroupOf Gbar := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ((hβ g).mp (Subgroup.mem_subgroupOf.mp hg))
    · intro hz
      refine ⟨β.symm z, Subgroup.mem_subgroupOf.mpr ((hβ _).mpr ?_), by simp⟩
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_subgroupOf.mp hz
  set e₀ : ↥G0 ≃* ↥(fix21.subgroupOf Gbar) :=
    (Subgroup.subgroupOfEquivOfLe hG0Gx).symm.trans
      ((β.subgroupMap (G0.subgroupOf Gx)).trans (MulEquiv.subgroupCongr hmap)) with he₀
  set e₁ : ↥(fix21.subgroupOf Gbar) ≃* ↥P0 :=
    (Subgroup.equivMapOfInjective _ psiBar psiBar_injective).trans
      (MulEquiv.subgroupCongr map_fix21_eq_P0) with he₁
  have hcard : Nat.card ↥G0 = 20160 := by
    rw [Nat.card_congr (e₀.trans e₁).toEquiv, card_range_pslPerm]
  refine ⟨?_, hcard⟩
  have := isSimpleGroup_P0
  have : Finite ↥G0 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial ↥G0 := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  exact IsSimpleGroup.isSimpleGroup_of_surjective (e₀.trans e₁).symm.toMonoidHom
    (e₀.trans e₁).symm.surjective

theorem exists_beta_of_setting [Finite G]
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    (hset : Stmt5_2_10_setting) (hfus : M23Fusion3) (h515 : Stmt5_2_15) (h516 : Stmt5_2_16)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ (ι : Fin 7 → Fin 23) (ζ : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀)),
      Function.Injective ι ∧ (∀ i, ι i ∈ heptad₀) ∧ IsPermEquiv M2 π ι ζ ∧
      ι 3 = 16 ∧ ι 4 = 19 ∧ ι 5 = 21 ∧ ι 6 = 22 ∧
      ∃ β : ↥(m23Gx T M L H B D) ≃* ↥Gbar,
        (∀ (g : ↥(m23Gx T M L H B D)) (hgM : (g : G) ∈ M2), (g : G) ∈ m23I M2 π →
          (β g : ↥NativeSporadic.M23) = (ζ ⟨g, hgM⟩ : ↥NativeSporadic.M23)) ∧
        (∀ g : ↥(m23Gx T M L H B D), (g : G) ∈ L ↔ (β g : ↥NativeSporadic.M23) ∈ Lbar) ∧
        (∀ g : ↥(m23Gx T M L H B D),
          (g : G) ∈ m23G0 M L H B D ↔ (β g : ↥NativeSporadic.M23) ∈ fix21) := by
  classical
  set Gx := m23Gx T M L H B D with hGxdef
  set G0 := m23G0 M L H B D with hG0def
  obtain ⟨ι, ζ, hinj, hιH, hζ, hι3, hι4, hι5, hι6⟩ :=
    exists_permEquiv_normalized h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨β₄, hβG0, hβL, hβM2⟩ :=
    exists_beta4 h526 h527 h1284 hSz hU4 hsp hQ hset hfus h515 h516 hyp hM23 hS
  refine ⟨ι, ζ, hinj, hιH, hζ, hι3, hι4, hι5, hι6, ?_⟩
  have hLG0 : L ≤ G0 := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hG0Gx : G0 ≤ Gx := le_sup_left
  have hH := eq_setStabIn_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hGxM2 : Gx ⊓ M2 = H :=
    (stmt5_2_19_of hQ h516 h526 h1284 hSz hU4 hsp G T M L V H B D L₂ n M2 π hyp hM23 hS).1
  have hcardH := card_H_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have h56 : ι 5 ≠ ι 6 := hinj.ne (by decide)
  have hζH : ∀ m : ↥M2, (m : G) ∈ H ↔ (ζ m : ↥NativeSporadic.M23) ∈ Gbar := by
    intro m
    rw [hH, mem_setStabIn, mem_stabilizer_iff, xbar0_eq_pair hι5 hι6 h56,
      hζ.smul_pair_eq_iff hinj m h56 h56]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨m.2, h⟩⟩
  have hHGx : ∀ g : G, g ∈ H → g ∈ Gx := fun g hg => (Subgroup.mem_inf.mp (hGxM2 ▸ hg)).1
  have hHM2 : ∀ g : G, g ∈ H → g ∈ M2 := fun g hg => (Subgroup.mem_inf.mp (hGxM2 ▸ hg)).2
  have hpre : ∀ h : ↥Hbar, ((ζ.symm ⟨h, (Subgroup.mem_inf.mp h.2).2⟩ : ↥M2) : G) ∈ H := by
    intro h
    rw [hζH, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_inf.mp h.2).1
  have hcardHbar : Nat.card ↥Hbar ≤ 1920 := by
    rw [← hcardH]
    refine Nat.card_le_card_of_injective (fun h : ↥Hbar =>
      (⟨(ζ.symm ⟨h, (Subgroup.mem_inf.mp h.2).2⟩ : ↥M2), hpre h⟩ : ↥H)) ?_
    intro x y hxy
    have h1 := congrArg (fun z : ↥H => (z : G)) hxy
    simp only at h1
    have h2 := ζ.symm.injective (Subtype.ext h1)
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  obtain ⟨hsimpleG0, hcardG0⟩ := simple_card_G0_of_beta hG0Gx β₄ hβG0
  obtain ⟨-, -, -, -, hcardL⟩ := setting_L_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hβLiff : ∀ g : ↥Gx, (g : G) ∈ L ↔ (β₄ g : ↥NativeSporadic.M23) ∈ Lbar := by
    set X : Subgroup ↥Gx := (Lbar.subgroupOf Gbar).comap β₄.toMonoidHom with hX
    have hLX : L.subgroupOf Gx ≤ X := fun g hg =>
      Subgroup.mem_subgroupOf.mpr (hβL g (Subgroup.mem_subgroupOf.mp hg))
    have hcX : Nat.card X ≤ 960 := by
      have h1 : Nat.card X = Nat.card ↥(Lbar.subgroupOf Gbar) := by
        rw [hX, ← Subgroup.card_map_of_injective (f := β₄.toMonoidHom) β₄.injective,
          Subgroup.map_comap_eq_self_of_surjective (f := β₄.toMonoidHom) β₄.surjective]
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (fun x hx => fix21_le_Gbar (mem_fix21_iff.mpr ⟨(mem_Lbar_iff.mp hx).2.1,
          (mem_Lbar_iff.mp hx).2.2⟩))).toEquiv, card_fix3 _ (by decide)]
    have heq : L.subgroupOf Gx = X := Subgroup.eq_of_le_of_card_ge hLX (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hLG0.trans hG0Gx)).toEquiv, hcardL]
      exact hcX)
    intro g
    constructor
    · exact hβL g
    · intro hg
      have : g ∈ X := Subgroup.mem_subgroupOf.mpr hg
      rw [← heq] at this
      exact Subgroup.mem_subgroupOf.mp this
  set ψ : ↥Hbar →* G := M2.subtype.comp (ζ.symm.toMonoidHom.comp
    (Subgroup.inclusion (inf_le_right : Hbar ≤ M2bar))) with hψ
  have hψGx : ∀ h, ψ h ∈ Gx := fun h => hHGx _ (hpre h)
  set γ : ↥Hbar →* ↥NativeSporadic.M23 :=
    Gbar.subtype.comp (β₄.toMonoidHom.comp (ψ.codRestrict Gx hψGx)) with hγ
  have hγapply : ∀ h : ↥Hbar, γ h = (β₄ ⟨ψ h, hψGx h⟩ : ↥NativeSporadic.M23) := fun h => rfl
  have hγinj : Function.Injective γ := by
    intro x y hxy
    rw [hγapply, hγapply] at hxy
    have h1 := β₄.injective (Subtype.ext hxy)
    have h2 : ψ x = ψ y := by
      have := congrArg (fun z : ↥Gx => (z : G)) h1
      exact this
    have h3 : (ζ.symm (Subgroup.inclusion (inf_le_right : Hbar ≤ M2bar) x) : ↥M2) =
        ζ.symm (Subgroup.inclusion (inf_le_right : Hbar ≤ M2bar) y) := Subtype.ext h2
    exact Subgroup.inclusion_injective _ (ζ.symm.injective h3)
  have hγH : ∀ h, γ h ∈ Hbar := by
    intro h
    rw [hγapply]
    exact Subgroup.mem_inf.mpr ⟨(β₄ _).2, hβM2 _ (hHM2 _ (hpre h))⟩
  have hγL : ∀ h : ↥Hbar, (h : ↥NativeSporadic.M23) ∈ Lbar → γ h ∈ Lbar := by
    intro h hL
    rw [hγapply, ← hβLiff]
    set m : ↥M2 := ζ.symm ⟨h, (Subgroup.mem_inf.mp h.2).2⟩ with hm
    have hζm : (ζ m : ↥NativeSporadic.M23) = h := by rw [hm, MulEquiv.apply_symm_apply]
    have hfixι : ∀ i : Fin 7, 4 ≤ i.val → π m i = i := by
      intro i hi
      have h1 := hζ m i
      rw [hζm, m23_smul_eq] at h1
      have h2 := mem_Lbar_iff.mp hL
      apply hinj
      rw [← h1]
      rcases (show i = 4 ∨ i = 5 ∨ i = 6 by omega) with rfl | rfl | rfl
      · rw [hι4]; exact h2.1
      · rw [hι5]; exact h2.2.1
      · rw [hι6]; exact h2.2.2
    exact mem_L_of_fix456 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS hsimpleG0 hcardG0 m.2
      (hfixι 4 (by decide)) (hfixι 5 (by decide)) (hfixι 6 (by decide))
  obtain ⟨g, hgH, hg19, hgI⟩ := exists_conj_of_hom_Hbar hcardHbar γ hγinj hγH hγL
  have hgG : g ∈ Gbar := (Subgroup.mem_inf.mp hgH).1
  set β : ↥Gx ≃* ↥Gbar := β₄.trans (MulAut.conj (⟨g, hgG⟩ : ↥Gbar)⁻¹) with hβdef
  have hβapply : ∀ x, (β x : ↥NativeSporadic.M23) = g⁻¹ * (β₄ x : ↥NativeSporadic.M23) * g :=
    fun x => by simp [hβdef]
  refine ⟨β, fun x hxM hxI => ?_, fun x => ?_, fun x => ?_⟩
  ·
    have hxH : (x : G) ∈ H := hGxM2 ▸ Subgroup.mem_inf.mpr ⟨x.2, hxM⟩
    set h₀ : ↥Hbar := ⟨ζ ⟨x, hxM⟩, Subgroup.mem_inf.mpr ⟨(hζH ⟨x, hxM⟩).mp hxH,
      (ζ ⟨x, hxM⟩).2⟩⟩ with hh₀
    have hIx : (h₀ : ↥NativeSporadic.M23) ∈ IxBar := by
      refine Subgroup.mem_inf.mpr ⟨?_, (hζH ⟨x, hxM⟩).mp hxH⟩
      have e : ({16, 19, 21, 22} : Set (Fin 23)) = ι '' {3, 4, 5, 6} := by
        simp only [Set.image_insert_eq, Set.image_singleton, hι3, hι4, hι5, hι6]
      rw [mem_stabilizer_iff, e, hζ.smul_image_eq_iff hinj]
      exact (mem_setStabIn.mp hxI).2
    have h1 := hgI h₀ hIx
    have hψh : (⟨ψ h₀, hψGx h₀⟩ : ↥Gx) = x := by
      apply Subtype.ext
      change ((ζ.symm (Subgroup.inclusion (inf_le_right : Hbar ≤ M2bar) h₀) : ↥M2) : G) = x
      have e : Subgroup.inclusion (inf_le_right : Hbar ≤ M2bar) h₀ = ζ ⟨x, hxM⟩ :=
        Subtype.ext rfl
      rw [e, MulEquiv.symm_apply_apply]
    have h2 : γ h₀ = (β₄ x : ↥NativeSporadic.M23) := by rw [hγapply, hψh]
    rw [hβapply, ← h2, h1]
    group
    rfl
  · rw [hβLiff, hβapply, conj_mem_Lbar_iff hgG hg19]
  · rw [hβG0, hβapply, conj_mem_fix21_iff hgG]

end CFSG.Quasithin.H13
