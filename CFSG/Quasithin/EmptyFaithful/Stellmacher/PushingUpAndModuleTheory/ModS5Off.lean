module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Klein
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Fe

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

theorem iso_of_card_le_sixteen (M : Model 5) (hnt : ∃ w : M.W, w ≠ 1) (hfix : fixW M ⊤ = ⊥)
    (hcard : Nat.card M.W ≤ 16) : Nonempty (M.Iso orth) ∨ Nonempty (M.Iso nat) := by
  obtain ⟨N, hN, hNbot, hirr⟩ := exists_minimal_inv M hnt
  have hmoved : ∃ σ w, (M.restrict N hN).act σ w ≠ w := by
    by_contra hall
    push Not at hall
    apply hNbot
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hfix' : u ∈ fixW M ⊤ := by
      intro b _
      exact congrArg Subtype.val (hall b ⟨u, hu⟩)
    rw [hfix, Subgroup.mem_bot] at hfix'
    exact hfix'
  have hN16 : Nat.card (M.restrict N hN).W = 16 := model5_irred_card _ hirr hmoved
  have hNtop : N = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top]
    have h1 : Nat.card N ≤ Nat.card M.W := Subgroup.card_le_of_le le_top |>.trans (by simp)
    have h2 : Nat.card N = 16 := hN16
    have h3 : Nat.card (⊤ : Subgroup M.W) = Nat.card M.W := Subgroup.card_top
    omega
  have hiso : M.Iso (M.restrict N hN) := M.isoRestrictTop N hN hNtop
  rcases model5_irred_classification _ hirr hmoved with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨hiso.trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨hiso.trans e⟩

@[expose] def OffConcl (M : Model 5) (B : Subgroup (Perm (Fin 5))) : Prop :=
  (fixW M B).index = Nat.card B ∧
    ((Nonempty (M.Iso orth) ∧
        ((∃ t : Perm (Fin 5), t.IsSwap ∧ B = Subgroup.zpowers t) ∨
          (Nat.card B = 4 ∧ ¬ B ≤ alternatingGroup (Fin 5)))) ∨
      (Nonempty (M.Iso nat) ∧ Nat.card B = 4 ∧ B ≤ alternatingGroup (Fin 5)))

private theorem sign_conj (h b : Perm (Fin 5)) : Perm.sign (h * b * h⁻¹) = Perm.sign b := by
  rw [map_mul, map_mul, map_inv]
  rw [mul_comm (Perm.sign h) (Perm.sign b), mul_assoc, mul_inv_cancel, mul_one]

private theorem le_alt_map_conj_iff (h : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) :
    B.map (MulAut.conj h).toMonoidHom ≤ alternatingGroup (Fin 5) ↔ B ≤ alternatingGroup (Fin 5) := by
  constructor
  · intro hB b hb
    have h1 := hB ⟨b, hb, rfl⟩
    have e : (MulAut.conj h).toMonoidHom b = h * b * h⁻¹ := rfl
    rw [e, Perm.mem_alternatingGroup, sign_conj] at h1
    exact Perm.mem_alternatingGroup.mpr h1
  · rintro hB _ ⟨b, hb, rfl⟩
    have h1 := Perm.mem_alternatingGroup.mp (hB hb)
    show h * b * h⁻¹ ∈ _
    rw [Perm.mem_alternatingGroup, sign_conj]
    exact h1

theorem OffConcl.map_conj {M : Model 5} {B : Subgroup (Perm (Fin 5))} (h : OffConcl M B)
    (g : Perm (Fin 5)) : OffConcl M (B.map (MulAut.conj g).toMonoidHom) := by
  have hcard : Nat.card (B.map (MulAut.conj g).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨hidx, hrest⟩ := h
  refine ⟨by rw [fidx_conj, hcard, hidx], ?_⟩
  rw [hcard, le_alt_map_conj_iff]
  rcases hrest with ⟨hi, hs | hk⟩ | hn
  · refine Or.inl ⟨hi, Or.inl ?_⟩
    obtain ⟨t, ⟨x, y, hxy, rfl⟩, rfl⟩ := hs
    refine ⟨swap (g x) (g y), ⟨g x, g y, g.injective.ne hxy, rfl⟩, ?_⟩
    rw [MonoidHom.map_zpowers, swap_apply_apply g x y]
    simp [MulAut.conj_apply]
  · exact Or.inl ⟨hi, Or.inr hk⟩
  · exact Or.inr hn

private theorem index_mul_of_profile_orth {B : Subgroup (Perm (Fin 5))} {a c d : ℕ}
    (h : profile orth B = (a, c, d)) : (fixW orth B).index * c = 16 := by
  have h1 : Nat.card (fixW orth B) = c := by
    have := congrArg (fun p => p.2.1) h
    simpa [profile] using this
  have h2 := Subgroup.card_mul_index (fixW orth B)
  rw [h1, card_orth] at h2
  rw [mul_comm]; exact h2

private theorem index_mul_of_profile_nat {B : Subgroup (Perm (Fin 5))} {a c d : ℕ}
    (h : profile nat B = (a, c, d)) : (fixW nat B).index * c = 16 := by
  have h1 : Nat.card (fixW nat B) = c := by
    have := congrArg (fun p => p.2.1) h
    simpa [profile] using this
  have h2 := Subgroup.card_mul_index (fixW nat B)
  rw [h1, card_nat] at h2
  rw [mul_comm]; exact h2

private theorem sq_le_sixteen {i : ℕ} (h : i ≤ 4) : i ^ 2 ≤ 16 := by
  calc i ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left h 2
    _ = 16 := by norm_num

theorem off_syl (M : Model 5) (hnt : ∃ w : M.W, w ≠ 1) (hfix : fixW M ⊤ = ⊥)
    {B : Subgroup (Perm (Fin 5))} (hle : B ≤ S5Syl) (hexp : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥)
    (hoff : (fixW M B).index ≤ Nat.card B) : OffConcl M B := by
  have hA0 : fixW M (alternatingGroup (Fin 5)) = ⊥ := fixW_alt5_eq_bot_of_fixW_top_eq_bot M hfix
  have hAnt : fixW M (alternatingGroup (Fin 5)) ≠ ⊤ := by
    intro h
    obtain ⟨w, hw⟩ := hnt
    have : w ∈ fixW M (alternatingGroup (Fin 5)) := by rw [h]; trivial
    rw [hA0, Subgroup.mem_bot] at this
    exact hw this
  rcases le_syl_cases hle hexp hne with ⟨t, htB, ht1, hBt, hc2⟩ | hT | hThat
  · subst hBt
    have htt : t * t = 1 := hexp t htB
    have hidx2 : idx M t ≤ 2 := by unfold idx; rw [hc2] at hoff; exact hoff
    by_cases hs : Perm.sign t = 1
    · exfalso
      have h5 : t ^ 5 ≠ 1 := by
        have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact htt
        have : t ^ 5 = t := by
          have e5 : t ^ 5 = (t ^ 2) ^ 2 * t := by rw [← pow_mul, ← pow_succ]
          rw [e5, ht2, one_pow, one_mul]
        rw [this]; exact ht1
      have := cf_small M hAnt (Perm.mem_alternatingGroup.mpr hs) ht1 h5
      omega
    · have hsw : t.IsSwap := (isSwap_iff t).mpr ⟨ht1, by rw [pow_two]; exact htt, hs⟩
      have hpow : Nat.card M.W ≤ idx M t ^ 4 := card_le_idx_pow_four M hsw hfix
      have h16 : Nat.card M.W ≤ 16 := hpow.trans (by
        calc idx M t ^ 4 ≤ 2 ^ 4 := Nat.pow_le_pow_left hidx2 4
          _ = 16 := by norm_num)
      rcases iso_of_card_le_sixteen M hnt hfix h16 with he | he
      · obtain ⟨e⟩ := he
        have h2 : idx orth t = 2 := ((transvections t ht1).2).mpr hsw
        have h3 : idx M t = 2 := (e.idx_eq t).symm.trans h2
        exact ⟨by rw [hc2]; exact h3, Or.inl ⟨⟨e⟩, Or.inl ⟨t, hsw, rfl⟩⟩⟩
      · obtain ⟨e⟩ := he
        exfalso
        have h4 := (transvections t ht1).1
        have h3 := e.idx_eq t
        omega
  · subst hT
    rw [card_S5T_eq_four] at hoff
    have hsq := card_le_fidx_sq M conjT34 alt5_le_syl_sup hA0
    have h16 : Nat.card M.W ≤ 16 := hsq.trans (sq_le_sixteen hoff)
    rcases iso_of_card_le_sixteen M hnt hfix h16 with he | he
    · obtain ⟨e⟩ := he
      exfalso
      have h1 := index_mul_of_profile_orth profile_orth.2.2.2.1
      rw [e.index_fixW_eq] at h1
      omega
    · obtain ⟨e⟩ := he
      have h1 := index_mul_of_profile_nat profile_nat.2.2.2.1
      rw [e.index_fixW_eq] at h1
      refine ⟨by rw [card_S5T_eq_four]; omega, Or.inr ⟨⟨e⟩, card_S5T_eq_four, ?_⟩⟩
      exact inf_le_right
  · subst hThat
    rw [card_S5That_eq_four] at hoff
    have hsq := card_le_fidx_sq M conjThat234 top_le_that_sup hfix
    have h16 : Nat.card M.W ≤ 16 := hsq.trans (sq_le_sixteen hoff)
    rcases iso_of_card_le_sixteen M hnt hfix h16 with he | he
    · obtain ⟨e⟩ := he
      have h1 := index_mul_of_profile_orth profile_orth.2.2.1
      rw [e.index_fixW_eq] at h1
      refine ⟨by rw [card_S5That_eq_four]; omega, Or.inl ⟨⟨e⟩, Or.inr ⟨card_S5That_eq_four, ?_⟩⟩⟩
      intro hA
      have hmem : swap (0 : Fin 5) 2 ∈ S5That := Subgroup.subset_closure (by simp)
      have := Perm.mem_alternatingGroup.mp (hA hmem)
      rw [Perm.sign_swap (by decide)] at this
      revert this; decide
    · obtain ⟨e⟩ := he
      exfalso
      have h1 := index_mul_of_profile_nat profile_nat.2.2.1
      rw [e.index_fixW_eq] at h1
      omega

theorem offender_dichotomy (M : Model 5) (hnt : ∃ w : M.W, w ≠ 1) (hfix : fixW M ⊤ = ⊥)
    {B : Subgroup (Perm (Fin 5))} (hne : B ≠ ⊥) (hexp : ∀ x ∈ B, x * x = 1)
    (hoff : (fixW M B).index ≤ Nat.card B) :
    (fixW M B).index = Nat.card B ∧
      ((Nonempty (M.Iso orth) ∧
          ((∃ t : Perm (Fin 5), t.IsSwap ∧ B = Subgroup.zpowers t) ∨
            (Nat.card B = 4 ∧ ¬ B ≤ alternatingGroup (Fin 5)))) ∨
        (Nonempty (M.Iso nat) ∧ Nat.card B = 4 ∧ B ≤ alternatingGroup (Fin 5))) := by
  obtain ⟨g, hg⟩ := exists_conj_le_syl hexp
  set B' := B.map (MulAut.conj g).toMonoidHom with hB'
  have hcard : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hne' : B' ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro b hb
    have : (MulAut.conj g).toMonoidHom b ∈ B' := ⟨b, hb, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    have : b = 1 := (MulAut.conj g).injective (by simpa using this)
    rw [this]; exact Subgroup.one_mem _
  have hexp' : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have := hexp b hb
    show (g * b * g⁻¹) * (g * b * g⁻¹) = 1
    calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hoff' : (fixW M B').index ≤ Nat.card B' := by rw [hB', fidx_conj, hcard]; exact hoff
  have h1 := (off_syl M hnt hfix hg hexp' hne' hoff').map_conj g⁻¹
  have hback : B'.map (MulAut.conj g⁻¹).toMonoidHom = B := by
    rw [hB', Subgroup.map_map]
    have : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  rw [hback] at h1
  exact h1

end CFSG.Quasithin.F53Mod
