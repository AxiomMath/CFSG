module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Fe
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolTrace

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ}

private theorem alt5_order_two_three_iff : ∀ σ : Perm (Fin 5), σ ≠ 1 → Perm.sign σ = 1 →
    (σ ^ 5 ≠ 1 ↔ σ ^ 2 = 1 ∨ σ ^ 3 = 1) := by decide +kernel

theorem mem_of_fixW_quot_eq_top {M : Model 5} {N : Subgroup M.W} (hN : IsInvSub M ⊤ N)
    {B : Subgroup (Perm (Fin 5))} (h : fixW (M.quot N hN) B = ⊤) (b : Perm (Fin 5)) (hb : b ∈ B)
    (w : M.W) : M.act b w * w⁻¹ ∈ N := by
  have : M.projQuot N hN w ∈ fixW (M.quot N hN) B := by rw [h]; trivial
  exact (M.projQuot_mem_fixW_iff N hN B w).mp this b hb

private theorem hAS_top : ∀ g ∈ (⊤ : Subgroup (Perm (Fin 5))), ∃ a ∈ alternatingGroup (Fin 5),
    ∃ s ∈ S5Syl, g = a * s := fun g _ => perm5_eq_alt5_mul_syl g

theorem irr_aux (M : Model 5) (hnt : ∃ w : M.W, w ≠ 1) (hfix : fixW M ⊤ = ⊥)
    (hgen : ∀ U : Subgroup M.W, IsInvSub M ⊤ U → fixW M S5Syl ≤ U → U = ⊤)
    {a : Perm (Fin 5)} (ha : a ∈ alternatingGroup (Fin 5)) (ha1 : a ≠ 1) (ha5 : a ^ 5 ≠ 1)
    (hidx : idx M a ≤ 8) :
    M.IsIrred ∧ (Nonempty (M.Iso orth) ∨ Nonempty (M.Iso nat)) := by
  set A := alternatingGroup (Fin 5) with hAdef
  have hA0 : fixW M A = ⊥ := fixW_alt5_eq_bot_of_fixW_top_eq_bot M hfix
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
  have hRA : fixW (M.restrict N hN) A ≠ ⊤ := by
    intro h
    apply hNbot
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hfix' : u ∈ fixW M A := by
      intro b hb
      have := (eq_top_iff.mp h (Subgroup.mem_top ⟨u, hu⟩)) b hb
      exact congrArg Subtype.val this
    rw [hA0, Subgroup.mem_bot] at hfix'
    exact hfix'
  have hR4 : 4 ≤ idx (M.restrict N hN) a := cf_small _ hRA ha ha1 ha5
  have hUA : fixW (M.quot N hN) A = ⊤ := by
    by_contra hU
    have h4 : 4 ≤ idx (M.quot N hN) a := cf_small _ hU ha ha1 ha5
    have := idx_restrict_mul_idx_quot_le M N hN a
    nlinarith
  have hmem := mem_of_fixW_quot_eq_top hN hUA
  obtain ⟨hSG, hodd⟩ : (S5Syl ≤ (⊤ : Subgroup (Perm (Fin 5)))) ∧ Odd (S5Syl.relIndex ⊤) :=
    ⟨le_top, odd_relIndex_S5Syl⟩
  have hSN : fixW M S5Syl ≤ N := by
    intro c hc
    obtain ⟨m, hm, f, hf, rfl⟩ := trace_model M hSG hodd hAS_top N
      (fun b hb w => hmem b hb w) hc
    rw [hfix, Subgroup.mem_bot] at hf
    rw [hf, mul_one]
    exact hm
  have hNtop : N = ⊤ := hgen N hN hSN
  have hiso : M.Iso (M.restrict N hN) := M.isoRestrictTop N hN hNtop
  refine ⟨Model.IsIrred.of_iso hiso.symm hirr, ?_⟩
  rcases model5_irred_classification _ hirr hmoved with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨hiso.trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨hiso.trans e⟩

theorem irr (M : Model 5) (hnt : ∃ w : M.W, w ≠ 1) (hfix : fixW M ⊤ = ⊥)
    (hgen : ∀ U : Subgroup M.W, IsInvSub M ⊤ U → fixW M S5Syl ≤ U → U = ⊤)
    {a : Perm (Fin 5)} (ha : a ∈ alternatingGroup (Fin 5)) (ha1 : a ≠ 1)
    (ha23 : a ^ 2 = 1 ∨ a ^ 3 = 1) (hidx : idx M a ≤ 8) :
    M.IsIrred ∧ (Nonempty (M.Iso orth) ∨ Nonempty (M.Iso nat)) :=
  irr_aux M hnt hfix hgen ha ha1
    ((alt5_order_two_three_iff a ha1 (Perm.mem_alternatingGroup.mp ha)).mpr ha23) hidx

theorem exists_even_of_klein {B : Subgroup (Perm (Fin n))} (hcard : Nat.card B = 4)
    (hexp : ∀ x ∈ B, x * x = 1) : ∃ a ∈ B, a ≠ 1 ∧ Perm.sign a = 1 := by
  have hbot : B ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hcard; omega
  obtain ⟨⟨x, hxB⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hnot : ¬ B ≤ Subgroup.zpowers x := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hexp x hxB)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨y, hyB, hyx⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  by_cases hsx : Perm.sign x = 1
  · exact ⟨x, hxB, hx1', hsx⟩
  by_cases hsy : Perm.sign y = 1
  · exact ⟨y, hyB, hy1, hsy⟩
  refine ⟨x * y, B.mul_mem hxB hyB, ?_, ?_⟩
  · intro h
    apply hyx
    have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
  · rw [map_mul, (Int.units_eq_one_or _).resolve_left hsx, (Int.units_eq_one_or _).resolve_left hsy]
    decide

end CFSG.Quasithin.F53Mod
