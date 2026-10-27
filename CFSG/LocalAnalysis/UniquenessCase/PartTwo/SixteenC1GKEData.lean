module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKEW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCLev
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCSyl

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

@[expose] def s16c1cEven : List ℕ :=
  ((sylowWords true).filter fun w => w.length % 2 == 0).map wordC

@[expose] def s16c1cBil (a b : ℕ) : Bool := qB true (a ^^^ b) ^^ qB true a ^^ qB true b

@[expose] def s16c1cSpanL (F : List ℕ) : List ℕ :=
  F.foldl (fun S f => if S.contains f then S else S ++ S.map (· ^^^ f)) [0]

@[expose] def s16c1cFixd (H : List ℕ) : List ℕ :=
  (List.range 64).filter fun n => H.any fun c => c != one && act c n == n

@[expose] def s16c1cE16Prop (H : List ℕ) (z : ℕ) : Prop :=
  z ≠ 0 ∧ (∀ c ∈ H, act c z = z) ∧
  (∀ n < 64, (∀ c ∈ H, act c n = n) → n = 0 ∨ n = z) ∧
  (∀ c ∈ H, ∀ n < 64, s16c1cBil n z = false → act c n = n ∨ act c n = n ^^^ z) ∧
  (∀ c ∈ H, c ≠ one → ∀ n < 64, (act c n = n ∨ act c n = n ^^^ z) → s16c1cBil n z = false) ∧
  (∀ n < 64, s16c1cBil n z = false → n ∈ s16c1cSpanL (s16c1cFixd H)) ∧
  ∃ c ∈ H, ∃ n < 64, s16c1cBil n z = false ∧ act c n ≠ n

instance (H : List ℕ) (z : ℕ) : Decidable (s16c1cE16Prop H z) := by
  unfold s16c1cE16Prop; infer_instance

theorem s16c1c_e16Check :
    ∀ H ∈ s16c1cLev 4, (∀ c ∈ H, c ∈ s16c1cEven) → ∃ z < 64, s16c1cE16Prop H z := by
  decide +kernel

private theorem s16c1cE_vec_inj {n m : ℕ} (hn : n < 64) (hm : m < 64) (h : vec n = vec m) :
    n = m := by
  have hall : ∀ a b : Fin 64, vec (a : ℕ) = vec (b : ℕ) → a = b := by decide +kernel
  have := hall ⟨n, hn⟩ ⟨m, hm⟩ h
  simpa using congrArg Fin.val this

private theorem s16c1cE_vec_zero : vec 0 = (0 : V₀) := by
  decide +kernel

theorem s16c1c_polar_vec (a b : ℕ) :
    polar (qModel true) (vec a) (vec b) = if s16c1cBil a b then 1 else 0 := by
  rw [QuadraticMap.polar, ← s16c1G_vec_xor, qModel_vec, qModel_vec, qModel_vec]
  unfold s16c1cBil
  cases qB true (a ^^^ b) <;> cases qB true a <;> cases qB true b <;> decide

private theorem s16c1cE_foldl_sound (C : AddSubgroup V₀) :
    ∀ (F S : List ℕ), (∀ s ∈ S, vec s ∈ C) → (∀ f ∈ F, vec f ∈ C) →
      ∀ n ∈ F.foldl (fun S f => if S.contains f then S else S ++ S.map (· ^^^ f)) S,
        vec n ∈ C := by
  intro F
  induction F with
  | nil =>
    intro S hS _ n hn
    exact hS n hn
  | cons f F ih =>
    intro S hS hF n hn
    rw [List.foldl_cons] at hn
    refine ih _ ?_ (fun g hg => hF g (List.mem_cons_of_mem _ hg)) n hn
    split_ifs with h
    · exact hS
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact hS s hs
      · rw [List.mem_map] at hs
        obtain ⟨t, ht, rfl⟩ := hs
        rw [s16c1G_vec_xor]
        exact add_mem (hS t ht) (hF f List.mem_cons_self)

theorem s16c1c_spanL_sound (F : List ℕ) :
    ∀ n ∈ s16c1cSpanL F, vec n ∈ AddSubgroup.closure (vec '' {m | m ∈ F}) := by
  intro n hn
  unfold s16c1cSpanL at hn
  refine s16c1cE_foldl_sound _ F [0] ?_ ?_ n hn
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    rw [s16c1cE_vec_zero]
    exact zero_mem _
  · intro f hf
    exact AddSubgroup.subset_closure ⟨f, hf, rfl⟩

theorem s16c1c_e16Lin_of_codes {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {H : List ℕ} {z : ℕ}
    (hz : z < 64) (hP : s16c1cE16Prop H z)
    (hc1 : ∀ y ∈ P, ∃ c ∈ H, Coded y c) (hc2 : ∀ c ∈ H, ∃ y ∈ P, Coded y c) :
    s16c1cE16Lin P := by
  obtain ⟨hz0, hzfix, hE1, hE2, hE3, hE4, hE5⟩ := hP
  have hzv : vec z ≠ (0 : V₀) := by
    intro h
    exact hz0 (s16c1cE_vec_inj hz (by norm_num) (h.trans s16c1cE_vec_zero.symm))
  let ℓ : V₀ →ₗ[ZMod 2] ZMod 2 := (QuadraticMap.polarBilin (qModel true)).flip (vec z)
  have hℓ : ∀ u, ℓ u = polar (qModel true) u (vec z) := fun u => by
    simp [ℓ, QuadraticMap.polarBilin_apply_apply]
  have hℓ0 : ∀ n : ℕ, ℓ (vec n) = 0 ↔ s16c1cBil n z = false := by
    intro n
    rw [hℓ, s16c1c_polar_vec]
    cases h : s16c1cBil n z <;> simp
  have hℓne : ℓ ≠ 0 := by
    intro h0
    apply hzv
    refine forall_polar_of_nondegenerate (qModel_nondegenerate true) _ (fun y => ?_)
    rw [polar_comm, ← hℓ, h0]
    rfl
  have hfix_iff : ∀ {e c}, Coded e c → ∀ n < 64, (e (vec n) = vec n ↔ act c n = n) := by
    intro e c he n hn
    rw [s16c1c_coded_apply he n]
    constructor
    · intro h
      exact s16c1cE_vec_inj (act_lt c n) hn h
    · intro h
      rw [h]
  have hxor_lt : ∀ n < 64, n ^^^ z < 64 := by
    intro n hn
    exact Nat.xor_lt_two_pow (n := 6) hn hz
  have hz_iff : ∀ {e c}, Coded e c → ∀ n < 64,
      (e (vec n) = vec n + vec z ↔ act c n = n ^^^ z) := by
    intro e c he n hn
    rw [s16c1c_coded_apply he n, ← s16c1G_vec_xor]
    constructor
    · intro h
      exact s16c1cE_vec_inj (act_lt c n) (hxor_lt n hn) h
    · intro h
      rw [h]
  refine ⟨vec z, hzv, ℓ, hℓne, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u
    obtain ⟨n, hn, rfl⟩ := s16c1G_exists_vec u
    constructor
    · intro h
      have h' : ∀ c ∈ H, act c n = n := by
        intro c hc
        obtain ⟨y, hy, hyc⟩ := hc2 c hc
        exact (hfix_iff hyc n hn).1 (h y hy)
      rcases hE1 n hn h' with h0 | h0
      · left
        rw [h0, s16c1cE_vec_zero]
      · right
        rw [h0]
    · rintro (h | h)
      · intro e _
        rw [h, map_zero]
      · intro e he
        obtain ⟨c, hc, hec⟩ := hc1 e he
        have hnz : n = z := s16c1cE_vec_inj hn hz h
        subst hnz
        exact (hfix_iff hec n hn).2 (hzfix c hc)
  ·
    intro e he u hu
    obtain ⟨n, hn, rfl⟩ := s16c1G_exists_vec u
    obtain ⟨c, hc, hec⟩ := hc1 e he
    rcases hE2 c hc n hn ((hℓ0 n).1 hu) with h | h
    · exact Or.inl ((hfix_iff hec n hn).2 h)
    · exact Or.inr ((hz_iff hec n hn).2 h)
  ·
    intro e he hne u hu
    obtain ⟨n, hn, rfl⟩ := s16c1G_exists_vec u
    obtain ⟨c, hc, hec⟩ := hc1 e he
    have hcne : c ≠ one := fun h => hne ((hec.eq_iff coded_one).2 h)
    refine (hℓ0 n).2 (hE3 c hc hcne n hn ?_)
    rcases hu with h | h
    · exact Or.inl ((hfix_iff hec n hn).1 h)
    · exact Or.inr ((hz_iff hec n hn).1 h)
  ·
    intro u hu
    obtain ⟨n, hn, rfl⟩ := s16c1G_exists_vec u
    have hsub := s16c1c_spanL_sound _ n (hE4 n hn ((hℓ0 n).1 hu))
    refine AddSubgroup.closure_mono ?_ hsub
    rintro _ ⟨m, hm, rfl⟩
    simp only [Set.mem_setOf_eq, s16c1cFixd, List.mem_filter, List.mem_range,
      List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hm
    obtain ⟨hm64, c, hc, hcne, hcm⟩ := hm
    obtain ⟨y, hy, hyc⟩ := hc2 c hc
    refine ⟨y, hy, fun hy1 => hcne ((hyc.eq_iff coded_one).1 hy1), ?_⟩
    exact (hfix_iff hyc m hm64).2 hcm
  ·
    obtain ⟨c, hc, n, hn, hbil, hmov⟩ := hE5
    obtain ⟨y, hy, hyc⟩ := hc2 c hc
    exact ⟨y, hy, vec n, (hℓ0 n).2 hbil, fun h => hmov ((hfix_iff hyc n hn).1 h)⟩

theorem s16c1c_e16Lin_of_T {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1)
    (hT : ∀ x ∈ P, x ∈ s16c1c_T) (hΩ : ∀ x ∈ P, x ∈ Ω₀ true) (hcard : Nat.card P = 16) :
    s16c1cE16Lin P := by
  obtain ⟨H, hH, hc1, hc2⟩ := s16c1c_describe hab h2
    (fun x hx => s16c1c_exists_coded_of_mem_T (hT x hx)) hcard
  have hEven : ∀ c ∈ H, c ∈ s16c1cEven := by
    intro c hc
    obtain ⟨y, hy, hyc⟩ := hc2 c hc
    obtain ⟨w, hw, rfl⟩ := s16c1c_mem_T.1 (hT y hy)
    have hev : Even w.length :=
      (wordProd_mem_omegaGroup_iff (s16c1c_spec.1 w hw)).1 (hΩ _ hy)
    have hcw : c = wordC w := (hyc.eq_iff (coded_wordProd w)).1 rfl
    subst hcw
    unfold s16c1cEven
    rw [List.mem_map]
    exact ⟨w, List.mem_filter.2 ⟨hw, beq_iff_eq.2 (Nat.even_iff.1 hev)⟩, rfl⟩
  obtain ⟨z, hz, hprop⟩ := s16c1c_e16Check H hH hEven
  exact s16c1c_e16Lin_of_codes hz hprop hc1 hc2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
