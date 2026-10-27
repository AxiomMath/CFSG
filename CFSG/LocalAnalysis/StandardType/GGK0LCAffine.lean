module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[simp] private lemma lk0xlcaff_fst_add {τ : Tag} (p q : AffPair τ) :
    (p + q).1 = p.1 + q.1 := rfl

@[simp] private lemma lk0xlcaff_snd_add {τ : Tag} (p q : AffPair τ) :
    (p + q).2 = p.2 + q.2 := rfl

@[simp] private lemma lk0xlcaff_fst_smul {τ : Tag} (c : ℤ) (p : AffPair τ) :
    (c • p).1 = c • p.1 := rfl

@[simp] private lemma lk0xlcaff_snd_smul {τ : Tag} (c : ℤ) (p : AffPair τ) :
    (c • p).2 = c • p.2 := rfl

@[simp] private lemma lk0xlcaff_fst_neg {τ : Tag} (p : AffPair τ) : (-p).1 = -p.1 := rfl

@[simp] private lemma lk0xlcaff_snd_neg {τ : Tag} (p : AffPair τ) : (-p).2 = -p.2 := rfl

@[simp] private lemma lk0xlcaff_fst_zero {τ : Tag} : (0 : AffPair τ).1 = 0 := rfl

@[simp] private lemma lk0xlcaff_snd_zero {τ : Tag} : (0 : AffPair τ).2 = 0 := rfl

@[simp] private lemma lk0xlcaff_fst_sum {τ : Tag} {ι : Type*} (s : Finset ι)
    (f : ι → AffPair τ) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 :=
  map_sum ({ toFun := Prod.fst, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    AffPair τ →+ (Fin τ.rank → ℤ)) f s

@[simp] private lemma lk0xlcaff_snd_sum {τ : Tag} {ι : Type*} (s : Finset ι)
    (f : ι → AffPair τ) : (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 :=
  map_sum ({ toFun := Prod.snd, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    AffPair τ →+ ℤ) f s

private lemma lk0xlcaff_height_add {τ : Tag} (u v : Fin τ.rank → ℤ) :
    height (u + v) = height u + height v := by
  simp only [height, Pi.add_apply, Finset.sum_add_distrib]

private lemma lk0xlcaff_height_smul {τ : Tag} (c : ℤ) (v : Fin τ.rank → ℤ) :
    height (c • v) = c * height v := by
  simp only [height]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.smul_apply]
  ring

private lemma lk0xlcaff_height_sum {τ : Tag} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Fin τ.rank → ℤ) : height (∑ i ∈ s, f i) = ∑ i ∈ s, height (f i) := by
  induction s using Finset.induction with
  | empty => simp [height]
  | insert a s ha ih => simp [Finset.sum_insert ha, lk0xlcaff_height_add, ih]

private lemma lk0xlcaff_sum_smul_single {τ : Tag} (g : Fin τ.rank → ℕ) (i : Fin τ.rank) :
    (∑ x, (g x : ℤ) • (Pi.single x (1 : ℤ) : Fin τ.rank → ℤ)) i = (g i : ℤ) := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    rw [Pi.smul_apply]
    simp [Pi.single_apply, hx]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma lk0xlcaff_snd_decomp {τ : Tag} (n0 : ℕ) (n : Fin τ.rank → ℕ) :
    ((n0 : ℤ) • extAff τ + ∑ j, (n j : ℤ) • simpleAff j : AffPair τ).2 = (n0 : ℤ) := by
  rw [lk0xlcaff_snd_add, lk0xlcaff_snd_smul, lk0xlcaff_snd_sum]
  simp [extAff, simpleAff]

private lemma lk0xlcaff_coord_decomp {τ : Tag} (n0 : ℕ) (n : Fin τ.rank → ℕ) (i : Fin τ.rank) :
    (((n0 : ℤ) • extAff τ + ∑ j, (n j : ℤ) • simpleAff j : AffPair τ).1 i) +
      ((n0 : ℤ) • extAff τ + ∑ j, (n j : ℤ) • simpleAff j : AffPair τ).2 * (hr τ i : ℤ)
      = (n i : ℤ) := by
  have h1 : ((n0 : ℤ) • extAff τ).1 = -((n0 : ℤ) • theta τ) := by
    rw [lk0xlcaff_fst_smul]; simp [extAff]
  have h2 : ((n0 : ℤ) • extAff τ).2 = (n0 : ℤ) := by
    rw [lk0xlcaff_snd_smul]; simp [extAff]
  have h3 : ((∑ j, (n j : ℤ) • simpleAff j : AffPair τ)).1
      = ∑ j, (n j : ℤ) • (Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) := by
    rw [lk0xlcaff_fst_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [lk0xlcaff_fst_smul]; rfl
  have h4 : ((∑ j, (n j : ℤ) • simpleAff j : AffPair τ)).2 = 0 := by
    rw [lk0xlcaff_snd_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [lk0xlcaff_snd_smul]
    simp [simpleAff]
  rw [lk0xlcaff_fst_add, lk0xlcaff_snd_add, h1, h2, h3, h4]
  rw [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, lk0xlcaff_sum_smul_single n i]
  simp only [theta, zsmul_eq_mul, Int.cast_id]
  ring

private lemma lk0xlcaff_coord_of_decomp {τ : Tag} {b : AffPair τ} {n0 : ℕ}
    {n : Fin τ.rank → ℕ} (h : b = (n0 : ℤ) • extAff τ + ∑ i, (n i : ℤ) • simpleAff i)
    (i : Fin τ.rank) : b.1 i + b.2 * (hr τ i : ℤ) = (n i : ℤ) := by
  rw [h]
  exact lk0xlcaff_coord_decomp n0 n i

private lemma lk0xlcaff_eq_of_snd_and_coord {τ : Tag} {b b' : AffPair τ}
    (h2 : b.2 = b'.2)
    (h1 : ∀ i, b.1 i + b.2 * (hr τ i : ℤ) = b'.1 i + b'.2 * (hr τ i : ℤ)) :
    b = b' := by
  apply Prod.ext
  · funext i
    have := h1 i
    rw [h2] at this
    linarith
  · exact h2

private lemma lk0xlcaff_affPos_snd_nonneg {τ : Tag} {a : AffPair τ} (h : AffPos a) :
    0 ≤ a.2 := by
  rcases h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h.symm

private lemma lk0xlcaff_affPos_height_pos_of_snd_eq_zero {τ : Tag} {a : AffPair τ}
    (h : AffPos a) (h2 : a.2 = 0) : 0 < height a.1 := by
  rcases h with h | ⟨_, hh⟩
  · omega
  · exact hh

theorem affNeg_iff_affPos_neg {τ : Tag} (a : AffPair τ) : AffNeg a ↔ AffPos (-a) := by
  obtain ⟨γ, k⟩ := a
  simp [AffNeg, AffPos, height_neg]

theorem affPos_iff_not_affNeg
    {τ : Tag} {a : AffPair τ} (ha : IsRoot τ a.1) :
    AffPos a ↔ ¬ AffNeg a := by
  obtain ⟨γ, k⟩ := a
  have hne := ha.height_ne_zero
  rw [AffPos, AffNeg]
  constructor
  · rintro (hk | ⟨hk, hh⟩) (hk' | ⟨hk', hh'⟩)
    all_goals omega
  · intro h
    push Not at h
    omega

theorem aff_pos_decomp
    {τ : Tag} (hT : KacBox τ) {a : AffPair τ} (ha : IsRoot τ a.1)
    (hpos : AffPos a) :
    ∃ (n0 : ℕ) (n : Fin τ.rank → ℕ),
      a = (n0 : ℤ) • extAff τ + ∑ i, (n i : ℤ) • simpleAff i ∧ (n0 ≠ 0 ∨ ∃ i, n i ≠ 0) := by
  obtain ⟨γ, k⟩ := a
  have hk_nonneg : 0 ≤ k := lk0xlcaff_affPos_snd_nonneg hpos
  have hcoord : ∀ i, 0 ≤ γ i + k * (hr τ i : ℤ) := by
    intro i
    rcases hpos with hk | ⟨hk, hh⟩
    · have hlow := (hT.1 γ ha i).1
      have hk1 : (1 : ℤ) ≤ k := by omega
      have hri : (0 : ℤ) ≤ (hr τ i : ℤ) := by omega
      have hmul : (hr τ i : ℤ) ≤ k * (hr τ i : ℤ) := by
        calc (hr τ i : ℤ) = 1 * (hr τ i : ℤ) := by ring
          _ ≤ k * (hr τ i : ℤ) := mul_le_mul_of_nonneg_right hk1 hri
      linarith
    · subst hk
      have hh' := (IsRoot.height_pos_iff ha).1 hh
      simpa using hh' i
  have hcast : ∀ i, (((γ i + k * (hr τ i : ℤ)).toNat : ℕ) : ℤ) = γ i + k * (hr τ i : ℤ) :=
    fun i => Int.toNat_of_nonneg (hcoord i)
  have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
  refine ⟨k.toNat, fun i => (γ i + k * (hr τ i : ℤ)).toNat, ?_, ?_⟩
  · apply lk0xlcaff_eq_of_snd_and_coord
    · rw [lk0xlcaff_snd_decomp]; exact hkcast.symm
    · intro i
      rw [← hcast i,
        lk0xlcaff_coord_decomp k.toNat (fun j => (γ j + k * (hr τ j : ℤ)).toNat) i]
  · by_cases hn0 : k.toNat = 0
    · right
      have hk0 : k = 0 := by
        have h0 : ((k.toNat : ℕ) : ℤ) = 0 := by simp [hn0]
        rwa [hkcast] at h0
      have hh : 0 < height γ := by
        rcases hpos with h | ⟨_, hh⟩
        · omega
        · exact hh
      obtain ⟨j, hj⟩ : ∃ j, γ j ≠ 0 := by
        by_contra h
        push Not at h
        exact ha.ne_zero (funext fun j => h j)
      refine ⟨j, ?_⟩
      have hposj : 0 < γ j := by
        have hnn := (IsRoot.height_pos_iff ha).1 hh j
        exact lt_of_le_of_ne hnn (Ne.symm hj)
      intro hcon
      have hzero : γ j + k * (hr τ j : ℤ) = 0 := by
        have h0 : (((γ j + k * (hr τ j : ℤ)).toNat : ℕ) : ℤ) = 0 := by simp [hcon]
        rwa [hcast j] at h0
      rw [hk0] at hzero
      simp at hzero
      omega
    · exact Or.inl hn0

theorem aff_pos_of_ncoord_pos
    {τ : Tag} (hT : KacBox τ) {a : AffPair τ}
    (ha : IsRoot τ a.1) {i : Fin τ.rank} (hi : 0 < a.1 i + a.2 * (hr τ i : ℤ)) : AffPos a := by
  rw [affPos_iff_not_affNeg ha]
  intro hneg
  have hpos' : AffPos (-a) := (affNeg_iff_affPos_neg a).1 hneg
  have hroot : IsRoot τ (-a).1 := by simpa [lk0xlcaff_fst_neg] using IsRoot.neg ha
  obtain ⟨n0, n, hdec, -⟩ := aff_pos_decomp hT hroot hpos'
  have hc := lk0xlcaff_coord_of_decomp hdec i
  have hnn : (0 : ℤ) ≤ (n i : ℤ) := by omega
  have hnegcoord : (-a).1 i + (-a).2 * (hr τ i : ℤ) =
      -(a.1 i + a.2 * (hr τ i : ℤ)) := by
    simp only [lk0xlcaff_fst_neg, lk0xlcaff_snd_neg, Pi.neg_apply]
    ring
  rw [hnegcoord] at hc
  omega

theorem exists_ncoord_pos_of_ne_ext
    {τ : Tag} (hT : KacBox τ) {a : AffPair τ}
    (ha : IsRoot τ a.1) (hpos : AffPos a) (hne : a ≠ extAff τ) :
    ∃ i, 0 < a.1 i + a.2 * (hr τ i : ℤ) := by
  obtain ⟨n0, n, hdec, hne'⟩ := aff_pos_decomp hT ha hpos
  by_cases hex : ∃ i, n i ≠ 0
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    have hc := lk0xlcaff_coord_of_decomp hdec i
    have hposn : 0 < (n i : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hi
    linarith
  · push Not at hex
    have hn0 : n0 ≠ 0 := by
      rcases hne' with h | ⟨i, hi⟩
      · exact h
      · exact absurd (hex i) hi
    have ha_eq : a = (n0 : ℤ) • extAff τ := by
      have hsum : ∑ i, (n i : ℤ) • simpleAff i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hex i]
        simp
      rw [hdec, hsum, add_zero]
    have ha1 : a.1 = -((n0 : ℤ) • theta τ) := by
      rw [ha_eq]
      simp [extAff, theta]
    obtain ⟨w, j, -⟩ := isRoot_iff_exists_smul_single.1 hT.2.1
    have hj : (0 : ℤ) < (hr τ j : ℤ) := by exact_mod_cast hT.2.2 j
    have hroot : IsRoot τ ((n0 : ℤ) • theta τ) := by
      simpa [ha1] using IsRoot.neg ha
    have hb := (hT.1 ((n0 : ℤ) • theta τ) hroot j).2
    have hb' : (n0 : ℤ) * (hr τ j : ℤ) ≤ (hr τ j : ℤ) := by
      simpa [Pi.smul_apply, theta] using hb
    have hn0eq : n0 = 1 := by
      have h1 : (n0 : ℤ) ≤ 1 := by nlinarith
      omega
    exact absurd (by rw [ha_eq, hn0eq]; simp) hne

theorem affPos_combo {τ : Tag} (n0 : ℕ) (n : Fin τ.rank → ℕ) {x0 : AffPair τ}
    {x : Fin τ.rank → AffPair τ} (h0 : AffPos x0) (hx : ∀ i, AffPos (x i))
    (hne : n0 ≠ 0 ∨ ∃ i, n i ≠ 0) : AffPos ((n0 : ℤ) • x0 + ∑ i, (n i : ℤ) • x i) := by
  set Y : AffPair τ := (n0 : ℤ) • x0 + ∑ i, (n i : ℤ) • x i with hY
  have hY2 : Y.2 = (n0 : ℤ) * x0.2 + ∑ i, (n i : ℤ) * (x i).2 := by
    rw [hY]; simp [zsmul_eq_mul]
  have hY2nn : 0 ≤ Y.2 := by
    rw [hY2]
    exact add_nonneg (mul_nonneg (by omega) (lk0xlcaff_affPos_snd_nonneg h0))
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (by omega) (lk0xlcaff_affPos_snd_nonneg (hx i)))
  rcases lt_or_eq_of_le hY2nn with hpos | heq
  · exact Or.inl hpos
  · right
    have hzero : Y.2 = 0 := heq.symm
    have hsum2nn : 0 ≤ ∑ i, (n i : ℤ) * (x i).2 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (by omega) (lk0xlcaff_affPos_snd_nonneg (hx i))
    have hT00 : (n0 : ℤ) * x0.2 = 0 := by
      have hle : (n0 : ℤ) * x0.2 ≤ Y.2 := by
        rw [hY2]; exact le_add_of_nonneg_right hsum2nn
      have hnn : 0 ≤ (n0 : ℤ) * x0.2 :=
        mul_nonneg (by omega) (lk0xlcaff_affPos_snd_nonneg h0)
      linarith
    have hTi0 : ∀ i, (n i : ℤ) * (x i).2 = 0 := by
      intro i
      have h1 : (n i : ℤ) * (x i).2 ≤ ∑ j, (n j : ℤ) * (x j).2 :=
        Finset.single_le_sum
          (fun j _ => mul_nonneg (by omega) (lk0xlcaff_affPos_snd_nonneg (hx j)))
          (Finset.mem_univ i)
      have hle : (n i : ℤ) * (x i).2 ≤ Y.2 := by
        rw [hY2]
        linarith [mul_nonneg (by omega) (lk0xlcaff_affPos_snd_nonneg h0)]
      have hnn : 0 ≤ (n i : ℤ) * (x i).2 :=
        mul_nonneg (by omega) (lk0xlcaff_affPos_snd_nonneg (hx i))
      linarith
    have hY1 : Y.1 = (n0 : ℤ) • x0.1 + ∑ i, (n i : ℤ) • (x i).1 := by
      rw [hY]; simp
    have hheight : height Y.1 =
        (n0 : ℤ) * height x0.1 + ∑ i, (n i : ℤ) * height (x i).1 := by
      rw [hY1, lk0xlcaff_height_add, lk0xlcaff_height_smul, lk0xlcaff_height_sum]
      exact congrArg (fun t => (n0 : ℤ) * height x0.1 + t)
        (Finset.sum_congr rfl fun i _ => lk0xlcaff_height_smul (n i : ℤ) (x i).1)
    have hterm0' : 0 ≤ (n0 : ℤ) * height x0.1 := by
      by_cases hn0 : n0 = 0
      · simp [hn0]
      · have hx02 : x0.2 = 0 := by
          have := hT00
          exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hn0)
        have hp := lk0xlcaff_affPos_height_pos_of_snd_eq_zero h0 hx02
        exact mul_nonneg (by omega) (le_of_lt hp)
    have htermi' : ∀ i, 0 ≤ (n i : ℤ) * height (x i).1 := by
      intro i
      by_cases hni : n i = 0
      · simp [hni]
      · have hxi2 : (x i).2 = 0 := by
          have := hTi0 i
          exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hni)
        have hp := lk0xlcaff_affPos_height_pos_of_snd_eq_zero (hx i) hxi2
        exact mul_nonneg (by omega) (le_of_lt hp)
    refine ⟨hzero, ?_⟩
    rw [hheight]
    rcases hne with hn0 | ⟨i, hi⟩
    · have hpos0 : 0 < (n0 : ℤ) * height x0.1 := by
        have hx02 : x0.2 = 0 := by
          have := hT00
          exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hn0)
        have hp := lk0xlcaff_affPos_height_pos_of_snd_eq_zero h0 hx02
        exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) hp
      have hsum : 0 ≤ ∑ i, (n i : ℤ) * height (x i).1 :=
        Finset.sum_nonneg (fun i _ => htermi' i)
      linarith
    · have hposi : 0 < (n i : ℤ) * height (x i).1 := by
        have hxi2 : (x i).2 = 0 := by
          have := hTi0 i
          exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hi)
        have hp := lk0xlcaff_affPos_height_pos_of_snd_eq_zero (hx i) hxi2
        exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) hp
      have hle : (n i : ℤ) * height (x i).1 ≤ ∑ j, (n j : ℤ) * height (x j).1 :=
        Finset.single_le_sum (fun j _ => htermi' j) (Finset.mem_univ i)
      linarith [hterm0']

end CFSG.StandardType.GGK0LC

end
