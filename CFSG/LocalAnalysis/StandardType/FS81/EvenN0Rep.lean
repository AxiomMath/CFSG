module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainBasic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def evenN0Rep (n : ℕ) (z : Bool) (k : ℕ) (ε : ZMod 3) : Fin (n + 1) → ZMod 3 :=
  fun i => if i = 0 then (if z then 0 else 1) else
    if (i : ℕ) ≤ k then (if (i : ℕ) = n then ε else 1) else 0

namespace EvenN0Rep

def support {n : ℕ} (v : Fin (n + 1) → ZMod 3) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => i ≠ 0 ∧ v i ≠ 0

def initSeg (n k : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ k

def sign {n : ℕ} (v : Fin (n + 1) → ZMod 3) (S : Finset (Fin (n + 1)))
    (j₀ : Fin (n + 1)) (P : ZMod 3) : Fin (n + 1) → ZMod 3 :=
  fun x => if x = 0 then (if v 0 = 0 then 1 else v 0) else
    (if x ∈ S then v x else 1) * (if x = j₀ then P else 1)

theorem wt_le {k : ℕ} (e : Coords k) : wt e ≤ k := by
  unfold wt
  simpa using Finset.card_le_univ (Finset.univ.filter fun i => e i ≠ 0)

theorem card_support {n : ℕ} (v : Fin (n + 1) → ZMod 3) :
    (support v).card = wt (fun i : Fin n => v i.succ) := by
  rw [support, Fin.card_filter_univ_succ, if_neg (by simp)]
  simp [wt]

theorem card_initSeg {n k : ℕ} (hk : k ≤ n) : (initSeg n k).card = k := by
  have h : initSeg n k =
      (Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) < k + 1).erase 0 := by
    ext i
    rw [initSeg, Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, Nat.lt_succ_iff.mpr h2⟩
      rintro rfl
      simp at h1
    · rintro ⟨hne, hlt⟩
      exact ⟨Nat.one_le_iff_ne_zero.mpr fun h0 => hne (Fin.ext h0),
        Nat.lt_succ_iff.mp hlt⟩
  rw [h, Finset.card_erase_of_mem, Fin.card_filter_val_lt]
  · omega
  · simp

theorem mem_swap_zero_iff {n : ℕ} {T : Finset (Fin (n + 1))} {a b : Fin (n + 1)}
    (h0 : (0 : Fin (n + 1)) ∉ T) (ha : a ∉ T) :
    Equiv.swap 0 a b ∈ T ↔ b ∈ T := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h ha, fun h => absurd h h0⟩
  · subst h2
    exact ⟨fun h => absurd h h0, fun h => absurd h ha⟩
  · exact Iff.rfl

theorem exists_perm_maps_support {n : ℕ} (v : Fin (n + 1) → ZMod 3) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), σ 0 = 0 ∧
      ∀ x, x ∈ support v ↔
        σ x ∈ initSeg n (wt (fun i : Fin n => v i.succ)) := by
  classical
  set k := wt (fun i : Fin n => v i.succ) with hk
  have hmemS : ∀ i, i ∈ support v ↔ i ≠ 0 ∧ v i ≠ 0 := fun i => by
    simp [support]
  have hmemT : ∀ i, i ∈ initSeg n k ↔ 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ k := fun i => by
    simp [initSeg]
  have hkS : (support v).card = k := by
    rw [hk]; exact card_support v
  have hkle : k ≤ n := by rw [hk]; exact wt_le _
  have hTc : (initSeg n k).card = k := card_initSeg hkle
  have hST : Fintype.card {x // x ∈ support v} =
      Fintype.card {x // x ∈ initSeg n k} := by
    rw [Fintype.card_coe, Fintype.card_coe, hkS, hTc]
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : Equiv.Perm (Fin (n + 1)),
      σ₁ = (Fintype.equivOfCardEq hST).extendSubtype := ⟨_, rfl⟩
  have hσ₁S : ∀ x, x ∈ support v ↔ σ₁ x ∈ initSeg n k := fun x => by
    constructor
    · intro hx
      rw [hσ₁]
      exact Equiv.extendSubtype_mem _ x hx
    · intro hx
      by_contra hx'
      rw [hσ₁] at hx
      exact Equiv.extendSubtype_not_mem _ x hx' hx
  have h0S : (0 : Fin (n + 1)) ∉ support v := fun h => ((hmemS 0).mp h).1 rfl
  have h0T : (0 : Fin (n + 1)) ∉ initSeg n k := fun h => by
    have := ((hmemT 0).mp h).1
    simp at this
  refine ⟨Equiv.swap 0 (σ₁ 0) * σ₁, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  · intro x
    rw [Equiv.Perm.mul_apply, hσ₁S x,
      mem_swap_zero_iff h0T (fun h => h0S ((hσ₁S 0).mpr h))]

theorem exists_absorbing_coord {n k : ℕ} (hn : 0 < n) (hkle : k ≤ n)
    {v : Fin (n + 1) → ZMod 3} {σ : Equiv.Perm (Fin (n + 1))}
    {S T : Finset (Fin (n + 1))} (hmemS : ∀ i, i ∈ S ↔ i ≠ 0 ∧ v i ≠ 0)
    (hmemT : ∀ i, i ∈ T ↔ 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ k) (hkS : S.card = k)
    (hσS : ∀ x, x ∈ S ↔ σ x ∈ T) :
    ∃ j₀ : Fin (n + 1), j₀ ≠ 0 ∧ (j₀ ∈ S → σ j₀ = Fin.last n) ∧
      (k = n → σ j₀ = Fin.last n) := by
  by_cases hk : k = n
  · refine ⟨σ.symm (Fin.last n), ?_, fun _ => by simp, fun _ => by simp⟩
    intro h
    have hlast : σ (σ.symm (Fin.last n)) ∈ T := by
      rw [Equiv.apply_symm_apply, hmemT]
      refine ⟨?_, ?_⟩
      · simp only [Fin.val_last]; omega
      · simp only [Fin.val_last]; omega
    have h0S : (0 : Fin (n + 1)) ∈ S := by
      rw [← h]
      exact (hσS _).mpr hlast
    exact ((hmemS 0).mp h0S).1 rfl
  · have hlt : k < n := lt_of_le_of_ne hkle hk
    obtain ⟨j₀, hj₀, hj₀'⟩ : ∃ j₀ : Fin (n + 1), j₀ ≠ 0 ∧ j₀ ∉ S := by
      by_contra hall
      push Not at hall
      have hsub : Finset.univ.erase 0 ⊆ S := fun x hx => hall x (Finset.ne_of_mem_erase hx)
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        hkS] at this
      omega
    exact ⟨j₀, hj₀, fun h => absurd h hj₀', fun h => absurd h hk⟩

theorem prod_support_mul_self {n : ℕ} {v : Fin (n + 1) → ZMod 3}
    {S : Finset (Fin (n + 1))} (hmemS : ∀ i, i ∈ S ↔ i ≠ 0 ∧ v i ≠ 0) :
    (∏ x, (if x ∈ S then v x else 1)) * (∏ x, (if x ∈ S then v x else 1)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun x _ => ?_
  by_cases hx : x ∈ S
  · rw [if_pos hx]
    exact mul_self_of_ne_zero ((hmemS x).mp hx).2
  · rw [if_neg hx]
    rfl

theorem mem_iff_ne_zero_of_card {n : ℕ} {S : Finset (Fin (n + 1))}
    (h0S : (0 : Fin (n + 1)) ∉ S) (hcard : S.card = n) : ∀ x, x ∈ S ↔ x ≠ 0 := by
  intro x
  have hsub : S ⊆ Finset.univ.erase 0 := fun y hy =>
    Finset.mem_erase.mpr ⟨by rintro rfl; exact h0S hy, Finset.mem_univ _⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      hcard]
    omega)
  rw [heq, Finset.mem_erase]
  simp

theorem prod_support_eq_prod_succ {n : ℕ} {v : Fin (n + 1) → ZMod 3}
    {S : Finset (Fin (n + 1))} (h0S : (0 : Fin (n + 1)) ∉ S)
    (hS : ∀ x, x ∈ S ↔ x ≠ 0) :
    (∏ x, (if x ∈ S then v x else 1)) = ∏ i : Fin n, v i.succ := by
  rw [Fin.prod_univ_succ (n := n), if_neg h0S, one_mul]
  exact Finset.prod_congr rfl fun i _ => if_pos ((hS _).mpr (Fin.succ_ne_zero i))

theorem sign_isSign {n : ℕ} {v : Fin (n + 1) → ZMod 3}
    {S : Finset (Fin (n + 1))} {j₀ : Fin (n + 1)} {P : ZMod 3}
    (hmemS : ∀ i, i ∈ S ↔ i ≠ 0 ∧ v i ≠ 0) (hP : P = 1 ∨ P = -1) :
    IsSign (sign v S j₀ P) := by
  intro x
  unfold sign
  by_cases hx : x = 0
  · rw [if_pos hx]
    by_cases hv : v 0 = 0
    · rw [if_pos hv]; exact Or.inl rfl
    · rw [if_neg hv]; exact eq_one_or_of_ne_zero hv
  · rw [if_neg hx]
    have h1 : (if x ∈ S then v x else 1) = 1 ∨ (if x ∈ S then v x else 1) = -1 := by
      by_cases hxS : x ∈ S
      · rw [if_pos hxS]; exact eq_one_or_of_ne_zero ((hmemS x).mp hxS).2
      · rw [if_neg hxS]; exact Or.inl rfl
    have h2 : (if x = j₀ then P else 1) = 1 ∨ (if x = j₀ then P else 1) = -1 := by
      by_cases hxj : x = j₀
      · rw [if_pos hxj]; exact hP
      · rw [if_neg hxj]; exact Or.inl rfl
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> decide

theorem prod_sign {n : ℕ} {v : Fin (n + 1) → ZMod 3}
    {S : Finset (Fin (n + 1))} {j₀ : Fin (n + 1)} {P : ZMod 3}
    (h0S : (0 : Fin (n + 1)) ∉ S) (hj₀0 : j₀ ≠ 0)
    (hP : P = ∏ x, (if x ∈ S then v x else 1)) (hPP : P * P = 1) :
    ∏ i : Fin n, sign v S j₀ P i.succ = 1 := by
  have e : ∏ i : Fin n, sign v S j₀ P i.succ =
      ∏ x : Fin (n + 1), ((if x ∈ S then v x else 1) * (if x = j₀ then P else 1)) := by
    rw [Fin.prod_univ_succ (n := n), if_neg h0S, if_neg (Ne.symm hj₀0), one_mul, one_mul]
    exact Finset.prod_congr rfl fun i _ => by
      unfold sign
      rw [if_neg (Fin.succ_ne_zero i)]
  rw [e, Finset.prod_mul_distrib, ← hP, Finset.prod_ite_eq' Finset.univ j₀,
    if_pos (Finset.mem_univ _), hPP]

theorem sign_mul_apply_of_ne_zero {n : ℕ} {v : Fin (n + 1) → ZMod 3}
    {S : Finset (Fin (n + 1))} {j₀ : Fin (n + 1)} {P : ZMod 3}
    (hmemS : ∀ i, i ∈ S ↔ i ≠ 0 ∧ v i ≠ 0) {x : Fin (n + 1)} (hx : x ≠ 0) :
    sign v S j₀ P x * v x = if x ∈ S then (if x = j₀ then P else 1) else 0 := by
  unfold sign
  rw [if_neg hx]
  by_cases hxS : x ∈ S
  · rw [if_pos hxS, if_pos hxS]
    have hv : v x ≠ 0 := ((hmemS x).mp hxS).2
    calc (v x * (if x = j₀ then P else 1)) * v x
        = (v x * v x) * (if x = j₀ then P else 1) := by ring
      _ = 1 * (if x = j₀ then P else 1) := by rw [mul_self_of_ne_zero hv]
      _ = _ := one_mul _
  · rw [if_neg hxS, if_neg hxS]
    have hv : v x = 0 := by
      by_contra h
      exact hxS ((hmemS x).mpr ⟨hx, h⟩)
    rw [hv, mul_zero]

theorem sign_mul_apply_zero {n : ℕ} {v : Fin (n + 1) → ZMod 3}
    {S : Finset (Fin (n + 1))} {j₀ : Fin (n + 1)} {P : ZMod 3} :
    sign v S j₀ P 0 * v 0 = if decide (v 0 = 0) then 0 else 1 := by
  unfold sign
  rw [if_pos rfl]
  by_cases hv : v 0 = 0
  · rw [if_pos hv, hv, mul_zero, if_pos (by simp)]
  · rw [if_neg hv, if_neg (by simpa using hv)]
    exact mul_self_of_ne_zero hv

theorem sign_mul_apply_eq_rep_of_ne_zero {n k : ℕ} (hkle : k ≤ n)
    {v : Fin (n + 1) → ZMod 3} {ε P : ZMod 3} {S T : Finset (Fin (n + 1))}
    {σ : Equiv.Perm (Fin (n + 1))} {j₀ : Fin (n + 1)}
    (hmemS : ∀ i, i ∈ S ↔ i ≠ 0 ∧ v i ≠ 0)
    (hmemT : ∀ i, i ∈ T ↔ 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ k)
    (hσ0 : σ 0 = 0) (hσS : ∀ x, x ∈ S ↔ σ x ∈ T)
    (hj₀S : j₀ ∈ S → σ j₀ = Fin.last n) (hj₀n : k = n → σ j₀ = Fin.last n)
    (hPeps : k = n → P = ε) {i : Fin (n + 1)} (hi : i ≠ 0) :
    sign v S j₀ P (σ.symm i) * v (σ.symm i) =
      evenN0Rep n (decide (v 0 = 0)) k ε i := by
  have hy : σ.symm i ≠ 0 := fun h => hi (by rw [← Equiv.apply_symm_apply σ i, h, hσ0])
  have hiy : σ (σ.symm i) = i := Equiv.apply_symm_apply σ i
  rw [sign_mul_apply_of_ne_zero hmemS hy]
  unfold evenN0Rep
  rw [if_neg hi]
  by_cases hyS : σ.symm i ∈ S
  · have hiT : i ∈ T := hiy ▸ (hσS _).mp hyS
    rw [if_pos hyS, if_pos ((hmemT i).mp hiT).2]
    by_cases hyj : σ.symm i = j₀
    · have hlast : σ j₀ = Fin.last n := hj₀S (hyj ▸ hyS)
      have hi_last : i = Fin.last n := by rw [← hiy, hyj, hlast]
      have hk : k = n := by
        have hle : (i : ℕ) ≤ k := ((hmemT i).mp hiT).2
        have hval : (i : ℕ) = n := by rw [hi_last]; simp
        omega
      rw [if_pos hyj, if_pos (by rw [hi_last]; simp)]
      exact hPeps hk
    · rw [if_neg hyj, if_neg]
      intro hval
      have hi_last : i = Fin.last n := Fin.ext (by simpa using hval)
      have hk : k = n := by
        have hle : (i : ℕ) ≤ k := ((hmemT i).mp hiT).2
        omega
      exact hyj (by rw [hi_last, ← hj₀n hk, Equiv.symm_apply_apply])
  · have hiT : i ∉ T := fun h => hyS ((hσS _).mpr (hiy.symm ▸ h))
    rw [if_neg hyS, if_neg]
    intro hle
    have h1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h => hi (Fin.ext h)
    exact hiT ((hmemT i).mpr ⟨h1, hle⟩)

theorem exists_mulVec_eq_rep_zero (v : Fin 1 → ZMod 3) :
    ∃ M ∈ evenN0 0, M *ᵥ v =
      evenN0Rep 0 (decide (v 0 = 0)) (wt (fun i : Fin 0 => v i.succ))
        (∏ i : Fin 0, v i.succ) := by
  let s : Fin 1 → ZMod 3 := fun _ => if v 0 = 0 then 1 else v 0
  refine ⟨spMat 1 s, ⟨1, s, ?_, ⟨by simp, by simp⟩, rfl⟩, ?_⟩
  · intro i
    fin_cases i
    dsimp only [s]
    by_cases hv : v 0 = 0
    · rw [if_pos hv]; exact Or.inl rfl
    · rw [if_neg hv]; exact eq_one_or_of_ne_zero hv
  · rw [spMat_mulVec]
    funext i
    have hi : i = 0 := Fin.ext (by
      have h := i.isLt
      omega)
    subst hi
    dsimp only [s]
    rw [show ((1 : Equiv.Perm (Fin 1))).symm 0 = 0 from rfl]
    by_cases hv : v 0 = 0
    · rw [if_pos hv, hv, mul_zero]
      unfold evenN0Rep
      simp
    · rw [if_neg hv, mul_self_of_ne_zero hv]
      unfold evenN0Rep
      simp [hv]

end EvenN0Rep

theorem wt_eq_wt_succ {n : ℕ} {e : Coords (n + 1)} (he : e 0 = 0) :
    wt e = wt (fun i : Fin n => e i.succ) := by
  unfold wt
  have hm : (Finset.univ.filter fun i : Fin (n + 1) => e i ≠ 0) =
      (Finset.univ.filter fun i : Fin n => e i.succ ≠ 0).image Fin.succ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      have hj0 : j ≠ 0 := by rintro rfl; exact hj he
      exact ⟨j.pred hj0, by rwa [Fin.succ_pred], Fin.succ_pred j hj0⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [hm, Finset.card_image_of_injective _ (Fin.succ_injective n)]

theorem exists_evenN0_mulVec_eq_rep (n : ℕ) (v : Fin (n + 1) → ZMod 3) :
    ∃ M ∈ evenN0 n, M *ᵥ v =
      evenN0Rep n (decide (v 0 = 0)) (wt (fun i : Fin n => v i.succ)) (∏ i : Fin n, v i.succ) := by
  classical
  by_cases hn : n = 0
  · subst hn
    exact EvenN0Rep.exists_mulVec_eq_rep_zero v
  · set k := wt (fun i : Fin n => v i.succ) with hk
    set ε := ∏ i : Fin n, v i.succ with hε
    obtain ⟨σ, hσ0, hσS⟩ := EvenN0Rep.exists_perm_maps_support v
    have hσS' : ∀ x, x ∈ EvenN0Rep.support v ↔ σ x ∈ EvenN0Rep.initSeg n k := by
      intro x
      rw [hk]
      exact hσS x
    have hmemS : ∀ i, i ∈ EvenN0Rep.support v ↔ i ≠ 0 ∧ v i ≠ 0 := fun i => by
      simp [EvenN0Rep.support]
    have hmemT : ∀ i, i ∈ EvenN0Rep.initSeg n k ↔ 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ k := fun i => by
      simp [EvenN0Rep.initSeg]
    have hkS : (EvenN0Rep.support v).card = k := by
      rw [hk]; exact EvenN0Rep.card_support v
    have hkle : k ≤ n := by rw [hk]; exact EvenN0Rep.wt_le _
    obtain ⟨j₀, hj₀0, hj₀S, hj₀n⟩ :=
      EvenN0Rep.exists_absorbing_coord (Nat.pos_of_ne_zero hn) hkle hmemS hmemT hkS hσS'
    set P := ∏ x, (if x ∈ EvenN0Rep.support v then v x else 1) with hP
    have hPP : P * P = 1 := by rw [hP]; exact EvenN0Rep.prod_support_mul_self hmemS
    have h0S : (0 : Fin (n + 1)) ∉ EvenN0Rep.support v := fun h => ((hmemS 0).mp h).1 rfl
    have hPeps : k = n → P = ε := by
      intro hkn
      have hS : ∀ x, x ∈ EvenN0Rep.support v ↔ x ≠ 0 :=
        EvenN0Rep.mem_iff_ne_zero_of_card h0S (by rw [hkS, hkn])
      rw [hP, hε]
      exact EvenN0Rep.prod_support_eq_prod_succ h0S hS
    have hP1 : P = 1 ∨ P = -1 :=
      eq_one_or_of_ne_zero fun h0 => by rw [h0, zero_mul] at hPP; exact zero_ne_one hPP
    have hsign : IsSign (EvenN0Rep.sign v (EvenN0Rep.support v) j₀ P) :=
      EvenN0Rep.sign_isSign hmemS hP1
    have hprod : ∏ i : Fin n, EvenN0Rep.sign v (EvenN0Rep.support v) j₀ P i.succ = 1 :=
      EvenN0Rep.prod_sign h0S hj₀0 hP hPP
    refine ⟨spMat σ (EvenN0Rep.sign v (EvenN0Rep.support v) j₀ P),
      ⟨σ, _, hsign, ⟨hσ0, hprod⟩, rfl⟩, ?_⟩
    rw [spMat_mulVec]
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [show σ.symm 0 = 0 from by rw [Equiv.symm_apply_eq, hσ0]]
      exact EvenN0Rep.sign_mul_apply_zero
    · exact EvenN0Rep.sign_mul_apply_eq_rep_of_ne_zero hkle hmemS hmemT hσ0 hσS'
        hj₀S hj₀n hPeps hi

end CFSG.StandardType.FrameRoute.FS81
