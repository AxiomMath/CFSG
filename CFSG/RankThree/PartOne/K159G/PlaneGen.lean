module

public import CFSG.RankThree.PartOne.KF.U4Blk
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.K159G

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.RankThree.PartOne.KFU
  CFSG.LinearGroups CFSG.RankThree.PartOne.KCUnitaryModel

section Action

variable {n : ℕ} {K : Type} [Field K]

theorem coordEmbed_mulVec {i j : Fin n} (hij : i ≠ j) (X : Matrix (Fin 2) (Fin 2) K)
    (v : Fin n → K) (k : Fin n) :
    (coordEmbed K i j X *ᵥ v) k =
      if k = i then X 0 0 * v i + X 0 1 * v j
      else if k = j then X 1 0 * v i + X 1 1 * v j else v k := by
  have h1 : (coordProj K i j *ᵥ v) = ![v i, v j] := by
    ext a
    have : ∀ c : Fin n, (∑ x, (if x = c then (1 : K) else 0) * v x) = v c := by
      intro c
      simp [ite_mul, Finset.sum_ite_eq']
    fin_cases a
    · simp [coordProj, coordIncl, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact this i
    · simp [coordProj, coordIncl, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have h2 : ∀ w : Fin 2 → K, (coordIncl K i j *ᵥ w) k =
      if k = i then w 0 else if k = j then w 1 else 0 := by
    intro w
    simp only [coordIncl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
    by_cases hk : k = i
    · subst hk; simp [hij]
    · by_cases hk' : k = j
      · subst hk'; simp [hk]
      · simp [hk, hk']
  have h3 : coordEmbed K i j X *ᵥ v =
      v + coordIncl K i j *ᵥ ((X - 1) *ᵥ (coordProj K i j *ᵥ v)) := by
    unfold coordEmbed
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h3, Pi.add_apply, h2, h1]
  by_cases hk : k = i
  · subst hk
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · by_cases hk' : k = j
    · subst hk'
      simp [hk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [hk, hk']

end Action

theorem two_eq_zero' {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) : (2 : K) = 0 := by
  have := h.charP
  exact CharTwo.two_eq_zero

section Rot

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem norm_bar (x : K) : h.norm (h.bar x) = h.norm x := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.norm, h.bar_bar, mul_comm]

theorem norm_eq_zero_iff (x : K) : h.norm x = 0 ↔ x = 0 := by
  rw [UnitaryFieldData.norm, mul_eq_zero, h.bar_eq_zero_iff, or_self]

@[expose] noncomputable def rotMat (α β : K) : Matrix (Fin 2) (Fin 2) K :=
  !![α, β; h.bar β, h.bar α]

variable {h}

theorem rotMat_det {α β : K} (hN : h.norm α + h.norm β = 1) : (rotMat h α β).det = 1 := by
  have h2 := two_eq_zero' h
  rw [rotMat, Matrix.det_fin_two_of]
  unfold UnitaryFieldData.norm at hN
  linear_combination hN - (h.bar β * β) * h2

theorem rotMat_unitary {α β : K} (hN : h.norm α + h.norm β = 1) :
    ((rotMat h α β).map h.bar)ᵀ * rotMat h α β = 1 := by
  have h2 := two_eq_zero' h
  unfold UnitaryFieldData.norm at hN
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, h.bar_bar]
  · linear_combination hN
  · linear_combination (h.bar α * β) * h2
  · linear_combination (α * h.bar β) * h2
  · linear_combination hN

@[expose] noncomputable def rotGL {α β : K} (hN : h.norm α + h.norm β = 1) : GL (Fin 2) K :=
  Matrix.SpecialLinearGroup.toGL ⟨rotMat h α β, rotMat_det hN⟩

theorem rotGL_val {α β : K} (hN : h.norm α + h.norm β = 1) :
    ((rotGL hN : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = rotMat h α β := rfl

theorem rotGL_mem {α β : K} (hN : h.norm α + h.norm β = 1) :
    rotGL hN ∈ gramSU h (idGram K 2) := by
  rw [mem_gramSU_iff_unitary]
  refine ⟨?_, ?_⟩
  · rw [mem_primeFormUnitary, rotGL_val]
    simpa [idGram] using rotMat_unitary hN
  · rw [rotGL_val]
    exact rotMat_det hN

theorem exists_plane_elt {k l : Fin n} (hkl : k ≠ l) {α β : K}
    (hN : h.norm α + h.norm β = 1) :
    ∃ g ∈ blk h hkl, ∀ (v : Fin n → K) (i : Fin n), ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) i =
      if i = k then α * v k + β * v l
      else if i = l then h.bar β * v k + h.bar α * v l else v i := by
  refine ⟨Units.map (coordEmbedHom K k l hkl) (rotGL hN),
    (mem_blk_iff hkl).2 ⟨rotGL hN, rotGL_mem hN, rfl⟩, fun v i => ?_⟩
  have : ((Units.map (coordEmbedHom K k l hkl) (rotGL hN) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      coordEmbed K k l (rotMat h α β) := by
    rfl
  rw [this, coordEmbed_mulVec hkl]
  simp [rotMat]

@[expose] noncomputable def planeGen (h : UnitaryFieldData 2 f K) (B : Finset (Fin n)) :
    Subgroup (GL (Fin n) K) :=
  ⨆ (i : Fin n) (_ : i ∈ B) (j : Fin n) (_ : j ∈ B) (hij : i ≠ j), blk h hij

theorem blk_le_planeGen {B : Finset (Fin n)} {i j : Fin n} (hi : i ∈ B) (hj : j ∈ B)
    (hij : i ≠ j) : blk h hij ≤ planeGen h B :=
  le_iSup₂_of_le i hi (le_iSup₂_of_le j hj (le_iSup (fun hij : i ≠ j => blk h hij) hij))

theorem planeGen_le_unitarySU (B : Finset (Fin n)) : planeGen h B ≤ unitarySU 2 f K n :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hij =>
    blk_le_unitarySU hij

theorem planeGen_mono {B B' : Finset (Fin n)} (hBB' : B ⊆ B') : planeGen h B ≤ planeGen h B' :=
  iSup_le fun _ => iSup_le fun hi => iSup_le fun _ => iSup_le fun hj => iSup_le fun hij =>
    blk_le_planeGen (hBB' hi) (hBB' hj) hij

theorem sum_norm_mulVec {g : GL (Fin n) K} (hg : g ∈ unitarySU 2 f K n) (v : Fin n → K) :
    ∑ i, h.norm (((g : Matrix (Fin n) (Fin n) K) *ᵥ v) i) = ∑ i, h.norm (v i) := by
  have := ((mem_unitarySU_iff_isometry h).1 hg).2 v v
  simp only [stdHermForm_apply] at this
  simpa [UnitaryFieldData.norm, mul_comm] using this

theorem eq_of_add_eq_zero' {a b : K} (h2 : (2 : K) = 0) (hab : a + b = 0) : a = b := by
  linear_combination hab - b * h2

theorem exists_merge {x y : K} (hs : h.norm x + h.norm y ≠ 0) :
    ∃ α β : K, h.norm α + h.norm β = 1 ∧ h.bar β * x + h.bar α * y = 0 := by
  have h2 := two_eq_zero' h
  have hsF : h.norm x + h.norm y ∈ h.fixedField :=
    add_mem (h.norm_mem_fixedField x) (h.norm_mem_fixedField y)
  have hsinv : (h.norm x + h.norm y)⁻¹ ∈ h.fixedField := inv_mem hsF
  obtain ⟨lam, hlam⟩ := h.normHom_surjective ⟨(h.norm x + h.norm y)⁻¹, hsinv⟩
  have hlam' : h.norm lam = (h.norm x + h.norm y)⁻¹ := congrArg Subtype.val hlam
  refine ⟨lam * h.bar x, lam * h.bar y, ?_, ?_⟩
  · rw [norm_mul_eq h, norm_mul_eq h, norm_bar, norm_bar, hlam', ← mul_add, inv_mul_cancel₀ hs]
  · rw [map_mul, map_mul, h.bar_bar, h.bar_bar]
    linear_combination (h.bar lam * x * y) * h2

variable (h) in
theorem exists_fixed_ne (hq : 4 ≤ 2 ^ f) : ∃ a : K, h.bar a = a ∧ a ≠ 0 ∧ a ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hfin := h.finite
  let g : h.fixedField → Bool := fun a => decide ((a : K) = 0)
  have hg : Function.Injective g := by
    intro a b hab
    have hab' : ((a : K) = 0) ↔ ((b : K) = 0) := by simpa [g] using hab
    apply Subtype.ext
    by_cases ha : (a : K) = 0
    · rw [ha, (hab'.1 ha)]
    · have hb : (b : K) ≠ 0 := fun hb => ha (hab'.2 hb)
      rw [hcon a a.2 ha, hcon b b.2 hb]
  have := Nat.card_le_card_of_injective g hg
  rw [h.card_fixedField, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

variable (h) in
theorem exists_norm_one_ne_one (hq : 4 ≤ 2 ^ f) : ∃ u : K, h.norm u = 1 ∧ u ≠ 1 := by
  have hcard := h.card_ker_normUnits_and_surjective.1
  have hne : (Units.map h.normHom).ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  refine ⟨u, (h.mem_ker_normUnits).1 hu, fun h1 => hu1 ?_⟩
  apply Subtype.ext
  apply Units.ext
  simpa using h1

theorem exists_rebalance (hq : 4 ≤ 2 ^ f) {x y : K} (hxy : h.norm x = h.norm y)
    (hx : h.norm x ≠ 0) :
    ∃ α β : K, h.norm α + h.norm β = 1 ∧ h.norm (α * x + β * y) ≠ h.norm x := by
  have h2 := two_eq_zero' h
  obtain ⟨a, haF, ha0, ha1⟩ := exists_fixed_ne h hq
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; simp [UnitaryFieldData.norm])
  have hy0 : y ≠ 0 := fun h0 => hx (by rw [hxy, h0]; simp [UnitaryFieldData.norm])
  have ha1' : 1 + a ≠ 0 := fun h0 => ha1 (by linear_combination h0 - h2)
  obtain ⟨u, hu, hT⟩ : ∃ u : K, h.norm u = 1 ∧
      u ^ 2 * (x * h.bar y) + h.bar u ^ 2 * (h.bar x * y) ≠ 0 := by
    by_cases ht : x * h.bar y + h.bar x * y = 0
    · obtain ⟨u, hu, hu1⟩ := exists_norm_one_ne_one h hq
      refine ⟨u, hu, ?_⟩
      have hxy' : h.bar x * y = x * h.bar y := eq_of_add_eq_zero' h2 (by rw [add_comm]; exact ht)
      have hz0 : x * h.bar y ≠ 0 := mul_ne_zero hx0 (by simpa using hy0)
      rw [hxy']
      have : u ^ 2 * (x * h.bar y) + h.bar u ^ 2 * (x * h.bar y) =
          (u + h.bar u) ^ 2 * (x * h.bar y) := by linear_combination (-(u * h.bar u) * (x * h.bar y)) * h2
      rw [this]
      refine mul_ne_zero (pow_ne_zero 2 fun h0 => ?_) hz0
      have hub : h.bar u = u := (eq_of_add_eq_zero' h2 h0).symm
      apply hu1
      have hu2 : u * u = 1 := by
        have := hu
        rw [UnitaryFieldData.norm, hub] at this
        exact this
      have : (u + 1) ^ 2 = 0 := by linear_combination hu2 + (u + 1) * h2
      exact (eq_of_add_eq_zero' h2 (pow_eq_zero_iff (two_ne_zero) |>.1 this))
    · refine ⟨1, by simp [UnitaryFieldData.norm], ?_⟩
      simpa using ht
  have hNu : h.norm (h.bar u) = 1 := by rw [norm_bar, hu]
  have hNa : h.norm a = a ^ 2 := by rw [UnitaryFieldData.norm, haF, sq]
  have hNa1 : h.norm (1 + a) = (1 + a) ^ 2 := by
    rw [UnitaryFieldData.norm, map_add, map_one, haF, sq]
  refine ⟨a * u, (1 + a) * h.bar u, ?_, ?_⟩
  · rw [norm_mul_eq h, norm_mul_eq h, hu, hNu, hNa, hNa1]
    linear_combination (a + a ^ 2) * h2
  · intro hne
    have key : h.norm ((a * u) * x + ((1 + a) * h.bar u) * y) =
        h.norm x + a * (1 + a) * (u ^ 2 * (x * h.bar y) + h.bar u ^ 2 * (h.bar x * y)) := by
      unfold UnitaryFieldData.norm at hu hxy ⊢
      simp only [map_add, map_mul, h.bar_bar, haF, map_one]
      linear_combination ((a ^ 2 * (x * h.bar x) + (1 + a) ^ 2 * (y * h.bar y)) ) * hu +
        (1 + a) ^ 2 * (-hxy) + (a * (1 + a) * (x * h.bar x)) * h2
    rw [key] at hne
    have : a * (1 + a) * (u ^ 2 * (x * h.bar y) + h.bar u ^ 2 * (h.bar x * y)) = 0 := by
      linear_combination hne
    exact mul_ne_zero (mul_ne_zero ha0 ha1') hT this

theorem exists_merge_elt {B : Finset (Fin n)} {k l : Fin n} (hk : k ∈ B) (hl : l ∈ B)
    (hkl : k ≠ l) (v : Fin n → K) (hs : h.norm (v k) + h.norm (v l) ≠ 0) :
    ∃ P ∈ planeGen h B, ((P : Matrix (Fin n) (Fin n) K) *ᵥ v) l = 0 ∧
      (∀ i, i ≠ k → i ≠ l → ((P : Matrix (Fin n) (Fin n) K) *ᵥ v) i = v i) ∧
      ∑ i, h.norm (((P : Matrix (Fin n) (Fin n) K) *ᵥ v) i) = ∑ i, h.norm (v i) := by
  obtain ⟨α, β, hN, h0⟩ := exists_merge hs
  obtain ⟨g, hg, hact⟩ := exists_plane_elt (h := h) hkl hN
  refine ⟨g, blk_le_planeGen hk hl hkl hg, ?_, fun i hik hil => ?_,
    sum_norm_mulVec (h := h) (blk_le_unitarySU hkl hg) v⟩
  · rw [hact v l]
    simp only [hkl.symm, ite_false, ite_true]
    exact h0
  · rw [hact v i]
    simp [hik, hil]

theorem exists_rebalance_elt (hq : 4 ≤ 2 ^ f) {B : Finset (Fin n)} {k l : Fin n} (hk : k ∈ B)
    (hl : l ∈ B) (hkl : k ≠ l) (v : Fin n → K) (hxy : h.norm (v k) = h.norm (v l))
    (hx : h.norm (v k) ≠ 0) :
    ∃ P ∈ planeGen h B, h.norm (((P : Matrix (Fin n) (Fin n) K) *ᵥ v) k) ≠ h.norm (v k) ∧
      (∀ i, i ≠ k → i ≠ l → ((P : Matrix (Fin n) (Fin n) K) *ᵥ v) i = v i) ∧
      ∑ i, h.norm (((P : Matrix (Fin n) (Fin n) K) *ᵥ v) i) = ∑ i, h.norm (v i) := by
  obtain ⟨α, β, hN, hne⟩ := exists_rebalance (h := h) hq hxy hx
  obtain ⟨g, hg, hact⟩ := exists_plane_elt (h := h) hkl hN
  refine ⟨g, blk_le_planeGen hk hl hkl hg, ?_, fun i hik hil => ?_,
    sum_norm_mulVec (h := h) (blk_le_unitarySU hkl hg) v⟩
  · rw [hact v k]
    simpa using hne
  · rw [hact v i]
    simp [hik, hil]

theorem exists_reduce (hq : 4 ≤ 2 ^ f) {B : Finset (Fin n)} :
    ∀ (m : ℕ) (S : Finset (Fin n)), S ⊆ B → S.card = m + 1 → ∀ v : Fin n → K,
      (∀ i, i ∉ S → v i = 0) → ∑ i, h.norm (v i) = 1 →
      ∃ P ∈ planeGen h B, ∃ k ∈ S, ∃ c : K, h.norm c = 1 ∧
        ∀ i, ((P : Matrix (Fin n) (Fin n) K) *ᵥ v) i = if i = k then c else 0 := by
  classical
  intro m
  induction m with
  | zero =>
    intro S hSB hS v hv hN
    obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 hS
    have hv' : ∀ i, i ≠ k → v i = 0 := fun i hi => hv i (by simpa using hi)
    refine ⟨1, one_mem _, k, Finset.mem_singleton_self k, v k, ?_, fun i => ?_⟩
    · rw [← hN, Finset.sum_eq_single k]
      · intro i _ hi
        rw [hv' i hi]
        simp [UnitaryFieldData.norm]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · by_cases hik : i = k
      · subst hik
        simp
      · simp [hik, hv' i hik]
  | succ m ih =>
    intro S hSB hS v hv hN
    have h2 := two_eq_zero' h
    have hsum : ∑ i, h.norm (v i) = ∑ i ∈ S, h.norm (v i) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_
      rw [hv i hi]
      simp [UnitaryFieldData.norm]
    have step : ∃ P' ∈ planeGen h B, ∃ l ∈ S,
        (∀ i, i ∉ S.erase l → ((P' : Matrix (Fin n) (Fin n) K) *ᵥ v) i = 0) ∧
        ∑ i, h.norm (((P' : Matrix (Fin n) (Fin n) K) *ᵥ v) i) = 1 := by
      by_cases hall : ∀ k ∈ S, ∀ l ∈ S, h.norm (v k) = h.norm (v l)
      ·
        have hS2 : 2 < S.card := by
          by_contra hle
          have hcard : S.card = 2 := by omega
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
          have hSab : S = {a, b} := by
            rw [Finset.card_eq_two] at hcard
            obtain ⟨x, y, hxy, rfl⟩ := hcard
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd rfl hab
            · rfl
            · exact Finset.pair_comm _ _
            · exact absurd rfl hab
          rw [hsum, hSab, Finset.sum_pair hab, hall a ha b hb] at hN
          have : h.norm (v b) + h.norm (v b) = 0 := by linear_combination h.norm (v b) * h2
          rw [this] at hN
          exact zero_ne_one hN
        obtain ⟨k, hk, l, hl, m', hm, hkl, hkm, hlm⟩ := Finset.two_lt_card.1 hS2
        have ha0 : h.norm (v k) ≠ 0 := by
          intro h0
          have : ∀ i ∈ S, h.norm (v i) = 0 := fun i hi => by rw [hall i hi k hk, h0]
          rw [hsum, Finset.sum_eq_zero this] at hN
          exact zero_ne_one hN
        obtain ⟨P₁, hP₁, hne₁, hP₁o, hP₁s⟩ := exists_rebalance_elt hq (hSB hk) (hSB hl) hkl v
          (hall k hk l hl) ha0
        have hP₁v : ((P₁ : Matrix (Fin n) (Fin n) K) *ᵥ v) m' = v m' := hP₁o m' hkm.symm hlm.symm
        have hs : h.norm (((P₁ : Matrix (Fin n) (Fin n) K) *ᵥ v) k) +
            h.norm (((P₁ : Matrix (Fin n) (Fin n) K) *ᵥ v) m') ≠ 0 := by
          intro h0
          apply hne₁
          rw [eq_of_add_eq_zero' h2 h0, hP₁v, hall m' hm k hk]
        obtain ⟨P₂, hP₂, h2z, hP₂o, hP₂s⟩ := exists_merge_elt (hSB hk) (hSB hm) hkm _ hs
        refine ⟨P₂ * P₁, mul_mem hP₂ hP₁, m', hm, fun i hi => ?_, ?_⟩
        · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
          by_cases him : i = m'
          · rw [him]
            exact h2z
          · have hiS : i ∉ S := fun hiS => hi (Finset.mem_erase.2 ⟨him, hiS⟩)
            have hik : i ≠ k := fun h' => hiS (h' ▸ hk)
            have hil : i ≠ l := fun h' => hiS (h' ▸ hl)
            rw [hP₂o i hik him, hP₁o i hik hil]
            exact hv i hiS
        · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hP₂s, hP₁s, hN]
      ·
        push Not at hall
        obtain ⟨k, hk, l, hl, hne⟩ := hall
        have hkl : k ≠ l := fun h' => hne (h' ▸ rfl)
        have hs : h.norm (v k) + h.norm (v l) ≠ 0 := fun h0 => hne (eq_of_add_eq_zero' h2 h0)
        obtain ⟨P, hP, hz, hPo, hPs⟩ := exists_merge_elt (h := h) (hSB hk) (hSB hl) hkl v hs
        refine ⟨P, hP, l, hl, fun i hi => ?_, by rw [hPs, hN]⟩
        by_cases hil : i = l
        · rw [hil]
          exact hz
        · have hiS : i ∉ S := fun hiS => hi (Finset.mem_erase.2 ⟨hil, hiS⟩)
          have hik : i ≠ k := fun h' => hiS (h' ▸ hk)
          rw [hPo i hik hil]
          exact hv i hiS
    obtain ⟨P', hP', l, hl, h0, hN'⟩ := step
    have hcard : (S.erase l).card = m + 1 := by rw [Finset.card_erase_of_mem hl, hS]; rfl
    obtain ⟨P'', hP'', k, hk, c, hc, hP⟩ :=
      ih (S.erase l) ((Finset.erase_subset l S).trans hSB) hcard _ h0 hN'
    refine ⟨P'' * P', mul_mem hP'' hP', k, Finset.mem_of_mem_erase hk, c, hc, fun i => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact hP i

@[expose] def fixOut (K : Type) [Field K] {n : ℕ} (B : Finset (Fin n)) : Subgroup (GL (Fin n) K) where
  carrier := {g | ∀ i, i ∉ B → (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = Pi.single i 1}
  mul_mem' {a b} ha hb := fun i hi => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb i hi, ha i hi]
  one_mem' := fun i _ => by rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha := fun i hi => by
    calc (((a⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1
        = (((a⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((a : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1) := by rw [ha i hi]
      _ = Pi.single i 1 := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]

theorem mem_fixOut {B : Finset (Fin n)} {g : GL (Fin n) K} :
    g ∈ fixOut K B ↔ ∀ i, i ∉ B → (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = Pi.single i 1 :=
  Iff.rfl

theorem blk_le_fixOut {B : Finset (Fin n)} {i j : Fin n} (hi : i ∈ B) (hj : j ∈ B) (hij : i ≠ j) :
    blk h hij ≤ fixOut K B := by
  intro g hg m hm
  obtain ⟨X, -, hX⟩ := (mem_blk_iff hij).1 hg
  have hmi : m ≠ i := fun h' => hm (h' ▸ hi)
  have hmj : m ≠ j := fun h' => hm (h' ▸ hj)
  ext r
  rw [hX, coordEmbed_mulVec hij]
  by_cases hri : r = i
  · subst hri
    simp [hmi.symm, hmj.symm]
  · by_cases hrj : r = j
    · subst hrj
      simp [hmi.symm, hmj.symm, hri]
    · simp [hri, hrj]

theorem planeGen_le_fixOut (B : Finset (Fin n)) : planeGen h B ≤ fixOut K B :=
  iSup_le fun _ => iSup_le fun hi => iSup_le fun _ => iSup_le fun hj => iSup_le fun hij =>
    blk_le_fixOut hi hj hij

theorem apply_eq_of_fix (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K}
    (hg : g ∈ unitarySU 2 f K n) {i : Fin n}
    (hfix : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = Pi.single i 1) (y : Fin n → K) :
    ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) i = y i := by
  have := ((mem_unitarySU_iff_isometry h).1 hg).2 (Pi.single i 1) y
  rw [hfix] at this
  simpa [stdHermForm_apply, Pi.single_apply] using this

theorem eq_one_of_fix_all {g : GL (Fin n) K}
    (hfix : ∀ i, (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = Pi.single i 1) : g = 1 := by
  apply Units.ext
  ext r c
  have := congrFun (hfix c) r
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

theorem eq_one_of_fix_ne (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K}
    (hg : g ∈ unitarySU 2 f K n) {b : Fin n}
    (hfix : ∀ i, i ≠ b → (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = Pi.single i 1) :
    g = 1 := by
  classical
  have hdet : (g : Matrix (Fin n) (Fin n) K).det = 1 := ((mem_unitarySU_iff h).1 hg).1
  set c : K := (g : Matrix (Fin n) (Fin n) K) b b with hc
  have hcol : ∀ r, r ≠ b → (g : Matrix (Fin n) (Fin n) K) r b = 0 := by
    intro r hr
    have := apply_eq_of_fix h hg (hfix r hr) (Pi.single b 1)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this
  have hent : ∀ r s, s ≠ b → (g : Matrix (Fin n) (Fin n) K) r s = if r = s then 1 else 0 := by
    intro r s hs
    have := congrFun (hfix s hs) r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hdiag : (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun i => if i = b then c else 1) := by
    ext r s
    by_cases hs : s = b
    · subst hs
      by_cases hr : r = s
      · subst hr
        simp [hc]
      · simp [hcol r hr, hr]
    · by_cases hr : r = s
      · subst hr
        simp [hs, hent r r hs]
      · simp [hr, hent r s hs]
  have hcdet : c = 1 := by
    have := hdet
    rw [hdiag, Matrix.det_diagonal, Finset.prod_eq_single b (fun i _ hi => by simp [hi])
      (fun hb => absurd (Finset.mem_univ b) hb)] at this
    simpa using this
  apply eq_one_of_fix_all
  intro i
  by_cases hi : i = b
  · subst hi
    ext r
    rw [hdiag, hcdet]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.diagonal_apply]
  · exact hfix i hi

theorem exists_to_basis {B : Finset (Fin n)} (hB : 2 ≤ B.card) {k b : Fin n} (hk : k ∈ B)
    (hb : b ∈ B) {c : K} (hc : h.norm c = 1) :
    ∃ Q ∈ planeGen h B, ∀ i, ((Q : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => if i = k then c else 0)) i = if i = b then 1 else 0 := by
  classical
  have h2 := two_eq_zero' h
  obtain ⟨l, hl, hlb⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) b
  have hc0 : c ≠ 0 := fun h0 => by
    have : h.norm c = 0 := (norm_eq_zero_iff h c).2 h0
    rw [hc] at this
    exact one_ne_zero this
  have step1 : ∃ Q₁ ∈ planeGen h B, ∀ i, ((Q₁ : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => if i = k then c else 0)) i = if i = b then c else 0 := by
    by_cases hkb : k = b
    · subst hkb
      exact ⟨1, one_mem _, fun i => by simp⟩
    · have hN : h.norm (0 : K) + h.norm (1 : K) = 1 := by simp [UnitaryFieldData.norm]
      obtain ⟨g, hg, hact⟩ := exists_plane_elt (h := h) hkb hN
      refine ⟨g, blk_le_planeGen hk hb hkb hg, fun i => ?_⟩
      rw [hact]
      by_cases hik : i = k
      · subst hik
        simp [hkb, Ne.symm hkb]
      · by_cases hib : i = b
        · subst hib
          simp [hik]
        · simp [hik, hib]
  obtain ⟨Q₁, hQ₁, h1⟩ := step1
  have hbl : b ≠ l := hlb.symm
  have hN : h.norm c⁻¹ + h.norm (0 : K) = 1 := by
    have : h.norm c⁻¹ = (h.norm c)⁻¹ := by
      simp only [UnitaryFieldData.norm, map_inv₀, mul_inv]
    rw [this, hc]
    simp [UnitaryFieldData.norm]
  obtain ⟨g, hg, hact⟩ := exists_plane_elt (h := h) hbl hN
  refine ⟨g * Q₁, mul_mem (blk_le_planeGen hb hl hbl hg) hQ₁, fun i => ?_⟩
  have hv : (fun i => if i = k then c else 0 : Fin n → K) = fun i => if i = k then c else 0 := rfl
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have h1' : (Q₁ : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => if i = k then c else 0) =
      fun i => if i = b then c else 0 := funext h1
  rw [h1', hact]
  by_cases hib : i = b
  · subst hib
    simp [hc0]
  · by_cases hil : i = l
    · subst hil
      simp [hbl.symm]
    · simp [hib, hil]

theorem mem_planeGen_of_fixOut (hq : 4 ≤ 2 ^ f) :
    ∀ (N : ℕ) (B : Finset (Fin n)), B.card = N → ∀ g : GL (Fin n) K, g ∈ unitarySU 2 f K n →
      g ∈ fixOut K B → g ∈ planeGen h B := by
  classical
  intro N
  induction N with
  | zero =>
    intro B hB g hg hfix
    rw [Finset.card_eq_zero] at hB
    subst hB
    have : g = 1 := eq_one_of_fix_all fun i => hfix i (Finset.notMem_empty i)
    rw [this]
    exact one_mem _
  | succ N ih =>
    intro B hB g hg hfix
    by_cases hN0 : N = 0
    · subst hN0
      obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 hB
      have : g = 1 := eq_one_of_fix_ne h hg (b := b) fun i hi => hfix i (by simpa using hi)
      rw [this]
      exact one_mem _
    · have hB2 : 2 ≤ B.card := by omega
      obtain ⟨b, hb⟩ : B.Nonempty := Finset.card_pos.1 (by omega)
      set v : Fin n → K := (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single b 1 with hvdef
      have hv : ∀ i, i ∉ B → v i = 0 := by
        intro i hi
        have hib : b ≠ i := fun h' => hi (h' ▸ hb)
        have := apply_eq_of_fix h hg (hfix i hi) (Pi.single b 1)
        rw [hvdef, this]
        simp [hib.symm]
      have hvN : ∑ i, h.norm (v i) = 1 := by
        rw [hvdef, sum_norm_mulVec hg, Finset.sum_eq_single b]
        · simp [UnitaryFieldData.norm]
        · intro i _ hi
          simp [hi, UnitaryFieldData.norm]
        · intro hb'
          exact absurd (Finset.mem_univ b) hb'
      obtain ⟨P, hP, k, hk, c, hc, hPv⟩ :=
        exists_reduce hq N B (Finset.Subset.refl B) hB v hv hvN
      obtain ⟨Q, hQ, hQv⟩ := exists_to_basis hB2 (hk) hb hc
      have hPv' : (P : Matrix (Fin n) (Fin n) K) *ᵥ v = fun i => if i = k then c else 0 :=
        funext hPv
      have hQPv : ((Q * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = Pi.single b 1 := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hPv']
        ext i
        rw [hQv i]
        simp [Pi.single_apply]
      have hQP : Q * P ∈ planeGen h B := mul_mem hQ hP
      have hg' : Q * P * g ∈ unitarySU 2 f K n := mul_mem (planeGen_le_unitarySU B hQP) hg
      have hfix' : Q * P * g ∈ fixOut K (B.erase b) := by
        intro i hi
        by_cases hib : i = b
        · subst hib
          rw [Units.val_mul, ← Matrix.mulVec_mulVec]
          exact hQPv
        · have hiB : i ∉ B := fun hiB => hi (Finset.mem_erase.2 ⟨hib, hiB⟩)
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hfix i hiB]
          exact planeGen_le_fixOut B hQP i hiB
      have hcard : (B.erase b).card = N := by rw [Finset.card_erase_of_mem hb, hB]; rfl
      have := ih (B.erase b) hcard (Q * P * g) hg' hfix'
      have hgg : g = (Q * P)⁻¹ * (Q * P * g) := by group
      rw [hgg]
      exact mul_mem (inv_mem hQP) (planeGen_mono (Finset.erase_subset b B) this)

theorem planeGen_induction {B : Finset (Fin n)} {C : GL (Fin n) K → Prop}
    (hmem : ∀ i ∈ B, ∀ j ∈ B, ∀ hij : i ≠ j, ∀ g ∈ blk h hij, C g) (h1 : C 1)
    (hmul : ∀ a b, C a → C b → C (a * b)) {g : GL (Fin n) K} (hg : g ∈ planeGen h B) : C g := by
  unfold planeGen at hg
  refine Subgroup.iSup_induction _ (C := C) hg (fun i x hx => ?_) h1 hmul
  refine Subgroup.iSup_induction _ (C := C) hx (fun hi y hy => ?_) h1 hmul
  refine Subgroup.iSup_induction _ (C := C) hy (fun j z hz => ?_) h1 hmul
  refine Subgroup.iSup_induction _ (C := C) hz (fun hj u hu => ?_) h1 hmul
  refine Subgroup.iSup_induction _ (C := C) hu (fun hij v hv => ?_) h1 hmul
  exact hmem i hi j hj hij v hv

end Rot

end CFSG.RankThree.PartOne.K159G
