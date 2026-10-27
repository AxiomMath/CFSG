module

public import CFSG.Quasithin.EmptyFaithful.S151ZM

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ}

theorem sum_window {p k : ℕ} (hpk : p + k ≤ n) {R : Type*} [AddCommMonoid R] (f : Fin n → R)
    (hf : ∀ m : Fin n, ((m : ℕ) < p ∨ p + k ≤ (m : ℕ)) → f m = 0) :
    ∑ m, f m = ∑ t : Fin k, f ⟨p + t, by have := t.2; omega⟩ := by
  classical
  let e : Fin k → Fin n := fun t => ⟨p + t, by have := t.2; omega⟩
  have he : Function.Injective e := fun a b h => by
    apply Fin.ext
    have := congrArg Fin.val h
    simpa [e] using this
  rw [← Finset.sum_image (s := (Finset.univ : Finset (Fin k))) (g := e) (f := f)
    (fun a _ b _ h => he h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m _ hm
  apply hf
  by_contra hcon
  have h1 : p ≤ (m : ℕ) := by omega
  have h2 : (m : ℕ) < p + k := by omega
  exact hm (Finset.mem_image.mpr ⟨⟨(m : ℕ) - p, by omega⟩, Finset.mem_univ _, by
    apply Fin.ext
    simp only [e]
    omega⟩)

@[expose] def winMat (p k : ℕ) (hpk : p + k ≤ n) (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun r c => M ⟨p + r, by have := r.2; omega⟩ ⟨p + c, by have := c.2; omega⟩

theorem winMat_mul {p k : ℕ} (hpk : p + k ≤ n) {M N : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : BCond n p M) (hN : BCond n (p + k) N) :
    winMat p k hpk (M * N) = winMat p k hpk M * winMat p k hpk N := by
  ext r c
  simp only [winMat, Matrix.of_apply, Matrix.mul_apply]
  apply sum_window hpk
  intro m hm
  rcases hm with hm | hm
  · rw [hM _ _ (by simp) hm, zero_mul]
  · have hc := c.2
    rw [hN _ _ hm (show p + (c : ℕ) < p + k by omega), mul_zero]

theorem winMat_one {p k : ℕ} (hpk : p + k ≤ n) :
    winMat p k hpk (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  ext r c
  simp only [winMat, Matrix.of_apply, Matrix.one_apply, Fin.mk.injEq]
  by_cases h : r = c
  · subst h
    simp
  · have h' : ¬ ((p + (r : ℕ)) = p + (c : ℕ)) := fun hh => h (Fin.ext (by omega))
    simp only [h', h, ite_false]

abbrev Awin (n p k : ℕ) : Subgroup (SLt n) :=
  stabilizer (flagSpace n (ZMod 2) p) ⊓ stabilizer (flagSpace n (ZMod 2) (p + k))

theorem Awin_bcond {p k : ℕ} {g : SLt n} (hg : g ∈ Awin n p k) :
    BCond n p (mat g) ∧ BCond n (p + k) (mat g) :=
  ⟨bcond_of_mem_stabilizer hg.1, bcond_of_mem_stabilizer hg.2⟩

theorem winMat_det {p k : ℕ} (hpk : p + k ≤ n) (g : ↥(Awin n p k)) :
    (winMat p k hpk (mat (g : SLt n))).det = 1 := by
  have hg := Awin_bcond g.2
  have hg' := Awin_bcond (Subgroup.inv_mem _ g.2)
  have h1 : winMat p k hpk (mat (g : SLt n)) * winMat p k hpk (mat ((g : SLt n)⁻¹)) = 1 := by
    rw [← winMat_mul hpk hg.1 hg'.2, mat_mul_inv, winMat_one]
  have h2 : (winMat p k hpk (mat (g : SLt n))).det * (winMat p k hpk (mat ((g : SLt n)⁻¹))).det
      = 1 := by
    rw [← Matrix.det_mul, h1, Matrix.det_one]
  revert h2
  generalize (winMat p k hpk (mat (g : SLt n))).det = a
  generalize (winMat p k hpk (mat ((g : SLt n)⁻¹))).det = b
  revert a b
  decide

@[expose] noncomputable def winHom (p k : ℕ) (hpk : p + k ≤ n) : ↥(Awin n p k) →* SLt k where
  toFun g := ⟨winMat p k hpk (mat (g : SLt n)), winMat_det hpk g⟩
  map_one' := by
    apply Subtype.ext
    show winMat p k hpk (mat ((1 : ↥(Awin n p k)) : SLt n)) = 1
    rw [Subgroup.coe_one, mat_one, winMat_one]
  map_mul' g h := by
    apply Subtype.ext
    show winMat p k hpk (mat (((g * h : ↥(Awin n p k)) : SLt n))) =
      winMat p k hpk (mat (g : SLt n)) * winMat p k hpk (mat (h : SLt n))
    rw [Subgroup.coe_mul, mat_mul]
    exact winMat_mul hpk (Awin_bcond g.2).1 (Awin_bcond h.2).2

@[expose] def e0 (k : ℕ) : Fin k → ZMod 2 := fun t => if (t : ℕ) = 0 then 1 else 0

theorem winMat_mulVec_e0 {p k : ℕ} (hk : 1 ≤ k) (hpk : p + k ≤ n)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (t : Fin k) :
    (winMat p k hpk M *ᵥ e0 k) t = M ⟨p + t, by have := t.2; omega⟩ ⟨p, by omega⟩ := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (⟨0, by omega⟩ : Fin k)]
  · simp [winMat, e0]
  · intro s _ hs
    have : (s : ℕ) ≠ 0 := fun h => hs (Fin.ext h)
    simp [e0, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mulVec_mem_succ_of_fix {p k : ℕ} (hk : 1 ≤ k) (hpk : p + k ≤ n) {g : SLt n}
    (hg : g ∈ Awin n p k) (hfix : winMat p k hpk (mat g) *ᵥ e0 k = e0 k) :
    ∀ v ∈ flagSpace n (ZMod 2) (p + 1), mat g *ᵥ v ∈ flagSpace n (ZMod 2) (p + 1) := by
  intro v hv
  rw [mem_flagSpace] at hv ⊢
  intro r hr
  obtain ⟨hb1, hb2⟩ := Awin_bcond hg
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : p + 1 ≤ (c : ℕ)
  · rw [hv c hc, mul_zero]
  · by_cases hcp : (c : ℕ) < p
    · rw [hb1 r c (by omega) hcp, zero_mul]
    · by_cases hrk : p + k ≤ (r : ℕ)
      · rw [hb2 r c hrk (by omega), zero_mul]
      · have hcp' : (c : ℕ) = p := by omega
        have h := congrFun hfix ⟨(r : ℕ) - p, by omega⟩
        rw [winMat_mulVec_e0 hk hpk] at h
        have hr0 : ¬ (((r : ℕ) - p) = 0) := by omega
        have h0 : e0 k ⟨(r : ℕ) - p, by omega⟩ = 0 := by simp [e0, hr0]
        rw [h0] at h
        have hrr : (⟨p + ((r : ℕ) - p), by omega⟩ : Fin n) = r := Fin.ext (by simp; omega)
        have hcc : (⟨p, by omega⟩ : Fin n) = c := Fin.ext (by simp; omega)
        rw [hrr, hcc] at h
        rw [h, zero_mul]

theorem mem_stabilizer_succ_of_fix {p k : ℕ} (hk : 1 ≤ k) (hpk : p + k ≤ n) {g : SLt n}
    (hg : g ∈ Awin n p k) (hfix : winMat p k hpk (mat g) *ᵥ e0 k = e0 k) :
    g ∈ stabilizer (flagSpace n (ZMod 2) (p + 1)) := by
  rw [mem_stabilizer_iff]
  intro v
  constructor
  · exact mulVec_mem_succ_of_fix hk hpk hg hfix v
  · intro hv
    have hg' : g⁻¹ ∈ Awin n p k := Subgroup.inv_mem _ hg
    have hfix' : winMat p k hpk (mat g⁻¹) *ᵥ e0 k = e0 k := by
      have h1 : winMat p k hpk (mat g⁻¹) *ᵥ (winMat p k hpk (mat g) *ᵥ e0 k) = e0 k := by
        rw [Matrix.mulVec_mulVec, ← winMat_mul hpk (Awin_bcond hg').1 (Awin_bcond hg).2,
          ← mat_mul, inv_mul_cancel, mat_one, winMat_one, Matrix.one_mulVec]
      rwa [hfix] at h1
    have := mulVec_mem_succ_of_fix hk hpk hg' hfix' _ hv
    rwa [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec] at this

theorem orbit_bound {k : ℕ} (R : Subgroup (SLt k)) :
    ((MulAction.stabilizer (SLt k) (e0 k)).subgroupOf R).index ≤ 2 ^ k ∧
      ((MulAction.stabilizer (SLt k) (e0 k)).subgroupOf R).index ∣ Nat.card (SLt k) := by
  rw [MulAction.stabilizer_subgroupOf]
  refine ⟨?_, (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card R)⟩
  rw [MulAction.index_stabilizer]
  calc (MulAction.orbit (↥R) (e0 k)).ncard ≤ (Set.univ : Set (Fin k → ZMod 2)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = 2 ^ k := by
        rw [Set.ncard_univ]
        simp [Nat.card_eq_fintype_card, ZMod.card]

theorem step_core {p k : ℕ} (hk : 2 ≤ k) (hpk : p + k ≤ n) (Q : Subgroup (SLt n))
    (hQ : Q ≤ Awin n p k) :
    (Q ⊓ stabilizer (flagSpace n (ZMod 2) (p + 1))).relIndex Q ∣ Nat.card (SLt k) ∧
      (Q ⊓ stabilizer (flagSpace n (ZMod 2) (p + 1))).relIndex Q ≤ 2 ^ k := by
  set K : Subgroup (SLt n) := Q ⊓ stabilizer (flagSpace n (ZMod 2) (p + 1)) with hK
  let φ : ↥Q →* SLt k := (winHom p k hpk).comp (Subgroup.inclusion hQ)
  let H₀ : Subgroup (SLt k) := MulAction.stabilizer (SLt k) (e0 k)
  have hH₁ : H₀.comap φ ≤ K.subgroupOf Q := by
    intro g hg
    have hfix : winMat p k hpk (mat (g : SLt n)) *ᵥ e0 k = e0 k := MulAction.mem_stabilizer_iff.mp hg
    exact ⟨g.2, mem_stabilizer_succ_of_fix (by omega) hpk (hQ g.2) hfix⟩
  have hdvd : K.relIndex Q ∣ (H₀.comap φ).index := Subgroup.index_dvd_of_le hH₁
  have hidx : (H₀.comap φ).index = (H₀.subgroupOf φ.range).index := Subgroup.index_comap H₀ φ
  obtain ⟨h1, h2⟩ := orbit_bound (k := k) φ.range
  rw [← hidx] at h1 h2
  refine ⟨hdvd.trans h2, ?_⟩
  have hpos : 0 < (H₀.comap φ).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd hpos hdvd).trans h1

theorem QI_insert (n a : ℕ) (C : Set ℕ) :
    QI n (insert a C) = QI n C ⊓ stabilizer (flagSpace n (ZMod 2) a) := by
  ext g
  simp only [Subgroup.mem_inf, mem_flagStabilizer, Set.mem_insert_iff, forall_eq_or_imp]
  tauto

theorem mem_stabilizer_flag_zero (g : SLt n) : g ∈ stabilizer (flagSpace n (ZMod 2) 0) := by
  rw [mem_stabilizer_iff]
  intro v
  have h0 : ∀ w : Vt n, w ∈ flagSpace n (ZMod 2) 0 ↔ w = 0 := by
    intro w
    rw [mem_flagSpace]
    constructor
    · intro h
      funext j
      exact h j (Nat.zero_le _)
    · rintro rfl j _
      rfl
  rw [h0, h0]
  constructor
  · rintro rfl
    exact Matrix.mulVec_zero _
  · intro h
    have h1 : mat g⁻¹ *ᵥ (mat g *ᵥ v) = 0 := by rw [h, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec] at h1

theorem mem_stabilizer_flag_top (g : SLt n) : g ∈ stabilizer (flagSpace n (ZMod 2) n) := by
  rw [mem_stabilizer_iff]
  intro v
  have h0 : ∀ w : Vt n, w ∈ flagSpace n (ZMod 2) n := by
    intro w
    rw [mem_flagSpace]
    intro j hj
    exact absurd j.2 (by omega)
  exact iff_of_true (h0 v) (h0 _)

theorem QI_le_Awin {C : Set ℕ} {p k : ℕ} (hp : p = 0 ∨ p ∈ C) (hq : p + k = n ∨ p + k ∈ C) :
    QI n C ≤ Awin n p k := by
  intro g hg
  rw [mem_flagStabilizer] at hg
  refine ⟨?_, ?_⟩
  · rcases hp with rfl | hp
    · exact mem_stabilizer_flag_zero g
    · exact hg p hp
  · rcases hq with hq | hq
    · rw [hq]
      exact mem_stabilizer_flag_top g
    · exact hg _ hq

theorem card_SLt_two : Nat.card (SLt 2) = 6 := by
  have h := Matrix.card_SL_field (n := 2) (𝔽 := ZMod 2)
  rw [h]
  simp [ZMod.card, Fin.prod_univ_succ]

theorem card_SLt_three : Nat.card (SLt 3) = 168 := by
  have h := Matrix.card_SL_field (n := 3) (𝔽 := ZMod 2)
  rw [h]
  simp [ZMod.card, Fin.prod_univ_succ]

theorem qi_step {C : Set ℕ} (hC : ∀ x ∈ C, IsNode n x) {p k : ℕ} (hk : 2 ≤ k) (hpk : p + k ≤ n)
    (hp : p = 0 ∨ p ∈ C) (hq : p + k = n ∨ p + k ∈ C) (ha : p + 1 ∉ C) :
    (QI n (insert (p + 1) C)).relIndex (QI n C) ∣ Nat.card (SLt k) ∧
      (QI n (insert (p + 1) C)).relIndex (QI n C) ≤ 2 ^ k ∧
      ¬ 2 ∣ (QI n (insert (p + 1) C)).relIndex (QI n C) ∧
      (QI n (insert (p + 1) C)).relIndex (QI n C) ≠ 1 := by
  have hn : 1 ≤ n := by omega
  have hcore := step_core hk hpk (QI n C) (QI_le_Awin hp hq)
  rw [← QI_insert] at hcore
  refine ⟨hcore.1, hcore.2, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
    have hodd : ¬ 2 ∣ (Ut n).index := by
      have := Sylow.not_dvd_index P
      rwa [hP] at this
    intro h2
    have h3 : (QI n (insert (p + 1) C)).relIndex (QI n C) ∣ (Ut n).relIndex (QI n C) :=
      Subgroup.relIndex_dvd_of_le_left _ (Ut_le_QI n _)
    have h4 : (Ut n).relIndex (QI n C) ∣ (Ut n).index :=
      Subgroup.relIndex_dvd_index_of_le (Ut_le_QI n C)
    exact hodd (h2.trans (h3.trans h4))
  · intro h1
    have h2 : QI n C ≤ QI n (insert (p + 1) C) := Subgroup.relIndex_eq_one.mp h1
    have hJ : ∀ j ∈ insert (p + 1) C, IsNode n j := by
      intro j hj
      rcases hj with rfl | hj
      · exact ⟨by omega, by omega⟩
      · exact hC j hj
    have := (QI_le_QI_iff hJ).mp h2 (Set.mem_insert _ _)
    exact ha this

theorem step_two_val {s : ℕ} (h1 : s ∣ Nat.card (SLt 2)) (h2 : s ≤ 2 ^ 2) (h3 : ¬ 2 ∣ s)
    (h4 : s ≠ 1) : s = 3 := by
  rw [card_SLt_two] at h1
  interval_cases s <;> omega

theorem step_three_val {s : ℕ} (h1 : s ∣ Nat.card (SLt 3)) (h2 : s ≤ 2 ^ 3) (h3 : ¬ 2 ∣ s)
    (h4 : s ≠ 1) : s = 3 ∨ s = 7 := by
  rw [card_SLt_three] at h1
  interval_cases s <;> omega

end CFSG.Quasithin.FLc
