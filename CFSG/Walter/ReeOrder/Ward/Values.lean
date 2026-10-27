module

public import CFSG.Walter.ReeOrder.Ward.Seven

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

theorem offdiag_const {ι : Type*} [DecidableEq ι] (f : ι → ι → ℤ) (c : ℤ)
    (hrow : ∀ i k l, f i k - f i l = c * ((if i = k then 1 else 0) - (if i = l then 1 else 0)))
    (hcol : ∀ i j k, f i k - f j k = c * ((if i = k then 1 else 0) - (if j = k then 1 else 0)))
    (hthird : ∀ i j : ι, ∃ m, m ≠ i ∧ m ≠ j) (i₀ k₀ : ι) (h₀ : i₀ ≠ k₀) :
    ∀ i k, f i k = f i₀ k₀ + if i = k then c else 0 := by
  have hoff : ∀ i k j l, i ≠ k → j ≠ l → f i k = f j l := by
    intro i k j l hik hjl
    obtain ⟨m, hmi, hmj⟩ := hthird i j
    have h1 := hrow i k m
    have h2 := hcol i j m
    have h3 := hrow j m l
    simp only [hik, Ne.symm hmi, Ne.symm hmj, hjl, ↓reduceIte, sub_self, mul_zero] at h1 h2 h3
    linarith
  intro i k
  by_cases hik : i = k
  · subst hik
    obtain ⟨l, hli, -⟩ := hthird i i
    have h := hrow i i l
    simp only [↓reduceIte, Ne.symm hli, sub_zero, mul_one] at h
    rw [hoff i l i₀ k₀ (Ne.symm hli) h₀] at h
    simp only [↓reduceIte]
    linarith
  · simp only [hik, ↓reduceIte, add_zero]
    exact hoff i k i₀ k₀ hik h₀

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} {S : WardSetup G L q e IV}

variable (S) in
noncomputable def i₀ : S.W.RFam :=
  Classical.choice (Fintype.card_pos_iff.mp (by have := EtaData.card_ge (S := S); omega))

variable (S) in
noncomputable def i₁ : S.W.RFam := (EtaData.exists_third (S := S) S.i₀ S.i₀).choose

theorem i₁_ne : S.i₁ ≠ S.i₀ := (EtaData.exists_third (S := S) S.i₀ S.i₀).choose_spec.1

variable (S) in
theorem exists_Ro : ∃ r : L, r ∈ S.W.Ro ∧ r ≠ 1 := by
  have hcard : 1 < Nat.card S.W.Ro := by
    have h1 := S.W.Ro_card
    have h2 := S.q_ge
    rcases S.W.e_eq with rfl | rfl <;> omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hcard)
  exact ⟨r, hr, fun h => hr1 (Subtype.ext h)⟩

theorem M_one_R {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) : S.M (1 : G → ℂ) θ = 0 := by
  have h := S.inner_σ (one_mem_blocksIrr G) (S.W.R_mem hθ)
  have hσ : S.σ (1 : G → ℂ) = (1 : L → ℂ) := rfl
  rw [hσ, blocksInnerProduct_irr S.W.one_mem (S.W.R_mem hθ),
    ite_eq_right (fun h => S.W.one_not_R (by rw [h]; exact hθ))] at h
  exact_mod_cast h.symm

theorem quad_ge {n x t : ℤ} (hn : 6 ≤ n) (ht : t = 1 ∨ t = -1) :
    0 ≤ n * (x * x) + 2 * t * x ∧ (x ≠ 0 → 4 ≤ n * (x * x) + 2 * t * x) := by
  have hx2 : 0 ≤ x * x := mul_self_nonneg x
  have h6 : 6 * (x * x) ≤ n * (x * x) := by nlinarith
  rcases ht with rfl | rfl
  · refine ⟨by rcases le_or_gt 0 x with h | h <;> nlinarith, fun hx => ?_⟩
    rcases lt_or_gt_of_ne hx with h | h <;> nlinarith
  · refine ⟨by rcases le_or_gt 0 x with h | h <;> nlinarith, fun hx => ?_⟩
    rcases lt_or_gt_of_ne hx with h | h <;> nlinarith

namespace EtaData

variable (D : S.EtaData)

@[expose] def IsExc (χ : G → ℂ) : Prop := (∃ i, χ = D.η i) ∨ ∃ i, χ = D.η' i

@[expose] noncomputable def NE : Finset (G → ℂ) :=
  (irreducibles_finite G).toFinset.filter fun χ => ¬ D.IsExc χ

theorem mem_NE {χ : G → ℂ} : χ ∈ D.NE ↔ χ ∈ BlocksIrr G ∧ ¬ D.IsExc χ := by
  rw [NE, Finset.mem_filter, Set.Finite.mem_toFinset]

theorem NE_ne_η {χ : G → ℂ} (h : χ ∈ D.NE) (i : S.W.RFam) : χ ≠ D.η i := fun hi =>
  (D.mem_NE.mp h).2 (Or.inl ⟨i, hi⟩)

theorem NE_ne_η' {χ : G → ℂ} (h : χ ∈ D.NE) (i : S.W.RFam) : χ ≠ D.η' i := fun hi =>
  (D.mem_NE.mp h).2 (Or.inr ⟨i, hi⟩)

theorem sum_split {M : Type*} [AddCommMonoid M] (f : (G → ℂ) → M) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, f χ =
      ∑ i, f (D.η i) + ∑ i, f (D.η' i) + ∑ χ ∈ D.NE, f χ := by
  have hη : Finset.univ.image D.η ⊆ (irreducibles_finite G).toFinset := by
    intro χ hχ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hχ
    rw [Set.Finite.mem_toFinset]; exact D.mem i
  have hη' : Finset.univ.image D.η' ⊆ (irreducibles_finite G).toFinset := by
    intro χ hχ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hχ
    rw [Set.Finite.mem_toFinset]; exact D.mem' i
  have hdisj : Disjoint (Finset.univ.image D.η) (Finset.univ.image D.η') := by
    rw [Finset.disjoint_left]
    intro χ h1 h2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h2
    exact D.disj i k hk.symm
  have hunion : (irreducibles_finite G).toFinset =
      (Finset.univ.image D.η ∪ Finset.univ.image D.η') ∪ D.NE := by
    ext χ
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, D.mem_NE, IsExc]
    constructor
    · intro hχ
      by_cases h1 : ∃ i, χ = D.η i
      · obtain ⟨i, rfl⟩ := h1; exact Or.inl (Or.inl ⟨i, rfl⟩)
      · by_cases h2 : ∃ i, χ = D.η' i
        · obtain ⟨i, rfl⟩ := h2; exact Or.inl (Or.inr ⟨i, rfl⟩)
        · rw [Set.Finite.mem_toFinset] at hχ
          exact Or.inr ⟨hχ, by tauto⟩
    · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨hχ, -⟩)
      · exact hη (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · exact hη' (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · rw [Set.Finite.mem_toFinset]; exact hχ
  have hdisj2 : Disjoint (Finset.univ.image D.η ∪ Finset.univ.image D.η') D.NE := by
    rw [Finset.disjoint_left]
    intro χ h1 h2
    have := (D.mem_NE.mp h2).2
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h1
    rcases h1 with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact this (Or.inl ⟨i, rfl⟩)
    · exact this (Or.inr ⟨i, rfl⟩)
  rw [hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj,
    Finset.sum_image (fun i _ j _ h => D.inj h), Finset.sum_image (fun i _ j _ h => D.inj' h)]

theorem ma_NE {χ : G → ℂ} (h : χ ∈ D.NE) (i j : S.W.RFam) : S.ma χ i.1 = S.ma χ j.1 := by
  have := D.ma_other χ (D.mem_NE.mp h).1 i j
  simp only [D.NE_ne_η h, ↓reduceIte, sub_self, mul_zero, sub_eq_zero] at this
  exact_mod_cast this

theorem mb_NE {χ : G → ℂ} (h : χ ∈ D.NE) (i j : S.W.RFam) : S.mb χ i.1 = S.mb χ j.1 := by
  have := D.mb_other χ (D.mem_NE.mp h).1 i j
  simp only [D.NE_ne_η' h, ↓reduceIte, sub_self, mul_zero, sub_eq_zero] at this
  exact_mod_cast this

@[expose] noncomputable def z (χ : G → ℂ) : ℤ :=
  S.Ar χ 1 - e * S.Ar χ S.W.θ4 + e * S.Ar χ S.i₀.1

theorem τ_NE {χ : G → ℂ} (h : χ ∈ D.NE) {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    χ (S.κ r) = z (S := S) χ := by
  rw [S.τ_Ro (D.mem_NE.mp h).1 hr hr1]
  have hconst : ∀ θ ∈ S.W.RFam, S.Ar χ θ = S.Ar χ S.i₀.1 := by
    intro θ hθ
    simp only [Ar, D.ma_NE h ⟨θ, hθ⟩ S.i₀, D.mb_NE h ⟨θ, hθ⟩ S.i₀]
  rw [Finset.sum_congr rfl fun θ hθ => by rw [hconst θ hθ], ← Finset.mul_sum,
    S.W.sum_R_Ro hr hr1, z]
  push_cast
  ring

theorem Ar_η_diff (i k l : S.W.RFam) :
    S.Ar (D.η i) k.1 - S.Ar (D.η i) l.1 =
      D.ε * ((if i = k then 1 else 0) - (if i = l then 1 else 0)) := by
  have h1 := D.ma_other (D.η i) (D.mem i) k l
  have h2 := D.mb_other (D.η i) (D.mem i) k l
  simp only [D.inj.eq_iff, fun m => D.disj i m, ↓reduceIte, sub_self, mul_zero] at h1 h2
  simp only [Ar]
  linear_combination h1 + h2

theorem Ar_η_diff' (i j k : S.W.RFam) :
    S.Ar (D.η i) k.1 - S.Ar (D.η j) k.1 =
      D.ε * ((if i = k then 1 else 0) - (if j = k then 1 else 0)) := by
  have h1 := D.ma_η i j k.1 (S.W.R_mem k.2)
  have h2 := D.mb_η i j k.1 (S.W.R_mem k.2)
  simp only [Ar, h2]
  have hik : (k.1 = i.1) ↔ (i = k) := by rw [eq_comm, Subtype.ext_iff]
  have hjk : (k.1 = j.1) ↔ (j = k) := by rw [eq_comm, Subtype.ext_iff]
  simp only [hik, hjk] at h1
  linear_combination h1

theorem Ar_η'_diff (i k l : S.W.RFam) :
    S.Ar (D.η' i) k.1 - S.Ar (D.η' i) l.1 =
      D.ε' * ((if i = k then 1 else 0) - (if i = l then 1 else 0)) := by
  have h1 := D.ma_other (D.η' i) (D.mem' i) k l
  have h2 := D.mb_other (D.η' i) (D.mem' i) k l
  simp only [D.inj'.eq_iff, fun m => (D.disj m i).symm, ↓reduceIte, sub_self, mul_zero] at h1 h2
  simp only [Ar]
  linear_combination h1 + h2

theorem Ar_η'_diff' (i j k : S.W.RFam) :
    S.Ar (D.η' i) k.1 - S.Ar (D.η' j) k.1 =
      D.ε' * ((if i = k then 1 else 0) - (if j = k then 1 else 0)) := by
  have h1 := D.ma_η' i j k.1 (S.W.R_mem k.2)
  have h2 := D.mb_η' i j k.1 (S.W.R_mem k.2)
  simp only [Ar, h1]
  have hik : (k.1 = i.1) ↔ (i = k) := by rw [eq_comm, Subtype.ext_iff]
  have hjk : (k.1 = j.1) ↔ (j = k) := by rw [eq_comm, Subtype.ext_iff]
  simp only [hik, hjk] at h2
  linear_combination h2

@[expose] noncomputable def xη : ℤ :=
  S.Ar (D.η S.i₀) 1 - e * S.Ar (D.η S.i₀) S.W.θ4 + e * S.Ar (D.η S.i₁) S.i₀.1

@[expose] noncomputable def xη' : ℤ :=
  S.Ar (D.η' S.i₀) 1 - e * S.Ar (D.η' S.i₀) S.W.θ4 + e * S.Ar (D.η' S.i₁) S.i₀.1

theorem τ_η (i : S.W.RFam) {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    D.η i (S.κ r) = D.xη + D.ε * i.1 r := by
  rw [S.τ_Ro (D.mem i) hr hr1]
  have hoff := offdiag_const (fun i k : S.W.RFam => S.Ar (D.η i) k.1) D.ε D.Ar_η_diff
    D.Ar_η_diff' (exists_third (S := S)) _ _ S.i₁_ne
  have hsum : ∑ θ ∈ S.W.RFam, (S.Ar (D.η i) θ : ℂ) * θ r =
      (S.Ar (D.η S.i₁) S.i₀.1 : ℂ) * e +
        D.ε * i.1 r := by
    rw [← Finset.sum_attach]
    simp_rw [show ∀ k : S.W.RFam, (S.Ar (D.η i) k.1 : ℂ) =
        S.Ar (D.η S.i₁) S.i₀.1 +
          if i = k then (D.ε : ℂ) else 0 from fun k => by
            rw [hoff i k]; push_cast; split_ifs <;> simp]
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte]
    rw [Finset.sum_attach S.W.RFam (fun θ => θ r), S.W.sum_R_Ro hr hr1]
  rw [hsum, xη, D.Ar_η_const i S.i₀ S.W.one_mem S.W.one_not_R,
    D.Ar_η_const i S.i₀ S.W.θ4_mem S.W.θ4_not_R]
  push_cast
  ring

theorem τ_η' (i : S.W.RFam) {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    D.η' i (S.κ r) = D.xη' + D.ε * i.1 r := by
  rw [S.τ_Ro (D.mem' i) hr hr1]
  have hoff := offdiag_const (fun i k : S.W.RFam => S.Ar (D.η' i) k.1) D.ε' D.Ar_η'_diff
    D.Ar_η'_diff' (exists_third (S := S)) _ _ S.i₁_ne
  have hsum : ∑ θ ∈ S.W.RFam, (S.Ar (D.η' i) θ : ℂ) * θ r =
      (S.Ar (D.η' S.i₁) S.i₀.1 : ℂ) * e +
        D.ε' * i.1 r := by
    rw [← Finset.sum_attach]
    simp_rw [show ∀ k : S.W.RFam, (S.Ar (D.η' i) k.1 : ℂ) =
        S.Ar (D.η' S.i₁) S.i₀.1 +
          if i = k then (D.ε' : ℂ) else 0 from fun k => by
            rw [hoff i k]; push_cast; split_ifs <;> simp]
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte]
    rw [Finset.sum_attach S.W.RFam (fun θ => θ r), S.W.sum_R_Ro hr hr1]
  rw [hsum, xη', D.Ar_η'_const i S.i₀ S.W.one_mem S.W.one_not_R,
    D.Ar_η'_const i S.i₀ S.W.θ4_mem S.W.θ4_not_R, ← D.ε_eq_ε'.1]
  push_cast
  ring

theorem one_NE : (1 : G → ℂ) ∈ D.NE := by
  rw [D.mem_NE]
  refine ⟨one_mem_blocksIrr G, ?_⟩
  rintro (⟨k, hk⟩ | ⟨k, hk⟩)
  · have h := D.dR_η k k
    rw [← hk, ite_eq_left rfl] at h
    have h0 : S.dR (1 : G → ℂ) k.1 = 0 := M_one_R k.2
    rcases D.ε_eq with he | he <;> omega
  · have h := D.dR_η' k k
    rw [← hk, ite_eq_left rfl] at h
    have h0 : S.dR (1 : G → ℂ) k.1 = 0 := M_one_R k.2
    rcases D.ε'_eq with he | he <;> omega

theorem z_one : z (S := S) (1 : G → ℂ) = 1 := by
  have hA : ∀ θ ∈ BlocksIrr L, S.Ar (1 : G → ℂ) θ = if (1 : L → ℂ) = θ then 1 else 0 := by
    intro θ hθ
    have h := S.inner_τ (one_mem_blocksIrr G) hθ
    have hτ : S.τ (1 : G → ℂ) = (1 : L → ℂ) := rfl
    rw [hτ, blocksInnerProduct_irr S.W.one_mem hθ] at h
    split_ifs at h ⊢ <;> exact_mod_cast h.symm
  have hi : (1 : L → ℂ) ≠ S.i₀.1 := fun h => S.W.one_not_R (by rw [h]; exact S.i₀.2)
  rw [z, hA 1 S.W.one_mem, hA _ S.W.θ4_mem, hA _ (S.W.R_mem S.i₀.2), ite_eq_left rfl,
    ite_eq_right S.W.one_ne_θ4, ite_eq_right hi]
  ring

theorem sum_sq_family {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) (c : ℤ) :
    ∑ i : S.W.RFam, ((c : ℂ) + D.ε * i.1 r) * starRingEnd ℂ ((c : ℂ) + D.ε * i.1 r) =
      (Fintype.card S.W.RFam : ℂ) * (c * c) + 2 * c * D.ε * e + ((Nat.card S.W.Ro : ℂ) - 2) := by
  have hε : (D.ε : ℂ) * D.ε = 1 := by exact_mod_cast D.ε_sq
  calc ∑ i : S.W.RFam, ((c : ℂ) + D.ε * i.1 r) * starRingEnd ℂ ((c : ℂ) + D.ε * i.1 r)
      = ∑ i : S.W.RFam, ((c : ℂ) * c + 2 * c * D.ε * i.1 r + i.1 r * i.1 r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_add, map_mul, map_intCast, map_intCast, S.W.conj_apply_R i.2]
        linear_combination (i.1 r * i.1 r) * hε
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
          Finset.sum_coe_sort S.W.RFam (fun θ => θ r),
          Finset.sum_coe_sort S.W.RFam (fun θ => θ r * θ r), S.W.sum_R_Ro hr hr1,
          S.W.sum_sq_R_Ro hr hr1, Finset.card_univ, nsmul_eq_mul]

theorem col_κR {S : WardSetup G L q e} (D : S.EtaData) {r : L} (hr : r ∈ S.W.Ro)
    (hr1 : r ≠ 1) :
    (Fintype.card S.W.RFam : ℤ) * (D.xη * D.xη) + 2 * (e * D.ε) * D.xη +
      ((Fintype.card S.W.RFam : ℤ) * (D.xη' * D.xη') + 2 * (e * D.ε) * D.xη') +
      ∑ χ ∈ D.NE, z (S := S) χ * z (S := S) χ = 4 := by
  have h := sum_irr_mul_conj (S.κ r) (S.κ r)
  rw [ite_eq_left (IsConj.refl _), S.card_centralizer_κR' hr hr1, D.sum_split] at h
  have h1 : ∑ i, D.η i (S.κ r) * starRingEnd ℂ (D.η i (S.κ r)) =
      ∑ i : S.W.RFam, ((D.xη : ℂ) + D.ε * i.1 r) * starRingEnd ℂ ((D.xη : ℂ) + D.ε * i.1 r) :=
    Finset.sum_congr rfl fun i _ => by rw [D.τ_η i hr hr1]
  have h2 : ∑ i, D.η' i (S.κ r) * starRingEnd ℂ (D.η' i (S.κ r)) =
      ∑ i : S.W.RFam, ((D.xη' : ℂ) + D.ε * i.1 r) * starRingEnd ℂ ((D.xη' : ℂ) + D.ε * i.1 r) :=
    Finset.sum_congr rfl fun i _ => by rw [D.τ_η' i hr hr1]
  have h3 : ∑ χ ∈ D.NE, χ (S.κ r) * starRingEnd ℂ (χ (S.κ r)) =
      ∑ χ ∈ D.NE, (z (S := S) χ : ℂ) * (z (S := S) χ : ℂ) :=
    Finset.sum_congr rfl fun χ hχ => by rw [D.τ_NE hχ hr hr1, map_intCast]
  rw [h1, h2, h3, D.sum_sq_family hr hr1, D.sum_sq_family hr hr1] at h
  have : (((Fintype.card S.W.RFam : ℤ) * (D.xη * D.xη) + 2 * (e * D.ε) * D.xη +
      ((Fintype.card S.W.RFam : ℤ) * (D.xη' * D.xη') + 2 * (e * D.ε) * D.xη') +
      ∑ χ ∈ D.NE, z (S := S) χ * z (S := S) χ : ℤ) : ℂ) = ((4 : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  exact_mod_cast this

theorem x_zero {S : WardSetup G L q e} (D : S.EtaData) :
    D.xη = 0 ∧ D.xη' = 0 ∧ ∑ χ ∈ D.NE, z (S := S) χ * z (S := S) χ = 4 := by
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have h := D.col_κR hr hr1
  have hn : (6 : ℤ) ≤ Fintype.card S.W.RFam := by exact_mod_cast card_ge (S := S)
  have ht : e * D.ε = 1 ∨ e * D.ε = -1 := by
    have h1 : (e * D.ε) * (e * D.ε) = 1 := by
      rw [mul_mul_mul_comm, S.W.e_sq, D.ε_sq, one_mul]
    exact mul_self_eq_one_iff.mp h1
  obtain ⟨hA, hA'⟩ := quad_ge (x := D.xη) hn ht
  obtain ⟨hB, hB'⟩ := quad_ge (x := D.xη') hn ht
  have hC : 1 ≤ ∑ χ ∈ D.NE, z (S := S) χ * z (S := S) χ := by
    have := Finset.single_le_sum (f := fun χ => z (S := S) χ * z (S := S) χ)
      (fun χ _ => mul_self_nonneg _) D.one_NE
    simp only [z_one (S := S), mul_one] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · by_contra hx
    have := hA' hx
    linarith
  · by_contra hx
    have := hB' hx
    linarith
  · have hx : D.xη = 0 := by
      by_contra hx
      have := hA' hx
      linarith
    have hx' : D.xη' = 0 := by
      by_contra hx
      have := hB' hx
      linarith
    rw [hx, hx'] at h
    linarith

theorem τ_η_eq {S : WardSetup G L q e} (D : S.EtaData) (i : S.W.RFam) {r : L}
    (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    D.η i (S.κ r) = D.ε * i.1 r := by
  rw [D.τ_η i hr hr1, D.x_zero.1]
  simp

theorem τ_η'_eq {S : WardSetup G L q e} (D : S.EtaData) (i : S.W.RFam) {r : L}
    (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    D.η' i (S.κ r) = D.ε * i.1 r := by
  rw [D.τ_η' i hr hr1, D.x_zero.2.1]
  simp

theorem d1_sq_le {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : S.d1 χ * S.d1 χ ≤ 1 := by
  obtain ⟨g11, -⟩ := S.gram_principal
  have horth := S.orth S.d1 (fun χ hχ => S.inner_Φ1 hχ) (x := 1)
    (by rw [orderOf_one]; exact odd_one)
  have hmem : χ ∈ (irreducibles_finite G).toFinset := by rw [Set.Finite.mem_toFinset]; exact hχ
  by_contra hlt
  push Not at hlt
  have h4 : 4 ≤ S.d1 χ * S.d1 χ := by
    have h1 : 2 ≤ |S.d1 χ| := by
      by_contra h
      push Not at h
      have : |S.d1 χ| * |S.d1 χ| ≤ 1 := by
        have h0 : 0 ≤ |S.d1 χ| := abs_nonneg _
        nlinarith
      rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at this
      omega
    have := mul_le_mul h1 h1 (by norm_num) (abs_nonneg _)
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at this
    linarith
  rw [← Finset.add_sum_erase _ _ hmem] at g11
  have hrest : ∑ χ' ∈ (irreducibles_finite G).toFinset.erase χ, S.d1 χ' * S.d1 χ' = 0 := by
    have hnn : 0 ≤ ∑ χ' ∈ (irreducibles_finite G).toFinset.erase χ, S.d1 χ' * S.d1 χ' :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    linarith
  have hzero : ∀ χ' ∈ (irreducibles_finite G).toFinset.erase χ, S.d1 χ' = 0 := by
    intro χ' hχ'
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)).mp hrest χ' hχ'
    exact zero_eq_mul_self.mp this.symm
  rw [← Finset.add_sum_erase _ _ hmem,
    Finset.sum_eq_zero (fun χ' hχ' => by rw [hzero χ' hχ']; simp), add_zero, conj_one hχ] at horth
  obtain ⟨n, hn, hn'⟩ := exists_deg hχ
  rw [hn'] at horth
  have hd : S.d1 χ ≠ 0 := by
    intro h0
    rw [h0] at hlt
    simp at hlt
  have : ((S.d1 χ * n : ℤ) : ℂ) = 0 := by push_cast; exact horth
  have := (mul_eq_zero.mp (by exact_mod_cast this : S.d1 χ * (n : ℤ) = 0))
  omega

theorem z_parity {χ : G → ℂ} (h : χ ∈ D.NE) : ∃ k : ℤ, z (S := S) χ = S.d1 χ + 2 * k := by
  have hM : S.M χ S.i₀.1 = 0 :=
    D.dR_other (D.mem_NE.mp h).1 (D.NE_ne_η h) (D.NE_ne_η' h) S.i₀
  refine ⟨S.mb χ 1 - e * S.mb χ S.W.θ4 + e * S.mb χ S.i₀.1, ?_⟩
  have h1 := S.two_mb χ 1
  have h4 := S.two_mb χ S.W.θ4
  have hi := S.two_mb χ S.i₀.1
  simp only [z, d1]
  linear_combination (-1 : ℤ) * h1 + e * h4 - e * hi + e * hM

theorem sum_NE_d1 : ∑ χ ∈ D.NE, S.d1 χ * S.d1 χ = 4 := by
  have h := (S.gram_principal).1
  rw [D.sum_split] at h
  simp only [fun i => (D.η_d i).1, fun i => (D.η'_d i).1, mul_zero, Finset.sum_const_zero,
    zero_add] at h
  exact h

theorem z_sq_eq {S : WardSetup G L q e} (D : S.EtaData) {χ : G → ℂ} (h : χ ∈ D.NE) :
    z (S := S) χ * z (S := S) χ = S.d1 χ * S.d1 χ := by
  have hle : ∀ ξ ∈ D.NE, S.d1 ξ * S.d1 ξ ≤ z (S := S) ξ * z (S := S) ξ := by
    intro ξ hξ
    obtain ⟨k, hk⟩ := D.z_parity hξ
    have hd := d1_sq_le (S := S) (D.mem_NE.mp hξ).1
    rw [hk]
    have hcases : S.d1 ξ = 0 ∨ S.d1 ξ = 1 ∨ S.d1 ξ = -1 := by
      have : -1 ≤ S.d1 ξ ∧ S.d1 ξ ≤ 1 := by constructor <;> nlinarith
      omega
    rcases hcases with h0 | h0 | h0 <;> rw [h0] <;>
      rcases (show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega) with hk0 | hk0 | hk0 <;> nlinarith
  have hsum : ∑ ξ ∈ D.NE, (z (S := S) ξ * z (S := S) ξ - S.d1 ξ * S.d1 ξ) = 0 := by
    rw [Finset.sum_sub_distrib, D.x_zero.2.2, D.sum_NE_d1, sub_self]
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun ξ hξ => sub_nonneg.mpr (hle ξ hξ))).mp hsum χ h
  linarith

theorem σ_NE_R {χ : G → ℂ} (h : χ ∈ D.NE) {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    S.σ χ r = S.d1 χ := by
  have hodd : Odd (orderOf r) := S.orderOf_Ro_odd hr
  obtain ⟨h2, h3, -, hS⟩ := S.W.val_Ro r hr hr1
  rw [S.σ_decomp (D.mem_NE.mp h).1 hodd, h2, h3,
    Finset.sum_eq_zero (s := S.W.RFam) (fun θ hθ => by
      rw [show S.dR χ θ = 0 from
        D.dR_other (D.mem_NE.mp h).1 (D.NE_ne_η h) (D.NE_ne_η' h) ⟨θ, hθ⟩]; simp),
    Finset.sum_eq_zero (s := S.W.SFam) (fun θ hθ => by rw [hS θ hθ, mul_zero])]
  simp

end EtaData

end WardSetup

end CFSG.Walter.Ward
