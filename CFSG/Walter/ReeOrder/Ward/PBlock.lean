module

public import CFSG.Walter.ReeOrder.Ward.FSCount
public import CFSG.Walter.ReeOrder.Ward.Formula
public import CFSG.Walter.ReeOrder.Ward.Values

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G]

theorem agree (d d' : (G → ℂ) → ℤ)
    (hn : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d χ = 4)
    (hn' : ∑ χ ∈ (irreducibles_finite G).toFinset, d' χ * d' χ = 4)
    (hdd : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d' χ = 2)
    (ho : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ = 0)
    (ho' : ∑ χ ∈ (irreducibles_finite G).toFinset, d' χ * deg χ = 0)
    {χ : G → ℂ} (h : χ ∈ supp d) (h' : χ ∈ supp d') : d χ = d' χ := by
  obtain ⟨hχ, hd⟩ := mem_supp.mp h
  obtain ⟨-, hd'⟩ := mem_supp.mp h'
  set c : (G → ℂ) → ℤ := fun ψ => d ψ - d' ψ with hc
  have hcn : ∑ ψ ∈ (irreducibles_finite G).toFinset, c ψ * c ψ = 4 := by
    have : ∀ ψ, c ψ * c ψ = d ψ * d ψ + d' ψ * d' ψ - 2 * (d ψ * d' ψ) := fun ψ => by
      simp only [hc]; ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hn, hn',
      hdd]
    norm_num
  have hco : ∑ ψ ∈ (irreducibles_finite G).toFinset, c ψ * deg ψ = 0 := by
    simp only [hc, sub_mul, Finset.sum_sub_distrib, ho, ho', sub_zero]
  have hcase := entry_cases c hcn hco hχ
  have h1 := entry_cases d hn ho hχ
  have h2 := entry_cases d' hn' ho' hχ
  simp only [hc] at hcase
  omega

theorem card_inter (d d' : (G → ℂ) → ℤ)
    (hn : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d χ = 4)
    (hn' : ∑ χ ∈ (irreducibles_finite G).toFinset, d' χ * d' χ = 4)
    (hdd : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d' χ = 2)
    (ho : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * deg χ = 0)
    (ho' : ∑ χ ∈ (irreducibles_finite G).toFinset, d' χ * deg χ = 0) :
    (supp d ∩ supp d').card = 2 := by
  have hsub : supp d ∩ supp d' ⊆ (irreducibles_finite G).toFinset :=
    Finset.inter_subset_left.trans (supp_sub d)
  have hvan : ∀ χ ∈ (irreducibles_finite G).toFinset, χ ∉ supp d ∩ supp d' →
      d χ * d' χ = 0 := by
    intro χ hχ hnot
    rw [Set.Finite.mem_toFinset] at hχ
    rw [Finset.mem_inter, not_and_or] at hnot
    rcases hnot with h | h
    · simp only [eq_zero_of_not_mem_supp hχ h, zero_mul]
    · simp only [eq_zero_of_not_mem_supp hχ h, mul_zero]
  have h1 : ∑ χ ∈ supp d ∩ supp d', d χ * d' χ = 2 := by
    rw [← sum_irr_eq_sum_of_vanish hsub _ hvan]
    exact hdd
  have h2 : ∀ χ ∈ supp d ∩ supp d', d χ * d' χ = 1 := by
    intro χ hχ
    rw [← agree d d' hn hn' hdd ho ho' (Finset.mem_inter.mp hχ).1 (Finset.mem_inter.mp hχ).2]
    exact sq_of_mem_supp d hn ho (Finset.mem_inter.mp hχ).1
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  exact_mod_cast h1

namespace WardSetup

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (S : WardSetup G L q e)

@[expose] noncomputable def S1 : Finset (G → ℂ) := supp S.d1
@[expose] noncomputable def S2 : Finset (G → ℂ) := supp S.d2
@[expose] noncomputable def S3 : Finset (G → ℂ) := supp S.d3

theorem g12 : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.d2 χ = 2 :=
  S.gram_principal.2.1
theorem g13 : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.d3 χ = 2 :=
  S.gram_principal.2.2.1
theorem g23 : ∑ χ ∈ (irreducibles_finite G).toFinset, S.d2 χ * S.d3 χ = 2 :=
  S.gram_principal.2.2.2.2.1

theorem card_S1 : S.S1.card = 4 := card_supp _ S.d1_norm S.d1_orth
theorem card_S2 : S.S2.card = 4 := card_supp _ S.d2_norm S.d2_orth
theorem card_S3 : S.S3.card = 4 := card_supp _ S.d3_norm S.d3_orth

theorem card_S12 : (S.S1 ∩ S.S2).card = 2 :=
  card_inter _ _ S.d1_norm S.d2_norm S.g12 S.d1_orth S.d2_orth
theorem card_S13 : (S.S1 ∩ S.S3).card = 2 :=
  card_inter _ _ S.d1_norm S.d3_norm S.g13 S.d1_orth S.d3_orth
theorem card_S23 : (S.S2 ∩ S.S3).card = 2 :=
  card_inter _ _ S.d2_norm S.d3_norm S.g23 S.d2_orth S.d3_orth

theorem agree12 {χ : G → ℂ} (h1 : χ ∈ S.S1) (h2 : χ ∈ S.S2) : S.d1 χ = S.d2 χ :=
  agree _ _ S.d1_norm S.d2_norm S.g12 S.d1_orth S.d2_orth h1 h2
theorem agree13 {χ : G → ℂ} (h1 : χ ∈ S.S1) (h3 : χ ∈ S.S3) : S.d1 χ = S.d3 χ :=
  agree _ _ S.d1_norm S.d3_norm S.g13 S.d1_orth S.d3_orth h1 h3
theorem agree23 {χ : G → ℂ} (h2 : χ ∈ S.S2) (h3 : χ ∈ S.S3) : S.d2 χ = S.d3 χ :=
  agree _ _ S.d2_norm S.d3_norm S.g23 S.d2_orth S.d3_orth h2 h3

theorem sq1 {χ : G → ℂ} (h : χ ∈ S.S1) : S.d1 χ * S.d1 χ = 1 :=
  sq_of_mem_supp _ S.d1_norm S.d1_orth h
theorem sq2 {χ : G → ℂ} (h : χ ∈ S.S2) : S.d2 χ * S.d2 χ = 1 :=
  sq_of_mem_supp _ S.d2_norm S.d2_orth h
theorem sq3 {χ : G → ℂ} (h : χ ∈ S.S3) : S.d3 χ * S.d3 χ = 1 :=
  sq_of_mem_supp _ S.d3_norm S.d3_orth h

theorem van1 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∉ S.S1) : S.d1 χ = 0 :=
  eq_zero_of_not_mem_supp hχ h
theorem van2 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∉ S.S2) : S.d2 χ = 0 :=
  eq_zero_of_not_mem_supp hχ h
theorem van3 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∉ S.S3) : S.d3 χ = 0 :=
  eq_zero_of_not_mem_supp hχ h

theorem M_one {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    S.M (1 : G → ℂ) θ = if (1 : L → ℂ) = θ then 1 else 0 := by
  have h := S.inner_σ (one_mem_blocksIrr G) hθ
  have hσ : S.σ (1 : G → ℂ) = (1 : L → ℂ) := rfl
  rw [hσ, blocksInnerProduct_irr S.W.one_mem hθ] at h
  split_ifs at h ⊢ <;> exact_mod_cast h.symm

theorem one_row : S.d1 (1 : G → ℂ) = 1 ∧ S.d2 (1 : G → ℂ) = 0 ∧ S.d3 (1 : G → ℂ) = 0 := by
  obtain ⟨h12, h13, h14, -, -, -⟩ := S.W.principal_ne
  simp only [d1, d2, d3, S.M_one S.W.one_mem, S.M_one S.W.θ2_mem, S.M_one S.W.θ3_mem,
    S.M_one S.W.θ4_mem, h12, h13, h14, ↓reduceIte]
  norm_num

theorem one_S1 : (1 : G → ℂ) ∈ S.S1 :=
  mem_supp.mpr ⟨one_mem_blocksIrr G, by rw [S.one_row.1]; norm_num⟩
theorem one_not_S2 : (1 : G → ℂ) ∉ S.S2 := fun h => (mem_supp.mp h).2 S.one_row.2.1
theorem one_not_S3 : (1 : G → ℂ) ∉ S.S3 := fun h => (mem_supp.mp h).2 S.one_row.2.2

theorem P_rows {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∈ S.S1 ∨ χ ∈ S.S2 ∨ χ ∈ S.S3) :
    (∀ θ ∈ S.W.RFam, S.dR χ θ = 0) ∧ (∀ θ ∈ S.W.SFam, S.dS χ θ = 0) := by
  apply S.principal_rows hχ
  rcases h with h | h | h
  · exact Or.inl (mem_supp.mp h).2
  · exact Or.inr (Or.inl (mem_supp.mp h).2)
  · exact Or.inr (Or.inr (mem_supp.mp h).2)

theorem J_val_P {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∈ S.S1 ∨ χ ∈ S.S2 ∨ χ ∈ S.S3) :
    χ S.J = S.d1 χ - (e : ℂ) * (((q : ℂ) + e) / 2) * (S.d2 χ + S.d3 χ) := by
  obtain ⟨hR, hS⟩ := S.P_rows hχ h
  have hd := S.σ_decomp hχ (y := 1) (by rw [orderOf_one]; exact odd_one)
  have hσ : S.σ χ 1 = χ S.J := by simp [σ]
  rw [hσ, Finset.sum_eq_zero (fun θ hθ => by rw [hR θ hθ]; simp),
    Finset.sum_eq_zero (fun θ hθ => by rw [hS θ hθ]; simp), S.W.deg2, S.W.deg3] at hd
  rw [hd]
  ring

theorem formula_S1 :
    (Nat.card G : ℂ) * ∑ χ ∈ S.S1, χ S.J ^ 2 * S.d1 χ / χ 1 =
      q ^ 2 * ((q : ℂ) ^ 2 - 1) ^ 2 * (q + e) := by
  rw [← S.formula_Φ1]
  congr 1
  exact (sum_irr_eq_sum_of_vanish (supp_sub _) _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van1 hχ hnot]
    simp).symm

theorem formula_S2 :
    (Nat.card G : ℂ) * ∑ χ ∈ S.S2, χ S.J ^ 2 * S.d2 χ / χ 1 =
      -e * q ^ 2 * ((q : ℂ) ^ 2 - 1) * (q + e) * (3 * q + e) := by
  rw [← S.formula_Φ2]
  congr 1
  exact (sum_irr_eq_sum_of_vanish (supp_sub _) _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van2 hχ hnot]
    simp).symm

theorem R3 : ∑ χ ∈ S.S1, S.d1 χ * deg χ = 0 := by
  rw [← S.d1_orth]
  exact (sum_irr_eq_sum_of_vanish (supp_sub _) _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van1 hχ hnot, zero_mul]).symm

theorem deg2_S2 : ∑ χ ∈ S.S2, S.d2 χ * deg χ = 0 := by
  rw [← S.d2_orth]
  exact (sum_irr_eq_sum_of_vanish (supp_sub _) _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van2 hχ hnot, zero_mul]).symm

theorem FS1 : ∑ χ ∈ S.S1, nu χ * S.d1 χ = 0 := by
  rw [← S.fs_col (fun y hy => S.W.Φ1_even hy) S.d1 (fun χ hχ => S.inner_Φ1 hχ)]
  exact (sum_irr_eq_sum_of_vanish (supp_sub _) _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van1 hχ hnot, mul_zero]).symm

theorem FS2 : ∑ χ ∈ S.S2, nu χ * S.d2 χ = 0 := by
  rw [← S.fs_col (fun y hy => S.W.Φ2_even hy) S.d2 (fun χ hχ => S.inner_Φ2 hχ)]
  exact (sum_irr_eq_sum_of_vanish (supp_sub _) _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van2 hχ hnot, mul_zero]).symm

theorem FS3 : ∑ χ ∈ S.S3, nu χ * S.d3 χ = 0 := by
  rw [← S.fs_col (fun y hy => S.W.Φ3_even hy) S.d3 (fun χ hχ => S.inner_Φ3 hχ)]
  exact (sum_irr_eq_sum_of_vanish (supp_sub _) _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van3 hχ hnot, mul_zero]).symm

namespace EtaData

variable {S} (D : S.EtaData)

theorem S1_NE {χ : G → ℂ} (h : χ ∈ S.S1) : χ ∈ D.NE := by
  rw [D.mem_NE]
  refine ⟨(mem_supp.mp h).1, ?_⟩
  rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact (mem_supp.mp h).2 (D.η_d i).1
  · exact (mem_supp.mp h).2 (D.η'_d i).1

include D in
theorem z_S1 {χ : G → ℂ} (h : χ ∈ S.S1) : z (S := S) χ * z (S := S) χ = 1 := by
  rw [D.z_sq_eq (D.S1_NE h), S.sq1 h]

theorem z_off {χ : G → ℂ} (h : χ ∈ D.NE) (h1 : χ ∉ S.S1) : z (S := S) χ = 0 := by
  have := D.z_sq_eq h
  rw [S.van1 (D.mem_NE.mp h).1 h1, mul_zero] at this
  exact zero_eq_mul_self.mp this.symm

theorem sum_NE_z (f : (G → ℂ) → ℂ) :
    ∑ χ ∈ D.NE, f χ * z (S := S) χ = ∑ χ ∈ S.S1, f χ * z (S := S) χ := by
  have hsub : S.S1 ⊆ D.NE := fun χ h => D.S1_NE h
  exact (Finset.sum_subset hsub fun χ h h1 => by rw [D.z_off h h1]; simp).symm

theorem orth_z {Φ : L → ℂ} (d : (G → ℂ) → ℤ)
    (hd : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) Φ = d χ) (hη : ∀ i, d (D.η i) = 0)
    (hη' : ∀ i, d (D.η' i) = 0) : ∑ χ ∈ S.S1, d χ * z (S := S) χ = 0 := by
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have hodd : Odd (orderOf (S.κ r)) := by rw [S.orderOf_κ]; exact S.orderOf_Ro_odd hr
  have h := S.orth d hd hodd
  rw [D.sum_split] at h
  simp only [hη, hη', Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add] at h
  rw [Finset.sum_congr rfl fun χ hχ => by rw [D.τ_NE hχ hr hr1, map_intCast],
    D.sum_NE_z (fun χ => (d χ : ℂ))] at h
  exact_mod_cast h

include D in
theorem R1 : ∑ χ ∈ S.S1, S.d1 χ * z (S := S) χ = 0 :=
  D.orth_z S.d1 (fun _ hχ => S.inner_Φ1 hχ) (fun i => (D.η_d i).1) (fun i => (D.η'_d i).1)
include D in
theorem O2 : ∑ χ ∈ S.S1, S.d2 χ * z (S := S) χ = 0 :=
  D.orth_z S.d2 (fun _ hχ => S.inner_Φ2 hχ) (fun i => (D.η_d i).2.1) (fun i => (D.η'_d i).2.1)
include D in
theorem O3 : ∑ χ ∈ S.S1, S.d3 χ * z (S := S) χ = 0 :=
  D.orth_z S.d3 (fun _ hχ => S.inner_Φ3 hχ) (fun i => (D.η_d i).2.2.1)
    (fun i => (D.η'_d i).2.2.1)

noncomputable def dη : ℤ := deg (D.η S.i₀)

theorem η_one (i : S.W.RFam) : D.η i 1 = D.dη := by
  rw [dη, deg_eq (D.mem S.i₀)]
  apply D.val 1 _ i S.i₀
  intro a
  simp only [mul_one, inv_mul_cancel]
  exact S.one_not_Kset

theorem η'_one (i : S.W.RFam) : D.η' i 1 = D.dη := by
  rw [← (D.ε_eq_ε').2 i, D.η_one]

theorem dη_pos : 0 < D.dη := deg_pos (D.mem S.i₀)

theorem η_J (i : S.W.RFam) : D.η i S.J = D.ε * ((q : ℂ) - e) := by
  have h := D.σ_η i (y := 1) (by rw [orderOf_one]; exact odd_one)
  simp only [σ, map_one, mul_one] at h
  rw [h, S.W.degR i.1 i.2]

theorem η'_J (i : S.W.RFam) : D.η' i S.J = -D.ε * ((q : ℂ) - e) := by
  have h := D.σ_η' i (y := 1) (by rw [orderOf_one]; exact odd_one)
  simp only [σ, map_one, mul_one] at h
  rw [h, S.W.degR i.1 i.2]

theorem R2 : 2 * D.ε * e * D.dη + ∑ χ ∈ S.S1, z (S := S) χ * deg χ = 0 := by
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have h := sum_irr_mul_conj (S.κ r) 1
  have hnc : ¬ IsConj (S.κ r) 1 := by
    rw [isConj_comm, isConj_one_right]
    intro h'
    exact hr1 (S.κ_inj (by rw [h', map_one]))
  rw [ite_eq_right hnc, D.sum_split] at h
  have hη : ∑ i, D.η i (S.κ r) * starRingEnd ℂ (D.η i 1) = D.ε * D.dη * e := by
    rw [Finset.sum_congr rfl fun i _ => by rw [D.τ_η_eq i hr hr1, D.η_one, map_intCast],
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_coe_sort S.W.RFam (fun θ => θ r),
      S.W.sum_R_Ro hr hr1]
    ring
  have hη' : ∑ i, D.η' i (S.κ r) * starRingEnd ℂ (D.η' i 1) = D.ε * D.dη * e := by
    rw [Finset.sum_congr rfl fun i _ => by rw [D.τ_η'_eq i hr hr1, D.η'_one, map_intCast],
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_coe_sort S.W.RFam (fun θ => θ r),
      S.W.sum_R_Ro hr hr1]
    ring
  have hN : ∑ χ ∈ D.NE, χ (S.κ r) * starRingEnd ℂ (χ 1) =
      ∑ χ ∈ S.S1, (z (S := S) χ : ℂ) * (deg χ : ℂ) := by
    rw [Finset.sum_congr rfl fun χ hχ => by
      rw [D.τ_NE hχ hr hr1, ← deg_eq (D.mem_NE.mp hχ).1, map_intCast, mul_comm]]
    rw [D.sum_NE_z (fun χ => (deg χ : ℂ))]
    exact Finset.sum_congr rfl fun χ _ => by ring
  rw [hη, hη', hN] at h
  have : ((2 * D.ε * e * D.dη + ∑ χ ∈ S.S1, z (S := S) χ * deg χ : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination h
  exact_mod_cast this

theorem F8 : ((q : ℂ) + e) * (Nat.card (Subgroup.centralizer ({S.J} : Set G)) : ℂ) ^ 2 =
    Nat.card G * (2 * ((q : ℂ) - e) ^ 2 * D.ε * e / D.dη +
      ∑ χ ∈ S.S1, χ S.J ^ 2 * z (S := S) χ / deg χ) := by
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have h := S.formula8 hr hr1
  rw [D.sum_split] at h
  have hε : (D.ε : ℂ) * D.ε = 1 := by exact_mod_cast D.ε_sq
  have hη : ∑ i, D.η i S.J ^ 2 * starRingEnd ℂ (D.η i (S.κ r)) / D.η i 1 =
      ((q : ℂ) - e) ^ 2 * D.ε * e / D.dη := by
    have hpt : ∀ i : S.W.RFam, D.η i S.J ^ 2 * starRingEnd ℂ (D.η i (S.κ r)) / D.η i 1 =
        ((q : ℂ) - e) ^ 2 * D.ε / D.dη * i.1 r := by
      intro i
      rw [D.η_J, D.τ_η_eq i hr hr1, D.η_one, map_mul, map_intCast, S.W.conj_apply_R i.2,
        mul_pow]
      linear_combination (((q : ℂ) - e) ^ 2 * D.ε * i.1 r / D.dη) * hε
    rw [Finset.sum_congr rfl fun i _ => hpt i, ← Finset.mul_sum,
      Finset.sum_coe_sort S.W.RFam (fun θ => θ r), S.W.sum_R_Ro hr hr1]
    ring
  have hη' : ∑ i, D.η' i S.J ^ 2 * starRingEnd ℂ (D.η' i (S.κ r)) / D.η' i 1 =
      ((q : ℂ) - e) ^ 2 * D.ε * e / D.dη := by
    have hpt : ∀ i : S.W.RFam, D.η' i S.J ^ 2 * starRingEnd ℂ (D.η' i (S.κ r)) / D.η' i 1 =
        ((q : ℂ) - e) ^ 2 * D.ε / D.dη * i.1 r := by
      intro i
      rw [D.η'_J, D.τ_η'_eq i hr hr1, D.η'_one, map_mul, map_intCast, S.W.conj_apply_R i.2,
        mul_pow, neg_sq]
      linear_combination (((q : ℂ) - e) ^ 2 * D.ε * i.1 r / D.dη) * hε
    rw [Finset.sum_congr rfl fun i _ => hpt i, ← Finset.mul_sum,
      Finset.sum_coe_sort S.W.RFam (fun θ => θ r), S.W.sum_R_Ro hr hr1]
    ring
  have hN : ∑ χ ∈ D.NE, χ S.J ^ 2 * starRingEnd ℂ (χ (S.κ r)) / χ 1 =
      ∑ χ ∈ S.S1, χ S.J ^ 2 * z (S := S) χ / deg χ := by
    rw [Finset.sum_congr rfl fun χ hχ => by
      rw [D.τ_NE hχ hr hr1, map_intCast, ← deg_eq (D.mem_NE.mp hχ).1]]
    have hpt : ∀ χ : G → ℂ, χ S.J ^ 2 * (z (S := S) χ : ℂ) / deg χ =
        χ S.J ^ 2 / deg χ * z (S := S) χ := fun χ => by ring
    rw [Finset.sum_congr rfl fun χ _ => hpt χ, Finset.sum_congr rfl fun χ _ => hpt χ]
    exact D.sum_NE_z (fun χ => χ S.J ^ 2 / deg χ)
  rw [hη, hη', hN] at h
  have hclass := card_conjClass_mul_card_centralizer S.J
  have hC0 : (Nat.card (Subgroup.centralizer ({S.J} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hG0 : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hK : (Nat.card (ConjClasses.mk S.J).carrier : ℂ) =
      Nat.card G / Nat.card (Subgroup.centralizer ({S.J} : Set G)) := by
    rw [eq_div_iff hC0]
    exact_mod_cast hclass
  rw [hK] at h
  rw [h]
  field_simp
  ring

end EtaData

end WardSetup

end CFSG.Walter.Ward
