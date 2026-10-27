module

public import CFSG.Walter.ReeOrder.Ward.Rows

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

theorem exists_deg {G : Type} [Group G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  refine ⟨Module.finrank ℂ V, ?_, Representation.char_one ρ⟩
  have h := blocksIrr_identity_re_pos ⟨ρ.character, ⟨V, inferInstance, inferInstance,
    inferInstance, ρ, hirr, rfl⟩⟩
  simp only [Representation.char_one, Complex.natCast_re] at h
  exact_mod_cast h

theorem conj_one {G : Type} [Group G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    starRingEnd ℂ (χ 1) = χ 1 := by
  obtain ⟨n, -, hn⟩ := exists_deg hχ
  rw [hn, Complex.conj_natCast]

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} {S : WardSetup G L q e IV}

namespace EtaData

variable (D : S.EtaData)

theorem dR_eq_zero_of_ne {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (k : S.W.RFam)
    (h1 : χ ≠ D.η k) (h2 : χ ≠ D.η' k) : S.dR χ k.1 = 0 := by
  by_cases hη : ∃ i, χ = D.η i
  · obtain ⟨i, rfl⟩ := hη
    rw [D.dR_η i k, ite_eq_right (fun h => h1 (by rw [h]))]
  · by_cases hη' : ∃ i, χ = D.η' i
    · obtain ⟨i, rfl⟩ := hη'
      rw [D.dR_η' i k, ite_eq_right (fun h => h2 (by rw [h]))]
    · push Not at hη hη'
      exact D.dR_other hχ hη hη' k

theorem ε_eq_ε' : D.ε = D.ε' ∧ ∀ k, D.η k 1 = D.η' k 1 := by
  have hk : ∀ k : S.W.RFam, (D.ε : ℂ) * D.η k 1 - D.ε' * D.η' k 1 = 0 := by
    intro k
    have h := S.orth (fun χ => S.dR χ k.1) (fun χ hχ => S.inner_ΦR hχ k.2)
      (x := 1) (by rw [orderOf_one]; exact odd_one)
    have hm1 : D.η k ∈ (irreducibles_finite G).toFinset := by
      rw [Set.Finite.mem_toFinset]; exact D.mem k
    have hm2 : D.η' k ∈ (irreducibles_finite G).toFinset := by
      rw [Set.Finite.mem_toFinset]; exact D.mem' k
    have hzero : ∀ χ ∈ (irreducibles_finite G).toFinset, χ ≠ D.η k ∧ χ ≠ D.η' k →
        (S.dR χ k.1 : ℂ) * starRingEnd ℂ (χ 1) = 0 := by
      intro χ hχ hne
      rw [Set.Finite.mem_toFinset] at hχ
      rw [D.dR_eq_zero_of_ne hχ k hne.1 hne.2]
      simp
    rw [Finset.sum_eq_add_of_mem (D.η k) (D.η' k) hm1 hm2 (D.disj k k) hzero] at h
    rw [D.dR_η k k, D.dR_η' k k, ite_eq_left rfl, ite_eq_left rfl, conj_one (D.mem k),
      conj_one (D.mem' k)] at h
    push_cast at h
    linear_combination h
  obtain ⟨k⟩ : Nonempty S.W.RFam := by
    have := card_ge (S := S)
    exact Fintype.card_pos_iff.mp (by omega)
  have hpos : ∀ χ ∈ BlocksIrr G, 0 < (χ 1).re := fun χ hχ => blocksIrr_identity_re_pos ⟨χ, hχ⟩
  have hεε : D.ε = D.ε' := by
    have h := congrArg Complex.re (hk k)
    simp only [Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.zero_re] at h
    have h1 := hpos _ (D.mem k)
    have h2 := hpos _ (D.mem' k)
    rcases D.ε_eq with he | he <;> rcases D.ε'_eq with he' | he' <;> rw [he, he'] at h ⊢ <;>
      push_cast at h <;> first | rfl | (exfalso; linarith)
  refine ⟨hεε, fun k => ?_⟩
  have h := hk k
  rw [← hεε] at h
  have hε0 : (D.ε : ℂ) ≠ 0 := by rcases D.ε_eq with he | he <;> rw [he] <;> norm_num
  have : (D.ε : ℂ) * (D.η k 1 - D.η' k 1) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hε0)

theorem const_entry_zero (d : (G → ℂ) → ℤ) (c : ℤ)
    (hnorm : ∑ χ ∈ (irreducibles_finite G).toFinset, d χ * d χ ≤ 4)
    (η : S.W.RFam → G → ℂ) (hinj : Function.Injective η) (hmem : ∀ i, η i ∈ BlocksIrr G)
    (hconst : ∀ i, d (η i) = c) : c = 0 := by
  have hle := sum_family_le η hinj hmem (fun χ => d χ * d χ) (fun χ => mul_self_nonneg _)
  simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
  have h6 := card_ge (S := S)
  exact eq_zero_of_mul_sq_le (hle.trans hnorm) (by omega) (by omega)

theorem nonR_one : (1 : L → ℂ) ∉ S.W.RFam := S.W.one_not_R
theorem nonR_θ2 : S.W.θ2 ∉ S.W.RFam := S.W.θ2_not_R
theorem nonR_θ3 : S.W.θ3 ∉ S.W.RFam := S.W.θ3_not_R
theorem nonR_θ4 : S.W.θ4 ∉ S.W.RFam := S.W.θ4_not_R

theorem η_d (i : S.W.RFam) :
    S.d1 (D.η i) = 0 ∧ S.d2 (D.η i) = 0 ∧ S.d3 (D.η i) = 0 ∧
      ∀ θ ∈ S.W.SFam, S.dS (D.η i) θ = 0 := by
  obtain ⟨g11, -, -, g22, -, g33⟩ := S.gram_principal
  have hM : ∀ θ ∈ BlocksIrr L, θ ∉ S.W.RFam → ∀ j, S.M (D.η j) θ = S.M (D.η i) θ :=
    fun θ hθ hR j => D.M_η_const j i hθ hR
  refine ⟨?_, ?_, ?_, fun θ hθ => ?_⟩
  · exact const_entry_zero S.d1 _ g11.le D.η D.inj D.mem (fun j => by
      simp only [d1, hM 1 S.W.one_mem S.W.one_not_R j, hM _ S.W.θ4_mem S.W.θ4_not_R j])
  · exact const_entry_zero S.d2 _ g22.le D.η D.inj D.mem (fun j => by
      simp only [d2, hM _ S.W.θ2_mem S.W.θ2_not_R j, hM _ S.W.θ4_mem S.W.θ4_not_R j])
  · exact const_entry_zero S.d3 _ g33.le D.η D.inj D.mem (fun j => by
      simp only [d3, hM _ S.W.θ3_mem S.W.θ3_not_R j, hM _ S.W.θ4_mem S.W.θ4_not_R j])
  · have hnorm := S.gram_S hθ hθ
    rw [ite_eq_left (Or.inl rfl)] at hnorm
    exact const_entry_zero (S.dS · θ) _ hnorm.le D.η D.inj D.mem (fun j => by
      simp only [dS, hM θ (S.W.S_mem hθ) (S.W.S_not_R hθ) j,
        hM _ (S.W.S_mem (S.W.sbar_mem θ hθ)) (S.W.S_not_R (S.W.sbar_mem θ hθ)) j])

theorem η'_d (i : S.W.RFam) :
    S.d1 (D.η' i) = 0 ∧ S.d2 (D.η' i) = 0 ∧ S.d3 (D.η' i) = 0 ∧
      ∀ θ ∈ S.W.SFam, S.dS (D.η' i) θ = 0 := by
  obtain ⟨g11, -, -, g22, -, g33⟩ := S.gram_principal
  have hM : ∀ θ ∈ BlocksIrr L, θ ∉ S.W.RFam → ∀ j, S.M (D.η' j) θ = S.M (D.η' i) θ :=
    fun θ hθ hR j => D.M_η'_const j i hθ hR
  refine ⟨?_, ?_, ?_, fun θ hθ => ?_⟩
  · exact const_entry_zero S.d1 _ g11.le D.η' D.inj' D.mem' (fun j => by
      simp only [d1, hM 1 S.W.one_mem S.W.one_not_R j, hM _ S.W.θ4_mem S.W.θ4_not_R j])
  · exact const_entry_zero S.d2 _ g22.le D.η' D.inj' D.mem' (fun j => by
      simp only [d2, hM _ S.W.θ2_mem S.W.θ2_not_R j, hM _ S.W.θ4_mem S.W.θ4_not_R j])
  · exact const_entry_zero S.d3 _ g33.le D.η' D.inj' D.mem' (fun j => by
      simp only [d3, hM _ S.W.θ3_mem S.W.θ3_not_R j, hM _ S.W.θ4_mem S.W.θ4_not_R j])
  · have hnorm := S.gram_S hθ hθ
    rw [ite_eq_left (Or.inl rfl)] at hnorm
    exact const_entry_zero (S.dS · θ) _ hnorm.le D.η' D.inj' D.mem' (fun j => by
      simp only [dS, hM θ (S.W.S_mem hθ) (S.W.S_not_R hθ) j,
        hM _ (S.W.S_mem (S.W.sbar_mem θ hθ)) (S.W.S_not_R (S.W.sbar_mem θ hθ)) j])

theorem σ_η (i : S.W.RFam) {y : L} (hy : Odd (orderOf y)) :
    S.σ (D.η i) y = D.ε * i.1 y := by
  obtain ⟨h1, h2, h3, hS⟩ := D.η_d i
  have hSz : ∑ θ ∈ S.W.SFam, (S.dS (D.η i) θ : ℂ) * θ y = 0 :=
    Finset.sum_eq_zero (fun θ hθ => by rw [hS θ hθ]; simp)
  rw [S.σ_decomp (D.mem i) hy, h1, h2, h3, hSz]
  have hR : ∑ θ ∈ S.W.RFam, (S.dR (D.η i) θ : ℂ) * θ y = D.ε * i.1 y := by
    rw [← Finset.sum_attach, Finset.sum_eq_single i]
    · rw [D.dR_η i i, ite_eq_left rfl]
    · intro k _ hk
      rw [D.dR_η i k, ite_eq_right (Ne.symm hk)]
      simp
    · intro h
      exact absurd (Finset.mem_attach _ i) h
  rw [hR]
  simp

theorem σ_η' (i : S.W.RFam) {y : L} (hy : Odd (orderOf y)) :
    S.σ (D.η' i) y = -D.ε * i.1 y := by
  obtain ⟨h1, h2, h3, hS⟩ := D.η'_d i
  have hSz : ∑ θ ∈ S.W.SFam, (S.dS (D.η' i) θ : ℂ) * θ y = 0 :=
    Finset.sum_eq_zero (fun θ hθ => by rw [hS θ hθ]; simp)
  rw [S.σ_decomp (D.mem' i) hy, h1, h2, h3, hSz]
  have hR : ∑ θ ∈ S.W.RFam, (S.dR (D.η' i) θ : ℂ) * θ y = -D.ε * i.1 y := by
    rw [← Finset.sum_attach, Finset.sum_eq_single i]
    · rw [D.dR_η' i i, ite_eq_left rfl, D.ε_eq_ε'.1]
      push_cast
      ring
    · intro k _ hk
      rw [D.dR_η' i k, ite_eq_right (Ne.symm hk)]
      simp
    · intro h
      exact absurd (Finset.mem_attach _ i) h
  rw [hR]
  simp

end EtaData

variable (S)

theorem card_centralizer_κR (S : WardSetup G L q e) {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    Nat.card (Subgroup.centralizer ({S.κ r} : Set G)) =
      2 * Nat.card (Subgroup.centralizer ({r} : Set L)) := by
  have hmap : Subgroup.centralizer ({S.κ r} : Set G) =
      ((⊤ : Subgroup (Subgroup.zpowers S.J)).prod (Subgroup.centralizer ({r} : Set L))).map
        S.ι := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro hx
      have hJ : x * S.J = S.J * x := by
        apply S.normalizer rfl r hr hr1 x
        rw [show x⁻¹ * S.κ r * x = S.κ r by
          rw [mul_assoc, ← hx, ← mul_assoc, inv_mul_cancel, one_mul]]
        exact Subgroup.mem_zpowers _
      obtain ⟨w, rfl | rfl⟩ := S.centralizer x hJ
      · refine ⟨(1, w), ⟨Subgroup.mem_top _, ?_⟩, by simp [ι_apply]⟩
        show w ∈ Subgroup.centralizer ({r} : Set L)
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply S.κ_inj
        rw [map_mul, map_mul]
        exact hx
      · refine ⟨(S.Jz, w), ⟨Subgroup.mem_top _, ?_⟩, by simp [ι_apply, Jz]⟩
        show w ∈ Subgroup.centralizer ({r} : Set L)
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply S.κ_inj
        rw [map_mul, map_mul]
        have h1 : S.J * S.κ w * S.κ r = S.κ r * (S.J * S.κ w) := hx
        have h2 : S.J * (S.κ w * S.κ r) = S.J * (S.κ r * S.κ w) := by
          rw [← mul_assoc, h1, ← mul_assoc, ← S.κ_comm' r, mul_assoc]
        exact mul_left_cancel h2
    · rintro ⟨⟨u, w⟩, ⟨-, hw⟩, rfl⟩
      have hw' : w ∈ Subgroup.centralizer ({r} : Set L) := hw
      rw [Subgroup.mem_centralizer_singleton_iff] at hw'
      have hκw : S.κ w * S.κ r = S.κ r * S.κ w := by rw [← map_mul, hw', map_mul]
      rw [ι_apply]
      have hu' := S.commute_zpowers u r
      calc (u : G) * S.κ w * S.κ r = (u : G) * (S.κ w * S.κ r) := by group
        _ = (u : G) * (S.κ r * S.κ w) := by rw [hκw]
        _ = ((u : G) * S.κ r) * S.κ w := by group
        _ = (S.κ r * (u : G)) * S.κ w := by rw [hu'.eq]
        _ = S.κ r * ((u : G) * S.κ w) := by group
  rw [hmap, Subgroup.card_map_of_injective S.ι_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top, S.card_Z]

theorem card_centralizer_κR' (S : WardSetup G L q e) {r : L} (hr : r ∈ S.W.Ro)
    (hr1 : r ≠ 1) :
    (Nat.card (Subgroup.centralizer ({S.κ r} : Set G)) : ℂ) = 2 * Nat.card S.W.Ro := by
  rw [S.card_centralizer_κR hr hr1, S.W.Ro_centralizer r hr hr1]
  push_cast
  ring

theorem τ_Ro {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    χ (S.κ r) = (S.Ar χ 1 : ℂ) - e * S.Ar χ S.W.θ4 +
      ∑ θ ∈ S.W.RFam, (S.Ar χ θ : ℂ) * θ r := by
  have h := S.τ_expand hχ r
  simp only [τ] at h
  rw [h, S.W.sum_irr]
  obtain ⟨h2, h3, h4, hS⟩ := S.W.val_Ro r hr hr1
  rw [h2, h3, h4, Finset.sum_eq_zero (s := S.W.SFam) (fun θ hθ => by rw [hS θ hθ, mul_zero])]
  simp only [Pi.one_apply, mul_one, mul_zero, add_zero]
  ring

end WardSetup

end CFSG.Walter.Ward
