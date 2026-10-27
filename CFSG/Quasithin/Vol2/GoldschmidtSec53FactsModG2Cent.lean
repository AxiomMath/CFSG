module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.Sec53F.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem centerQ0 {z : ModGL Tag.G2 K} (hzQ : z ∈ parabolicRadical Tag.G2 K {i0})
    (hzC : z ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i0} : Set (ModGL Tag.G2 K))) :
    ∃ t₄ t₅ : K, z = gX rB t₄ * gX rC t₅ := by
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_zero hzQ
  have hN := N0_le_centralizer (K := K)
  have hmem : ∀ {d : Fin Tag.G2.rank → ℤ},
      (d = rR ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ c : K,
        gX d c ∈ parabolicRadical Tag.G2 K {i0} := fun hd c => mem_zero hd c
  have hzg : ∀ g ∈ parabolicRadical Tag.G2 K {i0},
      ⁅gX rR t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))), g⁆ = 1 := by
    intro g hg
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have h1N : (1 : ModGL Tag.G2 K) ∈ N0 := N0.one_mem
  have hr : gX rR t₁ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inl rfl) t₁
  have hu : gX rU t₂ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inr (Or.inl rfl)) t₂
  have hv : gX rV t₃ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inr (Or.inr (Or.inl rfl))) t₃
  have hb : gX rB t₄ ∈ parabolicRadical Tag.G2 K {i0} :=
    hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) t₄
  have st1 := hzg (gX rV 1) (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
  have v1 : ⁅gX rR t₁, gX rV (1 : K)⁆ = gX rB (t₁ * 1) := rel_rv _ _
  have v2 : ⁅gX rU t₂, gX rV (1 : K)⁆ = gX rC (t₂ * 1) := rel_uv _ _
  have v3 : ⁅gX rV t₃, gX rV (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
  have v4 : ⁅gX rB t₄, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vb 1 t₄).symm
  have v5 : ⁅gX rC t₅, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vc 1 t₅).symm
  rw [comm_five hN hr hu hv hb (by rw [v2]; exact gX_c_mem_N0 _)
    (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
    v1, v2, v3, v4, v5] at st1
  simp only [one_mul, mul_one] at st1
  rw [← (comm_bc t₁ t₂).eq] at st1
  obtain ⟨rfl, rfl⟩ := prod_bc_eq_one st1
  have st2 := hzg (gX rR 1) (hmem (Or.inl rfl) 1)
  have w1 : ⁅gX rR (0 : K), gX rR (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
  have w2 : ⁅gX rU (0 : K), gX rR (1 : K)⁆ = 1 := by
    rw [gX_zero]
    exact commutatorElement_one_left _
  have w3 : ⁅gX rV t₃, gX rR (1 : K)⁆ = gX rB (1 * t₃) := by
    rw [← commutatorElement_inv, rel_rv, gX_inv]
  have w4 : ⁅gX rB t₄, gX rR (1 : K)⁆ = 1 := commutator_of_commute (comm_rb 1 t₄).symm
  have w5 : ⁅gX rC t₅, gX rR (1 : K)⁆ = 1 := commutator_of_commute (comm_rc 1 t₅).symm
  rw [comm_five hN hr hu hv hb (by rw [w2]; exact h1N)
    (by rw [w3]; exact gX_b_mem_N0 _) (by rw [w4]; exact h1N) (by rw [w5]; exact h1N),
    w1, w2, w3, w4, w5] at st2
  simp only [one_mul, mul_one] at st2
  have ht3 : t₃ = 0 := by simpa using gX_eq_one st2
  subst ht3
  exact ⟨t₄, t₅, by simp only [gX_zero, one_mul]⟩

theorem centerQ1 {z : ModGL Tag.G2 K} (hzQ : z ∈ parabolicRadical Tag.G2 K {i1})
    (hzC : z ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K))) :
    ∃ t : K, z = gX rC t := by
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_one hzQ
  have hN := N1_le_centralizer (K := K)
  have hmem : ∀ {d : Fin Tag.G2.rank → ℤ},
      (d = rA ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ c : K,
        gX d c ∈ parabolicRadical Tag.G2 K {i1} := fun hd c => mem_one hd c
  have hzg : ∀ g ∈ parabolicRadical Tag.G2 K {i1},
      ⁅gX rA t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))), g⁆ = 1 := by
    intro g hg
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have h1N : (1 : ModGL Tag.G2 K) ∈ N1 := N1.one_mem
  have ha : gX rA t₁ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inl rfl) t₁
  have hu : gX rU t₂ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inl rfl)) t₂
  have hv : gX rV t₃ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inr (Or.inl rfl))) t₃
  have hb : gX rB t₄ ∈ parabolicRadical Tag.G2 K {i1} :=
    hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) t₄
  have ht₁ : t₁ = 0 := by
    have st := hzg (gX rB 1) (hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 1)
    have v1 : ⁅gX rA t₁, gX rB (1 : K)⁆ = gX rC (t₁ * 1) := rel_ab _ _
    have v2 : ⁅gX rU t₂, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_ub _ _)
    have v3 : ⁅gX rV t₃, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_vb _ _)
    have v4 : ⁅gX rB t₄, gX rB (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v5 : ⁅gX rC t₅, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_bc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₂ : t₂ = 0 := by
    have st := hzg (gX rV 1) (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
    have v1 : ⁅gX rA t₁, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_av _ _)
    have v2 : ⁅gX rU t₂, gX rV (1 : K)⁆ = gX rC (t₂ * 1) := rel_uv _ _
    have v3 : ⁅gX rV t₃, gX rV (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v4 : ⁅gX rB t₄, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vb 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact gX_c_mem_N1 _)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₃ : t₃ = 0 := by
    have st := hzg (gX rU 1) (hmem (Or.inr (Or.inl rfl)) 1)
    have v1 : ⁅gX rA t₁, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_au _ _)
    have v2 : ⁅gX rU t₂, gX rU (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v3 : ⁅gX rV t₃, gX rU (1 : K)⁆ = gX rC (1 * t₃) := by
      rw [← commutatorElement_inv, rel_uv, gX_inv]
    have v4 : ⁅gX rB t₄, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_ub 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_uc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact gX_c_mem_N1 _) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₄ : t₄ = 0 := by
    have st := hzg (gX rA 1) (hmem (Or.inl rfl) 1)
    have v1 : ⁅gX rA t₁, gX rA (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v2 : ⁅gX rU t₂, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_au 1 t₂).symm
    have v3 : ⁅gX rV t₃, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_av 1 t₃).symm
    have v4 : ⁅gX rB t₄, gX rA (1 : K)⁆ = gX rC (1 * t₄) := by
      rw [← commutatorElement_inv, rel_ab, gX_inv]
    have v5 : ⁅gX rC t₅, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_ac 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact gX_c_mem_N1 _) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  subst ht₁ ht₂ ht₃ ht₄
  exact ⟨t₅, by simp only [gX_zero, one_mul]⟩

end CFSG.Quasithin.H13.Sec53F.G2
