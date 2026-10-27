module

public import CFSG.Quasithin.Vol2.Ch11SecHEnd2
public import CFSG.Quasithin.Vol2.Ch11SecHLin

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem sq_eq_one_of_flag {F : Type*} [Field F] [CharP F 2] (g : Matrix (Fin 3) (Fin 3) F)
    {u₀ u₁ x : Fin 3 → F} (hli : LinearIndependent F ![u₀, u₁, x]) {c₀ c₁ : F}
    (h0 : g.mulVec u₀ = u₀) (h1 : g.mulVec u₁ = u₁)
    (h3 : g.mulVec x = x + c₀ • u₀ + c₁ • u₁) : ∀ z, g.mulVec (g.mulVec z) = z := by
  have hgx : g.mulVec (g.mulVec x) = x := by
    rw [h3, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h0, h1,
      h3]
    have e0 : c₀ • u₀ + c₀ • u₀ = 0 := by
      rw [← two_smul F, CharTwo.two_eq_zero, zero_smul]
    have e1 : c₁ • u₁ + c₁ • u₁ = 0 := by
      rw [← two_smul F, CharTwo.two_eq_zero, zero_smul]
    calc x + c₀ • u₀ + c₁ • u₁ + c₀ • u₀ + c₁ • u₁ =
        x + (c₀ • u₀ + c₀ • u₀) + (c₁ • u₁ + c₁ • u₁) := by abel
      _ = x := by rw [e0, e1, add_zero, add_zero]
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp)
  intro z
  have hz : z ∈ Submodule.span F (Set.range ![u₀, u₁, x]) := htop ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hz
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.mulVec_add,
    Matrix.mulVec_smul, h0, h1, hgx]

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem false (i : Inp32) : False := by
  obtain ⟨hcV, F, _, _, hF, π, hπ⟩ := d.exists_sl3 i
  have hcP : IsMulCommutative ↥(pOf T I H h) := (d.isElemAbelian_P i).1
  have hchar : CharP F 2 := charP_two_of_card hF
  obtain ⟨φ, hφadd, hφbij, hφeq⟩ := exists_coords hπ
  have hyL : conjAct (fsuV T I) ⟨y, d.y_mem_normalizer_V⟩ ∈ autOn L (fsuV T I) :=
    ⟨⟨y, d.y_mem_normalizer_V⟩, Subgroup.mem_subgroupOf.mpr d.yL, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 3 F), π γ = ⟨_, hyL⟩ := hπ.1 ⟨_, hyL⟩
  have hγy : ∀ w : ↥(fsuV T I), φ (conjAct (fsuV T I) ⟨y, d.y_mem_normalizer_V⟩ w) =
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ w) := by
    intro w
    rw [← hφeq γ w, hγ]
  have hγyU : IsUnit ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := Units.isUnit _
  have hdet : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    det_eq_one_of_mem_statedSL γ.2
  obtain ⟨v, hv, hvB⟩ := Set.not_subset.mp d.not_fsuV_le_B
  obtain ⟨W₀, W₁, hW01, hW₀, hW₁⟩ := d.exists_two_natural i hF hπ
  obtain ⟨u₀, hu₀, hz₀, α₀, hα₀, hrel₀⟩ :=
    d.summand_line i hF hπ hφadd hφbij hφeq _ hγy hγyU ⟨v, hv⟩ hvB hW₀
  obtain ⟨u₁, hu₁, hz₁, α₁, hα₁, hrel₁⟩ :=
    d.summand_line i hF hπ hφadd hφbij hφeq _ hγy hγyU ⟨v, hv⟩ hvB hW₁
  have hli : LinearIndependent F ![u₀, u₁, φ ⟨v, hv⟩] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have h2 : c 2 = 0 := by
      by_contra h2
      apply hvB
      obtain ⟨z₀, hz₀B, -, -, hz₀φ⟩ := hz₀ (-(c 2)⁻¹ * c 0)
      obtain ⟨z₁, hz₁B, -, -, hz₁φ⟩ := hz₁ (-(c 2)⁻¹ * c 1)
      have hx2 : c 2 • φ ⟨v, hv⟩ = -(c 0 • u₀ + c 1 • u₁) :=
        eq_neg_of_add_eq_zero_right hc
      have hxe : φ ⟨v, hv⟩ = (-(c 2)⁻¹ * c 0) • u₀ + (-(c 2)⁻¹ * c 1) • u₁ := by
        calc φ ⟨v, hv⟩ = (c 2)⁻¹ • (c 2 • φ ⟨v, hv⟩) := by
              rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
          _ = (c 2)⁻¹ • (-(c 0 • u₀ + c 1 • u₁)) := by rw [hx2]
          _ = (-(c 2)⁻¹ * c 0) • u₀ + (-(c 2)⁻¹ * c 1) • u₁ := by module
      have hveq : (⟨v, hv⟩ : ↥(fsuV T I)) = z₀ * z₁ :=
        hφbij.1 (by rw [hφadd, hz₀φ, hz₁φ, ← hxe])
      have hvz : v = (z₀ : G) * (z₁ : G) := by
        have := congrArg Subtype.val hveq
        simpa using this
      rw [hvz]
      exact Subgroup.mul_mem _ hz₀B hz₁B
    rw [h2, zero_smul, add_zero] at hc
    obtain ⟨z₀, -, hz₀P, hz₀W, hz₀φ⟩ := hz₀ (c 0)
    obtain ⟨z₁, -, hz₁P, hz₁W, hz₁φ⟩ := hz₁ (-(c 1))
    have hz : z₀ = z₁ := hφbij.1 (by rw [hz₀φ, hz₁φ, neg_smul, eq_neg_iff_add_eq_zero, hc])
    subst hz
    have hmem : (⟨z₀, hz₀P⟩ : ↥(pOf T I H h)) ∈ W₀ ⊓ W₁ := ⟨hz₀W, hz₁W⟩
    rw [hW01, Subgroup.mem_bot] at hmem
    have hz1 : z₀ = 1 := Subtype.ext (by simpa using congrArg Subtype.val hmem)
    have hc0 : c 0 = 0 := by
      have : φ z₀ = 0 := by rw [hz1]; exact coords_one hφadd
      rw [hz₀φ] at this
      exact (smul_eq_zero.mp this).resolve_right hu₀
    have hc1 : c 1 = 0 := by
      rw [hc0, zero_smul, zero_add] at hc
      exact (smul_eq_zero.mp hc).resolve_right hu₁
    intro j
    fin_cases j <;> simp [hc0, hc1, h2]
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmemx : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ ⟨v, hv⟩) ∈
      Submodule.span F (Set.range ![u₀, u₁, φ ⟨v, hv⟩]) := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmemx
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  obtain ⟨z₀, hz₀B, -, -, hz₀φ⟩ := hz₀ (c 0)
  obtain ⟨z₁, hz₁B, -, -, hz₁φ⟩ := hz₁ (c 1)
  have hrelx : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ ⟨v, hv⟩) =
      c 2 • φ ⟨v, hv⟩ + φ (z₀ * z₁) := by
    rw [hφadd, hz₀φ, hz₁φ, ← hc]
    abel
  have hβB : ((z₀ * z₁ : ↥(fsuV T I)) : G) ∈ bOf T I H := by
    rw [Subgroup.coe_mul]
    exact Subgroup.mul_mem _ hz₀B hz₁B
  have hsq0 := hrel₀ (c 2) (z₀ * z₁) hβB hrelx
  have hsq1 := hrel₁ (c 2) (z₀ * z₁) hβB hrelx
  have h3 : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ ⟨v, hv⟩) =
      c 2 • φ ⟨v, hv⟩ + c 0 • u₀ + c 1 • u₁ := by
    rw [← hc]
    abel
  have hα0 : α₀ = 1 := eq_one_of_flag _ hdet hli hα₀ hα₁ h3 hsq0 hsq1
  have h01 : α₀ = α₁ := CharTwo.sq_inj.mp (hsq0.trans hsq1.symm)
  have hc2 : c 2 = 1 := by rw [← hsq0, hα0, one_pow]
  have hsqg := sq_eq_one_of_flag _ hli (by rw [hα₀, hα0, one_smul])
    (by rw [hα₁, ← h01, hα0, one_smul]) (by rw [h3, hc2, one_smul])
  have hy2 : y ^ 2 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := hsqg (φ ⟨w, hw⟩)
    rw [← hγy, ← hγy] at h1
    have h2 := congrArg Subtype.val (hφbij.1 h1)
    rw [conjAct_apply_coe, conjAct_apply_coe] at h2
    calc w * y ^ 2 = (y * (y * w * y⁻¹) * y⁻¹) * y ^ 2 := by rw [h2]
      _ = y ^ 2 * w := by rw [pow_two]; group
  have hyC : y ∈ Subgroup.centralizer (fsuV T I : Set G) :=
    mem_of_pow_two_pow_mem (e := 1) (by simpa using hy2) d.yodd
  apply d.not_le_centralizer
  intro w hw
  apply d.fpf i hw
  have hwy : w * y = y * w := Subgroup.mem_centralizer_iff.mp hyC w hw
  have : y * w * y⁻¹ * w⁻¹ = 1 := by rw [← hwy]; group
  rw [this]
  exact Subgroup.one_mem _

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
