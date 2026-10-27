module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallFix
public import CFSG.LocalAnalysis.RankThreeTheoremC.FPFSAbstract
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.LocalAnalysis.RankThreeTheoremC.FPFS Subgroup

theorem mem_of_small_commutator_13 {Hh : Type} [Group Hh] [Finite Hh] (R : Subgroup Hh)
    [R.Normal] (hR : IsPGroup 2 R) (hRc : centralizer (R : Set Hh) ≤ R)
    (hO2 : ∀ W : Subgroup Hh, W.Normal → IsPGroup 2 W → W ≤ R)
    (a b : Hh) (Ea Eb : Subgroup Hh) (hEa : Ea ≤ R) (hEb : Eb ≤ R)
    (hEa5 : Nat.card Ea ≤ 2 ^ 5) (hEb5 : Nat.card Eb ≤ 2 ^ 5)
    (ha : ∀ r ∈ R, r⁻¹ * (a * r * a⁻¹) ∈ Ea) (hb : ∀ r ∈ R, r⁻¹ * (b * r * b⁻¹) ∈ Eb)
    (y : Hh) (hy : y ∈ Subgroup.closure {a, b}) (hy13 : IsPGroup 13 (Subgroup.zpowers y)) :
    y ∈ R := by
  classical
  obtain ⟨hcomm, hexp⟩ := frattini_quot_comm R hR
  let ρ := frattiniAction R
  let π : ↥R →* ↥R ⧸ frattini ↥R := QuotientGroup.mk' (frattini ↥R)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hρπ : ∀ (g : Hh) (r : ↥R), ρ g (π r) = π (MulAut.conjNormal g r) :=
    fun g r => frattiniAction_apply R g r
  let A₀ : Subgroup (↥R ⧸ frattini ↥R) := (Ea.subgroupOf R).map π
  let B₀ : Subgroup (↥R ⧸ frattini ↥R) := (Eb.subgroupOf R).map π
  have hcard : ∀ E : Subgroup Hh, E ≤ R → Nat.card ((E.subgroupOf R).map π) ≤ Nat.card E := by
    intro E hE
    have h1 : Nat.card ((E.subgroupOf R).map π) ≤ Nat.card (E.subgroupOf R) :=
      Nat.card_le_card_of_surjective (π.subgroupMap (E.subgroupOf R))
        (MonoidHom.subgroupMap_surjective _ _)
    have h2 : Nat.card (E.subgroupOf R) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
    omega
  have hA₀ : Nat.card A₀ ≤ 2 ^ 5 := (hcard Ea hEa).trans hEa5
  have hB₀ : Nat.card B₀ ≤ 2 ^ 5 := (hcard Eb hEb).trans hEb5
  let B : Subgroup (↥R ⧸ frattini ↥R) := A₀ ⊔ B₀
  have hB : Nat.card B ≤ 2 ^ 10 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₀ B₀
      (fun x _ y _ => hcomm x y)).1
    have hpos : 0 < Nat.card (A₀ ⊓ B₀ : Subgroup (↥R ⧸ frattini ↥R)) := Nat.card_pos
    calc Nat.card B ≤ Nat.card B * Nat.card (A₀ ⊓ B₀ : Subgroup (↥R ⧸ frattini ↥R)) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card A₀ * Nat.card B₀ := h
      _ ≤ 2 ^ 5 * 2 ^ 5 := Nat.mul_le_mul hA₀ hB₀
      _ = 2 ^ 10 := by norm_num
  let Γ : Subgroup Hh :=
    { carrier := {g | ∀ w : ↥R ⧸ frattini ↥R, ρ g w * w⁻¹ ∈ B}
      mul_mem' := by
        intro g h hg hh w
        have h1 := B.mul_mem (hg (ρ h w)) (hh w)
        simpa [mul_assoc] using h1
      one_mem' := by
        intro w
        simp
      inv_mem' := by
        intro g hg w
        have h1 := B.inv_mem (hg (ρ g⁻¹ w))
        have h2 : ρ g (ρ g⁻¹ w) = w := by
          rw [← MulAut.mul_apply, ← map_mul]
          simp
        rw [h2] at h1
        simpa using h1 }
  have haΓ : a ∈ Γ := by
    intro w
    obtain ⟨r, rfl⟩ := hπ w
    refine Subgroup.mem_sup_left ⟨r⁻¹ * MulAut.conjNormal a r, ?_, ?_⟩
    · show r⁻¹ * MulAut.conjNormal a r ∈ Ea.subgroupOf R
      rw [Subgroup.mem_subgroupOf]
      simpa [MulAut.conjNormal_apply] using ha r r.2
    · rw [map_mul, map_inv, ← hρπ, hcomm]
  have hbΓ : b ∈ Γ := by
    intro w
    obtain ⟨r, rfl⟩ := hπ w
    refine Subgroup.mem_sup_right ⟨r⁻¹ * MulAut.conjNormal b r, ?_, ?_⟩
    · show r⁻¹ * MulAut.conjNormal b r ∈ Eb.subgroupOf R
      rw [Subgroup.mem_subgroupOf]
      simpa [MulAut.conjNormal_apply] using hb r r.2
    · rw [map_mul, map_inv, ← hρπ, hcomm]
  have hyΓ : y ∈ Γ :=
    (Subgroup.closure_le Γ).mpr (by
      intro x hx
      rcases hx with rfl | rfl
      · exact haΓ
      · exact hbΓ) hy
  have hφ13 : IsPGroup 13 (Subgroup.zpowers (ρ y)) := by
    rw [← MonoidHom.map_zpowers]
    exact hy13.map ρ
  have hone : ρ y = 1 :=
    mulAut_eq_one_of_commutator_small hcomm (fun x => by rw [sq]; exact hexp x) (ρ y) hφ13 B hB
      (fun β hβ => by
        have h1 := B.mul_mem (hyΓ β) hβ
        simpa using h1)
      hyΓ
  have hker := frattiniAction_ker R hR hRc hO2
  rw [← hker]
  exact MonoidHom.mem_ker.mpr hone

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
