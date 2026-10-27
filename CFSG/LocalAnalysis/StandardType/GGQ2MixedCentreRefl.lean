module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2mcr_reflTransGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α → β) (h : ∀ a b, r a b → s (f a) (f b)) :
    ∀ a b, Relation.ReflTransGen r a b → Relation.ReflTransGen s (f a) (f b) := by
  intro a b hab
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h _ _ hbc)

private theorem ggQ2mcr_intCast_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {z : ℤ}
    (hz : z = -1 ∨ z = -2) : (z : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h0
  have hdvd : (p : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h0
  have hnat : p ∣ z.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  rcases hz with rfl | rfl
  · exact hp.not_dvd_one (by simpa using hnat)
  · have h2 : p ∣ 2 := by simpa using hnat
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

private theorem ggQ2mcr_A_ne_six (n : ℕ) (u v : Fin n) : CoxeterMatrix.A n u v ≠ 6 := by
  intro h
  simp only [CoxeterMatrix.A, Matrix.of_apply] at h
  split_ifs at h <;> omega

private theorem ggQ2mcr_B_ne_six (n : ℕ) (u v : Fin n) : CoxeterMatrix.B n u v ≠ 6 := by
  intro h
  simp only [CoxeterMatrix.B, Matrix.of_apply] at h
  split_ifs at h <;> omega

private theorem ggQ2mcr_D_ne_six (n : ℕ) (u v : Fin n) : ggCoxeterMatrixD n u v ≠ 6 := by
  intro h
  rw [ggCoxeterMatrixD_apply] at h
  split_ifs at h <;> omega

private theorem ggQ2mcr_E6_ne_six (u v : Fin 6) : CoxeterMatrix.E₆ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem ggQ2mcr_E7_ne_six (u v : Fin 7) : CoxeterMatrix.E₇ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem ggQ2mcr_E8_ne_six (u v : Fin 8) : CoxeterMatrix.E₈ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem ggQ2mcr_F4_ne_six (u v : Fin 4) : CoxeterMatrix.F₄ u v ≠ 6 := by
  fin_cases u <;> fin_cases v <;> decide

private theorem ggQ2mcr_weylMatrix_ne_six {Γ : Type} [Fintype Γ] {M : CoxeterMatrix Γ}
    (hM : GGIsWeylMatrix M) (hrk : 3 ≤ Fintype.card Γ) (i j : Γ) : M.M i j ≠ 6 := by
  rcases hM with ⟨n, e, hn, h | ⟨hn2, h⟩ | ⟨hn4, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ |
    ⟨e, h⟩
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact ggQ2mcr_A_ne_six n _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact ggQ2mcr_B_ne_six n _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact ggQ2mcr_D_ne_six n _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact ggQ2mcr_E6_ne_six _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact ggQ2mcr_E7_ne_six _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact ggQ2mcr_E8_ne_six _ _
  · subst h
    rw [CoxeterMatrix.reindex_apply]
    exact ggQ2mcr_F4_ne_six _ _
  · exfalso
    have hc : Fintype.card Γ = 2 := (Fintype.card_congr e).symm.trans (Fintype.card_fin 2)
    omega

private theorem ggQ2mcr_intCartan_ne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Γ : Type} [Fintype Γ] {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hM : GGIsWeylMatrix M) (hrk : 3 ≤ Fintype.card Γ) (hC : GGIntCartan M C)
    {i j : Γ} (hij : i ≠ j) (hlab : M.M i j ≠ 2) :
    (C i j : ZMod p) ≠ 0 ∧ (C j i : ZMod p) ≠ 0 := by
  rcases hC.entries hij with ⟨hm2, -, -⟩ | ⟨hm3, h1, h2⟩ | ⟨hm4, h1 | h1⟩ | ⟨hm6, h1 | h1⟩
  · exact absurd hm2 hlab
  · exact ⟨by rw [h1]; exact ggQ2mcr_intCast_ne_zero hp2 (Or.inl rfl),
      by rw [h2]; exact ggQ2mcr_intCast_ne_zero hp2 (Or.inl rfl)⟩
  · exact ⟨by rw [h1.1]; exact ggQ2mcr_intCast_ne_zero hp2 (Or.inl rfl),
      by rw [h1.2]; exact ggQ2mcr_intCast_ne_zero hp2 (Or.inr rfl)⟩
  · exact ⟨by rw [h1.1]; exact ggQ2mcr_intCast_ne_zero hp2 (Or.inr rfl),
      by rw [h1.2]; exact ggQ2mcr_intCast_ne_zero hp2 (Or.inl rfl)⟩
  · exact absurd hm6 (ggQ2mcr_weylMatrix_ne_six hM hrk i j)
  · exact absurd hm6 (ggQ2mcr_weylMatrix_ne_six hM hrk i j)

theorem GGQ2LDatum.root_coroot_two {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : M.root i (M.coroot i) = 2 := by
  rw [M.pairing i i, M.isCartan.1 i]
  norm_num

theorem GGQ2LDatum.root_xV {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : M.root i M.xV = 0 := by
  have hx : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.mem_span_singleton_self _
  have h1 : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hfix := mem_ggFixedSubmodule_iff.mp hx (M.simple i) h1
  rw [M.simple_apply i, sub_eq_self] at hfix
  have hc : M.coroot i ≠ 0 := by
    intro h
    have h2 := GGQ2LDatum.root_coroot_two M i
    rw [h, map_zero] at h2
    exact absurd h2 (by decide : (0 : ZMod 3) ≠ 2)
  exact (smul_eq_zero.mp hfix).resolve_right hc

theorem GGQ2LDatum.mem_span_xV_of_root {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {z : M.V} (hz : ∀ i, M.root i z = 0) :
    z ∈ Submodule.span (ZMod 3) {M.xV} := by
  have hzF : z ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [M.automizer_L] at hφ
    refine Subgroup.closure_induction (p := fun φ _ =>
      ggLin (p := 3) M.model φ z = z) ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨i, rfl⟩
      rw [M.simple_apply i, hz i, zero_smul, sub_zero]
    · simp
    · intro a b _ _ ha hb
      rw [map_mul, LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha
      rw [map_inv]
      have h0 := LinearEquiv.symm_apply_apply (ggLin (p := 3) M.model a) z
      rwa [ha] at h0
  rw [M.fixed_x] at hzF
  simpa only [GGQ2LDatum.xV] using hzF

theorem GGQ2LDatum.simple_mem_top {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : M.simple i ∈ ggAutomizer ⊤ Bs := by
  have h1 : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  exact ggAutomizer_mono Bs le_top h1

theorem GGQ2LDatum.simple_mem_reflGp {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : M.simple i ∈ ggReflGp 3 Bs := by
  refine Subgroup.subset_closure ⟨GGQ2LDatum.simple_mem_top M i, ?_⟩
  have hfx : M.root i (M.coroot i) = 2 := GGQ2LDatum.root_coroot_two M i
  exact ggIsReflection_of_eq_reflection (p := 3) (by decide) M.model hfx
    (ggLin_eq_reflection (p := 3) M.model hfx (M.simple_apply i))

theorem GGQ2LDatum.pairing_connected {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hcard : 3 ≤ Fintype.card M.Λ) (i j : M.Λ) :
    Relation.ReflTransGen (fun a b => M.root a (M.coroot b) ≠ 0 ∧ M.root b (M.coroot a) ≠ 0)
      i j := by
  refine ggQ2mcr_reflTransGen_map (f := id)
    (r := fun u v : M.Λ => u ≠ v ∧ M.coxeter.M u v ≠ 2)
    (s := fun a b => M.root a (M.coroot b) ≠ 0 ∧ M.root b (M.coroot a) ≠ 0)
    ?_ i j (ggRC_weyl_connected M.isWeyl i j)
  rintro u v ⟨hne, hlab⟩
  have h1 := ggQ2mcr_intCartan_ne (p := 3) (by decide) M.isWeyl hcard M.isCartan hne hlab
  refine ⟨?_, ?_⟩
  · change M.root u (M.coroot v) ≠ 0
    rw [M.pairing u v]
    exact h1.1
  · change M.root v (M.coroot u) ≠ 0
    rw [M.pairing v u]
    exact h1.2

theorem ggQ2_coSpan_of_mem_normalizer {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {φ : MulAut ↥Bs}
    (hφ : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs))) :
    ∀ h ∈ M.coSpan, ggLin (p := 3) M.model φ h ∈ M.coSpan := by
  have hW : ∀ w ∈ ggAutomizer L Bs, ∀ v : M.V,
      ggLin (p := 3) M.model w v - v ∈ M.coSpan := by
    intro w hw
    rw [M.automizer_L] at hw
    refine Subgroup.closure_induction (p := fun w _ => ∀ v : M.V,
      ggLin (p := 3) M.model w v - v ∈ M.coSpan) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, rfl⟩ v
      rw [M.simple_apply i]
      have h : v - M.root i v • M.coroot i - v = -(M.root i v • M.coroot i) := by abel
      rw [h]
      exact M.coSpan.neg_mem (M.coSpan.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
    · intro v
      simp
    · intro a b _ _ ha hb v
      rw [map_mul, LinearEquiv.mul_apply]
      have h : ggLin (p := 3) M.model a (ggLin (p := 3) M.model b v) - v =
          (ggLin (p := 3) M.model a (ggLin (p := 3) M.model b v) -
            ggLin (p := 3) M.model b v) +
            (ggLin (p := 3) M.model b v - v) := by abel
      rw [h]
      exact M.coSpan.add_mem (ha _) (hb v)
    · intro a _ ha v
      rw [map_inv]
      have h : v - (ggLin (p := 3) M.model a)⁻¹ v ∈ M.coSpan := by
        have h0 := ha (ggLin (p := 3) M.model a⁻¹ v)
        simpa [map_inv] using h0
      simpa [neg_sub] using M.coSpan.neg_mem h
  have hmain : ∀ i : M.Λ, ggLin (p := 3) M.model φ (M.coroot i) ∈ M.coSpan := by
    intro i
    have hsimple : M.simple i ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hψ : φ * M.simple i * φ⁻¹ ∈ ggAutomizer L Bs :=
      (Subgroup.mem_normalizer_iff.mp hφ (M.simple i)).mp hsimple
    have hsc : ggLin (p := 3) M.model (M.simple i) (M.coroot i) - M.coroot i =
        M.coroot i := by
      rw [M.simple_apply i, GGQ2LDatum.root_coroot_two M i]
      have h2 : (2 : ZMod 3) = -1 := by decide
      rw [h2]
      module
    have h1 := hW _ hψ (ggLin (p := 3) M.model φ (M.coroot i))
    have h2 : ggLin (p := 3) M.model (φ * M.simple i * φ⁻¹)
        (ggLin (p := 3) M.model φ (M.coroot i)) =
        ggLin (p := 3) M.model φ
          (ggLin (p := 3) M.model (M.simple i) (M.coroot i)) := by
      simp [map_mul, LinearEquiv.mul_apply]
    rw [h2] at h1
    rw [← map_sub, hsc] at h1
    exact h1
  intro h hh
  have hle : M.coSpan ≤
      Submodule.comap (ggLin (p := 3) M.model φ).toLinearMap M.coSpan := by
    rw [GGQ2LDatum.coSpan]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmain i)
  exact hle hh

end CFSG.StandardType

end
