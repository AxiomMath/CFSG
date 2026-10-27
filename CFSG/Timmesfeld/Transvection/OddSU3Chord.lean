module

public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.Timmesfeld.ARS.Defs
public import CFSG.Timmesfeld.Transvection.PresSUModel
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Torus
public import CFSG.LieType.Steinberg.CentralExt.SUOddCover
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUEmbed
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Timmesfeld.ARS.BasicTwoGroup
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Universal.SpecialLinear
  CFSG.LocalAnalysis.UniquenessCase CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.BorelTits CFSG.AGLEmbedding.LeviBlock
  Subgroup
open Pres

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

section Defs

variable (σ : F ≃+* F)

@[expose] noncomputable def su2Top : Subgroup (SU σ 2) :=
  (longRootHom σ (i := (0 : Fin 2)) (by decide)).range

@[expose] noncomputable def su2Bot : Subgroup (SU σ 2) :=
  (longRootHom σ (i := (1 : Fin 2)) (by decide)).range

@[expose] noncomputable def su3Top : Subgroup (SU σ 3) :=
  (longRootHom σ (i := (0 : Fin 3)) (by decide)).range

@[expose] noncomputable def su3Bot : Subgroup (SU σ 3) :=
  (longRootHom σ (i := (2 : Fin 3)) (by decide)).range

@[expose] def su3ChordIdx : Fin 2 → Fin 3 := ![0, 2]

theorem su3ChordIdx_injective : Function.Injective su3ChordIdx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [su3ChordIdx]

theorem su3ChordIdx_rev (i : Fin 2) : su3ChordIdx (Fin.rev i) = Fin.rev (su3ChordIdx i) := by
  fin_cases i <;> rfl

@[expose] noncomputable def su3Chord : SU σ 2 →* SU σ 3 :=
  suEmbed σ su3ChordIdx_injective su3ChordIdx_rev

end Defs

variable {σ : F ≃+* F}

theorem mat_su3Chord (A : SU σ 2) : mat σ 3 (su3Chord σ A) =
    !![mat σ 2 A 0 0, 0, mat σ 2 A 0 1; 0, 1, 0; mat σ 2 A 1 0, 0, mat σ 2 A 1 1] := by
  have hmat : mat σ 3 (su3Chord σ A) = extendMat su3ChordIdx_injective (mat σ 2 A) :=
    mat_suEmbed (σ := σ) (hτ := su3ChordIdx_injective) (hr := su3ChordIdx_rev) A
  have hne1 : (1 : Fin 3) ∉ Set.range su3ChordIdx := by
    rintro ⟨a, ha⟩
    fin_cases a <;> exact absurd ha (by decide)
  have h00 : extendMat su3ChordIdx_injective (mat σ 2 A) 0 0 = mat σ 2 A 0 0 :=
    extendMat_apply_map su3ChordIdx_injective (mat σ 2 A) 0 0
  have h02 : extendMat su3ChordIdx_injective (mat σ 2 A) 0 2 = mat σ 2 A 0 1 :=
    extendMat_apply_map su3ChordIdx_injective (mat σ 2 A) 0 1
  have h20 : extendMat su3ChordIdx_injective (mat σ 2 A) 2 0 = mat σ 2 A 1 0 :=
    extendMat_apply_map su3ChordIdx_injective (mat σ 2 A) 1 0
  have h22 : extendMat su3ChordIdx_injective (mat σ 2 A) 2 2 = mat σ 2 A 1 1 :=
    extendMat_apply_map su3ChordIdx_injective (mat σ 2 A) 1 1
  have h01 : extendMat su3ChordIdx_injective (mat σ 2 A) 0 1 = 0 := by
    rw [extendMat_apply_of_not_mem su3ChordIdx_injective _ (Or.inr hne1), Matrix.one_apply]
    exact if_neg (by decide)
  have h10 : extendMat su3ChordIdx_injective (mat σ 2 A) 1 0 = 0 := by
    rw [extendMat_apply_of_not_mem su3ChordIdx_injective _ (Or.inl hne1), Matrix.one_apply]
    exact if_neg (by decide)
  have h12 : extendMat su3ChordIdx_injective (mat σ 2 A) 1 2 = 0 := by
    rw [extendMat_apply_of_not_mem su3ChordIdx_injective _ (Or.inl hne1), Matrix.one_apply]
    exact if_neg (by decide)
  have h21 : extendMat su3ChordIdx_injective (mat σ 2 A) 2 1 = 0 := by
    rw [extendMat_apply_of_not_mem su3ChordIdx_injective _ (Or.inr hne1), Matrix.one_apply]
    exact if_neg (by decide)
  have h11 : extendMat su3ChordIdx_injective (mat σ 2 A) 1 1 = 1 := by
    rw [extendMat_apply_of_not_mem su3ChordIdx_injective _ (Or.inl hne1)]
    simp
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact h00 | exact h01 | exact h02
      | exact h10 | exact h11 | exact h12
      | exact h20 | exact h21 | exact h22

theorem su3Chord_suLong_inl (c : F) :
    su3Chord σ (suLong σ (Sum.inl (0 : Fin (2 / 2))) c) =
      suLong σ (Sum.inl (0 : Fin (3 / 2))) c := by
  unfold suLong
  split_ifs with h
  · exact suEmbed_longRootHom (σ := σ) (hτ := su3ChordIdx_injective)
      (hr := su3ChordIdx_rev) _ _
  · simp

theorem su3Chord_suLong_inr (c : F) :
    su3Chord σ (suLong σ (Sum.inr (0 : Fin (2 / 2))) c) =
      suLong σ (Sum.inr (0 : Fin (3 / 2))) c := by
  unfold suLong
  split_ifs with h
  · exact suEmbed_longRootHom (σ := σ) (hτ := su3ChordIdx_injective)
      (hr := su3ChordIdx_rev) _ _
  · simp

theorem mem_su2Top_iff {x : SU σ 2} :
    x ∈ su2Top σ ↔ ∃ c : F, σ c = c ∧ suLong σ (Sum.inl (0 : Fin (2 / 2))) c = x := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(c.toAdd : F), (CharTwo.add_eq_zero.1 c.toAdd.2).symm, ?_⟩
    rw [suLong, dif_pos ((mem_traceZero (σ := σ)).1 c.toAdd.2)]
    rfl
  · rintro ⟨c, hc, rfl⟩
    have hz : c + σ c = 0 := CharTwo.add_eq_zero.2 hc.symm
    refine ⟨Multiplicative.ofAdd ⟨c, (mem_traceZero (σ := σ)).2 hz⟩, ?_⟩
    rw [suLong, dif_pos hz]
    rfl

theorem mem_su2Bot_iff {x : SU σ 2} :
    x ∈ su2Bot σ ↔ ∃ c : F, σ c = c ∧ suLong σ (Sum.inr (0 : Fin (2 / 2))) c = x := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(c.toAdd : F), (CharTwo.add_eq_zero.1 c.toAdd.2).symm, ?_⟩
    rw [suLong, dif_pos ((mem_traceZero (σ := σ)).1 c.toAdd.2)]
    rfl
  · rintro ⟨c, hc, rfl⟩
    have hz : c + σ c = 0 := CharTwo.add_eq_zero.2 hc.symm
    refine ⟨Multiplicative.ofAdd ⟨c, (mem_traceZero (σ := σ)).2 hz⟩, ?_⟩
    rw [suLong, dif_pos hz]
    rfl

theorem mem_su3Top_iff {x : SU σ 3} :
    x ∈ su3Top σ ↔ ∃ c : F, σ c = c ∧ suLong σ (Sum.inl (0 : Fin (3 / 2))) c = x := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(c.toAdd : F), (CharTwo.add_eq_zero.1 c.toAdd.2).symm, ?_⟩
    rw [suLong, dif_pos ((mem_traceZero (σ := σ)).1 c.toAdd.2)]
    rfl
  · rintro ⟨c, hc, rfl⟩
    have hz : c + σ c = 0 := CharTwo.add_eq_zero.2 hc.symm
    refine ⟨Multiplicative.ofAdd ⟨c, (mem_traceZero (σ := σ)).2 hz⟩, ?_⟩
    rw [suLong, dif_pos hz]
    rfl

theorem mem_su3Bot_iff {x : SU σ 3} :
    x ∈ su3Bot σ ↔ ∃ c : F, σ c = c ∧ suLong σ (Sum.inr (0 : Fin (3 / 2))) c = x := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(c.toAdd : F), (CharTwo.add_eq_zero.1 c.toAdd.2).symm, ?_⟩
    rw [suLong, dif_pos ((mem_traceZero (σ := σ)).1 c.toAdd.2)]
    rfl
  · rintro ⟨c, hc, rfl⟩
    have hz : c + σ c = 0 := CharTwo.add_eq_zero.2 hc.symm
    refine ⟨Multiplicative.ofAdd ⟨c, (mem_traceZero (σ := σ)).2 hz⟩, ?_⟩
    rw [suLong, dif_pos hz]
    rfl

theorem mem_su3Top_iff_Y {x : SU σ 3} :
    x ∈ su3Top σ ↔ ∃ β, ∃ hβ : σ β = β, x = UC22.uc22pwsu3Y β hβ := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(c.toAdd : F), (CharTwo.add_eq_zero.1 c.toAdd.2).symm, ?_⟩
    unfold UC22.uc22pwsu3Y
    rfl
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨Multiplicative.ofAdd ⟨β, (mem_traceZero (σ := σ)).2
      (CharTwo.add_eq_zero.2 hβ.symm)⟩, ?_⟩
    unfold UC22.uc22pwsu3Y
    rfl

theorem su3Top_le_X (hσ : ∀ c, σ (σ c) = c) : su3Top σ ≤ UC22.uc22pwsu3X hσ := by
  intro x hx
  obtain ⟨β, hβ, rfl⟩ := (mem_su3Top_iff_Y (σ := σ)).1 hx
  exact UC22.uc22pwsu3Y_mem hσ β hβ

theorem map_su2Top_su3Chord : (su2Top σ).map (su3Chord σ) = su3Top σ := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨x, hx, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (mem_su2Top_iff (σ := σ)).1 hx
    exact (mem_su3Top_iff (σ := σ)).2 ⟨c, hc, (su3Chord_suLong_inl c).symm⟩
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_su3Top_iff (σ := σ)).1 hy
    exact ⟨suLong σ (Sum.inl 0) c, (mem_su2Top_iff (σ := σ)).2 ⟨c, hc, rfl⟩,
      su3Chord_suLong_inl c⟩

theorem map_su2Bot_su3Chord : (su2Bot σ).map (su3Chord σ) = su3Bot σ := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨x, hx, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (mem_su2Bot_iff (σ := σ)).1 hx
    exact (mem_su3Bot_iff (σ := σ)).2 ⟨c, hc, (su3Chord_suLong_inr c).symm⟩
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_su3Bot_iff (σ := σ)).1 hy
    exact ⟨suLong σ (Sum.inr 0) c, (mem_su2Bot_iff (σ := σ)).2 ⟨c, hc, rfl⟩,
      su3Chord_suLong_inr c⟩

theorem conjSub_su3Top_of_mem_X (hσ : ∀ c, σ (σ c) = c) {u : SU σ 3}
    (hu : u ∈ UC22.uc22pwsu3X hσ) : conjSub (su3Top σ) u = su3Top σ := by
  have key : ∀ v ∈ UC22.uc22pwsu3X hσ, ∀ x ∈ su3Top σ, v * x * v⁻¹ ∈ su3Top σ := by
    intro v hv x hx
    obtain ⟨β, hβ, rfl⟩ := (mem_su3Top_iff_Y (σ := σ)).1 hx
    refine (mem_su3Top_iff_Y (σ := σ)).2 ⟨β, hβ, ?_⟩
    rw [UC22.uc22pwsu3Y_comm hσ hv β hβ]
    group
  rw [conjSub_eq_self_iff, mem_normalizer_iff]
  intro x
  exact ⟨key u hu x, fun hx => by
    have hk := key u⁻¹ (Subgroup.inv_mem _ hu) (u * x * u⁻¹) hx
    rwa [show u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x from by group] at hk⟩

theorem conjSub_su3Top_of_mem_H (hσ : ∀ c, σ (σ c) = c) {h : SU σ 3}
    (hh : h ∈ UC22.uc22pwsu3H σ) : conjSub (su3Top σ) h = su3Top σ := by
  have key : ∀ v ∈ UC22.uc22pwsu3H σ, ∀ x ∈ su3Top σ, v * x * v⁻¹ ∈ su3Top σ := by
    intro v hv x hx
    obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three (σ := σ) hv
    obtain ⟨β, hβ, rfl⟩ := (mem_su3Top_iff_Y (σ := σ)).1 hx
    set d : Fin 3 → F := ![t, σ t / t, (σ t)⁻¹] with hd
    have hdne : ∀ i, d i ≠ 0 := by
      intro i
      fin_cases i <;> simp [hd]
    have hγ : σ (d 0 * (d 2)⁻¹ * β) = d 0 * (d 2)⁻¹ * β := by
      have h0 : d 0 = (t : F) := by simp [hd]
      have h2 : d 2 = (σ (t : F))⁻¹ := by simp [hd]
      have h1 : σ (d 0 * (d 2)⁻¹ * β) = σ (t : F) * (t : F) * β := by
        rw [map_mul, map_mul, h0, h2, inv_inv, hσ, hβ]
      have h3 : d 0 * (d 2)⁻¹ * β = (t : F) * σ (t : F) * β := by
        rw [h0, h2, inv_inv]
      rw [h1, h3]
      ring
    refine (mem_su3Top_iff_Y (σ := σ)).2 ⟨d 0 * (d 2)⁻¹ * β, hγ, ?_⟩
    exact UC22.uc22pwsu3Y_conj hdne ht β hβ _ hγ rfl
  rw [conjSub_eq_self_iff, mem_normalizer_iff]
  intro x
  exact ⟨key h hh x, fun hx => by
    have hk := key h⁻¹ (Subgroup.inv_mem _ hh) (h * x * h⁻¹) hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x from by group] at hk⟩

private theorem mat_suLong_three (a : Fin (3 / 2) ⊕ Fin (3 / 2)) {c : F}
    (hc : c + σ c = 0) : mat σ 3 (suLong (m := 3) σ a c) = longRootMatrix (crd a) c := by
  rw [mat_suLong (m := 3) (a := a) hc, crd_swap]
  rfl

private theorem levelPerm_zero_three :
    levelPerm (0 : Fin (3 / 2)) = Equiv.swap (0 : Fin 3) 2 := by
  rw [levelPerm, dif_neg (by decide)]
  rfl

private theorem levelPerm_zero_three_crd_inl :
    levelPerm (0 : Fin (3 / 2)) (crd (Sum.inl (0 : Fin (3 / 2)))) =
      crd (Sum.swap (Sum.inl (0 : Fin (3 / 2)))) := by
  rw [levelPerm_zero_three]
  rfl

private theorem levelPerm_zero_three_crd_inr :
    levelPerm (0 : Fin (3 / 2)) (crd (Sum.inr (0 : Fin (3 / 2)))) =
      crd (Sum.swap (Sum.inr (0 : Fin (3 / 2)))) := by
  rw [levelPerm_zero_three]
  rfl

private theorem conj_W_suLong_inl (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) {c : F} (hc : c + σ c = 0) :
    UC22.uc22pwsu3W hσ ζ * suLong (m := 3) σ (Sum.inl 0) c =
      suLong (m := 3) σ (Sum.inr 0) (levelSign σ (ζ : F) (0 : Fin (3 / 2))
        (crd (Sum.inl (0 : Fin (3 / 2)))) * c *
        (levelSign σ (ζ : F) (0 : Fin (3 / 2))
          (Fin.rev (crd (Sum.inl (0 : Fin (3 / 2))))))⁻¹) * UC22.uc22pwsu3W hσ ζ := by
  have hts := mul_mem_traceZero_of_unitary (n := 3) (levelSign_unitary hσ hζ 0)
    (crd (Sum.inl (0 : Fin (3 / 2)))) hc
  have hwmat : mat σ 3 (UC22.uc22pwsu3W hσ ζ) =
      signedPerm (levelPerm (0 : Fin (3 / 2))) (levelSign σ (ζ : F) (0 : Fin (3 / 2))) := by
    rw [mat_apply]
    exact coe_levelWeyl hσ hζ 0
  apply mat_injective
  rw [map_mul, map_mul, hwmat, mat_suLong_three (Sum.inl 0) hc,
    mat_suLong_three (Sum.inr 0) hts,
    signedPerm_mul_longRootMatrix (σ := σ) (levelPerm_rev 0) (levelSign_unitary hσ hζ 0)
      (crd (Sum.inl (0 : Fin (3 / 2)))) c, levelPerm_zero_three_crd_inl]
  rfl

private theorem conj_W_suLong_inr (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) {c : F} (hc : c + σ c = 0) :
    UC22.uc22pwsu3W hσ ζ * suLong (m := 3) σ (Sum.inr 0) c =
      suLong (m := 3) σ (Sum.inl 0) (levelSign σ (ζ : F) (0 : Fin (3 / 2))
        (crd (Sum.inr (0 : Fin (3 / 2)))) * c *
        (levelSign σ (ζ : F) (0 : Fin (3 / 2))
          (Fin.rev (crd (Sum.inr (0 : Fin (3 / 2))))))⁻¹) * UC22.uc22pwsu3W hσ ζ := by
  have hts := mul_mem_traceZero_of_unitary (n := 3) (levelSign_unitary hσ hζ 0)
    (crd (Sum.inr (0 : Fin (3 / 2)))) hc
  have hwmat : mat σ 3 (UC22.uc22pwsu3W hσ ζ) =
      signedPerm (levelPerm (0 : Fin (3 / 2))) (levelSign σ (ζ : F) (0 : Fin (3 / 2))) := by
    rw [mat_apply]
    exact coe_levelWeyl hσ hζ 0
  apply mat_injective
  rw [map_mul, map_mul, hwmat, mat_suLong_three (Sum.inr 0) hc,
    mat_suLong_three (Sum.inl 0) hts,
    signedPerm_mul_longRootMatrix (σ := σ) (levelPerm_rev 0) (levelSign_unitary hσ hζ 0)
      (crd (Sum.inr (0 : Fin (3 / 2)))) c, levelPerm_zero_three_crd_inr]
  rfl

theorem conjSub_su3Top_W (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) :
    conjSub (su3Top σ) (UC22.uc22pwsu3W hσ ζ) = su3Bot σ := by
  have hw2 : UC22.uc22pwsu3W hσ ζ * UC22.uc22pwsu3W hσ ζ = 1 := by
    rw [← pow_two]
    exact UC22.uc22pwsu3_levelWeyl_sq hσ hζ
  have hwinv : (UC22.uc22pwsu3W hσ ζ)⁻¹ = UC22.uc22pwsu3W hσ ζ :=
    inv_eq_of_mul_eq_one_right hw2
  have key : ∀ x ∈ su3Top σ,
      UC22.uc22pwsu3W hσ ζ * x * (UC22.uc22pwsu3W hσ ζ)⁻¹ ∈ su3Bot σ := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := (mem_su3Top_iff (σ := σ)).1 hx
    have hcz : c + σ c = 0 := CharTwo.add_eq_zero.2 hc.symm
    have hγz := mul_mem_traceZero_of_unitary (n := 3) (levelSign_unitary hσ hζ 0)
      (crd (Sum.inl (0 : Fin (3 / 2)))) hcz
    have hwx : UC22.uc22pwsu3W hσ ζ * suLong σ (Sum.inl 0) c * (UC22.uc22pwsu3W hσ ζ)⁻¹ =
        suLong σ (Sum.inr 0) (levelSign σ (ζ : F) (0 : Fin (3 / 2)) (crd (Sum.inl 0)) * c *
          (levelSign σ (ζ : F) (0 : Fin (3 / 2))
            (Fin.rev (crd (Sum.inl (0 : Fin (3 / 2))))))⁻¹) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact conj_W_suLong_inl hσ hζ hcz
    rw [hwx]
    exact (mem_su3Bot_iff (σ := σ)).2 ⟨_, (CharTwo.add_eq_zero.1 hγz).symm, rfl⟩
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact key x hx
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_su3Bot_iff (σ := σ)).1 hy
    have hcz : c + σ c = 0 := CharTwo.add_eq_zero.2 hc.symm
    have hγz := mul_mem_traceZero_of_unitary (n := 3) (levelSign_unitary hσ hζ 0)
      (crd (Sum.inr (0 : Fin (3 / 2)))) hcz
    have hwx : UC22.uc22pwsu3W hσ ζ * suLong σ (Sum.inr 0) c * (UC22.uc22pwsu3W hσ ζ)⁻¹ =
        suLong σ (Sum.inl 0) (levelSign σ (ζ : F) (0 : Fin (3 / 2)) (crd (Sum.inr 0)) * c *
          (levelSign σ (ζ : F) (0 : Fin (3 / 2))
            (Fin.rev (crd (Sum.inr (0 : Fin (3 / 2))))))⁻¹) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact conj_W_suLong_inr hσ hζ hcz
    refine ⟨suLong σ (Sum.inl 0) (levelSign σ (ζ : F) (0 : Fin (3 / 2)) (crd (Sum.inr 0)) *
      c * (levelSign σ (ζ : F) (0 : Fin (3 / 2))
        (Fin.rev (crd (Sum.inr (0 : Fin (3 / 2))))))⁻¹),
      (mem_su3Top_iff (σ := σ)).2 ⟨_, (CharTwo.add_eq_zero.1 hγz).symm, rfl⟩, ?_⟩
    show UC22.uc22pwsu3W hσ ζ * suLong σ (Sum.inl 0) _ * (UC22.uc22pwsu3W hσ ζ)⁻¹ =
      suLong σ (Sum.inr 0) c
    rw [← hwx, hwinv]
    calc UC22.uc22pwsu3W hσ ζ * (UC22.uc22pwsu3W hσ ζ * suLong σ (Sum.inr 0) c *
        UC22.uc22pwsu3W hσ ζ) * UC22.uc22pwsu3W hσ ζ
        = (UC22.uc22pwsu3W hσ ζ * UC22.uc22pwsu3W hσ ζ) * suLong σ (Sum.inr 0) c *
          (UC22.uc22pwsu3W hσ ζ * UC22.uc22pwsu3W hσ ζ) := by group
      _ = suLong σ (Sum.inr 0) c := by rw [hw2, one_mul, mul_one]

theorem su2Top_sup_su2Bot (hFn : Nat.card F = (2 ^ n) ^ 2) :
    su2Top (unitaryInvolution F 2 n) ⊔ su2Bot (unitaryInvolution F 2 n) = ⊤ := by
  have hσ : ∀ c, unitaryInvolution F 2 n (unitaryInvolution F 2 n c) = c :=
    unitaryInvolution_involutive hFn
  rw [su2Top, su2Bot, ← rootGroup_two_eq_range (σ := unitaryInvolution F 2 n) hσ,
    ← rootGroup_two_neg_eq_range (σ := unitaryInvolution F 2 n) hσ]
  exact rankOne_two_eq_top (p := 2) (f := n) hFn

theorem odd_card_ker_toPSU (hFn : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) :
    Odd (Nat.card (SUOdd.toPSU hFn 3).ker) := by
  have hcard := Subgroup.card_ker_mul_card_of_surjective
    (SUOdd.toPSU_surjective (p := 2) (f := n) hFn 3)
  rw [card_SU_three (p := 2) (f := n) hFn] at hcard
  have hpsu := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd (p := 2) (f := n)
    Nat.prime_two (by omega) hFn
  rw [← mul_assoc] at hpsu
  have hker : Nat.card (SUOdd.toPSU hFn 3).ker = Nat.gcd 3 (2 ^ n + 1) := by
    refine Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos (α := CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))) ?_
    rw [mul_comm (Nat.gcd 3 (2 ^ n + 1))
      (Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))),
      hcard, hpsu]
  rw [hker]
  exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 (2 ^ n + 1))

theorem su3_exists_section
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) (E : Type)
    [Group E] [Finite E] (π : E →* SU (unitaryInvolution F 2 n) 3)
    (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    ∃ s : SU (unitaryInvolution F 2 n) 3 →* E, ∀ g, π (s g) = g := by
  have hq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : 2 ^ n = 2 := (Prod.mk.inj h).2
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [h1] at h2
    norm_num at h2
  have hker : ((equivStatedSU hFn 3).toMonoidHom.comp π).ker ≤ Subgroup.center E := by
    refine le_trans (fun x hx => ?_) hc
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (map_eq_one_iff _ (equivStatedSU hFn 3).injective).1 hx
  obtain ⟨s, hs⟩ := SUOdd.statedSU_odd_exists_section_of_central (p := 2) (f := n) (n := 3) hFn
    (by omega) le_rfl (by decide) hq
    (π := (equivStatedSU hFn 3).toMonoidHom.comp π)
    ((equivStatedSU hFn 3).surjective.comp hπ) hker
  refine ⟨s.comp (equivStatedSU hFn 3).toMonoidHom, fun g => ?_⟩
  exact (equivStatedSU hFn 3).injective (by simpa using hs ((equivStatedSU hFn 3) g))

end CFSG.Timmesfeld.Transvection
