module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortRankSym
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortOmegaData
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortOmegaTransfer
import CFSG.Open.StatedZModTwo
import CFSG.RankThree.Classical.EvenSurvivingScalarRank

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly
open CFSG.StandardType.FrameRoute.OmegaTen
open scoped commutatorElement

private theorem omegaTenSym_genProd_add (x y : Fin 4 → ZMod 3) :
    genProd (x + y) = genProd x * genProd y := by
  let a : Fin 4 → GL Idx (ZMod 2) := fun i => gen i ^ (x i).val
  let b : Fin 4 → GL Idx (ZMod 2) := fun i => gen i ^ (y i).val
  have hab : ∀ i j : Fin 4, i ≠ j → Commute (a i) (b j) := by
    intro i j _
    have h : Commute (gen i) (gen j) := gen_commute i j
    exact h.pow_pow _ _
  have hp0 := CFSG.RankThree.Classical.pow_val_add (gen_pow_three 0) (x 0) (y 0)
  have hp1 := CFSG.RankThree.Classical.pow_val_add (gen_pow_three 1) (x 1) (y 1)
  have hp2 := CFSG.RankThree.Classical.pow_val_add (gen_pow_three 2) (x 2) (y 2)
  have hp3 := CFSG.RankThree.Classical.pow_val_add (gen_pow_three 3) (x 3) (y 3)
  rw [genProd, genProd, genProd]
  simp only [Pi.add_apply, hp0, hp1, hp2, hp3]
  change (a 0 * b 0) * (a 1 * b 1) * (a 2 * b 2) * (a 3 * b 3) =
    (a 0 * a 1 * a 2 * a 3) * (b 0 * b 1 * b 2 * b 3)
  have h01 : (a 0 * b 0) * (a 1 * b 1) = (a 0 * a 1) * (b 0 * b 1) :=
    Commute.mul_mul_mul_comm (hab 1 0 (by decide)).symm (a 0) (b 1)
  have h02 : Commute (b 0 * b 1) (a 2) :=
    Commute.mul_left (hab 2 0 (by decide)).symm (hab 2 1 (by decide)).symm
  have h12 : ((a 0 * a 1) * (b 0 * b 1)) * (a 2 * b 2) =
      ((a 0 * a 1) * a 2) * ((b 0 * b 1) * b 2) :=
    Commute.mul_mul_mul_comm h02 (a 0 * a 1) (b 2)
  have h03 : Commute ((b 0 * b 1) * b 2) (a 3) :=
    Commute.mul_left (Commute.mul_left (hab 3 0 (by decide)).symm (hab 3 1 (by decide)).symm)
      (hab 3 2 (by decide)).symm
  calc
    (a 0 * b 0) * (a 1 * b 1) * (a 2 * b 2) * (a 3 * b 3)
        = ((a 0 * a 1) * (b 0 * b 1)) * (a 2 * b 2) * (a 3 * b 3) := by rw [h01]
    _ = (((a 0 * a 1) * a 2) * ((b 0 * b 1) * b 2)) * (a 3 * b 3) := by rw [h12]
    _ = (((a 0 * a 1) * a 2) * a 3) * (((b 0 * b 1) * b 2) * b 3) :=
      Commute.mul_mul_mul_comm h03 ((a 0 * a 1) * a 2) (b 3)
    _ = (a 0 * a 1 * a 2 * a 3) * (b 0 * b 1 * b 2 * b 3) := by rfl

private theorem omegaTenSym_genProd_mem (c : Fin 4 → ZMod 3) :
    genProd c ∈ LargeEvenOmega quadTen := by
  rw [genProd]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (gen_mem 0) _) (Subgroup.pow_mem _ (gen_mem 1) _))
    (Subgroup.pow_mem _ (gen_mem 2) _)) (Subgroup.pow_mem _ (gen_mem 3) _)

private def omegaTenSym_e : Fin 4 → ↥(LargeEvenOmega quadTen) :=
  fun i => ⟨gen i, gen_mem i⟩

private def omegaTenSym_fam (c : Fin 4 → ZMod 3) : ↥(LargeEvenOmega quadTen) :=
  ⟨genProd c, omegaTenSym_genProd_mem c⟩

private theorem omegaTenSym_genProd_injective : Function.Injective genProd := by
  decide +kernel

private theorem omegaTenSym_fam_add (c d : Fin 4 → ZMod 3) :
    omegaTenSym_fam (c + d) = omegaTenSym_fam c * omegaTenSym_fam d := by
  apply Subtype.ext
  exact omegaTenSym_genProd_add c d

private theorem omegaTenSym_fam_zero : omegaTenSym_fam 0 = 1 := by
  apply Subtype.ext
  show genProd 0 = (1 : GL Idx (ZMod 2))
  simp [genProd]

private theorem omegaTenSym_fam_neg (c : Fin 4 → ZMod 3) :
    (omegaTenSym_fam c)⁻¹ = omegaTenSym_fam (-c) := by
  have h : omegaTenSym_fam c * omegaTenSym_fam (-c) = 1 := by
    rw [← omegaTenSym_fam_add]
    have h0 : c + -c = 0 := add_neg_cancel c
    rw [h0, omegaTenSym_fam_zero]
  exact inv_eq_of_mul_eq_one_right h

private theorem omegaTenSym_gen_eq_single (i : Fin 4) :
    gen i = genProd (Pi.single i 1) := by
  fin_cases i <;> decide +kernel

private theorem omegaTenSym_e_eq_single (i : Fin 4) :
    omegaTenSym_e i = omegaTenSym_fam (Pi.single i 1) := by
  apply Subtype.ext
  simpa [omegaTenSym_e, omegaTenSym_fam] using omegaTenSym_gen_eq_single i

private theorem omegaTenSym_fam_mem_closure (c : Fin 4 → ZMod 3) :
    omegaTenSym_fam c ∈ Subgroup.closure (Set.range omegaTenSym_e) := by
  have h0 : omegaTenSym_e 0 ^ (c 0).val ∈
      Subgroup.closure (Set.range omegaTenSym_e) :=
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))) _
  have h1 : omegaTenSym_e 1 ^ (c 1).val ∈
      Subgroup.closure (Set.range omegaTenSym_e) :=
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 4))) _
  have h2 : omegaTenSym_e 2 ^ (c 2).val ∈
      Subgroup.closure (Set.range omegaTenSym_e) :=
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))) _
  have h3 : omegaTenSym_e 3 ^ (c 3).val ∈
      Subgroup.closure (Set.range omegaTenSym_e) :=
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (3 : Fin 4))) _
  have hm : omegaTenSym_e 0 ^ (c 0).val * omegaTenSym_e 1 ^ (c 1).val *
      omegaTenSym_e 2 ^ (c 2).val * omegaTenSym_e 3 ^ (c 3).val ∈
      Subgroup.closure (Set.range omegaTenSym_e) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h0 h1) h2) h3
  have heq : (omegaTenSym_e 0 ^ (c 0).val * omegaTenSym_e 1 ^ (c 1).val *
      omegaTenSym_e 2 ^ (c 2).val * omegaTenSym_e 3 ^ (c 3).val :
      ↥(LargeEvenOmega quadTen)) = omegaTenSym_fam c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, omegaTenSym_e, omegaTenSym_fam, genProd]
  rwa [heq] at hm

private theorem omegaTenSym_closure_subset_fam :
    ∀ x ∈ Subgroup.closure (Set.range omegaTenSym_e), x ∈ Set.range omegaTenSym_fam := by
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x ∈ Set.range omegaTenSym_fam) ?_ ?_ ?_ ?_
    hx
  · rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, (omegaTenSym_e_eq_single i).symm⟩
  · exact ⟨0, omegaTenSym_fam_zero⟩
  · rintro x y _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, omegaTenSym_fam_add c d⟩
  · rintro x _ ⟨c, rfl⟩
    exact ⟨-c, (omegaTenSym_fam_neg c).symm⟩

private theorem omegaTenSym_closure_card :
    Nat.card (Subgroup.closure (Set.range omegaTenSym_e)) = 3 ^ 4 := by
  have hinj : Function.Injective omegaTenSym_fam := by
    intro c d h
    apply omegaTenSym_genProd_injective
    simpa [omegaTenSym_fam] using congrArg Subtype.val h
  let F : (Fin 4 → ZMod 3) → Subgroup.closure (Set.range omegaTenSym_e) :=
    fun c => ⟨omegaTenSym_fam c, omegaTenSym_fam_mem_closure c⟩
  have hF : Function.Bijective F := by
    constructor
    · intro c d h
      exact hinj (congrArg Subtype.val h)
    · intro x
      obtain ⟨c, hc⟩ := omegaTenSym_closure_subset_fam x x.2
      exact ⟨c, Subtype.ext hc⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF)]
  rw [Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card]

private theorem omegaTenSym_closure_inter_center :
    Subgroup.closure (Set.range omegaTenSym_e) ⊓
      Subgroup.center ↥(LargeEvenOmega quadTen) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxcl, hxcent⟩
  obtain ⟨c, hc⟩ := omegaTenSym_closure_subset_fam x hxcl
  have hcomm : gTest * genProd c = genProd c * gTest := by
    have h := congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp hxcent) ⟨gTest, gTest_mem⟩)
    simp only [Subgroup.coe_mul] at h
    rw [← hc] at h
    exact h
  have hc0 : c = 0 := eq_zero_of_gTest_commute hcomm
  rw [Subgroup.mem_bot, ← hc, hc0]
  exact omegaTenSym_fam_zero

private def omegaTenSym_s01 : GL Idx (ZMod 2) := reflGL (av 0) * reflGL (av 1)

private def omegaTenSym_s02 : GL Idx (ZMod 2) := reflGL (av 0) * reflGL (av 2)

private def omegaTenSym_s34 : GL Idx (ZMod 2) := reflGL (av 3) * reflGL (av 4)

private def omegaTenSym_g01 : GL Idx (ZMod 2) :=
  reflGL (vec [iy 0, iy 1, ix 2, iy 2]) * reflGL (vec [iy 0, ix 2, iy 2])

private def omegaTenSym_g02 : GL Idx (ZMod 2) :=
  reflGL (vec [ix 1, ix 3, iy 3, iy 0, iy 2]) *
    reflGL (vec [ix 0, ix 1, ix 2, ix 3, iy 3])

private def omegaTenSym_g34 : GL Idx (ZMod 2) :=
  reflGL (vec [ix 3, iy 3, iv, ix 0, iy 0, iu]) *
    reflGL (vec [ix 2, iy 2, ix 3, iv, ix 0, iy 0])

private theorem omegaTenSym_s01_mem : omegaTenSym_s01 ∈ LargeEvenOmega quadTen := by
  have hg : omegaTenSym_g01 ∈ LargeEvenOrthGroup quadTen :=
    Subgroup.mul_mem _ (reflGL_mem_largeEvenOrthGroup (by decide +kernel))
      (reflGL_mem_largeEvenOrthGroup (by decide +kernel))
  have h : omegaTenSym_s01 = ⁅reflGL (av 0), omegaTenSym_g01⁆ := by decide +kernel
  rw [h, largeEvenOmega_def]
  exact Subgroup.commutator_mem_commutator
    (reflGL_mem_largeEvenOrthGroup (quadTen_av 0)) hg

private theorem omegaTenSym_s02_mem : omegaTenSym_s02 ∈ LargeEvenOmega quadTen := by
  have hg : omegaTenSym_g02 ∈ LargeEvenOrthGroup quadTen :=
    Subgroup.mul_mem _ (reflGL_mem_largeEvenOrthGroup (by decide +kernel))
      (reflGL_mem_largeEvenOrthGroup (by decide +kernel))
  have h : omegaTenSym_s02 = ⁅reflGL (av 0), omegaTenSym_g02⁆ := by decide +kernel
  rw [h, largeEvenOmega_def]
  exact Subgroup.commutator_mem_commutator
    (reflGL_mem_largeEvenOrthGroup (quadTen_av 0)) hg

private theorem omegaTenSym_s34_mem : omegaTenSym_s34 ∈ LargeEvenOmega quadTen := by
  have hg : omegaTenSym_g34 ∈ LargeEvenOrthGroup quadTen :=
    Subgroup.mul_mem _ (reflGL_mem_largeEvenOrthGroup (by decide +kernel))
      (reflGL_mem_largeEvenOrthGroup (by decide +kernel))
  have h : omegaTenSym_s34 = ⁅reflGL (av 3), omegaTenSym_g34⁆ := by decide +kernel
  rw [h, largeEvenOmega_def]
  exact Subgroup.commutator_mem_commutator
    (reflGL_mem_largeEvenOrthGroup (quadTen_av 3)) hg

private def omegaTenSym_sInv : Fin 4 → GL Idx (ZMod 2)
  | 0 => omegaTenSym_s01
  | 1 => omegaTenSym_s01
  | 2 => omegaTenSym_s02
  | 3 => omegaTenSym_s34

private def omegaTenSym_sPair (i j : Fin 4) : GL Idx (ZMod 2) :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
    then omegaTenSym_s02 else omegaTenSym_s01

private theorem omegaTenSym_sInv_mem (i : Fin 4) :
    omegaTenSym_sInv i ∈ LargeEvenOmega quadTen := by
  fin_cases i
  exacts [omegaTenSym_s01_mem, omegaTenSym_s01_mem, omegaTenSym_s02_mem,
    omegaTenSym_s34_mem]

private theorem omegaTenSym_sPair_mem (i j : Fin 4) :
    omegaTenSym_sPair i j ∈ LargeEvenOmega quadTen := by
  unfold omegaTenSym_sPair
  split_ifs with h
  exacts [omegaTenSym_s02_mem, omegaTenSym_s01_mem]

private theorem omegaTenSym_sInv_spec (i : Fin 4) :
    omegaTenSym_sInv i * gen i * (omegaTenSym_sInv i)⁻¹ = (gen i)⁻¹ ∧
      omegaTenSym_sInv i ^ 2 = 1 := by
  fin_cases i <;> exact ⟨by decide +kernel, by decide +kernel⟩

private theorem omegaTenSym_sPair_inv_lt :
    ∀ i j : Fin 4, i < j →
      omegaTenSym_sPair i j * gen i * (omegaTenSym_sPair i j)⁻¹ = (gen i)⁻¹ := by
  decide +kernel

private theorem omegaTenSym_sPair_fix_lt :
    ∀ i j : Fin 4, i < j →
      omegaTenSym_sPair i j * gen j * (omegaTenSym_sPair i j)⁻¹ = gen j := by
  decide +kernel

private theorem omegaTenSym_sPair_sq_lt :
    ∀ i j : Fin 4, i < j → omegaTenSym_sPair i j ^ 2 = 1 := by
  decide +kernel

private theorem omegaTenSym_sPair_spec (i j : Fin 4) (hij : i ≠ j) :
    ∃ s : GL Idx (ZMod 2), s ∈ LargeEvenOmega quadTen ∧ s ^ 2 = 1 ∧
      ((s * gen i * s⁻¹ = gen i ∧ s * gen j * s⁻¹ = (gen j)⁻¹) ∨
        (s * gen i * s⁻¹ = (gen i)⁻¹ ∧ s * gen j * s⁻¹ = gen j)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨omegaTenSym_sPair i j, omegaTenSym_sPair_mem i j,
      omegaTenSym_sPair_sq_lt i j h, Or.inr ⟨?_, ?_⟩⟩
    exact omegaTenSym_sPair_inv_lt i j h
    exact omegaTenSym_sPair_fix_lt i j h
  · refine ⟨omegaTenSym_sPair j i, omegaTenSym_sPair_mem j i,
      omegaTenSym_sPair_sq_lt j i h, Or.inl ⟨?_, ?_⟩⟩
    exact omegaTenSym_sPair_fix_lt j i h
    exact omegaTenSym_sPair_inv_lt j i h

private theorem omegaTenSym_invert_exists (i : Fin 4) :
    ∃ s : ↥(LargeEvenOmega quadTen),
      (∃ k : ℕ, s ^ 2 ^ k = 1) ∧
        s * omegaTenSym_e i * s⁻¹ = (omegaTenSym_e i)⁻¹ := by
  refine ⟨⟨omegaTenSym_sInv i, omegaTenSym_sInv_mem i⟩, ⟨1, ?_⟩, ?_⟩
  · apply Subtype.ext
    simpa using (omegaTenSym_sInv_spec i).2
  · apply Subtype.ext
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, omegaTenSym_e] using
      (omegaTenSym_sInv_spec i).1

private theorem omegaTenSym_pair_exists (i j : Fin 4) (hij : i ≠ j) :
    ∃ s : ↥(LargeEvenOmega quadTen),
      (∃ k : ℕ, s ^ 2 ^ k = 1) ∧
        ((s * omegaTenSym_e i * s⁻¹ = omegaTenSym_e i ∧
            s * omegaTenSym_e j * s⁻¹ = (omegaTenSym_e j)⁻¹) ∨
          (s * omegaTenSym_e i * s⁻¹ = (omegaTenSym_e i)⁻¹ ∧
            s * omegaTenSym_e j * s⁻¹ = omegaTenSym_e j)) := by
  obtain ⟨s, hmem, hsq, hdisj⟩ := omegaTenSym_sPair_spec i j hij
  refine ⟨⟨s, hmem⟩, ⟨1, ?_⟩, ?_⟩
  · apply Subtype.ext
    simpa using hsq
  · rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨?_, ?_⟩
      · apply Subtype.ext
        simpa [Subgroup.coe_mul, Subgroup.coe_inv, omegaTenSym_e] using h1
      · apply Subtype.ext
        simpa [Subgroup.coe_mul, Subgroup.coe_inv, omegaTenSym_e] using h2
    · refine Or.inr ⟨?_, ?_⟩
      · apply Subtype.ext
        simpa [Subgroup.coe_mul, Subgroup.coe_inv, omegaTenSym_e] using h1
      · apply Subtype.ext
        simpa [Subgroup.coe_mul, Subgroup.coe_inv, omegaTenSym_e] using h2

private def omegaTenSym_t : ↥(LargeEvenOmega quadTen) := ⟨tInv, tInv_mem⟩

private theorem omegaTenSym_t_sq : omegaTenSym_t ^ 2 = 1 := by
  apply Subtype.ext
  simpa [omegaTenSym_t] using tInv_sq

private theorem omegaTenSym_t_notcenter :
    omegaTenSym_t ∉ Subgroup.center ↥(LargeEvenOmega quadTen) := by
  intro ht
  have h := (Subgroup.mem_center_iff.mp ht) ⟨gTest, gTest_mem⟩
  have hgl : gTest * tInv = tInv * gTest := by
    have h' := congrArg (fun z : ↥(LargeEvenOmega quadTen) =>
      ((z : GL Idx (ZMod 2)))) h
    simpa only [Subgroup.coe_mul, omegaTenSym_t] using h'
  exact gTest_mul_tInv hgl

private theorem omegaTenSym_t_commute (i : Fin 4) :
    Commute omegaTenSym_t (omegaTenSym_e i) := by
  apply Subtype.ext
  simpa [Subgroup.coe_mul, omegaTenSym_t, omegaTenSym_e] using tInv_mul_gen i

private theorem rank3SymGens_largeEvenOmega_zmod_two :
    Rank3SymGens ↥(LargeEvenOmega (LargeEvenQMinus (K := ZMod 2) 4 1 1)) 4 := by
  refine ⟨omegaTenSym_e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    simpa [omegaTenSym_e] using gen_pow_three i
  · intro i j
    apply Subtype.ext
    simpa [Subgroup.coe_mul, omegaTenSym_e] using gen_commute i j
  · exact omegaTenSym_closure_card
  · exact omegaTenSym_closure_inter_center
  · refine ⟨omegaTenSym_t, ⟨1, by simpa using omegaTenSym_t_sq⟩,
      omegaTenSym_t_notcenter, omegaTenSym_t_commute⟩
  · exact omegaTenSym_invert_exists
  · exact omegaTenSym_pair_exists

private theorem rank3SymGens_largeEvenOmega_of_card_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Rank3SymGens ↥(LargeEvenOmega (LargeEvenQMinus (K := K) 4 1 1)) 4 := by
  let σ : ZMod 2 ≃+* K := by
    have : Fintype K := Fintype.ofFinite K
    exact ZMod.ringEquivOfPrime K Nat.prime_two (by rwa [Nat.card_eq_fintype_card] at hK)
  have hQ : ∀ v : LargeEvenMinusIdx 4 → ZMod 2,
      LargeEvenQMinus (K := K) 4 1 1 (fun i => σ (v i)) =
        σ (LargeEvenQMinus (K := ZMod 2) 4 1 1 v) := by
    intro v
    simp only [LargeEvenQMinus, map_add, map_sum, map_mul, map_pow, one_mul]
  obtain ⟨e⟩ := nonempty_mulEquiv_largeEvenOmega_of_ringEquiv
    (Q := LargeEvenQMinus (K := ZMod 2) 4 1 1)
    (Q' := LargeEvenQMinus (K := K) 4 1 1) σ hQ
  exact Rank3SymGens.of_mulEquiv e rank3SymGens_largeEvenOmega_zmod_two

theorem rank3SymGens_largeEvenProjOmegaTenMinus {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Rank3SymGens (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus 4 b c))) 4 := by
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  have hK01 : ∀ s : K, s = 0 ∨ s = 1 := fun s =>
    (eq_or_ne s 0).imp id fun h => congrArg Units.val (Subsingleton.elim (Units.mk0 s h) 1)
  have h2 : (2 : K) = 0 :=
    (hK01 2).resolve_right fun h => one_ne_zero (α := K) (by linear_combination h)
  have hc : c = 1 := (hK01 c).resolve_left fun h => hbc 0 (by simp [h])
  have hb : b = 1 :=
    (hK01 b).resolve_left fun h => hbc 1 (by rw [h, hc]; linear_combination h2)
  subst hb hc
  let H : Subgroup (GL (LargeEvenMinusIdx 4) K) :=
    LargeEvenOmega (LargeEvenQMinus (K := K) 4 1 1)
  have hscal : LargeEvenScalars (LargeEvenMinusIdx 4) K = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK _
  have hbot : (LargeEvenScalars (LargeEvenMinusIdx 4) K).subgroupOf H = ⊥ := by
    rw [hscal, Subgroup.bot_subgroupOf]
  obtain ⟨eR⟩ : Nonempty (LargeEvenProj H ≃* ↥H) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot⟩
  exact Rank3SymGens.of_mulEquiv eR.symm
    (rank3SymGens_largeEvenOmega_of_card_two hK)

end CFSG.StandardType.FrameRoute

end
