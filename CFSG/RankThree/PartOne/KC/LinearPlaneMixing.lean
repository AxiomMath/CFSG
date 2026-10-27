module

public import Mathlib
public import CFSG.RankThree.PartOne.KC.LinearPlaneDecomp
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartOne.KCLinPlane

open Polynomial Module Matrix CFSG CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCUnitaryPlane

section Field

variable {K : Type*} [Field K]

theorem exists_dvd_comp_pow {p : ℕ} (hp : p.Prime) {h₁ h₂ : K[X]} (hirr₂ : Irreducible h₂)
    (hmon₂ : h₂.Monic) (hd₁ : h₁ ∣ X ^ p - 1) (hd₂ : h₂ ∣ X ^ p - 1) (hne₂ : h₂ ≠ X - C 1)
    (hpos₁ : 0 < h₁.natDegree) : ∃ j : ℕ, h₂ ∣ h₁.comp (X ^ j) := by
  have : Fact (Irreducible h₂) := ⟨hirr₂⟩
  have : Fact p.Prime := ⟨hp⟩
  set ω : AdjoinRoot h₂ := AdjoinRoot.root h₂ with hω
  have hωp : ω ^ p = 1 := by
    have h0 : AdjoinRoot.mk h₂ (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd₂
    simpa [sub_eq_zero] using h0
  have hω1 : ω ≠ 1 := by
    intro h1
    apply hne₂
    have h0 : AdjoinRoot.mk h₂ (X - C 1) = 0 := by simp [hω] at h1 ⊢; simp [h1]
    have hdvd : h₂ ∣ X - C 1 := AdjoinRoot.mk_eq_zero.mp h0
    exact eq_of_monic_of_associated hmon₂ (monic_X_sub_C 1)
      (hirr₂.associated_of_dvd (irreducible_X_sub_C 1) hdvd)
  have hord : orderOf ω = p := orderOf_eq_prime hωp hω1
  have hprim : IsPrimitiveRoot ω p := hord ▸ IsPrimitiveRoot.orderOf ω
  have hsplit : Splits (X ^ p - C (1 : AdjoinRoot h₂)) := X_pow_sub_one_splits hprim
  have hd₁' : h₁.map (algebraMap K (AdjoinRoot h₂)) ∣ X ^ p - C (1 : AdjoinRoot h₂) := by
    have := Polynomial.map_dvd (algebraMap K (AdjoinRoot h₂)) hd₁
    simpa using this
  have hne0 : (X ^ p - C (1 : AdjoinRoot h₂) : (AdjoinRoot h₂)[X]) ≠ 0 :=
    (monic_X_pow_sub_C (1 : AdjoinRoot h₂) hp.ne_zero).ne_zero
  have hsplit₁ := hsplit.of_dvd hne0 hd₁'
  have hdeg : (h₁.map (algebraMap K (AdjoinRoot h₂))).degree ≠ 0 := by
    rw [degree_map]
    intro h0
    have := natDegree_eq_of_degree_eq_some (n := 0) (by simpa using h0)
    omega
  obtain ⟨ω₁, hω₁⟩ := hsplit₁.exists_eval_eq_zero hdeg
  have hω₁p : ω₁ ^ p = 1 := by
    obtain ⟨g, hg⟩ := hd₁'
    have h2 := congrArg (Polynomial.eval ω₁) hg
    rw [eval_mul, hω₁, zero_mul] at h2
    simpa [sub_eq_zero] using h2
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hω₁p
  refine ⟨j, ?_⟩
  have h3 : AdjoinRoot.mk h₂ (h₁.comp (X ^ j)) = 0 := by
    rw [← AdjoinRoot.aeval_eq, aeval_comp]
    simp only [map_pow, aeval_X]
    rw [← hω, hj, ← eval_map_algebraMap]
    exact hω₁
  exact AdjoinRoot.mk_eq_zero.mp h3

end Field

section Mixing

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] (E0 : Subgroup (SpecialLinearGroup (Fin n) K))
  [Fintype E0] [IsMulCommutative E0] [Finite K] (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)

local notation "ρ₀" => planeRep E0

omit [IsMulCommutative E0] [Finite K] in
theorem act_mul_projLine {y : ↥E0} {L : Subgroup ↥E0} (hy : y ∈ L) :
    act (planeRep E0) y * projLine (planeRep E0) L = projLine (planeRep E0) L := by
  unfold projLine
  rw [mul_sub, act_mul_avgOp _ hy, act_mul_avgOp _ (Subgroup.mem_top y)]

omit [IsMulCommutative E0] [Finite K] in
theorem exists_ne_one_mem {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (hP : IsPlane p E0) :
    ∃ b ∈ L, b ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : L = ⊥ := (Subgroup.eq_bot_iff_forall L).mpr fun y hy => hcon y hy
  have h1 : Nat.card L = p := mem_lines.mp hL
  rw [hbot, Subgroup.card_bot] at h1
  exact hP.prime.one_lt.ne h1

include hP hpK

omit [Finite K] hP hpK in
theorem stable_range_projLine (y : ↥E0) (N : Subgroup ↥E0) :
    ∀ u ∈ LinearMap.range (projLine ρ₀ N), act ρ₀ y u ∈ LinearMap.range (projLine ρ₀ N) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨act ρ₀ y w, ?_⟩
  have := congrArg (fun f : Module.End K (Fin n → K) => f w)
    (commute_act_projLine E0 y N).eq
  simpa using this.symm

omit [IsMulCommutative E0] [Finite K] hP hpK in
theorem fix_range_projLine {y : ↥E0} {L : Subgroup ↥E0} (hy : y ∈ L) :
    ∀ u ∈ LinearMap.range (projLine ρ₀ L), act ρ₀ y u = u := by
  rintro _ ⟨w, rfl⟩
  simpa using congrArg (fun f : Module.End K (Fin n → K) => f w) (act_mul_projLine E0 hy)

theorem exists_mixing_block {L M : Subgroup ↥E0} (hL : L ∈ lines p E0) (hM : M ∈ lines p E0)
    (hLM : L ≠ M) (hLne : projLine ρ₀ L ≠ 0) (hMne : projLine ρ₀ M ≠ 0) :
    ∃ a : ↥E0, a ≠ 1 ∧ ∃ h ∈ primaryFactors (act ρ₀ a),
      orderOf ((Nat.card K : ℕ) : ZMod p) ≤ h.natDegree ∧
      projLine ρ₀ L * primaryProjection (act ρ₀ a) h ≠ 0 ∧
      projLine ρ₀ M * primaryProjection (act ρ₀ a) h ≠ 0 := by
  obtain ⟨b, hbL, hb1⟩ := exists_ne_one_mem E0 hL hP
  obtain ⟨c, hcM, hc1⟩ := exists_ne_one_mem E0 hM hP
  obtain ⟨h₁, hh₁, hne₁, hne₁0⟩ := exists_factor E0 hP hpK hL hM hLM hLne hcM hc1
  obtain ⟨h₂, hh₂, hne₂, hne₂0⟩ := exists_factor E0 hP hpK hM hL (Ne.symm hLM) hMne hbL hb1
  have hxpc : act ρ₀ c ^ p = 1 := by rw [← act_pow, hP.pow c, act_one]
  have hxpb : act ρ₀ b ^ p = 1 := by rw [← act_pow, hP.pow b, act_one]
  have hsqc := squarefree_minpoly_of_pow_eq_one hpK hxpc
  have hsqb := squarefree_minpoly_of_pow_eq_one hpK hxpb
  have hd₁ : h₁ ∣ X ^ p - 1 :=
    (mem_primaryFactors.mp hh₁).2.2.trans (minpoly.dvd K _ (by simp [hxpc]))
  have hd₂ : h₂ ∣ X ^ p - 1 :=
    (mem_primaryFactors.mp hh₂).2.2.trans (minpoly.dvd K _ (by simp [hxpb]))
  have hirr₁ := irreducible_of_mem_primaryFactors hh₁
  have hmon₁ := monic_of_mem_primaryFactors hh₁
  obtain ⟨j, hj⟩ := exists_dvd_comp_pow hP.prime (irreducible_of_mem_primaryFactors hh₂)
    (monic_of_mem_primaryFactors hh₂) hd₁ hd₂ hne₂ hirr₁.natDegree_pos
  obtain ⟨q, hq⟩ := hj
  obtain ⟨v₁, hv₁⟩ : ∃ v, (projLine ρ₀ L * primaryProjection (act ρ₀ c) h₁) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne₁0 (LinearMap.ext fun v => hcon v)
  obtain ⟨v₂, hv₂⟩ : ∃ v, (projLine ρ₀ M * primaryProjection (act ρ₀ b) h₂) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne₂0 (LinearMap.ext fun v => hcon v)
  set y₁ := projLine ρ₀ L (primaryProjection (act ρ₀ c) h₁ v₁) with hy₁
  set y₂ := projLine ρ₀ M (primaryProjection (act ρ₀ b) h₂ v₂) with hy₂
  have hy₁0 : y₁ ≠ 0 := hv₁
  have hy₂0 : y₂ ≠ 0 := hv₂
  have hbj : b ^ j ∈ L := L.pow_mem hbL j
  have hxpa : act ρ₀ (b ^ j * c) ^ p = 1 := by rw [← act_pow, hP.pow _, act_one]
  have hsqa := squarefree_minpoly_of_pow_eq_one hpK hxpa
  have ha1 : b ^ j * c ≠ 1 := by
    intro h1
    have hcL : c ∈ L := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact L.inv_mem hbj
    have hcLM : c ∈ L ⊓ M := ⟨hcL, hcM⟩
    rw [hP.inf_eq_bot (mem_lines.mp hL) (mem_lines.mp hM) hLM] at hcLM
    exact hc1 (Subgroup.mem_bot.mp hcLM)
  have haL : ∀ u ∈ LinearMap.range (projLine ρ₀ L), act ρ₀ (b ^ j * c) u = act ρ₀ c u := by
    intro u hu
    rw [act_mul, Module.End.mul_apply]
    exact fix_range_projLine E0 hbj _ (stable_range_projLine E0 c L u hu)
  have haM : ∀ u ∈ LinearMap.range (projLine ρ₀ M),
      act ρ₀ (b ^ j * c) u = (act ρ₀ b ^ j) u := by
    intro u hu
    rw [act_mul, Module.End.mul_apply, fix_range_projLine E0 hcM u hu, act_pow]
  have hy₁c : y₁ ∈ primaryComponent (act ρ₀ c) h₁ :=
    apply_mem_primaryComponent (commute_act_projLine E0 c L).symm
      (primaryProjection_mem hsqc hh₁ v₁)
  have hy₁U : y₁ ∈ LinearMap.range (projLine ρ₀ L) := LinearMap.mem_range_self _ _
  have hy₁a : y₁ ∈ primaryComponent (act ρ₀ (b ^ j * c)) h₁ := by
    rw [mem_primaryComponent, aeval_apply_eq_of_agree (stable_range_projLine E0 _ L) haL h₁ hy₁U]
    exact mem_primaryComponent.mp hy₁c
  have hy₂b : y₂ ∈ primaryComponent (act ρ₀ b) h₂ :=
    apply_mem_primaryComponent (commute_act_projLine E0 b M).symm
      (primaryProjection_mem hsqb hh₂ v₂)
  have hy₂U : y₂ ∈ LinearMap.range (projLine ρ₀ M) := LinearMap.mem_range_self _ _
  have hy₂a : y₂ ∈ primaryComponent (act ρ₀ (b ^ j * c)) h₁ := by
    rw [mem_primaryComponent, aeval_apply_eq_of_agree (stable_range_projLine E0 _ M) haM h₁ hy₂U]
    have h5 : aeval (act ρ₀ b ^ j) h₁ = aeval (act ρ₀ b) (h₁.comp (X ^ j)) := by
      rw [aeval_comp]
      simp
    rw [h5, hq, mul_comm h₂ q, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hy₂b,
      map_zero]
  have hh : h₁ ∈ primaryFactors (act ρ₀ (b ^ j * c)) :=
    mem_primaryFactors_of_ne_zero hirr₁ hmon₁ hy₁0 hy₁a
  have hidL : ∀ w, projLine ρ₀ L (projLine ρ₀ L w) = projLine ρ₀ L w := fun w => by
    simpa using LinearMap.congr_fun (projLine_mul_self ρ₀ hP hpK (mem_lines.mp hL)) w
  have hidM : ∀ w, projLine ρ₀ M (projLine ρ₀ M w) = projLine ρ₀ M w := fun w => by
    simpa using LinearMap.congr_fun (projLine_mul_self ρ₀ hP hpK (mem_lines.mp hM)) w
  refine ⟨b ^ j * c, ha1, h₁, hh, orderOf_le_natDegree_of_mem_primaryFactors hP.prime hxpc hh₁
    hne₁, ?_, ?_⟩
  · intro h0
    have h1 := LinearMap.congr_fun h0 y₁
    rw [Module.End.mul_apply, primaryProjection_of_mem hsqa hh hy₁a, hy₁, hidL] at h1
    exact hy₁0 h1
  · intro h0
    have h1 := LinearMap.congr_fun h0 y₂
    rw [Module.End.mul_apply, primaryProjection_of_mem hsqa hh hy₂a, hy₂, hidM] at h1
    exact hy₂0 h1

end Mixing

end CFSG.RankThree.PartOne.KCLinPlane
