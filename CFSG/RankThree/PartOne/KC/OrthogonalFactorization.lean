module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockScalar
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Scalars

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.scalarGL_mem_range (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : Odd p) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) :
    ∀ c : (AdjoinRoot h)ˣ, c ^ p = 1 → scalarGL x h c ∈ (blockGL Q x h).range := by
  by_cases hself : h = reciprocalPolynomial h
  · obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
      hx.exists_selfDual_hermitian hp2 hh hne1 hself
    exact fun c hc => hx.scalarGL_mem_range_selfDual hp hh hne1 hself hroot H hH hleft hright c hc
  · exact fun c _ => hx.scalarGL_mem_range_paired hh hself c

omit [Finite K] in
theorem OddOrderIsometry.primaryMultiplicity_pos (hx : OddOrderIsometry Q p x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) :
    0 < primaryMultiplicity x.toLinearMap h := by
  have hne := primaryComponent_ne_bot hx.squarefree_minpoly hh
  have : Nontrivial (primaryComponent x.toLinearMap h) := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos

end Scalars

section Factorization

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.exists_local_factorization (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : Odd p) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hpm : h ≠ X - 1 → ¬ p ∣ primaryMultiplicity x.toLinearMap h)
    {t : ↥(supportedBlock Q x h)} (ht : t ^ p = 1) :
    ∃ s k w : ↥(supportedBlock Q x h), t = s * k * w ∧ (∀ g, s * g = g * s) ∧ s ^ p = 1 ∧
      k ^ p = 1 ∧ w ^ p = 1 ∧ (h = X - 1 → s = 1 ∧ k = 1) ∧
      (h ≠ X - 1 → w = 1 ∧ (k : V ≃ₗ[K] V) ∈ specialBlock Q x h) := by
  by_cases hne1 : h = X - 1
  · refine ⟨1, 1, t, by simp, fun g => by simp, one_pow _, one_pow _, ht, fun _ => ⟨rfl, rfl⟩,
      fun h' => absurd hne1 h'⟩
  · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    obtain ⟨s, hsc, hsp, hsd⟩ := hx.exists_scalar_factor hp hh
      (hx.scalarGL_mem_range hp hp2 hh hne1) (hpm hne1) ht
    refine ⟨s, s⁻¹ * t, 1, by simp, hsc, hsp, ?_, one_pow _, fun h' => absurd h' hne1,
      fun _ => ⟨rfl, ?_⟩⟩
    · have hcomm : Commute s⁻¹ t := by
        have := hsc t
        exact (Commute.inv_left (Commute.symm (by exact this.symm : t * s = s * t)))
      rw [hcomm.mul_pow, inv_pow, hsp, inv_one, ht, one_mul]
    · refine mem_specialBlock.mpr ⟨(s⁻¹ * t).2, ?_⟩
      rw [map_mul, ← hsd, ← map_mul, inv_mul_cancel, map_one]

theorem OddOrderIsometry.exists_factorization (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : Odd p) {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    (hpm : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      ¬ p ∣ primaryMultiplicity x.toLinearMap h)
    {v : V ≃ₗ[K] V} (hv : v ∈ isometryCentralizer Q x) (hvp : v ^ p = 1) :
    ∃ z k w : V ≃ₗ[K] V, v = z * k * w ∧ z ∈ isometryCentralizer Q x ∧
      (∀ g ∈ isometryCentralizer Q x, z * g = g * z) ∧ z ^ p = 1 ∧
      k ∈ isometryCentralizer Q x ∧ k ∈ (⨆ h ∈ Rep,
        ⨆ (_ : h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h), specialBlock Q x h) ∧
      k ^ p = 1 ∧ w ∈ supportedBlock Q x (X - 1) ∧ w ^ p = 1 ∧ k * w = w * k := by
  classical
  obtain ⟨t, rfl⟩ := exists_blockProduct_eq hx hRep hv
  set Φ := blockProduct hx hRep with hΦ
  have htp : ∀ i, t i ^ p = 1 := by
    have h1 : Φ (t ^ p) = Φ 1 := by rw [map_pow, hvp, map_one]
    have h2 := blockProduct_injective hx hRep h1
    intro i
    have := congrFun h2 i
    simpa using this
  have key := fun i : ↥Rep => hx.exists_local_factorization hp hp2 (hRep.1 i.2)
    (fun hne => hpm i.1 (hRep.1 i.2) hne) (htp i)
  choose s k w hdec using key
  have hts : t = s * k * w := funext fun i => (hdec i).1
  have hmem : ∀ u : ∀ i : ↥Rep, ↥(supportedBlock Q x ↑i), Φ u ∈ isometryCentralizer Q x := fun u =>
    (range_blockProduct hx hRep).le ⟨u, rfl⟩
  have hpow : ∀ u : ∀ i : ↥Rep, ↥(supportedBlock Q x ↑i), (∀ i, u i ^ p = 1) → Φ u ^ p = 1 := by
    intro u hu
    rw [← map_pow]
    have : u ^ p = 1 := funext fun i => by simpa using hu i
    rw [this, map_one]
  refine ⟨Φ s, Φ k, Φ w, ?_, hmem s, ?_, hpow s fun i => (hdec i).2.2.1, hmem k, ?_,
    hpow k fun i => (hdec i).2.2.2.1, ?_, hpow w fun i => (hdec i).2.2.2.2.1, ?_⟩
  · rw [hts, map_mul, map_mul]
  · intro g hg
    obtain ⟨t', rfl⟩ := exists_blockProduct_eq hx hRep hg
    rw [← map_mul, ← map_mul]
    exact congrArg Φ (funext fun i => (hdec i).2.1 (t' i))
  · refine blockProduct_mem hx hRep _ k fun i => ?_
    have hh := hRep.1 i.2
    have : Fact (Irreducible i.1) := ⟨irreducible_of_mem_primaryFactors hh⟩
    by_cases hne : i.1 = X - 1
    · rw [((hdec i).2.2.2.2.2.1 hne).2]
      exact one_mem _
    · have hkF := ((hdec i).2.2.2.2.2.2 hne).2
      by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap i.1
      · exact Subgroup.mem_iSup_of_mem i.1 (Subgroup.mem_iSup_of_mem i.2
          (Subgroup.mem_iSup_of_mem ⟨hne, hm⟩ hkF))
      · have h1 : primaryMultiplicity x.toLinearMap i.1 = 1 := by
          have := hx.primaryMultiplicity_pos hh
          omega
        have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hh h1
        rw [hbot] at hkF
        rw [(Subgroup.mem_bot.mp hkF)]
        exact one_mem _
  · by_cases hex : ∃ i₀ : ↥Rep, i₀.1 = X - 1
    · obtain ⟨i₀, hi₀⟩ := hex
      have hwe : w = Pi.mulSingle i₀ (w i₀) := by
        funext i
        by_cases hi : i = i₀
        · subst hi
          simp
        · have hne : i.1 ≠ X - 1 := fun e => hi (Subtype.ext (e.trans hi₀.symm))
          rw [Pi.mulSingle_eq_of_ne hi, ((hdec i).2.2.2.2.2.2 hne).1]
      rw [hwe, blockProduct_mulSingle hx hRep i₀ (w i₀)]
      have h2 := (w i₀).2
      have h3 : supportedBlock Q x ↑i₀ = supportedBlock Q x (X - 1) := by rw [hi₀]
      exact h3.le h2
    · have : w = 1 := funext fun i => ((hdec i).2.2.2.2.2.2 (fun e => hex ⟨i, e⟩)).1
      rw [this, map_one]
      exact one_mem _
  · rw [← map_mul, ← map_mul]
    refine congrArg Φ (funext fun i => ?_)
    by_cases hne : i.1 = X - 1
    · rw [Pi.mul_apply, Pi.mul_apply, ((hdec i).2.2.2.2.2.1 hne).2, one_mul, mul_one]
    · rw [Pi.mul_apply, Pi.mul_apply, ((hdec i).2.2.2.2.2.2 hne).1, one_mul, mul_one]

end Factorization

end CFSG.RankThree.PartOne.KCOrthogonal
