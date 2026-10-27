module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcHighThree

private def intervalVec {n : ℕ} (c : Fin 4 → Fin n) (i j : Fin 4) : Fin n → ℤ :=
  fun x => ∑ t ∈ Finset.Icc i j, if c t = x then (1 : ℤ) else 0

private def f4Path : Fin 4 → Fin Tag.F4.rank := ![0, 1, 2, 3]

private def e6Path : Fin 4 → Fin Tag.E6.rank := ![0, 2, 3, 4]

private def e7Path : Fin 4 → Fin Tag.E7.rank := ![0, 2, 3, 4]

private def e8Path : Fin 4 → Fin Tag.E8.rank := ![0, 2, 3, 4]

private lemma sum_intervalVec_mul {n : ℕ} (c : Fin 4 → Fin n) (i j : Fin 4)
    (k : Fin n → ℕ) :
    ∑ x, intervalVec c i j x * (k x : ℤ) = ∑ t ∈ Finset.Icc i j, (k (c t) : ℤ) := by
  simp only [intervalVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (c t)]
  · simp
  · intro x _ hx
    have hxt : c t ≠ x := fun h => hx h.symm
    simp [hxt]
  · intro h
    exact absurd (Finset.mem_univ (c t)) h

private lemma pigeonhole4 (a b : Fin 4 → ZMod 2) :
    ∃ i j : Fin 4, i ≤ j ∧ (∑ t ∈ Finset.Icc i j, a t) = 0 ∧
      (∑ t ∈ Finset.Icc i j, b t) = 0 := by
  revert a b
  decide +kernel

private lemma f4_interval_isRoot (i j : Fin 4) (hij : i ≤ j) :
    IsRoot .F4 (intervalVec f4Path i j) := by
  rw [isRoot_iff_mem_artifactRoots]
  revert i j
  decide +kernel

private lemma e6_interval_isRoot (i j : Fin 4) (hij : i ≤ j) :
    IsRoot .E6 (intervalVec e6Path i j) := by
  rw [isRoot_iff_mem_artifactRoots]
  revert i j
  decide +kernel

private lemma e7_interval_isRoot (i j : Fin 4) (hij : i ≤ j) :
    IsRoot .E7 (intervalVec e7Path i j) := by
  rw [isRoot_iff_mem_artifactRoots]
  revert i j
  decide +kernel

private lemma e8_interval_isRoot (i j : Fin 4) (hij : i ≤ j) :
    IsRoot .E8 (intervalVec e8Path i j) := by
  rw [isRoot_iff_mem_artifactRoots]
  revert i j
  decide +kernel

private lemma zmod_sum_eq_zero_iff_dvd {n : ℕ} (c : Fin 4 → Fin n) (i j : Fin 4)
    (k : Fin n → ℕ)
    (h : (∑ t ∈ Finset.Icc i j, (k (c t) : ZMod 2)) = 0) :
    (2 : ℤ) ∣ ∑ x, intervalVec c i j x * (k x : ℤ) := by
  rw [sum_intervalVec_mul]
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 ?_
  push_cast
  exact h

theorem exists_root_kills_two {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (k₁ k₂ : Fin τ.rank → ℕ) :
    ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ (2 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧
      (2 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · obtain ⟨i, j, hij, h1, h2⟩ :=
      pigeonhole4 (fun t => (k₁ (f4Path t) : ZMod 2)) (fun t => (k₂ (f4Path t) : ZMod 2))
    exact ⟨intervalVec f4Path i j, f4_interval_isRoot i j hij,
      zmod_sum_eq_zero_iff_dvd f4Path i j k₁ h1,
      zmod_sum_eq_zero_iff_dvd f4Path i j k₂ h2⟩
  · obtain ⟨i, j, hij, h1, h2⟩ :=
      pigeonhole4 (fun t => (k₁ (e6Path t) : ZMod 2)) (fun t => (k₂ (e6Path t) : ZMod 2))
    exact ⟨intervalVec e6Path i j, e6_interval_isRoot i j hij,
      zmod_sum_eq_zero_iff_dvd e6Path i j k₁ h1,
      zmod_sum_eq_zero_iff_dvd e6Path i j k₂ h2⟩
  · obtain ⟨i, j, hij, h1, h2⟩ :=
      pigeonhole4 (fun t => (k₁ (e7Path t) : ZMod 2)) (fun t => (k₂ (e7Path t) : ZMod 2))
    exact ⟨intervalVec e7Path i j, e7_interval_isRoot i j hij,
      zmod_sum_eq_zero_iff_dvd e7Path i j k₁ h1,
      zmod_sum_eq_zero_iff_dvd e7Path i j k₂ h2⟩
  · obtain ⟨i, j, hij, h1, h2⟩ :=
      pigeonhole4 (fun t => (k₁ (e8Path t) : ZMod 2)) (fun t => (k₂ (e8Path t) : ZMod 2))
    exact ⟨intervalVec e8Path i j, e8_interval_isRoot i j hij,
      zmod_sum_eq_zero_iff_dvd e8Path i j k₁ h1,
      zmod_sum_eq_zero_iff_dvd e8Path i j k₂ h2⟩

private lemma rootChar_eq_one_of_two_dvd
    {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    {k : Fin τ.rank → ℕ} (hak : ∀ i, a i = (-1 : Lˣ) ^ k i)
    {α : Fin τ.rank → ℤ} (hd : (2 : ℤ) ∣ ∑ i, α i * (k i : ℤ)) : rootChar a α = 1 := by
  obtain ⟨m, hm⟩ := hd
  have h1 : rootChar a α = (-1 : Lˣ) ^ (∑ i, α i * (k i : ℤ)) := by
    rw [rootChar, ← prod_zpow_eq_zpow_sum_of_group]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hak i, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h1, hm, zpow_mul]
  have h2 : (-1 : Lˣ) ^ (2 : ℤ) = 1 := by
    norm_num
  rw [h2, one_zpow]

theorem langPlaneData_kills_two
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {A : Subgroup (adjointGroup τ K)}
    (hA : ∀ x ∈ A, x ^ 2 = 1) (hcard : Nat.card A = 2 ^ 2) (D : LangPlaneData τ K A) :
    ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ D.Kills α := by
  have hpow : ∀ b : (AlgebraicClosure K)ˣ, b ^ 2 = 1 →
      ∃ k : ℕ, b = (-1 : (AlgebraicClosure K)ˣ) ^ k := by
    intro b hb
    have hb' : (b : AlgebraicClosure K) ^ 2 = 1 := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hb
      simpa using this
    rcases (sq_eq_one_iff (R := AlgebraicClosure K)).1 hb' with h | h
    · exact ⟨0, Units.ext (by simpa using h)⟩
    · exact ⟨1, Units.ext (by simpa using h)⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, -, -, hgen⟩ := exists_gens_of_plane (p := 2) hA hcard
  have hdiag : ∀ x ∈ A, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a = diagMap D x ∧ ∀ i, a i ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    refine ⟨a, ha, fun i => ?_⟩
    have h2 : rootDiagUnit τ (a ^ 2) = rootDiagUnit τ 1 := by
      have e1 : rootDiagUnit τ (a ^ 2) = (rootDiagUnit τ a) ^ 2 :=
        map_pow (rootDiagUnitHom τ (AlgebraicClosure K)) a 2
      have e2 : rootDiagUnit τ (1 : Fin τ.rank → (AlgebraicClosure K)ˣ) = 1 :=
        map_one (rootDiagUnitHom τ (AlgebraicClosure K))
      rw [e1, ha, e2, ← map_pow, hA x hx, map_one]
    have h4 : a ^ 2 = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h2
    simpa using congrFun h4 i
  obtain ⟨a₁, ha₁, hc₁⟩ := hdiag x₁ hx₁
  obtain ⟨a₂, ha₂, hc₂⟩ := hdiag x₂ hx₂
  choose k₁ hk₁ using fun i => hpow (a₁ i) (hc₁ i)
  choose k₂ hk₂ using fun i => hpow (a₂ i) (hc₂ i)
  obtain ⟨α, hα, hd₁, hd₂⟩ := exists_root_kills_two hτ k₁ k₂
  refine ⟨α, hα, ?_⟩
  set Sg : Subgroup (adjointGroup τ K) :=
    ((rootCharHom (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom τ (AlgebraicClosure K))).comap (diagMap D)
  have hmemS : ∀ (x : adjointGroup τ K) (a : Fin τ.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit τ a = diagMap D x → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hα1
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, ?_, hax⟩)
    exact hα1
  have hx₁S : x₁ ∈ Sg := hmemS x₁ a₁ ha₁ (rootChar_eq_one_of_two_dvd hk₁ hd₁)
  have hx₂S : x₂ ∈ Sg := hmemS x₂ a₂ ha₂ (rootChar_eq_one_of_two_dvd hk₂ hd₂)
  have hAS : A ≤ Sg := hgen.trans ((Subgroup.closure_le Sg).2 (by
    rintro y (rfl | rfl)
    · exact hx₁S
    · exact hx₂S))
  intro x hx
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hx))
  exact ⟨a, by rw [← diagMap_apply]; exact hax, ha⟩

end CFSG.LocalAnalysis.WeakClosure81
