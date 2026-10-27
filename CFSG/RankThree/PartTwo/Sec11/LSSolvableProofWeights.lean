module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent
public import CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace LSSolvableProof

open Module
open scoped TensorProduct

section Eigen

variable {L W : Type*} [Field L] [AddCommGroup W] [Module L W]

theorem exists_common_eigenvector_of_isAlgClosed [IsAlgClosed L] [FiniteDimensional L W]
    {ι : Type*} [Finite ι] (P : ι → Module.End L W) (hcomm : ∀ i j, Commute (P i) (P j))
    (U : Submodule L W) (hU : ∀ i, ∀ u ∈ U, P i u ∈ U) (hU0 : U ≠ ⊥) :
    ∃ v ∈ U, v ≠ 0 ∧ ∃ χ : ι → L, ∀ i, P i v = χ i • v := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, ∃ χ : ι → L,
      (U ⊓ ⨅ i ∈ s, (P i).eigenspace (χ i)) ≠ ⊥ by
    obtain ⟨χ, hχ⟩ := h Finset.univ
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    refine ⟨v, (Submodule.mem_inf.mp hv).1, hv0, χ, fun i => ?_⟩
    have h2 := (Submodule.mem_inf.mp hv).2
    simp only [Submodule.mem_iInf] at h2
    exact Module.End.mem_eigenspace_iff.mp (h2 i (Finset.mem_univ i))
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hU0⟩
  | insert j s hj ih =>
    obtain ⟨χ, hχ⟩ := ih
    set E := U ⊓ ⨅ i ∈ s, (P i).eigenspace (χ i) with hEdef
    have hE : ∀ e ∈ E, P j e ∈ E := by
      intro e he
      rw [hEdef, Submodule.mem_inf] at he ⊢
      refine ⟨hU j e he.1, ?_⟩
      have h2 := he.2
      simp only [Submodule.mem_iInf] at h2 ⊢
      intro i hi
      have h3 := Module.End.mem_eigenspace_iff.mp (h2 i hi)
      rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, (hcomm i j).eq,
        Module.End.mul_apply, h3, map_smul]
    have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hχ
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((P j).restrict hE)
    obtain ⟨⟨u, huE⟩, hu⟩ := hμ.exists_hasEigenvector
    have hu0 : u ≠ 0 := fun h0 => hu.2 (Subtype.ext h0)
    have hPu : P j u = μ • u := by
      have h1 := Module.End.mem_eigenspace_iff.mp hu.1
      have h2 := congrArg Subtype.val h1
      simpa [LinearMap.restrict_apply] using h2
    refine ⟨Function.update χ j μ, ?_⟩
    rw [Submodule.ne_bot_iff]
    refine ⟨u, ?_, hu0⟩
    rw [hEdef, Submodule.mem_inf] at huE
    rw [Submodule.mem_inf]
    refine ⟨huE.1, ?_⟩
    have h2 := huE.2
    simp only [Submodule.mem_iInf] at h2 ⊢
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Function.update_self, Module.End.mem_eigenspace_iff]
      exact hPu
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      rw [Function.update_of_ne hij]
      exact h2 i hi

theorem card_le_finrank_of_weights [FiniteDimensional L W] {Y : Type*} [Group Y]
    (σ : Y →* Module.End L W) (A : Subgroup Y) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {ι : Type*} [Finite ι] (g : ι → Y) (hg : ∀ i, ∀ a ∈ A, (g i)⁻¹ * a * g i ∈ A) {v : W}
    (hv0 : v ≠ 0) {χ : Y → L} (hv : ∀ a ∈ A, σ a v = χ a • v)
    (hinj : ∀ i j, (∀ a ∈ A, χ ((g i)⁻¹ * a * g i) = χ ((g j)⁻¹ * a * g j)) → i = j) :
    Nat.card ι ≤ Module.finrank L W := by
  set P : A → Module.End L W := fun a => σ a with hP
  have hcomm : ∀ a b : A, Commute (P a) (P b) := fun a b => by
    change σ a * σ b = σ b * σ a
    rw [← map_mul, ← map_mul, hA a a.2 b b.2]
  set w : ι → W := fun i => σ (g i) v with hw
  set χ' : ι → A → L := fun i a => χ ((g i)⁻¹ * a * g i) with hχ'
  have hwv : ∀ i (a : A), P a (w i) = χ' i a • w i := by
    intro i a
    have h1 : σ a * σ (g i) = σ (g i) * σ ((g i)⁻¹ * a * g i) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    change σ a (σ (g i) v) = χ ((g i)⁻¹ * a * g i) • σ (g i) v
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hv _ (hg i a a.2), map_smul]
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i h0
    apply hv0
    have h1 : σ (g i)⁻¹ (σ (g i) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1]
    change σ (g i)⁻¹ (w i) = 0
    rw [h0, map_zero]
  have hχinj : Function.Injective χ' := by
    intro i j h
    apply hinj i j
    intro a ha
    exact congrFun h ⟨a, ha⟩
  have hind := CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof.linearIndependent_of_eigen P hcomm
    χ' hχinj w hwv hw0
  exact CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof.natCard_le_finrank hind

theorem weight_mul {Y : Type*} [Group Y] (σ : Y →* Module.End L W) {A : Subgroup Y} {v : W}
    (hv0 : v ≠ 0) {χ : Y → L} (hv : ∀ a ∈ A, σ a v = χ a • v) {a b : Y} (ha : a ∈ A)
    (hb : b ∈ A) : χ (a * b) = χ a * χ b := by
  apply smul_left_injective L hv0
  change χ (a * b) • v = (χ a * χ b) • v
  rw [← hv _ (A.mul_mem ha hb), map_mul, Module.End.mul_apply, hv b hb, map_smul, hv a ha,
    smul_smul, mul_comm]

theorem weight_one {Y : Type*} [Group Y] (σ : Y →* Module.End L W) {A : Subgroup Y} {v : W}
    (hv0 : v ≠ 0) {χ : Y → L} (hv : ∀ a ∈ A, σ a v = χ a • v) : χ 1 = 1 := by
  apply smul_left_injective L hv0
  change χ 1 • v = (1 : L) • v
  rw [← hv 1 A.one_mem, map_one, Module.End.one_apply, one_smul]

theorem ker_inf_range_eq_bot {b : Module.End L W} {e : ℕ} (hb : b ^ e = 1) (he : (e : L) ≠ 0) :
    LinearMap.ker (b - 1) ⊓ LinearMap.range (b - 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwk, u, rfl⟩
  rw [Submodule.mem_bot]
  have hfix : b ((b - 1) u) = (b - 1) u := by
    have hwk' : (b - 1) u ∈ LinearMap.ker (b - 1) := hwk
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hwk'
    exact hwk'
  have hpow : ∀ i : ℕ, (b ^ i) ((b - 1) u) = (b - 1) u := by
    intro i
    induction i with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ i ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
  have hS : (∑ i ∈ Finset.range e, b ^ i) ((b - 1) u) = 0 := by
    rw [← Module.End.mul_apply, geom_sum_mul, hb, sub_self, LinearMap.zero_apply]
  have hS' : (∑ i ∈ Finset.range e, b ^ i) ((b - 1) u) = (e : L) • ((b - 1) u) := by
    rw [LinearMap.sum_apply]
    simp only [hpow]
    rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
  rw [hS'] at hS
  exact (smul_eq_zero.mp hS).resolve_left he

end Eigen

section BaseChange

variable {F E V : Type*} [Field F] [Field E] [Algebra F E] [AddCommGroup V] [Module F V]

theorem finrank_baseChange_eq [Module.Finite F V] :
    Module.finrank E (E ⊗[F] V) = Module.finrank F V :=
  Module.finrank_baseChange

theorem ker_baseChange_eq_bot {T : V →ₗ[F] V} (hT : LinearMap.ker T = ⊥) :
    LinearMap.ker (T.baseChange E) = ⊥ := by
  rw [← LinearMap.baseChange_ker_eq, hT, Submodule.baseChange_bot]

theorem baseChange_sub_one (T : V →ₗ[F] V) :
    (T - 1).baseChange E = T.baseChange E - 1 := by
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]

end BaseChange

end LSSolvableProof

end CFSG.RankThree.PartTwo.Sec11
