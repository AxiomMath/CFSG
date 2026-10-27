module

public import CFSG.Quasithin.Background.C2PushA3

public section

namespace CFSG.Quasithin.QA24

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.C2Push
open scoped commutatorElement

theorem closure_not_dvd_three_eq_top_of_perfect {Q : Type*} [Group Q] [Finite Q]
    [hQ : Group.IsPerfect Q] : Subgroup.closure {x : Q | ¬ 3 ∣ orderOf x} = ⊤ := by
  set S : Set Q := {x : Q | ¬ 3 ∣ orderOf x} with hS
  have hNn : (Subgroup.closure S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure S) ?_ ?_ ?_ ?_
      hn
    · intro x hx
      apply Subgroup.subset_closure
      show ¬ 3 ∣ orderOf (g * x * g⁻¹)
      have := (MulAut.conj g).orderOf_eq x
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hx
    · simp
    · intro x y _ _ hx hy
      simpa [mul_assoc] using mul_mem hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 (Q ⧸ Subgroup.closure S) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, b, hab, -, ha, hb⟩ := exists_threePrime_threePart g
    obtain ⟨k, hk⟩ := hb b (Subgroup.mem_zpowers b)
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk a : Q ⧸ Subgroup.closure S) = 1 :=
      (QuotientGroup.eq_one_iff a).mpr (Subgroup.subset_closure ha)
    have h2 : (QuotientGroup.mk g : Q ⧸ Subgroup.closure S) = QuotientGroup.mk b := by
      rw [← hab, QuotientGroup.mk_mul, h1, one_mul]
    rw [h2, ← QuotientGroup.mk_pow, hk]
    rfl
  by_contra hne
  have hidx : (Subgroup.closure S).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hnt : Nontrivial (Q ⧸ Subgroup.closure S) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h0 : (Subgroup.closure S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : Nat.card (Q ⧸ Subgroup.closure S) = (Subgroup.closure S).index := rfl
    omega
  have : Group.IsPerfect (Q ⧸ Subgroup.closure S) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Group.IsNilpotent (Q ⧸ Subgroup.closure S) := h3.isNilpotent
  have hsolv : Group.IsSolvable (Q ⧸ Subgroup.closure S) := inferInstance
  exact Group.IsPerfect.not_isSolvable _ hsolv

section Abstract

variable {X : Type*} [Group X] [Finite X]

theorem le_of_forall_eq_mul_prod_of_isPGroup_three_of_perfect {K M₀ : Subgroup X}
    (hKperf : Group.IsPerfect ↥K) (hKn : K.Normal)
    (hK3 : ∀ N : Subgroup X, N ≤ K → N.Normal → IsPGroup 3 N → N = ⊥)
    {r : ℕ} (B : Fin r → Subgroup X) (hB3 : ∀ i, IsPGroup 3 (B i))
    (hBsub : ∀ i, (B i).IsSubnormal)
    (hx : ∀ x ∈ K, ∃ m ∈ M₀, ∃ b : Fin r → X, (∀ i, b i ∈ B i) ∧
      x = m * (List.ofFn b).prod) : K ≤ M₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBP : ∀ i, B i ≤ pCoreOf 3 (⊤ : Subgroup X) := by
    intro i
    have hsub : IsSubnormal (B i) ⊤ := A3.subnormal_top_iff.mpr (hBsub i)
    have h1 : B i ≤ pCoreOf 3 (B i) :=
      le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer (hB3 i)
    exact h1.trans (A4.pCoreOf_le_of_subnormal 3 hsub)
  have hOn : (pCoreOf 3 (⊤ : Subgroup X)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg := le_normalizer_pCoreOf 3 (⊤ : Subgroup X) (Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hcomm : ∀ i, ∀ x ∈ K, ∀ y ∈ B i, Commute x y := by
    intro i x hx y hy
    have hyO : y ∈ pCoreOf 3 (⊤ : Subgroup X) := hBP i hy
    have hNn : (K ⊓ pCoreOf 3 (⊤ : Subgroup X)).Normal := inferInstance
    have hNbot : K ⊓ pCoreOf 3 (⊤ : Subgroup X) = ⊥ :=
      hK3 _ inf_le_left hNn (IsPGroup.to_inf_right (pCoreOf_isPGroup 3 (⊤ : Subgroup X)))
    have hcmK : ⁅x, y⁆ ∈ K := by
      have h1 : y * x⁻¹ * y⁻¹ ∈ K := hKn.conj_mem x⁻¹ (K.inv_mem hx) y
      have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact K.mul_mem hx h1
    have hcmO : ⁅x, y⁆ ∈ pCoreOf 3 (⊤ : Subgroup X) := by
      have : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact (pCoreOf 3 (⊤ : Subgroup X)).mul_mem (hOn.conj_mem y hyO x)
        ((pCoreOf 3 (⊤ : Subgroup X)).inv_mem hyO)
    have hmem : ⁅x, y⁆ ∈ K ⊓ pCoreOf 3 (⊤ : Subgroup X) := ⟨hcmK, hcmO⟩
    rw [hNbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hK3gen := closure_not_dvd_three_eq_top_of_perfect (Q := ↥K)
  have hle : Subgroup.closure {x : ↥K | ¬ 3 ∣ orderOf x} ≤ M₀.subgroupOf K := by
    rw [Subgroup.closure_le]
    intro x hx3
    have hx3' : ¬ 3 ∣ orderOf (x : X) := by
      rwa [Subgroup.orderOf_coe]
    obtain ⟨m, hm, b, hb, hxm⟩ := hx (x : X) x.2
    set f : X := (List.ofFn b).prod with hf
    have hfP : f ∈ pCoreOf 3 (⊤ : Subgroup X) :=
      Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hBP i (hb i)
    have hfk : ∃ k : ℕ, f ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 3 (⊤ : Subgroup X)) ⟨f, hfP⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hfc : Commute (x : X) f :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hcomm i (x : X) x.2 (b i) (hb i)
    have hm' : m = (x : X) * f⁻¹ := by rw [hxm]; group
    have := mem_zpowers_mul_inv_of_commute hfc hx3' hfk
    rw [← hm'] at this
    exact Subgroup.zpowers_le.mpr hm this
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥K) ∈ Subgroup.closure {x : ↥K | ¬ 3 ∣ orderOf x} :=
    hK3gen ▸ Subgroup.mem_top _
  exact hle hy'

end Abstract

end CFSG.Quasithin.QA24
