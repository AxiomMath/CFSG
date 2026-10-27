module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.H13.C1294

theorem conj_orderOf {K : Type} [Group K] (g x : K) : orderOf (g * x * g⁻¹) = orderOf x := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have := orderOf_injective (MulAut.conj g).toMonoidHom hinj x
  simpa [MulAut.conj_apply] using this

theorem subsingleton_of_perfect_isPGroup {Q : Type} [Group Q] [Finite Q] (hp : IsPGroup 2 Q)
    (hperf : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) : Subsingleton Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent Q := hp.isNilpotent
  have hnilT : Group.IsNilpotent (⊤ : Subgroup Q) := Group.isNilpotent_top.2 hnil
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (⊤ : Subgroup Q)).1 hnilT
  have htop : ∀ m : ℕ, (⊤ : Subgroup Q).lowerCentralSeries m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Subgroup.lowerCentralSeries_succ, ih, hperf]
  rw [htop n] at hn
  constructor
  intro x y
  have hx : x = 1 := Subgroup.mem_bot.1 (hn ▸ Subgroup.mem_top x)
  have hy : y = 1 := Subgroup.mem_bot.1 (hn ▸ Subgroup.mem_top y)
  rw [hx, hy]

theorem closure_three_eq_top {K : Type} [Group K] [Finite K] (P : Subgroup K) [P.Normal]
    (hP : IsPGroup 2 P) (hsimp : IsSimpleGroup (K ⧸ P))
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (h3 : 3 ∣ Nat.card K) :
    Subgroup.closure {x : K | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤ := by
  classical
  set S : Set K := {x : K | ∃ k : ℕ, orderOf x = 3 ^ k} with hS
  set Y : Subgroup K := Subgroup.closure S with hY
  have hYn : Y.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have key : ∀ m ∈ Y, g * m * g⁻¹ ∈ Y := by
      intro m hm
      induction hm using Subgroup.closure_induction with
      | mem x hx =>
        apply Subgroup.subset_closure
        obtain ⟨k, hk⟩ := hx
        exact ⟨k, by rw [conj_orderOf]; exact hk⟩
      | one => simp
      | mul x y _ _ hx hy =>
        have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [this]; exact Y.mul_mem hx hy
      | inv x _ hx =>
        have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [this]; exact Y.inv_mem hx
    exact key n hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (hp := ⟨Nat.prime_three⟩) h3
  have hxS : x ∈ S := ⟨1, by simpa using hx⟩
  have hxY : x ∈ Y := Subgroup.subset_closure hxS
  have hxP : x ∉ P := by
    intro hxP
    obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (3 : ℕ) ∣ 2 ^ k := by
      rw [← hx]; exact orderOf_dvd_of_pow_eq_one h1
    have h3' : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    norm_num at h3'
  haveI := hsimp
  have hNbar : Y.map (QuotientGroup.mk' P) = ⊤ := by
    have hN : (Y.map (QuotientGroup.mk' P)).Normal :=
      Subgroup.Normal.map hYn _ QuotientGroup.mk_surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map (QuotientGroup.mk' P)) with h | h
    · exfalso
      have hmem : QuotientGroup.mk' P x ∈ Y.map (QuotientGroup.mk' P) :=
        Subgroup.mem_map_of_mem _ hxY
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hxP hmem
    · exact h
  have hYP : ∀ k : K, ∃ y ∈ Y, y⁻¹ * k ∈ P := by
    intro k
    have hk : QuotientGroup.mk' P k ∈ Y.map (QuotientGroup.mk' P) := by
      rw [hNbar]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 hk
    refine ⟨y, hy, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyk
    exact (QuotientGroup.eq).1 hyk
  have hQ : IsPGroup 2 (K ⧸ Y) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, hyk⟩ := hYP k
    obtain ⟨j, hj⟩ := hP ⟨y⁻¹ * k, hyk⟩
    refine ⟨j, ?_⟩
    have hpow : (y⁻¹ * k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have e : (QuotientGroup.mk (y * (y⁻¹ * k)) : K ⧸ Y) = QuotientGroup.mk (y⁻¹ * k) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul]
    have hk' : y * (y⁻¹ * k) = k := by group
    rw [hk'] at e
    rw [e, ← QuotientGroup.mk_pow, hpow, QuotientGroup.mk_one]
  have hperfQ : ⁅(⊤ : Subgroup (K ⧸ Y)), (⊤ : Subgroup (K ⧸ Y))⁆ = ⊤ := by
    have hsurj : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk_surjective
    have h1 := Subgroup.map_commutator (QuotientGroup.mk' Y) (H₁ := (⊤ : Subgroup K)) (H₂ := (⊤ : Subgroup K))
    rw [hperf, Subgroup.map_top_of_surjective _ hsurj] at h1
    exact h1.symm
  have hsub := subsingleton_of_perfect_isPGroup hQ hperfQ
  apply eq_top_iff.2
  intro k _
  exact (QuotientGroup.eq_one_iff k).1 (Subsingleton.elim _ _)

end CFSG.Quasithin.H13.C1294
