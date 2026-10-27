module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822R1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem perfect_pgroup_eq_bot_kz3 {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : IsPGroup 2 K) (hperf : ⁅K, K⁆ = K) : K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent K := IsPGroup.isNilpotent hK
  have h1 : CFSG.Quasithin.perfectCore K = ⊥ :=
    (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot K).mp inferInstance
  have h2 : CFSG.Quasithin.perfectCore K = K := CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf
  rw [h1] at h2
  exact h2.symm

theorem subsingleton_of_perfect_pgroup_kz3 {Y : Type} [Group Y] [Finite Y]
    (h2 : ∀ y : Y, ∃ n : ℕ, y ^ 2 ^ n = 1) (hperf : Group.IsPerfect Y) : Subsingleton Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : IsPGroup 2 ↥(⊤ : Subgroup Y) := fun g => by
    obtain ⟨n, hn⟩ := h2 g.1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hXperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := Group.isPerfect_def.mp hperf
  have htop : (⊤ : Subgroup Y) = ⊥ := perfect_pgroup_eq_bot_kz3 hK hXperf
  constructor
  intro a b
  have ha : a ∈ (⊤ : Subgroup Y) := Subgroup.mem_top a
  have hb : b ∈ (⊤ : Subgroup Y) := Subgroup.mem_top b
  rw [htop, Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem pCore_quot_equiv_kz3 {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] (φ : X →* Y)
    (hφ : Function.Surjective φ) (hK : ∀ x : X, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    Nonempty ((X ⧸ CFSG.pCore 2 X) ≃* (Y ⧸ CFSG.pCore 2 Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ∀ x ∈ CFSG.pCore 2 X, φ x ∈ CFSG.pCore 2 Y := by
    intro x hx
    have hle : (CFSG.pCore 2 X).map φ ≤ CFSG.pCore 2 Y := by
      apply CFSG.LieType.BorelTits.le_pCore 2
      · exact Subgroup.Normal.map CFSG.pCore_normal φ hφ
      · exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := X)) φ
    exact hle (Subgroup.mem_map_of_mem φ hx)
  have hB : ∀ x : X, φ x ∈ CFSG.pCore 2 Y → x ∈ CFSG.pCore 2 X := by
    have hle : (CFSG.pCore 2 Y).comap φ ≤ CFSG.pCore 2 X := by
      apply CFSG.LieType.BorelTits.le_pCore 2
      · exact Subgroup.Normal.comap CFSG.pCore_normal φ
      · intro g
        obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)) ⟨φ g.1, g.2⟩
        have hφj : φ (g.1 ^ 2 ^ j) = 1 := by
          have := congrArg Subtype.val hj
          simpa [map_pow] using this
        obtain ⟨k, hk⟩ := hK _ hφj
        refine ⟨j + k, Subtype.ext ?_⟩
        have h3 : g.1 ^ 2 ^ (j + k) = (g.1 ^ 2 ^ j) ^ 2 ^ k := by
          rw [pow_add, pow_mul]
        simpa [h3] using hk
    intro x hx
    exact hle hx
  let ψ : X →* Y ⧸ CFSG.pCore 2 Y := (QuotientGroup.mk' (CFSG.pCore 2 Y)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hker : ψ.ker = CFSG.pCore 2 X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact hB x ((QuotientGroup.eq_one_iff (φ x)).mp h)
    · intro h
      exact (QuotientGroup.eq_one_iff (φ x)).mpr (hA x h)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem sup_perfectCore_eq_kz3 {X : Type} [Group X] [Finite X] {M C : Subgroup X} [M.Normal]
    (hMC : M ≤ C)
    (hperf : ⁅C.map (QuotientGroup.mk' M), C.map (QuotientGroup.mk' M)⁆ = C.map (QuotientGroup.mk' M)) :
    CFSG.Quasithin.perfectCore C ⊔ M = C := by
  have h1 : (CFSG.Quasithin.perfectCore C).map (QuotientGroup.mk' M) =
      C.map (QuotientGroup.mk' M) := by
    rw [CFSG.Quasithin.map_perfectCore, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]
  refine le_antisymm (sup_le (CFSG.Quasithin.perfectCore_le C) hMC) ?_
  intro x hx
  have hmem : (QuotientGroup.mk' M) x ∈ (CFSG.Quasithin.perfectCore C).map (QuotientGroup.mk' M) := by
    rw [h1]
    exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have hx' : x = y * (y⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hyx)

theorem subnormal_top_of_sup_pCore_aux_kz3 {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X) :
    ∀ {S K : Subgroup X}, CFSG.Open.IsSubnormal S K → K = ⊤ → S ⊔ CFSG.pCore 2 X = ⊤ → S = ⊤ := by
  intro S K hSK
  induction hSK with
  | refl H => intro hH _; exact hH
  | @step H M K hHM hN hMK ih =>
    intro hK hcov
    have hMcov : M ⊔ CFSG.pCore 2 X = ⊤ :=
      eq_top_iff.mpr (by rw [← hcov]; exact sup_le_sup_right hHM _)
    have hMtop := ih hK hMcov
    subst hMtop
    have hHnorm : H.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hg : g ∈ Subgroup.normalizer (H : Set X) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : H ≤ ⊤)).mp hN (Subgroup.mem_top g)
      exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
    haveI := hHnorm
    have hfT : (⊤ : Subgroup X).map (QuotientGroup.mk' H) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective H)
    have hfO : (CFSG.pCore 2 X).map (QuotientGroup.mk' H) = ⊤ := by
      have h1 : (H ⊔ CFSG.pCore 2 X).map (QuotientGroup.mk' H) = ⊤ := by
        rw [hcov]
        exact hfT
      rw [Subgroup.map_sup] at h1
      have h2 : H.map (QuotientGroup.mk' H) = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨h, hh, rfl⟩
        rw [Subgroup.mem_bot]
        exact (QuotientGroup.eq_one_iff h).mpr hh
      rw [h2, bot_sup_eq] at h1
      exact h1
    have hP : ∀ g : X ⧸ H, ∃ n : ℕ, g ^ 2 ^ n = 1 := by
      intro g
      have hg : g ∈ (CFSG.pCore 2 X).map (QuotientGroup.mk' H) := by
        rw [hfO]
        exact Subgroup.mem_top g
      obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨o, ho⟩
      refine ⟨n, ?_⟩
      have h1 : o ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      rw [← map_pow, h1, map_one]
    have hQperf : Group.IsPerfect (X ⧸ H) := by
      rw [Group.isPerfect_def]
      have hXperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := Group.isPerfect_def.mp hperf
      have h1 := Subgroup.map_commutator (⊤ : Subgroup X) (⊤ : Subgroup X) (QuotientGroup.mk' H)
      rw [hXperf, hfT] at h1
      exact h1.symm
    have hsub := subsingleton_of_perfect_pgroup_kz3 hP hQperf
    rw [eq_top_iff]
    intro x _
    have h := Subsingleton.elim (QuotientGroup.mk x : X ⧸ H) (QuotientGroup.mk 1)
    have h2 := QuotientGroup.eq.mp h
    simpa using H.inv_mem h2

theorem subnormal_top_of_sup_pCore_kz3 {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    {S : Subgroup X} (hS : CFSG.Open.IsSubnormal S ⊤) (hcov : S ⊔ CFSG.pCore 2 X = ⊤) : S = ⊤ :=
  subnormal_top_of_sup_pCore_aux_kz3 hperf hS rfl hcov

theorem subnormal_top_eq_top_or_le_center_aux_kz3 {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y) :
    ∀ {S K : Subgroup Y}, CFSG.Open.IsSubnormal S K → K = ⊤ → S = ⊤ ∨ S ≤ Subgroup.center Y := by
  intro S K hSK
  induction hSK with
  | refl H => intro hH; exact Or.inl hH
  | @step H M K hHM hN hMK ih =>
    intro hK
    rcases ih hK with hMt | hMc
    · subst hMt
      have hHnorm : H.Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hg : g ∈ Subgroup.normalizer (H : Set Y) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : H ≤ ⊤)).mp hN (Subgroup.mem_top g)
        exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
      haveI := hHnorm
      by_cases hHt : H = ⊤
      · exact Or.inl hHt
      · exact Or.inr (res822_le_center_of_quasisimple hY hHt)
    · exact Or.inr (hHM.trans hMc)

theorem eq_bot_or_top_of_perfect_subnormal_kz3 {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y)
    {S : Subgroup Y} (hS : CFSG.Open.IsSubnormal S ⊤) (hperf : ⁅S, S⁆ = S) : S = ⊥ ∨ S = ⊤ := by
  rcases subnormal_top_eq_top_or_le_center_aux_kz3 hY hS rfl with h | h
  · exact Or.inr h
  · left
    have hc : ⁅S, S⁆ ≤ ⊥ := by
      refine Subgroup.commutator_le.mpr fun a ha b _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_center_iff.mp (h ha)) b).symm
    rw [hperf] at hc
    exact le_bot_iff.mp hc

theorem isQuasisimple_of_simple_nonab_kz3 {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hY : ¬ ∀ a b : Y, a * b = b * a) : CFSG.IsQuasisimple Y := by
  have hc : Subgroup.center Y = ⊥ := res822_center_bot_of_simple hY
  have hperf : Group.IsPerfect Y := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      apply hY
      intro a b
      have hab : ⁅a, b⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
      exact hab
    · exact h
  have e : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := MulEquiv.isSimpleGroup e
  obtain ⟨a0, b0, hab⟩ : ∃ a0 b0 : Y, a0 * b0 ≠ b0 * a0 := by
    push Not at hY
    exact hY
  refine ⟨hperf, inferInstance, e.symm a0, e.symm b0, fun h => hab ?_⟩
  have h2 := congrArg e h
  simp only [map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem isQuasisimple_of_isAlt6_kz3 {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 6)) :
    CFSG.IsQuasisimple Y := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup Y := MulEquiv.isSimpleGroup e
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    omega
  have hA6 : ¬ ∀ a b : alternatingGroup (Fin 6), a * b = b * a :=
    res822_nonabelian_of_not_prime (by rw [hcard]; norm_num)
  apply isQuasisimple_of_simple_nonab_kz3
  intro hc
  apply hA6
  intro a b
  have h1 := hc (e.symm a) (e.symm b)
  have h2 := congrArg e h1
  simpa using h2

end CFSG.Quasithin.H13
