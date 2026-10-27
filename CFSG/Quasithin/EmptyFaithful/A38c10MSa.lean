module

public import CFSG.Quasithin.EmptyFaithful.SBd7Gen
public import CFSG.Quasithin.Background.FLc2Simple
public import CFSG.Quasithin.Background.FLcP0Ker
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.A38c10.MS

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.FLc CFSG.Quasithin
open scoped commutatorElement Pointwise

section Generic

variable {G : Type} [Group G] [Finite G]

theorem derivedSeries_SLt (n : ℕ) : derivedSeries (SLt 3) n = ⊤ := by
  have hp : Group.IsPerfect (SLt 3) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  induction n with
  | zero => exact derivedSeries_zero _
  | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def]; exact hp.commutator_eq_top

theorem exists_mem_perfectCore (P : Subgroup G) (ψ : ↥P →* SLt 3) (hψ : Function.Surjective ψ)
    (g : SLt 3) : ∃ x : ↥P, (x : G) ∈ perfectCore P ∧ ψ x = g := by
  obtain ⟨n, hn⟩ := exists_perfectCore_eq P
  have h1 : g ∈ (derivedSeries ↥P n).map ψ := by
    rw [map_derivedSeries_eq hψ n, derivedSeries_SLt]
    trivial
  obtain ⟨x, hx, rfl⟩ := h1
  refine ⟨x, ?_, rfl⟩
  rw [hn n le_rfl, derivedSeriesOf_eq_map_derivedSeries]
  exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem isPGroup_two_of_pow {H : Subgroup G} (h : ∀ x ∈ H, ∃ m : ℕ, x ^ 2 ^ m = 1) :
    IsPGroup 2 ↥H := by
  intro c
  obtain ⟨m, hm⟩ := h c c.2
  exact ⟨m, Subtype.ext (by simpa using hm)⟩

structure PsiData (P S : Subgroup G) (ψ : ↥P →* SLt 3) : Prop where
  two : IsPGroup 2 ↥S
  surj : Function.Surjective ψ
  ker : ∀ x : ↥P, ψ x = 1 → (x : G) ∈ S

variable {P S : Subgroup G} {ψ : ↥P →* SLt 3}

theorem exists_decomp (h : PsiData P S ψ) {p : G} (hp : p ∈ P) :
    ∃ k ∈ perfectCore P, ∃ n ∈ S ⊓ P, p = k * n := by
  obtain ⟨x, hxK, hx⟩ := exists_mem_perfectCore P ψ h.surj (ψ ⟨p, hp⟩)
  refine ⟨x, hxK, (x : G)⁻¹ * p, ⟨?_, P.mul_mem (P.inv_mem x.2) hp⟩, by group⟩
  have h1 : ψ (x⁻¹ * ⟨p, hp⟩) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
  simpa using h.ker _ h1

theorem le_perfectCore_sup (h : PsiData P S ψ) : P ≤ perfectCore P ⊔ S := by
  intro p hp
  obtain ⟨k, hk, n, hn, rfl⟩ := exists_decomp h hp
  exact (perfectCore P ⊔ S).mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hn.1)

theorem perfectCore_sup_eq (h : PsiData P S ψ) : perfectCore P ⊔ S = P ⊔ S :=
  le_antisymm (sup_le_sup_right (perfectCore_le P) S) (sup_le (le_perfectCore_sup h) le_sup_right)

omit [Finite G] in
theorem le_normalizer_perfectCore (P : Subgroup G) :
    P ≤ Subgroup.normalizer (perfectCore P : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le P)).mp (perfectCore_normal P)

theorem exists_pow_mem_perfectCore (h : PsiData P S ψ) :
    ∀ x ∈ P, ∃ m : ℕ, x ^ 2 ^ m ∈ perfectCore P := by
  have hprod : (P : Set G) = (perfectCore P : Set G) * ((S ⊓ P : Subgroup G) : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk', n, hn, rfl⟩ := exists_decomp h hx
      exact ⟨k, hk', n, hn, rfl⟩
    · rintro ⟨k, hk', n, hn, rfl⟩
      exact P.mul_mem (perfectCore_le P hk') hn.2
  exact SBd7.pow_mem_of_mul_pgroup (perfectCore_le P) (le_normalizer_perfectCore P) hprod
    inf_le_right (h.two.to_le inf_le_left)

theorem oTwoUpper_le_perfectCore (h : PsiData P S ψ) : oTwoUpper P ≤ perfectCore P :=
  oTwoUpper_le_of_pow_mem (exists_pow_mem_perfectCore h)

theorem mem_perfectCore_of_odd (h : PsiData P S ψ) {x : G} (hx : x ∈ P) (ho : Odd (orderOf x)) :
    x ∈ perfectCore P :=
  oTwoUpper_le_perfectCore h (mem_oTwoUpper_of_odd hx ho)

theorem psiK_surjective (h : PsiData P S ψ) :
    Function.Surjective (ψ.comp (Subgroup.inclusion (perfectCore_le P))) := by
  intro g
  obtain ⟨x, hxK, hx⟩ := exists_mem_perfectCore P ψ h.surj g
  exact ⟨⟨x, hxK⟩, hx⟩

omit [Finite G] in
theorem psiK_ker_two (h : PsiData P S ψ) (x : ↥(perfectCore P))
    (hx : (ψ.comp (Subgroup.inclusion (perfectCore_le P))) x = 1) :
    ∃ m : ℕ, (x : G) ^ 2 ^ m = 1 := by
  have hxS : (x : G) ∈ S := h.ker _ hx
  obtain ⟨m, hm⟩ := h.two ⟨x, hxS⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem ker_psiK (h : PsiData P S ψ) :
    (ψ.comp (Subgroup.inclusion (perfectCore_le P))).ker = CFSG.pCore 2 ↥(perfectCore P) := by
  set φ := ψ.comp (Subgroup.inclusion (perfectCore_le P)) with hφ
  have hsurj : Function.Surjective φ := psiK_surjective h
  apply le_antisymm
  · refine le_sSup ⟨φ.normal_ker, ?_⟩
    refine isPGroup_two_of_pow fun x hx => ?_
    obtain ⟨m, hm⟩ := psiK_ker_two h x hx
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hnorm : (CFSG.pCore 2 ↥(perfectCore P)).Normal :=
      CFSG.pCore_normal (p := 2) (G := ↥(perfectCore P))
    have hpg : IsPGroup 2 ↥(CFSG.pCore 2 ↥(perfectCore P)) :=
      CFSG.pCore_isPGroup (p := 2) (G := ↥(perfectCore P))
    have hmapnorm : ((CFSG.pCore 2 ↥(perfectCore P)).map φ).Normal :=
      Subgroup.Normal.map hnorm _ hsurj
    have := hmapnorm
    rcases (isSimpleGroup_SLt (le_refl 3)).eq_bot_or_eq_top_of_normal
      ((CFSG.pCore 2 ↥(perfectCore P)).map φ) with h1 | h1
    · have hmem : φ x ∈ (CFSG.pCore 2 ↥(perfectCore P)).map φ := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply not_isPGroup_SLt (by norm_num : 2 ≤ 3)
      intro g
      have hg : g ∈ (CFSG.pCore 2 ↥(perfectCore P)).map φ := by rw [h1]; trivial
      obtain ⟨c, hc, rfl⟩ := hg
      obtain ⟨m, hm⟩ := hpg ⟨c, hc⟩
      refine ⟨m, ?_⟩
      have h2 : c ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      rw [← map_pow, h2, map_one]

theorem perfectCore_mem_cComp_self (h : PsiData P S ψ) : perfectCore P ∈ cComp (perfectCore P) := by
  set K : Subgroup G := perfectCore P with hKdef
  set φ := ψ.comp (Subgroup.inclusion (perfectCore_le P)) with hφ
  have hperf : ⁅K, K⁆ = K := perfectCore_perfect P
  have hsurj : Function.Surjective φ := psiK_surjective h
  have hK0 : K ≠ ⊥ := by
    intro hb
    have hsub : Subsingleton ↥K := by rw [hb]; infer_instance
    have hs : Subsingleton (SLt 3) := hsurj.subsingleton
    have := (isSimpleGroup_SLt (le_refl 3)).toNontrivial
    exact not_subsingleton (SLt 3) hs
  refine ⟨hK0, hperf, IsSubnormal.refl _, fun K' hlt hne' hperf' hsub => ?_⟩
  obtain ⟨P', hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsub hlt
  have hPle : P' ≤ K := hPK.le
  have hmapn : ((P'.subgroupOf K).map φ).Normal := Subgroup.Normal.map hPn _ hsurj
  have := hmapn
  rcases (isSimpleGroup_SLt (le_refl 3)).eq_bot_or_eq_top_of_normal ((P'.subgroupOf K).map φ)
    with h1 | h1
  ·
    have hP2 : ∀ x ∈ P', ∃ m : ℕ, x ^ 2 ^ m = 1 := by
      intro x hx
      have hmem : (⟨x, hPle hx⟩ : ↥K) ∈ P'.subgroupOf K := hx
      have h2 : φ ⟨x, hPle hx⟩ ∈ (P'.subgroupOf K).map φ := ⟨_, hmem, rfl⟩
      rw [h1, Subgroup.mem_bot] at h2
      exact psiK_ker_two h ⟨x, hPle hx⟩ h2
    have hsol : Group.IsSolvable ↥K' := by
      have hp : IsPGroup 2 ↥K' := isPGroup_two_of_pow fun x hx => hP2 x (hK'P hx)
      have : Group.IsNilpotent ↥K' := hp.isNilpotent
      infer_instance
    have h2 := (isSolvable_iff_perfectCore_eq_bot K').mp hsol
    rw [perfectCore_eq_self_of_perfect hperf'] at h2
    exact hne' h2
  ·
    set N : Subgroup G := φ.ker.map K.subtype with hN
    have hNK : N ≤ K := Subgroup.map_subtype_le _
    have hN2 : ∀ x ∈ N, ∃ m : ℕ, x ^ 2 ^ m = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      exact psiK_ker_two h y hy
    have hKPN : K = P' ⊔ N := by
      refine le_antisymm (fun x hx => ?_) (sup_le hPle hNK)
      have h2 : φ ⟨x, hx⟩ ∈ (P'.subgroupOf K).map φ := by
        rw [h1]; trivial
      obtain ⟨p, hp, hpx⟩ := h2
      have hker : (p⁻¹ * ⟨x, hx⟩ : ↥K) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
      have hxN : (((p⁻¹ * ⟨x, hx⟩ : ↥K) : ↥K) : G) ∈ N := ⟨_, hker, rfl⟩
      have hpP : (p : G) ∈ P' := hp
      have : x = (p : G) * (((p⁻¹ * ⟨x, hx⟩ : ↥K) : ↥K) : G) := by
        simp
      rw [this]
      exact (P' ⊔ N).mul_mem (Subgroup.mem_sup_left hpP) (Subgroup.mem_sup_right hxN)
    have hNsol : Group.IsSolvable ↥N := by
      have hp : IsPGroup 2 ↥N := isPGroup_two_of_pow hN2
      have : Group.IsNilpotent ↥N := hp.isNilpotent
      infer_instance
    have hle := perfectCore_le_of_sup_solvable hPle hPn hKPN hNsol
    rw [perfectCore_eq_self_of_perfect hperf] at hle
    exact hPK.ne (le_antisymm hPle hle)

end Generic

end CFSG.Quasithin.A38c10.MS
