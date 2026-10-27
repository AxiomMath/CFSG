module

public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc4

section ThreeSubgroups

variable {G : Type} [Group G]

theorem three_subgroups_mod {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem mem_normalizer_commutator {P L : Subgroup G} {g : G}
    (hP : g ∈ Subgroup.normalizer (P : Set G)) (hL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((⁅P, L⁆ : Subgroup G) : Set G) := by
  rw [← A38.map_conj_eq_iff, Subgroup.map_commutator, A38.map_conj_eq_iff.mpr hP,
    A38.map_conj_eq_iff.mpr hL]

theorem commutator_centralizes {L Q E : Subgroup G} (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : ⁅E, Q⁆ = ⊥) : ⁅⁅L, E⁆, Q⁆ = ⊥ := by
  have h1 : ⁅⁅E, Q⁆, L⁆ = ⊥ := by rw [hEQ, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅Q, L⁆, E⁆ = ⊥ := by
    have hle : ⁅Q, L⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp hLQ
    refine eq_bot_iff.2 ?_
    calc ⁅⁅Q, L⁆, E⁆ ≤ ⁅Q, E⁆ := Subgroup.commutator_mono_left hle
      _ = ⁅E, Q⁆ := Subgroup.commutator_comm Q E
      _ = ⊥ := hEQ
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem pCoreOf_two_eq' {E : Type*} [Group E] (H : Subgroup E) :
    CFSG.Open.pCoreOf 2 H = (CFSG.pCore 2 H).map H.subtype := by
  rfl

end ThreeSubgroups

section Core

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_centralizes {L K : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hQne : ⁅pCoreOf 2 L, L⁆ ≠ ⊥)
    (hKL : K ≤ L) (hKn : L ≤ Subgroup.normalizer (K : Set G))
    (hKC : K ≤ Subgroup.centralizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G)) :
    K ≤ pCoreOf 2 L := by
  classical
  set Pc : Subgroup ↥L := CFSG.pCore 2 ↥L with hPc
  set NK : Subgroup ↥L := K.subgroupOf L with hNK
  have hNKn : NK.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hKn
  set π : ↥L →* ↥L ⧸ Pc := QuotientGroup.mk' Pc with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk_surjective
  have hmapn : (NK.map π).Normal := hNKn.map π hπs
  rcases hsimple.eq_bot_or_eq_top_of_normal (NK.map π) with h | h
  · have hle : NK ≤ π.ker := (Subgroup.map_eq_bot_iff _).1 h
    rw [hπ, QuotientGroup.ker_mk'] at hle
    intro k hk
    rw [pCoreOf_two_eq']
    exact ⟨⟨k, hKL hk⟩, hle (show (⟨k, hKL hk⟩ : ↥L) ∈ NK from hk), rfl⟩
  · exfalso
    have hcover : ∀ l : ↥L, ∃ k ∈ NK, k⁻¹ * l ∈ Pc := by
      intro l
      have hl : π l ∈ NK.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkl⟩ := hl
      refine ⟨k, hk, ?_⟩
      have : π (k⁻¹ * l) = 1 := by rw [map_mul, map_inv, hkl, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    set σ : ↥Pc →* ↥L ⧸ NK := (QuotientGroup.mk' NK).comp Pc.subtype with hσ
    have hσs : Function.Surjective σ := by
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk, hp⟩ := hcover l
      refine ⟨⟨k⁻¹ * l, hp⟩, ?_⟩
      show QuotientGroup.mk' NK (k⁻¹ * l) = QuotientGroup.mk' NK l
      have hk1 : QuotientGroup.mk' NK k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      rw [map_mul, map_inv, hk1, inv_one, one_mul]
    have hP2 : IsPGroup 2 ↥Pc := CFSG.pCore_isPGroup
    have hq2 : IsPGroup 2 (↥L ⧸ NK) := hP2.of_surjective σ hσs
    have : Group.IsNilpotent (↥L ⧸ NK) := hq2.isNilpotent
    have : Group.IsSolvable (↥L ⧸ NK) := inferInstance
    have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
    have : Group.IsPerfect (↥L ⧸ NK) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' NK) QuotientGroup.mk_surjective
    have hNKtop : NK = ⊤ := by
      by_cases ht : Subsingleton (↥L ⧸ NK)
      · rw [eq_top_iff]
        intro l _
        have h1 : (QuotientGroup.mk l : ↥L ⧸ NK) = QuotientGroup.mk 1 := Subsingleton.elim _ _
        exact (QuotientGroup.eq_one_iff l).1 (by simpa using h1)
      · have hnt : Nontrivial (↥L ⧸ NK) := not_subsingleton_iff_nontrivial.1 ht
        have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥L ⧸ NK)
        rw [Group.IsPerfect.commutator_eq_top] at hlt
        exact absurd hlt (lt_irrefl _)
    have hLK : L ≤ K := Subgroup.subgroupOf_eq_top.1 hNKtop
    have hLC : L ≤ Subgroup.centralizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G) := hLK.trans hKC
    have hLQ : ⁅L, ⁅pCoreOf 2 L, L⁆⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hLC
    have hQL : ⁅⁅pCoreOf 2 L, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hLQ
    have h1 : ⁅⁅L, pCoreOf 2 L⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm L (pCoreOf 2 L)]
      exact hQL
    have h3 : ⁅⁅L, L⁆, pCoreOf 2 L⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 hQL
    rw [hperf] at h3
    exact hQne (by rw [Subgroup.commutator_comm]; exact h3)

omit [Finite G] in
theorem commutator_le_Q {L I E : Subgroup G} (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hEI : E ≤ I) (hEP : ⁅L, E⁆ ≤ pCoreOf 2 L) :
    ⁅L, E⁆ ≤ ⁅pCoreOf 2 L, L⁆ := by
  have hLQ : L ≤ Subgroup.normalizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hEQ : E ≤ Subgroup.normalizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_commutator (normalizer_le_normalizer_pCoreOf 2 L (hIL (hEI hg))) (hIL (hEI hg))
  have h1 : ⁅⁅L, E⁆, L⁆ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono_left hEP
  have h2 : ⁅⁅E, L⁆, L⁆ ≤ ⁅pCoreOf 2 L, L⁆ := by
    rw [Subgroup.commutator_comm E L]
    exact h1
  have h3 := three_subgroups_mod (X := L) (Y := E) (Z := L) (N := ⁅pCoreOf 2 L, L⁆) hLQ hEQ hLQ h1 h2
  rwa [hperf] at h3

theorem commutator_le_centerOf_Q {L I E : Subgroup G} (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hQne : ⁅pCoreOf 2 L, L⁆ ≠ ⊥) (hEI : E ≤ I)
    (hEC : E ≤ Subgroup.centralizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G)) :
    ⁅L, E⁆ ≤ centerOf ⁅pCoreOf 2 L, L⁆ := by
  have hLN : ⁅L, E⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp (hEI.trans hIL)
  have hEQ : ⁅E, ⁅pCoreOf 2 L, L⁆⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hEC
  have hC : ⁅⁅L, E⁆, ⁅pCoreOf 2 L, L⁆⁆ = ⊥ :=
    commutator_centralizes (Subgroup.normalizer_commutator_ge_right _ _) hEQ
  have hKC : ⁅L, E⁆ ≤ Subgroup.centralizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
  have hKn : L ≤ Subgroup.normalizer ((⁅L, E⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left L E
  have hP : ⁅L, E⁆ ≤ pCoreOf 2 L := le_pCoreOf_of_centralizes hperf hsimple hQne hLN hKn hKC
  exact le_inf (commutator_le_Q hIL hperf hEI hP) hKC

omit [Finite G] in
theorem mem_centralizer_of_odd {L Z : Subgroup G} {d : G} (hZ2 : IsPGroup 2 ↥Z)
    (hdZ : d ∈ Subgroup.centralizer (Z : Set G)) (hcomm : ⁅L, Subgroup.zpowers d⁆ ≤ Z)
    (hodd : Odd (orderOf d)) : d ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set z : G := d * x * d⁻¹ * x⁻¹ with hz
  have hzZ : z ∈ Z := by
    have h1 : ⁅x, d⁆ ∈ Z := hcomm (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers d))
    have h2 : z = ⁅x, d⁆⁻¹ := by
      rw [hz, commutatorElement_def]
      group
    rw [h2]
    exact Z.inv_mem h1
  have hzd : z * d = d * z := Subgroup.mem_centralizer_iff.mp hdZ z hzZ
  have hdx : d * x * d⁻¹ = z * x := by
    rw [hz]
    group
  have hdz : d * z * d⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzd.symm
  clear_value z
  have hzk : ∀ k : ℕ, d * z ^ k * d⁻¹ = z ^ k := fun k => by
    rw [← conj_pow, hdz]
  have hk : ∀ k : ℕ, d ^ k * x * (d ^ k)⁻¹ = z ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc d ^ (k + 1) * x * (d ^ (k + 1))⁻¹
          = d * (d ^ k * x * (d ^ k)⁻¹) * d⁻¹ := by group
        _ = d * (z ^ k * x) * d⁻¹ := by rw [ih]
        _ = (d * z ^ k * d⁻¹) * (d * x * d⁻¹) := by group
        _ = z ^ k * (z * x) := by rw [hzk k, hdx]
        _ = z ^ (k + 1) * x := by rw [pow_succ, mul_assoc]
  have hm := hk (orderOf d)
  rw [pow_orderOf_eq_one] at hm
  have hzm : z ^ orderOf d = 1 := by
    have : z ^ orderOf d * x = 1 * x := by rw [← hm]; group
    exact mul_right_cancel this
  have hz1 : z = 1 := by
    obtain ⟨i, hi⟩ := hZ2 ⟨z, hzZ⟩
    have hi' : z ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    have h1 : orderOf z ∣ orderOf d := orderOf_dvd_of_pow_eq_one hzm
    have h2 : orderOf z ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hi'
    have hcop : Nat.Coprime (orderOf z) (orderOf d) := by
      have : Nat.Coprime (2 ^ i) (orderOf d) :=
        Nat.Coprime.pow_left i ((Nat.prime_two.coprime_iff_not_dvd).2 (by
          rcases hodd with ⟨a, ha⟩
          omega))
      exact Nat.Coprime.coprime_dvd_left h2 this
    have := Nat.Coprime.eq_one_of_dvd hcop h1
    exact orderOf_eq_one_iff.1 this
  rw [hz1, one_mul] at hdx
  have hfin : d * x = x * d := by
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [hdx]
  exact hfin.symm

end Core

end SBc4

end CFSG.Quasithin
