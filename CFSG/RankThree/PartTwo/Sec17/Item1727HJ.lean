module

import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec14.Item14J2
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open Equiv

section A6

def a6y : Perm (Fin 6) := swap 0 1 * swap 1 2

def a6g : Perm (Fin 6) := swap 3 4 * swap 4 5

def a6k : Perm (Fin 6) := swap 0 1 * swap 3 4

theorem a6y_mem : a6y ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem a6g_mem : a6g ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem a6k_mem : a6k ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

def a6yA : alternatingGroup (Fin 6) := ⟨a6y, a6y_mem⟩

def a6gA : alternatingGroup (Fin 6) := ⟨a6g, a6g_mem⟩

def a6kA : alternatingGroup (Fin 6) := ⟨a6k, a6k_mem⟩

theorem a6y_a6g_comm : a6y * a6g = a6g * a6y := by decide

theorem a6y_pow_three : a6y ^ 3 = 1 := by decide

theorem a6g_pow_three : a6g ^ 3 = 1 := by decide

theorem a6k_a6y : a6k * a6y * a6k⁻¹ = a6y⁻¹ := by decide +kernel

theorem a6k_a6g : a6k * a6g * a6k⁻¹ = a6g⁻¹ := by decide +kernel

theorem a6y_a6g_inj : ∀ p q : Fin 3 × Fin 3,
    a6y ^ (p.1 : ℕ) * a6g ^ (p.2 : ℕ) = a6y ^ (q.1 : ℕ) * a6g ^ (q.2 : ℕ) → p = q := by
  decide +kernel

theorem a6yA_pow_three : a6yA ^ 3 = 1 := Subtype.ext (by simpa [a6yA] using a6y_pow_three)

theorem a6gA_pow_three : a6gA ^ 3 = 1 := Subtype.ext (by simpa [a6gA] using a6g_pow_three)

theorem a6yA_comm : a6yA * a6gA = a6gA * a6yA := Subtype.ext (by simpa [a6yA, a6gA] using
  a6y_a6g_comm)

def a6E : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | ∃ i j : Fin 3, x = a6yA ^ (i : ℕ) * a6gA ^ (j : ℕ)}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    have h1 : ∀ n : ℕ, a6yA ^ n = a6yA ^ (n % 3) := fun n => pow_eq_pow_mod n a6yA_pow_three
    have h2 : ∀ n : ℕ, a6gA ^ n = a6gA ^ (n % 3) := fun n => pow_eq_pow_mod n a6gA_pow_three
    refine ⟨⟨(i + i' : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(j + j' : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only
    rw [← h1, ← h2, pow_add, pow_add]
    have hc : Commute (a6gA ^ (j : ℕ)) (a6yA ^ (i' : ℕ)) :=
      ((Commute.pow_pow a6yA_comm.symm) j i')
    calc a6yA ^ (i : ℕ) * a6gA ^ (j : ℕ) * (a6yA ^ (i' : ℕ) * a6gA ^ (j' : ℕ))
        = a6yA ^ (i : ℕ) * (a6gA ^ (j : ℕ) * a6yA ^ (i' : ℕ)) * a6gA ^ (j' : ℕ) := by
          simp only [mul_assoc]
      _ = a6yA ^ (i : ℕ) * (a6yA ^ (i' : ℕ) * a6gA ^ (j : ℕ)) * a6gA ^ (j' : ℕ) := by
          rw [hc.eq]
      _ = _ := by simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    have h1 : ∀ n : ℕ, a6yA ^ n = a6yA ^ (n % 3) := fun n => pow_eq_pow_mod n a6yA_pow_three
    have h2 : ∀ n : ℕ, a6gA ^ n = a6gA ^ (n % 3) := fun n => pow_eq_pow_mod n a6gA_pow_three
    refine ⟨⟨(2 * i : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(2 * j : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only
    refine inv_eq_of_mul_eq_one_right ?_
    have hc : Commute (a6gA ^ (j : ℕ)) (a6yA ^ ((2 * i : ℕ) % 3)) :=
      ((Commute.pow_pow a6yA_comm.symm) j _)
    calc a6yA ^ (i : ℕ) * a6gA ^ (j : ℕ) *
          (a6yA ^ ((2 * i : ℕ) % 3) * a6gA ^ ((2 * j : ℕ) % 3))
        = a6yA ^ (i : ℕ) * (a6gA ^ (j : ℕ) * a6yA ^ ((2 * i : ℕ) % 3)) *
            a6gA ^ ((2 * j : ℕ) % 3) := by
          simp only [mul_assoc]
      _ = a6yA ^ (i : ℕ) * (a6yA ^ ((2 * i : ℕ) % 3) * a6gA ^ (j : ℕ)) *
            a6gA ^ ((2 * j : ℕ) % 3) := by
          rw [hc.eq]
      _ = a6yA ^ ((i : ℕ) + (2 * i : ℕ) % 3) * a6gA ^ ((j : ℕ) + (2 * j : ℕ) % 3) := by
          rw [pow_add, pow_add]; simp only [mul_assoc]
      _ = 1 := by
          rw [h1, h2]
          have hi : ((i : ℕ) + (2 * i : ℕ) % 3) % 3 = 0 := by omega
          have hj : ((j : ℕ) + (2 * j : ℕ) % 3) % 3 = 0 := by omega
          rw [hi, hj]; simp

theorem card_a6E : Nat.card a6E = 9 := by
  have hbij : Function.Bijective (fun p : Fin 3 × Fin 3 =>
      (⟨a6yA ^ (p.1 : ℕ) * a6gA ^ (p.2 : ℕ), p.1, p.2, rfl⟩ : a6E)) := by
    refine ⟨fun p q h => a6y_a6g_inj p q ?_, fun x => ?_⟩
    · have := congrArg (fun z : a6E => (z : alternatingGroup (Fin 6)).1) h
      simpa [a6yA, a6gA] using this
    · obtain ⟨x, i, j, hx⟩ := x
      exact ⟨(i, j), Subtype.ext hx.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp

theorem a6E_inv {x : alternatingGroup (Fin 6)} (hx : x ∈ a6E) : a6kA * x * a6kA⁻¹ = x⁻¹ := by
  obtain ⟨i, j, rfl⟩ := hx
  have h1 : a6kA * a6yA * a6kA⁻¹ = a6yA⁻¹ := Subtype.ext (by simpa [a6kA, a6yA] using a6k_a6y)
  have h2 : a6kA * a6gA * a6kA⁻¹ = a6gA⁻¹ := Subtype.ext (by simpa [a6kA, a6gA] using a6k_a6g)
  have hc : Commute (a6yA ^ (i : ℕ)) (a6gA ^ (j : ℕ)) := Commute.pow_pow a6yA_comm i j
  calc a6kA * (a6yA ^ (i : ℕ) * a6gA ^ (j : ℕ)) * a6kA⁻¹
      = (a6kA * a6yA * a6kA⁻¹) ^ (i : ℕ) * (a6kA * a6gA * a6kA⁻¹) ^ (j : ℕ) := by
        rw [conj_pow, conj_pow]; group
    _ = (a6yA ^ (i : ℕ) * a6gA ^ (j : ℕ))⁻¹ := by
        rw [h1, h2, inv_pow, inv_pow, mul_inv_rev]
        exact (hc.inv_inv.symm.eq ▸ rfl)

theorem a6_exists_inverts (S : Sylow 3 (alternatingGroup (Fin 6))) :
    ∃ τ : alternatingGroup (Fin 6), ∀ x ∈ (S : Subgroup (alternatingGroup (Fin 6))),
      τ * x * τ⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 a6E := IsPGroup.of_card (n := 2) (by rw [card_a6E]; norm_num)
  obtain ⟨S₀, hES₀⟩ := hEp.exists_le_sylow
  have hS₀ : (S₀ : Subgroup (alternatingGroup (Fin 6))) = a6E := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S₀.isPGroup'
    have hdvd : Nat.card (S₀ : Subgroup (alternatingGroup (Fin 6))) ∣ 360 :=
      KFacts.KS14.card_alternatingGroup_six ▸ Subgroup.card_subgroup_dvd_card _
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have h27 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      rw [← hk] at h27
      have := h27.trans hdvd
      norm_num at this
    refine (Subgroup.eq_of_le_of_card_ge hES₀ ?_).symm
    rw [hk, card_a6E]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) S₀ S
  refine ⟨g * a6kA * g⁻¹, fun x hx => ?_⟩
  rw [← hg, Sec14.coe_sylow_smul_eq_map, hS₀] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hky := a6E_inv hy
  change g * a6kA * g⁻¹ * (g * y * g⁻¹) * (g * a6kA * g⁻¹)⁻¹ = (g * y * g⁻¹)⁻¹
  calc g * a6kA * g⁻¹ * (g * y * g⁻¹) * (g * a6kA * g⁻¹)⁻¹ = g * (a6kA * y * a6kA⁻¹) * g⁻¹ := by
        group
    _ = (g * y * g⁻¹)⁻¹ := by rw [hky]; group

end A6

section HJ

theorem j2_exists_inverts_mod_center (h415 : Sec4.Item4_15) {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) :
    ∃ t : X, t ∈ Subgroup.centralizer
        (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) :
          Set X) ∧
      ∀ x ∈ (P : Subgroup X), x * (t * x * t⁻¹) ∈
        (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ3, -, -⟩ := Sec14.j2_sylow_facts h415 hX P
  have hZne : (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    norm_num at hZ3
  obtain ⟨⟨z, hzZ⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzP : z ∈ (P : Subgroup X) := (Subgroup.mem_inf.mp hzZ).1
  have hPz : (P : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2 y hy)
  have hzc : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := ⟨P, hzP, hPz⟩
  have hZz : Subgroup.zpowers z =
      (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :=
    Sec14.j2_zpowers_eq h415 hX P hz1 hzP hzc
  obtain ⟨-, -, hN, ⟨φ⟩⟩ := KFacts.KS14.j2_centralizer_quotient h415 hX hz1 hzc
  set C := Subgroup.centralizer ({z} : Set X) with hC
  set N := (Subgroup.zpowers z).subgroupOf C with hNdef
  set H : Subgroup (alternatingGroup (Fin 6)) :=
    (((P : Subgroup X).subgroupOf C).map (QuotientGroup.mk' N)).map φ.toMonoidHom with hH
  have hHp : IsPGroup 3 H := ((P.isPGroup'.comap_subtype).map _).map _
  obtain ⟨S, hHS⟩ := hHp.exists_le_sylow
  obtain ⟨τ, hτ⟩ := a6_exists_inverts S
  obtain ⟨t', ht'⟩ := QuotientGroup.mk'_surjective N (φ.symm τ)
  refine ⟨(t' : X), ?_, fun x hx => ?_⟩
  · rw [← hZz, KFacts.KS14.centralizer_zpowers_eq]
    exact t'.2
  · set x' : C := ⟨x, hPz hx⟩ with hx'
    have hx'P : x' ∈ (P : Subgroup X).subgroupOf C := hx
    have hxH : φ (QuotientGroup.mk' N x') ∈ (S : Subgroup (alternatingGroup (Fin 6))) :=
      hHS (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hx'P))
    have hinv := hτ _ hxH
    have hφt : φ (QuotientGroup.mk' N t') = τ := by rw [ht', MulEquiv.apply_symm_apply]
    have h1 : QuotientGroup.mk' N (x' * (t' * x' * t'⁻¹)) = 1 := by
      apply φ.injective
      simp only [map_mul, map_inv, map_one]
      rw [hφt, hinv, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := Subgroup.mem_subgroupOf.mp h1
    rw [hZz] at h2
    simpa using h2

end HJ

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_inverts_mod_zpowers (h415 : Sec4.Item4_15) {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {T : Subgroup G} (hT : IsSylowOf 3 T L) {d : G} (hdT : d ∈ T) (hd1 : d ≠ 1)
    (hd : IsThreeCentralIn L d) :
    ∃ t ∈ L, t * d * t⁻¹ = d ∧ ∀ x ∈ T, x * (t * x * t⁻¹) ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdL, S₀, hdS₀, hS₀d⟩ := hd
  obtain ⟨T₀, hT₀⟩ := hT
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hmemT : ∀ {x : G}, x ∈ T → ∃ hxL : x ∈ L, (⟨x, hxL⟩ : ↥L) ∈ (T₀ : Subgroup ↥L) := by
    intro x hx
    rw [← hT₀] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y.2, hy⟩
  have hd'T : d' ∈ (T₀ : Subgroup ↥L) := (hmemT hdT).2
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hinj : Set.InjOn π ((T₀ : Subgroup ↥L) : Set ↥L) :=
    injOn_mk_of_isPGroup Nat.prime_three T₀.isPGroup'
  set Tb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    T₀.mapSurjective (QuotientGroup.mk'_surjective _) with hTbdef
  have hTb : (Tb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = (T₀ : Subgroup ↥L).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hdb1, hdbc⟩ := bar_facts_of_central hd'1 ⟨S₀, hdS₀, hS₀d⟩
  have hdbT : π d' ∈ (Tb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
    hTb ▸ Subgroup.mem_map_of_mem π hd'T
  have hZb := Sec14.j2_zpowers_eq h415 hJ Tb hdb1 hdbT hdbc
  obtain ⟨tb, htbC, htbx⟩ := j2_exists_inverts_mod_center h415 hJ Tb
  have htbN : tb ∈ Subgroup.normalizer
      ((Tb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have h1 := (Subgroup.mem_inf.mp (htbx y hy)).1
    have e : tb * y * tb⁻¹ = y⁻¹ * (y * (tb * y * tb⁻¹)) := by group
    rw [e]
    exact mul_mem (inv_mem hy) h1
  have hdZ : π d' ∈ (Tb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
      Subgroup.centralizer ((Tb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := hZb ▸ Subgroup.mem_zpowers _
  rw [hTb, normalizer_map_mk_eq T₀.isPGroup'] at htbN
  obtain ⟨t, htN, rfl⟩ := htbN
  refine ⟨(t : G), t.2, ?_, fun x hx => ?_⟩
  ·
    have h1 : t * d' * t⁻¹ ∈ (T₀ : Subgroup ↥L) :=
      (Subgroup.mem_normalizer_iff.mp htN d').mp hd'T
    have h2 : π (t * d' * t⁻¹) = π d' := by
      have hc := Subgroup.mem_centralizer_iff.mp htbC (π d') hdZ
      rw [map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right]
    exact congrArg Subtype.val (hinj h1 hd'T h2)
  · obtain ⟨hxL, hxT⟩ := hmemT hx
    set x' : ↥L := ⟨x, hxL⟩ with hx'
    have hmem : x' * (t * x' * t⁻¹) ∈ (T₀ : Subgroup ↥L) :=
      mul_mem hxT ((Subgroup.mem_normalizer_iff.mp htN x').mp hxT)
    have hxb : π x' ∈ (Tb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
      hTb ▸ Subgroup.mem_map_of_mem π hxT
    have h1 := htbx _ hxb
    rw [← hZb] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : π (x' * (t * x' * t⁻¹)) = π (d' ^ k) := by
      rw [map_zpow, hk, map_mul, map_mul, map_mul, map_inv]
    have h3 := hinj hmem (zpow_mem hd'T k) h2
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h4 := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at h4
    exact h4.symm

end Lift

end CFSG.RankThree.PartTwo.Sec17
