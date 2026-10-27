module

public import Mathlib
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.Open.LocalVocabulary
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.Quasithin.A94.Gen

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[instance_reducible]
private def conjActionOf (L : Subgroup G) : MulAction L G where
  smul l y := (l : G) * y * (l : G)⁻¹
  one_smul y := by
    show ((1 : L) : G) * y * ((1 : L) : G)⁻¹ = y
    simp
  mul_smul l m y := by
    show ((l * m : L) : G) * y * ((l * m : L) : G)⁻¹ =
      (l : G) * ((m : G) * y * (m : G)⁻¹) * (l : G)⁻¹
    simp [mul_assoc]

omit [Finite G] in
@[instance_reducible]
private def conjActionOnSub (K A : Subgroup G) (hK : K ≤ Subgroup.normalizer (A : Set G)) :
    MulAction K A where
  smul k a := ⟨(k : G) * a * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hK k.2) (a : G)).mp a.2⟩
  one_smul a := Subtype.ext (by
    show ((1 : K) : G) * (a : G) * ((1 : K) : G)⁻¹ = (a : G)
    simp)
  mul_smul k l a := Subtype.ext (by
    show ((k * l : K) : G) * (a : G) * ((k * l : K) : G)⁻¹ =
      (k : G) * ((l : G) * (a : G) * (l : G)⁻¹) * (k : G)⁻¹
    simp [mul_assoc])

theorem card_conjOrbit_mul_card_stab (L : Subgroup G) (z : G) :
    Nat.card {x : G // ∃ l ∈ L, x = l⁻¹ * z * l} *
        Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) =
      Nat.card L := by
  letI := conjActionOf L
  have hact : ∀ (l : L) (y : G), l • y = (l : G) * y * (l : G)⁻¹ := fun _ _ => rfl
  have horb : Nat.card {x : G // ∃ l ∈ L, x = l⁻¹ * z * l} = (MulAction.orbit L z).ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l⁻¹, L.inv_mem hl⟩, ?_⟩
      rw [hact]
      simp
    · rintro ⟨l, rfl⟩
      refine ⟨(l : G)⁻¹, L.inv_mem l.2, ?_⟩
      rw [hact]
      simp
  have hstab : Nat.card (MulAction.stabilizer L z) =
      Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    refine Nat.card_congr ((Equiv.subtypeEquivRight fun l => ?_).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun x : G => x ∈ L)
        (fun x : G => x ∈ Subgroup.centralizer ({z} : Set G))).trans
        (Equiv.subtypeEquivRight fun x => Subgroup.mem_inf.symm)))
    rw [MulAction.mem_stabilizer_iff, hact, Subgroup.mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
  have hidx := MulAction.index_stabilizer L z
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer L z)
  rw [hidx] at hcard
  rw [horb, ← hstab, mul_comm]
  exact hcard

omit [Finite G] in
private lemma mem_sylow_smul_iff {p : ℕ} {P : Sylow p G} {g y : G} :
    y ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * y * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
  · intro hs
    exact ⟨g⁻¹ * y * g, hs, by simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]⟩

theorem exists_normalizer_conj_of_normal {p : ℕ} [Fact p.Prime] (T : Sylow p G) {A B : Subgroup G}
    (hA : (A.subgroupOf (T : Subgroup G)).Normal) (hB : (B.subgroupOf (T : Subgroup G)).Normal)
    (hAT : A ≤ (T : Subgroup G)) (hBT : B ≤ (T : Subgroup G)) {g : G} (hg : conjSubgroup g B = A) :
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), conjSubgroup n B = A := by
  have hTA : (T : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hAT
  have hTB : (T : Subgroup G) ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hBT
  have hgA : ∀ t ∈ (T : Subgroup G), g * t * g⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hB' := Subgroup.mem_normalizer_iff.mp (hTB ht) (g⁻¹ * x * g)
    rw [← hg, mem_conjSubgroup, mem_conjSubgroup]
    have key : g⁻¹ * (g * t * g⁻¹ * x * (g * t * g⁻¹)⁻¹) * g = t * (g⁻¹ * x * g) * t⁻¹ := by
      group
    rw [key]
    exact hB'
  have hgTA : ((g • T : Sylow p G) : Subgroup G) ≤ Subgroup.normalizer (A : Set G) := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ (T : Subgroup G) := mem_sylow_smul_iff.mp hy
    have := hgA _ hy'
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
  set N : Subgroup G := Subgroup.normalizer (A : Set G) with hN_def
  haveI : Finite (Sylow p N) :=
    Finite.of_injective (fun P : Sylow p N => (P : Set N)) SetLike.coe_injective
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq N (T.subtype hTA) ((g • T).subtype hgTA)
  have hsm : h • T = g • T := by
    rw [Sylow.smul_subtype hTA h] at hh
    exact Sylow.subtype_injective hh
  have hmem : ∀ y : G, (h : G)⁻¹ * y * (h : G) ∈ (T : Subgroup G) ↔
      g⁻¹ * y * g ∈ (T : Subgroup G) := by
    intro y
    have hy : y ∈ (((h : G) • T : Sylow p G) : Subgroup G) ↔
        y ∈ (((g • T) : Sylow p G) : Subgroup G) := by
      rw [show ((h : G) • T : Sylow p G) = g • T from hsm]
    rw [mem_sylow_smul_iff, mem_sylow_smul_iff] at hy
    exact hy
  refine ⟨(h : G)⁻¹ * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : (h : G)⁻¹ * g * x * ((h : G)⁻¹ * g)⁻¹ = (h : G)⁻¹ * (g * x * g⁻¹) * (h : G) := by
      group
    rw [key, hmem, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  · apply Subgroup.ext
    intro x
    have hk := Subgroup.mem_normalizer_iff.mp h.2 x
    have hgA' : ∀ z : G, z ∈ A ↔ g⁻¹ * z * g ∈ B := fun z => by
      rw [← hg, mem_conjSubgroup]
    rw [mem_conjSubgroup, hk, hgA',
      show ((h : G)⁻¹ * g)⁻¹ * x * ((h : G)⁻¹ * g) = g⁻¹ * ((h : G) * x * (h : G)⁻¹) * g by group]

theorem maximal_pSubgroup_of_normalizer_le {p : ℕ} [Fact p.Prime] {P C K : Subgroup G}
    (hP : IsPGroup p P) (hPC : P ≤ C) (hPK : P ≤ K)
    (hC : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ C → P ≤ Q → Q = P)
    (hN : ∀ n ∈ K, n ∈ Subgroup.normalizer (P : Set G) → n ∈ C) :
    ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ K → P ≤ Q → Q = P := by
  intro Q hQ hQK hPQ
  by_contra hne
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hPQ
  haveI : Group.IsNilpotent Q := IsPGroup.isNilpotent hQ
  obtain ⟨y, hyN, hyP⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hPQ, Subgroup.mem_subgroupOf] at hyN
  have hyP' : (y : G) ∉ P := fun h => hyP (Subgroup.mem_subgroupOf.mpr h)
  have hPR : P ≤ Subgroup.normalizer (P : Set G) ⊓ Q := le_inf Subgroup.le_normalizer hPQ
  have hRC : Subgroup.normalizer (P : Set G) ⊓ Q ≤ C := fun r hr => hN r (hQK hr.2) hr.1
  have hRp : IsPGroup p (Subgroup.normalizer (P : Set G) ⊓ Q : Subgroup G) :=
    IsPGroup.to_le hQ inf_le_right
  have hRP := hC _ hRp hRC hPR
  have hyR : (y : G) ∈ Subgroup.normalizer (P : Set G) ⊓ Q := ⟨hyN, y.2⟩
  rw [hRP] at hyR
  exact hyP' hyR

theorem card_modEq_card_centralizer_inf {p : ℕ} [Fact p.Prime] {x : G} (hx : orderOf x = p)
    {A : Subgroup G} (hxA : x ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card A ≡ Nat.card ↥(A ⊓ Subgroup.centralizer ({x} : Set G)) [MOD p] := by
  have hK : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hxA
  letI := conjActionOnSub (Subgroup.zpowers x) A hK
  have hP : IsPGroup p ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hfixiff : ∀ a : A, a ∈ MulAction.fixedPoints (Subgroup.zpowers x) A ↔
      (a : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    intro a
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) • a = a := h _
      have h2 : (x : G) * (a : G) * (x : G)⁻¹ = (a : G) := congrArg Subtype.val h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro h m
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp m.2
      apply Subtype.ext
      show (m : G) * (a : G) * (m : G)⁻¹ = (a : G)
      rw [← hk, mul_inv_eq_iff_eq_mul]
      exact (Commute.zpow_left (show Commute x (a : G) from h.symm) k).eq
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) A) =
      Nat.card ↥(A ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_congr ((Equiv.subtypeEquivRight hfixiff).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun y : G => y ∈ A)
        (fun y : G => y ∈ Subgroup.centralizer ({x} : Set G))).trans
        (Equiv.subtypeEquivRight fun y => Subgroup.mem_inf.symm)))
  have h1 := hP.card_modEq_card_fixedPoints A
  rw [hfix] at h1
  exact h1

theorem exists_normal_of_card_mul {p m : ℕ} [Fact p.Prime] (hpm : ¬ p ∣ m)
    (hcard : Nat.card G = p * m) (hdiv : ∀ d : ℕ, d ∣ m → d % p = 1 → d = 1) :
    ∃ P : Subgroup G, P.Normal ∧ Nat.card P = p := by
  haveI : Finite (Sylow p G) :=
    Finite.of_injective (fun P : Sylow p G => (P : Set G)) SetLike.coe_injective
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  have hp1 : p.Prime := Fact.out
  have hm0 : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  have hfact : (Nat.card G).factorization p = 1 := by
    rw [hcard, Nat.factorization_mul hp1.ne_zero hm0, Finsupp.add_apply, hp1.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]
  have hcardP : Nat.card (P : Subgroup G) = p := by
    rw [Sylow.card_eq_multiplicity, hfact, pow_one]
  have hidx : (P : Subgroup G).index = m := by
    have h1 := Subgroup.index_mul_card (P : Subgroup G)
    rw [hcardP, hcard, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left hp1.pos h1
  have hdvd : Nat.card (Sylow p G) ∣ m := by
    have h1 := Sylow.card_dvd_index P
    rwa [hidx] at h1
  have hmod : Nat.card (Sylow p G) % p = 1 := by
    have h1 := card_sylow_modEq_one p G
    rw [Nat.ModEq, Nat.mod_eq_of_lt hp1.one_lt] at h1
    exact h1
  have hone : Nat.card (Sylow p G) = 1 := hdiv _ hdvd hmod
  haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hone).1
  exact ⟨(P : Subgroup G), Sylow.normal_of_subsingleton P, hcardP⟩

end CFSG.Quasithin.A94.Gen
