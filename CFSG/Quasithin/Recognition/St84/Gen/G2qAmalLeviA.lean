module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalRoots
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenRankOne

import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
import CFSG.Quasithin.H13.NQCatG2RadModel
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.Sporadic.Schreier.J4SFrattini

public noncomputable section

namespace CFSG.Quasithin.F112R.St84.G2q

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i0 i1 coords_one mem_one N1 gX rA rU rV rB rC)
open CFSG.Quasithin.H13.NQCat.G2Rad (centerOf_parabolicRadical_one)
open scoped Pointwise commutatorElement

variable {K : Type} [Field K]

local notation "A" => {x : ModGL Tag.G2 K // x ∈ adjointGroup Tag.G2 K}
local notation "X" => pinnedX Tag.G2 K

noncomputable abbrev leviASub (K : Type) [Field K] : Subgroup ↥(adjointGroup Tag.G2 K) :=
  (g2RankOne K g2ir).subgroupOf (adjointGroup Tag.G2 K)

noncomputable abbrev torusASub (K : Type) [Field K] :
    Subgroup ↥(adjointGroup Tag.G2 K) :=
  (torusGroup Tag.G2 K ⊓
    Subgroup.centralizer (rootSubgroup Tag.G2 K g2r : Set (ModGL Tag.G2 K))).subgroupOf
      (adjointGroup Tag.G2 K)

noncomputable abbrev complA (K : Type) [Field K] : Subgroup ↥(adjointGroup Tag.G2 K) :=
  leviASub K ⊔ torusASub K

private theorem i1_eq_g2ir : i1 = g2ir := Fin.ext rfl

theorem mem_torusASub_iff {h : A} :
    h ∈ torusASub K ↔ ∃ s : Kˣ, (h : ModGL Tag.G2 K) = dT s 1 := by
  constructor
  · intro hh
    rw [torusASub, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hh
    obtain ⟨hT, hC⟩ := hh
    obtain ⟨s, t, ht⟩ := mem_torusGroup_iff.1 hT
    have hgen : X g2r (1 : K) ∈ rootSubgroup Tag.G2 K g2r :=
      (mem_rootSubgroup (τ := Tag.G2) (R := K)).2 ⟨1, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 hC (X g2r 1) hgen
    have hconj : (h : ModGL Tag.G2 K) * X g2r 1 * (h : ModGL Tag.G2 K)⁻¹ = X g2r 1 := by
      rw [← hcomm]
      group
    rw [← ht] at hconj
    rw [dT_conj_r] at hconj
    simp only [Units.val_one, mul_one] at hconj
    have ht1 : t = 1 := Units.ext (pinnedX_injective Tag.G2 K g2r hconj)
    rw [ht1] at ht
    exact ⟨s, ht.symm⟩
  · rintro ⟨s, hs⟩
    rw [torusASub, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [hs]
      exact dT_mem_torusGroup s 1
    · refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := Tag.G2) (R := K)).1 hx
      rw [hs]
      have h := dT_conj_r s 1 c
      simp only [Units.val_one, mul_one] at h
      calc X g2r c * dT s 1 = (dT s 1 * X g2r c * (dT s 1)⁻¹) * dT s 1 := by
            rw [h]
            group
        _ = dT s 1 * X g2r c := by group

theorem card_torusASub [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (torusASub K) = 2 ^ f - 1 := by
  let f0 : Kˣ → ↥(torusASub K) := fun s =>
    ⟨⟨dT s 1, dT_mem_adjointGroup s 1⟩, mem_torusASub_iff.2 ⟨s, rfl⟩⟩
  have hf0 : Function.Bijective f0 := by
    constructor
    · intro a b hab
      have h := congrArg (fun x : ↥(torusASub K) => ((x : A) : ModGL Tag.G2 K)) hab
      exact (dT_injective h).1
    · rintro ⟨h, hh⟩
      obtain ⟨s, hs⟩ := mem_torusASub_iff.1 hh
      exact ⟨s, Subtype.ext (Subtype.ext hs.symm)⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f0 hf0)
  rw [← hcard, Nat.card_units, hK]

theorem mem_leviASub_of_eq_dT (l : Kˣ) {h : A}
    (hh : (h : ModGL Tag.G2 K) = dT (l⁻¹ ^ 3) (l ^ 2)) : h ∈ leviASub K := by
  rw [leviASub, Subgroup.mem_subgroupOf, hh, ← torusElt_ir_eq_dT]
  exact torusElt_mem_g2RankOne g2ir l

theorem X_r_mem_leviASub (c : K) {h : A}
    (hh : (h : ModGL Tag.G2 K) = X g2r c) : h ∈ leviASub K := by
  rw [leviASub, Subgroup.mem_subgroupOf, hh, g2RankOne_r_eq]
  exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem weylElt_mem_leviASub {h : A}
    (hh : (h : ModGL Tag.G2 K) = weylElt Tag.G2 K g2ir 1) : h ∈ leviASub K := by
  rw [leviASub, Subgroup.mem_subgroupOf, hh]
  exact weylElt_mem_g2RankOne g2ir 1

theorem mem_leviASub_iff_of_mem_torusSub [Finite K] [CharP K 2]
    {h : A}
    (hT : h ∈ torusSub Tag.G2 K) :
    h ∈ leviASub K ↔ ∃ l : Kˣ, (h : ModGL Tag.G2 K) = dT (l⁻¹ ^ 3) (l ^ 2) := by
  constructor
  · intro hL
    obtain ⟨s, t, ht⟩ := mem_torusGroup_iff.1 (Subgroup.mem_subgroupOf.1 hT)
    have hreg : (h : ModGL Tag.G2 K) ∈ g2RankOne K g2ir :=
      Subgroup.mem_subgroupOf.1 hL
    have hcXc := (commute_of_mem_g2RankOne_r hreg 1).eq
    have hst : (s : K) ^ 2 * (t : K) ^ 3 = 1 := by
      rw [← ht] at hcXc
      have hN : dT s t * g2N (0 : K) 0 0 0 0 1 = g2N 0 0 0 0 0 1 * dT s t := by
        simpa only [pinnedX_c_eq_g2N] using hcXc
      have h := (dT_comm_g2N_iff s t 0 0 0 0 0 1).1 hN
      simpa using h.2.2.2.2.2
    have hstU : s ^ 2 * t ^ 3 = 1 := Units.ext (by simpa using hst)
    obtain ⟨y, hy⟩ := (isSquare_iff_exists_sq (t : K)).1 (isSquare_of_charTwo' (t : K))
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact t.ne_zero (by simpa using hy)
    let l : Kˣ := Units.mk0 y hy0
    have hl : (l : K) = y := rfl
    have hlt : l ^ 2 = t := Units.ext (by rw [Units.val_pow_eq_pow_val, hl, hy])
    have h1 : s ^ 2 * l ^ 6 = 1 := by
      have h := hstU
      rw [← hlt] at h
      convert h using 1
      rw [← pow_mul]
    have h2 : (s * l ^ 3) * (s * l ^ 3) = 1 := by
      calc (s * l ^ 3) * (s * l ^ 3) = (s * l ^ 3) ^ 2 := by rw [sq]
        _ = s ^ 2 * (l ^ 3) ^ 2 := by rw [mul_pow]
        _ = s ^ 2 * l ^ 6 := by rw [← pow_mul]
        _ = 1 := h1
    have h3 : s * l ^ 3 = 1 := by
      apply Units.ext
      exact eq_one_of_mul_self_eq_one_two (by simpa [Units.val_mul] using congrArg Units.val h2)
    have hs : s = l⁻¹ ^ 3 := by
      calc s = (l ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
        _ = l⁻¹ ^ 3 := inv_pow l 3
    refine ⟨l, ?_⟩
    rw [← ht, hs, hlt]
  · rintro ⟨l, hl⟩
    exact mem_leviASub_of_eq_dT l hl

theorem card_torusSub_inf_leviASub [Finite K] [CharP K 2]
    {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    Nat.card ↥(torusSub Tag.G2 K ⊓ leviASub K) = 2 ^ f - 1 := by
  let f0 : Kˣ → ↥(torusSub Tag.G2 K ⊓ leviASub K) := fun l =>
    ⟨⟨dT (l⁻¹ ^ 3) (l ^ 2), dT_mem_adjointGroup _ _⟩,
      Subgroup.mem_inf.2 ⟨dT_mem_torusGroup _ _, mem_leviASub_of_eq_dT l rfl⟩⟩
  have hf0 : Function.Bijective f0 := by
    constructor
    · intro a b hab
      have h := congrArg
        (fun x : ↥(torusSub Tag.G2 K ⊓ leviASub K) =>
          (((x : A) : ModGL Tag.G2 K))) hab
      have h1 := (dT_injective h).1
      have h2 := (dT_injective h).2
      have h2' : a ^ 2 = b ^ 2 := by
        rw [← h2]
      have hcalc : (a * b⁻¹) * (a * b⁻¹) = 1 := by
        calc (a * b⁻¹) * (a * b⁻¹) = (a * b⁻¹) ^ 2 := by rw [sq]
          _ = a ^ 2 * (b⁻¹) ^ 2 := by rw [mul_pow]
          _ = a ^ 2 * (b ^ 2)⁻¹ := by rw [← inv_pow]
          _ = 1 := by rw [h2']; group
      have hm : a * b⁻¹ = 1 := by
        apply Units.ext
        exact eq_one_of_mul_self_eq_one_two (by simpa [Units.val_mul] using congrArg Units.val hcalc)
      exact mul_inv_eq_one.1 hm
    · rintro ⟨h, hh⟩
      have hT : h ∈ torusSub Tag.G2 K := (Subgroup.mem_inf.1 hh).1
      have hL : h ∈ leviASub K := (Subgroup.mem_inf.1 hh).2
      obtain ⟨l, hl⟩ := (mem_leviASub_iff_of_mem_torusSub hT).1 hL
      exact ⟨l, Subtype.ext (Subtype.ext hl.symm)⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f0 hf0)
  rw [← hcard, Nat.card_units, hK]

private theorem parabolicLevi_eq_rankOne_sup_torus :
    parabolicLevi Tag.G2 K {i1} = g2RankOne K g2ir ⊔ torusGroup Tag.G2 K := by
  rw [parabolicLevi]
  have hcl : Subgroup.closure {g : ModGL Tag.G2 K |
      ∃ j ∈ ({i1} : Set (Fin Tag.G2.rank)), ∃ c : K,
        g = xUnit Tag.G2 K j c ∨ g = yUnit Tag.G2 K j c} = g2RankOne K g2ir := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        rw [i1_eq_g2ir]
        exact xUnit_mem_g2RankOne g2ir c
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        rw [i1_eq_g2ir]
        exact yUnit_mem_g2RankOne g2ir c
    · rw [g2RankOne_r_eq]
      refine (Subgroup.closure_le _).2 ?_
      rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact Subgroup.subset_closure ⟨i1, by simp, c, Or.inl (by rw [i1_eq_g2ir, xUnit_g2ir])⟩
      · exact Subgroup.subset_closure ⟨i1, by simp, c, Or.inr (by rw [i1_eq_g2ir, yUnit_g2ir])⟩
  rw [hcl, sup_comm]

private theorem parabolicLevi_eq_rankOne_sup_torusFix [Finite K] [CharP K 2] :
    parabolicLevi Tag.G2 K {i1} = g2RankOne K g2ir ⊔
      (torusGroup Tag.G2 K ⊓
        Subgroup.centralizer (rootSubgroup Tag.G2 K g2r : Set (ModGL Tag.G2 K))) := by
  rw [parabolicLevi_eq_rankOne_sup_torus]
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    intro x hx
    obtain ⟨s, t, ht⟩ := mem_torusGroup_iff.1 hx
    obtain ⟨y, hy⟩ := (isSquare_iff_exists_sq (t : K)).1 (isSquare_of_charTwo' (t : K))
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact t.ne_zero (by simpa using hy)
    let l : Kˣ := Units.mk0 y hy0
    have hl : (l : K) = y := rfl
    have hlt : l ^ 2 = t := Units.ext (by rw [Units.val_pow_eq_pow_val, hl, hy])
    have hx_eq : x = dT (s * l ^ 3) 1 * dT (l⁻¹ ^ 3) (l ^ 2) := by
      rw [← ht, dT_mul]
      congr 2
      · group
      · simp only [one_mul]
        exact hlt.symm
    have hH : dT (s * l ^ 3) 1 ∈ torusGroup Tag.G2 K ⊓
        Subgroup.centralizer (rootSubgroup Tag.G2 K g2r : Set (ModGL Tag.G2 K)) := by
      refine Subgroup.mem_inf.2 ⟨dT_mem_torusGroup _ _, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := Tag.G2) (R := K)).1 hz
      have h := dT_conj_r (s * l ^ 3) 1 c
      simp only [Units.val_one, mul_one] at h
      calc X g2r c * dT (s * l ^ 3) 1 =
          (dT (s * l ^ 3) 1 * X g2r c * (dT (s * l ^ 3) 1)⁻¹) * dT (s * l ^ 3) 1 := by
            rw [h]
            group
        _ = dT (s * l ^ 3) 1 * X g2r c := by group
    have hL : dT (l⁻¹ ^ 3) (l ^ 2) ∈ g2RankOne K g2ir := by
      rw [← torusElt_ir_eq_dT]
      exact torusElt_mem_g2RankOne g2ir l
    have hmem : dT (s * l ^ 3) 1 * dT (l⁻¹ ^ 3) (l ^ 2) ∈
        (torusGroup Tag.G2 K ⊓
          Subgroup.centralizer (rootSubgroup Tag.G2 K g2r : Set (ModGL Tag.G2 K))) ⊔
          g2RankOne K g2ir :=
      Subgroup.mul_mem_sup hH hL
    rw [hx_eq, sup_comm]
    exact hmem
  · exact sup_le le_sup_left (inf_le_left.trans le_sup_right)

private theorem complA_eq_parabolicLevi [Finite K] [CharP K 2] :
    complA K = (parabolicLevi Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K) := by
  have hsup : (g2RankOne K g2ir ⊔
        (torusGroup Tag.G2 K ⊓
          Subgroup.centralizer (rootSubgroup Tag.G2 K g2r : Set (ModGL Tag.G2 K)))).subgroupOf
        (adjointGroup Tag.G2 K) = leviASub K ⊔ torusASub K := by
    apply Subgroup.map_injective (adjointGroup Tag.G2 K).subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (sup_le (g2RankOne_le_adjointGroup g2ir)
        (inf_le_left.trans ((torusGroup_le_borelGroup).trans borelGroup_le_adjointGroup'))),
      inf_eq_left.2 (g2RankOne_le_adjointGroup g2ir),
      inf_eq_left.2 (inf_le_left.trans ((torusGroup_le_borelGroup).trans
        borelGroup_le_adjointGroup'))]
  change leviASub K ⊔ torusASub K =
    (parabolicLevi Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K)
  rw [parabolicLevi_eq_rankOne_sup_torusFix, hsup]

private theorem complA_le_g2ParA [Finite K] [CharP K 2] : complA K ≤ g2ParA K := by
  rw [complA_eq_parabolicLevi, g2ParA, g2Index_one]
  exact Subgroup.subgroupOf_mono _ (parabolicLevi_le_parabolicSubgroup {i1})

private theorem pCoreOf_g2ParA_eq [Finite K] [CharP K 2] :
    pCoreOf 2 (g2ParA K) = (parabolicRadical Tag.G2 K {i1}).subgroupOf
      (adjointGroup Tag.G2 K) := by
  ext y
  rw [mem_pCoreOf_g2ParA_iff, Subgroup.mem_subgroupOf]

theorem exists_mul_of_mem_posUnipotentSub [Finite K] [CharP K 2] {u : A}
    (hu : u ∈ posUnipotentSub Tag.G2 K) :
    ∃ c : K, ∃ x ∈ pCoreOf 2 (g2ParA K),
      (u : ModGL Tag.G2 K) = X g2r c * (x : ModGL Tag.G2 K) := by
  rw [posUnipotentSub, Subgroup.mem_subgroupOf] at hu
  obtain ⟨c, B, C, D, E, F, hu_eq⟩ := exists_g2N_of_mem_posUnipotent hu
  have hQ : g2N (0 : K) B C D E F ∈ parabolicRadical Tag.G2 K {i1} :=
    g2N_mem_parabolicRadical_one_iff.2 rfl
  have hA : g2N (0 : K) B C D E F ∈ adjointGroup Tag.G2 K :=
    (parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}).trans posUnipotent_le_adjointGroup hQ
  refine ⟨c, ⟨⟨g2N 0 B C D E F, hA⟩, mem_pCoreOf_g2ParA_iff.2 hQ, ?_⟩⟩
  rw [← hu_eq]
  simp only [g2N, pinnedX_zero, one_mul, mul_assoc]

private theorem card_g2RankOne [Finite K] [CharP K 2] :
    Nat.card (g2RankOne K g2ir) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  obtain ⟨ρ, -, -, -, -, hrange, hinj, -,-⟩ := g2_rank_one (K := K) g2ir
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K

private theorem card_torusGroup_inf_g2RankOne [Finite K] [CharP K 2]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card ↥((torusGroup Tag.G2 K : Subgroup (ModGL Tag.G2 K)) ⊓
      g2RankOne K g2ir) = Nat.card K - 1 := by
  have hsub : (torusGroup Tag.G2 K ⊓ g2RankOne K g2ir).subgroupOf
        (adjointGroup Tag.G2 K) = torusSub Tag.G2 K ⊓ leviASub K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, torusSub, leviASub]
  have hle : (torusGroup Tag.G2 K ⊓ g2RankOne K g2ir) ≤ adjointGroup Tag.G2 K :=
    inf_le_left.trans ((torusGroup_le_borelGroup).trans borelGroup_le_adjointGroup')
  calc Nat.card ↥((torusGroup Tag.G2 K : Subgroup (ModGL Tag.G2 K)) ⊓
        g2RankOne K g2ir)
      = Nat.card ↥(torusSub Tag.G2 K ⊓ leviASub K) := by
        rw [← hsub]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv.symm
    _ = 2 ^ f - 1 := card_torusSub_inf_leviASub hK
    _ = Nat.card K - 1 := by rw [hK]

private theorem card_parabolicLevi_one [Finite K] [CharP K 2]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (parabolicLevi Tag.G2 K {i1}) =
      Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K - 1) := by
  have hq : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hnorm : torusGroup Tag.G2 K ≤
      Subgroup.normalizer (g2RankOne K g2ir : Set (ModGL Tag.G2 K)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact torus_conj_mem_g2RankOne_r hh hx
    · intro hx
      have := torus_conj_mem_g2RankOne_r (inv_mem hh) hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
  have hsup := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := torusGroup Tag.G2 K) (K := g2RankOne K g2ir) hnorm
  have hT : Nat.card (torusGroup Tag.G2 K) = (Nat.card K - 1) ^ 2 := card_torusGroup
  have hInt : Nat.card ↥((torusGroup Tag.G2 K : Subgroup (ModGL Tag.G2 K)) ⊓
      g2RankOne K g2ir) = Nat.card K - 1 :=
    card_torusGroup_inf_g2RankOne hK
  have hL : Nat.card (g2RankOne K g2ir) = Nat.card K * (Nat.card K ^ 2 - 1) :=
    card_g2RankOne
  have hsupCard : Nat.card ↥((g2RankOne K g2ir : Subgroup (ModGL Tag.G2 K)) ⊔
      torusGroup Tag.G2 K) =
      Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K - 1) := by
    apply Nat.mul_right_cancel hq
    calc Nat.card ↥((g2RankOne K g2ir : Subgroup (ModGL Tag.G2 K)) ⊔ torusGroup Tag.G2 K) *
          (Nat.card K - 1)
        = Nat.card ↥((torusGroup Tag.G2 K : Subgroup (ModGL Tag.G2 K)) ⊔
            g2RankOne K g2ir) *
            Nat.card ↥((torusGroup Tag.G2 K : Subgroup (ModGL Tag.G2 K)) ⊓
              g2RankOne K g2ir) := by
          rw [sup_comm, ← hInt]
      _ = Nat.card (torusGroup Tag.G2 K) * Nat.card (g2RankOne K g2ir) := hsup
      _ = (Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K - 1)) * (Nat.card K - 1) := by
          rw [hT, hL]
          ring
  rw [parabolicLevi_eq_rankOne_sup_torus]
  exact hsupCard

theorem complA_le_normalizer [Finite K] [CharP K 2] :
    complA K ≤ Subgroup.normalizer (pCoreOf 2 (g2ParA K) : Set A) := by
  have hKP := parabolicSubgroup_le_normalizer_parabolicRadical (τ := Tag.G2) (K := K) {i1}
  intro r hr
  have hrP : (r : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {i1} := by
    have h := complA_le_g2ParA hr
    rwa [g2ParA, g2Index_one, Subgroup.mem_subgroupOf] at h
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    rw [mem_pCoreOf_g2ParA_iff] at hq ⊢
    have h := (Subgroup.mem_normalizer_iff.1 (hKP hrP) (q : ModGL Tag.G2 K)).1 hq
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  · intro hq
    rw [mem_pCoreOf_g2ParA_iff] at hq ⊢
    have h := (Subgroup.mem_normalizer_iff.1 (hKP (inv_mem hrP))
      ((r * q * r⁻¹ : A) : ModGL Tag.G2 K)).1 hq
    have e : (q : ModGL Tag.G2 K) = (r : ModGL Tag.G2 K)⁻¹ *
        ((r * q * r⁻¹ : A) : ModGL Tag.G2 K) * (r : ModGL Tag.G2 K) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    simpa only [Subgroup.coe_inv, inv_inv] using h

theorem disjoint_pCoreOf_complA [Finite K] [CharP K 2] :
    Disjoint (pCoreOf 2 (g2ParA K)) (complA K) := by
  rw [disjoint_iff, pCoreOf_g2ParA_eq, complA_eq_parabolicLevi]
  have hinf : (parabolicRadical Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K) ⊓
        (parabolicLevi Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K) =
      (parabolicRadical Tag.G2 K {i1} ⊓ parabolicLevi Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [hinf, parabolicRadical_inf_parabolicLevi, Subgroup.bot_subgroupOf]

theorem pCoreOf_sup_complA [Finite K] [CharP K 2] :
    pCoreOf 2 (g2ParA K) ⊔ complA K = g2ParA K := by
  rw [pCoreOf_g2ParA_eq, complA_eq_parabolicLevi, g2ParA, g2Index_one]
  have hsup : (parabolicRadical Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K) ⊔
        (parabolicLevi Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K) =
      (parabolicRadical Tag.G2 K {i1} ⊔ parabolicLevi Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K) := by
    apply Subgroup.map_injective (adjointGroup Tag.G2 K).subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (sup_le ((parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}).trans
        posUnipotent_le_adjointGroup) (parabolicLevi_le_adjointGroup (τ := Tag.G2) (K := K) {i1})),
      inf_eq_left.2 ((parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}).trans
        posUnipotent_le_adjointGroup),
      inf_eq_left.2 (parabolicLevi_le_adjointGroup (τ := Tag.G2) (K := K) {i1})]
  rw [hsup, parabolicRadical_sup_parabolicLevi]

private theorem g2ParA_inf_centralizer_le [Finite K] [CharP K 2] :
    g2ParA K ⊓ Subgroup.centralizer (pCoreOf 2 (g2ParA K) : Set A) ≤
      pCoreOf 2 (g2ParA K) := by
  have hJ : ({i1} : Set (Fin Tag.G2.rank)) ≠ Set.univ := by
    intro h
    have h1 : i0 ∈ ({i1} : Set (Fin Tag.G2.rank)) := h ▸ Set.mem_univ i0
    rw [Set.mem_singleton_iff] at h1
    exact absurd h1 (by decide)
  have hSC := (Chevalley_proper_parabolic_root_radical_self_centralizing
    (τ := Tag.G2) (K := K) hJ).2
  intro r hr
  obtain ⟨hrP, hrC⟩ := Subgroup.mem_inf.1 hr
  rw [pCoreOf_g2ParA_eq] at ⊢
  have hrP' : (r : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {i1} := by
    rwa [g2ParA, g2Index_one, Subgroup.mem_subgroupOf] at hrP
  have hrC' : (r : ModGL Tag.G2 K) ∈ Subgroup.centralizer
      (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K)) := by
    rw [Subgroup.mem_centralizer_iff] at hrC ⊢
    intro x hx
    have hxA : x ∈ adjointGroup Tag.G2 K :=
      ((parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}).trans posUnipotent_le_adjointGroup) hx
    have hxQ : (⟨x, hxA⟩ : A) ∈ pCoreOf 2 (g2ParA K) :=
      mem_pCoreOf_g2ParA_iff.2 hx
    exact congrArg Subtype.val (hrC ⟨x, hxA⟩ hxQ)
  exact Subgroup.mem_subgroupOf.2 (hSC (Subgroup.mem_inf.2 ⟨hrP', hrC'⟩))

theorem eq_one_of_mem_complA_of_commute [Finite K] [CharP K 2] {r : A}
    (hr : r ∈ complA K)
    (hc : ∀ x ∈ pCoreOf 2 (g2ParA K), r * x = x * r) : r = 1 := by
  have hrP : r ∈ g2ParA K := complA_le_g2ParA hr
  have hrc : r ∈ Subgroup.centralizer (pCoreOf 2 (g2ParA K) : Set A) :=
    Subgroup.mem_centralizer_iff.2 fun x hx => (hc x hx).symm
  have hrQ : r ∈ pCoreOf 2 (g2ParA K) :=
    g2ParA_inf_centralizer_le (Subgroup.mem_inf.2 ⟨hrP, hrc⟩)
  have hbot : r ∈ (pCoreOf 2 (g2ParA K)) ⊓ complA K := Subgroup.mem_inf.2 ⟨hrQ, hr⟩
  rw [disjoint_iff.1 disjoint_pCoreOf_complA] at hbot
  simpa using hbot

theorem mem_centerOf_pCoreOf_g2ParA_iff [Finite K] [CharP K 2]
    {z : A} :
    z ∈ centerOf (pCoreOf 2 (g2ParA K)) ↔
      ∃ c : K, (z : ModGL Tag.G2 K) = pinnedX Tag.G2 K g2c c := by
  rw [pCoreOf_g2ParA_eq]
  have hcent : centerOf ((parabolicRadical Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K)) =
      (centerOf (parabolicRadical Tag.G2 K {i1})).subgroupOf (adjointGroup Tag.G2 K) := by
    ext x
    simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hxQ, hxC⟩
      refine ⟨hxQ, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro y hy
      have hA : y ∈ adjointGroup Tag.G2 K :=
        ((parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}).trans
          posUnipotent_le_adjointGroup) hy
      have hyA : (⟨y, hA⟩ : A) ∈ (parabolicRadical Tag.G2 K {i1}).subgroupOf
          (adjointGroup Tag.G2 K) := Subgroup.mem_subgroupOf.2 hy
      exact congrArg Subtype.val (hxC ⟨y, hA⟩ hyA)
    · rintro ⟨hxQ, hxC⟩
      refine ⟨hxQ, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro y hy
      exact Subtype.ext (hxC y (Subgroup.mem_subgroupOf.1 hy))
  rw [hcent, centerOf_parabolicRadical_one]
  change z ∈ (N1 : Subgroup (ModGL Tag.G2 K)).subgroupOf (adjointGroup Tag.G2 K) ↔
    ∃ c : K, (z : ModGL Tag.G2 K) = pinnedX Tag.G2 K g2c c
  rw [Subgroup.mem_subgroupOf]
  have hN1 : (N1 : Subgroup (ModGL Tag.G2 K)) = rootSubgroup Tag.G2 K g2c := rfl
  rw [hN1, mem_rootSubgroup]
  exact exists_congr fun c => eq_comm

theorem mem_leviASub_iff_commute_centerOf [Finite K] [CharP K 2]
    {h : A} (hT : h ∈ torusSub Tag.G2 K) :
    h ∈ leviASub K ↔
      ∀ z ∈ centerOf (pCoreOf 2 (g2ParA K)), h * z = z * h := by
  constructor
  · intro hL z hz
    have hL' : (h : ModGL Tag.G2 K) ∈ g2RankOne K g2ir := Subgroup.mem_subgroupOf.1 hL
    obtain ⟨c, hc⟩ := (mem_centerOf_pCoreOf_g2ParA_iff (K := K)).1 hz
    apply Subtype.ext
    show (h : ModGL Tag.G2 K) * (z : ModGL Tag.G2 K) =
      (z : ModGL Tag.G2 K) * (h : ModGL Tag.G2 K)
    rw [hc]
    exact (commute_of_mem_g2RankOne_r hL' c).eq
  · intro hc
    have hTmod : (h : ModGL Tag.G2 K) ∈ torusGroup Tag.G2 K :=
      Subgroup.mem_subgroupOf.1 hT
    obtain ⟨s, t, ht⟩ := mem_torusGroup_iff.1 hTmod
    have hz : (⟨X g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ : A) ∈
        centerOf (pCoreOf 2 (g2ParA K)) :=
      (mem_centerOf_pCoreOf_g2ParA_iff (K := K)).2 ⟨1, rfl⟩
    have hzc := congrArg (fun y : A => (y : ModGL Tag.G2 K)) (hc _ hz)
    simp only [Subgroup.coe_mul] at hzc
    rw [← ht] at hzc
    have hstU : s ^ 2 * t ^ 3 = 1 := by
      have hN : dT s t * g2N (0 : K) 0 0 0 0 1 = g2N 0 0 0 0 0 1 * dT s t := by
        simpa only [pinnedX_c_eq_g2N] using hzc
      have h := (dT_comm_g2N_iff s t 0 0 0 0 0 1).1 hN
      exact Units.ext (by simpa using h.2.2.2.2.2)
    obtain ⟨c, hcscale, hcL⟩ := torus_scale_c (K := K) hTmod
    have hc1 : c = 1 := by
      have e1 := hcscale 1
      have e2 : (h : ModGL Tag.G2 K) * X g2c 1 * (h : ModGL Tag.G2 K)⁻¹ =
          X g2c ((s : K) ^ 2 * (t : K) ^ 3 * 1) := by
        rw [← ht]
        exact dT_conj_c s t 1
      rw [e2] at e1
      have h := pinnedX_injective Tag.G2 K g2c e1
      simp only [mul_one] at h
      have hstK : (s : K) ^ 2 * (t : K) ^ 3 = 1 := by
        simpa using congrArg Units.val hstU
      rw [hstK] at h
      exact Units.ext h.symm
    rw [leviASub, Subgroup.mem_subgroupOf]
    exact hcL hc1

private theorem exists_unit_ne_one [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) : ∃ s : Kˣ, s ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, fun h => ?_⟩
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [h, orderOf_one] at hord
  have hcard : 3 ≤ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  omega

theorem commute_torusASub_iff [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {u : A}
    (hu : u ∈ posUnipotentSub Tag.G2 K) :
    (∀ h ∈ torusASub K, h * u = u * h) ↔
      ∃ c : K, (u : ModGL Tag.G2 K) = pinnedX Tag.G2 K g2r c := by
  constructor
  · intro hc
    obtain ⟨s, hs⟩ := exists_unit_ne_one hK hf
    let h0 : A := ⟨dT s 1, dT_mem_adjointGroup s 1⟩
    have hh0 : h0 ∈ torusASub K := mem_torusASub_iff.2 ⟨s, rfl⟩
    have hcomm := hc h0 hh0
    rw [posUnipotentSub, Subgroup.mem_subgroupOf] at hu
    obtain ⟨a, B, C, D, E, F, hu_eq⟩ := exists_g2N_of_mem_posUnipotent hu
    have hmod : dT s 1 * g2N a B C D E F = g2N a B C D E F * dT s 1 := by
      have := congrArg (fun y : A => (y : ModGL Tag.G2 K)) hcomm
      simpa [h0, hu_eq] using this
    obtain ⟨-, hB, hC, hD, hE, hF⟩ := (dT_comm_g2N_iff s 1 a B C D E F).1 hmod
    simp only [Units.val_one, one_pow, mul_one] at hB hC hD hE hF
    have hsv : (s : K) ≠ 1 := fun e => hs (Units.ext e)
    have hs2 : (s : K) ^ 2 ≠ 1 := fun h =>
      hsv (eq_one_of_mul_self_eq_one_two (by simpa [sq] using h))
    have hzero : ∀ {c x : K}, c ≠ 1 → c * x = x → x = 0 := by
      intro c x hc h
      have h' : (c - 1) * x = 0 := by linear_combination h
      exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hc)
    have hB0 : B = 0 := hzero hsv hB
    have hC0 : C = 0 := hzero hsv hC
    have hD0 : D = 0 := hzero hsv hD
    have hE0 : E = 0 := hzero hsv hE
    have hF0 : F = 0 := hzero hs2 hF
    refine ⟨a, ?_⟩
    rw [← hu_eq, hB0, hC0, hD0, hE0, hF0, pinnedX_r_eq_g2N]
  · rintro ⟨c, hc⟩
    intro h hh
    obtain ⟨s, hs⟩ := mem_torusASub_iff.1 hh
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    rw [hc, hs]
    have h := dT_conj_r s 1 c
    simp only [Units.val_one, mul_one] at h
    calc dT s 1 * X g2r c = (dT s 1 * X g2r c * (dT s 1)⁻¹) * dT s 1 := by
          group
      _ = X g2r c * dT s 1 := by rw [h]; group

theorem eq_one_of_mem_pCoreOf_of_commute_torusASub [Finite K] [CharP K 2]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {x : A}
    (hx : x ∈ pCoreOf 2 (g2ParA K))
    (hc : ∀ h ∈ torusASub K, h * x = x * h) : x = 1 := by
  have hxU : x ∈ posUnipotentSub Tag.G2 K := by
    rw [pCoreOf_g2ParA_eq, Subgroup.mem_subgroupOf] at hx
    rw [posUnipotentSub, Subgroup.mem_subgroupOf]
    exact (parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}) hx
  obtain ⟨c, hcX⟩ := (commute_torusASub_iff hK hf hxU).1 hc
  rw [pCoreOf_g2ParA_eq, Subgroup.mem_subgroupOf] at hx
  rw [hcX, pinnedX_r_eq_g2N, g2N_mem_parabolicRadical_one_iff] at hx
  rw [hx] at hcX
  apply Subtype.ext
  rw [hcX, pinnedX_zero]
  rfl

theorem mem_torusASub_iff_of_mem_torusSub [Finite K] [CharP K 2]
    {h : A}
    (hT : h ∈ torusSub Tag.G2 K) :
    h ∈ torusASub K ↔ ∀ u ∈ posUnipotentSub Tag.G2 K,
      h * u * h⁻¹ * u⁻¹ ∈ pCoreOf 2 (g2ParA K) := by
  obtain ⟨s, t, ht⟩ := mem_torusGroup_iff.1 (Subgroup.mem_subgroupOf.1 hT)
  constructor
  · intro hHmem u hu
    obtain ⟨c, x, hxQ, hu_eq⟩ := exists_mul_of_mem_posUnipotentSub hu
    obtain ⟨s', hs'⟩ := mem_torusASub_iff.1 hHmem
    have hxRad : (x : ModGL Tag.G2 K) ∈ parabolicRadical Tag.G2 K {i1} :=
      mem_pCoreOf_g2ParA_iff.1 hxQ
    have hP : (h : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {i1} := by
      rw [hs']
      exact (borelGroup_le_parabolicSubgroup _)
        (torusGroup_le_borelGroup (dT_mem_torusGroup s' 1))
    have hNP := parabolicSubgroup_le_normalizer_parabolicRadical
      (τ := Tag.G2) (K := K) {i1}
    have hQN : (h : ModGL Tag.G2 K) * (x : ModGL Tag.G2 K) * (h : ModGL Tag.G2 K)⁻¹ ∈
        parabolicRadical Tag.G2 K {i1} :=
      (Subgroup.mem_normalizer_iff.1 (hNP hP) (x : ModGL Tag.G2 K)).1 hxRad
    have hM : (h : ModGL Tag.G2 K) * (x : ModGL Tag.G2 K) * (h : ModGL Tag.G2 K)⁻¹ *
        (x : ModGL Tag.G2 K)⁻¹ ∈ parabolicRadical Tag.G2 K {i1} :=
      mul_mem hQN (inv_mem hxRad)
    have hXcP : X g2r c ∈ parabolicSubgroup Tag.G2 K {i1} := by
      rw [← xUnit_g2ir, ← i1_eq_g2ir]
      exact (parabolicLevi_le_parabolicSubgroup {i1})
        (xUnit_mem_parabolicLevi (Set.mem_singleton i1) c)
    have hXn := hNP hXcP
    have hHX : dT s' 1 * X g2r c = X g2r c * dT s' 1 := by
      have hconj : dT s' 1 * X g2r c * (dT s' 1)⁻¹ = X g2r c := by
        simpa using dT_conj_r s' 1 c
      calc dT s' 1 * X g2r c =
          (dT s' 1 * X g2r c * (dT s' 1)⁻¹) * dT s' 1 := by group
        _ = X g2r c * dT s' 1 := by rw [hconj]
    rw [mem_pCoreOf_g2ParA_iff]
    have e : ((h * u * h⁻¹ * u⁻¹ : A) : ModGL Tag.G2 K) =
        X g2r c * ((h : ModGL Tag.G2 K) * (x : ModGL Tag.G2 K) * (h : ModGL Tag.G2 K)⁻¹ *
          (x : ModGL Tag.G2 K)⁻¹) * (X g2r c)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hs', hu_eq]
      calc dT s' 1 * (X g2r c * (x : ModGL Tag.G2 K)) * (dT s' 1)⁻¹ *
            (X g2r c * (x : ModGL Tag.G2 K))⁻¹
          = (dT s' 1 * X g2r c) * (x : ModGL Tag.G2 K) * (dT s' 1)⁻¹ *
              ((x : ModGL Tag.G2 K)⁻¹ * (X g2r c)⁻¹) := by
            rw [mul_inv_rev]
            group
        _ = (X g2r c * dT s' 1) * (x : ModGL Tag.G2 K) * (dT s' 1)⁻¹ *
              ((x : ModGL Tag.G2 K)⁻¹ * (X g2r c)⁻¹) := by rw [hHX]
        _ = X g2r c * (dT s' 1 * (x : ModGL Tag.G2 K) * (dT s' 1)⁻¹ *
              (x : ModGL Tag.G2 K)⁻¹) * (X g2r c)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hXn _).1 hM
  · intro hcond
    let u0 : A := ⟨X g2r 1, pinnedX_mem_adjointGroup g2r 1⟩
    have hu0 : u0 ∈ posUnipotentSub Tag.G2 K := by
      rw [posUnipotentSub, Subgroup.mem_subgroupOf]
      rw [posUnipotent, rootSpan]
      refine Subgroup.mem_iSup_of_mem g2r ?_
      refine Subgroup.mem_iSup_of_mem ⟨isRoot_g2r, by decide⟩ ?_
      exact (mem_rootSubgroup (τ := Tag.G2) (R := K)).2 ⟨1, rfl⟩
    have hc := hcond u0 hu0
    rw [mem_pCoreOf_g2ParA_iff] at hc
    have hu0v : (u0 : ModGL Tag.G2 K) = X g2r 1 := rfl
    have hHX : dT s t * X g2r 1 * (dT s t)⁻¹ = X g2r t := by
      have h := dT_conj_r s t 1
      simpa only [mul_one] using h
    have e : ((h * u0 * h⁻¹ * u0⁻¹ : A) : ModGL Tag.G2 K) = X g2r ((t : K) + 1) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← ht, hu0v, hHX]
      rw [show (X g2r 1)⁻¹ = X g2r 1 by
        rw [pinnedX_neg]
        simp only [CharTwo.neg_eq]]
      rw [← pinnedX_add]
    rw [e, pinnedX_r_eq_g2N, g2N_mem_parabolicRadical_one_iff] at hc
    have ht1val : (t : K) = 1 := by
      have h := eq_neg_of_add_eq_zero_left hc
      rwa [CharTwo.neg_eq] at h
    have ht1 : t = 1 := Units.ext ht1val
    rw [ht1] at ht
    exact mem_torusASub_iff.2 ⟨s, ht.symm⟩

theorem card_complA [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    Nat.card (complA K) = 2 ^ f * (2 ^ (2 * f) - 1) * (2 ^ f - 1) := by
  have hM : Nat.card (complA K) = Nat.card (parabolicLevi Tag.G2 K {i1}) := by
    rw [complA_eq_parabolicLevi]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (parabolicLevi_le_adjointGroup (τ := Tag.G2) (K := K) {i1})).toEquiv
  rw [hM, card_parabolicLevi_one hK, hK,
    show (2 ^ f) ^ 2 = 2 ^ (2 * f) by rw [← pow_mul]; congr 1; omega]

theorem torusSub_le_complA [Finite K] [CharP K 2] :
    torusSub Tag.G2 K ≤ complA K := by
  rw [complA_eq_parabolicLevi, parabolicLevi_eq_rankOne_sup_torus]
  exact Subgroup.subgroupOf_mono _ le_sup_right

theorem mem_complA_of_mem_borelSub_of_commute [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {b : A}
    (hb : b ∈ borelSub Tag.G2 K) (hc : ∀ h ∈ torusASub K, h * b = b * h) :
    b ∈ complA K := by
  rw [borelSub, Subgroup.mem_subgroupOf] at hb
  obtain ⟨s, t, A', B, C, D, E, F, hb_eq⟩ := mem_borelGroup_iff.1 hb
  let N : ModGL Tag.G2 K := g2N A' B C D E F
  have hNpos : N ∈ posUnipotent Tag.G2 K := g2N_mem_posUnipotent A' B C D E F
  let nA : A := ⟨N, posUnipotent_le_adjointGroup hNpos⟩
  have hnU : nA ∈ posUnipotentSub Tag.G2 K := Subgroup.mem_subgroupOf.2 hNpos
  have hncomm : ∀ h ∈ torusASub K, h * nA = nA * h := by
    intro h hh
    obtain ⟨s', hs'⟩ := mem_torusASub_iff.1 hh
    have h1 : dT s' 1 * (dT s t * N) = (dT s t * N) * dT s' 1 := by
      have hcb := congrArg (fun y : A => (y : ModGL Tag.G2 K)) (hc h hh)
      simp only [Subgroup.coe_mul] at hcb
      rw [hs', hb_eq] at hcb
      exact hcb
    have hHh : dT s' 1 * dT s t = dT s t * dT s' 1 :=
      (triangular_borel_structure.{0, 0} Tag.G2 K).1 (dT s' 1)
        (dT_mem_torusGroup s' 1) (dT s t) (dT_mem_torusGroup s t)
    have hNcomm : dT s' 1 * N = N * dT s' 1 := by
      have h1' : dT s t * (dT s' 1 * N) = dT s t * (N * dT s' 1) := by
        calc dT s t * (dT s' 1 * N)
            = (dT s t * dT s' 1) * N := by group
          _ = (dT s' 1 * dT s t) * N := by rw [← hHh]
          _ = dT s' 1 * (dT s t * N) := by group
          _ = (dT s t * N) * dT s' 1 := h1
          _ = dT s t * (N * dT s' 1) := by group
      exact mul_left_cancel h1'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hs']
    simpa only [nA] using hNcomm
  have hnc := (commute_torusASub_iff hK hf hnU).1 hncomm
  obtain ⟨c, hc_eq⟩ := hnc
  have hnC : nA ∈ complA K :=
    Subgroup.mem_sup_left (X_r_mem_leviASub c hc_eq)
  let tA : A := ⟨dT s t, dT_mem_adjointGroup s t⟩
  have htT : tA ∈ torusSub Tag.G2 K := Subgroup.mem_subgroupOf.2 (dT_mem_torusGroup s t)
  have htC : tA ∈ complA K := torusSub_le_complA htT
  have hb_eqA : b = tA * nA := by
    apply Subtype.ext
    simpa only [tA, nA, Subgroup.coe_mul] using hb_eq
  rw [hb_eqA]
  exact mul_mem htC hnC

theorem torusSub_le_borelSub :
    torusSub Tag.G2 K ≤ borelSub Tag.G2 K := by
  intro x hx
  rw [torusSub, Subgroup.mem_subgroupOf] at hx
  rw [borelSub, Subgroup.mem_subgroupOf]
  exact torusGroup_le_borelGroup hx

theorem borelSub_le_g2ParB :
    borelSub Tag.G2 K ≤ g2ParB K := by
  intro x hx
  rw [borelSub, Subgroup.mem_subgroupOf] at hx
  rw [g2ParB, g2Index_zero, Subgroup.mem_subgroupOf]
  exact borelGroup_le_parabolicSubgroup _ hx

theorem posUnipotentSub_le_g2ParB :
    posUnipotentSub Tag.G2 K ≤ g2ParB K :=
  posUnipotentSub_le_borelSub.trans borelSub_le_g2ParB

theorem torusASub_le_g2ParB :
    torusASub K ≤ g2ParB K := by
  intro x hx
  rw [torusASub, Subgroup.mem_subgroupOf] at hx
  exact borelSub_le_g2ParB (torusSub_le_borelSub (Subgroup.mem_subgroupOf.mpr hx.1))

theorem torusSub_inf_leviASub_le_g2ParB :
    torusSub Tag.G2 K ⊓ leviASub K ≤ g2ParB K :=
  (inf_le_left.trans torusSub_le_borelSub).trans borelSub_le_g2ParB

theorem pCoreOf_g2ParA_le_g2ParB [Finite K] [CharP K 2] :
    pCoreOf 2 (g2ParA K) ≤ g2ParB K := by
  intro x hx
  have hxU : x ∈ posUnipotentSub Tag.G2 K := by
    rw [pCoreOf_g2ParA_eq, Subgroup.mem_subgroupOf] at hx
    exact (parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}) hx
  have hxB : x ∈ borelSub Tag.G2 K := by
    rw [borelSub, Subgroup.mem_subgroupOf]
    exact posUnipotent_le_borelGroup (Subgroup.mem_subgroupOf.1 hxU)
  rw [g2ParB, g2Index_zero, Subgroup.mem_subgroupOf]
  exact borelGroup_le_parabolicSubgroup {i0} (Subgroup.mem_subgroupOf.1 hxB)

theorem X_r_one_not_mem_pCoreOf [Finite K] [CharP K 2] {h : A}
    (hh : (h : ModGL Tag.G2 K) = pinnedX Tag.G2 K g2r 1) :
    h ∉ pCoreOf 2 (g2ParA K) := by
  intro hmem
  rw [mem_pCoreOf_g2ParA_iff] at hmem
  rw [hh, pinnedX_r_eq_g2N] at hmem
  have h10 : (1 : K) = 0 :=
    (g2N_mem_parabolicRadical_one_iff (K := K)).1 hmem
  exact one_ne_zero h10

end CFSG.Quasithin.F112R.St84.G2q

end
