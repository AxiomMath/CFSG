module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.Defs
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.1(b) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_mul
    (H : Subgroup G) (a b : G) :
    H.conjBy (a * b) = (H.conjBy b).conjBy a := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨h, hh, rfl⟩
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨b * h * b⁻¹, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Subgroup.conjBy, Subgroup.mem_map] at hy
    rcases hy with ⟨h, hh, rfl⟩
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨h, hh, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_eq_of_mem_normalizer
    {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (G := G) H) :
    H.conjBy g = H := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨h, hh, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg h).1 hh
  · intro hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    have hg_inv : g⁻¹ ∈ Subgroup.normalizer (G := G) H :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hg_inv x).1 hx
    · simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_mem_normalizer_of_conjBy_eq
    {H : Subgroup G} {g : G} (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (G := G) H := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      simpa [hg] using hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx'
    rcases hx' with ⟨y, hy, hyx⟩
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx
    have : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by simp [mul_assoc]
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [← hyx']
        _ = y := by simp [mul_assoc]
    simpa [this] using hy

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_normalIn_le_normalizer
    {Q L : Subgroup G} (hQnorm : section10NormalIn Q L) :
    L ≤ Subgroup.normalizer (Q : Set G) := by
  rcases hQnorm with ⟨hQL, hQnormal⟩
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    let lL : L := ⟨l, hl⟩
    let qL : L := ⟨q, hQL hq⟩
    have hq_sub : qL ∈ Q.subgroupOf L := by
      simpa [qL, Subgroup.mem_subgroupOf] using hq
    have hconj : lL * qL * lL⁻¹ ∈ Q.subgroupOf L :=
      hQnormal.conj_mem qL hq_sub lL
    change ((lL * qL * lL⁻¹ : L) : G) ∈ Q at hconj
    simpa [lL, qL, mul_assoc] using hconj
  · intro hq
    let lL : L := ⟨l, hl⟩
    let qConjL : L := ⟨l * q * l⁻¹, hQL hq⟩
    have hq_sub : qConjL ∈ Q.subgroupOf L := by
      simpa [qConjL, Subgroup.mem_subgroupOf] using hq
    have hconj : lL⁻¹ * qConjL * (lL⁻¹)⁻¹ ∈ Q.subgroupOf L :=
      hQnormal.conj_mem qConjL hq_sub lL⁻¹
    change ((lL⁻¹ * qConjL * (lL⁻¹)⁻¹ : L) : G) ∈ Q at hconj
    simpa [lL, qConjL, mul_assoc] using hconj

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_normalIn_of_le_normalizer
    {Q L : Subgroup G} (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) :
    section10NormalIn Q L := by
  refine ⟨hQL, ?_⟩
  refine { conj_mem := ?_ }
  intro q hq l
  change ((l * q * l⁻¹ : L) : G) ∈ Q
  have hlQ : (l : G) ∈ Subgroup.normalizer (Q : Set G) := hLQ l.property
  have hqQ : (q : G) ∈ Q := by
    simpa [Subgroup.mem_subgroupOf] using hq
  exact (Subgroup.mem_normalizer_iff.mp hlQ (q : G)).1 hqQ

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_one (H : Subgroup G) :
    H.conjBy 1 = H := by
  ext x
  simp [Subgroup.conjBy]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_inv (H : Subgroup G) (a : G) :
    (H.conjBy a).conjBy a⁻¹ = H := by
  rw [← section10_conjBy_mul H a⁻¹ a]
  simpa using section10_conjBy_one H

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_inv_mul_cancel
    (H : Subgroup G) {a b : G} (h : H.conjBy a = H.conjBy b) :
    H.conjBy (a⁻¹ * b) = H := by
  rw [section10_conjBy_mul]
  rw [← h]
  exact section10_conjBy_inv H a

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_mem_normalizer_conjBy_of_mem
    {H : Subgroup G} {m n : G}
    (hn : n ∈ Subgroup.normalizer (G := G) H) :
    m * n * m⁻¹ ∈ Subgroup.normalizer (G := G) (H.conjBy m) := by
  apply section10_mem_normalizer_of_conjBy_eq
  have hn_eq : H.conjBy n = H := section10_conjBy_eq_of_mem_normalizer hn
  calc
    (H.conjBy m).conjBy (m * n * m⁻¹)
        = H.conjBy ((m * n * m⁻¹) * m) :=
          (section10_conjBy_mul H (m * n * m⁻¹) m).symm
    _ = H.conjBy (m * n) := by simp [mul_assoc]
    _ = (H.conjBy n).conjBy m := section10_conjBy_mul H m n
    _ = H.conjBy m := by rw [hn_eq]

omit [Finite G] [IsMinCE G] in
set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.section10AmbientSylowSubgroup_smul
    {M : Subgroup G} {p : Nat.Primes}
    (X : Sylow p.val M) (m : M) :
    section10AmbientSylowSubgroup M (m • X) =
      (section10AmbientSylowSubgroup M X).conjBy (m : G) := by
  ext x
  constructor
  · intro hx
    change x ∈ ((m • X : Sylow p.val M) : Subgroup M).map M.subtype at hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul] at hy
    rw [Subgroup.pointwise_smul_def, Subgroup.mem_map] at hy
    rcases hy with ⟨z, hz, hzy⟩
    change (y : G) ∈ (((X : Subgroup M).map M.subtype).conjBy (m : G))
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨(z : G), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem M.subtype hz
    · simp [MulAut.conj_apply, ← hzy, mul_assoc]
  · intro hx
    change x ∈ (((X : Subgroup M).map M.subtype).conjBy (m : G)) at hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, hyx⟩
    rw [Subgroup.mem_map] at hy
    rcases hy with ⟨z, hz, hzy⟩
    change x ∈ ((m • X : Sylow p.val M) : Subgroup M).map M.subtype
    rw [Subgroup.mem_map]
    refine ⟨(m * z * m⁻¹ : M), ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
      refine ⟨z, hz, ?_⟩
      ext
      simp [MulAut.conj_apply, mul_assoc]
    · change ((m : G) * (z : G) * (m : G)⁻¹) = x
      rw [← hyx]
      rw [← hzy]
      simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10AmbientSylowSubgroup_card
    {M : Subgroup G} {p : Nat.Primes} (X : Sylow p.val M) :
    Nat.card (section10AmbientSylowSubgroup M X) = Nat.card (X : Subgroup M) := by
  simpa [section10AmbientSylowSubgroup] using
    (Subgroup.card_map_of_injective
      (K := (X : Subgroup M)) (f := M.subtype) M.subtype_injective)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_card (H : Subgroup G) (g : G) :
    Nat.card (H.conjBy g) = Nat.card H := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := H) (f := (MulAut.conj g).toMonoidHom)
      (EquivLike.injective (MulAut.conj g)))

omit [IsMinCE G] in
public theorem CFSG.section10_sigma_sylow_normalizer_le
    {M : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) (X : Sylow p.val M) :
    Subgroup.normalizer (section10AmbientSylowSubgroup M X : Set G) ≤ M := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hpσ with ⟨_hpM, P₀, hN₀⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M X P₀
  let XG : Subgroup G := section10AmbientSylowSubgroup M X
  have hP₀_eq : section10AmbientSylowSubgroup M P₀ = XG.conjBy (m : G) := by
    calc
      section10AmbientSylowSubgroup M P₀ =
          section10AmbientSylowSubgroup M (m • X) := by rw [hm]
      _ = XG.conjBy (m : G) := by
          simpa [XG] using section10AmbientSylowSubgroup_smul X m
  intro n hn
  have hn' : n ∈ Subgroup.normalizer (XG : Set G) := by
    simpa [XG] using hn
  have hconj :
      (m : G) * n * (m : G)⁻¹ ∈
        Subgroup.normalizer (XG.conjBy (m : G) : Set G) :=
    section10_mem_normalizer_conjBy_of_mem hn'
  have hconjP₀ :
      (m : G) * n * (m : G)⁻¹ ∈
        Subgroup.normalizer (section10AmbientSylowSubgroup M P₀ : Set G) := by
    simpa [hP₀_eq] using hconj
  have hconjM : (m : G) * n * (m : G)⁻¹ ∈ M := hN₀ hconjP₀
  have hn_eq : n = (m : G)⁻¹ * ((m : G) * n * (m : G)⁻¹) * (m : G) := by
    simp [mul_assoc]
  rw [hn_eq]
  exact M.mul_mem (M.mul_mem (M.inv_mem m.property) hconjM) m.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_mem_subgroupNormalizerIn
    {U : Subgroup G} {H : Set G} {x : G} :
    x ∈ subgroupNormalizerIn U H ↔ x ∈ Subgroup.normalizer H ∧ x ∈ U := by
  unfold subgroupNormalizerIn
  simp

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_subgroupNormalizerIn_le_normalizer
    (U : Subgroup G) (H : Set G) :
    subgroupNormalizerIn U H ≤ Subgroup.normalizer H := by
  intro x hx
  exact (section10_mem_subgroupNormalizerIn.mp hx).1

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_subgroupNormalizerIn_le
    (U : Subgroup G) (H : Set G) :
    subgroupNormalizerIn U H ≤ U := by
  intro x hx
  exact (section10_mem_subgroupNormalizerIn.mp hx).2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_le_subgroupNormalizerIn
    {U H : Subgroup G} (hHU : H ≤ U) :
    H ≤ subgroupNormalizerIn U (H : Set G) := by
  intro x hx
  exact section10_mem_subgroupNormalizerIn.mpr ⟨Subgroup.le_normalizer hx, hHU hx⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_subgroup_normalizer_le_of_subgroupNormalizerIn_le
    {U Q : Subgroup G} (hQU : Q ≤ U)
    (hN : subgroupNormalizerIn U (Q : Set G) ≤ Q) :
    Subgroup.normalizer ((Q.subgroupOf U : Subgroup U) : Set U) ≤
      Q.subgroupOf U := by
  intro x hx
  change (x : G) ∈ Q
  apply hN
  have hxnormQ : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyQ
      have hyK : (⟨y, hQU hyQ⟩ : U) ∈ Q.subgroupOf U := hyQ
      have hconj := (Subgroup.mem_normalizer_iff.mp hx (⟨y, hQU hyQ⟩ : U)).1 hyK
      change (((x : U) * ⟨y, hQU hyQ⟩ * (x : U)⁻¹ : U) : G) ∈ Q at hconj
      exact hconj
    · intro hyQ
      have hxinv : x⁻¹ ∈ Subgroup.normalizer ((Q.subgroupOf U : Subgroup U) : Set U) :=
        (Subgroup.normalizer ((Q.subgroupOf U : Subgroup U) : Set U)).inv_mem hx
      let z : U := ⟨(x : G) * y * (x : G)⁻¹, hQU hyQ⟩
      have hzK : z ∈ Q.subgroupOf U := hyQ
      have hconj := (Subgroup.mem_normalizer_iff.mp hxinv z).1 hzK
      change ((x⁻¹ * z * (x⁻¹)⁻¹ : U) : G) ∈ Q at hconj
      simpa [z, mul_assoc] using hconj
  exact section10_mem_subgroupNormalizerIn.mpr ⟨hxnormQ, x.property⟩

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_conjugate_mem_of_normalizer_le
    {M : Subgroup G} {p : Nat.Primes} (X : Sylow p.val M)
    (hNX : Subgroup.normalizer (section10AmbientSylowSubgroup M X : Set G) ≤ M)
    {g : G} (hXgM : (section10AmbientSylowSubgroup M X).conjBy g ≤ M) :
    g ∈ M := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let XG : Subgroup G := section10AmbientSylowSubgroup M X
  let XgSub : Subgroup M := (XG.conjBy g).subgroupOf M
  have hXg_card : Nat.card XgSub = p.val ^ (Nat.card M).factorization p.val := by
    calc
      Nat.card XgSub = Nat.card (XG.conjBy g) := by
        simpa [XgSub] using
          natCard_subgroupOf_eq (XG.conjBy g) M (by simpa [XG] using hXgM)
      _ = Nat.card XG := section10_conjBy_card XG g
      _ = Nat.card (X : Subgroup M) := by
          simpa [XG] using section10AmbientSylowSubgroup_card X
      _ = p.val ^ (Nat.card M).factorization p.val := Sylow.card_eq_multiplicity X
  let Xg : Sylow p.val M := Sylow.ofCard XgSub hXg_card
  have hXg_ambient : section10AmbientSylowSubgroup M Xg = XG.conjBy g := by
    calc
      section10AmbientSylowSubgroup M Xg = (XgSub.map M.subtype : Subgroup G) := by
        simp [section10AmbientSylowSubgroup, Xg]
      _ = (XG.conjBy g) ⊓ M := Subgroup.subgroupOf_map_subtype (XG.conjBy g) M
      _ = XG.conjBy g := inf_eq_left.mpr (by simpa [XG] using hXgM)
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M X Xg
  have hXg_eq : XG.conjBy g = XG.conjBy (m : G) := by
    calc
      XG.conjBy g = section10AmbientSylowSubgroup M Xg := hXg_ambient.symm
      _ = section10AmbientSylowSubgroup M (m • X) := by rw [hm]
      _ = XG.conjBy (m : G) := by
          simpa [XG] using section10AmbientSylowSubgroup_smul X m
  have hn : g⁻¹ * (m : G) ∈ Subgroup.normalizer (XG : Set G) := by
    apply section10_mem_normalizer_of_conjBy_eq
    exact section10_conjBy_inv_mul_cancel XG hXg_eq
  have hnM : g⁻¹ * (m : G) ∈ M := hNX (by simpa [XG] using hn)
  have hg_eq : g = (m : G) * (g⁻¹ * (m : G))⁻¹ := by
    simp
  rw [hg_eq]
  exact M.mul_mem m.property (M.inv_mem hnM)

public theorem CFSG.section10_maximal_normalizer_eq_self_of_sigma
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M) :
    Subgroup.normalizer (M : Set G) = M := by
  classical
  apply le_antisymm
  · have hnorm_proper : Subgroup.normalizer (M : Set G) ≠ ⊤ := by
      intro hnorm_top
      have hMnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
      let : IsSimpleGroup G := IsMinCE.simple
      rcases (haveI := hMnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal M) with hMbot | hMtop
      · have hpM : p.val ∣ Nat.card M := hpσ.1
        have hp_one : p.val ∣ 1 := by
          simpa [hMbot] using hpM
        exact p.property.not_dvd_one hp_one
      · exact hM.1 hMtop
    exact le_of_eq ((hM.le_iff_eq hnorm_proper).mp Subgroup.le_normalizer)
  · exact Subgroup.le_normalizer

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_inv' (H : Subgroup G) (a : G) :
    (H.conjBy a⁻¹).conjBy a = H := by
  rw [← section10_conjBy_mul H a a⁻¹]
  simpa using section10_conjBy_one H


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_le_conjBy_inv_of_conjBy_le
    {H K : Subgroup G} {a : G} (hHK : H.conjBy a ≤ K) :
    H ≤ K.conjBy a⁻¹ := by
  intro x hx
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨a * x * a⁻¹, ?_, ?_⟩
  · apply hHK
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_maximal_conjBy
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (a : G) :
    M.conjBy a ∈ section9MaximalSubgroups G := by
  have h_map : M.conjBy a = Subgroup.map ((MulAut.conj a : G ≃* G) : G →* G) M := rfl
  rw [h_map]
  exact ((MulAut.conj a : G ≃* G).mapSubgroup.isCoatom_iff M).mpr hM

omit [IsMinCE G] in
public theorem CFSG.section10_sigma_conjBy
    {M : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) (a : G) :
    p ∈ section10SigmaPrimes (M.conjBy a) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hpσ with ⟨hpM, P, hN⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  let PGa : Subgroup G := PG.conjBy a
  have hPG_le_M : PG ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPGa_le_Ma : PGa ≤ M.conjBy a := by
    intro x hx
    change x ∈ PG.conjBy a at hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hPG_le_M hy, rfl⟩
  let Psub : Subgroup (M.conjBy a) := PGa.subgroupOf (M.conjBy a)
  have hPsub_card :
      Nat.card Psub = p.val ^ (Nat.card (M.conjBy a)).factorization p.val := by
    calc
      Nat.card Psub = Nat.card PGa := by
        simpa [Psub] using natCard_subgroupOf_eq PGa (M.conjBy a) hPGa_le_Ma
      _ = Nat.card PG := by
        simpa [PGa] using section10_conjBy_card PG a
      _ = Nat.card (P : Subgroup M) := by
        simpa [PG] using section10AmbientSylowSubgroup_card P
      _ = p.val ^ (Nat.card M).factorization p.val := Sylow.card_eq_multiplicity P
      _ = p.val ^ (Nat.card (M.conjBy a)).factorization p.val := by
        rw [section10_conjBy_card M a]
  let P' : Sylow p.val (M.conjBy a) := Sylow.ofCard Psub hPsub_card
  have hP'_ambient : section10AmbientSylowSubgroup (M.conjBy a) P' = PGa := by
    calc
      section10AmbientSylowSubgroup (M.conjBy a) P' =
          (Psub.map (M.conjBy a).subtype : Subgroup G) := by
            simp [section10AmbientSylowSubgroup, P']
      _ = PGa ⊓ M.conjBy a := Subgroup.subgroupOf_map_subtype PGa (M.conjBy a)
      _ = PGa := inf_eq_left.mpr hPGa_le_Ma
  refine ⟨?_, P', ?_⟩
  · change p.val ∣ Nat.card (M.conjBy a)
    rw [section10_conjBy_card M a]
    exact hpM
  · intro n hn
    have hnPGa : n ∈ Subgroup.normalizer (PGa : Set G) := by
      simpa [hP'_ambient] using hn
    have hconj :
        a⁻¹ * n * a ∈ Subgroup.normalizer (PG : Set G) := by
      have hraw :=
        section10_mem_normalizer_conjBy_of_mem
          (G := G) (H := PGa) (m := a⁻¹) hnPGa
      simpa [PGa, section10_conjBy_inv, mul_assoc] using hraw
    have hM : a⁻¹ * n * a ∈ M := hN hconj
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨a⁻¹ * n * a, hM, by simp [mul_assoc]⟩

public theorem CFSG.section10_double_coset_of_transitive
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hXM : X ≤ M)
    (htrans :
      ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G))
        (section10ConjugatesContaining M X))
    {g : G} (hXgM : X.conjBy g ≤ M) :
    ∃ m : M, ∃ c : Subgroup.centralizer (X : Set G), g = (m : G) * (c : G) := by
  classical
  have hMnorm : Subgroup.normalizer (M : Set G) = M :=
    section10_maximal_normalizer_eq_self_of_sigma hM hpσ
  have hX_le_Mginv : X ≤ M.conjBy g⁻¹ := by
    intro x hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · apply hXgM
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · simp [mul_assoc]
  have hMginv_mem : M.conjBy g⁻¹ ∈ section10ConjugatesContaining M X :=
    ⟨g⁻¹, rfl, hX_le_Mginv⟩
  have hM_mem : M ∈ section10ConjugatesContaining M X :=
    ⟨1, (section10_conjBy_one M).symm, hXM⟩
  rcases htrans (M.conjBy g⁻¹) hMginv_mem M hM_mem with ⟨c, hc⟩
  have hcgnorm : (c : G) * g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    apply section10_mem_normalizer_of_conjBy_eq
    calc
      M.conjBy ((c : G) * g⁻¹) = (M.conjBy g⁻¹).conjBy (c : G) :=
        section10_conjBy_mul M (c : G) g⁻¹
      _ = M := hc.symm
  have hcgM : (c : G) * g⁻¹ ∈ M := by
    simpa [hMnorm] using hcgnorm
  refine ⟨⟨((c : G) * g⁻¹)⁻¹, M.inv_mem hcgM⟩, c, ?_⟩
  simp [mul_assoc]


omit [IsMinCE G] in
public theorem CFSG.section10_pPrimeCore_normalizer_le_centralizer
    {X : Subgroup G} {p : Nat.Primes} (hXp : IsPGroup p.val X) :
    (pPrimeCore p.val (Subgroup.normalizer (X : Set G))).map
        (Subgroup.normalizer (X : Set G)).subtype ≤
      Subgroup.centralizer (X : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let L : Subgroup G := Subgroup.normalizer (X : Set G)
  have hX_le_L : X ≤ L := by
    simpa [L] using (Subgroup.le_normalizer (H := X))
  let XL : Subgroup L := X.subgroupOf L
  have : XL.Normal := by
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
          (H := X) (K := L) hX_le_L).mpr (by simp [L])
  have hXLp : IsPGroup p.val XL :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := L) hX_le_L).symm
  have hcore_le_centXL :
      pPrimeCore p.val L ≤ Subgroup.centralizer (XL : Set L) :=
    pPrimeCore_le_centralizer_of_normal_pgroup (G := L) (p := p.val) XL hXLp
  intro x hx
  rw [Subgroup.mem_map] at hx
  rcases hx with ⟨n, hn, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let yL : L := ⟨y, hX_le_L hy⟩
  have hncent : n ∈ Subgroup.centralizer (XL : Set L) := hcore_le_centXL hn
  have hyXL : yL ∈ XL := by
    simpa [XL, yL, Subgroup.mem_subgroupOf] using hy
  exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hncent) yL hyXL)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_unique_overgroups_eq_of_contains_maximal'
    {H M : Subgroup G} (hH : H ∈ section9UniqueSubgroups G)
    (hM : M ∈ section9MaximalSubgroups G) (hHM : H ≤ M) :
    section9MaximalSubgroupsContaining H = {M} := by
  classical
  rcases hH with ⟨_hHproper, N, hNuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining H := ⟨hM, hHM⟩
  have hMN : M = N := by
    have hsingle : M ∈ ({N} : Set (Subgroup G)) := by
      simpa [hNuniq] using hMcont
    simpa using hsingle
  simpa [hMN] using hNuniq

omit [IsMinCE G] in
public theorem CFSG.section10_le_unique_maximal_of_le'
    {Y X M : Subgroup G} (hYX : Y ≤ X) (hXproper : X ≠ ⊤)
    (hMuniq : section9MaximalSubgroupsContaining Y = {M}) :
    X ≤ M := by
  classical
  rcases eq_top_or_exists_le_coatom X with hXtop | ⟨N, hNcoatom, hXN⟩
  · exact False.elim (hXproper hXtop)
  have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
  have hNcont : N ∈ section9MaximalSubgroupsContaining Y := ⟨hNmax, hYX.trans hXN⟩
  have hNM : N = M := by
    have hNsingle : N ∈ ({M} : Set (Subgroup G)) := by
      simpa [hMuniq] using hNcont
    simpa using hNsingle
  simpa [hNM] using hXN

public theorem CFSG.section10_normalizer_ne_top_of_ne_bot_le_maximal'
    {X M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hXM : X ≤ M) (hXne : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≠ ⊤ := by
  intro hnorm_top
  have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  let : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hXnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal X) with hXbot | hXtop
  · exact hXne hXbot
  · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXM
    exact hM.1 (top_le_iff.mp htop_le_M)

omit [IsMinCE G] in
public theorem CFSG.section10_le_maximal_of_unique_seed
    {D X M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hDunique : D ∈ section9UniqueSubgroups G) (hDM : D ≤ M)
    (hDX : D ≤ X) (hXproper : X ≠ ⊤) :
    X ≤ M := by
  have hMuniq : section9MaximalSubgroupsContaining D = {M} :=
    section10_unique_overgroups_eq_of_contains_maximal' hDunique hM hDM
  exact section10_le_unique_maximal_of_le' hDX hXproper hMuniq

public theorem CFSG.section10_normalizer_le_maximal_of_unique_seed
    {D X M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hDunique : D ∈ section9UniqueSubgroups G) (hDM : D ≤ M)
    (hDX : D ≤ Subgroup.normalizer (X : Set G))
    (hXM : X ≤ M) (hXne : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  exact section10_le_maximal_of_unique_seed hM hDunique hDM hDX
    (section10_normalizer_ne_top_of_ne_bot_le_maximal' hM hXM hXne)

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_le_of_quotient_coprime
    {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    {p : ℕ} [Fact p.Prime] (P : Sylow p H)
    (hcop : Nat.Coprime p (Nat.card (H ⧸ N))) :
    (P : Subgroup H) ≤ N := by
  classical
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let Pbar : Subgroup (H ⧸ N) := (P : Subgroup H).map q
  have hPbarp : IsPGroup p Pbar := P.isPGroup'.map q
  have hPbarcop : Nat.Coprime p (Nat.card Pbar) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card Pbar) hcop
  have hPbar_card : Nat.card Pbar = 1 := by
    rcases hPbarp.card_eq_or_dvd with hcard | hdiv
    · exact hcard
    · exact False.elim ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hPbarcop hdiv)
  have hPbar_bot : Pbar = ⊥ := Subgroup.card_eq_one.mp hPbar_card
  intro x hx
  have hxbar : q x ∈ Pbar := Subgroup.mem_map_of_mem q hx
  have hxone : q x = 1 := by
    simpa [hPbar_bot] using hxbar
  exact (QuotientGroup.eq_one_iff (N := N) (x := x)).1 hxone

omit [IsMinCE G] in
public theorem CFSG.section10_normalizer_sup_Op_p'p_eq_top_of_rank_le_two
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    (hsolv : Group.IsSolvable H) (hodd : Odd (Nat.card H))
    (hp_mem : p.val ∣ Nat.card H) (hrank : primeRank p.val H ≤ 2)
    (P : Sylow p.val H) :
    Subgroup.normalizer ((P : Subgroup H) : Set H) ⊔ Op_p'p p.val H = ⊤ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hcop : Nat.Coprime p.val (Nat.card (H ⧸ Op_p'p p.val H)) :=
    (theorem_4_18_e (G := H) (p := p.val) hsolv hodd hp_mem hrank).1
  have hP_le_Op : (P : Subgroup H) ≤ Op_p'p p.val H :=
    section10_sylow_le_of_quotient_coprime (P := P) hcop
  simpa using
    (Sylow.normalizer_sup_eq_top' (p := p.val) (N := Op_p'p p.val H) P hP_le_Op)

omit [IsMinCE G] in
public theorem CFSG.section10_pPrimeCore_le_Op_p'p
    {H : Type*} [Group H] (p : ℕ) [Fact p.Prime] :
    pPrimeCore p H ≤ Op_p'p p H := by
  let q : H →* H ⧸ pPrimeCore p H := QuotientGroup.mk' (pPrimeCore p H)
  intro x hx
  change q x ∈ pCore p (H ⧸ pPrimeCore p H)
  have hx1 : q x = 1 := (QuotientGroup.eq_one_iff (N := pPrimeCore p H) (x := x)).2 hx
  simp [hx1]

omit [IsMinCE G] in
public theorem CFSG.section10_Op_p'p_quotient_pPrimeCore_isPGroup
    {H : Type*} [Group H] [Finite H] (p : ℕ) [Fact p.Prime] :
    let L : Subgroup H := Op_p'p p H
    IsPGroup p (L ⧸ (pPrimeCore p H).subgroupOf L) := by
  let M : Subgroup H := pPrimeCore p H
  let L : Subgroup H := Op_p'p p H
  let q : H →* H ⧸ M := QuotientGroup.mk' M
  have hM_le_L : M ≤ L := by
    simpa [M, L] using section10_pPrimeCore_le_Op_p'p (H := H) p
  let N : Subgroup L := M.subgroupOf L
  let ψ0 : L →* pCore p (H ⧸ M) :=
    (q.comp L.subtype).codRestrict (pCore p (H ⧸ M)) (by
      intro x
      exact x.property)
  have hN_eq_ker : N = ψ0.ker := by
    ext x
    change (x : H) ∈ M ↔ ψ0 x = 1
    constructor
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := M) (x := (x : H))).2 hx
    · intro hx
      have hx' : q (x : H) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff (N := M) (x := (x : H))).1 hx'
  have hQker : IsPGroup p (L ⧸ ψ0.ker) := by
    let ψ : L ⧸ ψ0.ker →* pCore p (H ⧸ M) := QuotientGroup.kerLift ψ0
    have hψinj : Function.Injective ψ := QuotientGroup.kerLift_injective ψ0
    exact IsPGroup.of_injective (hG := pCore_isPGroup (p := p) (G := H ⧸ M))
      (ϕ := ψ) hψinj
  have hmap_id : N.map (MulEquiv.refl L : L →* L) = ψ0.ker := by
    simpa using hN_eq_ker
  let eQ : L ⧸ N ≃* L ⧸ ψ0.ker :=
    QuotientGroup.congr (G' := N) (H' := ψ0.ker) (e := MulEquiv.refl L) hmap_id
  have hQN : IsPGroup p (L ⧸ N) := hQker.of_equiv eQ.symm
  simpa [L, M, N] using hQN

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top
    {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    {p : ℕ} [Fact p.Prime] (hquot : IsPGroup p (H ⧸ N))
    (P : Sylow p H) :
    (P : Subgroup H) ⊔ N = ⊤ := by
  classical
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let Pbar : Sylow p (H ⧸ N) := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hPbar_top : (Pbar : Subgroup (H ⧸ N)) = ⊤ := by
    have hidx_pow :
        ∃ n : ℕ, (Pbar : Subgroup (H ⧸ N)).index = p ^ n :=
      hquot.index (Pbar : Subgroup (H ⧸ N))
    have hidx_not : ¬ p ∣ (Pbar : Subgroup (H ⧸ N)).index :=
      Pbar.not_dvd_index
    rcases hidx_pow with ⟨n, hn⟩
    have hidx_one : (Pbar : Subgroup (H ⧸ N)).index = 1 := by
      rw [hn]
      cases n with
      | zero =>
          simp
      | succ n =>
          exfalso
          apply hidx_not
          rw [hn]
          simp [pow_succ, mul_comm]
    exact (Subgroup.index_eq_one (H := (Pbar : Subgroup (H ⧸ N)))).1 hidx_one
  apply le_antisymm le_top
  intro x _hx
  have hxbar : q x ∈ (P.map q : Subgroup (H ⧸ N)) := by
    have hxbar' : q x ∈ (Pbar : Subgroup (H ⧸ N)) := by
      simp [hPbar_top]
    simpa [Pbar] using hxbar'
  rcases Subgroup.mem_map.mp hxbar with ⟨y, hyP, hyq⟩
  have hyxN : y⁻¹ * x ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N) (x := y⁻¹ * x)).1
    calc
      q (y⁻¹ * x) = (q y)⁻¹ * q x := by simp [q]
      _ = 1 := by rw [hyq]; simp
  have hx_eq : x = y * (y⁻¹ * x) := by simp
  rw [hx_eq]
  exact Subgroup.mul_mem_sup hyP hyxN

omit [IsMinCE G] in
public theorem CFSG.section10_Op_p'p_le_sylow_sup_pPrimeCore
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    (P : Sylow p.val H) (hP_le_Op : (P : Subgroup H) ≤ Op_p'p p.val H) :
    Op_p'p p.val H ≤ (P : Subgroup H) ⊔ pPrimeCore p.val H := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let L : Subgroup H := Op_p'p p.val H
  let M : Subgroup H := pPrimeCore p.val H
  have hM_le_L : M ≤ L := by
    simpa [M, L] using section10_pPrimeCore_le_Op_p'p (H := H) p.val
  let N : Subgroup L := M.subgroupOf L
  have : N.Normal := (inferInstance : M.Normal).subgroupOf L
  let PL : Sylow p.val L := P.subtype (by simpa [L] using hP_le_Op)
  have hquotL : IsPGroup p.val (L ⧸ N) := by
    simpa [L, M, N] using section10_Op_p'p_quotient_pPrimeCore_isPGroup (H := H) p.val
  have hsupL : (PL : Subgroup L) ⊔ N = ⊤ :=
    section10_sylow_sup_normal_of_p_quotient_eq_top (N := N) hquotL PL
  intro x hx
  let xL : L := ⟨x, hx⟩
  have hxLsup : xL ∈ (PL : Subgroup L) ⊔ N := by
    simp [hsupL]
  rcases (Subgroup.mem_sup_of_normal_right (s := (PL : Subgroup L)) (t := N)).1 hxLsup with
    ⟨y, hyP, z, hzM, hyz⟩
  have hyG : (y : H) ∈ (P : Subgroup H) := by
    change (y : H) ∈ (P : Subgroup H) at hyP
    exact hyP
  have hzG : (z : H) ∈ M := by
    simpa [N, M, Subgroup.mem_subgroupOf] using hzM
  have hmul : (y : H) * (z : H) = x := congrArg Subtype.val hyz
  rw [← hmul]
  exact Subgroup.mul_mem_sup hyG (by simpa [M] using hzG)

omit [IsMinCE G] in
public theorem CFSG.section10_normalizer_sup_pPrimeCore_eq_top_of_rank_le_two
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    (hsolv : Group.IsSolvable H) (hodd : Odd (Nat.card H))
    (hp_mem : p.val ∣ Nat.card H) (hrank : primeRank p.val H ≤ 2)
    (P : Sylow p.val H) :
    Subgroup.normalizer ((P : Subgroup H) : Set H) ⊔ pPrimeCore p.val H = ⊤ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hcop : Nat.Coprime p.val (Nat.card (H ⧸ Op_p'p p.val H)) :=
    (theorem_4_18_e (G := H) (p := p.val) hsolv hodd hp_mem hrank).1
  have hP_le_Op : (P : Subgroup H) ≤ Op_p'p p.val H :=
    section10_sylow_le_of_quotient_coprime (P := P) hcop
  have hFrattini :
      Subgroup.normalizer ((P : Subgroup H) : Set H) ⊔ Op_p'p p.val H = ⊤ :=
    section10_normalizer_sup_Op_p'p_eq_top_of_rank_le_two hsolv hodd hp_mem hrank P
  have hOp_le_PM :
      Op_p'p p.val H ≤ (P : Subgroup H) ⊔ pPrimeCore p.val H :=
    section10_Op_p'p_le_sylow_sup_pPrimeCore P hP_le_Op
  have hP_le_norm :
      (P : Subgroup H) ≤ Subgroup.normalizer ((P : Subgroup H) : Set H) :=
    Subgroup.le_normalizer
  have hPM_le_normM :
      (P : Subgroup H) ⊔ pPrimeCore p.val H ≤
        Subgroup.normalizer ((P : Subgroup H) : Set H) ⊔ pPrimeCore p.val H :=
    sup_le_sup hP_le_norm le_rfl
  apply le_antisymm le_top
  rw [← hFrattini]
  exact sup_le le_sup_left (hOp_le_PM.trans hPM_le_normM)

omit [IsMinCE G] in
public theorem CFSG.section10_normalizer_pPrimeCore_factor_of_rank_le_two
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    (hsolv : Group.IsSolvable H) (hodd : Odd (Nat.card H))
    (hp_mem : p.val ∣ Nat.card H) (hrank : primeRank p.val H ≤ 2)
    (P : Sylow p.val H) (t : H) :
    ∃ u : Subgroup.normalizer ((P : Subgroup H) : Set H),
      ∃ v : pPrimeCore p.val H, t = (u : H) * (v : H) := by
  classical
  have htop :
      Subgroup.normalizer ((P : Subgroup H) : Set H) ⊔ pPrimeCore p.val H = ⊤ :=
    section10_normalizer_sup_pPrimeCore_eq_top_of_rank_le_two hsolv hodd hp_mem hrank P
  have ht :
      t ∈ Subgroup.normalizer ((P : Subgroup H) : Set H) ⊔ pPrimeCore p.val H := by
    rw [htop]
    exact Subgroup.mem_top t
  rcases (Subgroup.mem_sup_of_normal_right
      (s := Subgroup.normalizer ((P : Subgroup H) : Set H))
      (t := pPrimeCore p.val H)).1 ht with
    ⟨u, hu, v, hv, huv⟩
  exact ⟨⟨u, hu⟩, ⟨v, hv⟩, huv.symm⟩

omit [IsMinCE G] in
public theorem CFSG.section10_rank_le_two_factor_in_ambient_normalizer_centralizer
    {X : Subgroup G} {p : Nat.Primes} (hXp : IsPGroup p.val X)
    (hsolv : Group.IsSolvable (Subgroup.normalizer (X : Set G)))
    (hodd : Odd (Nat.card (Subgroup.normalizer (X : Set G))))
    (hp_mem : p.val ∣ Nat.card (Subgroup.normalizer (X : Set G)))
    (hrank : primeRank p.val (Subgroup.normalizer (X : Set G)) ≤ 2)
    (P : Sylow p.val (Subgroup.normalizer (X : Set G)))
    (t : Subgroup.normalizer (X : Set G)) :
    ∃ u : Subgroup.normalizer
        ((section10AmbientSylowSubgroup (Subgroup.normalizer (X : Set G)) P) : Set G),
      ∃ v : Subgroup.centralizer (X : Set G), (t : G) = (u : G) * (v : G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let L : Subgroup G := Subgroup.normalizer (X : Set G)
  let PG : Subgroup G := section10AmbientSylowSubgroup L P
  rcases section10_normalizer_pPrimeCore_factor_of_rank_le_two
      (H := L) hsolv hodd hp_mem hrank P t with
    ⟨uL, vL, ht⟩
  have huG : (uL : G) ∈ Subgroup.normalizer (PG : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      change y ∈ ((P : Subgroup L).map L.subtype : Subgroup G) at hy
      rw [Subgroup.mem_map] at hy
      rcases hy with ⟨yL, hyP, rfl⟩
      have huNorm := uL.property yL
      change ((uL : G) * (yL : G) * (uL : G)⁻¹) ∈ PG
      exact Subgroup.mem_map_of_mem L.subtype (huNorm.1 hyP)
    · intro hy
      have hyL : y ∈ L := by
        have hu_mem_L : (uL : G) ∈ L := (uL : L).property
        have hu_inv_mem_L : (uL : G)⁻¹ ∈ L := L.inv_mem hu_mem_L
        have hconjL : (uL : G) * y * (uL : G)⁻¹ ∈ L := by
          change (uL : G) * y * (uL : G)⁻¹ ∈
            section10AmbientSylowSubgroup L P at hy
          exact (show PG ≤ L from by
            intro z hz
            change z ∈ ((P : Subgroup L).map L.subtype : Subgroup G) at hz
            rw [Subgroup.mem_map] at hz
            rcases hz with ⟨zL, _hzP, rfl⟩
            exact zL.property) hy
        have hy' : (uL : G)⁻¹ * ((uL : G) * y * (uL : G)⁻¹) * (uL : G) ∈ L :=
          L.mul_mem (L.mul_mem hu_inv_mem_L hconjL) hu_mem_L
        simpa [mul_assoc] using hy'
      let yL : L := ⟨y, hyL⟩
      have hyPconj : (uL : L) * yL * (uL : L)⁻¹ ∈ P := by
        change ((uL : G) * y * (uL : G)⁻¹) ∈ section10AmbientSylowSubgroup L P at hy
        rw [section10AmbientSylowSubgroup, Subgroup.mem_map] at hy
        rcases hy with ⟨zL, hzP, hz_eq⟩
        have hz_val : (zL : G) = (uL : G) * y * (uL : G)⁻¹ := by
          simpa using hz_eq
        have hzL_eq : zL = (uL : L) * yL * (uL : L)⁻¹ := by
          ext
          simpa [yL, mul_assoc] using hz_val
        rw [← hzL_eq]
        exact hzP
      have huNorm := uL.property yL
      have hyP : yL ∈ P := huNorm.2 hyPconj
      change y ∈ PG
      exact Subgroup.mem_map_of_mem L.subtype hyP
  have hvC : (vL : G) ∈ Subgroup.centralizer (X : Set G) := by
    apply section10_pPrimeCore_normalizer_le_centralizer (X := X) (p := p) hXp
    rw [Subgroup.mem_map]
    exact ⟨vL, vL.property, rfl⟩
  refine ⟨⟨(uL : G), huG⟩, ⟨(vL : G), hvC⟩, ?_⟩
  exact congrArg Subtype.val ht

omit [IsMinCE G] in
public theorem CFSG.section10_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup
    {S X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hSp : IsPGroup p S) (hXS : X < S) :
    ∃ Y : Subgroup G,
      X < Y ∧ Y ≤ S ∧ Y ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup p Y := by
  classical
  have hX_le_S : X ≤ S := hXS.le
  let XS : Subgroup S := X.subgroupOf S
  have hXS_lt_top : XS < ⊤ := by
    refine ⟨le_top, ?_⟩
    intro htop
    have hS_le_X : S ≤ X := by
      intro x hxS
      let xS : S := ⟨x, hxS⟩
      have hxXS : xS ∈ XS := htop (by simp)
      simpa [XS, Subgroup.mem_subgroupOf, xS] using hxXS
    exact hXS.ne (le_antisymm hX_le_S hS_le_X)
  have hnc : NormalizerCondition S := by
    let : Group.IsNilpotent S := IsPGroup.isNilpotent (p := p) (G := S) hSp
    exact Group.normalizerCondition_of_isNilpotent (G := S)
  let NS : Subgroup S := Subgroup.normalizer (XS : Set S)
  have hXS_lt_NS : XS < NS := by
    simpa [NS] using hnc XS hXS_lt_top
  let Y : Subgroup G := NS.map S.subtype
  have hX_le_Y : X ≤ Y := by
    intro x hx
    have hxS : x ∈ S := hX_le_S hx
    let xS : S := ⟨x, hxS⟩
    have hxXS : xS ∈ XS := by
      simpa [XS, Subgroup.mem_subgroupOf, xS] using hx
    have hxNS : xS ∈ NS := Subgroup.le_normalizer hxXS
    exact Subgroup.mem_map_of_mem S.subtype hxNS
  have hY_not_le_X : ¬ Y ≤ X := by
    intro hYX
    apply hXS_lt_NS.not_ge
    intro y hyNS
    have hyY : (y : G) ∈ Y := Subgroup.mem_map_of_mem S.subtype hyNS
    have hyX : (y : G) ∈ X := hYX hyY
    simpa [XS, Subgroup.mem_subgroupOf] using hyX
  have hY_le_S : Y ≤ S := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, _hyNS, rfl⟩
    exact yS.property
  have hY_le_normX : Y ≤ Subgroup.normalizer (X : Set G) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, hyNS, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyNorm := Subgroup.mem_normalizer_iff.mp hyNS
    constructor
    · intro hzX
      have hzS : z ∈ S := hX_le_S hzX
      let zS : S := ⟨z, hzS⟩
      have hzXS : zS ∈ XS := by
        simpa [XS, Subgroup.mem_subgroupOf, zS] using hzX
      have hzImage : yS * zS * yS⁻¹ ∈ XS := (hyNorm zS).1 hzXS
      simpa [XS, Subgroup.mem_subgroupOf, zS, mul_assoc] using hzImage
    · intro hzConjX
      have hzConjS : (yS : G) * z * (yS : G)⁻¹ ∈ S := hX_le_S hzConjX
      have hzS : z ∈ S := by
        have hyS : (yS : G) ∈ S := yS.property
        have hyinvS : (yS : G)⁻¹ ∈ S := S.inv_mem hyS
        have hz' : (yS : G)⁻¹ * ((yS : G) * z * (yS : G)⁻¹) * (yS : G) ∈ S :=
          S.mul_mem (S.mul_mem hyinvS hzConjS) hyS
        simpa [mul_assoc] using hz'
      let zS : S := ⟨z, hzS⟩
      have hzConjXS : yS * zS * yS⁻¹ ∈ XS := by
        simpa [XS, Subgroup.mem_subgroupOf, zS, mul_assoc] using hzConjX
      have hzXS : zS ∈ XS := (hyNorm zS).2 hzConjXS
      simpa [XS, Subgroup.mem_subgroupOf, zS] using hzXS
  have hYp : IsPGroup p Y := by
    have hNSp : IsPGroup p NS := hSp.to_subgroup NS
    simpa [Y] using IsPGroup.map (p := p) (H := NS) hNSp S.subtype
  exact ⟨Y, ⟨hX_le_Y, hY_not_le_X⟩, hY_le_S, hY_le_normX, hYp⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_sylow_ambient_not_lt_pSubgroup_le
    {M Y : Subgroup G} {p : Nat.Primes} (P : Sylow p.val M)
    (hPGY : section10AmbientSylowSubgroup M P < Y)
    (hYM : Y ≤ M) (hYp : IsPGroup p.val Y) :
    False := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let YM : Subgroup M := Y.subgroupOf M
  have hYMp : IsPGroup p.val YM :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Y) (K := M) hYM).symm
  have hP_le_YM : (P : Subgroup M) ≤ YM := by
    intro y hyP
    change (y : G) ∈ Y
    apply hPGY.le
    exact Subgroup.mem_map_of_mem M.subtype hyP
  have hYM_eq : YM = (P : Subgroup M) := P.is_maximal' hYMp hP_le_YM
  have hY_le_PG : Y ≤ section10AmbientSylowSubgroup M P := by
    intro y hyY
    have hyM : y ∈ M := hYM hyY
    let yM : M := ⟨y, hyM⟩
    have hyYM : yM ∈ YM := by
      simpa [YM, Subgroup.mem_subgroupOf, yM] using hyY
    have hyP : yM ∈ (P : Subgroup M) := by
      simpa [hYM_eq] using hyYM
    exact Subgroup.mem_map_of_mem M.subtype hyP
  exact hPGY.not_ge hY_le_PG

omit [IsMinCE G] in
public theorem CFSG.section10_sigma_ambient_sylow_eq_of_le_sylow
    {M : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) (P : Sylow p.val M)
    (S : Sylow p.val G)
    (hPGS : section10AmbientSylowSubgroup M P ≤ (S : Subgroup G)) :
    (S : Subgroup G) = section10AmbientSylowSubgroup M P := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  by_contra hne
  have hPG_lt_S : PG < (S : Subgroup G) := by
    refine ⟨by simpa [PG] using hPGS, ?_⟩
    intro hS_le_PG
    exact hne (le_antisymm hS_le_PG (by simpa [PG] using hPGS))
  rcases section10_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup
      (S := (S : Subgroup G)) (X := PG) (p := p.val) S.isPGroup' hPG_lt_S with
    ⟨Y, hPGY, _hYS, hYnorm, hYp⟩
  have hnorm_le_M :
      Subgroup.normalizer (PG : Set G) ≤ M := by
    simpa [PG] using section10_sigma_sylow_normalizer_le hpσ P
  have hYM : Y ≤ M := hYnorm.trans hnorm_le_M
  exact section10_sylow_ambient_not_lt_pSubgroup_le P (by simpa [PG] using hPGY) hYM hYp

omit [IsMinCE G] in
public theorem CFSG.section10_exists_conjBy_le_of_isPGroup_of_sigma
    {M Y : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) (hYp : IsPGroup p.val Y) :
    ∃ a : G, Y ≤ M.conjBy a := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hpσ_saved : p ∈ section10SigmaPrimes M := hpσ
  rcases hpσ with ⟨_hpM, P₀, _hN₀⟩
  let PG₀ : Subgroup G := section10AmbientSylowSubgroup M P₀
  have hPG₀p : IsPGroup p.val PG₀ := by
    change IsPGroup p.val ((P₀ : Subgroup M).map M.subtype)
    simpa using
      (IsPGroup.map (p := p.val) (H := (P₀ : Subgroup M)) P₀.isPGroup' M.subtype)
  have hPG₀_le_M : PG₀ ≤ M := by
    intro x hx
    change x ∈ section10AmbientSylowSubgroup M P₀ at hx
    rw [section10AmbientSylowSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  rcases IsPGroup.exists_le_sylow (G := G) (p := p.val) hPG₀p with ⟨S₀, hPG₀S₀⟩
  have hS₀_eq : (S₀ : Subgroup G) = PG₀ :=
    section10_sigma_ambient_sylow_eq_of_le_sylow hpσ_saved P₀ S₀ hPG₀S₀
  rcases IsPGroup.exists_le_sylow (G := G) (p := p.val) hYp with ⟨S, hYS⟩
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G S₀ S
  refine ⟨a, ?_⟩
  have hS₀_smul :
      ((a • S₀ : Sylow p.val G) : Subgroup G) = (S₀ : Subgroup G).conjBy a := by
    ext x
    constructor
    · intro hx
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hx
      simpa [Subgroup.conjBy] using hx
    · intro hx
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      simpa [Subgroup.conjBy] using hx
  have hS_eq_conj : (S : Subgroup G) = PG₀.conjBy a := by
    calc
      (S : Subgroup G) = ((a • S₀ : Sylow p.val G) : Subgroup G) := by
        rw [ha]
      _ = (S₀ : Subgroup G).conjBy a := hS₀_smul
      _ = PG₀.conjBy a := by rw [hS₀_eq]
  intro y hyY
  have hyS : y ∈ (S : Subgroup G) := hYS hyY
  rw [hS_eq_conj] at hyS
  rw [Subgroup.conjBy, Subgroup.mem_map] at hyS ⊢
  rcases hyS with ⟨z, hzPG₀, rfl⟩
  exact ⟨z, hPG₀_le_M hzPG₀, rfl⟩

omit [IsMinCE G] in
public theorem CFSG.section10_exists_pSubgroup_gt_le_normalizer_of_lt_sylow
    {M X : Subgroup G} {p : Nat.Primes} (P : Sylow p.val M)
    (hXPG : X < section10AmbientSylowSubgroup M P) :
    ∃ Y : Subgroup G,
      X < Y ∧ Y ≤ M ∧ Y ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup p.val Y := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hX_le_PG : X ≤ PG := by
    simpa [PG] using hXPG.le
  have hPG_le_M : PG ≤ M := by
    intro x hx
    change x ∈ section10AmbientSylowSubgroup M P at hx
    rw [section10AmbientSylowSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    simpa using
      (IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype)
  let XP : Subgroup PG := X.subgroupOf PG
  have hXP_lt_top : XP < ⊤ := by
    refine ⟨le_top, ?_⟩
    intro htop
    have hPG_le_X : PG ≤ X := by
      intro x hxPG
      let xPG : PG := ⟨x, hxPG⟩
      have hxXP : xPG ∈ XP := by
        exact htop (by simp)
      simpa [XP, Subgroup.mem_subgroupOf, xPG] using hxXP
    exact hXPG.ne (le_antisymm hX_le_PG hPG_le_X)
  have hnc : NormalizerCondition PG := by
    let : Group.IsNilpotent PG := IsPGroup.isNilpotent (p := p.val) (G := PG) hPGp
    exact Group.normalizerCondition_of_isNilpotent (G := PG)
  let NPG : Subgroup PG := Subgroup.normalizer (XP : Set PG)
  have hXP_lt_NPG : XP < NPG := by
    simpa [NPG] using hnc XP hXP_lt_top
  let Y : Subgroup G := NPG.map PG.subtype
  have hX_le_Y : X ≤ Y := by
    intro x hx
    have hxPG : x ∈ PG := hX_le_PG hx
    let xPG : PG := ⟨x, hxPG⟩
    have hxXP : xPG ∈ XP := by
      simpa [XP, Subgroup.mem_subgroupOf, xPG] using hx
    have hxNPG : xPG ∈ NPG := by
      exact Subgroup.le_normalizer hxXP
    exact Subgroup.mem_map_of_mem PG.subtype hxNPG
  have hY_not_le_X : ¬ Y ≤ X := by
    intro hYX
    apply hXP_lt_NPG.not_ge
    intro y hyNPG
    have hyY : (y : G) ∈ Y := Subgroup.mem_map_of_mem PG.subtype hyNPG
    have hyX : (y : G) ∈ X := hYX hyY
    simpa [XP, Subgroup.mem_subgroupOf] using hyX
  have hY_le_M : Y ≤ M := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yPG, _hyNPG, rfl⟩
    exact hPG_le_M yPG.property
  have hY_le_normX : Y ≤ Subgroup.normalizer (X : Set G) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yPG, hyNPG, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyNorm := Subgroup.mem_normalizer_iff.mp hyNPG
    constructor
    · intro hzX
      have hzPG : z ∈ PG := hX_le_PG hzX
      let zPG : PG := ⟨z, hzPG⟩
      have hzXP : zPG ∈ XP := by
        simpa [XP, Subgroup.mem_subgroupOf, zPG] using hzX
      have hzImage : yPG * zPG * yPG⁻¹ ∈ XP := (hyNorm zPG).1 hzXP
      simpa [XP, Subgroup.mem_subgroupOf, zPG, mul_assoc] using hzImage
    · intro hzConjX
      have hzConjPG : (yPG : G) * z * (yPG : G)⁻¹ ∈ PG := hX_le_PG hzConjX
      have hzPG : z ∈ PG := by
        have hyPG : (yPG : G) ∈ PG := yPG.property
        have hyinvPG : (yPG : G)⁻¹ ∈ PG := PG.inv_mem hyPG
        have hz' :
            (yPG : G)⁻¹ * ((yPG : G) * z * (yPG : G)⁻¹) * (yPG : G) ∈ PG :=
          PG.mul_mem (PG.mul_mem hyinvPG hzConjPG) hyPG
        simpa [mul_assoc] using hz'
      let zPG : PG := ⟨z, hzPG⟩
      have hzConjXP : yPG * zPG * yPG⁻¹ ∈ XP := by
        simpa [XP, Subgroup.mem_subgroupOf, zPG, mul_assoc] using hzConjX
      have hzXP : zPG ∈ XP := (hyNorm zPG).2 hzConjXP
      simpa [XP, Subgroup.mem_subgroupOf, zPG] using hzXP
  have hYp : IsPGroup p.val Y := by
    have hNPGp : IsPGroup p.val NPG := hPGp.to_subgroup NPG
    simpa [Y] using IsPGroup.map (p := p.val) (H := NPG) hNPGp PG.subtype
  exact ⟨Y, ⟨hX_le_Y, hY_not_le_X⟩, hY_le_M, hY_le_normX, hYp⟩

omit [IsMinCE G] in
public theorem CFSG.section10_card_measure_lt_of_lt
    {X Y : Subgroup G} (hXY : X < Y) :
    Nat.card G - Nat.card Y < Nat.card G - Nat.card X := by
  have hcardXY : Nat.card X < Nat.card Y := by
    by_contra hnot
    have hle : Nat.card Y ≤ Nat.card X := le_of_not_gt hnot
    exact hXY.ne (Subgroup.eq_of_le_of_card_ge hXY.le hle)
  exact (tsub_lt_tsub_iff_left_of_le_of_le
    (Subgroup.card_le_card_group Y) (Subgroup.card_le_card_group X)).2 hcardXY

public theorem CFSG.section10_generatorRank_le_natCard_pre
    (H : Type*) [Group H] [Finite H] :
    generatorRank H ≤ Nat.card H := by
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec H
  calc
    generatorRank H = Group.rank H := generatorRank_eq_group_rank H
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card H := by simpa using Finset.card_le_univ S
    _ = Nat.card H := by simp [Nat.card_eq_fintype_card]

public theorem CFSG.section10_primeRank_le_natCard_pre
    {q : ℕ} (H : Type*) [Group H] [Finite H] :
    primeRank q H ≤ Nat.card H := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := H), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard_pre A).trans (Subgroup.card_le_card_group A)

public theorem CFSG.section10_primeRank_le_of_equiv_pre
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (q : ℕ) (e : R ≃* S) :
    primeRank q S ≤ primeRank q R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <| (section10_generatorRank_le_natCard_pre A).trans
      (Subgroup.card_le_card_group A)
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map e.symm.toMonoidHom
    have hA'q : IsPGroup q A' :=
      IsPGroup.map (p := q) (H := A) hAq e.symm.toMonoidHom
    have hA'comm : IsMulCommutative A' := by
      let : IsMulCommutative A := hAcomm
      infer_instance
    have hgen_le : generatorRank A ≤ generatorRank A' := by
      let eA : A ≃* A' :=
        Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact le_of_eq (Group.rank_congr eA)
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
          n ≤ generatorRank B} :=
      ⟨A', hA'q, hA'comm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q R := by
      rw [primeRank]
      refine le_csSup ?_ hmem
      refine ⟨Nat.card R, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
      exact hnB.trans <| (section10_generatorRank_le_natCard_pre B).trans
        (Subgroup.card_le_card_group B)
    rw [primeRank]
    exact hsSup_le.trans hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp

public theorem CFSG.section10_groupRank_le_of_equiv_pre
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (e : R ≃* S) :
    groupRank S ≤ groupRank R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (section10_primeRank_le_natCard_pre (q := q) S)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    have hqle : primeRank q S ≤ groupRank R := by
      rw [groupRank]
      refine (section10_primeRank_le_of_equiv_pre (R := R) (S := S) q e).trans ?_
      refine le_csSup ?_ ⟨q, hq, le_rfl⟩
      refine ⟨Nat.card R, ?_⟩
      intro n hn
      rcases hn with ⟨r, _hr, hnr⟩
      exact hnr.trans (section10_primeRank_le_natCard_pre (q := r) R)
    rw [groupRank]
    exact hsSup_le.trans hqle
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

omit [IsMinCE G] in
public theorem CFSG.section10_generatorRank_le_groupRank_of_subgroup_pre
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : generatorRank A ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section10_generatorRank_le_natCard_pre B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simp [hgen_eq]⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section10_primeRank_le_natCard_pre (q := r) K)
  · exact ⟨q, hq, hqrankK⟩

omit [IsMinCE G] in
public theorem CFSG.section10_primeRank_le_groupRank_sylow_pre
    {p : Nat.Primes} (S : Sylow p.val G) :
    primeRank p.val G ≤ groupRank (S : Subgroup G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := G), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
    let Aconj : Subgroup G := A.map (MulAut.conj g).toMonoidHom
    have hAconj_le_S : Aconj ≤ (S : Subgroup G) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
      have haQ : a ∈ (Q : Subgroup G) := hAQ haA
      have hmem : (MulAut.conj g) a ∈ ((g • Q : Sylow p.val G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Q : Subgroup G) haQ
      simpa [hg] using hmem
    have hAconj_p : IsPGroup p.val Aconj := by
      exact hAp.of_equiv
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    have hAconj_comm : IsMulCommutative Aconj := by
      let : IsMulCommutative A := hAcomm
      simpa [Aconj] using
        (Subgroup.map_isMulCommutative (f := (MulAut.conj g).toMonoidHom) (H := A))
    have hgen_eq : generatorRank A = generatorRank Aconj := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    exact hnA.trans <| by
      rw [hgen_eq]
      exact section10_generatorRank_le_groupRank_of_subgroup_pre
        (G := G) (q := p.val) p.property hAconj_le_S hAconj_p hAconj_comm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_mono
    {H K : Subgroup G} (hHK : H ≤ K) (g : G) :
    H.conjBy g ≤ K.conjBy g := by
  intro x hx
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, hHK hy, rfl⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjBy_mul_normalizer_right
    (H : Subgroup G) {k n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) :
    H.conjBy (k * n) = H.conjBy k := by
  calc
    H.conjBy (k * n) = (H.conjBy n).conjBy k := section10_conjBy_mul H k n
    _ = H.conjBy k := by rw [section10_conjBy_eq_of_mem_normalizer hn]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_centralizer_le_of_le
    {X Y : Subgroup G} (hXY : X ≤ Y) :
    Subgroup.centralizer (Y : Set G) ≤ Subgroup.centralizer (X : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro x hx
  exact hc x (hXY hx)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_centralizer_conj_mem_of_mem_normalizer
    {X : Subgroup G} {u v : G}
    (hu : u ∈ Subgroup.normalizer (X : Set G))
    (hv : v ∈ Subgroup.centralizer (X : Set G)) :
    u * v * u⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hv ⊢
  intro x hx
  have hx' : u⁻¹ * x * u ∈ X := by
    have huinv : u⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      (Subgroup.normalizer (X : Set G)).inv_mem hu
    simpa using (Subgroup.mem_normalizer_iff.mp huinv x).1 hx
  have hcomm := hv (u⁻¹ * x * u) hx'
  calc
    x * (u * v * u⁻¹) = u * ((u⁻¹ * x * u) * v) * u⁻¹ := by simp [mul_assoc]
    _ = u * (v * (u⁻¹ * x * u)) * u⁻¹ := by rw [← hcomm]
    _ = u * v * u⁻¹ * x := by simp [mul_assoc]


omit [IsMinCE G] in
public theorem CFSG.section10_transitive_pair_of_sylow_left
    {M X Q₁ Q₂ : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hQ₁X : Q₁ ∈ section10ConjugatesContaining M X)
    (hQ₂X : Q₂ ∈ section10ConjugatesContaining M X)
    (P₁ : Sylow p.val Q₁)
    (hP₁X : section10AmbientSylowSubgroup Q₁ P₁ = X) :
    ∃ c : Subgroup.centralizer (X : Set G), Q₂ = Q₁.conjBy (c : G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hQ₁X with ⟨a, rfl, hXQ₁⟩
  rcases hQ₂X with ⟨b, hQ₂eq, hXQ₂⟩
  let g : G := a * b⁻¹
  have hQ₂gQ₁ : Q₂.conjBy g = M.conjBy a := by
    rw [hQ₂eq]
    calc
      (M.conjBy b).conjBy g = M.conjBy (g * b) :=
        (section10_conjBy_mul M g b).symm
      _ = M.conjBy a := by simp [g, mul_assoc]
  have hXgQ₁ : X.conjBy g ≤ M.conjBy a := by
    intro x hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨y, hyX, rfl⟩
    have hyQ₂ : y ∈ Q₂ := hXQ₂ hyX
    have hy_conj : g * y * g⁻¹ ∈ Q₂.conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨y, hyQ₂, by simp [MulAut.conj_apply]⟩
    simpa [hQ₂gQ₁] using hy_conj
  have hP₁gQ₁ :
      (section10AmbientSylowSubgroup (M.conjBy a) P₁).conjBy g ≤ M.conjBy a := by
    simpa [hP₁X] using hXgQ₁
  have hgQ₁ : g ∈ M.conjBy a := by
    exact section10_sylow_conjugate_mem_of_normalizer_le P₁
      (section10_sigma_sylow_normalizer_le (section10_sigma_conjBy hpσ a) P₁)
      hP₁gQ₁
  have hQ₂_eq_Q₁ : Q₂ = M.conjBy a := by
    calc
      Q₂ = (Q₂.conjBy g).conjBy g⁻¹ := (section10_conjBy_inv Q₂ g).symm
      _ = (M.conjBy a).conjBy g⁻¹ := by rw [hQ₂gQ₁]
      _ = M.conjBy a := by
        have hgN : g⁻¹ ∈ Subgroup.normalizer (G := G) (M.conjBy a) :=
          (Subgroup.normalizer ((M.conjBy a) : Set G)).inv_mem (Subgroup.le_normalizer hgQ₁)
        exact section10_conjBy_eq_of_mem_normalizer hgN
  refine ⟨⟨1, by simp⟩, ?_⟩
  simpa [section10_conjBy_one] using hQ₂_eq_Q₁

omit [IsMinCE G] in
public theorem CFSG.section10_transitive_pair_of_sylow_right
    {M X Q₁ Q₂ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hQ₁X : Q₁ ∈ section10ConjugatesContaining M X)
    (hQ₂X : Q₂ ∈ section10ConjugatesContaining M X)
    (P₂ : Sylow p.val Q₂)
    (hP₂X : section10AmbientSylowSubgroup Q₂ P₂ = X) :
    ∃ c : Subgroup.centralizer (X : Set G), Q₂ = Q₁.conjBy (c : G) := by
  classical
  rcases section10_transitive_pair_of_sylow_left hM hpσ hQ₂X hQ₁X P₂ hP₂X with
    ⟨c, hc⟩
  refine ⟨⟨(c : G)⁻¹, (Subgroup.centralizer (X : Set G)).inv_mem c.property⟩, ?_⟩
  calc
    Q₂ = (Q₂.conjBy (c : G)).conjBy (c : G)⁻¹ :=
      (section10_conjBy_inv Q₂ (c : G)).symm
    _ = Q₁.conjBy (c : G)⁻¹ := by rw [hc]

omit [IsMinCE G] in
public theorem CFSG.section10_exists_larger_in_conjugate_of_not_sylow
    {X Q : Subgroup G} {p : Nat.Primes}
    (hXp : IsPGroup p.val X) (hXQ : X ≤ Q)
    (hnotSylow : ¬ ∃ P : Sylow p.val Q, section10AmbientSylowSubgroup Q P = X) :
    ∃ Y : Subgroup G,
      X < Y ∧ Y ≤ Q ∧ Y ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup p.val Y := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let XQ : Subgroup Q := X.subgroupOf Q
  have hXQp : IsPGroup p.val XQ :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := Q) hXQ).symm
  rcases IsPGroup.exists_le_sylow (G := Q) (p := p.val) hXQp with ⟨P, hXQ_le_P⟩
  have hX_le_PG : X ≤ section10AmbientSylowSubgroup Q P := by
    intro x hx
    have hxQ : x ∈ Q := hXQ hx
    let xQ : Q := ⟨x, hxQ⟩
    have hxXQ : xQ ∈ XQ := by
      simpa [XQ, Subgroup.mem_subgroupOf, xQ] using hx
    exact Subgroup.mem_map_of_mem Q.subtype (hXQ_le_P hxXQ)
  have hX_lt_PG : X < section10AmbientSylowSubgroup Q P := by
    refine ⟨hX_le_PG, ?_⟩
    intro hPG_le_X
    exact hnotSylow ⟨P, le_antisymm hPG_le_X hX_le_PG⟩
  exact section10_exists_pSubgroup_gt_le_normalizer_of_lt_sylow P hX_lt_PG

public theorem CFSG.section10_normalizer_le_maximal_of_three_le_groupRank_seed
    {P X M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (hPM : P ≤ M)
    (hPNX : P ≤ Subgroup.normalizer (X : Set G))
    (hXM : X ≤ M) (hXne : X ≠ ⊥) (hPrank : 3 ≤ groupRank P) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  have hPproper : P ≠ ⊤ := by
    intro hPtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hPtop] using hPM
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hPrank2 : 2 ≤ groupRank P := by omega
  have hPunique : P ∈ section9UniqueSubgroups G :=
    theorem_9_6 hPproper hPrank2 (Or.inl hPrank)
  exact section10_normalizer_le_maximal_of_unique_seed hM hPunique hPM hPNX hXM hXne

public theorem CFSG.section10_normalizer_factor_of_transitive
    {M P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hPM : P ≤ M)
    (htransP :
      ConjugationActionTransitiveOn (Subgroup.centralizer (P : Set G))
        (section10ConjugatesContaining M P))
    {u : G} (hu : u ∈ Subgroup.normalizer (P : Set G)) :
    ∃ w : subgroupNormalizerIn M (P : Set G),
      ∃ c : Subgroup.centralizer (P : Set G), u = (w : G) * (c : G) := by
  classical
  have hPuM : P.conjBy u ≤ M := by
    rw [section10_conjBy_eq_of_mem_normalizer hu]
    exact hPM
  rcases section10_double_coset_of_transitive hM hpσ hPM htransP hPuM with
    ⟨m, c, hu_eq⟩
  have hcN : (c : G) ∈ Subgroup.normalizer (P : Set G) :=
    centralizer_le_normalizer P c.property
  have hmN : (m : G) ∈ Subgroup.normalizer (P : Set G) := by
    have hm_eq : (m : G) = u * (c : G)⁻¹ := by
      rw [hu_eq]
      simp [mul_assoc]
    rw [hm_eq]
    exact (Subgroup.normalizer (P : Set G)).mul_mem hu
      ((Subgroup.normalizer (P : Set G)).inv_mem hcN)
  refine ⟨⟨(m : G), ?_⟩, c, hu_eq⟩
  exact section10_mem_subgroupNormalizerIn.mpr ⟨hmN, m.property⟩

public theorem CFSG.section10_normalizer_factor_left_of_transitive
    {M P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hPM : P ≤ M)
    (htransP :
      ConjugationActionTransitiveOn (Subgroup.centralizer (P : Set G))
        (section10ConjugatesContaining M P))
    {u : G} (hu : u ∈ Subgroup.normalizer (P : Set G)) :
    ∃ c : Subgroup.centralizer (P : Set G),
      ∃ w : subgroupNormalizerIn M (P : Set G), u = (c : G) * (w : G) := by
  classical
  have hu_inv : u⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hu
  rcases section10_normalizer_factor_of_transitive hM hpσ hPM htransP hu_inv with
    ⟨w, c, hu_inv_eq⟩
  refine ⟨c⁻¹, w⁻¹, ?_⟩
  calc
    u = (u⁻¹)⁻¹ := by simp
    _ = ((w : G) * (c : G))⁻¹ := by rw [hu_inv_eq]
    _ = ((c⁻¹ : Subgroup.centralizer (P : Set G)) : G) *
        ((w⁻¹ : subgroupNormalizerIn M (P : Set G)) : G) := by simp

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_conjugatesContaining_conjBy_iff
    (M X Q : Subgroup G) (a : G) :
    Q ∈ section10ConjugatesContaining (M.conjBy a) X ↔
      Q ∈ section10ConjugatesContaining M X := by
  constructor
  · rintro ⟨g, hQ, hXQ⟩
    refine ⟨g * a, ?_, hXQ⟩
    calc
      Q = (M.conjBy a).conjBy g := hQ
      _ = M.conjBy (g * a) := (section10_conjBy_mul M g a).symm
  · rintro ⟨g, hQ, hXQ⟩
    refine ⟨g * a⁻¹, ?_, hXQ⟩
    calc
      Q = M.conjBy g := hQ
      _ = M.conjBy ((g * a⁻¹) * a) := by simp [mul_assoc]
      _ = (M.conjBy a).conjBy (g * a⁻¹) := section10_conjBy_mul M (g * a⁻¹) a

public theorem CFSG.section10_normalizer_solvable_of_ne_bot_le_maximal
    {M X : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hXM : X ≤ M) (hXne : X ≠ ⊥) :
    Group.IsSolvable (Subgroup.normalizer (X : Set G)) := by
  have hproper :
      Subgroup.normalizer (X : Set G) ≠ ⊤ :=
    section10_normalizer_ne_top_of_ne_bot_le_maximal' hM hXM hXne
  exact IsMinCE.proper_subgroups_solvable (Subgroup.normalizer (X : Set G))
    (lt_top_iff_ne_top.mpr hproper)

public theorem CFSG.section10_normalizer_odd_of_minCE (X : Subgroup G) :
    Odd (Nat.card (Subgroup.normalizer (X : Set G))) := by
  exact odd_of_card_dvd IsMinCE.odd_order
    (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (X : Set G)))

/-- Theorem 10.1(b). -/
public theorem CFSG.theorem_10_1_b
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hXne : X ≠ ⊥) (hXp : IsPGroup p.val X) (hXM : X ≤ M) :
    ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G))
      (section10ConjugatesContaining M X) := by
  classical
  let μ : Subgroup G → ℕ := fun X => Nat.card G - Nat.card X
  refine (measure μ).wf.induction
    (C := fun X =>
      ∀ (M : Subgroup G) (p : Nat.Primes),
        M ∈ section9MaximalSubgroups G →
        p ∈ section10SigmaPrimes M →
        X ≠ ⊥ → IsPGroup p.val X → X ≤ M →
        ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G))
          (section10ConjugatesContaining M X))
    X ?_ M p hM hpσ hXne hXp hXM
  intro X ih M p hM hpσ hXne hXp hXM
  have : Fact p.val.Prime := ⟨p.property⟩
  intro Q₁ hQ₁X Q₂ hQ₂X
  rcases hQ₁X with ⟨a₁, hQ₁eq, hXQ₁⟩
  rcases hQ₂X with ⟨a₂, hQ₂eq, hXQ₂⟩
  have hQ₁Xmem : Q₁ ∈ section10ConjugatesContaining M X := ⟨a₁, hQ₁eq, hXQ₁⟩
  have hQ₂Xmem : Q₂ ∈ section10ConjugatesContaining M X := ⟨a₂, hQ₂eq, hXQ₂⟩
  by_cases hQ₁Sylow :
      ∃ P₁ : Sylow p.val Q₁, section10AmbientSylowSubgroup Q₁ P₁ = X
  · rcases hQ₁Sylow with ⟨P₁, hP₁X⟩
    exact section10_transitive_pair_of_sylow_left hM hpσ hQ₁Xmem hQ₂Xmem P₁ hP₁X
  by_cases hQ₂Sylow :
      ∃ P₂ : Sylow p.val Q₂, section10AmbientSylowSubgroup Q₂ P₂ = X
  · rcases hQ₂Sylow with ⟨P₂, hP₂X⟩
    exact section10_transitive_pair_of_sylow_right hM hpσ hQ₁Xmem hQ₂Xmem P₂ hP₂X
  rcases section10_exists_larger_in_conjugate_of_not_sylow
      (X := X) (Q := Q₁) (p := p) hXp hXQ₁ hQ₁Sylow with
    ⟨Y₁, hXY₁, hY₁Q₁, hY₁NX, hY₁p⟩
  rcases section10_exists_larger_in_conjugate_of_not_sylow
      (X := X) (Q := Q₂) (p := p) hXp hXQ₂ hQ₂Sylow with
    ⟨Y₂, hXY₂, hY₂Q₂, hY₂NX, hY₂p⟩
  let L : Subgroup G := Subgroup.normalizer (X : Set G)
  let Y₁L : Subgroup L := Y₁.subgroupOf L
  have hY₁Lp : IsPGroup p.val Y₁L :=
    hY₁p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Y₁) (K := L) hY₁NX).symm
  rcases IsPGroup.exists_le_sylow (G := L) (p := p.val) hY₁Lp with
    ⟨P, hY₁L_le_P⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup L P
  have hY₁PG : Y₁ ≤ PG := by
    intro y hy
    have hyL : y ∈ L := hY₁NX hy
    let yL : L := ⟨y, hyL⟩
    have hyY₁L : yL ∈ Y₁L := by
      simpa [Y₁L, Subgroup.mem_subgroupOf, yL] using hy
    exact Subgroup.mem_map_of_mem L.subtype (hY₁L_le_P hyY₁L)
  have hXPG : X ≤ PG := hXY₁.le.trans hY₁PG
  have hXPG_lt : X < PG := hXY₁.trans_le hY₁PG
  have hPGL : PG ≤ L := by
    intro y hy
    change y ∈ ((P : Subgroup L).map L.subtype : Subgroup G) at hy
    rw [Subgroup.mem_map] at hy
    rcases hy with ⟨yL, _hyP, rfl⟩
    exact yL.property
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup L).map L.subtype)
    simpa using
      (IsPGroup.map (p := p.val) (H := (P : Subgroup L)) P.isPGroup' L.subtype)
  let Y₂L : Subgroup L := Y₂.subgroupOf L
  have hY₂Lp : IsPGroup p.val Y₂L :=
    hY₂p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Y₂) (K := L) hY₂NX).symm
  rcases IsPGroup.exists_le_sylow (G := L) (p := p.val) hY₂Lp with
    ⟨P₂, hY₂L_le_P₂⟩
  obtain ⟨tL, htL_smul⟩ := MulAction.exists_smul_eq L P P₂
  have hP₂_eq_conj :
      section10AmbientSylowSubgroup L P₂ = PG.conjBy (tL : G) := by
    rw [← htL_smul]
    exact section10AmbientSylowSubgroup_smul P tL
  have hY₂PGt : Y₂ ≤ PG.conjBy (tL : G) := by
    intro y hy
    have hyL : y ∈ L := hY₂NX hy
    let yL : L := ⟨y, hyL⟩
    have hyY₂L : yL ∈ Y₂L := by
      simpa [Y₂L, Subgroup.mem_subgroupOf, yL] using hy
    have hyP₂ : yL ∈ P₂ := hY₂L_le_P₂ hyY₂L
    have hyAmb : y ∈ section10AmbientSylowSubgroup L P₂ :=
      Subgroup.mem_map_of_mem L.subtype hyP₂
    simpa [hP₂_eq_conj] using hyAmb
  rcases section10_exists_conjBy_le_of_isPGroup_of_sigma
      (M := M) (Y := PG) (p := p) hpσ hPGp with
    ⟨a, hPGM₀⟩
  let M₀ : Subgroup G := M.conjBy a
  have hM₀ : M₀ ∈ section9MaximalSubgroups G := by
    simpa [M₀] using section10_maximal_conjBy hM a
  have hpσ₀ : p ∈ section10SigmaPrimes M₀ := by
    simpa [M₀] using section10_sigma_conjBy hpσ a
  have hY₁M₀ : Y₁ ≤ M₀ := hY₁PG.trans hPGM₀
  have hXM₀ : X ≤ M₀ := hXPG.trans hPGM₀
  have hY₁ne : Y₁ ≠ ⊥ := by
    intro hY₁bot
    apply hXne
    exact eq_bot_iff.mpr (by intro x hx; simpa [hY₁bot] using hXY₁.le hx)
  have htransY₁ :
      ConjugationActionTransitiveOn (Subgroup.centralizer (Y₁ : Set G))
        (section10ConjugatesContaining M₀ Y₁) :=
    ih Y₁ (section10_card_measure_lt_of_lt hXY₁) M₀ p hM₀ hpσ₀ hY₁ne hY₁p hY₁M₀
  have hQ₁Y₁_M₀ : Q₁ ∈ section10ConjugatesContaining M₀ Y₁ := by
    have hQ₁Y₁_M : Q₁ ∈ section10ConjugatesContaining M Y₁ :=
      ⟨a₁, hQ₁eq, hY₁Q₁⟩
    simpa [M₀] using
      (section10_conjugatesContaining_conjBy_iff M Y₁ Q₁ a).2 hQ₁Y₁_M
  have hM₀Y₁ : M₀ ∈ section10ConjugatesContaining M₀ Y₁ :=
    ⟨1, (section10_conjBy_one M₀).symm, hY₁M₀⟩
  rcases htransY₁ Q₁ hQ₁Y₁_M₀ M₀ hM₀Y₁ with ⟨c₁, hM₀_eq_Q₁c₁⟩
  let M₀t : Subgroup G := M₀.conjBy (tL : G)
  have hM₀t : M₀t ∈ section9MaximalSubgroups G := by
    simpa [M₀t] using section10_maximal_conjBy hM₀ (tL : G)
  have hpσ₀t : p ∈ section10SigmaPrimes M₀t := by
    simpa [M₀t] using section10_sigma_conjBy hpσ₀ (tL : G)
  have hY₂M₀t : Y₂ ≤ M₀t := by
    exact hY₂PGt.trans (section10_conjBy_mono hPGM₀ (tL : G))
  have hY₂ne : Y₂ ≠ ⊥ := by
    intro hY₂bot
    apply hXne
    exact eq_bot_iff.mpr (by intro x hx; simpa [hY₂bot] using hXY₂.le hx)
  have htransY₂ :
      ConjugationActionTransitiveOn (Subgroup.centralizer (Y₂ : Set G))
        (section10ConjugatesContaining M₀t Y₂) :=
    ih Y₂ (section10_card_measure_lt_of_lt hXY₂) M₀t p hM₀t hpσ₀t hY₂ne hY₂p hY₂M₀t
  have hQ₂Y₂_M₀t : Q₂ ∈ section10ConjugatesContaining M₀t Y₂ := by
    have hQ₂Y₂_M : Q₂ ∈ section10ConjugatesContaining M Y₂ :=
      ⟨a₂, hQ₂eq, hY₂Q₂⟩
    have hQ₂Y₂_M₀ : Q₂ ∈ section10ConjugatesContaining M₀ Y₂ := by
      simpa [M₀] using
        (section10_conjugatesContaining_conjBy_iff M Y₂ Q₂ a).2 hQ₂Y₂_M
    simpa [M₀t] using
      (section10_conjugatesContaining_conjBy_iff M₀ Y₂ Q₂ (tL : G)).2 hQ₂Y₂_M₀
  have hM₀tY₂ : M₀t ∈ section10ConjugatesContaining M₀t Y₂ :=
    ⟨1, (section10_conjBy_one M₀t).symm, hY₂M₀t⟩
  rcases htransY₂ M₀t hM₀tY₂ Q₂ hQ₂Y₂_M₀t with ⟨c₂, hQ₂_eq_M₀tc₂⟩
  have hmiddle :
      ∃ c₀ : Subgroup.centralizer (X : Set G),
        M₀.conjBy (tL : G) = M₀.conjBy (c₀ : G) := by
    by_cases hPGrank : 3 ≤ groupRank PG
    · have hL_le_M₀ : L ≤ M₀ :=
        section10_normalizer_le_maximal_of_three_le_groupRank_seed
          (P := PG) (X := X) (M := M₀) hM₀ hPGM₀ hPGL hXM₀ hXne hPGrank
      have htM₀ : (tL : G) ∈ M₀ := hL_le_M₀ tL.property
      refine ⟨1, ?_⟩
      calc
        M₀.conjBy (tL : G) = M₀ :=
          section10_conjBy_eq_of_mem_normalizer (Subgroup.le_normalizer htM₀)
        _ = M₀.conjBy (1 : G) := (section10_conjBy_one M₀).symm
    · have hPGrank_le_two : groupRank PG ≤ 2 := by omega
      let eP : (P : Subgroup L) ≃* PG :=
        Subgroup.equivMapOfInjective (f := L.subtype) (P : Subgroup L)
          L.subtype_injective
      have hlocal_rank_le : groupRank (P : Subgroup L) ≤ groupRank PG :=
        section10_groupRank_le_of_equiv_pre eP.symm
      have hprimeRankL_le_two : primeRank p.val L ≤ 2 :=
        ((section10_primeRank_le_groupRank_sylow_pre (G := L) P).trans
          hlocal_rank_le).trans hPGrank_le_two
      have hp_dvd_L : p.val ∣ Nat.card L := by
        have hXnontrivial : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hXne
        obtain ⟨n, hn_pos, hXcard⟩ :=
          (IsPGroup.nontrivial_iff_card (p := p.val) (G := X) (hG := hXp)).mp
            hXnontrivial
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
        have hp_dvd_X : p.val ∣ Nat.card X := by
          rw [hXcard, pow_succ']
          exact dvd_mul_right p.val (p.val ^ m)
        exact hp_dvd_X.trans (Subgroup.card_dvd_of_le (show X ≤ L from Subgroup.le_normalizer))
      have hsolvL : Group.IsSolvable L :=
        section10_normalizer_solvable_of_ne_bot_le_maximal hM₀ hXM₀ hXne
      have hoddL : Odd (Nat.card L) := by
        simpa [L] using section10_normalizer_odd_of_minCE (G := G) X
      rcases section10_rank_le_two_factor_in_ambient_normalizer_centralizer
          (X := X) (p := p) hXp hsolvL hoddL hp_dvd_L hprimeRankL_le_two P tL with
        ⟨u, v, ht_uv⟩
      have hvN : (v : G) ∈ L := centralizer_le_normalizer X v.property
      have huL : (u : G) ∈ L := by
        have hu_eq : (u : G) = (tL : G) * (v : G)⁻¹ := by
          rw [ht_uv]
          simp [mul_assoc]
        rw [hu_eq]
        exact L.mul_mem tL.property (L.inv_mem hvN)
      let v' : Subgroup.centralizer (X : Set G) :=
        ⟨(u : G) * (v : G) * (u : G)⁻¹,
          section10_centralizer_conj_mem_of_mem_normalizer huL v.property⟩
      have ht_vu : (tL : G) = (v' : G) * (u : G) := by
        calc
          (tL : G) = (u : G) * (v : G) := ht_uv
          _ = ((u : G) * (v : G) * (u : G)⁻¹) * (u : G) := by simp [mul_assoc]
          _ = (v' : G) * (u : G) := rfl
      have hPGne : PG ≠ ⊥ := by
        intro hPGbot
        apply hXne
        exact eq_bot_iff.mpr (by intro x hx; simpa [hPGbot] using hXPG hx)
      have htransPG :
          ConjugationActionTransitiveOn (Subgroup.centralizer (PG : Set G))
            (section10ConjugatesContaining M₀ PG) :=
        ih PG (section10_card_measure_lt_of_lt hXPG_lt) M₀ p hM₀ hpσ₀ hPGne hPGp hPGM₀
      rcases section10_normalizer_factor_left_of_transitive
          (M := M₀) (P := PG) (p := p) hM₀ hpσ₀ hPGM₀ htransPG u.property with
        ⟨cP, w, hu_cw⟩
      let cPX : Subgroup.centralizer (X : Set G) :=
        ⟨(cP : G), section10_centralizer_le_of_le hXPG cP.property⟩
      let k : Subgroup.centralizer (X : Set G) := v' * cPX
      have ht_kw : (tL : G) = (k : G) * (w : G) := by
        calc
          (tL : G) = (v' : G) * (u : G) := ht_vu
          _ = (v' : G) * ((cP : G) * (w : G)) := by rw [hu_cw]
          _ = (k : G) * (w : G) := by simp [k, cPX, mul_assoc]
      have hwM₀ : (w : G) ∈ M₀ := (section10_mem_subgroupNormalizerIn.mp w.property).2
      have hwN : (w : G) ∈ Subgroup.normalizer (M₀ : Set G) :=
        Subgroup.le_normalizer hwM₀
      refine ⟨k, ?_⟩
      calc
        M₀.conjBy (tL : G) = M₀.conjBy ((k : G) * (w : G)) := by rw [ht_kw]
        _ = M₀.conjBy (k : G) := section10_conjBy_mul_normalizer_right M₀ hwN
  rcases hmiddle with ⟨c₀, hM₀t_eq_M₀c₀⟩
  let c₁X : Subgroup.centralizer (X : Set G) :=
    ⟨(c₁ : G), section10_centralizer_le_of_le hXY₁.le c₁.property⟩
  let c₂X : Subgroup.centralizer (X : Set G) :=
    ⟨(c₂ : G), section10_centralizer_le_of_le hXY₂.le c₂.property⟩
  refine ⟨c₂X * c₀ * c₁X, ?_⟩
  calc
    Q₂ = (M₀.conjBy (tL : G)).conjBy (c₂ : G) := hQ₂_eq_M₀tc₂
    _ = (M₀.conjBy (c₀ : G)).conjBy (c₂ : G) := by rw [hM₀t_eq_M₀c₀]
    _ = ((Q₁.conjBy (c₁ : G)).conjBy (c₀ : G)).conjBy (c₂ : G) := by
      rw [hM₀_eq_Q₁c₁]
    _ = (Q₁.conjBy ((c₀ : G) * (c₁ : G))).conjBy (c₂ : G) := by
      rw [← section10_conjBy_mul Q₁ (c₀ : G) (c₁ : G)]
    _ = Q₁.conjBy ((c₂ : G) * ((c₀ : G) * (c₁ : G))) := by
      rw [← section10_conjBy_mul Q₁ (c₂ : G) ((c₀ : G) * (c₁ : G))]
    _ = Q₁.conjBy (((c₂X * c₀ * c₁X : Subgroup.centralizer (X : Set G)) : G)) := by
      simp [c₁X, c₂X, mul_assoc]


end Section10
