module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LocalAnalysis.EvenBN.Common.ProductSplit
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineSocle

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y]

structure PerfSocleMod (Kk F : Subgroup Y) : Prop where
  normal_left : Kk.Normal
  normal_right : F.Normal
  le : Kk ≤ F
  perfect : F ≤ ⁅F, F⁆ ⊔ Kk
  not_le : ¬ F ≤ Kk
  centralizer_le : ∀ y : Y, (∀ f ∈ F, ⁅y, f⁆ ∈ Kk) → y ∈ Kk

theorem SimpleSocleMod.toPerf {Kk F : Subgroup Y} (h : SimpleSocleMod Kk F) :
    PerfSocleMod Kk F where
  normal_left := h.normal_left
  normal_right := h.normal_right
  le := h.le
  perfect := by
    haveI := h.normal_left
    haveI := h.normal_right
    have hFFle : ⁅F, F⁆ ≤ F := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact F.mul_mem (F.mul_mem (F.mul_mem ha hb) (F.inv_mem ha)) (F.inv_mem hb)
    have hnorm : (⁅F, F⁆ ⊔ Kk : Subgroup Y).Normal := inferInstance
    have hsub : ((⁅F, F⁆ ⊔ Kk).subgroupOf F).Normal := hnorm.subgroupOf F
    rcases h.eq_or_eq (⁅F, F⁆ ⊔ Kk) le_sup_right (sup_le hFFle h.le) hsub with hT | hT
    · exfalso
      obtain ⟨f₁, hf₁, f₂, hf₂, hnk⟩ := h.not_abelian
      have hmem : ⁅f₁, f₂⁆ ∈ ⁅F, F⁆ ⊔ Kk :=
        Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hf₁ hf₂)
      rw [hT] at hmem
      exact hnk hmem
    · exact le_of_eq hT.symm
  not_le := fun hFK => by
    obtain ⟨f₁, hf₁, f₂, hf₂, hnk⟩ := h.not_abelian
    have hmemF : ⁅f₁, f₂⁆ ∈ F := by
      rw [commutatorElement_def]
      exact F.mul_mem (F.mul_mem (F.mul_mem hf₁ hf₂) (F.inv_mem hf₁)) (F.inv_mem hf₂)
    exact hnk (hFK hmemF)
  centralizer_le := h.centralizer_le

structure KernSetting (Kk F P : Subgroup Y) : Prop where
  socle : PerfSocleMod Kk F
  solvable : Group.IsSolvable ↥Kk
  o2_eq_bot : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 ↥N → N = ⊥
  normal : P.Normal
  two_quotient : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ P
  le_of_not_le : ∀ N : Subgroup Y, N.Normal → ¬ N ≤ Kk → P ≤ N

namespace KernSetting

variable {Kk F P : Subgroup Y}

private theorem kern_eq_of_perfect_of_pow_mem {X N : Subgroup Y} (hX : ⁅X, X⁆ = X) (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = X := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hX
  have := hN
  have hp : IsPGroup 2 (↥X ⧸ N.subgroupOf X) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  have : Group.IsNilpotent (↥X ⧸ N.subgroupOf X) := hp.isNilpotent
  have hsub : Subsingleton (↥X ⧸ N.subgroupOf X) := by
    by_contra hns
    have : Nontrivial (↥X ⧸ N.subgroupOf X) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isNilpotent (↥X ⧸ N.subgroupOf X) inferInstance
  refine le_antisymm hNX fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : X) : ↥X ⧸ N.subgroupOf X) = QuotientGroup.mk 1 :=
    Subsingleton.elim _ _
  rw [QuotientGroup.eq] at h1
  simpa [Subgroup.mem_subgroupOf] using h1

private theorem kern_mem_centralizer_of_commutator_mem_center {P : Subgroup Y} (hP : ⁅P, P⁆ = P)
    {h : Y} (hN : h ∈ normalizer (P : Set Y))
    (hc : ∀ p ∈ P, ∀ q ∈ P, h * p * h⁻¹ * p⁻¹ * q = q * (h * p * h⁻¹ * p⁻¹)) :
    h ∈ centralizer (P : Set Y) := by
  have hmem : ∀ p ∈ P, h * p * h⁻¹ * p⁻¹ ∈ P := fun p hp =>
    mul_mem ((mem_normalizer_iff.mp hN p).mp hp) (inv_mem hp)
  have key : ⁅P, P⁆ ≤ centralizer ({h} : Set Y) := by
    refine commutator_le.mpr fun p hp q hq => ?_
    obtain ⟨a, ha⟩ : ∃ a, a = h * p * h⁻¹ * p⁻¹ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = h * q * h⁻¹ * q⁻¹ := ⟨_, rfl⟩
    have hbP : b ∈ P := hb ▸ hmem q hq
    have hpa : h * p * h⁻¹ = a * p := by rw [ha]; group
    have hqb : h * q * h⁻¹ = b * q := by rw [hb]; group
    have e2 : a * (p * b * q * p⁻¹) = (p * b * q * p⁻¹) * a := by
      rw [ha]
      exact hc p hp _ (mul_mem (mul_mem (mul_mem hp hbP) hq) (inv_mem hp))
    have e3 : p * b = b * p := by
      rw [hb]
      exact (hc q hq p hp).symm
    have e4 : b * (p * q * p⁻¹ * q⁻¹) = (p * q * p⁻¹ * q⁻¹) * b := by
      rw [hb]
      exact hc q hq _ (mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq))
    have hconj : h * (p * q * p⁻¹ * q⁻¹) * h⁻¹ = p * q * p⁻¹ * q⁻¹ := by
      calc h * (p * q * p⁻¹ * q⁻¹) * h⁻¹
          = (h * p * h⁻¹) * (h * q * h⁻¹) * (h * p * h⁻¹)⁻¹ * (h * q * h⁻¹)⁻¹ := by
            group
        _ = (a * p) * (b * q) * (a * p)⁻¹ * (b * q)⁻¹ := by rw [hpa, hqb]
        _ = a * (p * b * q * p⁻¹) * a⁻¹ * (q⁻¹ * b⁻¹) := by group
        _ = (p * b * q * p⁻¹) * a * a⁻¹ * (q⁻¹ * b⁻¹) := by rw [e2]
        _ = (p * b) * (q * p⁻¹ * q⁻¹) * b⁻¹ := by group
        _ = (b * p) * (q * p⁻¹ * q⁻¹) * b⁻¹ := by rw [e3]
        _ = b * (p * q * p⁻¹ * q⁻¹) * b⁻¹ := by group
        _ = (p * q * p⁻¹ * q⁻¹) * b * b⁻¹ := by rw [e4]
        _ = p * q * p⁻¹ * q⁻¹ := by group
    rw [mem_centralizer_singleton_iff]
    calc p * q * p⁻¹ * q⁻¹ * h = h * (p * q * p⁻¹ * q⁻¹) * h⁻¹ * h := by rw [hconj]
      _ = h * (p * q * p⁻¹ * q⁻¹) := by group
  rw [hP] at key
  exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (key hx)

theorem perfect_core (h : KernSetting Kk F P) : ⁅P, P⁆ = P ∧ P ⊔ Kk = F := by
  haveI := h.socle.normal_left
  haveI := h.socle.normal_right
  have hFF : F ≤ ⁅F, F⁆ ⊔ Kk := h.socle.perfect
  obtain ⟨P', hP'norm, hP'perf, hP'le, hP'sup, _⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_perfect_normal_sup_eq
      (X := Kk) (H := F) h.socle.le hFF
  have hP'notK : ¬ P' ≤ Kk := by
    intro hle
    have hFK : F ≤ Kk := by
      rw [← hP'sup]
      exact sup_le hle le_rfl
    exact h.socle.not_le hFK
  have hPP' : P ≤ P' := h.le_of_not_le P' hP'norm hP'notK
  have hP'P : P' ≤ P := by
    have hNnorm : ((P ⊓ P').subgroupOf P').Normal := by
      rw [Subgroup.inf_subgroupOf_right]
      exact h.normal.subgroupOf P'
    have hpow : ∀ x ∈ P', ∃ k : ℕ, x ^ 2 ^ k ∈ P ⊓ P' := by
      intro x hx
      obtain ⟨k, hk⟩ := h.two_quotient x
      exact ⟨k, ⟨hk, pow_mem hx (2 ^ k)⟩⟩
    exact inf_eq_right.mp (kern_eq_of_perfect_of_pow_mem hP'perf inf_le_right hNnorm hpow)
  have hP_eq : P = P' := le_antisymm hPP' hP'P
  exact ⟨hP_eq.symm ▸ hP'perf, hP_eq.symm ▸ hP'sup⟩

theorem exists_odd_normal (h : KernSetting Kk F P) :
    ∃ Fo : Subgroup Y, Fo.Normal ∧ Fo ≤ Kk ∧ Odd (Nat.card ↥Fo) ∧
      ∀ y ∈ Kk, (∀ f ∈ Fo, y * f = f * y) → y ∈ Fo := by
  haveI := h.socle.normal_left
  let Fo : Subgroup Y := (fittingSubgroup ↥Kk).map Kk.subtype
  have hFoNorm : Fo.Normal := inferInstance
  have hFoK : Fo ≤ Kk := Subgroup.map_subtype_le _
  have hFoNil : Group.IsNilpotent ↥Fo :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (fittingSubgroup ↥Kk) Kk.subtype Kk.subtype_injective)
  have hFoodd : Odd (Nat.card ↥Fo) := by
    by_contra hnot
    have h2dvd : 2 ∣ Nat.card ↥Fo := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
    let S : Sylow 2 ↥Fo := default
    haveI : Group.IsNilpotent ↥Fo := hFoNil
    have hSnorm : (S : Subgroup ↥Fo).Normal := inferInstance
    have hSne : (S : Subgroup ↥Fo) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S h2dvd
    have hSchar : (S : Subgroup ↥Fo).Characteristic := Sylow.characteristic_of_normal S hSnorm
    haveI : (S : Subgroup ↥Fo).Characteristic := hSchar
    haveI : Fo.Normal := hFoNorm
    have hNnorm : ((S : Subgroup ↥Fo).map Fo.subtype).Normal := inferInstance
    have hNp : IsPGroup 2 ↥((S : Subgroup ↥Fo).map Fo.subtype) :=
      S.isPGroup'.map Fo.subtype
    have hbot := h.o2_eq_bot _ hNnorm hNp
    apply hSne
    rw [eq_bot_iff]
    intro s hs
    have hmem : (s : Y) ∈ (S : Subgroup ↥Fo).map Fo.subtype := ⟨s, hs, rfl⟩
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  refine ⟨Fo, hFoNorm, hFoK, hFoodd, ?_⟩
  intro y hyK hcomm
  have hcent : (⟨y, hyK⟩ : ↥Kk) ∈ Subgroup.centralizer (fittingSubgroup ↥Kk : Set ↥Kk) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact (hcomm (z : Y) ⟨z, hz, rfl⟩).symm
  have hmem : (⟨y, hyK⟩ : ↥Kk) ∈ fittingSubgroup ↥Kk :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable h.solvable hcent
  exact ⟨⟨y, hyK⟩, hmem, rfl⟩

theorem le_of_odd (h : KernSetting Kk F P) {X : Subgroup Y} (hX : Odd (Nat.card ↥X)) : X ≤ P := by
  intro x hx
  obtain ⟨k, hk⟩ := h.two_quotient x
  have hxodd : Odd (orderOf x) := hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx)
  have hcop : (orderOf x).Coprime (2 ^ k) := (Nat.coprime_two_right.mpr hxodd).pow_right k
  have horder : orderOf (x ^ 2 ^ k) = orderOf x := hcop.orderOf_pow
  have hle : Subgroup.zpowers (x ^ 2 ^ k) ≤ Subgroup.zpowers x :=
    Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers x (2 ^ k))
  have heq : Subgroup.zpowers (x ^ 2 ^ k) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, horder])
  have hxmem : x ∈ Subgroup.zpowers (x ^ 2 ^ k) := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact Subgroup.zpowers_le.mpr hk hxmem

theorem le_centralizer_of_odd (h : KernSetting Kk F P) {A Fo : Subgroup Y} (hA2 : IsPGroup 2 ↥A)
    (hA4 : 4 ≤ Nat.card ↥A) (hA : (A ⊓ centralizer (Fo : Set Y)).relIndex A ≤ 2)
    (hFo : Fo.Normal) (hFoK : Fo ≤ Kk) (hodd : Odd (Nat.card ↥Fo))
    (hself : ∀ y ∈ Kk, (∀ f ∈ Fo, y * f = f * y) → y ∈ Fo) :
    P ≤ centralizer (Fo : Set Y) := by
  let A₀ : Subgroup Y := A ⊓ centralizer (Fo : Set Y)
  have hA0 : A₀ = A ⊓ centralizer (Fo : Set Y) := rfl
  have hcard : 2 ≤ Nat.card ↥A₀ := by
    have h1 : A₀.relIndex A * Nat.card ↥A₀ = Nat.card ↥A := by
      have h := Subgroup.relIndex_mul_card (H := A₀) (K := A)
      rwa [show A₀ ⊓ A = A₀ from inf_eq_left.mpr (by rw [hA0]; exact inf_le_left)] at h
    have h2 : 4 ≤ A₀.relIndex A * Nat.card ↥A₀ := by rw [h1]; exact hA4
    have h3 : A₀.relIndex A * Nat.card ↥A₀ ≤ 2 * Nat.card ↥A₀ := Nat.mul_le_mul_right _ hA
    omega
  have hA0ne : A₀ ≠ ⊥ := by
    intro hbot
    have : Nat.card ↥A₀ = 1 := by rw [hbot]; simp
    omega
  have hA0K : A₀ ⊓ Kk = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyA0, hyK⟩ := Subgroup.mem_inf.mp hy
    rw [hA0] at hyA0
    obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hyA0
    have hyFo : y ∈ Fo := hself y hyK fun f hf => (mem_centralizer_iff.mp hyC f hf).symm
    have horder_dvd : orderOf y ∣ Nat.card ↥Fo := Subgroup.orderOf_dvd_natCard Fo hyFo
    have hyodd : Odd (orderOf y) := hodd.of_dvd_nat horder_dvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hA2.exists_orderOf_eq_pow ⟨y, hyA⟩
    have hk' : orderOf y = 2 ^ k := (Subgroup.orderOf_coe (⟨y, hyA⟩ : ↥A)).trans hk
    have hk0 : k = 0 := by
      by_contra hk0
      have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2dvd) (hk' ▸ hyodd)
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])
  have hA0notK : ¬ A₀ ≤ Kk := by
    intro hle
    have : A₀ = ⊥ := by
      rw [← hA0K]
      exact (inf_eq_left.mpr hle).symm
    exact hA0ne this
  let N : Subgroup Y := Subgroup.normalClosure (A₀ : Set Y)
  have hNnorm : N.Normal := Subgroup.normalClosure_normal
  have hNnotK : ¬ N ≤ Kk := fun hle =>
    hA0notK (Subgroup.subset_normalClosure.trans hle)
  have hPN : P ≤ N := h.le_of_not_le N hNnorm hNnotK
  have hNC : N ≤ centralizer (Fo : Set Y) := by
    haveI : Fo.Normal := hFo
    haveI : (centralizer (Fo : Set Y)).Normal := inferInstance
    exact Subgroup.normalClosure_le_normal fun x hx => (Subgroup.mem_inf.mp (hA0 ▸ hx)).2
  exact hPN.trans hNC

theorem le_centralizer_of_inf_le (h : KernSetting Kk F P) {Fo : Subgroup Y} (hP : ⁅P, P⁆ = P)
    (hKP : Kk ⊓ P ≤ Fo) (hFo : Fo ≤ centralizer (P : Set Y)) :
    Kk ≤ centralizer (P : Set Y) := by
  intro k hk
  refine kern_mem_centralizer_of_commutator_mem_center hP ?_ ?_
  · rw [Subgroup.normalizer_eq_top_iff.mpr h.normal]
    exact trivial
  · intro p hp q hq
    have hcomm_mem : k * p * k⁻¹ * p⁻¹ ∈ Kk ⊓ P := by
      refine ⟨?_, ?_⟩
      · have heq : k * p * k⁻¹ * p⁻¹ = k * (p * k⁻¹ * p⁻¹) := by group
        rw [heq]
        exact Kk.mul_mem hk (h.socle.normal_left.conj_mem k⁻¹ (Kk.inv_mem hk) p)
      · exact P.mul_mem (h.normal.conj_mem p hp k) (P.inv_mem hp)
    exact ((mem_centralizer_iff.mp (hFo (hKP hcomm_mem))) q hq).symm

theorem centralizer_le (h : KernSetting Kk F P) : centralizer (P : Set Y) ≤ P := by
  haveI hPnormal : P.Normal := h.normal
  set C : Subgroup Y := centralizer (P : Set Y) with hC
  have hCnorm : C.Normal := hC.symm ▸ (inferInstance : (centralizer (P : Set Y)).Normal)
  haveI : C.Normal := hCnorm
  set M : Subgroup Y := C ⊓ P with hM
  have hMnorm : M.Normal := hM.symm ▸ (inferInstance : (C ⊓ P).Normal)
  haveI : M.Normal := hMnorm
  let N : Subgroup ↥C := M.subgroupOf C
  have hNnorm : N.Normal := hMnorm.subgroupOf C
  haveI : N.Normal := hNnorm
  have hpQ : IsPGroup 2 (↥C ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      obtain ⟨k, hk⟩ := h.two_quotient (c : Y)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow, Subgroup.mem_inf]
      exact ⟨pow_mem c.2 (2 ^ k), hk⟩
  have hCnil : Group.IsNilpotent ↥C := by
    haveI : Finite (↥C ⧸ N) := inferInstance
    haveI : Group.IsNilpotent (↥C ⧸ N) := hpQ.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N) ?_
    rw [QuotientGroup.ker_mk']
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have hnP : (n : Y) ∈ P := (Subgroup.mem_subgroupOf.mp hn).2
    exact (mem_centralizer_iff.mp c.2 (n : Y) hnP).symm
  have hCodd : Odd (Nat.card ↥C) := by
    by_contra hnot
    have h2dvd : 2 ∣ Nat.card ↥C := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
    let S : Sylow 2 ↥C := default
    haveI : Group.IsNilpotent ↥C := hCnil
    have hSnorm : (S : Subgroup ↥C).Normal := inferInstance
    have hSne : (S : Subgroup ↥C) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S h2dvd
    have hSchar : (S : Subgroup ↥C).Characteristic := Sylow.characteristic_of_normal S hSnorm
    haveI : (S : Subgroup ↥C).Characteristic := hSchar
    have hNnorm' : ((S : Subgroup ↥C).map C.subtype).Normal := inferInstance
    have hNp : IsPGroup 2 ↥((S : Subgroup ↥C).map C.subtype) := S.isPGroup'.map C.subtype
    have hbot := h.o2_eq_bot _ hNnorm' hNp
    apply hSne
    rw [eq_bot_iff]
    intro s hs
    have hmem : (s : Y) ∈ (S : Subgroup ↥C).map C.subtype := ⟨s, hs, rfl⟩
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  exact h.le_of_odd hCodd

theorem inf_centralizer_le (h : KernSetting Kk F P) (hP : P ⊔ Kk = F) :
    P ⊓ centralizer (P : Set Y) ≤ Kk := by
  haveI := h.socle.normal_left
  intro z hz
  obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hz
  refine h.socle.centralizer_le z ?_
  intro f hf
  have hf' : f ∈ P ⊔ Kk := by rw [hP]; exact hf
  obtain ⟨p, hp, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hf'
  have hzk : ⁅z, k⁆ ∈ Kk := by
    rw [commutatorElement_def]
    exact Kk.mul_mem (h.socle.normal_left.conj_mem k hk z) (Kk.inv_mem hk)
  have hzpk : ⁅z, p * k⁆ = p * ⁅z, k⁆ * p⁻¹ := by
    have hzp : z * p = p * z := (mem_centralizer_iff.mp hzC p hp).symm
    rw [commutatorElement_def, commutatorElement_def]
    calc z * (p * k) * z⁻¹ * (p * k)⁻¹
        = z * p * (k * z⁻¹ * k⁻¹) * p⁻¹ := by group
      _ = p * z * (k * z⁻¹ * k⁻¹) * p⁻¹ := by rw [hzp]
      _ = p * (z * k * z⁻¹ * k⁻¹) * p⁻¹ := by group
  rw [hzpk]
  exact h.socle.normal_left.conj_mem _ hzk p

theorem kern_eq_centralizer (h : KernSetting Kk F P) {A : Subgroup Y} (hA2 : IsPGroup 2 ↥A)
    (hA4 : 4 ≤ Nat.card ↥A)
    (hA13 : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card ↥N) →
      (A ⊓ centralizer (N : Set Y)).relIndex A ≤ 2) :
    ⁅P, P⁆ = P ∧ P = F ∧ Kk ≤ P ∧ Kk = centralizer (P : Set Y) ∧ Odd (Nat.card ↥Kk) := by
  obtain ⟨hperf, hPF⟩ := h.perfect_core
  obtain ⟨Fo, hFoN, hFoK, hFoodd, hself⟩ := h.exists_odd_normal
  have hFoP : Fo ≤ P := h.le_of_odd hFoodd
  have hPC : P ≤ centralizer (Fo : Set Y) :=
    h.le_centralizer_of_odd hA2 hA4 (hA13 Fo hFoN hFoodd) hFoN hFoK hFoodd hself
  have hKP : Kk ⊓ P ≤ Fo := fun y hy =>
    hself y hy.1 fun f hf => (mem_centralizer_iff.1 (hPC hy.2) f hf).symm
  have hFoC : Fo ≤ centralizer (P : Set Y) := fun f hf =>
    mem_centralizer_iff.2 fun p hp => (mem_centralizer_iff.1 (hPC hp) f hf).symm
  have hKC : Kk ≤ centralizer (P : Set Y) := h.le_centralizer_of_inf_le hperf hKP hFoC
  have hCP : centralizer (P : Set Y) ≤ P := h.centralizer_le
  have hZK : P ⊓ centralizer (P : Set Y) ≤ Kk := h.inf_centralizer_le hPF
  have hKP' : Kk ≤ P := hKC.trans hCP
  have hKFo : Kk = Fo := le_antisymm (fun y hy => hKP ⟨hy, hKP' hy⟩) hFoK
  exact ⟨hperf, ((sup_eq_left.2 hKP').symm.trans hPF), hKP',
    le_antisymm hKC fun y hy => hZK ⟨hCP hy, hy⟩, hKFo ▸ hFoodd⟩

end KernSetting

end CFSG.LocalAnalysis.WeakClosure81

end
