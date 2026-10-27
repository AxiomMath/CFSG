module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

@[expose] def CensusDCentreless : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsSurvivingCase L →
      ∀ J : Subgroup (Subgroup.centralizer ({c * d} : Set G) ⧸
          aschbacherSolvableCore 3 (Subgroup.centralizer ({c * d} : Set G))),
        CFSG.IsComponent J → Subgroup.center J = ⊥

noncomputable abbrev cdπ (x : G) : CAt x →* QAt x :=
  QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt x))

@[expose] noncomputable def cdSub (x : G) (S : Subgroup G) : Subgroup (QAt x) :=
  (S.subgroupOf (Subgroup.centralizer ({x} : Set G))).map (cdπ x)

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem cd_R_facts (h113 : Item113) (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) :
    IsPGroup 3 R ∧ A ≤ R ∧ ∀ r ∈ R, r * c = c * r ∧ r * d = d * r := by
  have hs := h.toSec11Std hT
  have hA : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} := (h113 G A c L a R Y hs).1
  have hPgrp : IsPGroup 3 R := by
    obtain ⟨Q, hQ⟩ := h.isSylowOf_top
    have h1 := Q.isPGroup'.map (⊤ : Subgroup G).subtype
    rw [hQ] at h1
    exact h1
  have hAR : A ≤ R := by
    rw [hA]
    exact (Subgroup.closure_le R).mpr (fun y hy => hy.1)
  have hconj : ∀ s ∈ R, ∀ x ∈ A, s * x * s⁻¹ ∈ A := by
    intro s hsR x hx
    have hle : A ≤ A.comap (MulAut.conj s).toMonoidHom := by
      rw [hA]
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      obtain ⟨hyR, hy3⟩ := hy
      show (MulAut.conj s).toMonoidHom y ∈ Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}
      apply Subgroup.subset_closure
      show s * y * s⁻¹ ∈ R ∧ (s * y * s⁻¹) ^ 3 = 1
      exact ⟨R.mul_mem (R.mul_mem hsR hyR) (R.inv_mem hsR), by simp [conj_pow, hy3]⟩
    exact hle hx
  have hnorm : ∀ s ∈ R, s ∈ Subgroup.normalizer (A : Set G) := by
    intro s hsR
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj s hsR x hx
    · intro hx
      have h2 := hconj s⁻¹ (R.inv_mem hsR) (s * x * s⁻¹) hx
      have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rw [e] at h2
      exact h2
  refine ⟨hPgrp, hAR, ?_⟩
  intro r hr
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hPgrp) ⟨r, hr⟩
  have hk' : r ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcomm := h.threeElement_centralizes r (hnorm r hr) ⟨k, hk'⟩
  have hc : c ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert c {d})
  have hd : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  exact ⟨mul_inv_eq_iff_eq_mul.mp (hcomm c hc), mul_inv_eq_iff_eq_mul.mp (hcomm d hd)⟩

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem cdQ2_sylow_map_eq_top (p : ℕ) [Fact p.Prime] {H K : Type} [Group H] [Finite H]
    [Group K] [Finite K] (hK : IsPGroup p K) {f : H →* K} (hf : Function.Surjective f)
    (Q : Sylow p H) : (Q : Subgroup H).map f = ⊤ := by
  have hdvd : ((Q : Subgroup H).map f).index ∣ (Q : Subgroup H).index :=
    Subgroup.index_map_dvd (Q : Subgroup H) hf
  have hnd : ¬ p ∣ ((Q : Subgroup H).map f).index := fun h' =>
    Q.not_dvd_index (h'.trans hdvd)
  obtain ⟨n, hn⟩ := hK.index ((Q : Subgroup H).map f)
  have h1 : ((Q : Subgroup H).map f).index = 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [hn, h0, pow_zero]
    · have hpd : p ∣ ((Q : Subgroup H).map f).index := by
        rw [hn]
        exact dvd_pow_self p hpos.ne'
      exact absurd hpd hnd
  exact Subgroup.index_eq_one.mp h1

theorem cdQ2_exists_mem_sylow_map (p : ℕ) [Fact p.Prime] {H K : Type} [Group H] [Finite H]
    [Group K] [Finite K] (hK : IsPGroup p K) {f : H →* K} (hf : Function.Surjective f)
    (Q : Sylow p H) (k : K) : ∃ x ∈ (Q : Subgroup H), f x = k := by
  have hk : k ∈ (Q : Subgroup H).map f := by
    rw [cdQ2_sylow_map_eq_top p hK hf Q]
    exact Subgroup.mem_top k
  exact Subgroup.mem_map.mp hk

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem cd_R_transvection (h113 : Item113) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) :
    ∀ u ∈ A, u ∉ Subgroup.closure ({c, d} : Set G) →
      ∀ b ∈ Subgroup.closure ({c, d} : Set G), ∃ r ∈ R, r * u * r⁻¹ = u * b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro u hu huB b hb
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => hAe.2 x hx
  have hcA : c ∈ A := h.mem_A
  have haA : a ∈ A := h.a_mem
  set B : Subgroup G := Subgroup.closure ({c, d} : Set G) with hBdef
  have hcB : c ∈ B := by
    rw [hBdef]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hBA : B ≤ A := by
    rw [hBdef, ← h.closure_eq]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hBp : IsPGroup 3 ↥B := fun g => ⟨1, Subtype.ext (by simpa using hexp g.1 (hBA g.2))⟩
  have hcent_iff : ∀ w : G, w ∈ Subgroup.centralizer (B : Set G) ↔
      ∀ y ∈ B, w * y * w⁻¹ = y := by
    intro w
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hw y hy
      rw [← hw y hy, mul_inv_cancel_right]
    · intro hw y hy
      exact (mul_inv_eq_iff_eq_mul.mp (hw y hy)).symm
  have hzN : ∀ w : G, w * c = c * w →
      w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro w hw
    have hfwd : ∀ v : G, v * c * v⁻¹ = c → ∀ x ∈ Subgroup.zpowers c,
        v * x * v⁻¹ ∈ Subgroup.zpowers c := by
      intro v hv x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← conj_zpow, hv]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
    have hw1 : w * c * w⁻¹ = c := by
      rw [hw]
      group
    have hw2 : w⁻¹ * c * w⁻¹⁻¹ = c := by
      rw [inv_inv, mul_assoc, ← hw, inv_mul_cancel_left]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hfwd w hw1 x
    · intro hx
      have h2 := hfwd w⁻¹ hw2 _ hx
      have e : w⁻¹ * (w * x * w⁻¹) * w⁻¹⁻¹ = x := by group
      rwa [e] at h2
  set M : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (A : Set G) with hMdef
  set W₁ : Subgroup G := M ⊓ Subgroup.centralizer (B : Set G) with hW₁def
  have hWM : ∀ w ∈ W₁, w ∈ M := fun w hw => (Subgroup.mem_inf.mp hw).1
  have hWN : ∀ w ∈ W₁, w ∈ Subgroup.normalizer (A : Set G) :=
    fun w hw => (Subgroup.mem_inf.mp (hWM w hw)).2
  have hWZ : ∀ w ∈ W₁, w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    fun w hw => (Subgroup.mem_inf.mp (hWM w hw)).1
  have hWC : ∀ w ∈ W₁, ∀ y ∈ B, w * y * w⁻¹ = y :=
    fun w hw => (hcent_iff w).mp (Subgroup.mem_inf.mp hw).2
  have hβmem : ∀ w ∈ W₁, a⁻¹ * (w * a * w⁻¹) ∈ B := by
    intro w hw
    have hh := h.conj_mem_of_mem_normalizer w⁻¹ (inv_mem (hWN w hw)) (inv_mem (hWZ w hw)) a haA
    rw [inv_inv] at hh
    exact hh
  have hβmul : ∀ w ∈ W₁, ∀ w' ∈ W₁,
      a⁻¹ * (w * w' * a * (w * w')⁻¹) = (a⁻¹ * (w * a * w⁻¹)) * (a⁻¹ * (w' * a * w'⁻¹)) := by
    intro w hw w' hw'
    have hcent : w * (a⁻¹ * (w' * a * w'⁻¹)) * w⁻¹ = a⁻¹ * (w' * a * w'⁻¹) :=
      hWC w hw _ (hβmem w' hw')
    have hw'a : w' * a * w'⁻¹ = a * (a⁻¹ * (w' * a * w'⁻¹)) := by group
    calc a⁻¹ * (w * w' * a * (w * w')⁻¹)
        = a⁻¹ * (w * (w' * a * w'⁻¹) * w⁻¹) := by group
      _ = a⁻¹ * (w * (a * (a⁻¹ * (w' * a * w'⁻¹))) * w⁻¹) := by rw [← hw'a]
      _ = a⁻¹ * ((w * a * w⁻¹) * (w * (a⁻¹ * (w' * a * w'⁻¹)) * w⁻¹)) := by group
      _ = a⁻¹ * ((w * a * w⁻¹) * (a⁻¹ * (w' * a * w'⁻¹))) := by rw [hcent]
      _ = (a⁻¹ * (w * a * w⁻¹)) * (a⁻¹ * (w' * a * w'⁻¹)) := by group
  let β : ↥W₁ →* ↥B :=
    MonoidHom.mk' (fun w => (⟨a⁻¹ * (w.1 * a * w.1⁻¹), hβmem w.1 w.2⟩ : ↥B))
      (fun w w' => Subtype.ext (hβmul w.1 w.2 w'.1 w'.2))
  have hβsurj : Function.Surjective β := by
    intro k
    obtain ⟨w, hwN, hwC, hwa⟩ := h.exists_transvection k.1 k.2
    have hwc : w * c = c * w := mul_inv_eq_iff_eq_mul.mp (hwC c hcB)
    have hwW : w ∈ W₁ := by
      rw [hW₁def, hMdef]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzN w hwc, hwN⟩, (hcent_iff w).mpr hwC⟩
    refine ⟨⟨w, hwW⟩, Subtype.ext ?_⟩
    show a⁻¹ * (w * a * w⁻¹) = k.1
    rw [hwa]
    group
  have hconj : ∀ g ∈ M, ∀ n ∈ W₁, g * n * g⁻¹ ∈ W₁ := by
    intro g hg n hn
    have hgN : g ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hg).2
    have hnM : n ∈ M := hWM n hn
    rw [hW₁def]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hnM) (inv_mem hg), ?_⟩
    rw [hcent_iff]
    intro y hy
    have hz : g⁻¹ * y * g ∈ B := by
      refine (Subgroup.mem_normalizer_iff.mp (h.normalizer_le hgN) (g⁻¹ * y * g)).mpr ?_
      rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      exact hy
    have hnz : n * (g⁻¹ * y * g) * n⁻¹ = g⁻¹ * y * g := hWC n hn _ hz
    calc g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹ = g * (n * (g⁻¹ * y * g) * n⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hnz]
      _ = y := by group
  have hNK : W₁ ≤ M := fun w hw => hWM w hw
  have hKN : M ≤ Subgroup.normalizer (W₁ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hconj g hg n hn
    · intro hn
      have h2 := hconj g⁻¹ (inv_mem hg) _ hn
      have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rw [e] at h2
      exact h2
  obtain ⟨Q, hQ⟩ := h.isSylowOf_inf.inf_of_le_normalizer hNK hKN
  obtain ⟨i, b', hb', hu_eq⟩ := exists_pow_mul_mem_closure_pair hcomm h.closure_eq hu
  have hai : ∀ j : ℕ, 3 ∣ j → a ^ j = 1 := by
    rintro j ⟨m, rfl⟩
    rw [pow_mul, hexp a haA, one_pow]
  have hi3 : ¬ 3 ∣ i := by
    intro h3
    apply huB
    rw [hu_eq, hai i h3, one_mul]
    exact hb'
  have hi3' : i % 3 ≠ 0 := fun h0 => hi3 (Nat.dvd_of_mod_eq_zero h0)
  have hmod : i * i % 3 = 1 := by
    have h3 : i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h3 with h3 | h3 <;> simp [Nat.mul_mod, h3]
  have hbpow : b ^ (i * i) = b := by
    rw [pow_eq_pow_mod (i * i) (hexp b (hBA hb)), hmod, pow_one]
  obtain ⟨x, hx, hβx⟩ :=
    cdQ2_exists_mem_sylow_map 3 hBp hβsurj Q ⟨b ^ i, Subgroup.pow_mem B hb i⟩
  have hβx' : a⁻¹ * (x.1 * a * x.1⁻¹) = b ^ i := congrArg Subtype.val hβx
  have hxmem : (x : G) ∈ (R ⊓ Subgroup.normalizer (A : Set G)) ⊓ W₁ := by
    rw [← hQ]
    exact Subgroup.mem_map_of_mem W₁.subtype hx
  have hxR : (x : G) ∈ R := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hxmem).1).1
  have hxW : (x : G) ∈ W₁ := (Subgroup.mem_inf.mp hxmem).2
  have hra : (x : G) * a * (x : G)⁻¹ = a * b ^ i := by
    rw [← hβx']
    group
  have hcomm_ab : Commute a (b ^ i) := hcomm a haA _ (hBA (Subgroup.pow_mem B hb i))
  refine ⟨(x : G), hxR, ?_⟩
  rw [hu_eq]
  calc (x : G) * (a ^ i * b') * (x : G)⁻¹
      = (x : G) * a ^ i * (x : G)⁻¹ * ((x : G) * b' * (x : G)⁻¹) := by group
    _ = ((x : G) * a * (x : G)⁻¹) ^ i * b' := by
        rw [conj_pow, hWC (x : G) hxW b' hb']
    _ = (a * b ^ i) ^ i * b' := by rw [hra]
    _ = a ^ i * (b ^ i) ^ i * b' := by rw [Commute.mul_pow hcomm_ab]
    _ = a ^ i * b ^ (i * i) * b' := by rw [← pow_mul]
    _ = a ^ i * b * b' := by rw [hbpow]
    _ = a ^ i * b' * b := by
        rw [mul_assoc, hcomm b (hBA hb) b' (hBA hb'), ← mul_assoc]

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem cdRbar_aux (x : G) {R A : Subgroup G} (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤)
    (hRx : R ≤ Subgroup.centralizer ({x} : Set G)) (hAR : A ≤ R)
    (hAgen : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}) :
    (∃ Rs : Sylow 3 (QAt x), (Rs : Subgroup (QAt x)) = cdSub x R) ∧
      (∀ z ∈ cdSub x R, z ^ 3 = 1 → z ∈ cdSub x A) ∧
      cdSub x A ≤ cdSub x R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt x)) :=
    (solvable_prime_complement_core_characterization (H := CAt x) Nat.prime_three).2.2.1
  have hinj : ∀ s : CAt x, (s : G) ∈ R → cdπ x s = 1 → s = 1 := by
    intro s hsR hs1
    have hθs : s ∈ aschbacherSolvableCore 3 (CAt x) :=
      (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 (CAt x)) s).mp hs1
    obtain ⟨k, hk⟩ := hsyl.isPGroup ⟨(s : G), hsR⟩
    have hsk : s ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : orderOf s ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hsk
    have h2 : orderOf s ∣ Nat.card (aschbacherSolvableCore 3 (CAt x)) :=
      Subgroup.orderOf_dvd_natCard _ hθs
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 (CAt x))) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hcardK : Nat.card (R.subgroupOf (Subgroup.centralizer ({x} : Set G))) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRx).toEquiv
  have hcardS : Nat.card (cdSub x R) =
      Nat.card (R.subgroupOf (Subgroup.centralizer ({x} : Set G))) := by
    have hf : Function.Bijective (fun k : R.subgroupOf (Subgroup.centralizer ({x} : Set G)) =>
        (⟨cdπ x (k : CAt x), Subgroup.mem_map_of_mem (cdπ x) k.2⟩ : cdSub x R)) := by
      refine ⟨fun k₁ k₂ hk => ?_, fun y => ?_⟩
      · have hπ : cdπ x (k₁ : CAt x) = cdπ x (k₂ : CAt x) := congrArg Subtype.val hk
        have hs1 : cdπ x ((k₁ : CAt x)⁻¹ * (k₂ : CAt x)) = 1 := by
          rw [map_mul, map_inv, hπ, inv_mul_cancel]
        have hsR : (((k₁ : CAt x)⁻¹ * (k₂ : CAt x) : CAt x) : G) ∈ R := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          exact R.mul_mem (R.inv_mem (Subgroup.mem_subgroupOf.mp k₁.2))
            (Subgroup.mem_subgroupOf.mp k₂.2)
        exact Subtype.ext (inv_mul_eq_one.mp (hinj _ hsR hs1))
      · have hy : (y : QAt x) ∈ (R.subgroupOf (Subgroup.centralizer ({x} : Set G))).map (cdπ x) :=
          y.2
        obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hf)).symm
  have hRC : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.centralizer ({x} : Set G)) :=
    hsyl.of_le hRx le_top
  have hX0 : Nat.card (QAt x) ≠ 0 := Nat.card_pos.ne'
  have hθ0 : Nat.card (aschbacherSolvableCore 3 (CAt x)) ≠ 0 := Nat.card_pos.ne'
  have hXC : Nat.card (QAt x) * Nat.card (aschbacherSolvableCore 3 (CAt x)) = Nat.card (CAt x) := by
    rw [mul_comm]
    exact Subgroup.card_mul_index (H := aschbacherSolvableCore 3 (CAt x))
  have hfac : (Nat.card (CAt x)).factorization 3 = (Nat.card (QAt x)).factorization 3 := by
    rw [← hXC, Nat.factorization_mul hX0 hθ0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ3, add_zero]
  have hKcard : Nat.card (R.subgroupOf (Subgroup.centralizer ({x} : Set G))) =
      3 ^ (Nat.card (QAt x)).factorization 3 := by
    rw [hcardK, hRC.card_eq, hfac]
  have hS : Nat.card (cdSub x R) = 3 ^ (Nat.card (QAt x)).factorization 3 := by
    rw [hcardS, hKcard]
  refine ⟨⟨Sylow.ofCard (cdSub x R) hS, rfl⟩, ?_, ?_⟩
  · intro z hz hz3
    have hz' : z ∈ (R.subgroupOf (Subgroup.centralizer ({x} : Set G))).map (cdπ x) := hz
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hz'
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have hr3 : cdπ x (r ^ 3) = 1 := by
      rw [map_pow]
      exact hz3
    have hr3' : r ^ 3 = 1 := by
      refine hinj (r ^ 3) ?_ hr3
      rw [Subgroup.coe_pow]
      exact R.pow_mem hrR 3
    have hrG : (r : G) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hr3'
    have hrA : (r : G) ∈ A := by
      rw [hAgen]
      exact Subgroup.subset_closure (show (r : G) ∈ {y | y ∈ R ∧ y ^ 3 = 1} from ⟨hrR, hrG⟩)
    show cdπ x r ∈ (A.subgroupOf (Subgroup.centralizer ({x} : Set G))).map (cdπ x)
    exact Subgroup.mem_map.mpr ⟨r, Subgroup.mem_subgroupOf.mpr hrA, rfl⟩
  · unfold cdSub
    exact Subgroup.map_mono (by
      intro y hy
      exact Subgroup.mem_subgroupOf.mpr (hAR (Subgroup.mem_subgroupOf.mp hy)))

theorem cd_Rbar_data (h113 : Item113) (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) :
    (∃ Rs : Sylow 3 (QAt (c * d)), (Rs : Subgroup (QAt (c * d))) = cdSub (c * d) R) ∧
      (∀ x ∈ cdSub (c * d) R, x ^ 3 = 1 → x ∈ cdSub (c * d) A) ∧
      cdSub (c * d) A ≤ cdSub (c * d) R := by
  obtain ⟨-, hAR, hRc⟩ := cd_R_facts h113 h hT
  have hRx : R ≤ Subgroup.centralizer ({c * d} : Set G) := by
    intro r hr
    obtain ⟨hrc, hrd⟩ := hRc r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc r * (c * d) = r * c * d := (mul_assoc _ _ _).symm
      _ = c * r * d := by rw [hrc]
      _ = c * (r * d) := mul_assoc _ _ _
      _ = c * (d * r) := by rw [hrd]
      _ = c * d * r := (mul_assoc _ _ _).symm
  have hAgen : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} :=
    (h113 G A c L a R Y (h.toSec11Std hT)).1
  exact cdRbar_aux (c * d) h.isSylowOf_top hRx hAR hAgen

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem cdSub_card_of_exp_three (x : G) (S : Subgroup G)
    (hS : S ≤ Subgroup.centralizer ({x} : Set G))
    (h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt x)))
    (hexp : ∀ g ∈ S, g ^ 3 = 1) :
    Nat.card (cdSub x S) = Nat.card S := by
  have hinj : Function.Injective
      ((cdπ x).comp (S.subgroupOf (Subgroup.centralizer ({x} : Set G))).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, hg⟩ hfg
    by_contra hne
    have hg1 : g ≠ 1 := fun h1 => hne (Subtype.ext h1)
    have hg3 : g ^ 3 = 1 :=
      Subtype.ext (by simpa using hexp (g : G) (Subgroup.mem_subgroupOf.mp hg))
    exact mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt x)) h3 hg3 hg1 hfg
  have hrange : cdSub x S =
      ((cdπ x).comp (S.subgroupOf (Subgroup.centralizer ({x} : Set G))).subtype).range := by
    unfold cdSub
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv)

theorem cdSub_exp_three_of (x : G) (S : Subgroup G) (hexp : ∀ g ∈ S, g ^ 3 = 1) :
    ∀ y ∈ cdSub x S, y ^ 3 = 1 := by
  intro y hy
  unfold cdSub at hy
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
  have hg3 : g ^ 3 = 1 :=
    Subtype.ext (by simpa using hexp (g : G) (Subgroup.mem_subgroupOf.mp hg))
  rw [← map_pow, hg3, map_one]

theorem cdSub_comm_of (x : G) (S : Subgroup G)
    (hcomm : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u) :
    ∀ y ∈ cdSub x S, ∀ z ∈ cdSub x S, y * z = z * y := by
  intro y hy z hz
  unfold cdSub at hy hz
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp hg) _ (Subgroup.mem_subgroupOf.mp hk))

theorem cdSub_eq_closure_of (x : G) (S : Subgroup G)
    (hS : S ≤ Subgroup.centralizer ({x} : Set G)) (T : Set (CAt x))
    (hT : Subgroup.closure ((Subgroup.centralizer ({x} : Set G)).subtype '' T) = S) :
    cdSub x S = Subgroup.closure (cdπ x '' T) := by
  have hmap : (Subgroup.closure T).map (Subgroup.centralizer ({x} : Set G)).subtype = S := by
    rw [MonoidHom.map_closure, hT]
  have hkey : Subgroup.closure T = S.subgroupOf (Subgroup.centralizer ({x} : Set G)) := by
    apply Subgroup.map_injective (Subgroup.centralizer ({x} : Set G)).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS]
    exact hmap
  unfold cdSub
  rw [← hkey, MonoidHom.map_closure]

theorem cd_Abar_data (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hc : c ∈ Subgroup.centralizer ({c * d} : Set G)) (hd : d ∈ Subgroup.centralizer ({c * d} : Set G))
    (ha : a ∈ Subgroup.centralizer ({c * d} : Set G)) :
    (∀ x ∈ cdSub (c * d) A, x ^ 3 = 1) ∧
    (∀ x ∈ cdSub (c * d) A, ∀ y ∈ cdSub (c * d) A, x * y = y * x) ∧
    cdπ (c * d) ⟨c, hc⟩ ∈ cdSub (c * d) A ∧ cdπ (c * d) ⟨d, hd⟩ ∈ cdSub (c * d) A ∧
    cdπ (c * d) ⟨a, ha⟩ ∈ cdSub (c * d) A ∧
    Subgroup.closure ({cdπ (c * d) ⟨c, hc⟩, cdπ (c * d) ⟨d, hd⟩, cdπ (c * d) ⟨a, ha⟩} :
      Set (QAt (c * d))) = cdSub (c * d) A ∧
    cdSub (c * d) (Subgroup.closure ({c, d} : Set G)) =
      Subgroup.closure ({cdπ (c * d) ⟨c, hc⟩, cdπ (c * d) ⟨d, hd⟩} : Set (QAt (c * d))) ∧
    Nat.card (cdSub (c * d) A) = 27 ∧ Nat.card (cdSub (c * d) (Subgroup.closure ({c, d} : Set G))) = 9 ∧
    cdπ (c * d) ⟨c, hc⟩ * cdπ (c * d) ⟨d, hd⟩ ≠ 1 ∧
    (∀ x : QAt (c * d), x * (cdπ (c * d) ⟨c, hc⟩ * cdπ (c * d) ⟨d, hd⟩) =
      (cdπ (c * d) ⟨c, hc⟩ * cdπ (c * d) ⟨d, hd⟩) * x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hEA : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  have h27 : Nat.card A = 3 ^ 3 := by rw [h.card_eq]; norm_num
  have hdA := h.d_mem
  have hcA := h.mem_A
  have haA := h.a_mem
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hexpA : ∀ g ∈ A, g ^ 3 = 1 := fun g hg => hAe.2 g hg
  have hcdA : c * d ∈ A := mul_mem hcA hdA
  have hcd1 : c * d ≠ 1 := by
    intro h1
    apply h.not_mem_zpowers
    have hd' : d = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hd']
    exact inv_mem (Subgroup.mem_zpowers c)
  have hcd3 : (c * d) ^ 3 = 1 := by
    rw [(Commute.mul_pow (show Commute c d from hcomm c hcA d hdA) 3), hc3, hd3, mul_one]
  have hAC : A ≤ Subgroup.centralizer ({c * d} : Set G) := by
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm u hu (c * d) hcdA)
  have hBA : Subgroup.closure ({c, d} : Set G) ≤ A :=
    (Subgroup.closure_le A).mpr (Set.insert_subset_iff.mpr ⟨hcA, Set.singleton_subset_iff.mpr hdA⟩)
  have hBC : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer ({c * d} : Set G) :=
    hBA.trans hAC
  have hexpB : ∀ g ∈ Subgroup.closure ({c, d} : Set G), g ^ 3 = 1 :=
    fun g hg => hexpA g (hBA hg)
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt (c * d))) :=
    (solvable_prime_complement_core_characterization (H := CAt (c * d)) Nat.prime_three).2.2.1
  have hcd9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hcA h.ne_one hdA
    h.not_mem_zpowers
  have hBeq : Subgroup.closure ({c, d} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
      · rw [hy]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
    · exact sup_le
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _)))
        (Subgroup.zpowers_le.mpr
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hB9 : Nat.card (Subgroup.closure ({c, d} : Set G)) = 9 := by
    rw [hBeq, hcd9] <;> norm_num
  have hgenA : (Subgroup.centralizer ({c * d} : Set G)).subtype ''
      ({⟨c, hc⟩, ⟨d, hd⟩, ⟨a, ha⟩} : Set (CAt (c * d))) = {c, d, a} := by
    simp [Set.image_insert_eq]
  have hgenB : (Subgroup.centralizer ({c * d} : Set G)).subtype ''
      ({⟨c, hc⟩, ⟨d, hd⟩} : Set (CAt (c * d))) = {c, d} := by
    simp [Set.image_insert_eq]
  have hz : cdπ (c * d) ⟨c, hc⟩ * cdπ (c * d) ⟨d, hd⟩ =
      cdπ (c * d) ((⟨c, hc⟩ : CAt (c * d)) * (⟨d, hd⟩ : CAt (c * d))) :=
    (map_mul (cdπ (c * d)) (⟨c, hc⟩ : CAt (c * d)) (⟨d, hd⟩ : CAt (c * d))).symm
  have hclA : Subgroup.closure ({cdπ (c * d) ⟨c, hc⟩, cdπ (c * d) ⟨d, hd⟩, cdπ (c * d) ⟨a, ha⟩} :
      Set (QAt (c * d))) = cdSub (c * d) A := by
    rw [cdSub_eq_closure_of (c * d) A hAC ({⟨c, hc⟩, ⟨d, hd⟩, ⟨a, ha⟩} : Set (CAt (c * d)))
      (by rw [hgenA]; exact h.closure_eq)] <;>
      simp only [Set.image_insert_eq, Set.image_singleton]
  have hclB : cdSub (c * d) (Subgroup.closure ({c, d} : Set G)) =
      Subgroup.closure ({cdπ (c * d) ⟨c, hc⟩, cdπ (c * d) ⟨d, hd⟩} : Set (QAt (c * d))) := by
    rw [cdSub_eq_closure_of (c * d) (Subgroup.closure ({c, d} : Set G)) hBC
      ({⟨c, hc⟩, ⟨d, hd⟩} : Set (CAt (c * d))) (by rw [hgenB])] <;>
      simp only [Set.image_insert_eq, Set.image_singleton]
  have hmemc : cdπ (c * d) ⟨c, hc⟩ ∈ cdSub (c * d) A := by
    unfold cdSub
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcA)
  have hmemd : cdπ (c * d) ⟨d, hd⟩ ∈ cdSub (c * d) A := by
    unfold cdSub
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hdA)
  have hmema : cdπ (c * d) ⟨a, ha⟩ ∈ cdSub (c * d) A := by
    unfold cdSub
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haA)
  have hcardA : Nat.card (cdSub (c * d) A) = 27 := by
    rw [cdSub_card_of_exp_three (c * d) A hAC h3 hexpA, h.card_eq]
  have hcardB : Nat.card (cdSub (c * d) (Subgroup.closure ({c, d} : Set G))) = 9 := by
    rw [cdSub_card_of_exp_three (c * d) _ hBC h3 hexpB, hB9]
  have hne1 : cdπ (c * d) ⟨c, hc⟩ * cdπ (c * d) ⟨d, hd⟩ ≠ 1 := by
    rw [hz]
    have hz3 : ((⟨c, hc⟩ : CAt (c * d)) * (⟨d, hd⟩ : CAt (c * d))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hcd3)
    have hz1 : ((⟨c, hc⟩ : CAt (c * d)) * (⟨d, hd⟩ : CAt (c * d))) ≠ 1 :=
      fun h1 => hcd1 (by simpa using congrArg Subtype.val h1)
    exact mk_ne_one_of_pow_three (aschbacherSolvableCore 3 (CAt (c * d))) h3 hz3 hz1
  have hcent : ∀ y : QAt (c * d), y * (cdπ (c * d) ⟨c, hc⟩ * cdπ (c * d) ⟨d, hd⟩) =
      (cdπ (c * d) ⟨c, hc⟩ * cdπ (c * d) ⟨d, hd⟩) * y := by
    intro y
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 (CAt (c * d))) y
    show cdπ (c * d) y0 * _ = _ * cdπ (c * d) y0
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y0.2)
  exact ⟨cdSub_exp_three_of (c * d) A hexpA, cdSub_comm_of (c * d) A hcomm, hmemc, hmemd, hmema,
    hclA, hclB, hcardA, hcardB, hne1, hcent⟩

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem cd_lift_comm (x : G) (u : CAt x) (hu : u ^ 3 = 1) (z : QAt x)
    (hz : z * cdπ x u = cdπ x u * z) :
    ∃ y : CAt x, cdπ x y = z ∧ y * u = u * y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 (CAt x)) :=
    (solvable_prime_complement_core_characterization (H := CAt x) Nat.prime_three).2.2.1
  have hZ3 : IsPGroup 3 (Subgroup.zpowers u) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hu) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hmem : z ∈ (Subgroup.centralizer ((Subgroup.zpowers u : Subgroup (CAt x)) : Set (CAt x))).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt x))) := by
    rw [CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 (aschbacherSolvableCore 3 (CAt x)) hN
      (Subgroup.zpowers u) hZ3, MonoidHom.map_zpowers, aq_centralizer_zpowers_eq,
      Subgroup.mem_centralizer_singleton_iff]
    exact hz
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hmem
  refine ⟨y, hyz, ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp hy u (Subgroup.mem_zpowers u)).symm

theorem cd_centralizers (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hc : c ∈ Subgroup.centralizer ({c * d} : Set G)) (hd : d ∈ Subgroup.centralizer ({c * d} : Set G)) :
    (∀ x : QAt (c * d), x * cdπ (c * d) ⟨c, hc⟩ = cdπ (c * d) ⟨c, hc⟩ * x →
      x * cdπ (c * d) ⟨d, hd⟩ = cdπ (c * d) ⟨d, hd⟩ * x) ∧
    (∀ x : QAt (c * d), x * cdπ (c * d) ⟨d, hd⟩ = cdπ (c * d) ⟨d, hd⟩ * x →
      x * cdπ (c * d) ⟨c, hc⟩ = cdπ (c * d) ⟨c, hc⟩ * x) := by
  have hAe := h.mem_partTwoF.1
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have hd3 : d ^ 3 = 1 := hAe.2 d h.d_mem
  have hc3' : (⟨c, hc⟩ : CAt (c * d)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hd3' : (⟨d, hd⟩ : CAt (c * d)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  constructor
  · intro x hx
    obtain ⟨y, rfl, hyc⟩ := cd_lift_comm (c * d) ⟨c, hc⟩ hc3' x hx
    have hy2 : (y : G) * (c * d) = (c * d) * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp y.2
    have hyc' : (y : G) * c = c * (y : G) := by
      have := congrArg Subtype.val hyc
      simpa using this
    have hyd : (y : G) * d = d * (y : G) := by
      have h3 := (Commute.inv_right (show Commute (y : G) c from hyc')).mul_right
        (show Commute (y : G) (c * d) from hy2)
      rw [inv_mul_cancel_left] at h3
      exact h3
    have hyd' : y * (⟨d, hd⟩ : CAt (c * d)) = (⟨d, hd⟩ : CAt (c * d)) * y := by
      apply Subtype.ext
      simpa using hyd
    rw [← map_mul, ← map_mul, hyd']
  · intro x hx
    obtain ⟨y, rfl, hyd⟩ := cd_lift_comm (c * d) ⟨d, hd⟩ hd3' x hx
    have hy2 : (y : G) * (c * d) = (c * d) * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp y.2
    have hyd' : (y : G) * d = d * (y : G) := by
      have := congrArg Subtype.val hyd
      simpa using this
    have hyc : (y : G) * c = c * (y : G) := by
      have h3 := (show Commute (y : G) (c * d) from hy2).mul_right
        (Commute.inv_right (show Commute (y : G) d from hyd'))
      rw [mul_inv_cancel_right] at h3
      exact h3
    have hyc' : y * (⟨c, hc⟩ : CAt (c * d)) = (⟨c, hc⟩ : CAt (c * d)) * y := by
      apply Subtype.ext
      simpa using hyc
    rw [← map_mul, ← map_mul, hyc']

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem cdQ6_pow_pow_self {H : Type*} [Group H] (x : H) (hx : x ^ 3 = 1) {k : ℕ}
    (hk : ¬ 3 ∣ k) : (x ^ k) ^ k = x := by
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hkk : k * k % 3 = 1 := by
    rw [Nat.mul_mod]
    rcases hk3 with h | h <;> rw [h]
  have hdiv := Nat.div_add_mod (k * k) 3
  rw [hkk] at hdiv
  rw [← pow_mul, ← hdiv, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]

theorem cdQ6_comm_iff {H : Type*} [Group H] {x g : H} (hx : x ^ 3 = 1) {k : ℕ}
    (hk : ¬ 3 ∣ k) (hg : g * x * g⁻¹ = x ^ k) (y : H) :
    y * x = x * y ↔ (g * y * g⁻¹) * x = x * (g * y * g⁻¹) := by
  have hkk := cdQ6_pow_pow_self x hx hk
  have hT : y * x = x * y ↔ (g * y * g⁻¹) * x ^ k = x ^ k * (g * y * g⁻¹) := by
    rw [← hg]
    constructor
    · intro h
      calc (g * y * g⁻¹) * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [h]
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    · intro h
      have h' : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
        calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h
          _ = g * (x * y) * g⁻¹ := by group
      simpa only [mul_left_inj, mul_right_inj] using h'
  constructor
  · intro h
    have h3 : Commute (g * y * g⁻¹) ((x ^ k) ^ k) :=
      Commute.pow_right (hT.mp h : Commute (g * y * g⁻¹) (x ^ k)) k
    rw [hkk] at h3
    exact h3
  · intro h
    exact hT.mpr (Commute.pow_right (h : Commute (g * y * g⁻¹) x) k)

theorem cdQ6_mem_zpowers {H : Type*} [Group H] {d x : H} (hd3 : d ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers d) : ∃ p : ℕ, p < 3 ∧ x = d ^ p := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hd3' : d ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hd3
  have hmod : d ^ k = d ^ (k % 3) := by
    have hk : k = k % 3 + 3 * (k / 3) := by omega
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, hd3', one_zpow, mul_one]
  have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  rw [hmod, ← zpow_natCast, Int.toNat_of_nonneg hnn]

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem cd_swap_data (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G)
    (hR1 : ResidueR1 G A c a d) (hc : c ∈ Subgroup.centralizer ({c * d} : Set G))
    (hd : d ∈ Subgroup.centralizer ({c * d} : Set G)) (ha : a ∈ Subgroup.centralizer ({c * d} : Set G)) :
    ∃ (ν : MulAut (QAt (c * d))) (i : ℕ), ¬ 3 ∣ i ∧
      ν (cdπ (c * d) ⟨c, hc⟩) = cdπ (c * d) ⟨d, hd⟩ ^ i ∧
      ν (cdπ (c * d) ⟨d, hd⟩) = cdπ (c * d) ⟨c, hc⟩ ^ i ∧
      ν (cdπ (c * d) ⟨a, ha⟩) = (cdπ (c * d) ⟨a, ha⟩)⁻¹ := by
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA : c ∈ A := h.mem_A
  have hdA : d ∈ A := h.d_mem
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcd : Commute c d := hcomm c hcA d hdA
  have hc1 : c ≠ 1 := h.ne_one
  have hd1 : d ≠ 1 := fun h1 => h.not_mem_zpowers (h1 ▸ Subgroup.one_mem _)
  obtain ⟨-, -, n, -, hnc, hnd, hna⟩ := hR1
  obtain ⟨m, -, hmc, hmd, hma⟩ :=
    TheoremO.exists_inverting_fixing (h.toSec11Std hT) h.inf_eq_zpowers h.normalizer_le
      h.isIrreducibleOn h.not_mem_zpowers
  obtain ⟨p, hp3, hpc⟩ := cdQ6_mem_zpowers hd3 hnc
  obtain ⟨q, hq3, hqd⟩ := cdQ6_mem_zpowers hc3 hnd
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply hc1
    have h1 : n * c * n⁻¹ = 1 := by rw [hpc, pow_zero]
    calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hd1
    have h1 : n * d * n⁻¹ = 1 := by rw [hqd, pow_zero]
    calc d = n⁻¹ * (n * d * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hk3 : ¬ 3 ∣ p := by omega
  obtain ⟨n', hn'c, hn'd, hn'a⟩ : ∃ n' : G, n' * c * n'⁻¹ = d ^ p ∧ n' * d * n'⁻¹ = c ^ p ∧
      n' * a * n'⁻¹ = a⁻¹ := by
    rcases (show p = q ∨ p + q = 3 by omega) with hpq | hpq
    · rw [← hpq] at hqd
      exact ⟨n, hpc, hqd, hna⟩
    · refine ⟨n * m, ?_, ?_, ?_⟩
      · rw [show n * m * c * (n * m)⁻¹ = n * (m * c * m⁻¹) * n⁻¹ by group, hmc, hpc]
      · rw [show n * m * d * (n * m)⁻¹ = n * (m * d * m⁻¹) * n⁻¹ by group, hmd,
          show n * d⁻¹ * n⁻¹ = (n * d * n⁻¹)⁻¹ by group, hqd]
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_add, show q + p = 3 by omega, hc3]
      · rw [show n * m * a * (n * m)⁻¹ = n * (m * a * m⁻¹) * n⁻¹ by group, hma, hna]
  have hcd3 : (c * d) ^ 3 = 1 := by
    rw [hcd.mul_pow, hc3, hd3, one_mul]
  have hcdp : n' * (c * d) * n'⁻¹ = (c * d) ^ p := by
    rw [show n' * (c * d) * n'⁻¹ = (n' * c * n'⁻¹) * (n' * d * n'⁻¹) by group, hn'c, hn'd,
      hcd.mul_pow]
    exact (Commute.pow_pow hcd.symm p p).eq
  have hn'C : n' ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({c * d} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact cdQ6_comm_iff hcd3 hk3 hcdp y
  obtain ⟨σ, hσ⟩ : ∃ σ : MulAut (CAt (c * d)),
      ∀ y : CAt (c * d), ((σ y : CAt (c * d)) : G) = n' * (y : G) * n'⁻¹ :=
    ⟨(Subgroup.centralizer ({c * d} : Set G)).normalizerMonoidHom ⟨n', hn'C⟩, fun y => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : MulAut (QAt (c * d)),
      ∀ y : CAt (c * d), ν (cdπ (c * d) y) = cdπ (c * d) (σ y) :=
    ⟨Sec4.thetaQuotMulAut (CAt (c * d)) σ, fun y => Sec4.thetaQuotMulAut_mk σ y⟩
  have e1 : σ ⟨c, hc⟩ = (⟨d, hd⟩ : CAt (c * d)) ^ p := by
    apply Subtype.ext
    rw [hσ]
    exact hn'c
  have e2 : σ ⟨d, hd⟩ = (⟨c, hc⟩ : CAt (c * d)) ^ p := by
    apply Subtype.ext
    rw [hσ]
    exact hn'd
  have e3 : σ ⟨a, ha⟩ = (⟨a, ha⟩ : CAt (c * d))⁻¹ := by
    apply Subtype.ext
    rw [hσ]
    exact hn'a
  refine ⟨ν, p, hk3, ?_, ?_, ?_⟩
  · rw [hν, e1, map_pow]
  · rw [hν, e2, map_pow]
  · rw [hν, e3, map_inv]

end Certified

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

theorem censusD_of (h113 : Item113) (hK1 : CyclicSylowThreeOutAbelian)
    (hcl : CensusDCentreless) : CensusD := by
  intro G _ _ A c L a R Y d h hT hR1 hS J hJ
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA : c ∈ A := h.mem_A
  have hdA : d ∈ A := h.d_mem
  have haA : a ∈ A := h.a_mem
  have hcdA : c * d ∈ A := mul_mem hcA hdA
  have hc : c ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcA (c * d) hcdA)
  have hd : d ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdA (c * d) hcdA)
  have ha : a ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a haA (c * d) hcdA)
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11⟩ :=
    cd_Abar_data h hT hc hd ha
  obtain ⟨hCcd, hCdc⟩ := cd_centralizers h hT hc hd
  obtain ⟨⟨Rs, hRs⟩, hΩ, hAR⟩ := cd_Rbar_data h113 h hT
  obtain ⟨ν, i, hi, hνc, hνd, hνa⟩ := cd_swap_data h hT hR1 hc hd ha
  obtain ⟨-, -, hRc⟩ := cd_R_facts h113 h hT
  have hX : CFSG.IsKGroup (QAt (c * d)) := cd_isKGroup h hT
  have hcl' : ∀ K : Subgroup (QAt (c * d)), CFSG.IsComponent K → Subgroup.center K = ⊥ :=
    hcl G A c L a R Y d h hT hR1 hS
  have mem_cdSub : ∀ (x : G) (S : Subgroup G) (y : QAt x), y ∈ cdSub x S ↔
      ∃ s : CAt x, (s : G) ∈ S ∧ cdπ x s = y := by
    intro x S y
    unfold cdSub
    constructor
    · intro hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨s, Subgroup.mem_subgroupOf.mp hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  have hRB : ∀ r ∈ (Rs : Subgroup (QAt (c * d))),
      ∀ b ∈ cdSub (c * d) (Subgroup.closure ({c, d} : Set G)), r * b * r⁻¹ = b := by
    intro r hr b hb
    rw [hRs] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := (mem_cdSub (c * d) R r).mp hr
    obtain ⟨b₀, hb₀, rfl⟩ := (mem_cdSub (c * d) _ b).mp hb
    have hr₀R : (r₀ : G) ∈ R := hr₀
    have hb₀B : (b₀ : G) ∈ Subgroup.closure ({c, d} : Set G) := hb₀
    have hcomm_r : ∀ g ∈ Subgroup.closure ({c, d} : Set G), (r₀ : G) * g = g * (r₀ : G) := by
      intro g hg
      have hle : Subgroup.closure ({c, d} : Set G) ≤
          Subgroup.centralizer ({(r₀ : G)} : Set G) := by
        rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hRc (r₀ : G) hr₀R).1.symm
        · rw [hx]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hRc (r₀ : G) hr₀R).2.symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
    have hcommCAt : r₀ * b₀ = b₀ * r₀ := Subtype.ext (hcomm_r _ hb₀B)
    rw [← map_mul, hcommCAt, map_mul, mul_inv_cancel_right]
  have htrans : ∀ u ∈ cdSub (c * d) A, u ∉ cdSub (c * d) (Subgroup.closure ({c, d} : Set G)) →
      ∀ b ∈ cdSub (c * d) (Subgroup.closure ({c, d} : Set G)),
        ∃ r ∈ (Rs : Subgroup (QAt (c * d))), r * u * r⁻¹ = u * b := by
    intro u hu huB b hb
    rw [hRs]
    obtain ⟨u₀, hu₀, rfl⟩ := (mem_cdSub (c * d) A u).mp hu
    obtain ⟨b₀, hb₀, rfl⟩ := (mem_cdSub (c * d) _ b).mp hb
    have hu₀A : (u₀ : G) ∈ A := hu₀
    have hu₀B : (u₀ : G) ∉ Subgroup.closure ({c, d} : Set G) := fun hB =>
      huB ((mem_cdSub (c * d) _ _).mpr ⟨u₀, hB, rfl⟩)
    have hb₀B : (b₀ : G) ∈ Subgroup.closure ({c, d} : Set G) := hb₀
    obtain ⟨r, hrR, hr⟩ := cd_R_transvection h113 h hT (u₀ : G) hu₀A hu₀B (b₀ : G) hb₀B
    have hrC : r ∈ Subgroup.centralizer ({c * d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨hrc, hrd⟩ := hRc r hrR
      calc r * (c * d) = r * c * d := (mul_assoc _ _ _).symm
        _ = c * r * d := by rw [hrc]
        _ = c * (r * d) := mul_assoc _ _ _
        _ = c * (d * r) := by rw [hrd]
        _ = c * d * r := (mul_assoc _ _ _).symm
    refine ⟨cdπ (c * d) ⟨r, hrC⟩, (mem_cdSub (c * d) R _).mpr ⟨⟨r, hrC⟩, hrR, rfl⟩, ?_⟩
    have hconj : (⟨r, hrC⟩ : CAt (c * d)) * u₀ * (⟨r, hrC⟩ : CAt (c * d))⁻¹ = u₀ * b₀ :=
      Subtype.ext hr
    have key : cdπ (c * d) ((⟨r, hrC⟩ : CAt (c * d)) * u₀ * (⟨r, hrC⟩ : CAt (c * d))⁻¹) =
        cdπ (c * d) (u₀ * b₀) := by rw [hconj]
    simpa only [map_mul, map_inv] using key
  have hΩ' : ∀ x ∈ (Rs : Subgroup (QAt (c * d))), x ^ 3 = 1 → x ∈ cdSub (c * d) A := by
    rw [hRs]
    exact hΩ
  have hAR' : cdSub (c * d) A ≤ (Rs : Subgroup (QAt (c * d))) := by
    rw [hRs]
    exact hAR
  have H : CDHyp (cdSub (c * d) A) (cdSub (c * d) (Subgroup.closure ({c, d} : Set G)))
      (Rs : Subgroup (QAt (c * d))) (cdπ (c * d) ⟨c, hc⟩) (cdπ (c * d) ⟨d, hd⟩)
      (cdπ (c * d) ⟨a, ha⟩) :=
    { A_exp := hA1
      A_comm := hA2
      cb_mem := hA3
      db_mem := hA4
      ab_mem := hA5
      A_gen := hA6
      B_def := hA7
      card_A := hA8
      card_B := hA9
      z_ne := hA10
      z_central := hA11
      R_pgroup := Rs.isPGroup'
      A_le_R := hAR'
      omega := hΩ'
      R_centralizes_B := hRB
      transvection := htrans
      C_cd := hCcd
      C_dc := hCdc }
  exact censusD_pure hK1 hX Rs H hi ν hνc hνd hνa hcl' J hJ

end Certified

end CFSG.RankThree.PartTwo.Sec11

end
