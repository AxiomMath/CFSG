module

public import CFSG.RankThree.Theta.TwoPlaneQuotient
public import CFSG.RankThree.Theta.TwoPlaneAlpha

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace TwoStarComponents

theorem eq_one_of_pow_two_pow_of_pow_three {M : Type*} [Group M] {z : M} {n : ℕ}
    (h2 : z ^ 2 ^ n = 1) (h3 : z ^ 3 = 1) : z = 1 := by
  have hcop : Nat.Coprime (2 ^ n) 3 :=
    Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)
  have h := pow_gcd_eq_one.2 ⟨h2, h3⟩
  rwa [hcop, pow_one] at h

theorem exists_pow_two_pow_eq_one {M : Type*} [Group M] {P : Subgroup M} (hP : IsPGroup 2 P)
    {x : M} (hx : x ∈ P) : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem pow_three_eq_one_of_mem_centralLine {X : Type*} [Group X] {c : X} (hc3 : c ^ 3 = 1)
    {z : Subgroup.centralizer ({c} : Set X)} (hz : z ∈ centralLine c) : z ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have h1 : (⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({c} : Set X)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  rw [h1, one_zpow]

section Quotient

variable {C : Type*} [Group C] (N : Subgroup C) [N.Normal]

theorem exists_two_lift (hN3 : ∀ z ∈ N, z ^ 3 = 1) (g : C) {n : ℕ}
    (hs : (QuotientGroup.mk' N g) ^ 2 ^ n = 1) :
    ∃ g' : C, g' ∈ Subgroup.zpowers g ∧ QuotientGroup.mk' N g' = QuotientGroup.mk' N g ∧
      g' ^ 2 ^ n = 1 := by
  set π := QuotientGroup.mk' N with hπ
  have hker : g ^ 2 ^ n ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_pow]
    exact hs
  have h3 : (g ^ 2 ^ n) ^ 3 = 1 := hN3 _ hker
  have hgcd : Int.gcd 3 (2 ^ n) = 1 := by
    have : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    simpa [Int.gcd] using this
  have hbez := Int.gcd_eq_gcd_ab 3 (2 ^ n)
  rw [hgcd] at hbez
  set u := Int.gcdA 3 (2 ^ n)
  set v := Int.gcdB 3 (2 ^ n)
  have hb1 : 3 * u + 2 ^ n * v = 1 := by rw [← hbez]; rfl
  refine ⟨g ^ (3 * u), Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _, ?_, ?_⟩
  · have hs' : (π g) ^ ((2 : ℤ) ^ n) = 1 := by exact_mod_cast hs
    calc π (g ^ (3 * u)) = (π g) ^ (3 * u) := map_zpow π g _
      _ = (π g) ^ (3 * u) * ((π g) ^ ((2 : ℤ) ^ n)) ^ v := by rw [hs', one_zpow, mul_one]
      _ = (π g) ^ (3 * u + 2 ^ n * v) := by rw [← zpow_mul, ← zpow_add]
      _ = π g := by rw [hb1, zpow_one]
  · have h3' : (g ^ ((2 : ℤ) ^ n * 3)) = 1 := by
      have : g ^ (2 ^ n * 3) = 1 := by rw [pow_mul]; exact h3
      exact_mod_cast this
    calc (g ^ (3 * u)) ^ 2 ^ n = g ^ (3 * u * (2 : ℤ) ^ n) := by
          rw [← zpow_natCast, ← zpow_mul]
          push_cast
          rfl
      _ = (g ^ ((2 : ℤ) ^ n * 3)) ^ u := by rw [← zpow_mul]; congr 1; ring
      _ = 1 := by rw [h3', one_zpow]

variable [Finite C]

theorem pCore_centralizer_le_map (hNc : N ≤ Subgroup.center C) (hN3 : ∀ z ∈ N, z ^ 3 = 1)
    (y : C) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({QuotientGroup.mk' N y} : Set (C ⧸ N))) ≤
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set C))).map
        (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  set D := Subgroup.centralizer ({π y} : Set (C ⧸ N)) with hD
  set Yh : Subgroup C := D.comap π with hYh
  set T : Subgroup C := inSubgroup (CFSG.pCore 2) Yh with hT
  have hyY : y ∈ Yh := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hT2 : IsPGroup 2 T := SteinbergBY.isPGroup_inSubgroup_pCore 2 Yh
  have hTY : T ≤ Yh := SteinbergBY.inSubgroup_pCore_le 2 Yh
  have hYT : Yh ≤ Subgroup.normalizer (T : Set C) :=
    SteinbergBY.le_normalizer_inSubgroup_pCore 2 Yh
  have hTcomm : ∀ t ∈ T, t * y = y * t := by
    intro t ht
    have hyt : y * t⁻¹ * y⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hYT hyY) t⁻¹).mp (T.inv_mem ht)
    set z := t * (y * t⁻¹ * y⁻¹) with hz
    have hzT : z ∈ T := T.mul_mem ht hyt
    have hzN : z ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      have htD : π t ∈ D := hTY ht
      have hcomm : π t * π y = π y * π t := Subgroup.mem_centralizer_singleton_iff.mp htD
      have hz' : π z = π t * π y * (π t)⁻¹ * (π y)⁻¹ := by
        simp only [hz, map_mul, map_inv, mul_assoc]
      rw [hz', hcomm]
      group
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one hT2 hzT
    have hz1 := eq_one_of_pow_two_pow_of_pow_three hn (hN3 z hzN)
    rw [hz] at hz1
    calc t * y = t * (y * t⁻¹ * y⁻¹) * (y * t) := by group
      _ = y * t := by rw [hz1, one_mul]
  have hTP : T ≤ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set C)) := by
    refine SteinbergBY.le_inSubgroup_pCore hT2 ?_ ?_
    · intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hTcomm t ht)
    · intro h hh
      have hhY : h ∈ Yh := by
        change π h ∈ D
        rw [hD, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp hh]
      exact hYT hhY
  rintro _ ⟨⟨s, hsD⟩, hs, rfl⟩
  have hs2 : IsPGroup 2 (CFSG.pCore 2 D) := CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hs2 ⟨⟨s, hsD⟩, hs⟩
  have hsn : s ^ 2 ^ n = 1 := by
    simpa using congrArg (fun x : CFSG.pCore 2 D => ((x : D) : C ⧸ N)) hn
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N s
  obtain ⟨g', -, hg's, hg'n⟩ := exists_two_lift N hN3 g hsn
  have hg'Y : g' ∈ Yh := by
    change π g' ∈ D
    rw [hg's]
    exact hsD
  let f : Yh →* D := (π.comp Yh.subtype).codRestrict D fun x => x.2
  have hcen : f.ker ≤ Subgroup.center Yh := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro w
    have hxN : (x : C) ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hNc hxN) w)
  have hZ2 : IsPGroup 2 (Subgroup.zpowers (⟨g', hg'Y⟩ : Yh)) := by
    have hdvd : orderOf (⟨g', hg'Y⟩ : Yh) ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hg'n))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hmapZ : (Subgroup.zpowers (⟨g', hg'Y⟩ : Yh)).map f ≤ CFSG.pCore 2 D := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    have : f ⟨g', hg'Y⟩ = ⟨π g, hsD⟩ := Subtype.ext hg's
    rw [this]
    exact hs
  have hZT := TwoPlane.le_pCore_of_map_le f hcen hZ2 hmapZ
  have hg'T : g' ∈ T := ⟨⟨g', hg'Y⟩, hZT (Subgroup.mem_zpowers _), rfl⟩
  exact ⟨g', hTP hg'T, hg's⟩

omit [Finite C] in
theorem eq_of_mk_eq (hNc : N ≤ Subgroup.center C) (hN3 : ∀ z ∈ N, z ^ 3 = 1) {u v : C}
    {a b : ℕ} (hu : u ^ 2 ^ a = 1) (hv : v ^ 2 ^ b = 1)
    (h : QuotientGroup.mk' N u = QuotientGroup.mk' N v) : u = v := by
  set z := v⁻¹ * u with hz
  have hzN : z ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, hz, map_mul, map_inv, h, inv_mul_cancel]
  have huv : u = v * z := by rw [hz, mul_inv_cancel_left]
  have hcomm : Commute v z := (Subgroup.mem_center_iff.mp (hNc hzN) v)
  have hu' : u ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, hu, one_pow]
  have hv' : v ^ 2 ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hv, one_pow]
  have hz' : z ^ 2 ^ (a + b) = 1 := by
    have h1 := hu'
    rw [huv, hcomm.mul_pow, hv', one_mul] at h1
    exact h1
  rw [huv, eq_one_of_pow_two_pow_of_pow_three hz' (hN3 z hzN), mul_one]

omit [Finite C] in
theorem map_pCore_le_pCore {K : Type*} [Group K] (f : C →* K) (hf : Function.Surjective f) :
    (CFSG.pCore 2 C).map f ≤ CFSG.pCore 2 K :=
  le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := C)).map f hf,
    (CFSG.pCore_isPGroup (p := 2) (G := C)).map f⟩

end Quotient

theorem commutator_le_of_map_le {X : Type*} [Group X] {C : Subgroup X} {K₁ K₂ K : Subgroup C}
    (h : ⁅K₁.map C.subtype, K₂.map C.subtype⁆ ≤ K.map C.subtype) : ⁅K₁, K₂⁆ ≤ K := by
  rw [← Subgroup.map_le_map_iff_of_injective C.subtype_injective, Subgroup.map_commutator]
  exact h

end TwoStarComponents

open TwoStarComponents

variable {X : Type*} [Group X] [Finite X]

theorem twoStarConditionAt_of_centralizers {A : Subgroup X}
    (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) {c : X} (hcA : c ∈ A) (hc3 : c ^ 3 = 1)
    {y₀ : X} (hy₀A : y₀ ∈ A) (hy₀c : y₀ ∉ Subgroup.zpowers c)
    (hJ : ∀ y ∈ A, y ∉ Subgroup.zpowers c →
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X) ⊓
          Subgroup.centralizer ({y} : Set X)), A⁆ ≤
        inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X)))
    (hT : ∀ u : X, (∀ y ∈ A, y ∉ Subgroup.zpowers c →
      u ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X) ⊓
          Subgroup.centralizer ({y} : Set X))) →
        u ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X))) :
    TwoStarConditionAt A c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({c} : Set X) with hC
  set N := centralLine c with hN
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hNc : N ≤ Subgroup.center C := centralLine_le_center c
  have hN3 : ∀ z ∈ N, z ^ 3 = 1 := fun z hz => pow_three_eq_one_of_mem_centralLine hc3 hz
  have hAC : A ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hPy : ∀ y : C, (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set C))).map
      C.subtype = inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({(y : X)} : Set X)) :=
    fun y => SteinbergBY.map_subtype_inSubgroup_pCore_centralizer 2 C y
  have hlift : ∀ b ∈ (A.subgroupOf C).map π, b ≠ 1 →
      ∃ y : C, (y : X) ∈ A ∧ (y : X) ∉ Subgroup.zpowers c ∧ π y = b := by
    rintro _ ⟨y, hy, rfl⟩ hb1
    refine ⟨y, hy, fun hyc => hb1 ?_, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyc
    have hyN : y ∈ N := Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hyN
  have hmapP : (CFSG.pCore 2 C).map π ≤ CFSG.pCore 2 (C ⧸ N) := map_pCore_le_pCore π hπs
  have hPc : ∀ u : C, (u : X) ∈ inSubgroup (CFSG.pCore 2) C → u ∈ CFSG.pCore 2 C := by
    rintro u ⟨w, hw, hwu⟩
    rwa [Subtype.ext hwu] at hw
  unfold TwoStarConditionAt
  rw [twoAlpha]
  refine sup_le ?_ ?_
  ·
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    obtain ⟨y, hyA, hyc, rfl⟩ := hlift b hb hb1
    refine (Subgroup.commutator_mono (pCore_centralizer_le_map N hNc hN3 y) le_rfl).trans ?_
    rw [← Subgroup.map_commutator]
    refine (Subgroup.map_mono ?_).trans hmapP
    refine commutator_le_of_map_le ?_
    rw [hPy y, Subgroup.subgroupOf_map_subtype]
    exact (Subgroup.commutator_mono le_rfl inf_le_left).trans (hJ y hyA hyc)
  ·
    intro x hx
    have hxy : ∀ y : C, (y : X) ∈ A → (y : X) ∉ Subgroup.zpowers c →
        ∃ v : C, v ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set C)) ∧
          π v = x := by
      intro y hyA hyc
      have hb : π y ∈ (A.subgroupOf C).map π := ⟨y, hyA, rfl⟩
      have hb1 : π y ≠ 1 := by
        intro h1
        apply hyc
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hxm : x ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({π y} : Set (C ⧸ N))) :=
        Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx (π y)) hb) hb1
      obtain ⟨v, hv, hvx⟩ := pCore_centralizer_le_map N hNc hN3 y hxm
      exact ⟨v, hv, hvx⟩
    obtain ⟨u, hu, hux⟩ := hxy ⟨y₀, hAC hy₀A⟩ hy₀A hy₀c
    obtain ⟨a, ha⟩ := exists_pow_two_pow_eq_one (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) hu
    have hall : ∀ y ∈ A, y ∉ Subgroup.zpowers c →
        (u : X) ∈ inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({y} : Set X)) := by
      intro y hyA hyc
      obtain ⟨v, hv, hvx⟩ := hxy ⟨y, hAC hyA⟩ hyA hyc
      obtain ⟨b, hb⟩ := exists_pow_two_pow_eq_one (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) hv
      rw [eq_of_mk_eq N hNc hN3 ha hb (hux.trans hvx.symm)]
      rw [← hPy ⟨y, hAC hyA⟩]
      exact ⟨v, hv, rfl⟩
    rw [← hux]
    exact hmapP ⟨u, hPc u (hT u hall), rfl⟩

end CFSG.RankThree.Theta
