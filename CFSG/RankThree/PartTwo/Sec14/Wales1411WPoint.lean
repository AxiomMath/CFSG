module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WDefs
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ_of_invariant {A L : Subgroup G} {c : G} (hAab : IsMulCommutative A)
    (hcA : c ∈ A) (h142 : Item142 A (lB A) c L hAab hcA) {Z : Subgroup G}
    (hZ : Z ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    Z ∈ scriptQ A (lB A) := by
  obtain ⟨Q, hZQ, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))) hZ
  exact mem_scriptQ_of_le (h142 Q hQ).1.1 hZQ hZ.2.2

theorem le_k_of_delta_eq {A Y : Subgroup G} {c : G} (hYc : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hYΔ : Y = delta A (lB A) Y) : Y ≤ k142 A (lB A) c := by
  rw [hYΔ]
  exact delta_mono (hYc.trans (centralizer_singleton_le_normalizer_zpowers c))

section Sylow

variable {X : Type*} [Group X] [Finite X]

noncomputable def sylowOfMaximalIn {p : ℕ} {K R : Subgroup X} (hRK : R ≤ K) (hR : IsPGroup p R)
    (hRmax : ∀ R' : Subgroup X, R ≤ R' → R' ≤ K → IsPGroup p R' → R' = R) : Sylow p K where
  toSubgroup := R.subgroupOf K
  isPGroup' := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
  is_maximal' := fun {Q'} hQ' hle => by
    have h1 := hRmax (Q'.map K.subtype)
      (fun x hx => ⟨⟨x, hRK hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩)
      (Subgroup.map_subtype_le Q') (hQ'.map K.subtype)
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf, ← h1]
      exact ⟨y, hy, rfl⟩
    · intro hy
      exact hle hy

omit [Finite X] in
theorem conj_mem_of_smul_eq_sylow {p : ℕ} {K : Subgroup X} {T T' : Sylow p K} {k : K}
    (hk : k • T' = T) {y : K} (hy : y ∈ (T' : Subgroup K)) : k * y * k⁻¹ ∈ (T : Subgroup K) := by
  have h1 : MulAut.conj k • y ∈ ((k • T' : Sylow p K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hy
  rwa [hk, MulAut.smul_def, MulAut.conj_apply] at h1

theorem exists_mem_map_conj_eq_of_maximal_pGroup {p : ℕ} [Fact p.Prime] {K P P' : Subgroup X}
    (hPK : P ≤ K) (hP : IsPGroup p P)
    (hPmax : ∀ R : Subgroup X, P ≤ R → R ≤ K → IsPGroup p R → R = P)
    (hP'K : P' ≤ K) (hP' : IsPGroup p P')
    (hP'max : ∀ R : Subgroup X, P' ≤ R → R ≤ K → IsPGroup p R → R = P') :
    ∃ k ∈ K, P'.map (MulAut.conj k).toMonoidHom = P := by
  set T := sylowOfMaximalIn hPK hP hPmax
  set T' := sylowOfMaximalIn hP'K hP' hP'max
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K T' T
  have hk' : k⁻¹ • T = T' := by rw [← hk, inv_smul_smul]
  refine ⟨k, k.2, le_antisymm ?_ fun x hx => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := conj_mem_of_smul_eq_sylow hk (y := ⟨y, hP'K hy⟩) (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_subgroupOf.mp h1
  · have h1 := conj_mem_of_smul_eq_sylow hk' (y := ⟨x, hPK hx⟩) (Subgroup.mem_subgroupOf.mpr hx)
    refine ⟨_, Subgroup.mem_subgroupOf.mp h1, ?_⟩
    simp [mul_assoc]

end Sylow

theorem map_sylow_eq_range_of_isPGroup {X Q : Type*} [Group X] [Finite X] [Group Q] {p : ℕ}
    [Fact p.Prime] (f : X →* Q) (hf : IsPGroup p f.range) (P : Sylow p X) :
    (P : Subgroup X).map f = f.range := by
  set P' := P.mapSurjective f.rangeRestrict_surjective with hP'
  have htop : ((P' : Sylow p f.range) : Subgroup f.range) = ⊤ :=
    (P'.is_maximal' (hf.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have h1 : (P : Subgroup X).map f =
      ((P : Subgroup X).map f.rangeRestrict).map f.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, ← Sylow.coe_mapSurjective f.rangeRestrict_surjective, ← hP', htop,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Img

variable {A : Subgroup G} {c : G} [(ker142 A (lB A) c).Normal]

@[expose] noncomputable def pb (U : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))
    (Y : Subgroup G) : Subgroup G :=
  (U.comap (QuotientGroup.mk' (ker142 A (lB A) c))).map (kA142 A (lB A) c).subtype ⊓ Y

theorem mem_pb {U : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)} {Y : Subgroup G}
    {g : G} : g ∈ pb U Y ↔
      ∃ hg : g ∈ kA142 A (lB A) c, QuotientGroup.mk' (ker142 A (lB A) c) ⟨g, hg⟩ ∈ U ∧ g ∈ Y := by
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hY⟩
    exact ⟨k.2, hk, hY⟩
  · rintro ⟨hg, hU, hY⟩
    exact ⟨⟨⟨g, hg⟩, hU, rfl⟩, hY⟩

theorem mk_mem_img_A {a : G} (ha : a ∈ A) :
    QuotientGroup.mk' (ker142 A (lB A) c) ⟨a, (le_sup_right : A ≤ kA142 A (lB A) c) ha⟩ ∈
      img142 A (lB A) c A :=
  ⟨⟨a, (le_sup_right : A ≤ kA142 A (lB A) c) ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem le_normalizer_pb {U : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hAU : img142 A (lB A) c A ≤
      Subgroup.normalizer (U : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))) :
    A ≤ Subgroup.normalizer (pb U Y : Set G) := by
  intro a ha
  refine Subgroup.mem_normalizer_fintype fun g hg => ?_
  obtain ⟨hgK, hgU, hgY⟩ := mem_pb.mp hg
  have haKA : a ∈ kA142 A (lB A) c := (le_sup_right : A ≤ kA142 A (lB A) c) ha
  refine mem_pb.mpr ⟨mul_mem (mul_mem haKA hgK) (inv_mem haKA), ?_,
    (Subgroup.mem_normalizer_iff.mp (hAY ha) g).mp hgY⟩
  have h := (Subgroup.mem_normalizer_iff.mp (hAU (mk_mem_img_A ha)) _).mp hgU
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

theorem le_pb_img {X Y : Subgroup G} (hXK : X ≤ kA142 A (lB A) c) (hXY : X ≤ Y) :
    X ≤ pb (img142 A (lB A) c X) Y := fun x hx =>
  mem_pb.mpr ⟨hXK hx, ⟨⟨x, hXK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, hXY hx⟩

theorem img_map_conj {X : Subgroup G} (hX : X ≤ kA142 A (lB A) c) {n : G}
    (hn : n ∈ kA142 A (lB A) c) :
    img142 A (lB A) c (X.map (MulAut.conj n).toMonoidHom) =
      (img142 A (lB A) c X).map
        (MulAut.conj (QuotientGroup.mk' (ker142 A (lB A) c) ⟨n, hn⟩)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_subgroupOf.mp hk
    refine ⟨QuotientGroup.mk' (ker142 A (lB A) c) ⟨x, hX hx⟩,
      ⟨⟨x, hX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using hxk
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨n, hn⟩ * k * ⟨n, hn⟩⁻¹, Subgroup.mem_subgroupOf.mpr
      ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, by simp⟩, ?_⟩
    simp [map_mul, map_inv]

theorem img_le_normalizer_img {U V : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V : Set G)) :
    img142 A (lB A) c U ≤ Subgroup.normalizer
      (img142 A (lB A) c V : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := by
  have h1 : U.subgroupOf (kA142 A (lB A) c) ≤
      Subgroup.normalizer (V.subgroupOf (kA142 A (lB A) c) : Set ↥(kA142 A (lB A) c)) := by
    intro u hu
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hUV (Subgroup.mem_subgroupOf.mp hu)) v).mp hv
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

theorem isPGroup_img {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) :
    IsPGroup p (img142 A (lB A) c X) :=
  hX.comap_subtype.map _

theorem not_three_dvd_card_img {X : Subgroup G} (hXK : X ≤ kA142 A (lB A) c)
    (hX : ¬ 3 ∣ Nat.card X) : ¬ 3 ∣ Nat.card (img142 A (lB A) c X) := fun h3 => by
  apply hX
  refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]

theorem img_eq_sSup {Y : Subgroup G} (hYK : Y ≤ kA142 A (lB A) c)
    (hYΔ : Y = delta A (lB A) Y) :
    img142 A (lB A) c Y = sSup {V | V ≤ img142 A (lB A) c Y ∧
      img142 A (lB A) c A ≤ Subgroup.normalizer
        (V : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) ∧ ¬ 3 ∣ Nat.card V} := by
  set 𝒮 : Set (Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :=
    {V | V ≤ img142 A (lB A) c Y ∧ img142 A (lB A) c A ≤ Subgroup.normalizer
      (V : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) ∧ ¬ 3 ∣ Nat.card V} with h𝒮
  refine le_antisymm ?_ (sSup_le fun V hV => by rw [h𝒮] at hV; exact hV.1)
  set KA := kA142 A (lB A) c with hKA
  set M := (sSup 𝒮).comap (QuotientGroup.mk' (ker142 A (lB A) c)) with hM
  have hY : Y ≤ M.map KA.subtype := by
    refine hYΔ.le.trans (sSup_le fun Q hQ => ?_)
    have hQY : Q ≤ Y := hQ.2
    have hQ3 : ¬ 3 ∣ Nat.card Q :=
      (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    have hQ𝒮 : img142 A (lB A) c Q ∈ 𝒮 := by
      rw [h𝒮, Set.mem_setOf_eq]
      exact ⟨Subgroup.map_mono (Subgroup.comap_mono hQY), img_le_normalizer_img hQ.1.1.2.2,
        not_three_dvd_card_img (hQY.trans hYK) hQ3⟩
    intro x hx
    refine ⟨⟨x, hYK (hQY hx)⟩, ?_, rfl⟩
    exact le_sSup hQ𝒮 ⟨⟨x, hYK (hQY hx)⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [img142, Subgroup.map_le_iff_le_comap]
  intro y hy
  obtain ⟨m, hm, hmy⟩ := hY (Subgroup.mem_subgroupOf.mp hy)
  have hmy' : m = y := Subtype.ext hmy
  rw [← hmy']
  exact hm

theorem img_sup {S T : Subgroup G} (hS : S ≤ kA142 A (lB A) c) (hT : T ≤ kA142 A (lB A) c) :
    img142 A (lB A) c (S ⊔ T) = img142 A (lB A) c S ⊔ img142 A (lB A) c T := by
  rw [img142, img142, img142, Subgroup.subgroupOf_sup hS hT, Subgroup.map_sup]

end Img

structure Frame142 (A : Subgroup G) (c : G) : Prop where
  isE27 : Late.IsE27 A
  mem_A : c ∈ A
  k_le_centralizer : k142 A (lB A) c ≤ Subgroup.centralizer ({c} : Set G)
  zpow_eq_one_of_mem : ∀ i : ℤ, c ^ i ∈ k142 A (lB A) c → c ^ i = 1
  mem_scriptQ : ∀ Z : Subgroup G, Z ≤ k142 A (lB A) c →
    A ≤ Subgroup.normalizer (Z : Set G) → ¬ 3 ∣ Nat.card Z → Z ∈ scriptQ A (lB A)

namespace Frame142

variable {A : Subgroup G} {c : G} [(ker142 A (lB A) c).Normal] (f : Frame142 A c)
include f

theorem mem_pCore_of_mem {k : G} (hk : k ∈ k142 A (lB A) c)
    (hker : k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c) :
    k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  set K := k142 A (lB A) c with hKdef
  set OK := pPrimeCoreOf 3 K with hOK
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (OK : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun o ho => ?_
    have hoc : Commute o c :=
      Subgroup.mem_centralizer_singleton_iff.mp ((pPrimeCoreOf_le 3 K).trans
        f.k_le_centralizer ho)
    rw [hoc.symm.eq, mul_inv_cancel_right]
    exact ho
  have hx : k ∈ (OK : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left OK _ hcN]
    exact hker
  obtain ⟨o, ho, z, hz, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hzK : c ^ i ∈ K := by
    rw [show c ^ i = o⁻¹ * (o * c ^ i) by group]
    exact mul_mem (inv_mem (pPrimeCoreOf_le 3 K ho)) hk
  rw [f.zpow_eq_one_of_mem _ hzK]
  simpa using ho

theorem mem_zpowers_of_mem_ker {k : ↥(kA142 A (lB A) c)} (hk : k ∈ ker142 A (lB A) c) {m : ℕ}
    (hkm : k ^ 3 ^ m = 1) : (k : G) ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := k142 A (lB A) c with hKdef
  set OK := pPrimeCoreOf 3 K with hOK
  have hOKc : OK ≤ Subgroup.centralizer ({c} : Set G) :=
    (pPrimeCoreOf_le 3 K).trans f.k_le_centralizer
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (OK : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun o ho => ?_
    have hoc : Commute o c := Subgroup.mem_centralizer_singleton_iff.mp (hOKc ho)
    rw [hoc.symm.eq, mul_inv_cancel_right]
    exact ho
  have hx : (k : G) ∈ (OK : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left OK _ hcN]
    exact Subgroup.mem_subgroupOf.mp hk
  obtain ⟨o, ho, z, hz, hoz⟩ := hx
  change o * z = (k : G) at hoz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hcomm : Commute o (c ^ i) :=
    (show Commute o c from Subgroup.mem_centralizer_singleton_iff.mp (hOKc ho)).zpow_right i
  have hk' : (o * c ^ i) ^ 3 ^ m = 1 := by
    rw [hoz]
    have := congrArg Subtype.val hkm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [hcomm.mul_pow] at hk'
  have hom : o ^ 3 ^ m = 1 := by
    have h1 : o ^ 3 ^ m = ((c ^ i) ^ 3 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hk'
    have h2 : (c ^ i) ^ 3 ^ m ∈ K := by
      rw [← zpow_natCast, ← zpow_mul, show (c ^ (i * (3 ^ m : ℕ) : ℤ)) =
        (o ^ 3 ^ m)⁻¹ by rw [h1, inv_inv, ← zpow_natCast, ← zpow_mul]]
      exact inv_mem (pow_mem (pPrimeCoreOf_le 3 K ho) _)
    rw [← zpow_natCast, ← zpow_mul] at h2
    rw [h1, ← zpow_natCast, ← zpow_mul, f.zpow_eq_one_of_mem _ h2, inv_one]
  have ho1 : o = 1 := by
    have h1 : orderOf o ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hom
    have h2 : orderOf o ∣ Nat.card OK := Subgroup.orderOf_dvd_natCard OK ho
    have hcop : Nat.Coprime (3 ^ m) (Nat.card OK) :=
      Nat.Coprime.pow_left m (coprime_card_pPrimeCoreOf 3 K)
    have h3 : orderOf o ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [← hoz, ho1, one_mul]
  exact Subgroup.zpow_mem_zpowers c i

theorem not_three_dvd_card_pb {U : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (hU : IsPGroup 2 U) {Y : Subgroup G} (hYK : Y ≤ k142 A (lB A) c) :
    ¬ 3 ∣ Nat.card (pb U Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pb U Y) 3 h3
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  obtain ⟨hxK, hxU, hxY⟩ := mem_pb.mp x.2
  set k : ↥(kA142 A (lB A) c) := ⟨(x : G), hxK⟩ with hk
  have hk3 : k ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxG, pow_orderOf_eq_one]
  have hq1 : QuotientGroup.mk' (ker142 A (lB A) c) k = 1 := by
    obtain ⟨j, hj⟩ := hU ⟨_, hxU⟩
    have hj' : (QuotientGroup.mk' (ker142 A (lB A) c) k) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h3' : (QuotientGroup.mk' (ker142 A (lB A) c) k) ^ 3 = 1 := by rw [← map_pow, hk3, map_one]
    have hg : Nat.gcd 3 (2 ^ j) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2))
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3') (orderOf_dvd_of_pow_eq_one hj')
    rw [hg] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hkN : k ∈ ker142 A (lB A) c := (QuotientGroup.eq_one_iff k).mp hq1
  have hxO := f.mem_pCore_of_mem (hYK hxY) (Subgroup.mem_subgroupOf.mp hkN)
  have hdvd := Subgroup.orderOf_dvd_natCard _ hxO
  rw [hxG] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 (k142 A (lB A) c)) hdvd

theorem maximal_img
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hYK : Y ≤ k142 A (lB A) c)
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    Maximal (InvTwo (img142 A (lB A) c A) (img142 A (lB A) c Y)) (img142 A (lB A) c S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set KA := kA142 A (lB A) c with hKA
  set N := ker142 A (lB A) c with hN
  set q := QuotientGroup.mk' N with hq
  have hYKA : Y ≤ KA := hYK.trans le_sup_left
  have hSY : S ≤ Y := hS.prop.1.2
  have hSq : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSq.1.2.2
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using f.isE27.1.2 x x.2)⟩
  refine ⟨⟨Subgroup.map_mono (Subgroup.comap_mono hSY), img_le_normalizer_img hAS,
    isPGroup_img hS2⟩, fun U hU hSU => ?_⟩
  obtain ⟨hUY, hAU, hU2⟩ := hU
  set Uh := pb U Y with hUh
  have hUh3 : ¬ 3 ∣ Nat.card Uh := f.not_three_dvd_card_pb hU2 hYK
  have hAUh : A ≤ Subgroup.normalizer (Uh : Set G) := le_normalizer_pb hAY hAU
  have hSUh : S ≤ Uh := fun s hs =>
    mem_pb.mpr ⟨hYKA (hSY hs), hSU ⟨⟨s, hYKA (hSY hs)⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩,
      hSY hs⟩
  obtain ⟨S', hS'syl, hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hUh3 hAUh hSUh hS2 hAS
  have hS'Y : S' ≤ Y := hS'syl.1.trans inf_le_right
  have hS'3 : ¬ 3 ∣ Nat.card S' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS'syl.2.1
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hS'q : S' ∈ scriptQ A (lB A) := f.mem_scriptQ S' (hS'Y.trans hYK) hAS' hS'3
  have hS'S : S' = S := le_antisymm (hS.2 ⟨⟨hS'q, hS'Y⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'syl.2.1⟩ hSS') hSS'
  have hUhKA : Uh ≤ KA := inf_le_left.trans (Subgroup.map_subtype_le _)
  set f : ↥Uh →* ↥KA ⧸ N := q.comp (Subgroup.inclusion hUhKA) with hf
  have hfr : f.range = U := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨hxK, hxU, -⟩ := mem_pb.mp x.2
      exact hxU
    · intro u hu
      obtain ⟨k, hk, rfl⟩ := hUY hu
      have hkY : (k : G) ∈ Y := Subgroup.mem_subgroupOf.mp hk
      exact ⟨⟨k, mem_pb.mpr ⟨k.2, hu, hkY⟩⟩, rfl⟩
  have hmax : ∀ R : Subgroup G, S ≤ R → R ≤ Uh → IsPGroup 2 R → R = S := by
    intro R hSR hRU hR2
    rw [← hS'S]
    exact hS'syl.2.2 R hRU hR2 (hS'S ▸ hSR)
  set P := sylowOfMaximalIn (hS'S ▸ hS'syl.1) hS2 hmax with hP
  have himg := map_sylow_eq_range_of_isPGroup f (hfr ▸ hU2) P
  rw [hfr] at himg
  rw [← himg]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨Subgroup.inclusion hUhKA x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx),
    rfl⟩

theorem exists_lift {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hYK : Y ≤ kA142 A (lB A) c)
    {ñ : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c}
    (hñ : ñ ∈ img142 A (lB A) c Y ⊓ Subgroup.normalizer
      (img142 A (lB A) c A : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))) :
    ∃ n ∈ Subgroup.normalizer (A : Set G) ⊓ Y, ∃ hn : n ∈ kA142 A (lB A) c,
      ∃ a₁ ∈ img142 A (lB A) c A, ∃ a₂ ∈ img142 A (lB A) c A,
        QuotientGroup.mk' (ker142 A (lB A) c) ⟨n, hn⟩ = a₁ * ñ * a₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set KA := kA142 A (lB A) c with hKA
  set N := ker142 A (lB A) c with hN
  set q := QuotientGroup.mk' N with hq
  have hAKA : A ≤ KA := le_sup_right
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using f.isE27.1.2 x x.2)⟩
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr f.mem_A
  obtain ⟨⟨k, hk, rfl⟩, hñA⟩ := hñ
  have hyY : (k : G) ∈ Y := Subgroup.mem_subgroupOf.mp hk
  set P := pb (img142 A (lB A) c A) (Y ⊔ A) with hP
  have hAP : A ≤ P := le_pb_img hAKA le_sup_right
  set Ay := A.map (MulAut.conj (k : G)).toMonoidHom with hAy
  have hAyP : Ay ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hñA (q ⟨a, hAKA ha⟩)).mp (mk_mem_img_A ha)
    rw [← map_inv, ← map_mul, ← map_mul] at hconj
    refine mem_pb.mpr ⟨mul_mem (mul_mem k.2 (hAKA ha)) (inv_mem k.2), hconj, ?_⟩
    exact mul_mem (mul_mem (le_sup_left (a := Y) hyY) (le_sup_right (b := A) ha))
      (inv_mem (le_sup_left (a := Y) hyY))
  have hker3 : ∀ {R : Subgroup G}, IsPGroup 3 R → ∀ r ∈ R, ∀ e ∈ R, ∀ (hr : r ∈ KA)
      (he : e ∈ KA), q ⟨r, hr⟩ = q ⟨e, he⟩ → r * e⁻¹ ∈ Subgroup.zpowers c := by
    intro R hR r hr e he hrK heK hre
    have hmem : (⟨r, hrK⟩ : KA) * (⟨e, heK⟩ : KA)⁻¹ ∈ N := by
      have h1 : q ((⟨r, hrK⟩ : KA) * (⟨e, heK⟩ : KA)⁻¹) = 1 := by
        rw [map_mul, map_inv, hre, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨m, hm⟩ := hR ⟨r * e⁻¹, mul_mem hr (inv_mem he)⟩
    exact f.mem_zpowers_of_mem_ker hmem (m := m)
      (Subtype.ext (by simpa using congrArg Subtype.val hm))
  have hmaxA : ∀ R : Subgroup G, A ≤ R → R ≤ P → IsPGroup 3 R → R = A := by
    intro R hAR hRP hR3
    refine le_antisymm (fun r hr => ?_) hAR
    obtain ⟨hrK, hrA, -⟩ := mem_pb.mp (hRP hr)
    obtain ⟨⟨e, heK⟩, he, hre⟩ := hrA
    have heA : e ∈ A := Subgroup.mem_subgroupOf.mp he
    have h1 := hcA (hker3 hR3 r hr e (hAR heA) hrK heK hre.symm)
    simpa using mul_mem h1 heA
  have hcAy : Subgroup.zpowers c ≤ Ay := by
    rw [Subgroup.zpowers_le]
    refine ⟨c, f.mem_A, ?_⟩
    have hyc : (k : G) * c = c * k := Subgroup.mem_centralizer_singleton_iff.mp (hYc hyY)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hyc, mul_inv_cancel_right]
  have himgAy : img142 A (lB A) c Ay = img142 A (lB A) c A := by
    rw [hAy, img_map_conj hAKA k.2]
    exact Sec13.map_conj_eq_of_mem_normalizer hñA
  have hmaxAy : ∀ R : Subgroup G, Ay ≤ R → R ≤ P → IsPGroup 3 R → R = Ay := by
    intro R hAR hRP hR3
    refine le_antisymm (fun r hr => ?_) hAR
    obtain ⟨hrK, hrA, -⟩ := mem_pb.mp (hRP hr)
    rw [← himgAy] at hrA
    obtain ⟨⟨e, heK⟩, he, hre⟩ := hrA
    have heA : e ∈ Ay := Subgroup.mem_subgroupOf.mp he
    have h1 := hcAy (hker3 hR3 r hr e (hAR heA) hrK heK hre.symm)
    simpa using mul_mem h1 heA
  obtain ⟨p, hpP, hpA⟩ := exists_mem_map_conj_eq_of_maximal_pGroup hAP hA3 hmaxA hAyP
    (hA3.map _) hmaxAy
  have hpyN : p * k ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 : p * k * a * (p * k)⁻¹ ∈ A.map (MulAut.conj (p * (k : G))).toMonoidHom :=
      ⟨a, ha, by simp [MulAut.conj_apply, mul_assoc]⟩
    rwa [← Late.map_conj_map_conj, ← hAy, hpA] at h1
  obtain ⟨hpK, hpα, hpYA⟩ := mem_pb.mp hpP
  have hpYA' : p ∈ (Y : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y A hAY]
    exact hpYA
  obtain ⟨y₁, hy₁, a₁, ha₁, hpya⟩ := hpYA'
  change y₁ * a₁ = p at hpya
  have hnY : p * k * a₁⁻¹ ∈ Y := by
    have h1 : p * k * a₁⁻¹ = y₁ * (a₁ * k * a₁⁻¹) := by rw [← hpya]; group
    rw [h1]
    exact mul_mem hy₁ ((Subgroup.mem_normalizer_iff.mp (hAY ha₁) _).mp hyY)
  have hnK : p * k * a₁⁻¹ ∈ KA := mul_mem (mul_mem hpK k.2) (inv_mem (hAKA ha₁))
  refine ⟨p * k * a₁⁻¹, Subgroup.mem_inf.mpr ⟨mul_mem hpyN
    (inv_mem ((Subgroup.le_normalizer : A ≤ Subgroup.normalizer (A : Set G)) ha₁)), hnY⟩,
    hnK, q ⟨p, hpK⟩, hpα, (q ⟨a₁, hAKA ha₁⟩)⁻¹, inv_mem (mk_mem_img_A ha₁), ?_⟩
  rw [show (⟨p * k * a₁⁻¹, hnK⟩ : KA) = ⟨p, hpK⟩ * k * (⟨a₁, hAKA ha₁⟩ : KA)⁻¹ from
    Subtype.ext rfl, map_mul, map_mul, map_inv]

theorem isConjIn_of_img_conj
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hYK : Y ≤ k142 A (lB A) c)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2))
    {ñ : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c}
    (hñ : ñ ∈ img142 A (lB A) c Y ⊓ Subgroup.normalizer
      (img142 A (lB A) c A : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)))
    (hñT : img142 A (lB A) c T = (img142 A (lB A) c S).map (MulAut.conj ñ).toMonoidHom) :
    Late.IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set KA := kA142 A (lB A) c with hKA
  have hYKA : Y ≤ KA := hYK.trans le_sup_left
  have hSY : S ≤ Y := hS.prop.1.2
  have hTY : T ≤ Y := hT.prop.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.prop.1.1.1.2.2
  obtain ⟨n, hn, hnK, a₁, ha₁, a₂, ha₂, hna⟩ := f.exists_lift hAY hYc hYKA hñ
  set Sn := S.map (MulAut.conj n).toMonoidHom with hSn
  have himg : img142 A (lB A) c Sn = img142 A (lB A) c T := by
    rw [hSn, img_map_conj (hSY.trans hYKA) hnK, hna, ← Late.map_conj_map_conj,
      ← Late.map_conj_map_conj,
      Sec13.map_conj_eq_of_mem_normalizer (img_le_normalizer_img hAS ha₂), ← hñT,
      Sec13.map_conj_eq_of_mem_normalizer (img_le_normalizer_img hAT ha₁)]
  have hnY : n ∈ Y := (Subgroup.mem_inf.mp hn).2
  have hSnY : Sn ≤ Y := by
    rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem hnY (hSY hs)) (inv_mem hnY)
  have hSnStar : Sn ∈ scriptQPiStar A (lB A) Y (piOf 2) := by
    refine Late.maximal_map_conj (W := Subgroup.normalizer (A : Set G) ⊓ Y) (fun R hR w hw => ?_)
      hS hn
    refine ⟨⟨rank3II_14_4_5_lB (Subgroup.mem_inf.mp hw).1 hR.1.1, ?_⟩, fun p hp => hR.2 p ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      have hwY := (Subgroup.mem_inf.mp hw).2
      exact mul_mem (mul_mem hwY (hR.1.2 hr)) (inv_mem hwY)
    · rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at hp
  set Z := pb (img142 A (lB A) c T) Y with hZ
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.prop.2
  have hZY : Z ≤ Y := inf_le_right
  have hZQ : Z ∈ scriptQ A (lB A) :=
    f.mem_scriptQ Z (hZY.trans hYK) (le_normalizer_pb hAY (img_le_normalizer_img hAT))
      (f.not_three_dvd_card_pb (isPGroup_img hT2) hYK)
  have hTZ : T ≤ Z := le_pb_img (hTY.trans hYKA) hTY
  have hSnZ : Sn ≤ Z := by
    have h1 := le_pb_img (hSnY.trans hYKA) hSnY
    rwa [himg] at h1
  obtain ⟨x, hx, hxT⟩ := Proof1413Res5.isConjIn_of_le_mem_scriptQ f.isE27 hbot hZQ hZY
    hSnStar hT hSnZ hTZ
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) (Subgroup.mem_inf.mp hx).1
  refine ⟨x * n, mul_mem (Subgroup.mem_inf.mpr ⟨hxN, (Subgroup.mem_inf.mp hx).2⟩) hn, ?_⟩
  rw [hxT, hSn, Late.map_conj_map_conj]

theorem isConjIn_of_etrans2 (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hET : ETrans2 (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) (img142 A (lB A) c A))
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hYST : Y = S ⊔ T) :
    Late.IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have hCH := centralizer_singleton_le_normalizer_zpowers c
  have hSK : S ≤ k142 A (lB A) c := le_delta hS.prop.1.1 (hS.prop.1.2.trans (hYc.trans hCH))
  have hTK : T ≤ k142 A (lB A) c := le_delta hT.prop.1.1 (hT.prop.1.2.trans (hYc.trans hCH))
  have hYK : Y ≤ k142 A (lB A) c := hYST ▸ sup_le hSK hTK
  have hYimg : img142 A (lB A) c Y = img142 A (lB A) c S ⊔ img142 A (lB A) c T := by
    rw [hYST]
    exact img_sup (hSK.trans le_sup_left) (hTK.trans le_sup_left)
  have hSα := f.maximal_img hAY hYc hYK hS
  have hTα := f.maximal_img hAY hYc hYK hT
  rw [hYimg] at hSα hTα
  obtain ⟨ñ, hñ, hñT⟩ := hET _ _ hSα hTα
  rw [← hYimg] at hñ
  exact f.isConjIn_of_img_conj hbot hAY hYc hYK hS hT hñ hñT

end Frame142

end Wales1411W

namespace Res5Types.Inner142

open Wales1411W

variable {G : Type} [Group G] [Finite G]
variable {A L : Subgroup G} {c : G} [(ker142 A (lB A) c).Normal] (d : Res5Types.Inner142 A c L)
include d

theorem img_l_eq_top : img142 A (lB A) c L = ⊤ := by
  set KA := kA142 A (lB A) c with hKA
  have hK : k142 A (lB A) c ≤ KA := le_sup_left
  have hA : A ≤ KA := le_sup_right
  have htop : (k142 A (lB A) c).subgroupOf KA ⊔ A.subgroupOf KA = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK hA, Subgroup.subgroupOf_self]
  have himg : img142 A (lB A) c (k142 A (lB A) c) ⊔ img142 A (lB A) c A = ⊤ := by
    rw [img142, img142, ← Subgroup.map_sup, htop, ← MonoidHom.range_eq_map,
      QuotientGroup.range_mk']
  rw [d.img_k] at himg
  rw [← himg]
  exact (sup_eq_left.mpr d.img_A_le).symm

@[expose] noncomputable def kαEquiv :
    (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) ≃* (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr d.img_l_eq_top.symm)).trans
    d.lbarEquiv.symm

theorem map_kαEquiv_img_A :
    (img142 A (lB A) c A).map d.kαEquiv.toMonoidHom =
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
  rw [← d.bar_A, bar]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, d.img_l_eq_top ▸ Subgroup.mem_top y⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(y : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c), Subgroup.mem_subgroupOf.mp hy, ?_⟩
    rfl

theorem etrans_kα
    (hET : ETrans (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))) :
    ETrans (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) (img142 A (lB A) c A) :=
  ETrans.of_mulEquiv d.kαEquiv d.map_kαEquiv_img_A hET

theorem etrans2_kα
    (hET : ETrans2 (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))) :
    ETrans2 (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) (img142 A (lB A) c A) :=
  ETrans2.of_mulEquiv d.kαEquiv d.map_kαEquiv_img_A hET

theorem toFrame142
    (h142 : Item142 A (lB A) c L d.std.toSec13Data.isElemAbelian.1 d.std.toSec13Data.mem_A) :
    Frame142 A c where
  isE27 := d.std.isE27
  mem_A := d.std.toSec13Data.mem_A
  k_le_centralizer := d.k_le_centralizer
  zpow_eq_one_of_mem := fun _ h => d.zpow_eq_one_of_mem h
  mem_scriptQ := fun Z hZK hAZ hZ3 => mem_scriptQ_of_invariant _ _ h142
    ⟨hZK.trans (delta_le _), (isPiSubgroup_piCompl_iff Nat.prime_three Z).mpr hZ3, hAZ⟩

theorem isConjIn_of_etrans
    (h142 : Item142 A (lB A) c L d.std.toSec13Data.isElemAbelian.1 d.std.toSec13Data.mem_A)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hET : ETrans (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))))
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hYΔ : Y = delta A (lB A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    Late.IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have hYK := le_k_of_delta_eq hYc hYΔ
  have hYKA : Y ≤ kA142 A (lB A) c := hYK.trans le_sup_left
  obtain ⟨ñ, hñ, hñT⟩ := d.etrans_kα hET (img142 A (lB A) c Y) (img_le_normalizer_img hAY)
    (img_eq_sSup hYKA hYΔ) _ _ ((d.toFrame142 h142).maximal_img hAY hYc hYK hS)
    ((d.toFrame142 h142).maximal_img hAY hYc hYK hT)
  exact (d.toFrame142 h142).isConjIn_of_img_conj hbot hAY hYc hYK hS hT hñ hñT

theorem isConjIn_of_etrans2
    (h142 : Item142 A (lB A) c L d.std.toSec13Data.isElemAbelian.1 d.std.toSec13Data.mem_A)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hET : ETrans2 (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))))
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hYST : Y = S ⊔ T) :
    Late.IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T :=
  (d.toFrame142 h142).isConjIn_of_etrans2 hbot (d.etrans2_kα hET) hAY hYc hS hT hYST

end Res5Types.Inner142

end CFSG.RankThree.PartTwo.Sec14
