module

public import CFSG.RankThree.PartTwo.Sec18.Item185Ctx
public import CFSG.RankThree.PartTwo.Sec18.Item185Leaves
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Transport
import CFSG.RankThree.PartTwo.Sec18.Item185O23
import CFSG.RankThree.PartTwo.Sec18.Item185Omega
import CFSG.RankThree.PartTwo.Sec18.Item185Quot
import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Lc
import CFSG.GF2Type.Smith1980Orth.S4Fixed
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem comm_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 3 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem eq_one_of_mem_pCoreOf {A : Subgroup G} (hA : IsElemAbelian 3 A) {K : Subgroup G}
    {x : G} (hxA : x ∈ A) (hxO : x ∈ CFSG.Open.pCoreOf 2 K) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨x, hxO⟩
  have h2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : x ^ 3 = 1 := hA.2 x hxA
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h4 : x ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
  rw [show Nat.gcd 3 (2 ^ k) = 1 from hcop, pow_one] at h4
  exact h4

private theorem eq_of_mk_eq_of_mem {A K : Subgroup G} (hA : IsElemAbelian 3 A) (hAK : A ≤ K)
    {x y : K} (hx : (x : G) ∈ A) (hy : (y : G) ∈ A)
    (h : QuotientGroup.mk' (CFSG.pCore 2 K) x = QuotientGroup.mk' (CFSG.pCore 2 K) y) : x = y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
  have h1 := QuotientGroup.eq.mp h
  have h2 := (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mp h1
  have h3 : (x : G)⁻¹ * (y : G) ∈ A := A.mul_mem (A.inv_mem hx) hy
  have h4 : (x : G)⁻¹ * (y : G) = 1 :=
    eq_one_of_mem_pCoreOf hA h3 (by simpa using h2)
  exact Subtype.ext (inv_mul_eq_one.mp h4)

private theorem card_map_of_injOn' {H Y : Type} [Group H] [Group Y] (S : Subgroup H)
    (f : H →* Y) (hf : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) :
    Nat.card (S.map f) = Nat.card S := by
  have hinj : Function.Injective (f.subgroupMap S) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz1 : f (z : H) = 1 := congrArg Subtype.val hz
    exact Subtype.ext (hf z z.2 1 S.one_mem (by rw [hz1, map_one]))
  have hbij : Function.Bijective (f.subgroupMap S) := ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

private theorem card_mk_map {A K : Subgroup G} (hA : IsElemAbelian 3 A) (hAK : A ≤ K)
    {S : Subgroup G} (hSA : S ≤ A) :
    Nat.card ((S.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) = Nat.card S := by
  have hf : ∀ x ∈ S.subgroupOf K, ∀ y ∈ S.subgroupOf K,
      QuotientGroup.mk' (CFSG.pCore 2 K) x = QuotientGroup.mk' (CFSG.pCore 2 K) y → x = y :=
    fun x hx y hy hxy => eq_of_mk_eq_of_mem hA hAK (hSA (Subgroup.mem_subgroupOf.mp hx))
      (hSA (Subgroup.mem_subgroupOf.mp hy)) hxy
  rw [card_map_of_injOn' _ _ hf]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hSA.trans hAK)).toEquiv

private theorem eq_of_quotAct_eq {K P : Subgroup G}
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1)
    (x y : Subgroup.normalizer (K : Set G)) (hx : (x : G) ∈ P) (hy : (y : G) ∈ P)
    (e : Sec19.SimsC198.quotAct K x = Sec19.SimsC198.quotAct K y) : (x : G) = (y : G) := by
  have hu : Sec19.SimsC198.quotAct K (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, e, inv_mul_cancel]
  have hPu : ((x⁻¹ * y : Subgroup.normalizer (K : Set G)) : G) ∈ P := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact P.mul_mem (P.inv_mem hx) hy
  have h1 := hfaith _ hPu ((Sec19.SimsC198.quotAct_eq_one_iff K _).mp hu)
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  exact inv_mul_eq_one.mp h1

private theorem mul_comm_of_quotAct_comm {K P : Subgroup G}
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1)
    (x y : Subgroup.normalizer (K : Set G)) (hx : (x : G) ∈ P) (hy : (y : G) ∈ P)
    (h : Sec19.SimsC198.quotAct K x * Sec19.SimsC198.quotAct K y =
      Sec19.SimsC198.quotAct K y * Sec19.SimsC198.quotAct K x) :
    (x : G) * (y : G) = (y : G) * (x : G) := by
  have e : Sec19.SimsC198.quotAct K (x * y) = Sec19.SimsC198.quotAct K (y * x) := by
    rw [map_mul, map_mul]
    exact h
  have h2 := eq_of_quotAct_eq hfaith (x * y) (y * x)
    (by rw [Subgroup.coe_mul]; exact P.mul_mem hx hy)
    (by rw [Subgroup.coe_mul]; exact P.mul_mem hy hx) e
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
  exact h2

private theorem quotAct_comm_of_mul_comm {K : Subgroup G} (x y : Subgroup.normalizer (K : Set G))
    (h : (x : G) * (y : G) = (y : G) * (x : G)) :
    Sec19.SimsC198.quotAct K x * Sec19.SimsC198.quotAct K y =
      Sec19.SimsC198.quotAct K y * Sec19.SimsC198.quotAct K x := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h)

private theorem quotAct_conj_eq_of_mul {K : Subgroup G} (x z : Subgroup.normalizer (K : Set G))
    {d : G} (hd : d ∈ Subgroup.normalizer (K : Set G))
    (h : (x : G) * (z : G) * (x : G)⁻¹ = d * (z : G)) :
    Sec19.SimsC198.quotAct K x * Sec19.SimsC198.quotAct K z * (Sec19.SimsC198.quotAct K x)⁻¹ =
      Sec19.SimsC198.quotAct K ⟨d, hd⟩ * Sec19.SimsC198.quotAct K z := by
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; exact h)

private theorem card_actImage_of_le {K P D : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1)
    (hDP : D ≤ P) : Nat.card (Sec19.SimsC198.actImage K D) = Nat.card D := by
  have hDN : D ≤ Subgroup.normalizer (K : Set G) := hDP.trans hPN
  have hinj : Function.Injective
      ((Sec19.SimsC198.quotAct K).subgroupMap (D.subgroupOf (Subgroup.normalizer (K : Set G)))) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz1 : Sec19.SimsC198.quotAct K (z : Subgroup.normalizer (K : Set G)) = 1 :=
      congrArg Subtype.val hz
    have hzD : ((z : Subgroup.normalizer (K : Set G)) : G) ∈ D := Subgroup.mem_subgroupOf.mp z.2
    exact Subtype.ext (Subtype.ext (hfaith _ (hDP hzD)
      ((Sec19.SimsC198.quotAct_eq_one_iff K _).mp hz1)))
  have hbij : Function.Bijective
      ((Sec19.SimsC198.quotAct K).subgroupMap (D.subgroupOf (Subgroup.normalizer (K : Set G)))) :=
    ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩
  have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Sec19.SimsC198.actImage, ← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv]

private theorem mem_actImage_of {K D : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx : x ∈ D) :
    Sec19.SimsC198.quotAct K ⟨x, hxN⟩ ∈ Sec19.SimsC198.actImage K D :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)

private theorem actImage_mono {K D D' : Subgroup G} (h : D ≤ D') :
    Sec19.SimsC198.actImage K D ≤ Sec19.SimsC198.actImage K D' := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx)))

private theorem actImage_sup {K D₁ D₂ : Subgroup G} (h₁ : D₁ ≤ Subgroup.normalizer (K : Set G))
    (h₂ : D₂ ≤ Subgroup.normalizer (K : Set G)) :
    Sec19.SimsC198.actImage K (D₁ ⊔ D₂) =
      Sec19.SimsC198.actImage K D₁ ⊔ Sec19.SimsC198.actImage K D₂ := by
  unfold Sec19.SimsC198.actImage
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

private theorem subgroupOf_zpowers_eq {K : Subgroup G} {c : G} (hc : c ∈ K) :
    (Subgroup.zpowers c).subgroupOf K = Subgroup.zpowers (⟨c, hc⟩ : K) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩

private theorem actImage_zpowers {K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) :
    Sec19.SimsC198.actImage K (Subgroup.zpowers c) =
      Subgroup.zpowers (Sec19.SimsC198.quotAct K ⟨c, hcN⟩) := by
  unfold Sec19.SimsC198.actImage
  rw [subgroupOf_zpowers_eq hcN, MonoidHom.map_zpowers]

private theorem actImage_self_eq_inner (K : Subgroup G) :
    Sec19.SimsC198.actImage K K = innerAut (K ⧸ CFSG.pCore 2 K) := by
  apply le_antisymm
  · rintro φ hφ
    obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := Subgroup.mem_map.mp hφ
    rw [Sec19.SimsC198.quotAct_conj K (Subgroup.mem_subgroupOf.mp hg) hgN]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · rintro φ hφ
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hφ
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) x
    have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
    have e := Sec19.SimsC198.quotAct_conj K k.2 hkN
    have hmem := mem_actImage_of hkN k.2
    rw [e] at hmem
    exact hmem

private theorem le_of_isSylowOf_normalizer {A P : Subgroup G} (hA : IsElemAbelian 3 A)
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G))) : A ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAN : A ≤ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer
  have hn : (A.subgroupOf (Subgroup.normalizer (A : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAN).mpr le_rfl
  obtain ⟨Q, hQ⟩ := hP
  haveI := hn
  have hle := IsPGroup.le_sylow_of_normal
    (CFSG.Open.IsElemAbelian.subgroupOf hA (Subgroup.normalizer (A : Set G))).isPGroup Q
  have e : A = (A.subgroupOf (Subgroup.normalizer (A : Set G))).map
      (Subgroup.normalizer (A : Set G)).subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAN]
  rw [← hQ]
  exact e.le.trans (Subgroup.map_mono hle)

private theorem isElemAbelian_comap_of_injective {H Y : Type} [Group H] [Group Y] {E : Subgroup Y}
    (hE : IsElemAbelian 3 E) {f : H →* Y} (hf : Function.Injective f) :
    IsElemAbelian 3 (E.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    simp only [Subgroup.coe_mul, map_mul]
    exact comm_of_elemAbelian hE (Subgroup.mem_comap.mp a.2) (Subgroup.mem_comap.mp b.2)
  · apply hf
    rw [map_pow, map_one]
    exact hE.2 (f x) (Subgroup.mem_comap.mp hx)

private theorem card_le_actImage {A M K P : Subgroup G} (hM : Sec18Std G A M)
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) (hPM : P ≤ M)
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1)
    {E : Subgroup (MulAut (K ⧸ CFSG.pCore 2 K))} (hE : E ≤ Sec19.SimsC198.actImage K P)
    (hEa : IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  let ψ : ↥P →* MulAut (K ⧸ CFSG.pCore 2 K) :=
    (Sec19.SimsC198.quotAct K).comp (Subgroup.inclusion hPN)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Sec19.SimsC198.quotAct K (⟨(x : G), hPN x.2⟩ : Subgroup.normalizer (K : Set G)) = 1 :=
      hx
    exact Subtype.ext (hfaith _ x.2 ((Sec19.SimsC198.quotAct_eq_one_iff K _).mp h1))
  have hEr : E ≤ ψ.range := by
    intro e he
    obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := Subgroup.mem_map.mp (hE he)
    exact MonoidHom.mem_range.mpr ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩
  have hmap : (E.comap ψ).map ψ = E := Subgroup.map_comap_eq_self hEr
  have hcard₁ : Nat.card E = Nat.card (E.comap ψ) := by
    have h2 : Nat.card ((E.comap ψ).map ψ) = Nat.card (E.comap ψ) :=
      Subgroup.card_map_of_injective hinj
    rwa [hmap] at h2
  have hF₁ : IsElemAbelian 3 (E.comap ψ) := isElemAbelian_comap_of_injective hEa hinj
  have hFa : IsElemAbelian 3 ((E.comap ψ).map P.subtype) :=
    CFSG.Open.IsElemAbelian.map hF₁ P.subtype
  have hFM : (E.comap ψ).map P.subtype ≤ M := (Subgroup.map_subtype_le _).trans hPM
  have hcardF : Nat.card ((E.comap ψ).map P.subtype) = Nat.card (E.comap ψ) :=
    Subgroup.card_map_of_injective P.subtype_injective
  rw [hcard₁, ← hcardF]
  exact card_le_of_le_M hM hFM hFa

private theorem sylow_actImage {K P : Subgroup G} (hPK : IsSylowOf 3 P ⊤)
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) :
    IsSylowOf 3 (Sec19.SimsC198.actImage K P)
      (Sec19.SimsC198.actImage K P ⊔ innerAut (K ⧸ CFSG.pCore 2 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPsN : IsSylowOf 3 P (Subgroup.normalizer (K : Set G)) := hPK.of_le hPN le_top
  have htop : (⊤ : Subgroup (Subgroup.normalizer (K : Set G))).map
      (Subgroup.normalizer (K : Set G)).subtype = Subgroup.normalizer (K : Set G) := by
    ext x
    simp
  have hPsub : IsSylowOf 3 (P.subgroupOf (Subgroup.normalizer (K : Set G))) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (Subgroup.normalizer (K : Set G))).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, htop, inf_of_le_left hPN]
    exact hPsN
  have hPPK : IsSylowOf 3 (P.subgroupOf (Subgroup.normalizer (K : Set G)))
      (P.subgroupOf (Subgroup.normalizer (K : Set G)) ⊔
        K.subgroupOf (Subgroup.normalizer (K : Set G))) :=
    hPsub.of_le le_sup_left le_top
  have hmap := Sec20.SimsFinalL2.isSylowOf_map_hom (Sec19.SimsC198.quotAct K) hPPK
  have hKi : Subgroup.map (Sec19.SimsC198.quotAct K)
      (K.subgroupOf (Subgroup.normalizer (K : Set G))) = innerAut (K ⧸ CFSG.pCore 2 K) :=
    actImage_self_eq_inner K
  rw [Subgroup.map_sup, hKi] at hmap
  exact hmap

private theorem not_mem_innerAut {K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hout : ¬ InducesInnerMod c K (CFSG.Open.pCoreOf 2 K)) :
    Sec19.SimsC198.quotAct K ⟨c, hcN⟩ ∉ innerAut (K ⧸ CFSG.pCore 2 K) := by
  intro hin
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hin
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) x
  rw [QuotientGroup.mk'_apply] at hx
  apply hout
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  refine ⟨hcN, (k : G), k.2, fun y hyK => ?_⟩
  have hcy : c * y * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hcN y).mp hyK
  have hw : (k : G) * y * (k : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hkN y).mp hyK
  have hx' : MulAut.conj ((k : K) : K ⧸ CFSG.pCore 2 K) ((⟨y, hyK⟩ : K) : K ⧸ CFSG.pCore 2 K) =
      Sec19.SimsC198.quotAct K ⟨c, hcN⟩ ((⟨y, hyK⟩ : K) : K ⧸ CFSG.pCore 2 K) := by
    rw [hx]
  rw [MulAut.conj_apply, Sec19.SimsC198.quotAct_mk K ⟨c, hcN⟩ ⟨y, hyK⟩ hcy] at hx'
  have hx'' : ((k * ⟨y, hyK⟩ * k⁻¹ : K) : K ⧸ CFSG.pCore 2 K) =
      (((⟨c * y * c⁻¹, hcy⟩ : K)) : K ⧸ CFSG.pCore 2 K) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hx'
  have h1 := QuotientGroup.eq.mp hx''.symm
  have h2 : (c * y * c⁻¹)⁻¹ * ((k : G) * y * (k : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 K :=
    (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mp h1
  have hO' : ((k : G) * y * (k : G)⁻¹)⁻¹ * (c * y * c⁻¹) ∈ CFSG.Open.pCoreOf 2 K := by
    have e1 : ((k : G) * y * (k : G)⁻¹)⁻¹ * (c * y * c⁻¹) =
        ((c * y * c⁻¹)⁻¹ * ((k : G) * y * (k : G)⁻¹))⁻¹ := by group
    rw [e1]
    exact (CFSG.Open.pCoreOf 2 K).inv_mem h2
  have hconj := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hw) _).mp hO'
  have e2 : (k : G) * y * (k : G)⁻¹ * (((k : G) * y * (k : G)⁻¹)⁻¹ * (c * y * c⁻¹)) *
      ((k : G) * y * (k : G)⁻¹)⁻¹ = c * y * c⁻¹ * ((k : G) * y * (k : G)⁻¹)⁻¹ := by group
  rw [e2] at hconj
  exact hconj

private theorem comm_actImage_of_normalizes {P : Subgroup G} {c : G} {K : Subgroup G}
    (hP3 : IsPGroup 3 P) (hc3 : orderOf c = 3)
    (hPz : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) (hcN : c ∈ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ Sec19.SimsC198.actImage K P,
      x * Sec19.SimsC198.quotAct K ⟨c, hcN⟩ = Sec19.SimsC198.quotAct K ⟨c, hcN⟩ * x := by
  intro φ hφ
  obtain ⟨⟨y, hyN⟩, hy, rfl⟩ := Subgroup.mem_map.mp hφ
  have hcomm := commute_of_normalizes_zpowers hP3 hc3 hPz y (Subgroup.mem_subgroupOf.mp hy)
  exact quotAct_comm_of_mul_comm ⟨y, hyN⟩ ⟨c, hcN⟩ hcomm

private theorem dichotomy_of_caseTwo {A B P : Subgroup G} {c : G} {K : Subgroup G}
    (hS : SylowFive.CaseTwo P A B c)
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1)
    (hcA : c ∈ A) :
    (∀ x ∈ Sec19.SimsC198.actImage K P,
        (∀ a ∈ Sec19.SimsC198.actImage K A, x * a = a * x) → x ∈ Sec19.SimsC198.actImage K A) ∧
      ∀ b ∈ Sec19.SimsC198.actImage K B, ∃ x ∈ Sec19.SimsC198.actImage K P ⊓
          Subgroup.centralizer (Sec19.SimsC198.actImage K B : Set (MulAut (K ⧸ CFSG.pCore 2 K))),
        x * Sec19.SimsC198.quotAct K ⟨c, hcN⟩ * x⁻¹ = b * Sec19.SimsC198.quotAct K ⟨c, hcN⟩ := by
  have hAP : A ≤ P := hS.le_sylow
  have hBA : B ≤ A := hS.le
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAP.trans hPN
  constructor
  · intro φ hφ hcomm
    obtain ⟨⟨y, hyN⟩, hy, rfl⟩ := Subgroup.mem_map.mp hφ
    have hyP : y ∈ P := Subgroup.mem_subgroupOf.mp hy
    have hyA : y ∈ A := by
      refine hS.mem_of_commute y hyP (fun a ha => ?_)
      exact mul_comm_of_quotAct_comm hfaith ⟨y, hyN⟩ ⟨a, hAN ha⟩ hyP (hAP ha)
        (hcomm _ (mem_actImage_of (hAN ha) ha))
    exact mem_actImage_of hyN hyA
  · intro b' hb'
    obtain ⟨⟨d, hdN⟩, hd, rfl⟩ := Subgroup.mem_map.mp hb'
    have hdB : d ∈ B := Subgroup.mem_subgroupOf.mp hd
    obtain ⟨y, hy, hyc⟩ := hS.exists_conj_eq d hdB
    have hyP : y ∈ P := (Subgroup.mem_inf.mp hy).1
    have hyB : ∀ e ∈ B, e * y = y * e := fun e he =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 e he
    have hyN : y ∈ Subgroup.normalizer (K : Set G) := hPN hyP
    refine ⟨Sec19.SimsC198.quotAct K ⟨y, hyN⟩, ⟨mem_actImage_of hyN hyP, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr (fun β hβ => ?_)
      obtain ⟨⟨e, heN⟩, he, rfl⟩ := Subgroup.mem_map.mp (SetLike.mem_coe.mp hβ)
      exact quotAct_comm_of_mul_comm ⟨e, heN⟩ ⟨y, hyN⟩ (hyB e (Subgroup.mem_subgroupOf.mp he))
    · exact quotAct_conj_eq_of_mul ⟨y, hyN⟩ ⟨c, hcN⟩ hdN hyc

theorem outerData_of {A M H : Subgroup G} {c : G} {P : Subgroup G}
    (hC : Ctx G A M H c P) {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hWK : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hBK : A ⊓ inSubgroup perfectResidual H ≤ K)
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1)
    (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hout : ¬ InducesInnerMod c K (CFSG.Open.pCoreOf 2 K))
    (hΩ : A ⊓ inSubgroup perfectResidual H ≤
      (Sec4.oTwoP 3 ↥(M ⊓ Subgroup.centralizer ({c} : Set G))).map
        (M ⊓ Subgroup.centralizer ({c} : Set G)).subtype) :
    OuterData (K ⧸ CFSG.pCore 2 K) (Sec19.SimsC198.actImage K P) (Sec19.SimsC198.actImage K A)
      (Sec19.SimsC198.actImage K (A ⊓ inSubgroup perfectResidual H))
      (Sec19.SimsC198.quotAct K ⟨c, hcN⟩) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : Sec18Std G A M := hC.toSec18H.toSec18Std
  have hA : IsElemAbelian 3 A := hC.planeQ8.isElemAbelian
  have hAP : A ≤ P := le_of_isSylowOf_normalizer hA hC.sylow_W
  have hPN : P ≤ Subgroup.normalizer (K : Set G) := hC.sylow_W.le.trans hWK
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAP.trans hPN
  have hPM : P ≤ M := hC.sylow_W.le.trans
    ((normalizer_le_gamma le_rfl (two_le_pRank_of_elemAbelian hA
      (by rw [hC.planeQ8.card_eq]; norm_num))).trans hC.mem_scriptM.2)
  have hBA : A ⊓ inSubgroup perfectResidual H ≤ A := inf_le_left
  have hBP : A ⊓ inSubgroup perfectResidual H ≤ P := hBA.trans hAP
  have hcA : c ∈ A := hC.planeQ8.mem
  have hcAP : c ∈ P := hAP hcA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hc1 : c ≠ 1 := fun h => hC.planeQ8.not_mem (by rw [h]; exact one_mem _)
  have hc3ord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  exact
    { isPGroup := (sylow_actImage hC.sylow_G hPN).isPGroup
      sylow := sylow_actImage hC.sylow_G hPN
      card_le := fun E hE hEa => card_le_actImage hM hPN hPM hfaith hE hEa
      isElemAbelian := CFSG.Open.IsElemAbelian.map
        (CFSG.Open.IsElemAbelian.subgroupOf hA (Subgroup.normalizer (K : Set G)))
        (Sec19.SimsC198.quotAct K)
      card_A := (card_actImage_of_le hPN hfaith hAP).trans hC.planeQ8.card_eq
      le_P := actImage_mono hAP
      le_B := actImage_mono hBA
      card_B := (card_actImage_of_le hPN hfaith hBP).trans hC.planeQ8.card_plane
      eq_sup := by
        have e := congrArg (Sec19.SimsC198.actImage K) hC.planeQ8.eq_sup
        rw [e, actImage_sup (Subgroup.zpowers_le.mpr hcN) (hBA.trans hAN), actImage_zpowers hcN]
      not_mem := by
        intro hmem
        obtain ⟨d, hdN, hdB, hd⟩ := Sec19.SimsC198.mem_actImage hmem
        have hdP : d ∈ P := hBP hdB
        have hdc : d = c := eq_of_quotAct_eq hfaith ⟨d, hdN⟩ ⟨c, hcN⟩ hdP hcAP hd
        exact hC.planeQ8.not_mem (by rw [← hdc]; exact hdB)
      le_inner := (actImage_mono hBK).trans (actImage_self_eq_inner K).le
      dichotomy := by
        rcases hC.dichotomy with hWc | hS
        · exact Or.inl (comm_actImage_of_normalizes hC.sylow_G.isPGroup hc3ord
            (hC.sylow_W.le.trans hWc) hPN hcN)
        · exact Or.inr (dichotomy_of_caseTwo hS hPN hcN hfaith hcA)
      omega := omega_quot hK hBK hcN hc3 hΩ
      outer := not_mem_innerAut hcN hout }

private theorem mem_normalizer_of_comm {X : Type} [Group X] {H : Subgroup X} {g : X}
    (hg : ∀ h ∈ H, g * h = h * g) : g ∈ Subgroup.normalizer (H : Set X) := by
  have hgi : ∀ k ∈ H, g⁻¹ * k = k * g⁻¹ := fun k hk => by
    calc g⁻¹ * k = g⁻¹ * (k * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * k) * g⁻¹ := by rw [← hg k hk]
      _ = k * g⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hg h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have e := hgi _ hh
    have e2 : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g * h * g⁻¹ * g⁻¹ * g := by rw [e]
        _ = g * h * g⁻¹ := by group
    rw [e2]
    exact hh

private theorem mk_mem_normalizer_map {K B : Subgroup G} {m : K}
    (hm : (m : G) ∈ Subgroup.normalizer (B : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 K) m ∈
      Subgroup.normalizer (((B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :
        Subgroup (K ⧸ CFSG.pCore 2 K)) : Set (K ⧸ CFSG.pCore 2 K)) := by
  have hmS : m ∈ Subgroup.normalizer ((B.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have e : ((m * h * m⁻¹ : K) : G) = (m : G) * (h : G) * (m : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hm (h : G)
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 K))
    (Subgroup.mem_map_of_mem _ hmS)

private theorem omega_inner {M K B : Subgroup G} {c : G} (hKM : K ≤ M) (hBK : B ≤ K)
    (hcK : c ∈ K) (hc3 : c ^ 3 = 1)
    (hΩ : B ≤ (Sec4.oTwoP 3 ↥(M ⊓ Subgroup.centralizer ({c} : Set G))).map
      (M ⊓ Subgroup.centralizer ({c} : Set G)).subtype) :
    (B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
      (Sec4.oTwoP 3 ↥(Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)} :
        Set (K ⧸ CFSG.pCore 2 K)))).map
        (Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)} :
          Set (K ⧸ CFSG.pCore 2 K))).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYX : K ⊓ Subgroup.centralizer ({c} : Set G) ≤ M ⊓ Subgroup.centralizer ({c} : Set G) :=
    le_inf (inf_le_left.trans hKM) inf_le_right
  have hBC : B ≤ Subgroup.centralizer ({c} : Set G) := fun b hb => by
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp (hΩ hb)
    exact t.2.2
  have hΩ' : B ≤ (Sec4.oTwoP 3 ↥(K ⊓ Subgroup.centralizer ({c} : Set G))).map
      (K ⊓ Subgroup.centralizer ({c} : Set G)).subtype := fun b hb =>
    inf_oTwoP_le hYX ⟨hΩ hb, (⟨hBK hb, hBC hb⟩ : b ∈ K ⊓ Subgroup.centralizer ({c} : Set G))⟩
  have hYK : K ⊓ Subgroup.centralizer ({c} : Set G) ≤ K := inf_le_left
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hcK
  let g : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)) →* K ⧸ CFSG.pCore 2 K :=
    (QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hYK)
  have hgfix : ∀ y : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)),
      g y ∈ Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)} :
        Set (K ⧸ CFSG.pCore 2 K)) := by
    rintro ⟨y, hy⟩
    have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    show QuotientGroup.mk' (CFSG.pCore 2 K) (⟨y, hy.1⟩ : K) *
        QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K) =
      QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K) *
        QuotientGroup.mk' (CFSG.pCore 2 K) (⟨y, hy.1⟩ : K)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyc
  have hcinv3 : (c⁻¹) ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  have hcinvN : c⁻¹ ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) :=
    inv_mem (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hcN)
  have hcinvnorm : ∀ h ∈ CFSG.Open.pCoreOf 2 K,
      c⁻¹ * h * (c⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
    fun h hh => (Subgroup.mem_normalizer_iff.mp hcinvN h).mp hh
  have hpO : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hgsurj : Function.Surjective (g.codRestrict _ hgfix) := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) z
    have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hz'
    have hO := (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mp
      (QuotientGroup.eq.mp hz'.symm)
    have hxc : (x : G)⁻¹ * (c⁻¹ * (x : G) * (c⁻¹)⁻¹) ∈ CFSG.Open.pCoreOf 2 K := by
      have e : (x : G)⁻¹ * (c⁻¹ * (x : G) * (c⁻¹)⁻¹) = (c * (x : G))⁻¹ * ((x : G) * c) := by
        group
      rw [e]
      exact hO
    obtain ⟨h, hh, hfix⟩ :=
      CFSG.GF2Type.Smith1980Orth.exists_fixed_mem_coset hpO hcinv3 hcinvnorm hxc
    have hyc : (x : G) * h * c = c * ((x : G) * h) := by
      calc (x : G) * h * c = c * (c⁻¹ * ((x : G) * h) * (c⁻¹)⁻¹) := by group
        _ = c * ((x : G) * h) := by rw [hfix]
    have hyK : (x : G) * h ∈ K := K.mul_mem x.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 K hh)
    refine ⟨⟨(x : G) * h, ⟨hyK, Subgroup.mem_centralizer_singleton_iff.mpr hyc⟩⟩, ?_⟩
    apply Subtype.ext
    show QuotientGroup.mk' (CFSG.pCore 2 K) (⟨(x : G) * h, hyK⟩ : K) =
      QuotientGroup.mk' (CFSG.pCore 2 K) x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    apply QuotientGroup.eq.mpr
    apply (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mpr
    show ((x : G) * h)⁻¹ * (x : G) ∈ CFSG.Open.pCoreOf 2 K
    have e2 : ((x : G) * h)⁻¹ * (x : G) = h⁻¹ := by group
    rw [e2]
    exact inv_mem hh
  have hP := oTwoP_map_le_of_surjective (g.codRestrict _ hgfix) hgsurj
  intro b' hb'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb'
  obtain ⟨z, hz, hzk⟩ := Subgroup.mem_map.mp (hΩ' (Subgroup.mem_subgroupOf.mp hk))
  refine Subgroup.mem_map.mpr ⟨g.codRestrict _ hgfix z, hP (Subgroup.mem_map_of_mem _ hz), ?_⟩
  show QuotientGroup.mk' (CFSG.pCore 2 K) (Subgroup.inclusion hYK z) =
    QuotientGroup.mk' (CFSG.pCore 2 K) k
  congr 1
  exact Subtype.ext hzk

theorem false_of_inner {A M H : Subgroup G} {c : G} {P : Subgroup G}
    (hC : Ctx G A M H c P) (hIn : LeafInner) {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hWK : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hAK : A ≤ K)
    (hfaith : ∀ x ∈ P, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → x = 1)
    (hΩ : A ⊓ inSubgroup perfectResidual H ≤
      (Sec4.oTwoP 3 ↥(M ⊓ Subgroup.centralizer ({c} : Set G))).map
        (M ⊓ Subgroup.centralizer ({c} : Set G)).subtype) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hM : Sec18Std G A M := hC.toSec18H.toSec18Std
  have hA : IsElemAbelian 3 A := hC.planeQ8.isElemAbelian
  have hA3 : IsPGroup 3 A := CFSG.Open.IsElemAbelian.isPGroup hA
  have hAP : A ≤ P := le_of_isSylowOf_normalizer hA hC.sylow_W
  have hBA : A ⊓ inSubgroup perfectResidual H ≤ A := inf_le_left
  have hBK : A ⊓ inSubgroup perfectResidual H ≤ K := hBA.trans hAK
  have hcA : c ∈ A := hC.planeQ8.mem
  have hcK : c ∈ K := hAK hcA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hKM : K ≤ M := by
    obtain ⟨L, -, hL⟩ := hK
    rw [← hL]
    exact Subgroup.map_subtype_le L
  have hAeab : IsElemAbelian 3 ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hA K)
      (QuotientGroup.mk' (CFSG.pCore 2 K))
  have hAcard : Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) = 27 :=
    (card_mk_map hA hAK le_rfl).trans hC.planeQ8.card_eq
  have hBAhat : ((A ⊓ inSubgroup perfectResidual H).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
        (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (hBA (Subgroup.mem_subgroupOf.mp hk)))
  have hBcard : Nat.card (((A ⊓ inSubgroup perfectResidual H).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 K))) = 9 :=
    (card_mk_map hA hAK hBA).trans hC.planeQ8.card_plane
  have hsup : (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) =
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)) ⊔
        ((A ⊓ inSubgroup perfectResidual H).subgroupOf K).map
          (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
    have e : (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) =
        ((Subgroup.zpowers c ⊔ (A ⊓ inSubgroup perfectResidual H)).subgroupOf K).map
          (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
      rw [← hC.planeQ8.eq_sup]
    rw [e, Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hcK) hBK, Subgroup.map_sup,
      subgroupOf_zpowers_eq hcK, MonoidHom.map_zpowers]
  have hcB : QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K) ∉
      ((A ⊓ inSubgroup perfectResidual H).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
    intro hmem
    obtain ⟨k, hk, hkc⟩ := Subgroup.mem_map.mp hmem
    have hkB : (k : G) ∈ A ⊓ inSubgroup perfectResidual H := Subgroup.mem_subgroupOf.mp hk
    have e := eq_of_mk_eq_of_mem hA hAK (x := (⟨c, hcK⟩ : K)) (y := k) hcA (hBA hkB) hkc.symm
    apply hC.planeQ8.not_mem
    have hck : c = (k : G) := congrArg Subtype.val e
    rw [hck]
    exact hkB
  have hcenter : (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) ⊓
      Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    obtain ⟨hxA, hxZ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hxA
    have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hcomm : ∀ m ∈ K, (a : G)⁻¹ * m * (a : G) * m⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
      intro m hm
      have hk : m⁻¹ ∈ K := K.inv_mem hm
      have hz := Subgroup.mem_center_iff.mp hxZ
        (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨m⁻¹, hk⟩ : K))
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hz
      have h2 := (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mp
        (QuotientGroup.eq.mp hz)
      have e : ((((⟨m⁻¹, hk⟩ : K) * a)⁻¹ * (a * (⟨m⁻¹, hk⟩ : K)) : K) : G) =
          (a : G)⁻¹ * m * (a : G) * m⁻¹ := by
        show ((m⁻¹ : G) * (a : G))⁻¹ * ((a : G) * m⁻¹) = (a : G)⁻¹ * m * (a : G) * m⁻¹
        group
      rw [← e]
      exact h2
    have hconj : ∀ k ∈ K, (a : G)⁻¹ * k * ((a : G)⁻¹)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
      intro k hk
      rw [inv_inv]
      exact hcomm k hk
    have h1 : (a : G)⁻¹ = 1 := hfaith _ (P.inv_mem (hAP ha')) hconj
    have ha0 : (a : G) = 1 := inv_eq_one.mp h1
    have ha1 : a = 1 := Subtype.ext ha0
    rw [Subgroup.mem_bot]
    simp [ha1]
  have hnorm : Subgroup.normalizer (((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :
      Subgroup (K ⧸ CFSG.pCore 2 K)) : Set (K ⧸ CFSG.pCore 2 K)) ≤
      Subgroup.normalizer ((((A ⊓ inSubgroup perfectResidual H).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 K)) : Subgroup (K ⧸ CFSG.pCore 2 K)) :
        Set (K ⧸ CFSG.pCore 2 K)) := by
    intro x hx
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) x
    obtain ⟨y, hy, m, hm, rfl⟩ := Sec20.exists_mul_of_mk_mem_normalizer hAK hA3 hx
    have hy' : QuotientGroup.mk' (CFSG.pCore 2 K) y ∈ Subgroup.normalizer
        ((((A ⊓ inSubgroup perfectResidual H).subgroupOf K).map
          (QuotientGroup.mk' (CFSG.pCore 2 K)) : Subgroup (K ⧸ CFSG.pCore 2 K)) :
          Set (K ⧸ CFSG.pCore 2 K)) := by
      obtain ⟨b, hb, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      have ho1 : QuotientGroup.mk' (CFSG.pCore 2 K) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
      rw [map_mul, ho1, mul_one]
      refine mem_normalizer_of_comm ?_
      intro h hh
      exact comm_of_elemAbelian (G := K ⧸ CFSG.pCore 2 K) hAeab
        (Subgroup.mem_map_of_mem _ hb) (hBAhat hh)
    rw [map_mul]
    exact mul_mem hy' (mk_mem_normalizer_map (hC.normalizer_le hm))
  have hΩX := omega_inner hKM hBK hcK hc3 hΩ
  exact hIn (K ⧸ CFSG.pCore 2 K) (rankHyp_of_mem hM hK) _ _ _ hAeab hAcard hBAhat hBcard
    hsup hcB hcenter hnorm hΩX

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
