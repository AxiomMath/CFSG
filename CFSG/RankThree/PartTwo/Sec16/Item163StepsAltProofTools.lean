module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16.Step163Alt

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec15
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)
open Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_two_iff {Y : Subgroup G} (y : ↥Y) :
    y ∈ CFSG.pCore 2 ↥Y ↔ (y : G) ∈ CFSG.Open.pCoreOf 2 Y := (CFSG.mem_openPCoreOf_iff y).symm

omit [Finite G] in
theorem mk_eq_mk_iff {Y : Subgroup G} (y y' : ↥Y) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y = QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y') ↔
      (y : G)⁻¹ * y' ∈ CFSG.Open.pCoreOf 2 Y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_pCore_two_iff]
  rfl

noncomputable def conjQuotTwo (Y : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥Y) (CFSG.pCore 2 ↥Y) (Y.normalizerMonoidHom ⟨x, hx⟩)
    (by rw [← MulEquiv.toMonoidHom_eq_coe]; exact CFSG.pCore_map_iso 2 _)

omit [Finite G] in
theorem conjQuotTwo_mk (Y : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (Y : Set G))
    (y : ↥Y) : conjQuotTwo Y hx (y : ↥Y ⧸ CFSG.pCore 2 ↥Y) =
      ((⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y).mp y.2⟩ : ↥Y) :
        ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  rw [conjQuotTwo, QuotientGroup.congr_mk]
  rfl

omit [Finite G] in
theorem conjQuotTwo_pow_three (Y : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : x ^ 3 = 1) : conjQuotTwo Y hx ^ 3 = 1 := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H k =>
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, conjQuotTwo_mk, conjQuotTwo_mk,
      conjQuotTwo_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only
    have hx3' : x * x * x = 1 := by rw [← pow_three', hx3]
    calc x * (x * (x * (k : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * k * (x * x * x)⁻¹ := by
          group
      _ = k := by rw [hx3']; group

theorem center_eq_bot_of_ten {X : Type*} [Group X] (φ : X ≃* alternatingGroup (Fin 10)) :
    Subgroup.center X = ⊥ := by
  have h4 : 4 ≤ Nat.card (Fin 10) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hZ : Subgroup.center (alternatingGroup (Fin 10)) = ⊥ := alternatingGroup.center_eq_bot h4
  refine le_bot_iff.mp fun x hx => ?_
  have hφx : φ x ∈ Subgroup.center (alternatingGroup (Fin 10)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [hZ, Subgroup.mem_bot] at hφx
  rw [Subgroup.mem_bot]
  exact φ.injective (hφx.trans (map_one φ).symm)

theorem exists_conj_of_pow_three_ten {X : Type*} [Group X] [Finite X]
    (φ : X ≃* alternatingGroup (Fin 10)) (σ : MulAut X) (hσ : σ ^ 3 = 1) :
    ∃ x : X, σ = MulAut.conj x := by
  have hZ := center_eq_bot_of_ten φ
  have hcardAut : Nat.card (MulAut (alternatingGroup (Fin 10))) = 3628800 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
        (by norm_num))).toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hXc : Nat.card X = 1814400 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2
  have hAut : Nat.card (MulAut X) ≤ 2 * Nat.card X := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv, hcardAut, hXc]
  exact CFSG.RankThree.PartTwo.KFacts.KS14.exists_conj_of_card_mulAut_le hZ hAut σ
    ⟨1, by rwa [pow_one]⟩

omit [Finite G] in
theorem isElemAbelian_map_hom {X X' : Type*} [Group X] [Group X'] {p : ℕ} {H : Subgroup X}
    (j : X →* X') (hH : CFSG.Assembly.IsElemAbelian p H) :
    CFSG.Assembly.IsElemAbelian p (H.map j) := CFSG.Open.IsElemAbelian.map hH _

omit [Finite G] in
theorem isElemAbelian_of_map_hom {X X' : Type*} [Group X] [Group X'] {p : ℕ} {H : Subgroup X}
    (j : X →* X') (hj : ∀ h ∈ H, j h = 1 → h = 1)
    (hH : CFSG.Assembly.IsElemAbelian p (H.map j)) : CFSG.Assembly.IsElemAbelian p H := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have hc := congrArg Subtype.val (hH.1.is_comm.comm ⟨j a, a, a.2, rfl⟩ ⟨j b, b, b.2, rfl⟩)
    change j a * j b = j b * j a at hc
    have h1 : j ((a : X) * b * ((b : X) * a)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
    have h2 := hj _ (H.mul_mem (H.mul_mem a.2 b.2) (H.inv_mem (H.mul_mem b.2 a.2))) h1
    apply Subtype.ext
    change (a : X) * b = b * a
    exact mul_inv_eq_one.mp h2
  · exact hj _ (H.pow_mem hx p) (by rw [map_pow]; exact hH.2 _ ⟨x, hx, rfl⟩)

omit [Finite G] in
theorem eq_one_of_two_three {X : Type*} [Group X] {x : X} {m n : ℕ} (h2 : x ^ 2 ^ m = 1)
    (h3 : x ^ 3 ^ n = 1) : x = 1 := by
  have ho : orderOf x ∣ Nat.gcd (2 ^ m) (3 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow m n (by norm_num))] at ho
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp ho)

theorem exists_elemAbelian_lift {K : Subgroup G} {Q : Type*} [Group Q] [Finite Q] (f : ↥K →* Q)
    (hker : IsPGroup 2 f.ker) {E : Subgroup Q} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEf : E ≤ f.range) :
    ∃ S : Subgroup G, S ≤ K ∧ CFSG.Assembly.IsElemAbelian 3 S ∧ Nat.card S = Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup ↥K := E.comap f with hP
  set f' : ↥P →* ↥E := (f.comp P.subtype).codRestrict E (fun p => p.2) with hf'
  have hf's : Function.Surjective f' := by
    rintro ⟨q, hq⟩
    obtain ⟨k, rfl⟩ := hEf hq
    exact ⟨⟨k, hq⟩, rfl⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥P) := inferInstance
  have htop : (S₀ : Subgroup ↥P).map f' = ⊤ := by
    have hS := (S₀.mapSurjective hf's).3 (Q := ⊤) (hE3.of_equiv Subgroup.topEquiv.symm) le_top
    rw [Sylow.coe_mapSurjective] at hS
    exact hS.symm
  have hinj : ∀ s ∈ (S₀ : Subgroup ↥P), f' s = 1 → s = 1 := by
    intro s hs hs1
    have hk : ((s : ↥K)) ∈ f.ker := by
      have h := congrArg Subtype.val hs1
      exact h
    obtain ⟨m, hm⟩ := hker ⟨(s : ↥K), hk⟩
    obtain ⟨n, hn⟩ := S₀.isPGroup' ⟨s, hs⟩
    have h2 : s ^ 2 ^ m = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hm
      simpa using this
    have h3 : s ^ 3 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    exact eq_one_of_two_three h2 h3
  set ι : ↥P →* G := K.subtype.comp P.subtype with hι
  have hιinj : Function.Injective ι := K.subtype_injective.comp P.subtype_injective
  refine ⟨(S₀ : Subgroup ↥P).map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact (s : ↥K).2
  · have hEtop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup ↥E) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hE.1.is_comm.comm (a : ↥E) (b : ↥E))⟩⟩,
        fun x _ => Subtype.ext ?_⟩
      simpa using hE.2 x x.2
    refine isElemAbelian_map_hom ι (isElemAbelian_of_map_hom f' hinj ?_)
    rw [htop]
    exact hEtop
  · rw [Subgroup.card_map_of_injective hιinj]
    set g' : ↥(S₀ : Subgroup ↥P) →* ↥E := f'.comp (S₀ : Subgroup ↥P).subtype with hg'
    have hg'inj : Function.Injective g' := by
      intro a b hab
      have hab' : f' a = f' b := hab
      have := hinj _ ((S₀ : Subgroup ↥P).mul_mem a.2 ((S₀ : Subgroup ↥P).inv_mem b.2))
        (by rw [map_mul, map_inv, hab', mul_inv_cancel])
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have hrange : g'.range = ⊤ := by
      rw [hg', MonoidHom.range_comp, Subgroup.range_subtype, htop]
    have h1 := Nat.card_congr (MonoidHom.ofInjective hg'inj).toEquiv
    rw [hrange, Subgroup.card_top] at h1
    exact h1

theorem exists_normalizer_lift {Γ Q : Type*} [Group Γ] [Finite Γ] [Group Q] (κ : Γ →* Q)
    (hker : IsPGroup 2 κ.ker) {B : Subgroup Γ} (hB : IsPGroup 3 B)
    (hBc : ∀ x ∈ B.map κ, ∀ z ∈ B.map κ, x * z = z * x) {h : Q} (hh : h ∈ κ.range)
    (hN : h ∈ Subgroup.normalizer ((B.map κ : Subgroup Q) : Set Q)) :
    ∃ y ∈ Subgroup.normalizer (B : Set Γ), ∀ b ∈ B, κ (y * b * y⁻¹) = h * κ b * h⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, rfl⟩ := hh
  set K := κ.ker ⊔ B with hK
  have hBK : CFSG.ABGLocalTools.IsSylowOf 3 B K := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hB, ?_⟩
    rw [hK, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal]
    intro h3
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hker
    have h32 : 3 ∣ 2 ^ m := hm ▸ h3.trans (Subgroup.relIndex_dvd_card B κ.ker)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h32)
    omega
  have hconjK : ∀ b ∈ B, y₀ * b * y₀⁻¹ ∈ K := by
    intro b hb
    obtain ⟨b', hb', hbb'⟩ := (Subgroup.mem_normalizer_iff.mp hN (κ b)).mp ⟨b, hb, rfl⟩
    have hk : y₀ * b * y₀⁻¹ * b'⁻¹ ∈ κ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hbb', mul_inv_cancel]
    have := K.mul_mem (Subgroup.mem_sup_left hk : _ ∈ K) (Subgroup.mem_sup_right hb' : b' ∈ K)
    rwa [inv_mul_cancel_right] at this
  set B' := B.map (MulAut.conj y₀).toMonoidHom with hB'
  have hB'K : CFSG.ABGLocalTools.IsSylowOf 3 B' K := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      exact hconjK b hb
    · rw [hB', Subgroup.card_map_of_injective (MulAut.conj y₀).injective]
      exact hBK.card_eq
  obtain ⟨k, hkK, hkconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hBK hB'K
  have hκk : κ k ∈ B.map κ := by
    have hle : K ≤ (B.map κ).comap κ := sup_le (fun z hz => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
      exact one_mem _) (Subgroup.le_comap_map κ B)
    exact hle hkK
  refine ⟨k⁻¹ * y₀, ?_, fun b hb => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx : k⁻¹ * y₀ * x * (k⁻¹ * y₀)⁻¹ = k⁻¹ * (y₀ * x * y₀⁻¹) * k := by group
    rw [hx, ← hkconj]
    constructor
    · intro hxB
      exact ⟨x, hxB, rfl⟩
    · rintro ⟨b, hb, hbx⟩
      have hbx' : y₀ * b * y₀⁻¹ = y₀ * x * y₀⁻¹ := hbx
      rw [mul_left_inj, mul_right_inj] at hbx'
      exact hbx' ▸ hb
  · have hc : κ y₀ * κ b * (κ y₀)⁻¹ ∈ B.map κ :=
      (Subgroup.mem_normalizer_iff.mp hN (κ b)).mp ⟨b, hb, rfl⟩
    have hcomm := hBc _ hκk _ hc
    calc κ (k⁻¹ * y₀ * b * (k⁻¹ * y₀)⁻¹)
        = (κ k)⁻¹ * (κ y₀ * κ b * (κ y₀)⁻¹) * κ k := by
          simp only [map_mul, map_inv]
          group
      _ = κ y₀ * κ b * (κ y₀)⁻¹ := by
          rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem isElemAbelian_eTwentySeven :
    CFSG.Assembly.IsElemAbelian 3 CFSG.RankThree.PartTwo.KFacts.KP2.eTwentySeven := by
  open CFSG.RankThree.PartTwo.KFacts.KP2 in
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, i, j, k, rfl⟩ := a
    obtain ⟨_, i', j', k', rfl⟩ := b
    exact eTwentySevenF_comm i j k i' j' k'
  · rintro _ ⟨i, j, k, rfl⟩
    exact eTwentySevenF_pow_three i j k

omit [Finite G] in
theorem mem_pCoreOf_of_mem_centralizerSection {Y : Subgroup G}
    (hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥) {z : G} (hzY : z ∈ Y)
    (hz : z ∈ CFSG.GH74.GLS.centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) :
    z ∈ CFSG.Open.pCoreOf 2 Y := by
  have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (⟨z, hzY⟩ : ↥Y) ∈
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) w
    rw [← map_mul, ← map_mul, mk_eq_mk_iff]
    have h := hz.2.2 (k⁻¹ : ↥Y) (k⁻¹ : ↥Y).2
    have e : ((k * ⟨z, hzY⟩ : ↥Y) : G)⁻¹ * ((⟨z, hzY⟩ * k : ↥Y) : G) =
        z⁻¹ * ⁅((k⁻¹ : ↥Y) : G), z⁆ * z⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y (inv_mem hzY)) _).mp h
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_pCore_two_iff] at hcen
  exact hcen

theorem le_of_alternating_ten {A Y : Subgroup G}
    (hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) :
    A ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hZ := center_eq_bot_of_ten φ
  intro x₀ hx₀A
  by_contra hx₀Y
  have hx₀N : x₀ ∈ Subgroup.normalizer (Y : Set G) := hAY hx₀A
  have hx₀3 : x₀ ^ 3 = 1 := hA.2 x₀ hx₀A
  obtain ⟨yb, hyb⟩ := exists_conj_of_pow_three_ten φ (conjQuotTwo Y hx₀N)
    (conjQuotTwo_pow_three Y hx₀N hx₀3)
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk'_surjective N yb
  have hcong : ∀ y : ↥Y, ((y₁ : G) * y * (y₁ : G)⁻¹)⁻¹ * (x₀ * y * x₀⁻¹) ∈ O := by
    intro y
    have h1 := congrArg (fun σ : MulAut (↥Y ⧸ N) => σ (π y)) hyb
    simp only [hπ, QuotientGroup.mk'_apply] at h1
    rw [conjQuotTwo_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul] at h1
    have h2 := (mk_eq_mk_iff (y₁ * y * y₁⁻¹) ⟨x₀ * y * x₀⁻¹, _⟩).mp
      (by simpa only [QuotientGroup.mk'_apply] using h1.symm)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  set d := (y₁ : G)⁻¹ * x₀ with hd
  have hdN : d ∈ Subgroup.normalizer (Y : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer y₁.2)) hx₀N
  have hdcs : d ∈ CFSG.GH74.GLS.centralizerSection Y O := by
    refine ⟨hdN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hdN, fun k hk => ?_⟩
    have ho := hcong ⟨k⁻¹, inv_mem hk⟩
    simp only at ho
    have e : ⁅k, d⁆ = (y₁ : G)⁻¹ * (((y₁ : G) * k⁻¹ * (y₁ : G)⁻¹)⁻¹ * (x₀ * k⁻¹ * x₀⁻¹)) *
        (y₁ : G)⁻¹⁻¹ := by
      rw [hd, commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYO (inv_mem y₁.2)) _).mp ho
  have hdY : d ∉ Y := fun h => hx₀Y (by
    have := Y.mul_mem y₁.2 h
    rwa [hd, mul_inv_cancel_left] at this)
  have hd3Y : d ^ 3 ∈ Y := by
    have e : d ^ 3 = (y₁ : G)⁻¹ * (x₀ * (y₁ : G)⁻¹ * x₀⁻¹) * (x₀ ^ 2 * (y₁ : G)⁻¹ * (x₀ ^ 2)⁻¹) *
        x₀ ^ 3 := by
      rw [hd, pow_three, pow_three, pow_two]
      group
    rw [e, hx₀3, mul_one]
    refine Y.mul_mem (Y.mul_mem (inv_mem y₁.2) ?_) ?_
    · exact (Subgroup.mem_normalizer_iff.mp hx₀N _).mp (inv_mem y₁.2)
    · exact (Subgroup.mem_normalizer_iff.mp (pow_mem hx₀N 2) _).mp (inv_mem y₁.2)
  have hd3O : d ^ 3 ∈ O := mem_pCoreOf_of_mem_centralizerSection hZ hd3Y (pow_mem hdcs 3)
  obtain ⟨k, hk⟩ := hOp ⟨d ^ 3, hd3O⟩
  have hk' : (d ^ 3) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  set e := d ^ 2 ^ k with he
  have he3 : e ^ 3 = 1 := by
    rw [he, ← pow_mul, mul_comm, pow_mul, hk']
  have hecs : e ∈ CFSG.GH74.GLS.centralizerSection Y O := pow_mem hdcs _
  have heN : e ∈ Subgroup.normalizer (Y : Set G) := hecs.1
  have heY : e ∉ Y := by
    intro heY
    have heO := mem_pCoreOf_of_mem_centralizerSection hZ heY hecs
    obtain ⟨j, hj⟩ := hOp ⟨e, heO⟩
    have hj' : e ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have he1 : e = 1 := eq_one_of_two_three hj' (by rwa [pow_one])
    have hcop : Nat.Coprime 3 (orderOf d) :=
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one (by rw [← he, he1]))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    exact hdY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y (hm ▸ pow_mem hd3O m))
  have hep : IsPGroup 3 (Subgroup.zpowers e) := by
    rintro ⟨g, hg⟩
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  have hzN : Subgroup.zpowers e ≤ Subgroup.normalizer (Y : Set G) := Subgroup.zpowers_le.mpr heN
  have hzcs : Subgroup.zpowers e ≤ CFSG.GH74.GLS.centralizerSection Y O :=
    Subgroup.zpowers_le.mpr hecs
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hm]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hlift : ∀ y : ↥Y, ∃ y' : ↥Y,
      (y' : G) ∈ Subgroup.centralizer (Subgroup.zpowers e : Set G) ∧ π y' = π y := by
    intro y
    refine exists_centralizer_with_same_image_of_trivial_quotient_action
      3 Nat.prime_three (Subgroup.zpowers e) Y hep hzN π hker3 (fun member element => ?_) y
    have h := (hzcs member.2).2.2 (element⁻¹ : ↥Y) (element⁻¹ : ↥Y).2
    rw [hπ, eq_comm, mk_eq_mk_iff]
    simpa only [commutatorElement_def, Subgroup.coe_inv, mul_assoc, inv_inv] using h
  set K := Y ⊓ Subgroup.centralizer (Subgroup.zpowers e : Set G) with hK
  set κ : ↥Y →* Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp (φ.toMonoidHom.comp π) with hκ
  set f : ↥K →* Perm (Fin 10) := κ.comp (Subgroup.inclusion inf_le_left) with hf
  have hfker : IsPGroup 2 f.ker := by
    rintro ⟨z, hz⟩
    have hz1 : π (Subgroup.inclusion inf_le_left z) = 1 := by
      have h1 : φ (π (Subgroup.inclusion inf_le_left z)) = 1 :=
        Subtype.ext (by simpa [hf, hκ] using hz)
      rw [← map_one φ] at h1
      exact φ.injective h1
    have hzO : (z : G) ∈ O := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_two_iff] at hz1
      exact hz1
    obtain ⟨n, hn⟩ := hOp ⟨z, hzO⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hEf : CFSG.RankThree.PartTwo.KFacts.KP2.eTwentySeven ≤ f.range := by
    intro z hz
    have hzA := CFSG.RankThree.PartTwo.KFacts.KP2.eTwentySeven_le_alternatingGroup hz
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (φ.symm ⟨z, hzA⟩)
    obtain ⟨y', hy'C, hy'⟩ := hlift y
    refine ⟨⟨y', y'.2, hy'C⟩, ?_⟩
    change ((φ (π y') : alternatingGroup (Fin 10)) : Perm (Fin 10)) = z
    rw [hy', show π y = φ.symm ⟨z, hzA⟩ from hy, MulEquiv.apply_symm_apply]
  obtain ⟨S, hSK, hS, hS27⟩ := exists_elemAbelian_lift f hfker isElemAbelian_eTwentySeven hEf
  rw [CFSG.RankThree.PartTwo.KFacts.K412.card_eTwentySeven] at hS27
  have hSE : S ∈ partTwoE G :=
    ⟨hS, hS27, O, hO, hOp, (hSK.trans inf_le_left).trans hYO⟩
  have hSe : ∀ x ∈ S, x * e = e * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hSK hx).2 e (Subgroup.mem_zpowers e)).symm
  have hsup := hmax S hSE (S ⊔ Subgroup.zpowers e) (isElemAbelian_sup_zpowers hS he3 hSe)
    le_sup_left
  have heS : e ∈ S := hsup ▸ (le_sup_right : Subgroup.zpowers e ≤ S ⊔ Subgroup.zpowers e)
    (Subgroup.mem_zpowers e)
  exact heY ((hSK heS).1)

end CFSG.RankThree.PartTwo.Sec16.Step163Alt
