module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Fusion
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Types
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldAssembly
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.WielandtProductAux
import CFSG.Assembly.ComponentFreeOddCores
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

private theorem mem_commutator_rhoL_of_mem_commutator {L M : Subgroup G}
    (hMN : M ≤ normalizer (L : Set G)) {s : G} (hsM : s ∈ M) (hs : s ∈ ⁅M, M⁆) :
    rhoL L ⟨s, hMN hsM⟩ ∈ _root_.commutator (MulAut (Bar2 L)) := by
  classical
  let ρ : ↥M →* MulAut (Bar2 L) := (rhoL L).comp (Subgroup.inclusion hMN)
  have hρs : ρ ⟨s, hsM⟩ = rhoL L ⟨s, hMN hsM⟩ := rfl
  have hmemM : s ∈ (commutator ↥M).map M.subtype := by
    rw [Subgroup.map_subtype_commutator]
    exact hs
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hmemM
  have ht' : t = ⟨s, hsM⟩ := Subtype.ext hts
  rw [← hρs, ← ht']
  let K : Subgroup ↥M := ⁅(⊤ : Subgroup ↥M), ⊤⁆
  have hmem : ρ t ∈ K.map ρ := Subgroup.mem_map_of_mem ρ ht
  have hK : K.map ρ = ⁅(⊤ : Subgroup ↥M).map ρ, (⊤ : Subgroup ↥M).map ρ⁆ := by
    simpa [K] using (Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥M)) (H₂ := ⊤) ρ)
  rw [hK] at hmem
  exact Subgroup.commutator_mono le_top le_top hmem

private theorem center_bar2_eq_bot_of_isU45 {L : Subgroup G} {n : ℕ}
    (hX : IsU45 (Bar2 L) n) : Subgroup.center (Bar2 L) = ⊥ := by
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, -⟩
  · exact center_eq_bot_of_lieModel_clause1 (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)) hU5
  · exact center_eq_bot_of_lieModel_clause1 (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)) hU4

private theorem exists_inner_rhoL_of_mem_commutator (hK6 : KU45Out) {L M S : Subgroup G}
    {n : ℕ} (hX : IsU45 (Bar2 L) n) (hMN : M ≤ normalizer (L : Set G)) (hS : IsPGroup 3 S)
    (hSM : S ≤ ⁅M, M⁆) {s : G} (hs : s ∈ S) (hsM : s ∈ M)
    (hsN : s ∈ normalizer (L : Set G)) :
    ∃ (z : Bar2 L) (k : ℕ), MulAut.conj z = rhoL L ⟨s, hsN⟩ ∧ z ^ (3 ^ k) = 1 := by
  classical
  have hcomm := mem_commutator_rhoL_of_mem_commutator hMN hsM (hSM hs)
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hkG : s ^ (3 ^ k) = 1 := by simpa using congrArg (Subtype.val) hk
  have hpow : (rhoL L ⟨s, hsN⟩) ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    have hk' : (⟨s, hsN⟩ : ↥(normalizer (L : Set G))) ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      simpa using hkG
    rw [hk', map_one]
  obtain ⟨z, hz⟩ := hK6 (Bar2 L) n hX (rhoL L ⟨s, hsN⟩) hcomm ⟨k, hpow⟩
  refine ⟨z, k, hz, ?_⟩
  have hZ := center_bar2_eq_bot_of_isU45 hX
  have hconj : MulAut.conj (z ^ (3 ^ k)) = (1 : MulAut (Bar2 L)) := by
    rw [map_pow, hz, hpow]
  have hmem : z ^ (3 ^ k) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : z ^ (3 ^ k) * x * (z ^ (3 ^ k))⁻¹ = x := by
      have hφ := congrArg (fun φ : MulAut (Bar2 L) => φ x) hconj
      rw [MulAut.conj_apply] at hφ
      simpa using hφ
    calc x * z ^ (3 ^ k) = (z ^ (3 ^ k) * x * (z ^ (3 ^ k))⁻¹) * z ^ (3 ^ k) := by
          rw [hx]
      _ = z ^ (3 ^ k) * x := by group
  rw [hZ] at hmem
  simpa using hmem

private theorem mem_normalizer_of_isSylowOf_of_isPGroup {L P S : Subgroup G}
    (hP : IsSylowOf 3 P L) (hS : IsPGroup 3 S) (hPS : P ≤ S) {s : G} (hs : s ∈ S)
    (hsN : s ∈ normalizer (L : Set G)) : ∀ x ∈ P, s * x * s⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hSinf : S ⊓ L = P := by
    refine IsSylowOf.eq_of_le hP ?_ inf_le_right (hS.to_le inf_le_left)
    exact fun x hx => ⟨hPS hx, hP.le hx⟩
  intro x hxP
  have hmem : s * x * s⁻¹ ∈ S ⊓ L :=
    ⟨S.mul_mem (S.mul_mem hs (hPS hxP)) (S.inv_mem hs),
      (Subgroup.mem_normalizer_iff.mp hsN x).mp (hP.le hxP)⟩
  rwa [hSinf] at hmem

private theorem mem_barImage_of_three_elem_normalizer {L P : Subgroup G}
    (hP : IsSylowOf 3 P L) {z : Bar2 L}
    (hzP : z ∈ normalizer (barImage L P : Set (Bar2 L))) {k : ℕ} (hz3 : z ^ (3 ^ k) = 1) :
    z ∈ barImage L P := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPb := isPGroup_barImage_of_isSylowOf (s := 3) Nat.prime_three hP
  have hZp : IsPGroup 3 (Subgroup.zpowers z) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  let Q : Sylow 3 (Bar2 L) := hPb.1.toSylow hPb.2
  have hQcoe : (Q : Subgroup (Bar2 L)) = barImage L P := IsPGroup.toSylow_coe ..
  have hzQ : z ∈ Subgroup.zpowers z ⊓ normalizer (Q : Set (Bar2 L)) := by
    refine ⟨Subgroup.mem_zpowers z, ?_⟩
    rw [show (Q : Set (Bar2 L)) = (barImage L P : Set (Bar2 L)) from
      congrArg (fun H : Subgroup (Bar2 L) => (H : Set (Bar2 L))) hQcoe]
    exact hzP
  rw [IsPGroup.inf_normalizer_sylow hZp Q] at hzQ
  rw [← hQcoe]
  exact hzQ.2

private theorem mem_normalizer_barImage_of_conj_eq {L P : Subgroup G} {s : G}
    (hP : IsSylowOf 3 P L) (hsN : s ∈ normalizer (L : Set G))
    (hsP : ∀ x ∈ P, s * x * s⁻¹ ∈ P) {z : Bar2 L}
    (hz : MulAut.conj z = rhoL L ⟨s, hsN⟩) :
    z ∈ normalizer (barImage L P : Set (Bar2 L)) := by
  have key : ∀ p : ↥L, (p : G) ∈ P →
      (MulAut.conj z) ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)) p) ∈ barImage L P := by
    intro p hpP
    rw [hz, show (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) p = QuotientGroup.mk p from rfl,
      UC6S846.rhoL_mk]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hsP (p : G) hpP))
  have hmap_le : (barImage L P).map (MulAut.conj z).toMonoidHom ≤ barImage L P := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hpz⟩ := Subgroup.mem_map.mp hx
    rw [← hpz]
    exact key p (Subgroup.mem_subgroupOf.mp hp)
  have hcard : Nat.card ((barImage L P).map (MulAut.conj z).toMonoidHom) =
      Nat.card (barImage L P) :=
    Subgroup.card_map_of_injective (MulAut.conj z).injective
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)

private theorem exists_mem_rhoL_eq_of_three_elem {L P S : Subgroup G} {s : G}
    (hP : IsSylowOf 3 P L) (hPS : P ≤ S) (hs : s ∈ S)
    (hsN : s ∈ normalizer (L : Set G)) (hsP : ∀ x ∈ P, s * x * s⁻¹ ∈ P) {z : Bar2 L}
    (hz : MulAut.conj z = rhoL L ⟨s, hsN⟩) {k : ℕ} (hz3 : z ^ (3 ^ k) = 1) :
    ∃ x, ∃ hx : x ∈ P, rhoL L ⟨x, Subgroup.le_normalizer (hP.le hx)⟩ =
      rhoL L ⟨s, hsN⟩ := by
  have hzP := mem_normalizer_barImage_of_conj_eq hP hsN hsP hz
  have hzBar := mem_barImage_of_three_elem_normalizer hP hzP hz3
  obtain ⟨x, hxsub, hxz⟩ := Subgroup.mem_map.mp hzBar
  have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hxsub
  have hxL : (x : G) ∈ L := hP.le hxP
  refine ⟨(x : G), hxP, ?_⟩
  have hxbar : (QuotientGroup.mk (⟨(x : G), hxL⟩ : ↥L) : Bar2 L) = z := by
    have hxeq : (⟨(x : G), hxL⟩ : ↥L) = x := Subtype.ext rfl
    rw [hxeq]
    exact hxz
  rw [UC6S846.rhoL_inner L (x : G) hxL, hxbar, hz]

theorem exists_mem_forall_mem_pCoreOf (hK6 : KU45Out) {L P S M : Subgroup G} {n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hMN : M ≤ normalizer (L : Set G))
    (hS : IsPGroup 3 S) (hSM : S ≤ ⁅M, M⁆) (hPS : P ≤ S) {s : G} (hs : s ∈ S) :
    ∃ x ∈ P, ∀ l ∈ L, (x⁻¹ * s) * l * (x⁻¹ * s)⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsM : s ∈ M := Subgroup.commutator_le_self M (hSM hs)
  have hsN : s ∈ normalizer (L : Set G) := hMN hsM
  obtain ⟨z, k, hz, hz3⟩ :=
    exists_inner_rhoL_of_mem_commutator hK6 hX hMN hS hSM hs hsM hsN
  obtain ⟨x, hxP, hρx⟩ :=
    exists_mem_rhoL_eq_of_three_elem hP hPS hs hsN
      (mem_normalizer_of_isSylowOf_of_isPGroup hP hS hPS hs hsN) hz hz3
  have hxL : x ∈ L := hP.le hxP
  let mx : ↥(normalizer (L : Set G)) := ⟨x, Subgroup.le_normalizer hxL⟩
  let ms : ↥(normalizer (L : Set G)) := ⟨s, hsN⟩
  have hρ : rhoL L (mx⁻¹ * ms) = 1 := by
    rw [map_mul, map_inv, show rhoL L mx = rhoL L ms from hρx, inv_mul_cancel]
  refine ⟨x, hxP, fun l hl => ?_⟩
  have hfix : rhoL L (mx⁻¹ * ms) (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) =
      QuotientGroup.mk (⟨l, hl⟩ : ↥L) := by rw [hρ, MulAut.one_apply]
  simpa [mx, ms] using (UC6S846.rhoL_fix_iff L (mx⁻¹ * ms) (⟨l, hl⟩ : ↥L)).mp hfix

private theorem not_mem_of_mem_centOverO2_of_orderOf_three {L S : Subgroup G} {y : G}
    (hZ : Subgroup.center (Bar2 L) = ⊥) (hyR : y ∈ F08.CentOverO2 S L)
    (hy3 : orderOf y = 3) : y ∉ L := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro hyL
  have hytriv : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hyR).2
  have hcent : (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
      have hcoe : (((l * ⟨y, hyL⟩) / (⟨y, hyL⟩ * l) : ↥L) : G) =
          (y * l * y⁻¹ * l⁻¹)⁻¹ := by
        simp [div_eq_mul_inv, mul_assoc]
      have hG : (((l * ⟨y, hyL⟩) / (⟨y, hyL⟩ * l) : ↥L) : G) ∈ pCoreOf 2 L := by
        rw [hcoe]
        exact (pCoreOf 2 L).inv_mem (hytriv l l.2)
      obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp hG
      have hp_eq : p = (l * ⟨y, hyL⟩) / (⟨y, hyL⟩ * l) := L.subtype_injective hpeq
      rwa [← hp_eq]
  rw [hZ] at hcent
  have hyCore : y ∈ pCoreOf 2 L := by
    have h1 : (⟨y, hyL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hcent)
    exact Subgroup.mem_map_of_mem (f := L.subtype) (K := CFSG.pCore 2 ↥L) h1
  obtain ⟨j, hj⟩ := (UC6S846.isPGroup_pCoreOf L).exists_orderOf_eq_pow ⟨y, hyCore⟩
  rw [← Subgroup.orderOf_coe] at hj
  rw [hy3] at hj
  rcases j with _ | j
  · norm_num at hj
  · rw [pow_succ] at hj
    omega

private theorem le_normalizer_centOverO2 {L S : Subgroup G}
    (hSN : S ≤ normalizer (L : Set G)) :
    S ≤ normalizer (F08.CentOverO2 S L : Set G) := by
  let R : Subgroup G := F08.CentOverO2 S L
  have hRle : R ≤ S := fun x hx =>
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hx).1
  have hRnorm : (R.subgroupOf S).Normal := by
    let φ : ↥S →* MulAut (Bar2 L) := (rhoL L).comp (Subgroup.inclusion hSN)
    have hker : R = φ.ker.map S.subtype :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.centOverO2_eq_ker_map hSN
    rw [hker]
    have heq : (φ.ker.map S.subtype).subgroupOf S = φ.ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, hkx⟩
        rwa [Subtype.ext hkx] at hk
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact MonoidHom.normal_ker φ
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).mp hRnorm

private theorem exists_prime_order_mem_centOverO2 {L S : Subgroup G} (hS : IsPGroup 3 S)
    (hSN : S ≤ normalizer (L : Set G)) {r : G} (hrS : r ∈ S) (hr1 : r ≠ 1)
    (hr : ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∃ y ∈ S, y ∈ F08.CentOverO2 S L ∧ y ∈ centralizer (S : Set G) ∧ orderOf y = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let R : Subgroup G := F08.CentOverO2 S L
  have hrR : r ∈ R :=
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff).mpr ⟨hrS, hr⟩
  have hRle : R ≤ S := fun x hx =>
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hx).1
  have hRne : R ≠ ⊥ := by
    intro hbot
    have : r ∈ (⊥ : Subgroup G) := hbot ▸ hrR
    exact hr1 (by simpa using this)
  have hSNR : S ≤ normalizer (R : Set G) := le_normalizer_centOverO2 hSN
  obtain ⟨n, hnR, hn1, hncomm⟩ :=
    CFSG.GroupTheory.WielandtProduct.exists_mem_commute_of_le_of_isPGroup hS hRle hSNR hRne
  have hnC : n ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hncomm y hy).symm
  have hZne : R ⊓ centralizer (S : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : n ∈ R ⊓ centralizer (S : Set G) := ⟨hnR, hnC⟩
    rw [hbot] at hmem
    exact hn1 (by simpa using hmem)
  have hZP : IsPGroup 3 ↥(R ⊓ centralizer (S : Set G)) :=
    hS.to_le (inf_le_left.trans hRle)
  have hZcard : 3 ∣ Nat.card ↥(R ⊓ centralizer (S : Set G)) := by
    rcases hZP.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZne
    · exact h
  obtain ⟨y, hyord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(R ⊓ centralizer (S : Set G))) 3 hZcard
  exact ⟨(y : G), hRle y.2.1, y.2.1, y.2.2, by rw [Subgroup.orderOf_coe, hyord]⟩

private theorem exists_three_elem_centOverO2 {L S : Subgroup G} (hS : IsPGroup 3 S)
    (hSN : S ≤ normalizer (L : Set G)) (hZ : Subgroup.center (Bar2 L) = ⊥) {r : G}
    (hrS : r ∈ S) (hr1 : r ≠ 1)
    (hr : ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∃ y ∈ S, y ∈ F08.CentOverO2 S L ∧ y ∈ centralizer (S : Set G) ∧ orderOf y = 3 ∧
      y ∉ L := by
  obtain ⟨y, hyS, hyR, hyC, hyord⟩ := exists_prime_order_mem_centOverO2 hS hSN hrS hr1 hr
  exact ⟨y, hyS, hyR, hyC, hyord,
    not_mem_of_mem_centOverO2_of_orderOf_three hZ hyR hyord⟩

private theorem comm_A_zpowers_of_le_centralizer {S A : Subgroup G} {y : G}
    (hAC : A ≤ centralizer (S : Set G)) (hyS : y ∈ S) :
    ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
  intro a ha b hb
  have hbS : b ∈ S := Subgroup.zpowers_le.mpr hyS hb
  exact (Subgroup.mem_centralizer_iff.mp (hAC ha) b hbS).symm

private theorem isElemAbelian_sup_zpowers_card_nine {L P S A : Subgroup G} {p n : ℕ}
    (hP : IsSylowOf 3 P L) (hS : IsPGroup 3 S) (hPS : P ≤ S)
    (hSN : S ≤ normalizer (L : Set G)) (hK2 : KU45Syl3) (hX : IsU45 (Bar2 L) n)
    (hA : F08.NotationA8103 L P p n A) {y : G} (hyS : y ∈ S)
    (hyC : y ∈ centralizer (S : Set G)) (hyord : orderOf y = 3) (hyL : y ∉ L) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers y) ∧
      Nat.card ↥(A ⊔ Subgroup.zpowers y) = 9 ∧
      A ⊔ Subgroup.zpowers y ≤ S ⊓ centralizer (S : Set G) ∧
      ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
  classical
  have hAcard : Nat.card A = 3 := hA.1
  have hAP : A ≤ P := hA.2.1
  have hAea : IsElemAbelian 3 A :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.isElemAbelian_of_card_prime Nat.prime_three hAcard
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    exact orderOf_dvd_iff_pow_eq_one.mp (by
      have h := Subgroup.orderOf_dvd_natCard A ha
      rwa [hAcard] at h)
  have hAcS : A ≤ centralizer (S : Set G) := fun a ha =>
    mem_centralizer_of_isSylowOf hK2 hX hP hS hSN hPS (hAP ha) (hA3 a ha)
  have hcommAZ := comm_A_zpowers_of_le_centralizer hAcS hyS
  have hy3 : y ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hyord])
  have hEea : IsElemAbelian 3 (A ⊔ Subgroup.zpowers y) :=
    hAea.sup_of_commute (isElemAbelian_zpowers hy3) hcommAZ
  have hEcard : Nat.card ↥(A ⊔ Subgroup.zpowers y) = 9 := by
    have hdisj : A ⊓ Subgroup.zpowers y = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_inf] at hz
      by_contra hz1
      have hzL : z ∈ L := hP.le (hAP hz.1)
      have hzord : orderOf z = 3 := orderOf_eq_prime (hA3 z hz.1) hz1
      have hle : Subgroup.zpowers z ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hz.2
      have hcz : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
      have hcy : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyord]
      have heq : Subgroup.zpowers z = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hcy])
      exact hyL (Subgroup.zpowers_le.mpr hzL (heq.symm ▸ Subgroup.mem_zpowers y))
    rw [CFSG.card_sup_eq_mul_of_commute A (Subgroup.zpowers y) hcommAZ hdisj, hAcard,
      Nat.card_zpowers, hyord]
  have hEleS : A ⊔ Subgroup.zpowers y ≤ S :=
    sup_le (hAP.trans hPS) (Subgroup.zpowers_le.mpr hyS)
  have hEleC : A ⊔ Subgroup.zpowers y ≤ centralizer (S : Set G) :=
    sup_le hAcS (Subgroup.zpowers_le.mpr hyC)
  exact ⟨hEea, hEcard, le_inf hEleS hEleC, hcommAZ⟩

private theorem commutator_sup_zpowers_le_pCoreOf {L S A : Subgroup G} {y : G}
    (hSN : S ≤ normalizer (L : Set G)) (hAP : A ≤ S)
    (hyR : y ∈ F08.CentOverO2 S L)
    (hcommAZ : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, a * b = b * a) {F : Subgroup G}
    (hFL : F ≤ L) (hFCA : F ≤ centralizer (A : Set G)) :
    ∀ e ∈ A ⊔ Subgroup.zpowers y, ∀ a ∈ F, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 L := by
  intro e he a ha
  obtain ⟨a1, ha1, z, hz, rfl⟩ := (CFSG.mem_sup_of_commute hcommAZ).mp he
  have hzR : z ∈ F08.CentOverO2 S L := Subgroup.zpowers_le.mpr hyR hz
  have hzO : z * a * z⁻¹ * a⁻¹ ∈ pCoreOf 2 L :=
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hzR).2 a (hFL ha)
  have ha1N : a1 ∈ normalizer (pCoreOf 2 L : Set G) :=
    (hSN.trans (UC6S846.normalizer_le_normalizer_pCoreOf L)) (hAP ha1)
  have hcomm1 : a1 * a = a * a1 := (Subgroup.mem_centralizer_iff.mp (hFCA ha) a1 ha1)
  have hinv : a1⁻¹ * a⁻¹ = a⁻¹ * a1⁻¹ := by
    calc a1⁻¹ * a⁻¹ = (a * a1)⁻¹ := (mul_inv_rev a a1).symm
      _ = (a1 * a)⁻¹ := by rw [← hcomm1]
      _ = a⁻¹ * a1⁻¹ := mul_inv_rev a1 a
  have heq' : a1 * z * a * (a1 * z)⁻¹ * a⁻¹ =
      a1 * (z * a * z⁻¹ * a⁻¹) * a1⁻¹ := by
    rw [mul_inv_rev]
    calc a1 * z * a * (z⁻¹ * a1⁻¹) * a⁻¹
        = a1 * z * a * z⁻¹ * (a1⁻¹ * a⁻¹) := by group
      _ = a1 * z * a * z⁻¹ * (a⁻¹ * a1⁻¹) := by rw [hinv]
      _ = a1 * (z * a * z⁻¹ * a⁻¹) * a1⁻¹ := by group
  rw [heq']
  exact (Subgroup.mem_normalizer_iff.mp ha1N (z * a * z⁻¹ * a⁻¹)).mp hzO

private theorem two_le_pRank_centralizer {D : Data G} {L S E F : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hLm : L ≤ D.M) (hSN : S ≤ normalizer (L : Set G))
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hF : IsElemAbelian p F)
    (hFcard : Nat.card F = p ^ 2) (hES : E ≤ S) (hEC : E ≤ centralizer (S : Set G))
    (hFL : F ≤ L) (hcomm : ∀ e ∈ E, ∀ a ∈ F, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 L) :
    2 ≤ Open.pRank p (D.M ⊓ centralizer (E : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hO : IsPGroup 2 (pCoreOf 2 L) := UC6S846.isPGroup_pCoreOf L
  have hFnorm : F ≤ normalizer (pCoreOf 2 L : Set G) :=
    hFL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hEnorm : E ≤ normalizer (pCoreOf 2 L : Set G) :=
    hES.trans (hSN.trans (UC6S846.normalizer_le_normalizer_pCoreOf L))
  obtain ⟨F', hF'C, hF'le, ⟨eF⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_centralizing_copy (ℓ := 3) (p := p)
      Nat.prime_three (by norm_num) hp hp2 (pCoreOf 2 L) F E hO hFnorm hEnorm hF.isPGroup
      hE.isPGroup hcomm
  have hF'D : F' ≤ D.M ⊓ centralizer (E : Set G) := by
    refine le_inf ?_ hF'C
    refine hF'le.trans (sup_le ?_ ?_)
    · exact hFL.trans hLm
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLm
  have hF'ea : IsElemAbelian p F' := by
    haveI : IsMulCommutative ↥F := hF.1
    refine ⟨⟨⟨fun x z => ?_⟩⟩, fun x hx => ?_⟩
    · apply eF.injective
      rw [map_mul, map_mul]
      exact mul_comm' (eF x) (eF z)
    · have h : (⟨x, hx⟩ : ↥F') ^ p = 1 := by
        apply eF.injective
        rw [map_pow, map_one]
        exact Subtype.ext (hF.2 (eF ⟨x, hx⟩) (eF ⟨x, hx⟩).2)
      simpa using congrArg (Subtype.val) h
  have hF'card : Nat.card F' = p ^ 2 := by
    rw [← hFcard]
    exact Nat.card_congr eF.toEquiv
  exact CFSG.SectionRank.le_pRank hp.one_lt hF'D hF'ea hF'card

theorem false_of_mem_forall_mem_pCoreOf {D : Data G} (hSg : SigmaStd D) (h76 : F07.R76Sig D)
    (h614 : UC6.R6_14 D) (hK2 : KU45Syl3) {L P S A : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G))
    (hS : IsSylowOf 3 S D.M) (hPS : P ≤ S) (hA : F08.NotationA8103 L P p n A) {r : G}
    (hrS : r ∈ S) (hr1 : r ≠ 1) (hr : ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hH.1
  have hLm : L ≤ D.M := hH.1.1.le
  have hSN : S ≤ normalizer (L : Set G) := hS.le.trans hN
  have hP : IsSylowOf 3 P L := hH.2.2.2.2
  obtain ⟨hp, hp2, -⟩ := prime_of_hyp8102 hSg hH
  have hZ : Subgroup.center (Bar2 L) = ⊥ := center_bar2_eq_bot_of_hyp8102 hH
  obtain ⟨y, hyS, hyR, hyC, hyord, hyL⟩ :=
    exists_three_elem_centOverO2 hS.isPGroup hSN hZ hrS hr1 hr
  obtain ⟨hEea, hEcard, hER, hcommAZ⟩ :=
    isElemAbelian_sup_zpowers_card_nine hP hS.isPGroup hPS hSN hK2 hX hA hyS hyC hyord hyL
  obtain ⟨F, hFle, hFea, hFcard0⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (L ⊓ centralizer (A : Set G))
  have hFL : F ≤ L := hFle.trans inf_le_left
  have hFCA : F ≤ centralizer (A : Set G) := hFle.trans inf_le_right
  have hFcard : Nat.card F = p ^ 2 := by
    rw [hFcard0, hA.2.2.2]
  have hcommEF := commutator_sup_zpowers_le_pCoreOf hSN (hA.2.1.trans hPS) hyR hcommAZ hFL hFCA
  have hrank : 2 ≤ Open.pRank p (D.M ⊓ centralizer ((A ⊔ Subgroup.zpowers y : Subgroup G) :
      Set G)) :=
    two_le_pRank_centralizer hp hp2 hLm hSN hEea hEcard hFea hFcard
      (hER.trans inf_le_left) (hER.trans inf_le_right) hFL hcommEF
  exact hH.2.2.1 (stronglyEmbedded_of_two_le_pRank_centralizer hSg hns h76 h614
    hH.2.2.2.1 Nat.prime_three (by norm_num) (three_not_mem_sig_of_hyp8102 hSg hH)
    hS hER hEea (by rw [hEcard]; norm_num) hrank)

private theorem exists_sylow_top_of_mem_uniqueSet {D : Data G} {L P A : Subgroup G}
    (hP : IsSylowOf 3 P L) (hLM : L ≤ D.M) (hA : A ∈ uniqueSet D.M) (hAP : A ≤ P) :
    ∃ S : Subgroup G, IsSylowOf 3 S ⊤ ∧ S ≤ D.M ∧ P ≤ S := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPsub : IsPGroup 3 (P.subgroupOf D.M) := hP.isPGroup.comap_subtype
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hPsub
  let S : Subgroup G := (Q : Subgroup ↥D.M).map D.M.subtype
  have hS : IsSylowOf 3 S D.M := ⟨Q, rfl⟩
  have hPS : P ≤ S := by
    have h := Subgroup.map_mono (f := D.M.subtype) hPQ
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hP.le.trans hLM)] at h
  refine ⟨S, ?_, hS.le, hPS⟩
  exact isSylowOf_top_of_mem_uniqueSet Nat.prime_three D.maxLocal hS hA (hAP.trans hPS)

private theorem le_of_forall_mem_pCoreOf {D : Data G} (hSg : SigmaStd D) (h76 : F07.R76Sig D)
    (h614 : UC6.R6_14 D) (hK2 : KU45Syl3) (hK6 : KU45Out) {L P S A : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G))
    (hS : IsSylowOf 3 S D.M) (hPS : P ≤ S) (hA : F08.NotationA8103 L P p n A)
    (hSM' : S ≤ ⁅D.M, D.M⁆) : S ≤ P := by
  intro s hs
  obtain ⟨x, hxP, hx⟩ :=
    exists_mem_forall_mem_pCoreOf hK6 hX hH.2.2.2.2 hN hS.isPGroup hSM' hPS hs
  have hrS : x⁻¹ * s ∈ S := S.mul_mem (S.inv_mem (hPS hxP)) hs
  by_contra hne
  have hrne : x⁻¹ * s ≠ 1 := by
    intro h1
    apply hne
    have hsx : s = x := by
      calc s = x * (x⁻¹ * s) := by group
        _ = x := by rw [h1, mul_one]
    rwa [hsx]
  exact false_of_mem_forall_mem_pCoreOf hSg h76 h614 hK2 hH hX hN hS hPS hA hrS hrne hx

theorem isSylowOf_top_of_hyp8102 {D : Data G} (hSg : SigmaStd D) (h76 : F07.R76Sig D)
    (h614 : UC6.R6_14 D) (hK2 : KU45Syl3) (hK5 : KU45Types) (hK6 : KU45Out)
    {L P : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n)
    (hN : D.M ≤ normalizer (L : Set G)) (hpn : p ∣ 2 ^ n + 1)
    (h6 : ∀ A : Subgroup G, F08.NotationA8103 L P p n A → A ∈ uniqueSet D.M) :
    IsSylowOf 3 P ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hp, hp2, -⟩ := prime_of_hyp8102 hSg hH
  have hP : IsSylowOf 3 P L := hH.2.2.2.2
  obtain ⟨A, hA⟩ := exists_notationA8103 hK5 hX hP hp hp2 hpn
  obtain ⟨S, hStop, hSM, hPS⟩ :=
    exists_sylow_top_of_mem_uniqueSet hP hH.1.1.le (h6 A hA) hA.2.1
  have hS : IsSylowOf 3 S D.M := hStop.of_le hSM le_top
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    exact orderOf_dvd_iff_pow_eq_one.mp (by
      have h := Subgroup.orderOf_dvd_natCard A ha
      rwa [hA.1] at h)
  have hAC : A ≤ centralizer (S : Set G) := fun a ha =>
    mem_centralizer_of_isSylowOf hK2 hX hP hS.isPGroup (hS.le.trans hN) hPS (hA.2.1 ha)
      (hA3 a ha)
  have hAS : A ≤ S := hA.2.1.trans hPS
  have hctl : ∀ x ∈ S, ∀ g : G, g * x * g⁻¹ ∈ S →
      ∃ m ∈ D.M, g * x * g⁻¹ = m * x * m⁻¹ := by
    intro x hx g hgx
    exact exists_conj_eq_of_mem_uniqueSet Nat.prime_three D.maxLocal hStop hSM (h6 A hA)
      (le_inf hAS hAC) (x := x) (g := g) hx hgx
  have hcommG : commutator G = ⊤ := by
    haveI : IsSimpleGroup G := D.standing.simple
    exact CFSG.Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup D.standing.nonab
  have hSM' : S ≤ ⁅D.M, D.M⁆ :=
    le_commutator_of_control Nat.prime_three hcommG hStop hSM hctl
  have hSP : S ≤ P :=
    le_of_forall_mem_pCoreOf hSg h76 h614 hK2 hK6 hH hX hN hS hPS hA hSM'
  have hSPeq : S = P := le_antisymm hSP hPS
  simpa [hSPeq] using hStop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
