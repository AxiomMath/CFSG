module

import CFSG.RankThree.PartTwo.Sec17.Item175ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] noncomputable def Step176SecFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} →
    ∀ K : Subgroup G, K ≠ ⊤ → c ∈ K → SectionFourHyp (↥K ⧸ CFSG.pPrimeCore 3 ↥K)

@[expose] noncomputable def Step176Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item175 A c → omegaA A = {Subgroup.zpowers c} →
    ∀ K : Subgroup G, K ≠ ⊤ → ∀ hcK : c ∈ K,
      ¬ Sec4.IsoGTwoPrime ↥(Subgroup.normalClosure
          (((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
            Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) : Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K))) ∧
        IsEmpty (↥(Subgroup.normalClosure
          (((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
            Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) : Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K))) ≃*
          CFSG.Blueprint.NativeSporadic.J2)

namespace Proof176

variable {G : Type} [Group G] [Finite G]

section Quotient

variable {K : Subgroup G}

theorem injOn_mk_pPrimeCore {S : Subgroup ↥K} (hS : IsPGroup 3 S) :
    Set.InjOn (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) (S : Set ↥K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hdisj : Disjoint S (CFSG.pPrimeCore 3 ↥K) := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)))
  intro x hx y hy hxy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
  have hmem : x⁻¹ * y ∈ S ⊓ CFSG.pPrimeCore 3 ↥K := ⟨S.mul_mem (S.inv_mem hx) hy, hxy⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
  exact eq_of_inv_mul_eq_one hmem

theorem map_map_conj {M M' : Type*} [Group M] [Group M'] (φ : M →* M') (S : Subgroup M)
    (v : M) : (S.map φ).map (MulAut.conj (φ v)).toMonoidHom =
      (S.map (MulAut.conj v).toMonoidHom).map φ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

omit [Finite G] in
theorem orderOf_mk_eq {c : G} (hcK : c ∈ K) : orderOf (⟨c, hcK⟩ : ↥K) = orderOf c :=
  Subgroup.orderOf_mk c hcK

theorem card_map_zpowers {c : G} (hc : orderOf c = 3) (hcK : c ∈ K) :
    Nat.card ((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) =
      3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc' : orderOf (⟨c, hcK⟩ : ↥K) = 3 := (orderOf_mk_eq hcK).trans hc
  have hS : IsPGroup 3 (Subgroup.zpowers (⟨c, hcK⟩ : ↥K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc', pow_one])
  rw [Sec13.card_map_eq_of_injOn _ (injOn_mk_pPrimeCore hS), Nat.card_zpowers, hc']

theorem weaklyClosed_quot {c : G} (hc : orderOf c = 3)
    (hweak : ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c)
    (hcK : c ∈ K) :
    ∀ g : ↥K ⧸ CFSG.pPrimeCore 3 ↥K,
      ((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map
          (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) : Subgroup _) : Set _) →
      ((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map
          (MulAut.conj g).toMonoidHom =
        (Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥K with hN
  set π := QuotientGroup.mk' N with hπ
  set c' : ↥K := ⟨c, hcK⟩ with hc'def
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N g
  intro hg
  have hc' : orderOf c' = 3 := (orderOf_mk_eq hcK).trans hc
  have hc'3 : c' ^ 3 = 1 := by rw [← hc']; exact pow_orderOf_eq_one c'
  have hS₀ : IsPGroup 3 (Subgroup.zpowers c') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc', pow_one])
  have hπc : orderOf (π c') = 3 := by
    rw [← Nat.card_zpowers, ← MonoidHom.map_zpowers, Sec13.card_map_eq_of_injOn _
      (injOn_mk_pPrimeCore hS₀), Nat.card_zpowers, hc']
  have hZeq : (Subgroup.zpowers c').map π = Subgroup.zpowers (π c') := MonoidHom.map_zpowers π c'
  set z := π (y * c' * y⁻¹) with hzdef
  have hZg : ((Subgroup.zpowers c').map π).map (MulAut.conj (π y)).toMonoidHom =
      Subgroup.zpowers z := by
    rw [map_map_conj, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hzN : z ∈ Subgroup.normalizer (Subgroup.zpowers (π c') : Set _) := by
    rw [← hZeq]
    exact hg (hZg ▸ Subgroup.mem_zpowers z)
  have hz3 : z ^ 3 = 1 := by
    rw [hzdef, ← map_pow, conj_pow, hc'3, mul_one, mul_inv_cancel, map_one]
  have hzC : z ∈ Subgroup.centralizer ({π c'} : Set _) :=
    Proof175.mem_centralizer_of_mem_normalizer hπc hzN (k := 1) (by rw [pow_one]; exact hz3)
  have hE₁ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (π c')) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hπc3 : π c' ^ 3 = 1 := by
      have := pow_orderOf_eq_one (π c')
      rwa [hπc] at this
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hπc3, one_zpow]
  have hzE : ∀ e ∈ Subgroup.zpowers (π c'), e * z = z * e := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hzC).symm k)
  have hE := isElemAbelian_sup_zpowers hE₁ hz3 hzE
  set E := Subgroup.zpowers (π c') ⊔ Subgroup.zpowers z with hEdef
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set R := E.comap π with hRdef
  have hcR : c' ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers (π c'))
  have hycR : y * c' * y⁻¹ ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  obtain ⟨S, hS, hcS⟩ := Item134SylowBarProof.exists_isSylowOf_le
    (Subgroup.zpowers_le.mpr hcR) hS₀
  have hS₁ : IsPGroup 3 (Subgroup.zpowers (y * c' * y⁻¹)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, show y * c' * y⁻¹ = (MulAut.conj y) c' from rfl, MulEquiv.orderOf_eq,
        hc', pow_one])
  obtain ⟨S', hS', hyS'⟩ := Item134SylowBarProof.exists_isSylowOf_le
    (Subgroup.zpowers_le.mpr hycR) hS₁
  obtain ⟨m, hmR, hS'm⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf hS hS'
  have hwS : m⁻¹ * (y * c' * y⁻¹) * m ∈ S := by
    have h1 : y * c' * y⁻¹ ∈ S.map (MulAut.conj m).toMonoidHom :=
      hS'm ▸ hyS' (Subgroup.mem_zpowers _)
    obtain ⟨s, hs, hse⟩ := h1
    have : s = m⁻¹ * (y * c' * y⁻¹) * m := by
      rw [← hse]
      simp [mul_assoc]
    exact this ▸ hs
  have hSab : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    refine injOn_mk_pPrimeCore hS.isPGroup (mul_mem hs ht) (mul_mem ht hs) ?_
    rw [map_mul, map_mul]
    exact hEcomm _ (hS.le hs) _ (hS.le ht)
  set v : ↥K := m⁻¹ * y with hvdef
  have hvc : v * c' * v⁻¹ = m⁻¹ * (y * c' * y⁻¹) * m := by rw [hvdef]; group
  have hcomm : (v * c' * v⁻¹) * c' = c' * (v * c' * v⁻¹) := by
    rw [hvc]
    exact hSab _ hwS _ (hcS (Subgroup.mem_zpowers c'))
  have hvG : ((v : G) * c * (v : G)⁻¹) * c = c * ((v : G) * c * (v : G)⁻¹) := by
    have := congrArg Subtype.val hcomm
    simpa using this
  have hzG : (Subgroup.zpowers c).map (MulAut.conj (v : G)).toMonoidHom =
      Subgroup.zpowers ((v : G) * c * (v : G)⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hweakv := hweak (v : G) (by
    rw [hzG, Subgroup.zpowers_le]
    exact Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
      (Subgroup.mem_centralizer_singleton_iff.mpr hvG))
  have hvK : (Subgroup.zpowers c').map (MulAut.conj v).toMonoidHom = Subgroup.zpowers c' := by
    apply Subgroup.map_injective K.subtype_injective
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    have h1 := hweakv
    rw [hzG] at h1
    simpa using h1
  have hπv : ((Subgroup.zpowers c').map π).map (MulAut.conj (π v)).toMonoidHom =
      (Subgroup.zpowers c').map π := by
    rw [map_map_conj, hvK]
  have hπm : π m ∈ Subgroup.normalizer
      (((Subgroup.zpowers c').map π : Subgroup _) : Set (↥K ⧸ N)) := by
    rw [hZeq]
    refine Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hEcomm _ hmR _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have hy : π y = π m * π v := by rw [hvdef, map_mul, map_inv, mul_inv_cancel_left]
  rw [hy, map_conj_mul, hπv, Late.map_conj_eq_of_mem_normalizer hπm]

end Quotient

theorem pRank_le_quot {K : Subgroup G} {c : G} (hcK : c ∈ K) :
    CFSG.Open.pRank 3 (normalClosureIn K c) ≤
      CFSG.Open.pRank 3 (Subgroup.normalClosure
        (((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
          Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) : Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥K with hN
  set π := QuotientGroup.mk' N with hπ
  set Xq := Subgroup.normalClosure
    (((Subgroup.zpowers (⟨c, hcK⟩ : ↥K)).map π : Subgroup (↥K ⧸ N)) : Set (↥K ⧸ N)) with hXq
  have hXK : normalClosureIn K c ≤ K := by
    rw [normalClosureIn, Subgroup.closure_le]
    rintro x ⟨m, hm, rfl⟩
    exact mul_mem (mul_mem hm hcK) (inv_mem hm)
  have hXXq : normalClosureIn K c ≤ (Xq.comap π).map K.subtype := by
    rw [normalClosureIn, Subgroup.closure_le]
    rintro x ⟨m, hm, rfl⟩
    refine ⟨(⟨m, hm⟩ : ↥K) * ⟨c, hcK⟩ * (⟨m, hm⟩ : ↥K)⁻¹, ?_, rfl⟩
    show π (⟨m, hm⟩ * ⟨c, hcK⟩ * ⟨m, hm⟩⁻¹) ∈ Xq
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure
        (Subgroup.mem_map_of_mem π (Subgroup.mem_zpowers (⟨c, hcK⟩ : ↥K)))) _
  apply csSup_le'
  rintro k ⟨E, hEX, hEab, hEcard⟩
  set E' := E.subgroupOf K with hE'
  have hE'card : Nat.card E' = 3 ^ k := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEX.trans hXK)).toEquiv, hEcard]
  have hE'3 : IsPGroup 3 E' := IsPGroup.of_card hE'card
  refine le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three Xq)
    ⟨E'.map π, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hXXq (hEX he)
    have : x = e := Subtype.ext hxe
    rw [← this]
    exact hx
  · have hE'ab : CFSG.Assembly.IsElemAbelian 3 E' := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        have h1 := congrArg Subtype.val
          (hEab.1.is_comm.comm ⟨((a : ↥K) : G), a.2⟩ ⟨((b : ↥K) : G), b.2⟩)
        exact h1
      · apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hEab.2 _ hx
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π E' hE'ab
  · rw [Sec13.card_map_eq_of_injOn _ (injOn_mk_pPrimeCore hE'3), hE'card]

theorem one_le_pRank {K : Subgroup G} {c : G} (hc : orderOf c = 3) :
    1 ≤ CFSG.Open.pRank 3 (normalClosureIn K c) := by
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  refine le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
    ⟨Subgroup.zpowers c, ?_, ⟨inferInstance, fun x hx => ?_⟩, by rw [Nat.card_zpowers, hc,
      pow_one]⟩
  · refine Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨1, one_mem K, ?_⟩)
    rw [one_mul, inv_one, mul_one]
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]

end Proof176

end CFSG.RankThree.PartTwo.Sec17
