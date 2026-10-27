module

public import CFSG.Quasithin.H13.NQBlockXiMinusCore
public import CFSG.Quasithin.H13.NQCoreP134Input137Holds
public import CFSG.Quasithin.H13.GoldschmidtU3ThreeCase
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Bender
public import CFSG.Quasithin.Vol2.GoldschmidtCor332L2p
public import CFSG.Quasithin.Vol2.GoldschmidtCor332L33
public import CFSG.Quasithin.Vol2.GoldschmidtCor332M11

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.Cor332
open CFSG.LieType.BorelTits
open scoped MatrixGroups

section TwoThree

variable {G : Type*} [Group G]

@[expose] def TwoLocalsTwoThree (G : Type*) [Group G] : Prop :=
  ∀ Q H : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q → H ≤ normalizer (Q : Set G) →
    ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3

theorem twoLocalsTwoThree_of [Finite G] (k : ℕ)
    (hE : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ k)
    (hr : ∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ Nat.card G → ∀ d : ℕ, 1 ≤ d → d ≤ k →
      ¬ r ∣ 2 ^ d - 1)
    (hC : ∀ x z : G, orderOf z = 2 → x * z = z * x → ∀ r : ℕ, r.Prime → 5 ≤ r → orderOf x ≠ r) :
    TwoLocalsTwoThree G := by
  intro Q H hQ hQ2 hHQ r hrp hrd
  classical
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  simp only [not_or] at hne
  have h5 : 5 ≤ r := Cor332.five_le_of_prime_ne hrp hne.1 hne.2
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) r hrd
  have hxN : (x : G) ∈ Subgroup.normalizer (Q : Set G) := hHQ x.2
  have hxo : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
  have hQne : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  have hZ0Q : omegaCenter Q ≤ Q := Cor332.omegaCenter_le Q
  have hZ0p : IsPGroup 2 (omegaCenter Q) := hQ2.to_le hZ0Q
  obtain ⟨z, hzG, hz1, hz2⟩ : ∃ z : G, z ∈ omegaCenter Q ∧ z ≠ 1 ∧ orderOf z = 2 := by
    have hcen : Nontrivial (Subgroup.center Q) := hQ2.center_nontrivial
    have hcp : IsPGroup 2 (Subgroup.center Q) := hQ2.to_subgroup _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
      exact not_subsingleton _ hn.1
    have h2dvd : 2 ∣ Nat.card (Subgroup.center Q) := by rw [hn]; exact dvd_pow_self 2 hn0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 h2dvd
    let φ : Subgroup.center Q →* G := Q.subtype.comp (Subgroup.center Q).subtype
    have hφ : Function.Injective φ := fun a b hab => Subtype.ext (Subtype.ext hab)
    have hzo : orderOf (φ z) = 2 := by rw [orderOf_injective φ hφ z, hz]
    have hzsq : φ z ^ 2 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
    refine ⟨φ z, mem_omegaCenter.mpr ⟨(z : Q).2, fun q hq => ?_, hzsq⟩, ?_, hzo⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩
      exact congrArg Subtype.val this
    · intro h
      rw [h, orderOf_one] at hzo
      omega
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hZ0p
  have hZ0ea : IsElemAbelian 2 (omegaCenter Q) :=
    ⟨⟨⟨fun a b => Subtype.ext ((mem_omegaCenter.mp b.2).2.1 a (mem_omegaCenter.mp a.2).1)⟩⟩,
      fun g hg => (mem_omegaCenter.mp hg).2.2⟩
  have hdk : d ≤ k := by
    have := hE _ hZ0ea
    rw [hd] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hd1 : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [hd0, pow_zero] at hd
    have hbot : omegaCenter Q = ⊥ := Subgroup.card_eq_one.mp hd
    exact hz1 (Subgroup.mem_bot.mp (hbot ▸ hzG))
  have hrG : r ∣ Nat.card G := hrd.trans (Subgroup.card_subgroup_dvd_card H)
  have hnd := hr r hrp h5 hrG d hd1 hdk
  let c : Equiv.Perm G := MulAut.toPerm G (MulAut.conj (x : G))
  have hcapp : ∀ g, c g = (x : G) * g * (x : G)⁻¹ := fun g => rfl
  have hmem_iff : ∀ g, c g ∈ omegaCenter Q ↔ g ∈ omegaCenter Q := by
    intro g
    refine ⟨fun hg => ?_, fun hg => Cor332.conj_mem_omegaCenter hxN hg⟩
    have h := Cor332.conj_mem_omegaCenter ((Subgroup.normalizer (Q : Set G)).inv_mem hxN) hg
    rw [hcapp] at h
    simpa [mul_assoc] using h
  let p : G → Prop := fun g => g ∈ omegaCenter Q ∧ g ≠ 1
  have hp : ∀ g, p (c g) ↔ p g := by
    intro g
    refine and_congr (hmem_iff g) ?_
    rw [hcapp]
    simp
  let σ : Equiv.Perm {g // p g} := c.subtypePerm hp
  have hxr : (x : G) ^ r = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
  have hcr : c ^ r = 1 := by
    have : MulAut.toPerm G (MulAut.conj (x : G)) ^ r =
        MulAut.toPerm G (MulAut.conj ((x : G) ^ r)) := by
      rw [map_pow, map_pow]
    rw [this, hxr, map_one, map_one]
  have hσr : σ ^ r ^ 1 = 1 := by
    rw [pow_one]
    ext a
    have h1 : ((σ ^ r) a : G) = (c ^ r) a := by
      change (((c.subtypePerm hp) ^ r) a : G) = _
      rw [Equiv.Perm.subtypePerm_pow]
      rfl
    rw [h1, hcr]
    rfl
  have : Fintype {g // p g} := Fintype.ofFinite _
  have hcard : Fintype.card {g // p g} = 2 ^ d - 1 := by
    have e : {g : omegaCenter Q // (g : G) ≠ 1} ≃ {g // p g} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun g : G => g ∈ omegaCenter Q)
        (fun g : G => g ≠ 1)
    have : Fintype (omegaCenter Q) := Fintype.ofFinite _
    rw [← Fintype.card_congr e]
    have h1 : Fintype.card {g : omegaCenter Q // (g : G) ≠ 1} =
        Fintype.card {g : omegaCenter Q // ¬ g = 1} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun g => by simp)
    have h2 : Fintype.card {g : omegaCenter Q // ¬ g = 1} =
        Fintype.card (omegaCenter Q) - Fintype.card {g : omegaCenter Q // g = 1} :=
      Fintype.card_subtype_compl _
    rw [h1, h2, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hd]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := r) (n := 1)
    (by rw [hcard]; exact hnd) hσr
  have hfix : (x : G) * a.1 * (x : G)⁻¹ = a.1 := congrArg Subtype.val ha
  have hcomm : (x : G) * a.1 = a.1 * (x : G) := by
    have := congrArg (· * (x : G)) hfix
    simpa [mul_assoc] using this
  have ha2 : orderOf a.1 = 2 := by
    have hsq : a.1 ^ 2 = 1 := (mem_omegaCenter.mp a.2.1).2.2
    exact orderOf_eq_prime hsq a.2.2
  exact hC (x : G) a.1 ha2 hcomm r hrp h5 hxo

theorem TwoLocalsTwoThree.of_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G')
    (h : TwoLocalsTwoThree G') : TwoLocalsTwoThree G := by
  intro Q H hQ hQ2 hHQ r hr hrd
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hbij : Function.Bijective e.toMonoidHom := e.bijective
  have hQ' : Q.map e.toMonoidHom ≠ ⊥ := fun hbot =>
    hQ ((Subgroup.map_eq_bot_iff_of_injective Q hinj).mp hbot)
  have hHQ' : H.map e.toMonoidHom ≤
      normalizer ((Q.map e.toMonoidHom : Subgroup G') : Set G') := by
    rw [← Subgroup.map_normalizer_eq_of_bijective Q hbij]
    exact Subgroup.map_mono hHQ
  have hcard : Nat.card (H.map e.toMonoidHom) = Nat.card H := Subgroup.card_map_of_injective hinj
  exact h _ _ hQ' (hQ2.map e.toMonoidHom) hHQ' r hr (hcard ▸ hrd)

end TwoThree

theorem twoLocalsTwoThree_psl2
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hF : (∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1)) :
    TwoLocalsTwoThree PSL(2, ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  refine twoLocalsTwoThree_of 2 ?_ ?_ ?_
  · intro E hE
    simpa using card_le_four_psl2_zmod (by omega) E hE
  · intro r hr h5 hrG d hd1 hdk h
    have hpos : 0 < 2 ^ d - 1 := by
      have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
      omega
    have hle := Nat.le_of_dvd hpos h
    have h4 : 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hdk
    omega
  · intro x z hz hxz r hr h5 hxo
    exact not_orderOf_commute_involution_psl2 hp hp7 hF x z hz hxz hr h5 hxo

theorem twoLocalsTwoThree_psl33 : TwoLocalsTwoThree PSL(3, ZMod 3) := by
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine twoLocalsTwoThree_of 4 ?_ ?_ ?_
  · intro E hE
    have hEp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
    have hdvd : 2 ^ n ∣ 5616 :=
      hn ▸ (Subgroup.card_subgroup_dvd_card E).trans card_psl33_dvd
    by_contra hlt
    have h5 : 2 ^ 5 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by
      by_contra h
      have : n ≤ 4 := by omega
      have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
      omega)
    have := h5.trans hdvd
    omega
  · intro r hr h5 hrG d hd1 hdk h
    have hr5616 : r ∣ 5616 := hrG.trans card_psl33_dvd
    have hpos : 0 < 2 ^ d - 1 := by
      have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
      omega
    have hle := Nat.le_of_dvd hpos h
    have h16 : 2 ^ d ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hdk
    have : r ≤ 15 := by omega
    interval_cases r <;> interval_cases d <;> omega
  · intro x z hz hxz r hr h5 hxo
    have hdvd := orderOf_dvd_of_commute_involution (F := ZMod 3)
      (by rw [Nat.card_zmod]; decide) hz hxz
    rw [hxo, Nat.card_zmod] at hdvd
    have h48 : r ∣ 2 ^ 4 * 3 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hr).mp h48 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h
      omega

theorem twoLocalsTwoThree_nativeM11 :
    TwoLocalsTwoThree CFSG.Blueprint.NativeSporadic.M11 := by
  refine twoLocalsTwoThree_of 3 card_le_eight_of_isElemAbelian_nativeM11 ?_ ?_
  · intro r hr h5 hrG d hd1 hdk h
    rw [CFSG.Semidihedral.GL2Recognition.card_nativeM11] at hrG
    have hpos : 0 < 2 ^ d - 1 := by
      have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
      omega
    have hle := Nat.le_of_dvd hpos h
    have h8 : 2 ^ d ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hdk
    have : r ≤ 7 := by omega
    interval_cases r <;> interval_cases d <;> omega
  · intro x z hz hxz r hr h5
    exact not_orderOf_commute_involution_nativeM11 x z hz hxz hr h5

theorem twoLocalsTwoThree_of_uniqueSmallModel
    {G : Type*} [Group G] (h : UniqueSmallModel G) : TwoLocalsTwoThree G := by
  rcases h with ⟨p, hp, hp7, hpF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact TwoLocalsTwoThree.of_mulEquiv e (twoLocalsTwoThree_psl2 hp hp7 hpF)
  · exact TwoLocalsTwoThree.of_mulEquiv e twoLocalsTwoThree_psl33
  · exact TwoLocalsTwoThree.of_mulEquiv
      (e.trans (CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11.symm.trans
        (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11)))
      twoLocalsTwoThree_nativeM11

variable {G : Type} [Group G] [Finite G]

theorem false_of_isXi_of_fusionIsBenderGroup (hB : fusionIsBenderGroup G) {T X : Subgroup G}
    (hX : IsXi T X) : False := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hBB⟩ : ∃ q k : ℕ, fusionBenderBorel G q k := by
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv G e.toEquiv
      exact ⟨2 ^ f, 1, (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
    · have : Finite (PSU3 2 f) := Finite.of_equiv G e.toEquiv
      exact ⟨2 ^ f, 3, (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
    · have : Finite (Sz a) := Finite.of_equiv G e.toEquiv
      exact ⟨2 ^ (2 * a + 1), 2, (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩
  have hR : pCoreOf 2 (X ⊔ T) ≠ ⊥ := hX.2.2.1
  obtain ⟨S, hRS⟩ := (pCoreOf_isPGroup 2 (X ⊔ T)).exists_le_sylow
  obtain ⟨hSE, ⟨D, hDc, -, -, hSD⟩, -⟩ := hBB S
  set B := normalizer (((S : Subgroup G)) : Set G) with hBdef
  have hXB : X ≤ B :=
    (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T))).trans
      (normalizer_le_of_stronglyEmbedded hSE hR hRS)
  obtain ⟨-, -, -, p, hp, hp2, -, hidx, -⟩ := id hX
  have : Fact p.Prime := ⟨hp⟩
  have hpX : p ∣ Nat.card X := by
    have h : p ∣ (pCoreOf 2 X).relIndex X := by
      rcases hidx with h | ⟨h, -⟩ <;> rw [h] <;> exact dvd_pow_self p (by norm_num)
    exact h.trans (relIndex_dvd_card _ _)
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge p (H := X) (P := ⊥) bot_le IsPGroup.of_bot
  have hSB : (S : Subgroup G) ≤ B := le_normalizer
  have hDB : D ≤ B := hSD ▸ le_sup_right
  set S' := (S : Subgroup G).subgroupOf B with hS'
  set D' := D.subgroupOf B with hD'
  have hS'n : S'.Normal := normal_in_normalizer
  have hD'c : IsCyclic D' :=
    isCyclic_of_surjective (subgroupOfEquivOfLe hDB).symm.toMonoidHom
      (subgroupOfEquivOfLe hDB).symm.surjective
  have htop : S' ⊔ D' = ⊤ := by
    rw [← subgroupOf_sup hSB hDB, hSD, subgroupOf_self]
  have hmap : D'.map (QuotientGroup.mk' S') = ⊤ := by
    have h1 : (S' ⊔ D').map (QuotientGroup.mk' S') = ⊤ := by
      rw [htop, map_top_of_surjective _ (QuotientGroup.mk'_surjective S')]
    rwa [Subgroup.map_sup, (map_eq_bot_iff S').2 (QuotientGroup.ker_mk' S').ge, bot_sup_eq] at h1
  have hsurj : Function.Surjective ((QuotientGroup.mk' S').comp D'.subtype) := by
    intro y
    obtain ⟨d, hd, rfl⟩ := mem_map.1 (hmap ▸ mem_top y)
    exact ⟨⟨d, hd⟩, rfl⟩
  have : IsCyclic (↥B ⧸ S') := isCyclic_of_surjective _ hsurj
  have hPB : P ≤ B := hP.le.trans hXB
  have hPS : P ⊓ (S : Subgroup G) = ⊥ :=
    (IsPGroup.disjoint_of_ne p 2 hp2 P S hP.isPGroup S.isPGroup').eq_bot
  let f : ↥(P.subgroupOf B) →* ↥B ⧸ S' := (QuotientGroup.mk' S').comp (P.subgroupOf B).subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h0 : ((a : B) : ↥B ⧸ S') = 1 := ha
    have h1 : ((a : B) : G) ∈ (S : Subgroup G) :=
      mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (a : B)).mp h0)
    have h3 : ((a : B) : G) ∈ P ⊓ (S : Subgroup G) := ⟨a.2, h1⟩
    rw [hPS, mem_bot] at h3
    exact Subtype.ext (Subtype.ext h3)
  have hcyc : IsCyclic ↥(P.subgroupOf B) := isCyclic_of_injective f hf
  have hcard : Nat.card ↥(P.subgroupOf B) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv
  have hexp : Monoid.exponent ↥(P.subgroupOf B) ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      Subtype.ext (Subtype.ext (by simpa using hX.pow_eq_one hp2 hpX hP a.2))
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have hle := Nat.le_of_dvd hp.pos hexp
  have hsq := hX.sq_le_card_sylow hp2 hpX hP
  have hlt : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

theorem exists_isHStar_or_isXiMinus
    (h211 : U3.UniqueThreeCaseModelReduction) {T X : Subgroup G} (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hX : IsXi T X) (hU : IsUniqueM (X ⊔ T) (normalizer (X : Set G))) :
    (∃ H : Subgroup G, IsHStar T (normalizer (X : Set G)) H) ∨ IsXiMinus T X := by
  by_cases hH : ∃ H : Subgroup G, IsHStar T (normalizer (X : Set G)) H
  · exact Or.inl hH
  right
  have hMmax := hU.1.1
  have hTM : T ≤ normalizer (X : Set G) := le_sup_right.trans hU.1.2
  have huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → T ≤ M' →
      M' = normalizer (X : Set G) := by
    intro M' hM' hTM'
    by_contra hne
    exact hH (exists_isHStar_of hMmax hM' hTM' hne)
  have hset : UniqueSetting G T (normalizer (X : Set G)) :=
    { simple := hs
      nonabelian := hnab
      qtke := qtkeCore_of_cat hnab hQ
      sylow := CFSG.Quasithin.H13.U3.isSylowTwoOf_top_of_quasithin hT
      maxLocal := hMmax
      le := hTM
      unique := huniq }
  rcases h211 G T _ hset with hB | hS
  · exact (false_of_isXi_of_fusionIsBenderGroup hB hX).elim
  · refine ⟨hX, Or.inl fun q hq hqX => ?_⟩
    exact twoLocalsTwoThree_of_uniqueSmallModel hS (pCoreOf 2 (X ⊔ T)) X hX.2.2.1
      (pCoreOf_isPGroup 2 _)
      (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T))) q hq hqX

theorem input3213_of
    (h316 : Theorem316Statement) (h137 : EmptyFaithfulMultiple.Input137)
    (h211 : U3.UniqueThreeCaseModelReduction) : EmptyFaithfulMultiple.Input3213 := by
  intro G _ _ T hs hnab hQ hT X hXs
  have hU := h137 G T hs hnab hQ hT X hXs.1
  rcases exists_isHStar_or_isXiMinus h211 hs hnab hQ hT hXs.1.1 hU with hH | hXm
  · exact isXiMinus_of_isHStar h316 h137 hs hnab hQ hT hXs hH
  · exact hXm

theorem input3213_of_316
    (h316 : Theorem316Statement) : EmptyFaithfulMultiple.Input3213 :=
  input3213_of h316 NQCore.input137_holds U3.uniqueThreeCaseModelReduction_holds

end CFSG.Quasithin.H13.NQBlock
