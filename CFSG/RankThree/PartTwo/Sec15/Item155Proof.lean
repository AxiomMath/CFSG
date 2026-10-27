module

public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Char

omit [Finite G]

theorem characteristic_map_mulEquiv155 {P P' : Type*} [Group P] [Group P'] (e : P ≃* P')
    {D : Subgroup P} (hD : D.Characteristic) : (D.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro ψ
  have h1 := Subgroup.characteristic_iff_map_eq.mp hD ((e.trans ψ).trans e.symm)
  calc (D.map e.toMonoidHom).map ψ.toMonoidHom
      = (D.map ((e.trans ψ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp
    _ = D.map e.toMonoidHom := by rw [h1]

theorem characteristic_subgroupOf_map {R H : Subgroup G} (hRH : R ≤ H) {C : Subgroup ↥H}
    (hCR : C ≤ R.subgroupOf H) (hC : (C.subgroupOf (R.subgroupOf H)).Characteristic) :
    ((C.map H.subtype).subgroupOf R).Characteristic := by
  have heq : (C.map H.subtype).subgroupOf R =
      (C.subgroupOf (R.subgroupOf H)).map (Subgroup.subgroupOfEquivOfLe hRH).toMonoidHom := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, hCR hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, Subgroup.subgroupOfEquivOfLe_apply_coe]
      exact hyx
    · rintro ⟨z, hz, hzx⟩
      refine ⟨z, Subgroup.mem_subgroupOf.mp hz, ?_⟩
      have := congrArg Subtype.val hzx
      rw [MulEquiv.coe_toMonoidHom, Subgroup.subgroupOfEquivOfLe_apply_coe] at this
      exact this
  rw [heq]
  exact characteristic_map_mulEquiv155 _ hC

theorem omegaOneCenter_top_characteristic155 (P : Type*) [Group P] :
    (CFSG.omegaOneCenter (⊤ : Subgroup P)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rintro _ ⟨z, ⟨⟨w, hw, rfl⟩, hz2⟩, rfl⟩
  refine ⟨⟨⟨φ w, Subgroup.mem_top _⟩, Subgroup.mem_center_iff.mpr fun u => ?_, rfl⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨u, -⟩ := u
    change u * φ w = φ w * u
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨φ.symm u, Subgroup.mem_top _⟩)
    change φ.symm u * w = w * φ.symm u at h1
    have h2 := congrArg φ h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  · change (φ w) ^ 2 = 1
    rw [← map_pow]
    have : ((w : P)) ^ 2 = 1 := hz2
    rw [this, map_one]

theorem higherElemThompson_characteristic155 (P : Type*) [Group P] [Finite P] (j : ℕ) :
    (CFSG.higherElemThompson P j).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [CFSG.higherElemThompson, (Subgroup.gc_map_comap φ.toMonoidHom).l_sSup]
  refine iSup₂_le fun E hE => le_sSup ?_
  rw [CFSG.mem_higherElemThompsonFamily_iff] at hE ⊢
  obtain ⟨hEel, hEc⟩ := hE
  have e : ↥E ≃* ↥(E.map φ.toMonoidHom) := E.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨?_, by rw [← Nat.card_congr e.toEquiv, hEc]⟩
  have hcomm : ∀ a b : ↥(E.map φ.toMonoidHom), a * b = b * a := fun a b => by
    have := hEel.1.is_comm.comm (e.symm a) (e.symm b)
    have h2 := congrArg e this
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  have hexp : ∀ x : ↥(E.map φ.toMonoidHom), x ^ 2 = 1 := fun x => by
    have h1 : (e.symm x) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEel.exponent_dvd_p _
    have h2 := congrArg e h1
    rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
  exact
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }

theorem omegaOneCenter_top_ne_bot {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hP : IsPGroup 2 P) : CFSG.omegaOneCenter (⊤ : Subgroup P) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := hP.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup (Subgroup.center P)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center P) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  intro hbot
  have hmem : (z : P) ∈ CFSG.omegaOneCenter (⊤ : Subgroup P) := by
    refine ⟨⟨⟨z, Subgroup.mem_top _⟩, Subgroup.mem_center_iff.mpr fun u => ?_, rfl⟩, ?_⟩
    · apply Subtype.ext
      exact Subgroup.mem_center_iff.mp z.2 u
    · rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext hmem
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem higherElemThompson_zero_ne_bot {P : Type*} [Group P] [Finite P] [Nontrivial P]
    (hP : IsPGroup 2 P) : CFSG.higherElemThompson P 0 ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := {r : ℕ | ∃ E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ r} with hs
  have hbdd : BddAbove s := by
    refine ⟨Nat.card P, fun r hr => ?_⟩
    obtain ⟨E, -, hE⟩ := hr
    calc r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card P := Subgroup.card_le_card_group E
  have hdvd : 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have h1 : 1 < Nat.card P := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hEz : IsElementaryAbelian 2 (Subgroup.zpowers z) := by
    have hexp : ∀ x : ↥(Subgroup.zpowers z), x ^ 2 = 1 := fun x => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, hz2, one_zpow]
    exact
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  have h1s : 1 ∈ s := ⟨Subgroup.zpowers z, hEz, by rw [Nat.card_zpowers, hz, pow_one]⟩
  have hrank : 1 ≤ CFSG.pRank 2 P := le_csSup hbdd h1s
  obtain ⟨E, hE, hEc⟩ := Nat.sSup_mem ⟨1, h1s⟩ hbdd
  change Nat.card E = 2 ^ CFSG.pRank 2 P at hEc
  have hEmem : E ∈ CFSG.higherElemThompsonFamily P 0 :=
    (CFSG.mem_higherElemThompsonFamily_iff 0 E).mpr ⟨hE, by rw [Nat.sub_zero]; exact hEc⟩
  intro hbot
  have hle : E ≤ CFSG.higherElemThompson P 0 := le_sSup hEmem
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hEc
  have h2 : 2 ≤ 2 ^ CFSG.pRank 2 P :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ CFSG.pRank 2 P := Nat.pow_le_pow_right (by norm_num) hrank
  omega

end Char

omit [Finite G] in
theorem mem_pCoreOf_iff155 {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ CFSG.Open.pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

omit [Finite G] in
theorem le_normalizer_map_of_normal155 {H : Subgroup G} {D : Subgroup ↥H} (hD : D.Normal) :
    H ≤ Subgroup.normalizer ((D.map H.subtype : Subgroup G) : Set G) := by
  have hle : D.map H.subtype ≤ H := Subgroup.map_subtype_le D
  have hD' : ((D.map H.subtype).subgroupOf H).Normal := by
    rwa [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hD'

theorem exists_mem_scriptQPiStar155 {A : Subgroup G} (Y : Subgroup G) (π : Set Nat.Primes) :
    ∃ S : Subgroup G, S ∈ scriptQPiStar A (lB A) Y π := by
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) Y π := by
    have hπ : IsPiSubgroup π (⊥ : Subgroup G) := fun q hq => by
      rw [Subgroup.card_bot] at hq
      exact absurd (Nat.le_of_dvd one_pos hq) (by have := q.2.two_le; omega)
    refine ⟨⟨⟨⟨le_top, (bot_mem_invariantPiSubgroups ⊤ A (piCompl 3)).2.1,
      (bot_mem_invariantPiSubgroups ⊤ A (piCompl 3)).2.2⟩, fun B _ => ?_⟩, bot_le⟩, hπ⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) Y π)) hbot
  exact ⟨S, hS⟩

theorem isY155_of_mem_scriptY0 {A K : Subgroup G} (hK : K ∈ scriptY0 A (lB A)) :
    IsY155 A K ∧ oPrimeResidualOf 3 K = K := by
  have hres : oPrimeResidualOf 3 K = K := hK.1.2.1.symm
  refine ⟨⟨⟨hK.2, hK.1.2.2.1⟩, by rw [hres]; exact hK.1, ?_⟩, hres⟩
  rw [hres]
  exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).symm

theorem omg155_of_le {A X K : Subgroup G} (hXK : X ≤ K)
    (h : ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') : omg155 A K := by
  obtain ⟨c', L', hc', hL', heq⟩ := h
  refine Or.inr ⟨c', L', hc', hL', le_antisymm ?_ ?_⟩
  · calc L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L' := heq
      _ ≤ (L' ⊓ K) ⊔ CFSG.Open.pCoreOf 2 L' := sup_le_sup_right (inf_le_inf_left _ hXK) _
  · exact sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 L')

theorem le_n155_of_isPLocal {A : Subgroup G} (h153 : Item153Main A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) {H₀ : Subgroup G} (hH : IsPLocal 2 H₀) (hKA : K ⊔ A ≤ H₀) :
    H₀ ≤ n155 A K := by
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hH
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle (hKA hx)⟩
  rw [(h153 K hK).1, Set.mem_singleton_iff] at hmem
  exact hle.trans hmem.le

theorem claim155_of_le_normalizer {A : Subgroup G} (h153 : Item153Main A (lB A))
    {K Y : Subgroup G} (hK : K ∈ scriptY0Star A (lB A))
    (hKR : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G))
    (hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) : Claim155 A K Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro C hC1 hCR hCc
  have hNC : Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    have h' := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := CFSG.Open.pCoreOf 2 Y) (C.subgroupOf (CFSG.Open.pCoreOf 2 Y))
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCR] at h'
  have hC2 : IsPGroup 2 C := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y).to_le hCR
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hC2 hC1
  exact (delta_le _).trans (le_n155_of_isPLocal h153 hK hloc (sup_le (hKR.trans hNC)
    (hAR.trans hNC)))

theorem le_of_inf_normalizer_le155 {R Q : Subgroup G} (hR2 : IsPGroup 2 R) (hQ2 : IsPGroup 2 Q)
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hN : Q ⊓ Subgroup.normalizer (R : Set G) ≤ R) : Q ≤ R := by
  by_contra hQR
  set H := R ⊔ Q with hH
  have hH2 : IsPGroup 2 H := IsPGroup.to_sup_of_normal_right' hR2 hQ2 hRQ
  have hRH : R ≤ H := le_sup_left
  have hlt : R.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hQR fun x hx => ?_
    have : (⟨x, (le_sup_right : Q ≤ R ⊔ Q) hx⟩ : H) ∈ R.subgroupOf H :=
      htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent H := hH2.isNilpotent
  obtain ⟨y, hyN, hyR⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hRH, Subgroup.mem_subgroupOf] at hyN
  have hy : (y : G) ∈ ((R : Set G) * (Q : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R Q hRQ]
    exact y.2
  obtain ⟨r, hr, q, hq, hrq⟩ := hy
  have hqN : q ∈ Subgroup.normalizer (R : Set G) := by
    have : q = r⁻¹ * y := by rw [← hrq]; group
    rw [this]
    exact mul_mem (Subgroup.le_normalizer (inv_mem hr)) hyN
  have hqR : q ∈ R := hN ⟨hq, hqN⟩
  exact hyR (Subgroup.mem_subgroupOf.mpr (hrq ▸ mul_mem hr hqR))

theorem exists_char_normal_of_hyp315 (h315 : Item3_15) {H S : Subgroup G} (hyp : Hyp315 H S) :
    (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧
      H ≤ Subgroup.normalizer (C : Set G)) ∨ IsScriptLBlock ⊤ (oResidual 2 ↥H) := by
  obtain ⟨hSH, hF, htype, A', hA', hmax, hS⟩ := hyp
  rcases h315 ↥H hF htype A' hA' hmax (S.subgroupOf H) hS with ⟨C, hC1, hCS, hCc, hCn⟩ | hbl
  · refine Or.inl ⟨C.map H.subtype, ?_, ?_, characteristic_subgroupOf_map hSH hCS hCc,
      le_normalizer_map_of_normal155 hCn⟩
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
      exact hC1
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hCS hy)
  · exact Or.inr hbl

theorem exists_maxT155 {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    ∃ Y₀ M₀ T₀ : Subgroup G, Ctx155 A X K Y₀ M₀ T₀ ∧ MaxT155 A X K T₀ := by
  set s := {n : ℕ | ∃ Y' M' T' : Subgroup G, Ctx155 A X K Y' M' T' ∧ Nat.card T' = n} with hs
  have hbdd : BddAbove s := by
    refine ⟨Nat.card G, fun n hn => ?_⟩
    obtain ⟨Y', M', T', -, rfl⟩ := hn
    exact Subgroup.card_le_card_group T'
  have hne : s.Nonempty := ⟨Nat.card T, Y, M, T, hC, rfl⟩
  obtain ⟨Y₀, M₀, T₀, hC₀, hT₀⟩ := Nat.sSup_mem hne hbdd
  refine ⟨Y₀, M₀, T₀, hC₀, fun Y' M' T' hC' => ?_⟩
  rw [hT₀]
  exact le_csSup hbdd ⟨Y', M', T', hC', rfl⟩

end CFSG.RankThree.PartTwo.Sec15
