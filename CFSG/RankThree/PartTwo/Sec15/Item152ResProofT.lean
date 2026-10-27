module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofT
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofFX
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Proof152ResT

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
theorem mem_of_commutatorElement_mem {X W : Subgroup G} (hWX : W ≤ X)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) {u o : G} (hu : u ∈ X) (ho : o ∈ X)
    (hc : ⁅o, u⁆ ∈ W) {n m : ℕ} (hn : Nat.Coprime n (2 ^ m)) (hun : u ^ n = 1)
    (huo : (u * o) ^ n = 1) (hom : o ^ 2 ^ m = 1) : o ∈ W := by
  have : (W.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hXW
  set π := QuotientGroup.mk' (W.subgroupOf X) with hπ
  have hker : ∀ z : ↥X, π z = 1 ↔ (z : G) ∈ W := fun z => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set u' : ↥X := ⟨u, hu⟩ with hu'
  set o' : ↥X := ⟨o, ho⟩ with ho'
  have hcomm : Commute (π o') (π u') := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hker]
    simpa [hu', ho', commutatorElement_def] using hc
  have hu1 : π u' ^ n = 1 := by
    rw [← map_pow]
    have : u' ^ n = 1 := Subtype.ext (by simpa [hu'] using hun)
    rw [this, map_one]
  have huo1 : (π u' * π o') ^ n = 1 := by
    rw [← map_mul, ← map_pow]
    have : (u' * o') ^ n = 1 := Subtype.ext (by simpa [hu', ho'] using huo)
    rw [this, map_one]
  have hon : π o' ^ n = 1 := by
    rw [hcomm.symm.mul_pow, hu1, one_mul] at huo1
    exact huo1
  have hom' : π o' ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : o' ^ 2 ^ m = 1 := Subtype.ext (by simpa [ho'] using hom)
    rw [this, map_one]
  have hord : orderOf (π o') = 1 :=
    Nat.dvd_one.mp (hn.gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hon) (orderOf_dvd_of_pow_eq_one hom'))
  rw [orderOf_eq_one_iff, hker] at hord
  exact hord

theorem le_normalizer_sup_of_commutator_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X P O W : Subgroup G} (hPX : P ≤ X) (hOX : O ≤ X) (hWX : W ≤ X) (hP : IsPGroup p P)
    (hO : IsPGroup 2 O) (hPO : P ≤ Subgroup.normalizer (O : Set G))
    (hXPO : X ≤ Subgroup.normalizer ((P ⊔ O : Subgroup G) : Set G))
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hOXW : ⁅O, X⁆ ≤ W) :
    X ≤ Subgroup.normalizer ((P ⊔ W : Subgroup G) : Set G) := by
  have hPW : ((P ⊔ W : Subgroup G) : Set G) = (P : Set G) * (W : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P W (hPX.trans hXW)
  have hPOs : ((P ⊔ O : Subgroup G) : Set G) = (P : Set G) * (O : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P O hPO
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  intro x hx
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  rw [← SetLike.mem_coe, hPW] at hy
  obtain ⟨u, hu, w, hw, rfl⟩ := hy
  have hxu : x * u * x⁻¹ ∈ P ⊔ W := by
    have h1 : x * u * x⁻¹ ∈ ((P ⊔ O : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hXPO hx) u).mp (Subgroup.mem_sup_left hu)
    rw [hPOs] at h1
    obtain ⟨u', hu', o, ho, hxuo⟩ := h1
    change u' * o = x * u * x⁻¹ at hxuo
    have hoW : o ∈ W := by
      obtain ⟨m, hm⟩ := hO ⟨o, ho⟩
      have hom : o ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
      have hu'n : u' ^ (p ^ k) = 1 := by
        have h := pow_card_eq_one' (G := ↥P) (x := ⟨u', hu'⟩)
        rw [hk] at h
        simpa using congrArg Subtype.val h
      have hun : u ^ (p ^ k) = 1 := by
        have h := pow_card_eq_one' (G := ↥P) (x := ⟨u, hu⟩)
        rw [hk] at h
        simpa using congrArg Subtype.val h
      have huo : (u' * o) ^ (p ^ k) = 1 := by
        rw [hxuo, conj_pow, hun, mul_one, mul_inv_cancel]
      exact mem_of_commutatorElement_mem hWX hXW (hPX hu') (hOX ho)
        (hOXW (Subgroup.commutator_mem_commutator ho (hPX hu'))) hcop hu'n huo hom
    rw [← hxuo]
    exact mul_mem (Subgroup.mem_sup_left hu') (Subgroup.mem_sup_right hoW)
  have hxw : x * w * x⁻¹ ∈ P ⊔ W :=
    Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hXW hx) w).mp hw)
  rw [show x * (u * w) * x⁻¹ = (x * u * x⁻¹) * (x * w * x⁻¹) by group]
  exact mul_mem hxu hxw

omit [Finite G] in
theorem coe_sup_eq_mul_of_le_normalizer {T P W : Subgroup G} (hWT : W ≤ T)
    (hPW : P ≤ Subgroup.normalizer (W : Set G))
    (hTN : T ≤ Subgroup.normalizer ((P ⊔ W : Subgroup G) : Set G)) :
    ((T ⊔ P : Subgroup G) : Set G) = (T : Set G) * (P : Set G) := by
  have h1 : ((T ⊔ (W ⊔ P) : Subgroup G) : Set G) = (T : Set G) * ((W ⊔ P : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T (W ⊔ P) (by rwa [sup_comm])
  have h2 : ((W ⊔ P : Subgroup G) : Set G) = (W : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W P hPW
  have h3 : (T : Set G) * (W : Set G) = T := by
    refine Set.Subset.antisymm ?_ fun t ht => ⟨t, ht, 1, W.one_mem, mul_one t⟩
    rintro _ ⟨t, ht, w, hw, rfl⟩
    exact mul_mem ht (hWT hw)
  have hTP : ((T ⊔ (W ⊔ P) : Subgroup G) : Set G) = (T : Set G) * (P : Set G) := by
    rw [h1, h2, ← mul_assoc, h3]
  refine Set.Subset.antisymm ?_ ?_
  · rw [← hTP]
    exact sup_le_sup_left le_sup_right T
  · rintro _ ⟨t, ht, u, hu, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hu)

variable {A : Subgroup G}

theorem eq_deltaZero_of_bot (hA : Late.IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYres : Y = oPrimeResidualOf 3 Y) (hYdelta : Y = delta A (lB A) Y) :
    Y = deltaZero A (lB A) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdelta, -, hnorm⟩ := rank3II_14_5 hA (isNaturalFamily_lB A) hbot hAY
  set D := deltaZero A (lB A) Y with hD
  set C' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hC'
  have hYeq : Y = D ⊔ C' := hYdelta.trans hdelta
  have hYN : Y ≤ Subgroup.normalizer (D : Set G) := hYdelta.le.trans hnorm
  have hDY : D ≤ Y := deltaZero_le Y
  have hC'N : C' ≤ Subgroup.normalizer (D : Set G) := inf_le_right.trans hYN
  have hN : (D.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).mpr hYN
  have hcop : Nat.Coprime 3 (Nat.card C') :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  have key : ∀ x : Y, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ D.subgroupOf Y := by
    rintro x ⟨k, hk⟩
    have hx : (x : G) ∈ ((D : Set G) * (C' : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left D C' hC'N, ← hYeq]
      exact x.2
    obtain ⟨d, hd, c, hc, hdc⟩ := hx
    have hcY : c ∈ Y := (Subgroup.mem_inf.mp hc).2
    have hdY : d ∈ Y := hDY hd
    let π : Y →* Y ⧸ D.subgroupOf Y := QuotientGroup.mk' (D.subgroupOf Y)
    have hπd : π ⟨d, hdY⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := D.subgroupOf Y) _).mpr (Subgroup.mem_subgroupOf.mpr hd)
    have hπx : π x = π ⟨c, hcY⟩ := by
      have hxdc : x = ⟨d, hdY⟩ * ⟨c, hcY⟩ := Subtype.ext hdc.symm
      rw [hxdc, map_mul, hπd, one_mul]
    have hc1 : (⟨c, hcY⟩ : Y) ^ Nat.card C' = 1 := by
      have h : (⟨c, hc⟩ : C') ^ Nat.card C' = 1 := pow_card_eq_one'
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h' ⊢
      exact h'
    have h1 : π x ^ Nat.card C' = 1 := by rw [hπx, ← map_pow, hc1, map_one]
    have h2 : π x ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have hord : orderOf (π x) = 1 := Nat.dvd_one.mp ((Nat.Coprime.pow_left k hcop).gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1))
    rw [orderOf_eq_one_iff] at hord
    exact (QuotientGroup.eq_one_iff (N := D.subgroupOf Y) _).mp hord
  have hres : oPrimeResidualOf 3 Y ≤ D := by
    unfold oPrimeResidualOf oPrimeResidual
    rw [← Subgroup.map_subgroupOf_eq_of_le hDY]
    exact Subgroup.map_mono ((Subgroup.closure_le _).mpr fun x hx => key x hx)
  exact le_antisymm (hYres.le.trans hres) hDY

theorem commutator_pCoreOf_mem_scriptQ_of_le (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {X : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX0 : X = deltaZero A (lB A) X)
    (h147 : ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X)) :
    ⁅CFSG.Open.pCoreOf 2 X, X⁆ ∈ scriptQ A (lB A) := by
  have hK := Sec17.Proof17Q0.pPrimeCoreOf_mem_invariantPiSubgroups hAX
  have hle : ⁅CFSG.Open.pCoreOf 2 X, X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X) :=
    calc ⁅CFSG.Open.pCoreOf 2 X, X⁆ ≤ ⁅pPrimeCoreOf 3 X, X⁆ :=
          Subgroup.commutator_mono (Sec17.Proof17Q0.pCoreOf_le_pPrimeCoreOf X) le_rfl
      _ = ⁅X, pPrimeCoreOf 3 X⁆ := Subgroup.commutator_comm _ _
      _ = ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ :=
          congrArg (fun Z => ⁅Z, pPrimeCoreOf 3 X⁆) hX0
      _ ≤ _ := h147
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    hAX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  exact mem_scriptQ_of_le (delta_mem_scriptQ hA h146 hK) hle (le_normalizer_commutator hAV hAX)

theorem commutator_le_delta_of_eq_delta (hA : Late.IsE27 A) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) {X : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hXΔ : X = delta A (lB A) X) :
    ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X) := by
  have hK := Sec17.Proof17Q0.pPrimeCoreOf_mem_invariantPiSubgroups hAX
  have hXN : X ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) :=
    calc X = delta A (lB A) X := hXΔ
      _ ≤ _ := delta_le_normalizer_delta (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hK
          (le_normalizer_pPrimeCoreOf 3 X)
  exact rank3II_14_7_reduction hA h1444 h146 hAX ((pPrimeCoreOf_le 3 X).trans hXN)

theorem commutator_le_of_mem_scriptQPiStar (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {X T : Subgroup G} (hW : ⁅CFSG.Open.pCoreOf 2 X, X⁆ ∈ scriptQ A (lB A))
    (hT : T ∈ scriptQPiStar A (lB A) X (piOf 2)) : ⁅CFSG.Open.pCoreOf 2 X, X⁆ ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 X with hO
  set W := ⁅O, X⁆ with hWdef
  have hTX : T ≤ X := hT.prop.1.2
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hWO : W ≤ O := Subgroup.le_normalizer_iff_commutator_le_left.mp hXO
  have hXW : X ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator (A := X) hXO Subgroup.le_normalizer
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop
  have hW2 : IsPGroup 2 W := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X).to_le hWO
  have hTWQ : T ⊔ W ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 hA h146 hT.prop.1.1 hW (hTX.trans hXW)
  have hmem : T ⊔ W ∈ scriptQPi A (lB A) X (piOf 2) :=
    ⟨⟨hTWQ, sup_le hTX (hWO.trans hOX)⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
        (hT2.to_sup_of_normal_right' hW2 (hTX.trans hXW))⟩
  exact le_sup_right.trans (hT.2 hmem le_sup_left)

theorem coe_sup_eq_mul_of_mem_scriptQPiStar (hA : Late.IsE27 A) (h146 : Item146 A (lB A))
    {X P T : Subgroup G} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hPX : P ≤ X) (hP : IsPGroup p P)
    (hchar : ∃ R : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype) ∧ P ≤ R ∧
        (P.subgroupOf R).Characteristic)
    (hW : ⁅CFSG.Open.pCoreOf 2 X, X⁆ ∈ scriptQ A (lB A))
    (hT : T ∈ scriptQPiStar A (lB A) X (piOf 2)) :
    ((T ⊔ P : Subgroup G) : Set G) = (T : Set G) * (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 X with hO
  set W := ⁅O, X⁆ with hWdef
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hWO : W ≤ O := Subgroup.le_normalizer_iff_commutator_le_left.mp hXO
  have hXW : X ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator (A := X) hXO Subgroup.le_normalizer
  have hWT := commutator_le_of_mem_scriptQPiStar hA h146 hW hT
  have hXPW := le_normalizer_sup_of_commutator_le hp2 hPX hOX (hWO.trans hOX) hP
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) (hPX.trans hXO)
    (Proof152FX.le_normalizer_sup_pCoreOf hchar) hXW le_rfl
  exact coe_sup_eq_mul_of_le_normalizer hWT (hPX.trans hXW) (hT.prop.1.2.trans hXPW)

end Proof152ResT

open Proof152ResT

variable {G : Type} [Group G] [Finite G]

theorem step152ConfTPerm_of_le
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X)) :
    Step152ConfTPerm A (lB A) := by
  intro Y M X c' L' p P hpt hPd
  have hctx := hpt.ctx
  have hA : Late.IsE27 A := h.isE27
  have : Fact p.Prime := ⟨hPd.prime⟩
  have hPp : IsPGroup p P := by
    rcases hPd.type_p with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact IsPGroup.of_card h'
    · exact IsPGroup.of_card h'
  have hX := hctx.mem_comp
  have hX3 : X = oPrimeResidualOf 3 X :=
    eq_oPrimeResidualOf_of_le (isPerfect_of_mem_thetaComponentsIn hX)
      (isQuasisimple_theta_of_mem_thetaComponentsIn hX) hctx.le_x hctx.mem_y4.2.1
      (isPerfect_of_mem_scriptY4 hctx.mem_y4) (ne_bot_of_mem_scriptY4 hctx.mem_y4)
  have hX0 : X = deltaZero A (lB A) X :=
    eq_deltaZero_of_bot hA hbot hctx.norm_x hX3 hctx.delta_x
  have hXtop : X ≠ ⊤ := fun h' =>
    hctx.mem_y2.1.1 (top_le_iff.mp (h' ▸ le_of_mem_thetaComponentsIn hX))
  have hW := commutator_pCoreOf_mem_scriptQ_of_le hA h146 hctx.norm_x hX0
    (h147 X ⟨hXtop, hctx.norm_x⟩ hctx.delta_x)
  obtain ⟨T₀, hT₀, hT₀θ⟩ := Proof152ConfA.exists_two_subgroup_not_le_theta hctx
    h.toSec13Data.mem_partTwoF hA
  obtain ⟨T, hT₀T, hT⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) X (piOf 2))) hT₀
  exact ⟨T, hT, fun hTθ => hT₀θ (hT₀T.trans hTθ),
    coe_sup_eq_mul_of_mem_scriptQPiStar hA h146 hPd.odd hPd.le_px hPp hPd.char_p hW hT⟩

theorem step152ConfTPerm_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) : Step152ConfTPerm A (lB A) :=
  step152ConfTPerm_of_le h h146 hbot fun _ hXY hXΔ =>
    commutator_le_delta_of_eq_delta h.isE27 h1444 h146 hXY.2 hXΔ

theorem step152ConfTPermR_of
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) : Step152ConfTPermR :=
  fun G _ _ A c L hR => step152ConfTPerm_of hR.toSec14Std (h1444 G A c L hR.toSec14Std)
    (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std)

theorem step152ConfTR_of_items
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) : Step152ConfTR :=
  step152ConfTR_of (step152ConfTPermR_of h1444 h146 hbot)

end CFSG.RankThree.PartTwo.Sec15
