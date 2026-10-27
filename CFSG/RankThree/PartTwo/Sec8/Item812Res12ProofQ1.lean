module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofTools
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofQ2
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofPaExp
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGen
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec10.Item105
import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open Item812Res3 (IsMaxPSub)
open Subgroup

namespace Item812Res12

section Generic

variable {G : Type} [Group G]

theorem mem_zpowers_of_mem_zpowers_of_ne_one [Finite G] {c x : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hx : x ∈ zpowers c) (hx1 : x ≠ 1) : c ∈ zpowers x := by
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hle : zpowers x ≤ zpowers c := zpowers_le.mpr hx
  have hdvd : Nat.card (zpowers x) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers c, hco] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    apply hx1
    have h2 : zpowers x = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have h3 : x ∈ zpowers x := mem_zpowers x
    rw [h2, mem_bot] at h3
    exact h3
  · have heq : zpowers x = zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers c, hco])
    rw [heq]
    exact mem_zpowers c

theorem commute_of_inf_eq_bot {H K : Subgroup G} (hH : ∀ k ∈ K, ∀ x ∈ H, k * x * k⁻¹ ∈ H)
    (hK : ∀ h ∈ H, ∀ y ∈ K, h * y * h⁻¹ ∈ K) (hHK : H ⊓ K = ⊥) :
    ∀ x ∈ H, ∀ y ∈ K, x * y = y * x := by
  intro x hx y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ H := by
    have := H.mul_mem hx (hH y hy x⁻¹ (H.inv_mem hx))
    rwa [show x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ by group] at this
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ K := K.mul_mem (hK x hx y hy) (K.inv_mem hy)
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ H ⊓ K := ⟨h1, h2⟩
  rw [hHK, mem_bot] at h3
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

set_option maxRecDepth 100000 in
theorem exists_cube_root_zmod9sq : ∀ z : Multiplicative (ZMod 9 × ZMod 9), z ^ 3 = 1 →
    ∃ w : Multiplicative (ZMod 9 × ZMod 9), w ^ 3 = z := by
  decide

theorem exists_not_cube_one_zmod9sq : ∃ z : Multiplicative (ZMod 9 × ZMod 9), z ^ 3 ≠ 1 :=
  ⟨Multiplicative.ofAdd (1, 0), by decide⟩

theorem mem_normalizer_of_conj {Q H : Subgroup G} (hQ : ∀ q ∈ Q, ∀ x ∈ H, q * x * q⁻¹ ∈ H)
    {q : G} (hq : q ∈ Q) : q ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hQ q hq x, fun hx => ?_⟩
  have h1 := hQ q⁻¹ (Q.inv_mem hq) _ hx
  rwa [show q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x by group] at h1

end Generic

end Item812Res12


namespace Item812Res12

variable {G : Type} [Group G] [Finite G]

theorem card_le_three_mul_sec8R {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) {Q : Subgroup G}
    (hQp : IsPGroup 3 Q) (hQN : Q ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card Q ≤ 3 * Nat.card (sec8R Q X) := by
  classical
  set F := GaloisField 2 3 with hFdef
  set P := StatedProj (StatedSp 2 F) with hPdef
  set e : X ⧸ aschbacherSolvableCore 3 X ≃* P :=
    h.item89_X.some.trans (Sec4.projSpEquivStatedProj 2 F) with he
  set φ : Q →* CFSG.ComponentClassification.OuterAutomorphisms.Outer P :=
    (QuotientGroup.mk' (inner P)).comp ((KFacts.inducedAutHom X e).comp
      (Subgroup.inclusion hQN)) with hφ
  have hφker : ∀ g : Q, φ g = 1 ↔ (g : G) ∈ X ⊔ Sec4.thetaQuotCentralizer X := by
    intro g
    rw [Item812Res2.mem_sup_thetaQuotCentralizer_iff (hQN g.2), hφ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change IsInnerAut (MulAut.congr e (thetaQuotMulAut X (compAction X ⟨g, hQN g.2⟩))) ↔ _
    exact isInnerAut_congr e _
  have hRker : sec8R Q X = φ.ker.map Q.subtype := by
    ext x
    constructor
    · rintro ⟨hxQ, hxXC⟩
      exact ⟨⟨x, hxQ⟩, (hφker ⟨x, hxQ⟩).mpr hxXC, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.2, (hφker g).mp hg⟩
  have hRcard' : Nat.card (sec8R Q X) = Nat.card φ.ker := by
    rw [hRker, Subgroup.card_map_of_injective Q.subtype_injective]
  have hK : Nat.card F = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num) hK
  obtain ⟨-, -, -, -, -, hcardOut, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (by norm_num) hFr hord hzp
  have hrange3 : Nat.card φ.range ≤ 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 φ.range :=
      hQp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have h6 : Nat.card φ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [hcardOut] at this
    rw [hk] at h6 ⊢
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · exfalso
      have h9 : 9 ∣ 3 ^ (k + 2) := ⟨3 ^ k, by ring⟩
      have := h9.trans h6
      norm_num at this
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  rw [hRcard', ← h1]
  nlinarith [Nat.card_pos (α := φ.ker)]

end Item812Res12


open Item812Res12 in
theorem fin812Q1Cyclic_of (h45 : Sec4.Item4_5) (h84 : Pair84A) :
    Fin812Q1Cyclic := by
  intro G _ _ A c L a b X Y n h Pa Q hPa hAPa hpaeq hBeq hQ hPaQ
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := sec8B A X with hBdef
  set Q₁ : Subgroup G := Q ⊓ Sec4.thetaQuotCentralizer X with hQ₁
  set Q₂ : Subgroup G := Q ⊓ X with hQ₂
  set R : Subgroup G := sec8R Q X with hRdef
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hbC : b ∈ Sec4.thetaQuotCentralizer X :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXb
  have hbB : b ∈ B := ⟨hbA, Subgroup.mem_sup_right hbC⟩
  have hQp : IsPGroup 3 Q := hQ.2.1
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAc y (Item812Res4.b_le_a hy) x hx
  have hQA := hQ.2.2 _ (Item812Res4.isPGroup_sup hQp
    (Item812Res4.isPGroup_of_isElemAbelian hAab) (hAPa.trans hPaQ)) le_sup_left
    (sup_le hQ.1 hAB)
  have hAQ : A ≤ Q := hQA ▸ le_sup_right
  have haQ : a ∈ Q := hAQ haA
  have hbQ : b ∈ Q := hAQ hbA
  have hQB : ∀ q ∈ Q, ∀ x ∈ B, q * x = x * q := fun q hq x hx =>
    (Subgroup.mem_centralizer_iff.mp (hQ.1 hq) x hx).symm
  have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hQB q hq b hbB)
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hQp hQb X
      hXb
  have haout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h.toSec8Pair with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  have hQR3 : Nat.card Q ≤ 3 * Nat.card R := card_le_three_mul_sec8R h hQp hQN
  obtain ⟨e2⟩ := fin812Q2Iso_of_card (fin812Q2Card_of h45) G A c L a b X Y n h Pa Q hPa hAPa
    hpaeq hBeq hQ hPaQ
  have hQ2card : Nat.card Q₂ = 81 := by
    rw [Nat.card_congr e2.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hQ2ab : ∀ v ∈ Q₂, ∀ v' ∈ Q₂, v * v' = v' * v := by
    intro v hv v' hv'
    have := e2.injective (by rw [map_mul, map_mul, mul_comm] :
      e2 (⟨v, hv⟩ * ⟨v', hv'⟩) = e2 (⟨v', hv'⟩ * ⟨v, hv⟩))
    exact congrArg Subtype.val this
  have hQ2exp : ∀ v ∈ Q₂, v ^ 9 = 1 := by
    intro v hv
    have := e2.injective (by rw [map_pow, Item812Res10.pow_nine_zmod9sq, map_one] :
      e2 (⟨v, hv⟩ ^ 9) = e2 1)
    simpa using congrArg Subtype.val this
  have hZ := Item812Res10.center_eq_bot h
  have hinf12 : Q₁ ⊓ Q₂ = ⊥ := Item812Res10.inf_eq_bot hQp hZ
  have hcomm12 : ∀ u ∈ Q₁, ∀ v ∈ Q₂, u * v = v * u := fun u hu v hv =>
    Item812Res10.commute_of_mem hQp hu hv
  have hRle : Nat.card R ≤ Nat.card Q₁ * 81 := by
    have h1 := Item812Res10.card_le_of_le_sup (hQp.to_le (inf_le_left : R ≤ Q))
      (inf_le_right : R ≤ X ⊔ Sec4.thetaQuotCentralizer X) (Item812Res10.not_dvd_card h)
    have h2 : Nat.card (R ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≤ Nat.card Q₁ :=
      Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
    calc Nat.card R ≤ _ := h1
      _ ≤ Nat.card Q₁ * 81 := Nat.mul_le_mul_right _ h2
  have hsup12 : Q₁ ⊔ Q₂ ≤ R :=
    sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_right))
      (le_inf inf_le_left (inf_le_right.trans le_sup_left))
  obtain ⟨hcard12, hset12⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q₁ Q₂ hcomm12
  rw [hinf12, Subgroup.card_bot, mul_one, hQ2card] at hcard12
  have hReq : R = Q₁ ⊔ Q₂ :=
    (Subgroup.eq_of_le_of_card_ge hsup12 (by rw [hcard12]; exact hRle)).symm
  have hRcard : Nat.card R = Nat.card Q₁ * 81 := by rw [hReq, hcard12]
  have hQ1N : ∀ q ∈ Q, ∀ x ∈ Q₁, q * x * q⁻¹ ∈ Q₁ := fun q hq x hx =>
    ⟨Q.mul_mem (Q.mul_mem hq hx.1) (Q.inv_mem hq),
      Sec6.conj_mem_thetaQuotCentralizer hx.2 (hQN hq)⟩
  have hQ2N : ∀ q ∈ Q, ∀ x ∈ Q₂, q * x * q⁻¹ ∈ Q₂ := fun q hq x hx =>
    ⟨Q.mul_mem (Q.mul_mem hq hx.1) (Q.inv_mem hq),
      (Subgroup.mem_normalizer_iff.mp (hQN hq) x).mp hx.2⟩
  have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  have hY : Item812Res4.IsYQuot Y := h.item89_Y
  have hBY : B ≤ Y := by rw [hBeq]; exact inf_le_right
  have hBab : CFSG.Assembly.IsElemAbelian 3 B :=
    Item812Res4.isElemAbelian_of_le hAab Item812Res4.b_le_a
  have hBp : IsPGroup 3 B := Item812Res4.isPGroup_of_isElemAbelian hBab
  have hB27 : Nat.card B = 27 := Item812Res8.card_sec8B h
  have hAeq : Subgroup.zpowers a ⊔ B = A := by rw [hBeq]; exact Item812Res6.zpowers_sup_inf_eq h
  have hPaYlt : B < Pa ⊓ Y := by
    have hle : B ≤ Pa ⊓ Y := le_inf (Item812Res4.b_le_a.trans hAPa) hBY
    refine lt_of_le_of_ne hle fun heq => ?_
    obtain ⟨SY, hSY⟩ := (hBp.comap_subtype (K := Y)).exists_le_sylow
    have hSY81 : Nat.card (SY : Subgroup Y) = 81 := by
      rw [Sylow.card_eq_multiplicity, factorization_card_Y hY]
      norm_num
    set SY' : Subgroup G := (SY : Subgroup Y).map Y.subtype with hSY'
    have hSY'p : IsPGroup 3 SY' := SY.isPGroup'.map Y.subtype
    have hBSY : B ≤ SY' := fun x hx => ⟨⟨x, hBY hx⟩, hSY (mem_subgroupOf.mpr hx), rfl⟩
    have hBlt : B < SY' := lt_of_le_of_ne hBSY fun hBS => by
      have h1 : Nat.card SY' = 81 := by
        rw [hSY', Subgroup.card_map_of_injective Y.subtype_injective, hSY81]
      rw [← hBS, hB27] at h1
      norm_num at h1
    obtain ⟨y, hySY, hyB, hyN⟩ :=
      Sec10.exists_mem_normalizer_not_mem_of_lt_of_isPGroup hSY'p hBlt
    have hyY : y ∈ Y := Subgroup.map_subtype_le _ hySY
    have hya : y ∈ Subgroup.centralizer ({a} : Set G) := hYa hyY
    have hPaA : Pa = A := by
      rw [← hpaeq, ← heq]
      exact hAeq
    have hyNA : y ∈ Subgroup.normalizer (A : Set G) := by
      rw [← hAeq]
      refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, hyN⟩
      exact Item812Res3.mem_normalizer_of_forall_commute fun z hz => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (Commute.zpow_right (show Commute y a from
          Subgroup.mem_centralizer_singleton_iff.mp hya) k).eq
    have hy3 : IsPGroup 3 (Subgroup.zpowers y) := hSY'p.to_le (Subgroup.zpowers_le.mpr hySY)
    have hT : IsPGroup 3 (A ⊔ Subgroup.zpowers y : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' (Item812Res4.isPGroup_of_isElemAbelian hAab) hy3
        (Subgroup.zpowers_le.mpr hyNA)
    have hTC : A ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({a} : Set G) :=
      sup_le (hAPa.trans hPa.1) (Subgroup.zpowers_le.mpr hya)
    have hTeq := hPa.2.2 _ hT (by rw [hPaA]; exact le_sup_left) hTC
    apply hyB
    have hyA : y ∈ A := by
      rw [← hPaA, ← hTeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rw [hBeq]
    exact ⟨hyA, hyY⟩
  obtain ⟨t, htPaY, htB⟩ := IsConcreteLE.exists_of_lt hPaYlt
  have htQ : t ∈ Subgroup.normalizer (Q : Set G) := hPaQ htPaY.1
  have hta : t * a = a * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (hPa.1 htPaY.1)
  obtain ⟨S₀, hS₀A, hS₀9, -, -, -, hBS⟩ := Item812Res2.sec8B_structure_of_projSp
    h.toTheoremFourHyp.localRank_three.le h.mem_partTwoF h.card_eq hbA hb1 hXb h.item89_X haA
    haout
  set S : Subgroup G := S₀.map X.subtype with hSdef
  have hS9 : Nat.card S = 9 := by
    rw [hSdef, Subgroup.card_map_of_injective X.subtype_injective, hS₀9]
  have hSX : S ≤ X := Subgroup.map_subtype_le _
  have hSA : S ≤ A := hS₀A
  have hBS' : B = Subgroup.zpowers b ⊔ S := hBS
  have hSB : S ≤ B := by rw [hBS']; exact le_sup_right
  have hSQ2 : S ≤ Q₂ := le_inf (hSA.trans hAQ) hSX
  have hSJ : S ≤ sec8J X a :=
    Item812Res11.map_le_perfectResidual hAab haA haout h.item89_X hS₀A
  have hJY : sec8J X a ≤ Y := le_sup_right.trans h.le_Y
  have hJp : Group.IsPerfect (sec8J X a) := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hJb : sec8J X a ≤ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.map_subtype_le _).trans
      (inf_le_left.trans (le_centralizer_of_mem_thetaComponentsAt_three hXb))
  have hbS : b ∉ S := by
    intro hbS
    have hle : B ≤ S := by
      rw [hBS']
      exact sup_le (Subgroup.zpowers_le.mpr hbS) le_rfl
    have := Subgroup.card_le_of_le hle
    rw [hB27, hS9] at this
    norm_num at this
  obtain ⟨hsh1, hsh2, s₀, hs₀S, hs₀t⟩ := shift_Y hY (inf_le_right : Pa ⊓ Y ≤ Y) hBab hB27
    hPaYlt.le (hPa.2.1.to_le inf_le_left) htPaY htB hSB hS9 hbB hbS hJp hJY hSJ hJb
  have hfix : ∀ x ∈ Q₁, x * a = a * x → x ^ 3 = 1 → x ∈ Subgroup.zpowers b := by
    intro x hx hxa hx3
    have hAx : A ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hxa.symm)) ?_
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hQB x hx.1 z hz).symm
    have hab := Sec21.Item211Proof.isElemAbelian_sup_zpowers hAab hx3 fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mp (hAx hz)
    have hxA : x ∈ A := by
      have heq := h.mem_partTwoF.2.1 _ hab le_sup_left
      exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hxB : x ∈ B := ⟨hxA, Subgroup.mem_sup_right hx.2⟩
    rw [hBS'] at hxB
    have hcbS : ∀ u ∈ Subgroup.zpowers b, ∀ v ∈ S, u * v = v * u := fun u hu v hv =>
      hAc u (Subgroup.zpowers_le.mpr hbA hu) v (hSA hv)
    have hxset : x ∈ ((Subgroup.zpowers b ⊔ S : Subgroup G) : Set G) := hxB
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcbS).2] at hxset
    obtain ⟨u, hu, v, hv, huv'⟩ := hxset
    have huv : u * v = x := huv'
    have hvC : v ∈ Sec4.thetaQuotCentralizer X := by
      have e1 : v = u⁻¹ * x := by rw [← huv]; group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpowers_le.mpr hbC hu)) hx.2
    have hv1 : v = 1 := Item812Res10.eq_one_of_mem_theta hQp (hAQ (hSA hv))
      (Item812Res10.mem_theta_of_mem_thetaQuotCentralizer hZ (hSX hv) hvC)
    rw [← huv, hv1, mul_one]
    exact hu
  have hconj : ∀ g ∈ Subgroup.normalizer (Q : Set G), g * a = a * g →
      (Q₁.map (MulAut.conj g).toMonoidHom ≤ Q) ∧
      (∀ q ∈ Q, ∀ y ∈ Q₁.map (MulAut.conj g).toMonoidHom,
        q * y * q⁻¹ ∈ Q₁.map (MulAut.conj g).toMonoidHom) ∧
      (∀ y ∈ Q₁.map (MulAut.conj g).toMonoidHom, y * a = a * y → y ^ 3 = 1 →
        y ∈ Subgroup.zpowers (g * b * g⁻¹)) := by
    intro g hg hga
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx.1
    · rintro q hq _ ⟨x, hx, rfl⟩
      have hq' : g⁻¹ * q * g ∈ Q := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
        rwa [inv_inv] at h1
      refine ⟨g⁻¹ * q * g * x * (g⁻¹ * q * g)⁻¹, hQ1N _ hq' x hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro _ ⟨x, hx, rfl⟩ hya hy3
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hya hy3 ⊢
      have hga' : g⁻¹ * a = a * g⁻¹ := by
        calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hga]
          _ = a * g⁻¹ := by group
      have hxa : x * a = a * x := by
        calc x * a = g⁻¹ * (g * x * g⁻¹) * (g * a) := by group
          _ = g⁻¹ * (g * x * g⁻¹) * (a * g) := by rw [hga]
          _ = g⁻¹ * ((g * x * g⁻¹) * a) * g := by group
          _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [hya]
          _ = (g⁻¹ * a) * (g * x * g⁻¹) * g := by group
          _ = (a * g⁻¹) * (g * x * g⁻¹) * g := by rw [hga']
          _ = a * x := by group
      have hx3 : x ^ 3 = 1 := by
        have h1 : g * x ^ 3 * g⁻¹ = 1 := by rw [← conj_pow]; exact hy3
        calc x ^ 3 = g⁻¹ * (g * x ^ 3 * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hfix x hx hxa hx3)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [conj_zpow]⟩
  have ht2Q : t ^ 2 ∈ Subgroup.normalizer (Q : Set G) := Subgroup.pow_mem _ htQ 2
  have ht2a : t ^ 2 * a = a * t ^ 2 := by
    calc t ^ 2 * a = t * (t * a) := by rw [sq, mul_assoc]
      _ = t * (a * t) := by rw [hta]
      _ = (t * a) * t := by rw [mul_assoc]
      _ = (a * t) * t := by rw [hta]
      _ = a * t ^ 2 := by rw [sq, mul_assoc]
  obtain ⟨h1Q, h1N, h1fix⟩ := hconj t htQ hta
  obtain ⟨h2Q, h2N, h2fix⟩ := hconj (t ^ 2) ht2Q ht2a
  set Q₁t : Subgroup G := Q₁.map (MulAut.conj t).toMonoidHom with hQ₁t
  set Q₁tt : Subgroup G := Q₁.map (MulAut.conj (t ^ 2)).toMonoidHom with hQ₁tt
  have hbc3 : ∀ g : G, (g * b * g⁻¹) ^ 3 = 1 := fun g => by rw [conj_pow, hb3]; group
  have hbc1 : ∀ g : G, g * b * g⁻¹ ≠ 1 := fun g h1 => hb1 (by
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hi1 : Q₁ ⊓ Q₁t = ⊥ := by
    by_contra hne
    obtain ⟨z, hzN, hz1, hz3, hzc⟩ := exists_central_of_normal hQp
      (inf_le_left.trans inf_le_left) (fun q hq x hx => ⟨hQ1N q hq x hx.1, h1N q hq x hx.2⟩) hne
    have hza : z * a = a * z := (hzc a haQ).symm
    have hzb := hfix z hzN.1 hza hz3
    have hzt := h1fix z hzN.2 hza hz3
    exact hsh1 (Subgroup.zpowers_le.mpr hzb
      (mem_zpowers_of_mem_zpowers_of_ne_one (hbc3 t) (hbc1 t) hzt hz1))
  have hi2 : Q₁ ⊓ Q₁tt = ⊥ := by
    by_contra hne
    obtain ⟨z, hzN, hz1, hz3, hzc⟩ := exists_central_of_normal hQp
      (inf_le_left.trans inf_le_left) (fun q hq x hx => ⟨hQ1N q hq x hx.1, h2N q hq x hx.2⟩) hne
    have hza : z * a = a * z := (hzc a haQ).symm
    have hzb := hfix z hzN.1 hza hz3
    have hzt := h2fix z hzN.2 hza hz3
    exact hsh2 (Subgroup.mem_sup_left (Subgroup.zpowers_le.mpr hzb
      (mem_zpowers_of_mem_zpowers_of_ne_one (hbc3 (t ^ 2)) (hbc1 (t ^ 2)) hzt hz1)))
  have hcomm1t : ∀ x ∈ Q₁, ∀ y ∈ Q₁t, x * y = y * x :=
    commute_of_inf_eq_bot (fun k hk x hx => hQ1N k (h1Q hk) x hx)
      (fun k hk y hy => h1N k hk.1 y hy) hi1
  obtain ⟨hc1t, hset1t⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q₁ Q₁t hcomm1t
  have hsupN : ∀ q ∈ Q, ∀ x ∈ Q₁ ⊔ Q₁t, q * x * q⁻¹ ∈ Q₁ ⊔ Q₁t := fun q hq x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inf_normalizer_le_normalizer_sup Q₁ Q₁t
      ⟨mem_normalizer_of_conj hQ1N hq, mem_normalizer_of_conj h1N hq⟩) x).mp hx
  have hsupQ : Q₁ ⊔ Q₁t ≤ Q := sup_le inf_le_left h1Q
  have hi4 : (Q₁ ⊔ Q₁t) ⊓ Q₁tt = ⊥ := by
    by_contra hne
    obtain ⟨z, hzN, hz1, hz3, hzc⟩ := exists_central_of_normal hQp (inf_le_right.trans h2Q)
      (fun q hq x hx => ⟨hsupN q hq x hx.1, h2N q hq x hx.2⟩) hne
    have hza : z * a = a * z := (hzc a haQ).symm
    have hztt := h2fix z hzN.2 hza hz3
    have hzset : z ∈ ((Q₁ ⊔ Q₁t : Subgroup G) : Set G) := hzN.1
    rw [hset1t] at hzset
    obtain ⟨y₁, hy₁, y₂, hy₂, hyz'⟩ := hzset
    have hyz : y₁ * y₂ = z := hyz'
    have hay₁ := hQ1N a haQ y₁ hy₁
    have hay₂ := h1N a haQ y₂ hy₂
    have hdec : (a * y₁ * a⁻¹) * (a * y₂ * a⁻¹) = y₁ * y₂ := by
      calc (a * y₁ * a⁻¹) * (a * y₂ * a⁻¹) = a * (y₁ * y₂) * a⁻¹ := by group
        _ = a * z * a⁻¹ := by rw [hyz]
        _ = y₁ * y₂ := by rw [← hza, mul_inv_cancel_right, hyz]
    have hu : y₁⁻¹ * (a * y₁ * a⁻¹) ∈ Q₁ ⊓ Q₁t := by
      refine ⟨Q₁.mul_mem (Q₁.inv_mem hy₁) hay₁, ?_⟩
      have e1 : y₁⁻¹ * (a * y₁ * a⁻¹) = y₂ * (a * y₂ * a⁻¹)⁻¹ := by
        calc y₁⁻¹ * (a * y₁ * a⁻¹) =
            y₁⁻¹ * ((a * y₁ * a⁻¹) * (a * y₂ * a⁻¹)) * (a * y₂ * a⁻¹)⁻¹ := by group
          _ = y₁⁻¹ * (y₁ * y₂) * (a * y₂ * a⁻¹)⁻¹ := by rw [hdec]
          _ = y₂ * (a * y₂ * a⁻¹)⁻¹ := by group
      rw [e1]
      exact Q₁t.mul_mem hy₂ (Q₁t.inv_mem hay₂)
    rw [hi1, Subgroup.mem_bot, inv_mul_eq_one] at hu
    have hy₁a : y₁ * a = a * y₁ := by
      calc y₁ * a = a * y₁ * a⁻¹ * a := by rw [← hu]
        _ = a * y₁ := by group
    have hy₂a : y₂ * a = a * y₂ := by
      rw [← hu] at hdec
      have h1 : a * y₂ * a⁻¹ = y₂ := mul_left_cancel hdec
      calc y₂ * a = a * y₂ * a⁻¹ * a := by rw [h1]
        _ = a * y₂ := by group
    have hc12 : y₁ * y₂ = y₂ * y₁ := hcomm1t y₁ hy₁ y₂ hy₂
    have hcube : y₁ ^ 3 * y₂ ^ 3 = 1 := by
      rw [← (Commute.mul_pow hc12 3), hyz]
      exact hz3
    have hy₁3 : y₁ ^ 3 = 1 := by
      have h1 : y₁ ^ 3 ∈ Q₁ ⊓ Q₁t := by
        refine ⟨Q₁.pow_mem hy₁ 3, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hcube]
        exact Q₁t.inv_mem (Q₁t.pow_mem hy₂ 3)
      rw [hi1, Subgroup.mem_bot] at h1
      exact h1
    have hy₂3 : y₂ ^ 3 = 1 := by
      rw [hy₁3, one_mul] at hcube
      exact hcube
    have hy₁b := hfix y₁ hy₁ hy₁a hy₁3
    have hy₂b := h1fix y₂ hy₂ hy₂a hy₂3
    apply hsh2
    have hmem := mem_zpowers_of_mem_zpowers_of_ne_one (hbc3 (t ^ 2)) (hbc1 (t ^ 2)) hztt hz1
    rw [← hyz] at hmem
    exact Subgroup.zpowers_le.mpr (Subgroup.mul_mem_sup hy₁b hy₂b) hmem
  have hcomm4 : ∀ x ∈ Q₁ ⊔ Q₁t, ∀ y ∈ Q₁tt, x * y = y * x :=
    commute_of_inf_eq_bot (fun k hk x hx => hsupN k (h2Q hk) x hx)
      (fun k hk y hy => h2N k (hsupQ hk) y hy) hi4
  obtain ⟨hcN, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Q₁ ⊔ Q₁t) Q₁tt hcomm4
  have hQ1tc : Nat.card Q₁t = Nat.card Q₁ :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hQ1ttc : Nat.card Q₁tt = Nat.card Q₁ :=
    Subgroup.card_map_of_injective (MulAut.conj (t ^ 2)).injective
  rw [hi1, Subgroup.card_bot, mul_one, hQ1tc] at hc1t
  rw [hi4, Subgroup.card_bot, mul_one, hc1t, hQ1ttc] at hcN
  have hNQ : (Q₁ ⊔ Q₁t) ⊔ Q₁tt ≤ Q := sup_le hsupQ h2Q
  have hNle := Subgroup.card_le_of_le hNQ
  have hQ1pos : 0 < Nat.card Q₁ := Nat.card_pos
  have hineq : Nat.card Q₁ * Nat.card Q₁ ≤ 243 := by
    have h1 : Nat.card Q₁ * Nat.card Q₁ * Nat.card Q₁ ≤ 243 * Nat.card Q₁ := by
      rw [← hcN]
      calc _ ≤ Nat.card Q := hNle
        _ ≤ 3 * Nat.card R := hQR3
        _ = 243 * Nat.card Q₁ := by rw [hRcard]; ring
    exact Nat.le_of_mul_le_mul_right h1 hQ1pos
  have hbQ1 : b ∈ Q₁ := ⟨hbQ, hbC⟩
  have hQ1card : Nat.card Q₁ = 3 ∨ Nat.card Q₁ = 9 := by
    obtain ⟨m, hm⟩ := (hQp.to_le (inf_le_left : Q₁ ≤ Q)).exists_card_eq
    rw [hm] at hineq ⊢
    rcases m with _ | _ | _ | m
    · exfalso
      have h1 : Q₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero])
      rw [h1, Subgroup.mem_bot] at hbQ1
      exact hb1 hbQ1
    · left; norm_num
    · right; norm_num
    · exfalso
      have h27 : 27 ≤ 3 ^ (m + 3) := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
  have hQ1ab : ∀ x ∈ Q₁, ∀ y ∈ Q₁, x * y = y * x := by
    rcases hQ1card with h3 | h9
    · have hQ1b : Q₁ = Subgroup.zpowers b :=
        (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbQ1)
          (by rw [h3, Nat.card_zpowers, orderOf_eq_prime hb3 hb1])).symm
      intro x hx y hy
      rw [hQ1b] at hx hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm]
    · intro x hx y hy
      have h9' : Nat.card Q₁ = 3 ^ 2 := by rw [h9]; norm_num
      exact congrArg Subtype.val
        ((IsPGroup.isMulCommutative_of_card_eq_prime_sq h9').is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    rw [← SetLike.mem_coe, hReq, hset12] at hx hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hy
    calc u * v * (u' * v') = (u * u') * (v * v') := by
          rw [mul_assoc, ← mul_assoc v, (hcomm12 u' hu' v hv).symm, mul_assoc, mul_assoc]
      _ = (u' * u) * (v' * v) := by rw [hQ1ab u hu u' hu', hQ2ab v hv v' hv']
      _ = u' * v' * (u * v) := by
          rw [mul_assoc, ← mul_assoc u, hcomm12 u hu v' hv', mul_assoc, mul_assoc]
  have hC2 : Nat.card (Q₂ ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≤ 9 := by
    set C₂ : Subgroup G := Q₂ ⊓ Subgroup.centralizer ({a} : Set G) with hC₂
    have hC2X : C₂ ≤ X := inf_le_left.trans inf_le_right
    set φ : C₂ →* X ⧸ aschbacherSolvableCore 3 X :=
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (Subgroup.inclusion hC2X) with hφ
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
      exact Subtype.ext (Item812Res10.eq_one_of_mem_theta hQp y.2.1.1 ⟨_, hy, rfl⟩)
    have hrange : φ.range ≤ Sec8.barCentralizer (Subgroup.zpowers a) X := by
      rintro _ ⟨y, rfl⟩
      rw [KFacts.mem_barCentralizer_zpowers_iff haout.1, hφ, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      change a * (y : G) * a⁻¹ = y
      rw [← Subgroup.mem_centralizer_singleton_iff.mp y.2.2, mul_inv_cancel_right]
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := 1) one_ne_zero ha3 haout
      h.item89_X
    have h720 : Nat.card (Sec8.barCentralizer (Subgroup.zpowers a) X) = 720 := by
      rw [Nat.card_congr ι.toEquiv, Item812Res2.card_projSp_two_one]
    have hdvd : Nat.card φ.range ∣ 720 := h720 ▸ Subgroup.card_dvd_of_le hrange
    have hp : IsPGroup 3 φ.range :=
      (hQp.to_le (inf_le_left.trans inf_le_left : C₂ ≤ Q)).of_surjective φ.rangeRestrict
        φ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have h27 : 3 ^ 3 ∣ 720 := (Nat.pow_dvd_pow 3 hk3).trans (hk ▸ hdvd)
      norm_num at h27
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have hCR : Nat.card (R ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≤
      9 * Nat.card Q₁ := by
    set C₂ : Subgroup G := Q₂ ⊓ Subgroup.centralizer ({a} : Set G) with hC₂
    have hle : R ⊓ Subgroup.centralizer ({a} : Set G) ≤ Q₁ ⊔ C₂ := by
      intro x hx
      obtain ⟨hxR, hxa⟩ := Subgroup.mem_inf.mp hx
      rw [← SetLike.mem_coe, hReq, hset12] at hxR
      obtain ⟨u, hu, v, hv, huv'⟩ := hxR
      have huv : u * v = x := huv'
      rw [← huv] at hxa ⊢
      have hxa' : a * (u * v) = u * v * a := (Subgroup.mem_centralizer_singleton_iff.mp hxa).symm
      have hau := hQ1N a haQ u hu
      have hav := hQ2N a haQ v hv
      have hdec : (a * u * a⁻¹) * (a * v * a⁻¹) = u * v := by
        calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
          _ = u * v := by rw [hxa', mul_inv_cancel_right]
      have hw : u⁻¹ * (a * u * a⁻¹) ∈ Q₁ ⊓ Q₂ := by
        refine ⟨Q₁.mul_mem (Q₁.inv_mem hu) hau, ?_⟩
        have e1 : u⁻¹ * (a * u * a⁻¹) = v * (a * v * a⁻¹)⁻¹ := by
          calc u⁻¹ * (a * u * a⁻¹) =
              u⁻¹ * ((a * u * a⁻¹) * (a * v * a⁻¹)) * (a * v * a⁻¹)⁻¹ := by group
            _ = u⁻¹ * (u * v) * (a * v * a⁻¹)⁻¹ := by rw [hdec]
            _ = v * (a * v * a⁻¹)⁻¹ := by group
        rw [e1]
        exact Q₂.mul_mem hv (Q₂.inv_mem hav)
      rw [hinf12, Subgroup.mem_bot, inv_mul_eq_one] at hw
      rw [← hw] at hdec
      have h1 : a * v * a⁻¹ = v := mul_left_cancel hdec
      have hvC : v ∈ C₂ := by
        refine ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc v * a = a * v * a⁻¹ * a := by rw [h1]
          _ = a * v := by group
      exact Subgroup.mul_mem_sup hu hvC
    have hcommC : ∀ u ∈ Q₁, ∀ v ∈ C₂, u * v = v * u := fun u hu v hv => hcomm12 u hu v hv.1
    obtain ⟨hcC, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q₁ C₂ hcommC
    have h1 := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card (Q₁ ⊓ C₂ : Subgroup G) := Nat.card_pos
    have h2 : Nat.card (Q₁ ⊔ C₂ : Subgroup G) ≤ Nat.card Q₁ * Nat.card C₂ := by
      rw [← hcC]
      exact Nat.le_mul_of_pos_right _ hpos
    calc Nat.card (R ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≤ _ := h1
      _ ≤ Nat.card Q₁ * Nat.card C₂ := h2
      _ ≤ Nat.card Q₁ * 9 := Nat.mul_le_mul_left _ hC2
      _ = 9 * Nat.card Q₁ := by ring
  set Rt : Subgroup G := R.map (MulAut.conj t).toMonoidHom with hRt
  have hRtQ : Rt ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp htQ x).mp hx.1
  have hRtcard : Nat.card Rt = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hRtab : ∀ x ∈ Rt, ∀ y ∈ Rt, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc t * x * t⁻¹ * (t * y * t⁻¹) = t * (x * y) * t⁻¹ := by group
      _ = t * (y * x) * t⁻¹ := by rw [hRab x hx y hy]
      _ = t * y * t⁻¹ * (t * x * t⁻¹) := by group
  have hRN : Q ≤ Subgroup.normalizer (R : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer fun q hq =>
      Subgroup.inf_normalizer_le_normalizer_sup X (Sec4.thetaQuotCentralizer X)
        ⟨hQN hq, Sec6.normalizer_le_normalizer_thetaQuotCentralizer X (hQN hq)⟩
  have hRR : Rt = R := by
    by_contra hne
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := R) (B := Rt) (hRtQ.trans hRN)
    rw [hRtcard] at h1
    have hRsupQ : R ⊔ Rt ≤ Q := sup_le inf_le_left hRtQ
    have hlt : R < R ⊔ Rt := lt_of_le_of_ne le_sup_left fun heq => hne
      (Subgroup.eq_of_le_of_card_ge (heq ▸ le_sup_right) (by rw [hRtcard]))
    have hRQ : R ≤ Q := inf_le_left
    have hpow : 3 * Nat.card R ≤ Nat.card (R ⊔ Rt : Subgroup G) := by
      obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hQp.to_le hRQ)
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hQp.to_le hRsupQ)
      have hdvd : Nat.card R ∣ Nat.card (R ⊔ Rt : Subgroup G) :=
        Subgroup.card_dvd_of_le le_sup_left
      have hne' : Nat.card R ≠ Nat.card (R ⊔ Rt : Subgroup G) := fun hc =>
        (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge le_sup_left hc.symm.le)
      rw [hi, hj] at hdvd hne' ⊢
      have hij : i < j := by
        have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
        rcases this.lt_or_eq with h' | h'
        · exact h'
        · exact absurd (by rw [h']) hne'
      calc 3 * 3 ^ i = 3 ^ (i + 1) := by ring
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hij
    have hsupeq : R ⊔ Rt = Q := Subgroup.eq_of_le_of_card_ge hRsupQ (le_trans hQR3 hpow)
    have hinfC : R ⊓ Rt ≤ R ⊓ Subgroup.centralizer ({a} : Set G) := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hC : R ⊔ Rt ≤ Subgroup.centralizer ({x} : Set G) :=
        sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hRab x hx.1 y hy).symm)
          (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hRtab x hx.2 y hy).symm)
      have hax : a ∈ Subgroup.centralizer ({x} : Set G) := hC (by rw [hsupeq]; exact haQ)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hax).symm
    have h2 := (Subgroup.card_le_of_le hinfC).trans hCR
    have h3 : Nat.card (R ⊔ Rt : Subgroup G) ≤ 3 * Nat.card R := hsupeq ▸ hQR3
    rw [hRcard] at h1 h3
    nlinarith
  have hconjR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := fun r hr => by
    rw [← hRR]
    exact ⟨r, hr, rfl⟩
  rcases hQ1card with h3 | h9
  ·
    exfalso
    have hQ1b : Q₁ = Subgroup.zpowers b :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbQ1)
        (by rw [h3, Nat.card_zpowers, orderOf_eq_prime hb3 hb1])).symm
    have hΩ : ∀ w ∈ Q₂, w ^ 3 = 1 → w ∈ S := by
      have hT9 : Nat.card {z : Q₂ // z ^ 3 = 1} = 9 :=
        (Item812Res10.card_cube_congr e2).trans Item812Res10.card_cube_zmod9sq
      let f : S → {z : Q₂ // z ^ 3 = 1} := fun s =>
        ⟨⟨s, hSQ2 s.2⟩, Subtype.ext (by simpa using hAab.2 _ (hSA s.2))⟩
      have hf : Function.Injective f := fun s s' hss => Subtype.ext (by
        have := congrArg (fun z : {z : Q₂ // z ^ 3 = 1} => ((z : Q₂) : G)) hss
        simpa [f] using this)
      have hbij := hf.bijective_of_nat_card_le (by rw [hT9, hS9])
      intro w hw hw3
      obtain ⟨s, hs⟩ := hbij.2 ⟨⟨w, hw⟩, Subtype.ext (by simpa using hw3)⟩
      have h1 := congrArg (fun z : {z : Q₂ // z ^ 3 = 1} => ((z : Q₂) : G)) hs
      simp only [f] at h1
      rw [← h1]
      exact s.2
    have hcubeR : ∀ r ∈ R, r ^ 3 ∈ S := by
      intro r hr
      rw [← SetLike.mem_coe, hReq, hset12] at hr
      obtain ⟨u, hu, v, hv, huv'⟩ := hr
      have huv'' : u * v = r := huv'
      rw [← huv'']
      have huv : u * v = v * u := hcomm12 u hu v hv
      have hu3 : u ^ 3 = 1 := by
        rw [hQ1b] at hu
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
      rw [Commute.mul_pow huv 3, hu3, one_mul]
      refine hΩ _ (Q₂.pow_mem hv 3) ?_
      rw [← pow_mul]
      exact hQ2exp v hv
    apply hs₀t
    have hs₀Q2 : s₀ ∈ Q₂ := hSQ2 hs₀S
    have hs₀3 : (⟨s₀, hs₀Q2⟩ : Q₂) ^ 3 = 1 := Subtype.ext (by simpa using hAab.2 _ (hSA hs₀S))
    obtain ⟨w, hw⟩ := exists_cube_root_zmod9sq (e2 ⟨s₀, hs₀Q2⟩) (by rw [← map_pow, hs₀3, map_one])
    have hy3 : (e2.symm w) ^ 3 = ⟨s₀, hs₀Q2⟩ :=
      e2.injective (by rw [map_pow, e2.apply_symm_apply, hw])
    have hy3' : ((e2.symm w : Q₂) : G) ^ 3 = s₀ := by
      simpa using congrArg Subtype.val hy3
    rw [← hy3', ← conj_pow]
    exact hcubeR _ (hconjR _ (hsup12 (Subgroup.mem_sup_right (e2.symm w).2)))
  ·
    have hQ1R : Q₁ ≤ R := le_sup_left.trans hsup12
    have hQ1tR : Q₁t ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact hconjR x (hQ1R hx)
    have hQ1ttR : Q₁tt ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show t ^ 2 * x * (t ^ 2)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ by
        rw [sq, mul_inv_rev]
        simp only [mul_assoc]]
      exact hconjR _ (hconjR x (hQ1R hx))
    have hNeq : (Q₁ ⊔ Q₁t) ⊔ Q₁tt = R :=
      Subgroup.eq_of_le_of_card_ge (sup_le (sup_le hQ1R hQ1tR) hQ1ttR)
        (by rw [hcN, hRcard, h9])
    by_cases hexp : ∀ x ∈ Q₁, x ^ 3 = 1
    · exfalso
      set Ω : Subgroup G :=
        { carrier := {y | y ∈ R ∧ y ^ 3 = 1}
          mul_mem' := by
            rintro y z ⟨hy, hy3⟩ ⟨hz, hz3⟩
            refine ⟨R.mul_mem hy hz, ?_⟩
            rw [(Commute.mul_pow (hRab y hy z hz) 3), hy3, hz3, one_mul]
          one_mem' := ⟨R.one_mem, one_pow 3⟩
          inv_mem' := by
            rintro y ⟨hy, hy3⟩
            exact ⟨R.inv_mem hy, by rw [inv_pow, hy3, inv_one]⟩ } with hΩ
      have hconjΩ : ∀ g : G, (∀ x ∈ Q₁, g * x * g⁻¹ ∈ R) →
          Q₁.map (MulAut.conj g).toMonoidHom ≤ Ω := by
        rintro g hg _ ⟨x, hx, rfl⟩
        refine ⟨hg x hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [conj_pow, hexp x hx, mul_one, mul_inv_cancel]
      have hQ1Ω : Q₁ ≤ Ω := fun x hx => ⟨hQ1R hx, hexp x hx⟩
      have hQ1tΩ : Q₁t ≤ Ω := hconjΩ t fun x hx => hQ1tR ⟨x, hx, rfl⟩
      have hQ1ttΩ : Q₁tt ≤ Ω := hconjΩ (t ^ 2) fun x hx => hQ1ttR ⟨x, hx, rfl⟩
      have hRΩ : R ≤ Ω := by
        rw [← hNeq]
        exact sup_le (sup_le hQ1Ω hQ1tΩ) hQ1ttΩ
      obtain ⟨z, hz⟩ := exists_not_cube_one_zmod9sq
      apply hz
      have h1 : ((e2.symm z : Q₂) : G) ^ 3 = 1 :=
        (hRΩ (hsup12 (Subgroup.mem_sup_right (e2.symm z).2))).2
      have h2 : (e2.symm z) ^ 3 = 1 := Subtype.ext (by simpa using h1)
      rw [← e2.apply_symm_apply z, ← map_pow, h2, map_one]
    · push Not at hexp
      obtain ⟨x, hxQ1, hx3⟩ := hexp
      set x' : Q₁ := ⟨x, hxQ1⟩ with hx'
      have hx'3 : x' ^ 3 ≠ 1 := fun h1 => hx3 (by simpa using congrArg Subtype.val h1)
      have hdvd : orderOf x' ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = Nat.card Q₁ by rw [h9]; norm_num]
        exact orderOf_dvd_natCard x'
      obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      have hord : orderOf x' = Nat.card Q₁ := by
        rw [h9]
        interval_cases i
        · exfalso
          rw [pow_zero, orderOf_eq_one_iff] at hio
          exact hx'3 (by rw [hio, one_pow])
        · exfalso
          rw [pow_one] at hio
          exact hx'3 (by rw [← hio]; exact pow_orderOf_eq_one x')
        · rw [hio]
          norm_num
      have hcyc : IsCyclic Q₁ := isCyclic_of_orderOf_eq_card x' hord
      exact ⟨(h9 ▸ zmodCyclicMulEquiv hcyc).symm⟩

end CFSG.RankThree.PartTwo.Sec8
