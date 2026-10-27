module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofDefs
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.KFacts.K72Moving
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3
import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesOdd

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_lift_of_fixed {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hB3 : IsPGroup 3 B) {tb : L ⧸ aschbacherSolvableCore 3 L} (htb3 : tb ^ 3 = 1)
    (htb : ∀ τ ∈ autThetaQuot B L, τ tb = tb) :
    ∃ t : L, (t : G) ∈ Subgroup.centralizer (B : Set G) ∧ t ^ 3 = 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) t = tb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  set Ebar : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := Subgroup.zpowers tb with hEbar
  have hE3 : IsPGroup 3 Ebar := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact htb3) : orderOf tb ∣ 3 ^ 1)
    exact IsPGroup.of_card (n := i) (by rw [hEbar, Nat.card_zpowers, hi])
  set P : Subgroup L := Ebar.comap q with hP
  set P' : Subgroup G := P.map L.subtype with hP'
  have hfix : ∀ b : G, ∀ hb : b ∈ Subgroup.normalizer (L : Set G), b ∈ B →
      ∀ y ∈ Ebar, thetaQuotMulAut L (compAction L ⟨b, hb⟩) y = y := by
    intro b hb hbB y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : thetaQuotMulAut L (compAction L ⟨b, hb⟩) tb = tb :=
      htb _ (mem_autThetaQuot_iff.mpr ⟨b, hb, hbB, rfl⟩)
    rw [map_zpow, h1]
  have hconjP : ∀ b : G, ∀ hb : b ∈ Subgroup.normalizer (L : Set G), b ∈ B →
      ∀ g ∈ P', b * g * b⁻¹ ∈ P' := by
    rintro b hb hbB _ ⟨l, hl, rfl⟩
    refine ⟨compAction L ⟨b, hb⟩ l, ?_, rfl⟩
    change q (compAction L ⟨b, hb⟩ l) ∈ Ebar
    have h1 : q (compAction L ⟨b, hb⟩ l) = thetaQuotMulAut L (compAction L ⟨b, hb⟩) (q l) :=
      (thetaQuotMulAut_mk _ l).symm
    rw [h1, hfix b hb hbB _ hl]
    exact hl
  have hBP' : B ≤ Subgroup.normalizer (P' : Set G) := by
    intro b hbB
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hconjP b (hBN hbB) hbB g
    · intro hg
      have h1 := hconjP b⁻¹ (inv_mem (hBN hbB)) (inv_mem hbB) _ hg
      have e : b⁻¹ * (b * g * b⁻¹) * b⁻¹⁻¹ = g := by group
      rwa [e] at h1
  obtain ⟨Q, hQ⟩ := KFacts.exists_sylow_le_normalizer hB3 hBP'
  set E : Subgroup G := (Q : Subgroup P').map P'.subtype with hE
  have hEP' : E ≤ P' := Subgroup.map_subtype_le _
  have hP'L : P' ≤ L := Subgroup.map_subtype_le _
  have hEL : E ≤ L := hEP'.trans hP'L
  have hE3' : IsPGroup 3 E := Q.isPGroup'.map P'.subtype
  have hmemP : ∀ x : L, (x : G) ∈ E → x ∈ P := by
    intro x hx
    obtain ⟨l, hl, hlx⟩ := hEP' hx
    rwa [show l = x from Subtype.ext hlx] at hl
  have hinj : ∀ x : L, (x : G) ∈ E → q x = 1 → x = 1 := by
    intro x hx hqx
    have hxθ : x ∈ aschbacherSolvableCore 3 L := by
      rw [hq, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hqx
      exact hqx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE3') ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by
      have h1 : (⟨(x : G), hx⟩ : E) ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
      exact Subtype.ext (by simpa using congrArg Subtype.val h1)
    exact KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow hxθ hxk
  have hle : Sec8.imageModTheta L E ≤ Ebar := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmemP x hx
  have hθP : aschbacherSolvableCore 3 L ≤ P := by
    intro x hx
    change q x ∈ Ebar
    have h1 : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact one_mem _
  have hcardP : Nat.card P = Nat.card (aschbacherSolvableCore 3 L) * Nat.card Ebar := by
    have h1 := Subgroup.card_ker_mul_card_range (q.comp P.subtype)
    have hker : (q.comp P.subtype).ker = (aschbacherSolvableCore 3 L).subgroupOf P := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hrange : (q.comp P.subtype).range = Ebar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L)) Ebar
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθP).toEquiv] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    not_three_dvd_card_aschbacherSolvableCore L
  have hθ0 : Nat.card (aschbacherSolvableCore 3 L) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card P').factorization 3 = k := by
    rw [hP', Subgroup.card_map_of_injective L.subtype_injective, hcardP, hk,
      Nat.factorization_mul hθ0 (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ3, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  have hcardQ : Nat.card E = 3 ^ k := by
    rw [hE, Subgroup.card_map_of_injective P'.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  have hcardIm : Nat.card (Sec8.imageModTheta L E) = Nat.card E := by
    set g := q.comp (E.subgroupOf L).subtype with hg
    have hker : g.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (Subtype.ext (hinj (x : L) x.2 hx))
    have h1 := Subgroup.card_ker_mul_card_range g
    rw [hker, Subgroup.card_bot, one_mul] at h1
    have hrange : g.range = Sec8.imageModTheta L E := by
      rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    rw [← hrange, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
  have himage : Sec8.imageModTheta L E = Ebar :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardIm, hcardQ, hk])
  have htbE : tb ∈ Sec8.imageModTheta L E := by
    rw [himage]
    exact Subgroup.mem_zpowers tb
  obtain ⟨t, htE, htq⟩ := htbE
  have htE' : (t : G) ∈ E := Subgroup.mem_subgroupOf.mp htE
  refine ⟨t, ?_, ?_, htq⟩
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro b hbB
    have hb := hBN hbB
    have he' : b * t * b⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hQ hbB) t).mp htE'
    set x : L := t
    set x' : L := compAction L ⟨b, hb⟩ x
    have hx' : (x' : G) = b * t * b⁻¹ := rfl
    have hqx : q x' = q x := by
      have h1 : q x' = thetaQuotMulAut L (compAction L ⟨b, hb⟩) (q x) :=
        (thetaQuotMulAut_mk _ x).symm
      rw [h1, hfix b hb hbB _ (hmemP x htE')]
    have h1 : x'⁻¹ * x = 1 := by
      refine hinj _ ?_ (by rw [map_mul, map_inv, hqx, inv_mul_cancel])
      change (x' : G)⁻¹ * t ∈ E
      rw [hx']
      exact E.mul_mem (E.inv_mem he') htE'
    have h2 : (x' : G) = t := congrArg Subtype.val (inv_mul_eq_one.mp h1)
    rw [hx'] at h2
    calc b * (t : G) = b * t * b⁻¹ * b := by group
      _ = t * b := by rw [h2]
  ·
    refine hinj _ (E.pow_mem htE' 3) ?_
    rw [map_pow, htq, htb3]

end Lift

section PSL2


@[expose] def Item82TwoPSL2Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → Nat.card A = 81 →
      IsEmpty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem false_of_psl2_three (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {e : ℕ} (he : 3 ≤ e)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * e))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := GaloisField 3 (3 * e)
  have hAF := h.mem_partTwoF
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  have hF : Nat.card F = 3 ^ (3 * e) := card_galoisField 3 (3 * e) (by omega)
  set E : (L ⧸ aschbacherSolvableCore 3 L) ≃* GorensteinWalter.PSL2 F :=
    e₁.trans (projSLEquivPSL F) with hEdef
  have hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) :=
    (outThreeCyclic_psl2 F).of_mulEquiv E
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv_fwd E.symm (GorensteinWalter.psl2_center_eq_bot _)
  have hinj := Item82OneProof.conj_injective_of_center_eq_bot hZ
  have hf := inducesKind_field_of_pow_three L ha3 h.inducesOuterTheta E
  obtain ⟨σ, -, hcard, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_of_field ha3 E hf
  rw [hF] at hcard
  obtain ⟨j, hej, hje⟩ := Item82OneProof.exists_eq_pow_of_pow_three_eq Nat.prime_three hcard
  rw [show j = e by omega] at hej
  set C := Sec8.barCentralizer (Subgroup.zpowers a) L with hC
  set Γ := autThetaQuot A L with hΓ
  set τ := thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) with hτ
  have hτΓ : τ ∈ Γ := mem_autThetaQuot_iff.mpr ⟨a, hAN h.a_mem, h.a_mem, rfl⟩
  have hτout : ¬ IsInnerAut τ := h.not_isInnerAut_induced
  have hΓ27 : Nat.card Γ = 27 := card_autThetaQuot_eq_27 h h81 hAN
  set ιc : (L ⧸ aschbacherSolvableCore 3 L) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    MulAut.conj with hιc
  set X : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (Γ ⊓ ιc.range).comap ιc with hX
  have hXcard : Nat.card X = Nat.card (Γ ⊓ ιc.range : Subgroup _) := by
    have hmap : X.map ιc = Γ ⊓ ιc.range := Subgroup.map_comap_eq_self inf_le_right
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hX9 : Nat.card X ≤ 9 := by
    rw [hXcard]
    have hlt : (Γ ⊓ ιc.range : Subgroup _) ≠ Γ := fun heq =>
      hτout (by rw [← heq] at hτΓ; exact hτΓ.2)
    have hdvd : Nat.card (Γ ⊓ ιc.range : Subgroup _) ∣ 3 ^ 3 := by
      rw [show 3 ^ 3 = 27 by norm_num, ← hΓ27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases i
    · rw [hik]; norm_num
    · rw [hik]; norm_num
    · rw [hik]; norm_num
    · exfalso
      exact hlt (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hik, hΓ27]; norm_num))
  have hXC : X ≤ C := by
    intro x hx
    rw [hC, barCentralizer_zpowers_eq_autFix (hAN h.a_mem)]
    have hcomm := (Item82OneProof.commute_of_mem_autThetaQuot hAe hτΓ
      (Subgroup.mem_comap.mp hx).1).eq
    apply hinj
    change MulAut.conj (τ x) = MulAut.conj x
    rw [← mul_mulAutConj_mul_inv]
    change τ * ιc x * τ⁻¹ = ιc x
    rw [hcomm, mul_inv_cancel_right]
  have hX3 : IsPGroup 3 X := by
    intro x
    refine ⟨1, Subtype.ext (hinj ?_)⟩
    rw [pow_one, Subgroup.coe_pow, map_pow, OneMemClass.coe_one, map_one]
    exact Item82OneProof.pow_three_of_mem_autThetaQuot hAe (Subgroup.mem_comap.mp x.2).1
  obtain ⟨P, hXP⟩ := (hX3.comap_subtype (K := C)).exists_le_sylow
  set Q : Sylow 3 (GorensteinWalter.PSL2 (GH74.GLS.IVK.fixedField σ)) :=
    P.mapSurjective (f := ι.toMonoidHom) ι.surjective with hQ
  obtain ⟨eQ⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hej Q
  set QS : Subgroup (GorensteinWalter.PSL2 (GH74.GLS.IVK.fixedField σ)) := Q.toSubgroup
    with hQS
  have hQcomm : ∀ x ∈ QS, ∀ y ∈ QS, x * y = y * x := by
    intro x hx y hy
    have h1 := congrArg eQ (mul_comm (eQ.symm ⟨x, hx⟩) (eQ.symm ⟨y, hy⟩))
    rw [map_mul, map_mul, eQ.apply_symm_apply, eQ.apply_symm_apply] at h1
    exact congrArg Subtype.val h1
  have hQcard : Nat.card QS = 3 ^ e := by
    rw [← Nat.card_congr eQ.toEquiv, Nat.card_congr Multiplicative.toAdd, hej]
  have hPQ : ((P : Subgroup C).map ι.toMonoidHom) = QS := rfl
  have hPcard : Nat.card (P : Subgroup C) = 3 ^ e := by
    rw [← hQcard, ← hPQ, Subgroup.card_map_of_injective ι.injective]
  have hPcomm : ∀ x ∈ (P : Subgroup C), ∀ y ∈ (P : Subgroup C), x * y = y * x := by
    intro x hx y hy
    apply ι.injective
    rw [map_mul, map_mul]
    exact hQcomm _ (hPQ ▸ Subgroup.mem_map_of_mem _ hx) _ (hPQ ▸ Subgroup.mem_map_of_mem _ hy)
  set T : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (P : Subgroup C).map C.subtype with hT
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hXT : X ≤ T := fun x hx => ⟨⟨x, hXC hx⟩, hXP (Subgroup.mem_comap.mpr hx), rfl⟩
  have hTcard : Nat.card T = 3 ^ e := by
    rw [hT, Subgroup.card_map_of_injective C.subtype_injective, hPcard]
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hPcomm x hx y hy)
  obtain ⟨tb, htbT, htbX⟩ : ∃ tb ∈ T, tb ∉ X := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card T ≤ Nat.card X := Subgroup.card_le_of_le hcon
    have h2 : 27 ≤ 3 ^ e := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have htbC : tb ∈ C := hTC htbT
  have hτfix : ∀ m : ℕ, (τ ^ m) tb = tb := by
    intro m
    have h1 := htbC
    rw [hC, barCentralizer_zpowers_eq_autFix (hAN h.a_mem)] at h1
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, h1, ih]
  have htbfix : ∀ β ∈ Γ, β tb = tb := by
    intro β hβ
    obtain ⟨k, hk, hkin⟩ := hcyc τ β (Item82OneProof.commute_of_mem_autThetaQuot hAe hτΓ hβ)
      (Item82OneProof.pow_three_of_mem_autThetaQuot hAe hτΓ)
      (Item82OneProof.pow_three_of_mem_autThetaQuot hAe hβ) hτout
    obtain ⟨x, hx⟩ := hkin
    have hxΓ : τ ^ k * β ∈ Γ := Γ.mul_mem (Γ.pow_mem hτΓ k) hβ
    have hxX : x ∈ X := Subgroup.mem_comap.mpr ⟨by rw [hx]; exact hxΓ, ⟨x, rfl⟩⟩
    have h1 : (τ ^ k * β) tb = tb := by
      rw [← hx, MulAut.conj_apply, hTcomm x (hXT hxX) tb htbT, mul_inv_cancel_right]
    have h2 : β = (τ ^ k)⁻¹ * (τ ^ k * β) := by group
    rw [h2, MulAut.mul_apply, h1]
    calc (τ ^ k)⁻¹ tb = (τ ^ k)⁻¹ ((τ ^ k) tb) := by rw [hτfix k]
      _ = tb := MulEquiv.symm_apply_apply _ _
  have h3 : (3 : GH74.GLS.IVK.fixedField σ) = 0 := by
    have : Fintype (GH74.GLS.IVK.fixedField σ) := Fintype.ofFinite _
    have hc := FiniteField.cast_card_eq_zero (GH74.GLS.IVK.fixedField σ)
    rw [← Nat.card_eq_fintype_card, hej] at hc
    push_cast at hc
    exact (pow_eq_zero_iff (n := e) (by omega)).mp hc
  have hmul3 : ∀ z : Multiplicative (GH74.GLS.IVK.fixedField σ), z ^ 3 = 1 := fun z => by
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_ofNat, h3, zero_mul, ofAdd_zero]
  have hQ3 : ∀ x ∈ QS, x ^ 3 = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : QS) ^ 3 = 1 := by
      rw [← eQ.apply_symm_apply ⟨x, hx⟩, ← map_pow, hmul3, map_one]
    simpa using congrArg Subtype.val h1
  have htb3 : tb ^ 3 = 1 := by
    obtain ⟨y, hyP, rfl⟩ := htbT
    have h1 : ι (y ^ 3) = 1 := by
      rw [map_pow]
      exact hQ3 _ (hPQ ▸ Subgroup.mem_map_of_mem _ hyP)
    have h2 : y ^ 3 = 1 := by
      rw [← map_one ι] at h1
      exact ι.injective h1
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, h2, OneMemClass.coe_one]
  obtain ⟨t, htA, ht3, htq⟩ := exists_lift_of_fixed hAN hA3 htb3 htbfix
  have ht3' : (t : G) ^ 3 = 1 := by simpa using congrArg Subtype.val ht3
  have htAmem : (t : G) ∈ A := by
    have hc : ∀ x ∈ A, x * (t : G) = (t : G) * x := fun x hx =>
      Subgroup.mem_centralizer_iff.mp htA x hx
    have hab := Sec21.Item211Proof.isElemAbelian_sup_zpowers hAe ht3' hc
    have heq := hAF.2.1 _ hab le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (t : G))
  have htN : (t : G) ∈ Subgroup.normalizer (L : Set G) := hAN htAmem
  have hconj : thetaQuotMulAut L (compAction L ⟨t, htN⟩) = ιc tb := by
    rw [thetaQuotMulAut_compAction_of_mem t.2 htN, ← htq]
  apply htbX
  refine Subgroup.mem_comap.mpr ⟨?_, ⟨tb, rfl⟩⟩
  rw [← hconj]
  exact mem_autThetaQuot_iff.mpr ⟨t, htN, htAmem, rfl⟩

theorem item82TwoPSL2Three_of (h45 : Sec4.Item4_5) (h9 : Item82TwoPSL2Nine) :
    Item82TwoPSL2Three := by
  intro G _ _ A c L a h h81 e he
  rcases (show e = 2 ∨ 3 ≤ e by omega) with rfl | he3
  · exact h9 G A c L a h h81
  · refine ⟨fun e₁ => ?_⟩
    have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
      Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1
        h.mem_A h.ne_one L h.mem_thetaComponentsAt
    exact false_of_psl2_three h h81 hAN he3 e₁

end PSL2

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
