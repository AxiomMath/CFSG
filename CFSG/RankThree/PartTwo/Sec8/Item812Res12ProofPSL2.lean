module

public import CFSG.RankThree.PartTwo.Sec8.Item82Res2ProofPSL2
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3
import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)


@[expose] def Item82TwoPSL2NineCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → Nat.card A = 81 → A ≤ Subgroup.normalizer (L : Set G) →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2))) →
    Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) ≠ 9

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem false_of_psl2_of_card_lt (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {e : ℕ} (he : 1 ≤ e)
    (hlt : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) < 3 ^ e)
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
  have hXlt : Nat.card X < 3 ^ e := by
    rw [hXcard]
    exact hlt
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

theorem item82TwoPSL2Nine_of_core (h45 : Sec4.Item4_5) (hC : Item82TwoPSL2NineCore) :
    Item82TwoPSL2Nine := by
  intro G _ _ A c L a h h81
  refine ⟨fun e₁ => ?_⟩
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1
      h.mem_A h.ne_one L h.mem_thetaComponentsAt
  have h9 := hC G A c L a h h81 hAN ⟨e₁⟩
  refine false_of_psl2_of_card_lt h h81 hAN (e := 2) (by norm_num) ?_ e₁
  set Γ := autThetaQuot A L with hΓ
  set ιc : (L ⧸ aschbacherSolvableCore 3 L) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    MulAut.conj with hιc
  have hτΓ : thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) ∈ Γ :=
    mem_autThetaQuot_iff.mpr ⟨a, hAN h.a_mem, h.a_mem, rfl⟩
  have hτout : ¬ IsInnerAut (thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩)) :=
    h.not_isInnerAut_induced
  have hΓ27 : Nat.card Γ = 27 := card_autThetaQuot_eq_27 h h81 hAN
  have hlt : (Γ ⊓ ιc.range : Subgroup _) ≠ Γ := fun heq =>
    hτout (by rw [← heq] at hτΓ; exact hτΓ.2)
  have hdvd : Nat.card (Γ ⊓ ιc.range : Subgroup _) ∣ 3 ^ 3 := by
    rw [show 3 ^ 3 = 27 by norm_num, ← hΓ27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases i
  · rw [hik]; norm_num
  · rw [hik]; norm_num
  · exact absurd (by rw [hik]; norm_num) h9
  · exfalso
    exact hlt (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hik, hΓ27]; norm_num))


theorem item82TwoPSL2Three_of_core (h45 : Sec4.Item4_5) (hC : Item82TwoPSL2NineCore) :
    Item82TwoPSL2Three :=
  item82TwoPSL2Three_of h45 (item82TwoPSL2Nine_of_core h45 hC)

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
