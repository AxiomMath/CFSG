module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 4.17 from BG Section 4 -/

universe u

section Main

open scoped FixedPoints commutatorElement

private theorem CFSG.derivedSubgroup_isPGroup_of_faithful_elementaryAbelian_card_le_p_sq_odd
    {B V : Type*} [Group B] [Finite B] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    [MulDistribMulAction B V] [FaithfulSMul B V]
    (hoddB : Odd (Nat.card B)) (hVcard : Nat.card V ≤ p ^ 2) :
    IsPGroup p (derivedSubgroup B) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hVp : IsPGroup p V := IsElementaryAbelian.isPGroup p V
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hn_le : n ≤ 2 := by
    have hpow_le : p ^ n ≤ p ^ 2 := by simpa [hn] using hVcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hpow_le
  interval_cases n
  · have hVcard1 : Nat.card V = 1 := by simpa using hn
    have hVsub : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hVcard1).1
    let : Subsingleton V := hVsub
    have hBsub : Subsingleton B :=
      ⟨fun _ _ => FaithfulSMul.eq_of_smul_eq_smul (α := V) fun _ => Subsingleton.elim _ _⟩
    let : Subsingleton B := hBsub
    have hD_bot : derivedSubgroup B = ⊥ := by
      apply eq_bot_iff.2
      intro x _hx
      exact Subsingleton.elim x 1
    rw [hD_bot]
    exact IsPGroup.of_card (p := p) (G := (⊥ : Subgroup B)) (n := 0) (by simp)
  · have hVcardp : Nat.card V = p := by simpa using hn
    have hVcyc : IsCyclic V := isCyclic_of_prime_card hVcardp
    let : IsCyclic V := hVcyc
    let eAut : MulAut V ≃* (ZMod (Nat.card V))ˣ := IsCyclic.mulAutMulEquiv (G := V)
    let : CommGroup (MulAut V) :=
      MonoidHom.commGroupOfInjective eAut.toMonoidHom eAut.injective
    have hBcomm : IsMulCommutative B := by
      refine ⟨⟨fun a b => ?_⟩⟩
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro v
      let φ : B →* MulAut V := MulDistribMulAction.toMulAut B V
      have hφeq : φ (a * b) = φ (b * a) := by
        calc
          φ (a * b) = φ a * φ b := by exact map_mul φ a b
          _ = φ b * φ a := by rw [mul_comm]
          _ = φ (b * a) := by exact (map_mul φ b a).symm
      simpa [φ, MulDistribMulAction.toMulAut_apply] using
        congrArg (fun f : MulAut V => f v) hφeq
    have hcenter : Subgroup.center B = ⊤ := by
      apply top_unique
      intro x _hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact (IsMulCommutative.is_comm (M := B)).comm y x
    have hD_bot : derivedSubgroup B = ⊥ := by
      change derivedSeries B 1 = ⊥
      rw [derivedSeries_one]
      exact (commutator_eq_bot_iff_center_eq_top B).2 hcenter
    rw [hD_bot]
    exact IsPGroup.of_card (p := p) (G := (⊥ : Subgroup B)) (n := 0) (by simp)
  · have hVcardp2 : Nat.card V = p ^ 2 := by simpa using hn
    let : CommGroup V := IsMulCommutative.instCommGroup
    let ρ : Representation (ZMod p) B (Additive V) :=
      Theory.Representation.ofElementaryAbelianAction (A := B) (G := V) (p := p)
    have hρinj : Function.Injective ρ := by
      intro a b hab
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro v
      have h := congrArg (fun f : Module.End (ZMod p) (Additive V) => f (Additive.ofMul v)) hab
      exact Additive.ofMul.injective (by simpa [ρ] using h)
    have hdim : Module.finrank (ZMod p) (Additive V) = 2 := by
      have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
      have hVcardp2_add : Nat.card (Additive V) = p ^ 2 := by
        calc
          Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
          _ = p ^ 2 := hVcardp2
      have hpow : p ^ Module.finrank (ZMod p) (Additive V) = p ^ 2 := by
        simpa [ZMod.card, hVcardp2_add] using hnat.symm
      exact Nat.pow_right_injective hp.one_lt hpow
    obtain ⟨C, _hCcomm, hcomm_le_C⟩ :=
      theorem_2_6_b (F := ZMod p) (G := B) hoddB hdim (ρ := ρ) hρinj
    let D : Subgroup B := derivedSubgroup B
    have hD_le_C : D ≤ (C : Subgroup B) := by
      change ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ ≤ (C : Subgroup B)
      exact hcomm_le_C
    have hDsub_p : IsPGroup p (D.subgroupOf (C : Subgroup B)) := by
      simpa [ZMod.ringChar_zmod_n] using
        C.isPGroup'.to_subgroup (D.subgroupOf (C : Subgroup B))
    have hDmap_p : IsPGroup p ((D.subgroupOf (C : Subgroup B)).map (C : Subgroup B).subtype) :=
      IsPGroup.map (p := p) (H := D.subgroupOf (C : Subgroup B)) hDsub_p
        (C : Subgroup B).subtype
    have hDmap_eq : (D.subgroupOf (C : Subgroup B)).map (C : Subgroup B).subtype = D := by
      simpa [D] using
        Subgroup.map_subgroupOf_eq_of_le (H := D) (K := (C : Subgroup B)) hD_le_C
    change IsPGroup p D
    rw [← hDmap_eq]
    exact hDmap_p

public theorem CFSG.theorem_4_17 {R A : Type*} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    [MulDistribMulAction A R] [FaithfulSMul A R] (hsolvA : Group.IsSolvable A)
    (hrank : groupRank R ≤ 2) (hAodd : Odd (Nat.card A)) :
    IsPGroup p (derivedSubgroup A) := by
  classical
  rcases hsolvA with ⟨_hsolvA⟩
  by_cases hRsub : Subsingleton R
  · let : Subsingleton R := hRsub
    have hAsub : Subsingleton A :=
      ⟨fun _ _ => FaithfulSMul.eq_of_smul_eq_smul (α := R) fun _ => Subsingleton.elim _ _⟩
    let : Subsingleton A := hAsub
    have hD_bot : derivedSubgroup A = ⊥ := by
      apply eq_bot_iff.2
      intro x _hx
      exact Subsingleton.elim x 1
    rw [hD_bot]
    exact IsPGroup.of_card (p := p) (G := (⊥ : Subgroup A)) (n := 0) (by simp)
  · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hRsub
    obtain ⟨H, hHchar, _hHcomm, _hHnil, hHexp, hHfix_p⟩ :=
      theorem_1_13 (G := R) (p := p) hpodd
    let : H.Characteristic := hHchar
    let : H.Normal := by infer_instance
    have hHp : IsPGroup p H := (Fact.out : IsPGroup p R).to_subgroup H
    let : Fact (IsPGroup p H) := ⟨hHp⟩
    have hHrank : groupRank H ≤ 2 :=
      (groupRank_le_of_subgroup (R := R) H).trans hrank
    have hVcard : Nat.card (H ⧸ frattini H) ≤ p ^ 2 :=
      natCard_frattini_quotient_le_p_sq_of_groupRank_le_two_and_exponent_p
        (R := H) (p := p) hHrank hHexp
    let : IsInvariant A R H := isInvariant_of_characteristic (A := A) (G := R) H
    let : MulDistribMulAction A H := inferInstance
    have hΦinv : IsInvariant A H (frattini H) :=
      isInvariant_of_characteristic (A := A) (G := H) (frattini H)
    let V : Type _ := H ⧸ frattini H
    let : MulDistribMulAction A V :=
      quotientMulDistribMulAction (A := A) (G := H) (frattini H) hΦinv
    have hVelem : IsElementaryAbelian p V := by
      simpa [V] using isElementaryAbelian_quotient_frattini (R := H) (p := p)
    let : IsElementaryAbelian p V := hVelem
    let φ : A →* MulAut V := MulDistribMulAction.toMulAut A V
    have hker_p : IsPGroup p φ.ker := by
      refine (IsPGroup.iff_card (p := p) (G := φ.ker)).2 ?_
      refine ⟨(Nat.card φ.ker).primeFactorsList.length, ?_⟩
      apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := φ.ker)).ne'
      intro q hqprime hq_dvd
      by_contra hq_ne_p
      let : Fact q.Prime := ⟨hqprime⟩
      obtain ⟨a, ha_order⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) q hq_dvd
      have ha_order_A : orderOf (a : A) = q := by
        calc
          orderOf (a : A) = orderOf a := Subgroup.orderOf_coe (H := φ.ker) a
          _ = q := ha_order
      let Aq : Subgroup A := Subgroup.zpowers (a : A)
      have hAq_card : Nat.card Aq = q := by
        simp [Aq, ha_order_A]
      have hAq_le_ker : Aq ≤ φ.ker := by
        intro b hb
        rcases Subgroup.mem_zpowers_iff.mp hb with ⟨k, hk⟩
        rw [← hk]
        exact φ.ker.zpow_mem a.2 k
      let : MulDistribMulAction Aq H := inferInstance
      let : MulDistribMulAction Aq V := MulDistribMulAction.compHom V Aq.subtype
      have hquot_triv : ActsTrivially (A := Aq) (G := V) := by
        intro b v
        have hbker : (b : A) ∈ φ.ker := hAq_le_ker b.2
        have hbφ : φ (b : A) = 1 := by simpa [MonoidHom.mem_ker] using hbker
        have hv := congrArg (fun f : MulAut V => f v) hbφ
        change (b : A) • v = v
        simpa [φ, MulDistribMulAction.toMulAut_apply] using hv
      have hcop_Aq_H : Nat.Coprime (Nat.card Aq) (Nat.card H) := by
        obtain ⟨m, hHcard⟩ := hHp.exists_card_eq
        have hq_coprime_p : Nat.Coprime q p :=
          (Nat.coprime_primes hqprime (Fact.out : Nat.Prime p)).2 hq_ne_p
        simpa [hAq_card, hHcard] using hq_coprime_p.pow_right m
      have htrivH : ActsTrivially (A := Aq) (G := H) :=
        theorem_1_8 (R := H) (A := Aq) (p := p) hcop_Aq_H (by simpa [V] using hquot_triv)
      let aAq : Aq := ⟨(a : A), Subgroup.mem_zpowers (a : A)⟩
      let ψ : MulAut R := MulDistribMulAction.toMulAut A R (a : A)
      have hψ_ne_one : ψ ≠ 1 := by
        intro hψ_one
        have ha_one_A : (a : A) = 1 := by
          apply FaithfulSMul.eq_of_smul_eq_smul (α := R)
          intro r
          have hr := congrArg (fun f : MulAut R => f r) hψ_one
          simpa [ψ, MulDistribMulAction.toMulAut_apply] using hr
        have hq_one : q = 1 := by
          simpa [ha_one_A] using ha_order_A.symm
        exact hqprime.ne_one hq_one
      have hψ_dvd_q : orderOf ψ ∣ q := by
        simpa [ψ, ha_order_A] using orderOf_map_dvd (MulDistribMulAction.toMulAut A R) (a : A)
      have hψ_order : orderOf ψ = q := by
        have hψ_order_ne_one : orderOf ψ ≠ 1 := by
          intro horder
          exact hψ_ne_one (orderOf_eq_one_iff.mp horder)
        rcases (Nat.dvd_prime hqprime).1 hψ_dvd_q with h1 | hq
        · exact False.elim (hψ_order_ne_one h1)
        · exact hq
      let Afix : Subgroup (MulAut R) := fixingSubgroup (M := MulAut R) (α := R) (H : Set R)
      have hψ_mem : ψ ∈ Afix := by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        let xH : H := ⟨x, hx⟩
        have hfix := htrivH aAq xH
        exact congrArg Subtype.val hfix
      let ψfix : Afix := ⟨ψ, hψ_mem⟩
      have hψfix_order : orderOf ψfix = q := by
        calc
          orderOf ψfix = orderOf (ψfix : MulAut R) := (Subgroup.orderOf_coe (H := Afix) ψfix).symm
          _ = orderOf ψ := rfl
          _ = q := hψ_order
      have hq_dvd_Afix : q ∣ Nat.card Afix := by
        rw [← hψfix_order]
        exact orderOf_dvd_natCard ψfix
      obtain ⟨m, hAfix_card⟩ := hHfix_p.exists_card_eq
      have hq_dvd_pow : q ∣ p ^ m := by
        simpa [Afix, hAfix_card] using hq_dvd_Afix
      have hq_eq_p : q = p :=
        Nat.prime_eq_prime_of_dvd_pow hqprime (Fact.out : Nat.Prime p) hq_dvd_pow
      exact hq_ne_p hq_eq_p
    let B : Subgroup (MulAut V) := φ.range
    let φB : A →* B := φ.rangeRestrict
    have hBodd : Odd (Nat.card B) :=
      hAodd.of_dvd_nat (Subgroup.card_dvd_of_surjective φ.rangeRestrict_surjective)
    have hBder_p : IsPGroup p (derivedSubgroup B) :=
      derivedSubgroup_isPGroup_of_faithful_elementaryAbelian_card_le_p_sq_odd
        (B := B) (V := V) (p := p) hBodd (by simpa [V] using hVcard)
    have hmap_der : (derivedSubgroup A).map φB = derivedSubgroup B := by
      simpa [derivedSubgroup, derivedSeries_one] using
        (map_derivedSeries_eq (f := φB) φ.rangeRestrict_surjective 1)
    have hDimage_p : IsPGroup p ((derivedSubgroup A).map φ) := by
      have hmap_p : IsPGroup p ((derivedSubgroup A).map φB) := by
        rw [hmap_der]
        exact hBder_p
      have hmap_subtype_p : IsPGroup p (((derivedSubgroup A).map φB).map B.subtype) :=
        IsPGroup.map (p := p) (H := (derivedSubgroup A).map φB) hmap_p B.subtype
      have hmap_map : ((derivedSubgroup A).map φB).map B.subtype = (derivedSubgroup A).map φ := by
        ext x
        constructor
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨g, hg, rfl⟩
          exact Subgroup.mem_map_of_mem φ hg
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
          refine Subgroup.mem_map.mpr ?_
          refine ⟨φB g, Subgroup.mem_map_of_mem φB hg, rfl⟩
      rw [hmap_map] at hmap_subtype_p
      exact hmap_subtype_p
    intro d
    let img : (derivedSubgroup A).map φ := ⟨φ (d : A), Subgroup.mem_map_of_mem φ d.2⟩
    obtain ⟨m, hm⟩ := hDimage_p img
    have hφpow : φ ((d : A) ^ (p ^ m)) = 1 := by
      have hmval : ((img : MulAut V) ^ (p ^ m)) = 1 := congrArg Subtype.val hm
      calc
        φ ((d : A) ^ (p ^ m)) = φ (d : A) ^ (p ^ m) := map_pow φ (d : A) (p ^ m)
        _ = 1 := by simpa [img] using hmval
    let dk : φ.ker := ⟨(d : A) ^ (p ^ m), by simpa [MonoidHom.mem_ker] using hφpow⟩
    obtain ⟨n, hn⟩ := hker_p dk
    refine ⟨m + n, ?_⟩
    apply Subtype.ext
    have hnval := congrArg Subtype.val hn
    change (((d : A) ^ (p ^ m)) ^ (p ^ n) : A) = 1 at hnval
    have hdn : (d : A) ^ (p ^ m * p ^ n) = 1 := by
      simpa [pow_mul] using hnval
    change ((d : A) ^ (p ^ (m + n)) : A) = 1
    simpa [Nat.pow_add] using hdn
