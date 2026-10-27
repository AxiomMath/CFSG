module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: source-independent core facts

This module collects the arithmetic and Peterfalvi-kernel facts used in the
proof of Lemma 11.5.  In particular, the small-prime divisibility argument is
proved directly rather than being left behind an earlier-book boundary.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

private def lemma115_invariantSubgroupAut
    {X : Type u} [Group X]
    (phi : MulAut X) (D : Subgroup X)
    (hD : ∀ x : X, x ∈ D ↔ phi x ∈ D) : MulAut D where
  toFun x := ⟨phi x, (hD x).mp x.2⟩
  invFun x := ⟨phi.symm x, (hD (phi.symm x)).mpr (by simp)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

/-- If `p` is an odd prime and `f` is one of the two possible orders supplied
by Lemma 11.4, then `f` does not divide the relevant Mersenne number. -/
public theorem lemma115_small_prime_not_dvd_mersenne
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f = 3 ∨ f = 5) :
    ¬ f ∣ 2 ^ p - 1 := by
  rcases hf with rfl | rfl
  · intro hdiv
    have hmod : 1 ≡ 2 ^ p [MOD 3] := by
      apply (Nat.modEq_iff_dvd' (Nat.one_le_pow p 2 (by omega))).2
      exact hdiv
    let z : (ZMod 3)ˣ := Units.mk0 2 (by decide)
    have hpow : z ^ p = 1 := by
      apply Units.ext
      simpa [z, Nat.cast_pow] using
        ((ZMod.natCast_eq_natCast_iff (2 ^ p) 1 3).2 hmod.symm)
    have htwo : z ^ 2 = 1 := by decide
    have hne : z ≠ 1 := by decide
    have horder : orderOf z = 2 := orderOf_eq_prime htwo hne
    have h2dvd : 2 ∣ p := by
      rw [← horder]
      exact orderOf_dvd_of_pow_eq_one hpow
    rcases hp.odd_of_ne_two hp2 with ⟨k, hk⟩
    rcases h2dvd with ⟨l, hl⟩
    omega
  · intro hdiv
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hmod : 1 ≡ 2 ^ p [MOD 5] := by
      apply (Nat.modEq_iff_dvd' (Nat.one_le_pow p 2 (by omega))).2
      exact hdiv
    let z : (ZMod 5)ˣ := Units.mk0 (2 : ZMod 5) (by decide)
    have hpow : z ^ p = 1 := by
      apply Units.ext
      simpa [z, Nat.cast_pow] using
        ((ZMod.natCast_eq_natCast_iff (2 ^ p) 1 5).2 hmod.symm)
    have hfour : z ^ 4 = 1 := by decide
    have hne : z ≠ 1 := by decide
    have hnot2 : z ^ 2 ≠ 1 := by decide
    have hnot3 : z ^ 3 ≠ 1 := by decide
    have hdiv4 : orderOf z ∣ 4 := orderOf_dvd_of_pow_eq_one hfour
    have hpos : 0 < orderOf z := orderOf_pos z
    have hle : orderOf z ≤ 4 := Nat.le_of_dvd (by omega) hdiv4
    have hcases : orderOf z = 1 ∨ orderOf z = 2 ∨
        orderOf z = 3 ∨ orderOf z = 4 := by omega
    have horder : orderOf z = 4 := by
      rcases hcases with h1 | h2 | h3 | h4
      · exact False.elim (hne (orderOf_eq_one_iff.mp h1))
      · exact False.elim (hnot2
          (orderOf_dvd_iff_pow_eq_one.mp (by simp [h2])))
      · exact False.elim (hnot3
          (orderOf_dvd_iff_pow_eq_one.mp (by simp [h3])))
      · exact h4
    have h4dvd : 4 ∣ p := by
      rw [← horder]
      exact orderOf_dvd_of_pow_eq_one hpow
    have h2dvd : 2 ∣ p := dvd_trans (by norm_num : 2 ∣ 4) h4dvd
    rcases hp.odd_of_ne_two hp2 with ⟨k, hk⟩
    rcases h2dvd with ⟨l, hl⟩
    omega

/-- A prime absent from `r` and `q` is also absent from `r ^ a * q`. -/
public theorem lemma115_prime_not_dvd_prime_power_mul
    {f r a q : ℕ} (hf : f.Prime) (hr : r.Prime)
    (hne : f ≠ r) (hq : ¬ f ∣ q) :
    ¬ f ∣ r ^ a * q := by
  intro h
  rcases (Nat.Prime.dvd_mul hf).mp h with hpow | hq'
  · have hfr : f ∣ r := hf.dvd_of_dvd_pow hpow
    have hfeq : f = r := by
      rcases (Nat.dvd_prime hr).mp hfr with h | h
      · exact (hf.ne_one h).elim
      · exact h
    exact hne hfeq
  · exact hq hq'

/-- The exact arithmetic endpoint needed to rule out `f ∣ |I|` in Lemma
11.5, after Proposition 10.2 has expressed the relevant exponent. -/
public theorem lemma115_small_prime_not_dvd_exponent_product
    {p f r a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f = 3 ∨ f = 5) (hr : r.Prime)
    (hrq : r ∣ 2 ^ p - 1) :
    ¬ f ∣ r ^ a * (2 ^ p - 1) := by
  have hfprime : f.Prime := by
    rcases hf with rfl | rfl
    · exact Nat.prime_three
    · exact Nat.prime_five
  have hfq : ¬ f ∣ 2 ^ p - 1 :=
    lemma115_small_prime_not_dvd_mersenne hp hp2 hf
  have hfr : f ≠ r := by
    intro h
    exact hfq (h.symm ▸ hrq)
  exact lemma115_prime_not_dvd_prime_power_mul hfprime hr hfr hfq

/-- A prime dividing the cardinality of a Peterfalvi anti-fixed set occurs as
the order of an element of that set.  The proof chooses an involution-
invariant Sylow subgroup, applies Peterfalvi `lemma_a` inside it, and takes a
suitable power of a nontrivial anti-fixed element. -/
public theorem lemma115_exists_prime_order_mem_peterfalviKSet_of_dvd_card
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card {x : X // x ∈ peterfalviKSet D t}) :
    ∃ x : X, x ∈ peterfalviKSet D t ∧ orderOf x = r := by
  classical
  let phiX : MulAut X := MulAut.conj t
  have hphiX_D : ∀ x : X, x ∈ D ↔ phiX x ∈ D := by
    intro x
    simpa [phiX, MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hDnorm x)
  let phi : MulAut D := lemma115_invariantSubgroupAut phiX D hphiX_D
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have hphi_sq : phi ^ 2 = 1 := by
    ext x
    simp [phi, lemma115_invariantSubgroupAut, phiX, pow_two,
      MulAut.conj_apply, ht.inv_eq_self, mul_assoc]
    rw [← mul_assoc, htt, one_mul, mul_one]
  have hphi_order : orderOf phi ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hphi_sq
  let A : Subgroup (MulAut D) := Subgroup.zpowers phi
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA_pgroup : IsPGroup 2 A := by
    have hcard_dvd : Nat.card A ∣ 2 := by
      simpa [A, Nat.card_zpowers] using hphi_order
    rcases Nat.prime_two.eq_one_or_self_of_dvd (Nat.card A) hcard_dvd with
      hcard_one | hcard_two
    · exact IsPGroup.of_card (p := 2) (G := A) (n := 0)
        (by simp [hcard_one])
    · exact IsPGroup.of_card (p := 2) (G := A) (n := 1)
        (by simp [hcard_two])
  letI : Fact (IsPGroup 2 A) := ⟨hA_pgroup⟩
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hcoprime : Nat.Coprime 2 (Nat.card D) :=
    hDodd.coprime_two_left
  obtain ⟨P, hPinv⟩ :=
    exists_invariant_sylow (G := D) (A := A) (p := 2) (q := r) hcoprime
  let Y : Subgroup X := D ⊓ Subgroup.centralizer ({t} : Set X)
  let J : Set X := peterfalviKSet D t
  have hfactor : Nat.card D = Nat.card Y * Nat.card J := by
    simpa [Y, J, peterfalviKSet] using
      (PFchapter1section1.lemma_a t D ht hDodd hDnorm).2.2
  have hJ_dvd_D : Nat.card J ∣ Nat.card D := by
    refine ⟨Nat.card Y, ?_⟩
    simpa [Nat.mul_comm] using hfactor
  have hr_dvd_D : r ∣ Nat.card D :=
    hrdvd.trans (by simpa [J] using hJ_dvd_D)
  have hr_ne_two : r ≠ 2 := by
    intro hr2
    exact hDodd.not_two_dvd_nat (by simpa [hr2] using hr_dvd_D)
  let YD : Subgroup D := Y.subgroupOf D
  have hY_le_D : Y ≤ D := inf_le_left
  have hYDcard : Nat.card YD = Nat.card Y := by
    simpa [YD] using natCard_subgroupOf_eq Y D hY_le_D
  have hYDindex : YD.index = Nat.card J := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Y))
    calc
      YD.index * Nat.card Y = YD.index * Nat.card YD := by rw [hYDcard]
      _ = Nat.card D := Subgroup.index_mul_card (H := YD)
      _ = Nat.card Y * Nat.card J := hfactor
      _ = Nat.card J * Nat.card Y := by rw [Nat.mul_comm]
  have hP_not_le_YD : ¬ (P : Subgroup D) ≤ YD := by
    intro hP_le
    have hr_dvd_YDindex : r ∣ YD.index := by
      simpa [hYDindex, J] using hrdvd
    have hindex_dvd : YD.index ∣ (P : Subgroup D).index :=
      Subgroup.index_dvd_of_le hP_le
    exact P.not_dvd_index (hr_dvd_YDindex.trans hindex_dvd)
  let PX : Subgroup X := (P : Subgroup D).map D.subtype
  have hPX_le_D : PX ≤ D := by
    simpa [PX] using
      (Subgroup.map_subtype_le (H := D) (K := (P : Subgroup D)))
  have hPX_not_le_Ct : ¬ PX ≤ Subgroup.centralizer ({t} : Set X) := by
    intro hPX_le
    apply hP_not_le_YD
    intro x hxP
    change (x : X) ∈ Y
    refine ⟨x.2, hPX_le ?_⟩
    exact ⟨x, hxP, rfl⟩
  have ht_norm_PX : t ∈ Subgroup.normalizer (PX : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    have hforward : ∀ x : X, x ∈ PX → t * x * t⁻¹ ∈ PX := by
      intro x hx
      rcases hx with ⟨xD, hxP, rfl⟩
      let a : A := ⟨phi, Subgroup.mem_zpowers phi⟩
      have hmem : phi xD ∈ (P : Subgroup D) := by
        have hmem' := (hPinv.invariant a xD).mp hxP
        change (a : MulAut D) xD ∈ (P : Subgroup D) at hmem'
        simpa [a] using hmem'
      refine ⟨phi xD, hmem, ?_⟩
      rfl
    intro x
    constructor
    · exact hforward x
    · intro hx
      have hback := hforward (t * x * t⁻¹) hx
      have hconj_twice : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [ht.inv_eq_self]
        calc
          t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [htt]; simp
      rwa [hconj_twice] at hback
  obtain ⟨z, hzPX, hznotC⟩ := SetLike.not_le_iff_exists.mp hPX_not_le_Ct
  have hPXp : IsPGroup r PX :=
    IsPGroup.map (p := r) (H := (P : Subgroup D)) P.isPGroup' D.subtype
  have hPXodd : Odd (Nat.card PX) := by
    rcases (IsPGroup.iff_card.mp hPXp) with ⟨n, hn⟩
    rw [hn]
    exact (hr.odd_of_ne_two hr_ne_two).pow
  let YP : Subgroup X := PX ⊓ Subgroup.centralizer ({t} : Set X)
  let ZP : Set X := peterfalviKSet PX t
  have hbij :
      Set.BijOn
        (fun p : YP × ZP => (p.1 : X) * (p.2 : X))
        Set.univ (PX : Set X) := by
    simpa [YP, ZP, peterfalviKSet] using
      (PFchapter1section1.lemma_a t PX ht hPXodd ht_norm_PX).1
  rcases hbij.2.2 hzPX with ⟨yz, _hyz, hyz_eq⟩
  let z0 : X := yz.2
  have hz0PX : z0 ∈ PX := yz.2.property.1
  have hz0inv : rightConjugateElem z0 t = z0⁻¹ := yz.2.property.2
  have hz0_ne : z0 ≠ 1 := by
    intro hz0
    apply hznotC
    have hz_eq : z = (yz.1 : X) := by
      simpa [z0, hz0] using hyz_eq.symm
    rw [hz_eq]
    exact yz.1.property.2
  let zPX : PX := ⟨z0, hz0PX⟩
  rcases (IsPGroup.iff_orderOf.mp hPXp) zPX with ⟨k, hk⟩
  have hz0_order : orderOf z0 = r ^ k := by
    simpa [zPX] using hk
  have hk_ne : k ≠ 0 := by
    intro hk0
    apply hz0_ne
    apply orderOf_eq_one_iff.mp
    simp [hz0_order, hk0]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne
  have hr_dvd_order : r ∣ orderOf z0 := by
    rw [hz0_order, pow_succ]
    exact dvd_mul_left r (r ^ l)
  let x : X := z0 ^ (orderOf z0 / r)
  refine ⟨x, ⟨hPX_le_D (PX.pow_mem hz0PX _), ?_⟩, ?_⟩
  · have hx_conj : (MulAut.conj t⁻¹) x = x⁻¹ := by
      rw [show (MulAut.conj t⁻¹) x =
          (MulAut.conj t⁻¹ z0) ^ (orderOf z0 / r) by
        exact map_pow (MulAut.conj t⁻¹) z0 _]
      have hz0inv' : (MulAut.conj t⁻¹) z0 = z0⁻¹ := by
        simpa [MulAut.conj_apply, rightConjugateElem] using hz0inv
      rw [hz0inv']
      simp [x]
    simpa [MulAut.conj_apply, rightConjugateElem] using hx_conj
  · exact orderOf_pow_orderOf_div (orderOf_pos z0).ne' hr_dvd_order

/-- Combining the existing `[II1; 4.2]` prime-transfer callback with the
preceding internal argument produces the exact prime-order-element endpoint
needed in Lemma 11.5. -/
public theorem lemma115_exists_prime_order_mem_peterfalviKSet_of_dvd_closure
    {X : Type u} [Group X] [Finite X]
    (h42 : II1Lemma42PrimeTransfer (X := X))
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card (Subgroup.closure (peterfalviKSet D t))) :
    ∃ x : X, x ∈ peterfalviKSet D t ∧ orderOf x = r := by
  apply lemma115_exists_prime_order_mem_peterfalviKSet_of_dvd_card
    ht hDodd hDnorm hr
  exact h42 D t hDodd ht hDnorm r hr hrdvd

/-- A prime at least seven does not divide the automorphism-group order of a
cyclic `3`- or `5`-group.  Written arithmetically, it does not divide the
Euler totient of the corresponding prime power. -/
public theorem lemma115_large_prime_not_dvd_totient_small_prime_power
    {p f n : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hf : f = 3 ∨ f = 5) :
    ¬ p ∣ Nat.totient (f ^ n) := by
  have hfprime : f.Prime := by
    rcases hf with rfl | rfl
    · exact Nat.prime_three
    · exact Nat.prime_five
  rcases n with _ | n
  · simpa using hp.not_dvd_one
  · rw [Nat.totient_prime_pow hfprime (Nat.succ_pos n)]
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with hpow | hpred
    · have hpf : p ∣ f := hp.dvd_of_dvd_pow hpow
      have hple : p ≤ f := Nat.le_of_dvd hfprime.pos hpf
      rcases hf with rfl | rfl <;> omega
    · have hpredpos : 0 < f - 1 := by
        rcases hf with rfl | rfl <;> omega
      have hple : p ≤ f - 1 := Nat.le_of_dvd hpredpos hpred
      rcases hf with rfl | rfl <;> omega

/-- Under the disjointness supplied by the Lemma 11.5 argument, Peterfalvi's
factorization lemma shows that the closure of the anti-fixed set is already
the anti-fixed set itself. -/
public theorem lemma115_closure_peterfalviKSet_eq_set_of_disjoint
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hDodd : Odd (Nat.card D))
    (hdisj : Disjoint (Subgroup.closure (peterfalviKSet D t))
      (peterfalviV D t)) :
    (Subgroup.closure (peterfalviKSet D t) : Set X) =
      peterfalviKSet D t := by
  classical
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  apply Set.Subset.antisymm
  · intro x hxK
    have hKD : K ≤ D := by
      rw [Subgroup.closure_le]
      intro y hy
      exact hy.1
    obtain ⟨hleft, _hright, _hcard⟩ :=
      PFchapter1section1.lemma_a t D ht hDodd hDnorm
    obtain ⟨p, _hp_univ, hp⟩ := hleft.surjOn (hKD hxK)
    have hpV : (p.1 : X) ∈ V := p.1.property
    have hpK : (p.2 : X) ∈ K :=
      Subgroup.subset_closure p.2.property
    have hp1_eq : (p.1 : X) = x * (p.2 : X)⁻¹ := by
      rw [← hp]
      simp [mul_assoc]
    have hp1K : (p.1 : X) ∈ K := by
      rw [hp1_eq]
      exact K.mul_mem hxK (K.inv_mem hpK)
    have hp1bot : (p.1 : X) ∈ (⊥ : Subgroup X) := by
      rw [← hdisj.eq_bot]
      exact ⟨hp1K, hpV⟩
    have hp1one : (p.1 : X) = 1 := by simpa using hp1bot
    have hx_eq : x = (p.2 : X) := by
      rw [← hp]
      simp [hp1one]
    rw [hx_eq]
    exact p.2.property
  · exact Subgroup.subset_closure

/-- A subgroup equal, as a set, to Peterfalvi's anti-fixed set is abelian. -/
public theorem lemma115_peterfalviKernel_commutative_of_eq_set
    {X : Type u} [Group X]
    {D K : Subgroup X} {t : X}
    (hKset : (K : Set X) = peterfalviKSet D t) :
    IsMulCommutative K := by
  refine IsMulCommutative.mk ⟨?_⟩
  intro a b
  apply Subtype.ext
  have haI : (a : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact a.property
  have hbI : (b : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact b.property
  have habI : (a : X) * (b : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact K.mul_mem a.property b.property
  have hinvComm : (a : X)⁻¹ * (b : X)⁻¹ =
      (b : X)⁻¹ * (a : X)⁻¹ := by
    calc
      (a : X)⁻¹ * (b : X)⁻¹ =
          rightConjugateElem (a : X) t *
            rightConjugateElem (b : X) t := by rw [haI.2, hbI.2]
      _ = rightConjugateElem ((a : X) * (b : X)) t := by
            simp [rightConjugateElem, mul_assoc]
      _ = ((a : X) * (b : X))⁻¹ := habI.2
      _ = (b : X)⁻¹ * (a : X)⁻¹ := by simp
  have h := congrArg Inv.inv hinvComm
  simpa using h.symm

/-- If an element has no fixed point in the conjugate-coset action of a
strongly embedded subgroup, then its centralizer has odd order.  Indeed, an
involution in the centralizer would have a unique fixed coset, which the
commuting element would necessarily fix as well. -/
public theorem lemma115_centralizer_odd_of_fixedPoints_eq_empty
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} (hM : IsStronglyEmbedded M) {x : X}
    (hfix : fixedPointsOfSubgroup X (conjugateCosetSpace M)
      (Subgroup.zpowers x) = ∅) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set X))) := by
  let C : Subgroup X := Subgroup.centralizer ({x} : Set X)
  by_contra hodd
  have heven : Even (Nat.card C) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨zC, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) 2 heven.two_dvd
  let z : X := zC
  have hzorderX : orderOf z = 2 := by
    rw [show orderOf z = orderOf zC by
      exact Subgroup.orderOf_coe zC, hzorder]
  have hz : IsInvolution z := by
    have hz' := (orderOf_eq_prime_iff (x := z) (p := 2)).mp hzorderX
    exact ⟨hz'.2, hz'.1⟩
  have hzx : z * x = x * z :=
    Subgroup.mem_centralizer_singleton_iff.mp zC.property
  obtain ⟨gamma, hzgamma, hgammaUnique⟩ :=
    hM.involution_fixed_coset_unique hz
  have hzxgamma : z • (x • gamma) = x • gamma := by
    calc
      z • (x • gamma) = (z * x) • gamma := by rw [mul_smul]
      _ = (x * z) • gamma := by rw [hzx]
      _ = x • (z • gamma) := by rw [mul_smul]
      _ = x • gamma := by rw [hzgamma]
  have hxgamma : x • gamma = gamma := hgammaUnique _ hzxgamma
  have hmem : gamma ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M)
      (Subgroup.zpowers x) :=
    mem_fixedPointsOfSubgroup_zpowers_iff.mpr hxgamma
  rw [hfix] at hmem
  exact hmem

end CFSG.BenderSuzuki
