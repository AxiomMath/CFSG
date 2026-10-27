module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki.PFchapter2

open PFchapter1section1 PFAppendixIII PFchapter1section3
open scoped Pointwise

private theorem chapter2_claim16_centralizer_le_normalizer
    {G : Type*} [Group G] (A : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hxy : y * g = g * y := (Subgroup.mem_centralizer_iff.mp hg) y hy
    have hconj : g * y * g⁻¹ = y := by
      calc
        g * y * g⁻¹ = (g * y) * g⁻¹ := by simp [mul_assoc]
        _ = (y * g) * g⁻¹ := by rw [hxy.symm]
        _ = y := by simp [mul_assoc]
    simpa [hconj] using hy
  · intro hy
    have hginv : g⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.inv_mem_iff (H := Subgroup.centralizer (A : Set G))).2 hg
    have hy' : g⁻¹ * (g * y * g⁻¹) * g ∈ A := by
      have hyc : g * y * g⁻¹ ∈ A := hy
      have hxy : (g * y * g⁻¹) * g⁻¹ = g⁻¹ * (g * y * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hginv) (g * y * g⁻¹) hyc
      have hconj : g⁻¹ * (g * y * g⁻¹) * g = g * y * g⁻¹ := by
        calc
          g⁻¹ * (g * y * g⁻¹) * g =
              (g⁻¹ * (g * y * g⁻¹)) * g := by simp [mul_assoc]
          _ = ((g * y * g⁻¹) * g⁻¹) * g := by rw [hxy]
          _ = g * y * g⁻¹ := by simp [mul_assoc]
      simpa [hconj] using hyc
    simpa [mul_assoc] using hy'

private theorem chapter2_claim16_mem_normalizer_centralizer_of_mem_normalizer
    {G : Type*} [Group G] (A : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      apply (hg (g⁻¹ * a * g)).mpr
      simpa [mul_assoc] using ha
    calc
      a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [hx _ ha']
      _ = (g * x * g⁻¹) * a := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    have hga : g * a * g⁻¹ ∈ A := (hg a).mp ha
    have hcomm := hx (g * a * g⁻¹) hga
    have h := congrArg (fun z : G => g⁻¹ * z * g) hcomm
    simpa [mul_assoc] using h

private theorem chapter2_claim16_mem_normalizer_inf
    {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩,
    fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

private theorem chapter2_claim16_mem_normalizer_sup
    {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hforward :
      ∀ {x : G},
        x ∈ Subgroup.normalizer (A : Set G) →
        x ∈ Subgroup.normalizer (B : Set G) →
        ∀ y, y ∈ A ⊔ B → x * y * x⁻¹ ∈ A ⊔ B := by
    intro x hxA hxB y hy
    rw [Subgroup.sup_eq_closure] at hy ⊢
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with hzA | hzB
      · exact Subgroup.subset_closure
          (Or.inl ((Subgroup.mem_normalizer_iff.mp hxA z).1 hzA))
      · exact Subgroup.subset_closure
          (Or.inr ((Subgroup.mem_normalizer_iff.mp hxB z).1 hzB))
    · simp
    · intro a b _ _ ha hb
      simpa [mul_assoc] using
        (Subgroup.closure ((A : Set G) ∪ (B : Set G))).mul_mem ha hb
    · intro a _ ha
      simpa [mul_assoc] using
        (Subgroup.closure ((A : Set G) ∪ (B : Set G))).inv_mem ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward hA hB x
  · intro hx
    have hAinv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hA
    have hBinv : g⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem hB
    have h := hforward hAinv hBinv (g * x * g⁻¹) hx
    simpa [mul_assoc] using h

private theorem chapter2_claim16_natCard_rightConjugate
    {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (rightConjugate A g) = Nat.card A := by
  rw [rightConjugate, Subgroup.conjBy]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.toEquiv


private theorem chapter2_claim16_mem_normalizer_of_rightConjugate_eq_self
    {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (h : rightConjugate A g = A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : g⁻¹ * x * (g⁻¹)⁻¹ ∈ rightConjugate A g := ⟨x, hx, rfl⟩
      simpa [h] using this
    · intro hx
      have hx' : g⁻¹ * x * (g⁻¹)⁻¹ ∈ A := by simpa using hx
      have : g⁻¹ * x * (g⁻¹)⁻¹ ∈ rightConjugate A g := by simpa [h] using hx'
      rcases this with ⟨y, hy, heq⟩
      have hyx : y = x := by
        apply (MulAut.conj g⁻¹).injective
        simpa [MulAut.conj_apply] using heq
      simpa [hyx] using hy
  simpa using (Subgroup.normalizer (A : Set G)).inv_mem hginv

private theorem chapter2_claim16_normalizer_le_normalizer_centerIn
    {G : Type*} [Group G] (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro g hg
  exact chapter2_claim16_mem_normalizer_inf hg
    (chapter2_claim16_mem_normalizer_centralizer_of_mem_normalizer A hg)

private theorem chapter2_claim16_disjoint_of_card_three_of_not_le
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hAcard : Nat.card A = 3) (hnot : ¬ A ≤ B) :
    Disjoint A B := by
  rw [disjoint_iff_inf_le]
  let K : Subgroup A := (A ⊓ B).subgroupOf A
  haveI : Fact (Nat.card A).Prime := ⟨by simpa [hAcard] using Nat.prime_three⟩
  rcases K.eq_bot_or_eq_top_of_prime_card with hK | hK
  · intro x hx
    have hxK : (⟨x, hx.1⟩ : A) ∈ K := hx
    rw [hK] at hxK
    simpa using hxK
  · exfalso
    apply hnot
    intro x hxA
    have hxK : (⟨x, hxA⟩ : A) ∈ K := by rw [hK]; trivial
    exact hxK.2

private theorem chapter2_claim16_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.property
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem chapter2_claim16_normal_of_index_eq_prime_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hGp : IsPGroup p G) (A : Subgroup G) (hindex : A.index = p) :
    A.Normal := by
  rcases hGp.exists_card_eq with ⟨n, hGcard⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    have hcard_one : Nat.card G = 1 := by simpa [hn] using hGcard
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard_one).1
    have hAtop : A = ⊤ := by
      apply le_antisymm le_top
      intro x hx
      have hxone : x = 1 := Subsingleton.elim x 1
      simp [hxone]
    have hp_one : p = 1 := by simpa [hAtop] using hindex.symm
    exact (Fact.out : Nat.Prime p).ne_one hp_one
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [hindex, hGcard]
  exact ((Fact.out : Nat.Prime p).pow_minFac hn_ne).symm

private theorem chapter2_claim16_not_stronglyReal_of_mem_peterfalviV_order_three
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s x : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧ W ≤ V ∧
      W = peterfalviW V (K : Set G) ∧ Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
      ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hxV : x ∈ V) (hxne : x ≠ 1) (hx3 : x ^ 3 = 1) :
    ¬ IsStronglyReal x := by
  intro hxstrong
  have hx2 : x ^ 2 ≠ 1 := by
    intro hx2
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hdvd1 : orderOf x ∣ 1 := by
      simpa using Nat.dvd_gcd hdvd2 hdvd3
    exact hxne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))
  have hodd := (lemma_3 H D Q K V W Q0 S Q1 t s hsec x hxstrong hx2).2
  have htC : t ∈ Subgroup.centralizer ({x} : Set G) := by
    have hxCt : x ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [hsec.1.2.2.2.1] at hxV
      exact hxV.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxCt).symm
  let tC : Subgroup.centralizer ({x} : Set G) := ⟨t, htC⟩
  have htC_order : orderOf tC = 2 := by
    have ht_order : orderOf t = 2 :=
      orderOf_eq_prime hsec.1.1.A1.involution_t.sq_eq_one
        hsec.1.1.A1.involution_t.ne_one
    simpa [tC] using (Subgroup.orderOf_coe tC).symm.trans ht_order
  have htwo_dvd : 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [← htC_order]
    exact orderOf_dvd_natCard tC
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr htwo_dvd)

private theorem chapter2_claim16_stronglyReal_rightConjugateElem
    {G : Type*} [Group G] {x : G} (g : G) (hx : IsStronglyReal x) :
    IsStronglyReal (rightConjugateElem x g) := by
  rcases hx with ⟨u, v, hu, hv, huv⟩
  refine ⟨rightConjugateElem u g, rightConjugateElem v g,
    isInvolution_rightConjugateElem hu, isInvolution_rightConjugateElem hv, ?_⟩
  calc
    rightConjugateElem x g = rightConjugateElem (u * v) g := by rw [huv]
    _ = rightConjugateElem u g * rightConjugateElem v g := by
      simp [rightConjugateElem, mul_assoc]


private theorem chapter2_claim16_Z1_stronglyReal
    {G : Type*} [Group G] (Z1 : Subgroup G) (s t : G)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hs : IsInvolution s) (ht : IsInvolution t) :
    ∀ z : G, z ∈ Z1 → z ≠ 1 → IsStronglyReal z := by
  intro z hzZ1 hzne
  have hzpow : z ∈ Subgroup.zpowers (s * t) := by simpa [hZ1] using hzZ1
  have hzinv : rightConjugateElem z s = z⁻¹ := by
    rw [Subgroup.mem_zpowers_iff] at hzpow
    rcases hzpow with ⟨n, rfl⟩
    have hss : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
    have hgen : (MulAut.conj s⁻¹) (s * t) = (s * t)⁻¹ := by
      simp only [MulAut.conj_apply, hs.inv_eq_self, mul_inv_rev, ht.inv_eq_self]
      calc
        s * (s * t) * s = (s * s) * t * s := by simp [mul_assoc]
        _ = t * s := by rw [hss]; simp
    have hmap : (MulAut.conj s⁻¹) ((s * t) ^ n) = ((s * t) ^ n)⁻¹ := by
      rw [map_zpow, hgen]
      exact inv_zpow (s * t) n
    simpa [rightConjugateElem, MulAut.conj_apply] using hmap
  have hs_inv : s⁻¹ = s := hs.inv_eq_self
  have hs_mul : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
  have hconj : s * z * s = z⁻¹ := by
    simpa [rightConjugateElem, hs_inv, mul_assoc] using hzinv
  have hzs_sq : (z * s) ^ 2 = 1 := by
    calc
      (z * s) ^ 2 = z * (s * z * s) := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hconj]; simp
  have hzs_ne : z * s ≠ 1 := by
    intro hzs
    have hz_eq_s : z = s := by
      calc
        z = z * 1 := by simp
        _ = z * (s * s) := by rw [hs_mul]
        _ = (z * s) * s := by simp [mul_assoc]
        _ = s := by rw [hzs]; simp
    have hz2 : z ^ 2 = 1 := by simpa [hz_eq_s] using hs.sq_eq_one
    have hdvd2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have hdvd3 : orderOf z ∣ 3 := by
      rw [← hst3]
      exact orderOf_dvd_of_mem_zpowers (by simpa [hZ1] using hzZ1)
    have hdvd1 : orderOf z ∣ 1 := by simpa using Nat.dvd_gcd hdvd2 hdvd3
    exact hzne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))
  exact ⟨z * s, s, ⟨hzs_ne, hzs_sq⟩, hs, by simp [hs_mul, mul_assoc]⟩

private theorem chapter2_claim16_s_inverts_Z1
    {G : Type*} [Group G] (Z1 : Subgroup G) (s t : G)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hs : IsInvolution s) (ht : IsInvolution t) :
    ∀ z : G, z ∈ Z1 → rightConjugateElem z s = z⁻¹ := by
  intro z hz
  have hzpow : z ∈ Subgroup.zpowers (s * t) := by simpa [hZ1] using hz
  rw [Subgroup.mem_zpowers_iff] at hzpow
  rcases hzpow with ⟨n, rfl⟩
  have hss : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
  have hgen : (MulAut.conj s⁻¹) (s * t) = (s * t)⁻¹ := by
    simp only [MulAut.conj_apply, hs.inv_eq_self, mul_inv_rev, ht.inv_eq_self]
    calc
      s * (s * t) * s = (s * s) * t * s := by simp [mul_assoc]
      _ = t * s := by rw [hss]; simp
  have hmap : (MulAut.conj s⁻¹) ((s * t) ^ n) = ((s * t) ^ n)⁻¹ := by
    rw [map_zpow, hgen]
    exact inv_zpow (s * t) n
  simpa [rightConjugateElem, MulAut.conj_apply] using hmap

private theorem chapter2_claim16_cyclic_order_three_mulAut_eq_id_or_inv
    {C : Type*} [Group C] [Finite C]
    (hcard : Nat.card C = 3) (alpha : MulAut C) :
    alpha = 1 ∨ ∀ x : C, alpha x = x⁻¹ := by
  letI : IsCyclic C := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hcard
  let u : (ZMod (Nat.card C))ˣ := IsCyclic.mulAutMulEquiv C alpha
  have hu_cases : u = 1 ∨ u = -1 := by
    have hcases : ∀ v : (ZMod (Nat.card C))ˣ, v = 1 ∨ v = -1 := by
      rw [hcard]
      decide
    exact hcases u
  rcases hu_cases with hu | hu
  · left
    apply (IsCyclic.mulAutMulEquiv C).injective
    simpa [u] using hu
  · right
    intro x
    haveI : Fintype C := Fintype.ofFinite _
    haveI : Fintype (MulAut C) := Fintype.ofFinite _
    haveI : DecidableEq (MulAut C) := Classical.decEq _
    have halpha : alpha = (IsCyclic.mulAutMulEquiv C).symm (-1) := by
      apply (IsCyclic.mulAutMulEquiv C).injective
      simpa [u] using hu
    rw [halpha]
    have h_card_mulAut : Nat.card (MulAut C) = 2 := by
      calc
        Nat.card (MulAut C) = (Nat.card C).totient := IsCyclic.card_mulAut (C)
        _ = 2 := by
          rw [hcard]
          decide
    have h_neg_one_ne_one : (-1 : (ZMod (Nat.card C))ˣ) ≠ 1 := by
      rw [hcard]; decide
    have h_phi_ne_one : (IsCyclic.mulAutMulEquiv C).symm (-1 : (ZMod (Nat.card C))ˣ) ≠ 1 := by
      intro h
      apply h_neg_one_ne_one
      calc
        (-1 : (ZMod (Nat.card C))ˣ) = (IsCyclic.mulAutMulEquiv C) ((IsCyclic.mulAutMulEquiv C).symm (-1)) := by
          simp
        _ = (IsCyclic.mulAutMulEquiv C) 1 := by rw [h]
        _ = 1 := by simp
    haveI : IsMulCommutative C := IsCyclic.isMulCommutative
    letI : CommGroup C := IsMulCommutative.instCommGroup
    let inv_aut : MulAut C :=
      { toFun := λ x : C => x⁻¹
        invFun := λ x : C => x⁻¹
        left_inv := λ x => by simp
        right_inv := λ x => by simp
        map_mul' := λ x y => by
          have hc : IsMulCommutative C := IsCyclic.isMulCommutative
          calc
            (x * y)⁻¹ = y⁻¹ * x⁻¹ := by simp
            _ = x⁻¹ * y⁻¹ := hc.is_comm.comm (y⁻¹) (x⁻¹) }
    have h_inv_ne_one : inv_aut ≠ (1 : MulAut C) := by
      have h_card3 : Fintype.card C = 3 := by
        simpa [Nat.card_eq_fintype_card] using hcard
      have h_gt1 : 1 < Fintype.card C := by
        rw [h_card3]; norm_num
      have h_nontriv : Nontrivial C := Fintype.one_lt_card_iff_nontrivial.mp h_gt1
      have h_exists : ∃ (x : C), x ≠ 1 := by
        obtain ⟨x, y, hxy⟩ := h_nontriv.exists_pair_ne
        by_cases hx1 : x = 1
        · refine ⟨y, ?_⟩
          intro hy1; apply hxy; rw [hx1, hy1]
        · exact ⟨x, hx1⟩
      rcases h_exists with ⟨z, hz⟩
      intro h
      have hz_inv_eq_z : z⁻¹ = z := by
        calc
          z⁻¹ = inv_aut z := rfl
          _ = (1 : MulAut C) z := by rw [h]
          _ = z := rfl
      have hz_sq_one : z ^ 2 = 1 := by
        have h_zz_one : z * z = 1 := by
          calc
            z * z = z * z⁻¹ := by rw [hz_inv_eq_z]
            _ = 1 := by simp
        calc
          z ^ 2 = z * z := by simp [pow_two]
          _ = 1 := h_zz_one
      have h_dvd2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz_sq_one
      have h_dvd3 : orderOf z ∣ 3 := by
        haveI : Fintype C := Fintype.ofFinite _
        have h := orderOf_dvd_card (x := z)
        have h_card3 : Fintype.card C = 3 := by
          simpa [Nat.card_eq_fintype_card] using hcard
        rw [h_card3] at h
        exact h
      have h_dvd1 : orderOf z ∣ 1 := by
        have h_gcd := Nat.dvd_gcd h_dvd2 h_dvd3
        simpa [show Nat.gcd 2 3 = 1 from by norm_num] using h_gcd
      have h_order1 : orderOf z = 1 := by
        exact Nat.dvd_one.mp h_dvd1
      apply hz
      exact orderOf_eq_one_iff.mp h_order1
    have h_card_fintype : Fintype.card (MulAut C) = 2 := by
      calc
        Fintype.card (MulAut C) = Nat.card (MulAut C) := (Nat.card_eq_fintype_card (α := MulAut C)).symm
        _ = 2 := h_card_mulAut
    have h_all_auts : (Finset.univ : Finset (MulAut C)) = {1, inv_aut} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · exact Finset.subset_univ _
      · have h_card_goal : Finset.card (Finset.univ : Finset (MulAut C)) ≤ Finset.card ({1, inv_aut} : Finset (MulAut C)) := by
          calc
            Finset.card (Finset.univ : Finset (MulAut C)) = Fintype.card (MulAut C) := by simp
            _ = 2 := h_card_fintype
            _ ≤ Finset.card ({1, inv_aut} : Finset (MulAut C)) := by
              have h_eq : Finset.card ({1, inv_aut} : Finset (MulAut C)) = 2 := by
                rw [Finset.card_insert_eq_ite]
                have h_not_mem : 1 ∉ ({inv_aut} : Finset (MulAut C)) := by
                  intro h; apply Ne.symm h_inv_ne_one; simpa using h
                rw [if_neg h_not_mem]
                norm_num
              rw [h_eq]
        exact h_card_goal
    have h_mem : (IsCyclic.mulAutMulEquiv C).symm (-1 : (ZMod (Nat.card C))ˣ) ∈ (Finset.univ : Finset (MulAut C)) :=
      Finset.mem_univ _
    rw [h_all_auts] at h_mem
    have h_mem_cases : (IsCyclic.mulAutMulEquiv C).symm (-1 : (ZMod (Nat.card C))ˣ) = 1 ∨
      (IsCyclic.mulAutMulEquiv C).symm (-1 : (ZMod (Nat.card C))ˣ) = inv_aut := by
      simpa using h_mem
    rcases h_mem_cases with (h | h)
    · exact False.elim (h_phi_ne_one h)
    · calc
        ((IsCyclic.mulAutMulEquiv C).symm (-1 : (ZMod (Nat.card C))ˣ)) x = inv_aut x := by rw [h]
        _ = x⁻¹ := rfl

private theorem chapter2_claim16_normalizer_Z1_eq
    {G : Type*} [Group G] [Finite G]
    (Z1 R2 : Subgroup G) (s t : G)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hZ1card : Nat.card Z1 = 3)
    (hs : IsInvolution s) (ht : IsInvolution t)
    (hR2 : R2 = Subgroup.centralizer (Z1 : Set G)) :
    Subgroup.normalizer (Z1 : Set G) =
      R2 ⊔ Subgroup.closure ({s} : Set G) := by
  classical
  have hs_inv : s⁻¹ = s := hs.inv_eq_self
  have hsinv := chapter2_claim16_s_inverts_Z1 Z1 s t hZ1 hs ht
  have hs_norm : s ∈ Subgroup.normalizer (Z1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hconj : s * z * s⁻¹ = z⁻¹ := by
        simpa [rightConjugateElem, hs_inv] using hsinv z hz
      rw [hconj]
      exact Z1.inv_mem hz
    · intro hz
      have hz' : s * z * s⁻¹ ∈ Z1 := hz
      have h := hsinv (s * z * s⁻¹) hz'
      have hz_eq : z = (s * z * s⁻¹)⁻¹ := by
        calc
          z = s⁻¹ * (s * z * s⁻¹) * s := by group
          _ = (s * z * s⁻¹)⁻¹ := h
      rw [hz_eq]
      exact Z1.inv_mem hz'
  apply le_antisymm
  · intro g hg
    let gN : Subgroup.normalizer (Z1 : Set G) := ⟨g, hg⟩
    let alpha : MulAut Z1 := Z1.normalizerMonoidHom gN
    rcases chapter2_claim16_cyclic_order_three_mulAut_eq_id_or_inv hZ1card alpha with ha | ha
    · have hgC : g ∈ Subgroup.centralizer (Z1 : Set G) := by
        have hgker : gN ∈ Z1.normalizerMonoidHom.ker := by
          rw [MonoidHom.mem_ker]
          exact ha
        rw [Subgroup.normalizerMonoidHom_ker] at hgker
        exact hgker
      exact Subgroup.mem_sup_left (by simpa [hR2] using hgC)
    · have hgsC : g * s ∈ Subgroup.centralizer (Z1 : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hgInv : g * z * g⁻¹ = z⁻¹ := by
          have hz' := ha ⟨z, hz⟩
          exact congrArg Subtype.val hz'
        have hsInv : s * z * s⁻¹ = z⁻¹ := by
          simpa [rightConjugateElem, hs_inv] using hsinv z hz
        have hgInvInv : g * z⁻¹ * g⁻¹ = z := by
          calc
            g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ := by group
            _ = z := by rw [hgInv]; simp
        have hconj : (g * s) * z * (g * s)⁻¹ = z := by
          rw [mul_inv_rev]
          calc
            (g * s) * z * (s⁻¹ * g⁻¹) = g * (s * z * s⁻¹) * g⁻¹ := by group
            _ = g * z⁻¹ * g⁻¹ := by rw [hsInv]
            _ = z := hgInvInv
        have hmul := congrArg (fun w : G => w * (g * s)) hconj
        have hcomm : (g * s) * z = z * (g * s) := by
          simpa [mul_assoc] using hmul
        exact hcomm.symm
      have hsClosure : s ∈ Subgroup.closure ({s} : Set G) :=
        Subgroup.subset_closure (Set.mem_singleton s)
      have hprod : (g * s) * s ∈ R2 ⊔ Subgroup.closure ({s} : Set G) :=
        (R2 ⊔ Subgroup.closure ({s} : Set G)).mul_mem
          (Subgroup.mem_sup_left (by simpa [hR2] using hgsC))
          (Subgroup.mem_sup_right hsClosure)
      have hss : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
      exact by simpa only [mul_assoc, hss, mul_one] using hprod
  · refine sup_le ?_ ?_
    · rw [hR2]
      exact chapter2_claim16_centralizer_le_normalizer Z1
    · rw [Subgroup.closure_le]
      simpa [Set.singleton_subset_iff] using hs_norm

private theorem chapter2_claim16_claim16_commutative
    {G : Type*} [Group G] (P Sigma Z1 LV : Subgroup G)
    (hPcard : Nat.card P = 3) (hP_le_LV : P ≤ LV)
    (hcenter : LV ⊓ Subgroup.centralizer (LV : Set G) = Z1 ⊔ Sigma) :
    IsMulCommutative (Z1 ⊔ P ⊔ Sigma : Subgroup G) := by
  let A : Subgroup G := Z1 ⊔ Sigma
  have hA_le_LV : A ≤ LV := by
    change Z1 ⊔ Sigma ≤ LV
    rw [← hcenter]
    exact inf_le_left
  have hA_le_CLV : A ≤ Subgroup.centralizer (LV : Set G) := by
    change Z1 ⊔ Sigma ≤ Subgroup.centralizer (LV : Set G)
    rw [← hcenter]
    exact inf_le_right
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : IsMulCommutative P := (isCyclic_of_prime_card hPcard).isMulCommutative
  have hA_le_CA : A ≤ Subgroup.centralizer (A : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (hA_le_CLV ha) b (hA_le_LV hb))
  have hA_le_CP : A ≤ Subgroup.centralizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (hA_le_CLV ha) b (hP_le_LV hb))
  have hP_le_CA : P ≤ Subgroup.centralizer (A : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hA_le_CP ha)) p hp).symm
  have hP_le_CP : P ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hA_le_Csup : A ≤ Subgroup.centralizer ((A ⊔ P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_sup_of_le_centralizers hA_le_CA hA_le_CP
  have hP_le_Csup : P ≤ Subgroup.centralizer ((A ⊔ P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_sup_of_le_centralizers hP_le_CA hP_le_CP
  rw [show Z1 ⊔ P ⊔ Sigma = A ⊔ P by simp only [A]; ac_rfl]
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp
    (sup_le hA_le_Csup hP_le_Csup)

private theorem chapter2_claim16_z_mul_three_element_stronglyReal
    {G : Type*} [Group G] [Finite G]
    (R Z X : Subgroup G)
    (hZcard : Nat.card Z = 3) (hXcard : Nat.card X = 3)
    (hX_le_R : X ≤ R)
    (hcenter : R ⊓ Subgroup.centralizer (R : Set G) = Z)
    (hsecond : ∀ x y : G, x ∈ X → y ∈ R →
      x * y * x⁻¹ * y⁻¹ ∈ R ⊓ Subgroup.centralizer (R : Set G))
    (hX_not_le_Z : ¬ X ≤ Z)
    (hXstrong : ∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) :
    ∀ z x : G, z ∈ Z → x ∈ X → x ≠ 1 → IsStronglyReal (z * x) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro z x hz hx hxne
  have hx_not_C : x ∉ Subgroup.centralizer (R : Set G) := by
    intro hxC
    apply hX_not_le_Z
    intro u hu
    have hupow : (⟨u, hu⟩ : X) ∈ Submonoid.powers (⟨x, hx⟩ : X) :=
      mem_powers_of_prime_card hXcard (by
        intro h
        apply hxne
        exact congrArg Subtype.val h)
    rcases hupow with ⟨n, hn⟩
    have hu_eq : u = x ^ n := by
      simpa using congrArg Subtype.val hn.symm
    have hxCpow : x ^ n ∈ Subgroup.centralizer (R : Set G) :=
      (Subgroup.centralizer (R : Set G)).pow_mem hxC n
    have huCenter : u ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
      rw [hu_eq]
      exact ⟨R.pow_mem (hX_le_R hx) n, hxCpow⟩
    rw [hcenter] at huCenter
    exact huCenter
  rw [Subgroup.mem_centralizer_iff] at hx_not_C
  push Not at hx_not_C
  obtain ⟨y, hy, hyx⟩ := hx_not_C
  let c : G := x * y * x⁻¹ * y⁻¹
  have hcCenter : c ∈ R ⊓ Subgroup.centralizer (R : Set G) :=
    hsecond x y hx hy
  have hcZ : c ∈ Z := by simpa [hcenter] using hcCenter
  have hcne : c ≠ 1 := by
    intro hc
    apply hyx
    have hxy : x * y = y * x := by
      calc
        x * y = c * (y * x) := by
          dsimp [c]
          group
        _ = y * x := by rw [hc]; simp
    exact hxy.symm
  have hc_comm_y : c * y = y * c :=
    ((Subgroup.mem_centralizer_iff.mp hcCenter.2) y hy).symm
  have hconj : rightConjugateElem x y = c * x := by
    calc
      rightConjugateElem x y = y⁻¹ * x * y := rfl
      _ = (y⁻¹ * c * y) * x := by simp [c]; group
      _ = c * x := by rw [show y⁻¹ * c * y = c by
        calc
          y⁻¹ * c * y = y⁻¹ * (c * y) := by simp [mul_assoc]
          _ = y⁻¹ * (y * c) := by rw [hc_comm_y]
          _ = c := by simp]
  have hconj_c_pow : ∀ n : ℕ, rightConjugateElem (c ^ n) y = c ^ n := by
    intro n
    have hcPowCenter : c ^ n ∈ Subgroup.centralizer (R : Set G) :=
      (Subgroup.centralizer (R : Set G)).pow_mem hcCenter.2 n
    have hcomm : y * c ^ n = c ^ n * y :=
      (Subgroup.mem_centralizer_iff.mp hcPowCenter) y hy
    calc
      rightConjugateElem (c ^ n) y = y⁻¹ * c ^ n * y := rfl
      _ = c ^ n := by
        rw [show y⁻¹ * c ^ n = c ^ n * y⁻¹ by
          exact (show Commute y⁻¹ (c ^ n) from
            (show Commute y (c ^ n) from hcomm).inv_left).eq]
        simp
  have hconj_pow : ∀ n : ℕ, rightConjugateElem x (y ^ n) = c ^ n * x := by
    intro n
    induction n with
    | zero => simp [rightConjugateElem]
    | succ n ih =>
        calc
          rightConjugateElem x (y ^ (n + 1)) =
              rightConjugateElem (rightConjugateElem x (y ^ n)) y := by
                simp [rightConjugateElem, pow_succ, mul_assoc]
          _ = rightConjugateElem (c ^ n * x) y := by rw [ih]
          _ = rightConjugateElem (c ^ n) y * rightConjugateElem x y := by
                simp [rightConjugateElem, mul_assoc]
          _ = c ^ n * (c * x) := by rw [hconj_c_pow, hconj]
          _ = c ^ (n + 1) * x := by rw [pow_succ]; group
  have hzpow : (⟨z, hz⟩ : Z) ∈ Submonoid.powers (⟨c, hcZ⟩ : Z) :=
    mem_powers_of_prime_card hZcard (by
      intro h
      apply hcne
      exact congrArg Subtype.val h)
  rcases hzpow with ⟨n, hn⟩
  have hzn : z = c ^ n := by simpa using congrArg Subtype.val hn.symm
  rw [hzn, ← hconj_pow n]
  exact chapter2_claim16_stronglyReal_rightConjugateElem (y ^ n) (hXstrong x hx hxne)

private theorem chapter2_claim16_second_center
    {G : Type*} [Group G] [Finite G]
    (R A Z : Subgroup G)
    (hRp : IsPGroup 3 R)
    (hA_le_R : A ≤ R) (hZ_le_A : Z ≤ A)
    (hR_norm_A : R ≤ Subgroup.normalizer (A : Set G))
    (hcenter : R ⊓ Subgroup.centralizer (R : Set G) = Z)
    (hAcard : Nat.card A = 9) (hZcard : Nat.card Z = 3) :
    ∀ x y : G, x ∈ A → y ∈ R →
      x * y * x⁻¹ * y⁻¹ ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
  let ZR : Subgroup R := Z.subgroupOf R
  let AR : Subgroup R := A.subgroupOf R
  have hZ_le_R : Z ≤ R := hZ_le_A.trans hA_le_R
  have hZR_center : ZR = Subgroup.center R := by
    ext z
    constructor
    · intro hz
      have hzG : (z : G) ∈ Z := hz
      have hzCenter : (z : G) ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
        rw [hcenter]
        exact hzG
      rw [Subgroup.mem_center_iff]
      intro r
      exact Subtype.ext
        ((Subgroup.mem_centralizer_iff.mp hzCenter.2) r r.property)
    · intro hz
      have hzCenter : (z : G) ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
        refine ⟨z.property, ?_⟩
        change (z : G) ∈ Subgroup.centralizer (R : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hzcomm := Subgroup.mem_center_iff.mp hz ⟨r, hr⟩
        exact congrArg Subtype.val hzcomm
      rw [hcenter] at hzCenter
      exact hzCenter
  have hAR_normal : AR.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_R).mpr hR_norm_A
  letI : AR.Normal := hAR_normal
  have hZR_normal : ZR.Normal := by
    rw [hZR_center]
    infer_instance
  letI : ZR.Normal := hZR_normal
  let Abar : Subgroup (R ⧸ ZR) := AR.map (QuotientGroup.mk' ZR)
  haveI : Abar.Normal := by
    dsimp [Abar]
    infer_instance
  have hZR_le_AR : ZR ≤ AR := by
    intro z hz
    exact hZ_le_A hz
  have hARcard : Nat.card AR = 9 := by
    simpa [AR] using natCard_subgroupOf_eq A R hA_le_R |>.trans hAcard
  have hZRcard : Nat.card ZR = 3 := by
    simpa [ZR] using (natCard_subgroupOf_eq Z R hZ_le_R).trans hZcard
  have hZR_AR_card : Nat.card (ZR.subgroupOf AR) = 3 := by
    rw [natCard_subgroupOf_eq ZR AR hZR_le_AR, hZRcard]
  have hAbar_card : Nat.card Abar = 3 := by
    rw [show Abar = AR.map (QuotientGroup.mk' ZR) by rfl,
      natCard_map_mk'_eq]
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (s := ZR.subgroupOf AR)
    rw [hARcard, hZR_AR_card] at hmul
    omega
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (IsPGroup 3 R) := ⟨hRp⟩
  letI : Fact (IsPGroup 3 (R ⧸ ZR)) := ⟨hRp.to_quotient ZR⟩
  have hAbar_center : Abar ≤ Subgroup.center (R ⧸ ZR) :=
    normal_subgroup_card_eq_prime_le_center Abar hAbar_card
  intro x y hx hy
  let xR : R := ⟨x, hA_le_R hx⟩
  let yR : R := ⟨y, hy⟩
  have hxbar : QuotientGroup.mk' ZR xR ∈ Abar := by
    exact ⟨xR, hx, rfl⟩
  have hcommQ :
      QuotientGroup.mk' ZR xR * QuotientGroup.mk' ZR yR =
        QuotientGroup.mk' ZR yR * QuotientGroup.mk' ZR xR :=
    (Subgroup.mem_center_iff.mp (hAbar_center hxbar)
      (QuotientGroup.mk' ZR yR)).symm
  have hcomm_one :
      QuotientGroup.mk' ZR
          (xR * yR * xR⁻¹ * yR⁻¹) = 1 := by
    change
      QuotientGroup.mk' ZR xR * QuotientGroup.mk' ZR yR *
          (QuotientGroup.mk' ZR xR)⁻¹ * (QuotientGroup.mk' ZR yR)⁻¹ = 1
    rw [hcommQ]
    simp [mul_assoc]
  have hcomm_ZR : xR * yR * xR⁻¹ * yR⁻¹ ∈ ZR :=
    (QuotientGroup.eq_one_iff (N := ZR)
      (x := xR * yR * xR⁻¹ * yR⁻¹)).mp hcomm_one
  rw [hcenter]
  exact hcomm_ZR

private theorem chapter2_claim16_claim16_second_center
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧ W ≤ V ∧
      W = peterfalviW V (K : Set G) ∧ Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
      ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
      HypothesisB1 G V P p ∧ HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
      Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
      (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
        Z1 ⊔ P ∧
      R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
      R ⊔ Sigma ≤ R1 ∧ R2 = Subgroup.centralizer (Z1 : Set G) ∧ R1 ≤ R2)
    (h15 : L ≤ R1 ∧ (Nat.card L = 9 ∧ IsCyclic L) ∧
      (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
      V ≤ Subgroup.normalizer (L : Set G) ∧
      W ≤ Subgroup.centralizer (L : Set G) ∧
      ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
      L ⊔ V ≤ R2 ∧ Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
      (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
        Z1 ⊔ Sigma ∧
      ∀ x : G, x ∈ L ⊔ V → (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P))
    (hR1p : IsPGroup 3 R1) (hR2p : IsPGroup 3 R2)
    (hcenterR1 : R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1) :
    ∀ x y : G, x ∈ Z1 ⊔ P ⊔ Sigma → y ∈ R1 →
      x * y * x⁻¹ * y⁻¹ ∈ R1 ⊓ Subgroup.centralizer (R1 : Set G) := by
  have hPcard : Nat.card P = 3 := by simpa [hp3] using hch.B1.P_card
  have hZ1card : Nat.card Z1 = 3 := by
    rw [hZ1, Nat.card_zpowers, hst3]
  have hSigma_le_V : Sigma ≤ V := by
    rw [hSigma]
    exact inf_le_left.trans hch.section3.section2.W_le_V
  have hst_ne : s * t ≠ 1 := by
    intro h
    exact Nat.prime_three.ne_one (hst3.symm.trans (orderOf_eq_one_iff.mpr h))
  have hst_pow : (s * t) ^ 3 = 1 := by
    rw [← hst3]
    exact pow_orderOf_eq_one (s * t)
  have hst_strong : IsStronglyReal (s * t) :=
    ⟨s, t, hch.section3.2.2.1, hch.section3.section2.hA.A1.involution_t, rfl⟩
  have hZ1_not_le_Sigma : ¬ Z1 ≤ Sigma := by
    intro hle
    have hstZ1 : s * t ∈ Z1 := by rw [hZ1]; exact Subgroup.mem_zpowers (s * t)
    exact
      (chapter2_claim16_not_stronglyReal_of_mem_peterfalviV_order_three
        H D Q K V W Q0 S Q1 t s (s * t) hch.section3
        (hSigma_le_V (hle hstZ1)) hst_ne hst_pow) hst_strong
  have hZ1_disj_Sigma : Disjoint Z1 Sigma :=
    chapter2_claim16_disjoint_of_card_three_of_not_le Z1 Sigma hZ1card hZ1_not_le_Sigma
  have hP_not_le_Z1 : ¬ P ≤ Z1 := by
    intro hPZ1
    apply h15.2.2.2.2.2.1
    intro x hxP
    have hxCenterLV : x ∈ (L ⊔ V) ⊓
        Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) := by
      rw [h15.2.2.2.2.2.2.2.2.1]
      exact Subgroup.mem_sup_left (hPZ1 hxP)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp hxCenterLV.2) l (Subgroup.mem_sup_left hl)
  have hP_disj_Z1 : Disjoint P Z1 :=
    chapter2_claim16_disjoint_of_card_three_of_not_le P Z1 hPcard hP_not_le_Z1
  have hZ1_disj_P : Disjoint Z1 P := hP_disj_Z1.symm
  have hP_le_CZ1 : P ≤ Subgroup.centralizer (Z1 : Set G) := by
    intro x hxP
    have hxCenter : x ∈ (R ⊔ Sigma) ⊓
        Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) := by
      rw [h14.2.2.2.2.1]
      exact Subgroup.mem_sup_right hxP
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hxCenter.2) z
      (Subgroup.mem_sup_left ((h14.2.2.2.1 (Subgroup.mem_sup_left hz)).1))
  have hSigma_le_CZ1 : Sigma ≤ Subgroup.centralizer (Z1 : Set G) := by
    intro x hxSigma
    have hxCenter : x ∈ (L ⊔ V) ⊓
        Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) := by
      rw [h15.2.2.2.2.2.2.2.2.1]
      exact Subgroup.mem_sup_right hxSigma
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hxCenter.2) z
      (by
        have hzCenter : z ∈ (L ⊔ V) ⊓
            Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) := by
          rw [h15.2.2.2.2.2.2.2.2.1]
          exact Subgroup.mem_sup_left hz
        exact hzCenter.1)
  have hZPcard : Nat.card (Z1 ⊔ P : Subgroup G) = 9 := by
    rw [chapter2_claim16_natCard_sup_eq_mul_of_disjoint_of_le_normalizer Z1 P
      (hP_le_CZ1.trans (chapter2_claim16_centralizer_le_normalizer Z1)) hZ1_disj_P,
      hZ1card, hPcard]
  have hZSigmacard : Nat.card (Z1 ⊔ Sigma : Subgroup G) = 9 := by
    rw [chapter2_claim16_natCard_sup_eq_mul_of_disjoint_of_le_normalizer Z1 Sigma
      (hSigma_le_CZ1.trans (chapter2_claim16_centralizer_le_normalizer Z1)) hZ1_disj_Sigma,
      hZ1card, hSigmaCard]
  have hZ1_le_ZP : Z1 ≤ Z1 ⊔ P := le_sup_left
  have hZ1_le_ZSigma : Z1 ≤ Z1 ⊔ Sigma := le_sup_left
  have hZP_le_R1 : Z1 ⊔ P ≤ R1 :=
    le_trans (le_trans h14.2.2.2.1 inf_le_left)
      (le_trans le_sup_left h14.2.2.2.2.2.2.1)
  have hZP_normalizer : R1 ≤ Subgroup.normalizer ((Z1 ⊔ P : Subgroup G) : Set G) := by
    intro r hr
    have hrCenter := chapter2_claim16_normalizer_le_normalizer_centerIn (R ⊔ Sigma)
      (h14.2.2.2.2.2.1 hr)
    simpa [h14.2.2.2.2.1] using hrCenter
  let LV : Subgroup G := L ⊔ V
  have hLV_le_R2 : LV ≤ R2 := h15.2.2.2.2.2.2.1
  have hLVindex : (LV.subgroupOf R2).index = 3 := by
    have hmul := (LV.subgroupOf R2).index_mul_card
    rw [natCard_subgroupOf_eq LV R2 hLV_le_R2,
      h15.2.2.2.2.2.2.2.1] at hmul
    exact Nat.mul_right_cancel (Nat.card_pos (α := LV)) hmul
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLVnormal : (LV.subgroupOf R2).Normal :=
    chapter2_claim16_normal_of_index_eq_prime_of_isPGroup hR2p (LV.subgroupOf R2) hLVindex
  have hR2_norm_LV : R2 ≤ Subgroup.normalizer (LV : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLV_le_R2).mp hLVnormal
  have hZSigma_le_R1 : Z1 ⊔ Sigma ≤ R1 := by
    exact sup_le
      (le_sup_left.trans hZP_le_R1)
      (le_trans le_sup_right h14.2.2.2.2.2.2.1)
  have hZSigma_normalizer :
      R1 ≤ Subgroup.normalizer ((Z1 ⊔ Sigma : Subgroup G) : Set G) := by
    intro r hr
    have hrLV : (r : G) ∈ Subgroup.normalizer (LV : Set G) :=
      hR2_norm_LV (h14.2.2.2.2.2.2.2.2 hr)
    have hrCenter := chapter2_claim16_normalizer_le_normalizer_centerIn LV hrLV
    simpa [LV, h15.2.2.2.2.2.2.2.2.1] using hrCenter
  have hsecondZP := chapter2_claim16_second_center R1 (Z1 ⊔ P) Z1 hR1p
    hZP_le_R1 hZ1_le_ZP hZP_normalizer hcenterR1 hZPcard hZ1card
  have hsecondZSigma := chapter2_claim16_second_center R1 (Z1 ⊔ Sigma) Z1 hR1p
    hZSigma_le_R1 hZ1_le_ZSigma hZSigma_normalizer hcenterR1
    hZSigmacard hZ1card
  have hSigma_le_CZP : Sigma ≤ Subgroup.centralizer ((Z1 ⊔ P : Subgroup G) : Set G) := by
    intro x hxSigma
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Subgroup.sup_eq_closure] at hz
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hz
    · intro a ha
      rcases ha with haZ | haP
      · exact (Subgroup.mem_centralizer_iff.mp (hSigma_le_CZ1 hxSigma) a haZ)
      · have hxCenter : x ∈ (L ⊔ V) ⊓
            Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) := by
          rw [h15.2.2.2.2.2.2.2.2.1]
          exact Subgroup.mem_sup_right hxSigma
        exact (Subgroup.mem_centralizer_iff.mp hxCenter.2) a
          (hch.B1.P_le_V haP |> Subgroup.mem_sup_right)
    · simp
    · intro a b _ _ ha hb
      exact (show Commute (a * b) x from
        (show Commute a x from ha).mul_left (show Commute b x from hb)).eq
    · intro a _ ha
      exact (show Commute a⁻¹ x from (show Commute a x from ha).inv_left).eq
  intro x y hx hy
  have hxprod : x ∈ ((Z1 ⊔ P : Subgroup G) : Set G) * (Sigma : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Z1 ⊔ P) Sigma
      (hSigma_le_CZP.trans (chapter2_claim16_centralizer_le_normalizer (Z1 ⊔ P)))]
    exact hx
  rcases hxprod with ⟨a, ha, b, hb, rfl⟩
  have hca := hsecondZP a y ha hy
  have hcb := hsecondZSigma b y (Subgroup.mem_sup_right hb) hy
  have hcb_comm_a : (b * y * b⁻¹ * y⁻¹) * a =
      a * (b * y * b⁻¹ * y⁻¹) :=
    ((Subgroup.mem_centralizer_iff.mp hcb.2) a (hZP_le_R1 ha)).symm
  have heq :
      (a * b) * y * (a * b)⁻¹ * y⁻¹ =
        (b * y * b⁻¹ * y⁻¹) * (a * y * a⁻¹ * y⁻¹) := by
    calc
      (a * b) * y * (a * b)⁻¹ * y⁻¹ =
          a * (b * y * b⁻¹ * y⁻¹) * (y * a⁻¹ * y⁻¹) := by group
      _ = (b * y * b⁻¹ * y⁻¹) * (a * y * a⁻¹ * y⁻¹) := by
        rw [← hcb_comm_a]
        group
  rw [heq]
  exact (R1 ⊓ Subgroup.centralizer (R1 : Set G)).mul_mem hcb hca

private theorem chapter2_claim16_claim16_unique
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R1 L : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧ W ≤ V ∧
      W = peterfalviW V (K : Set G) ∧ Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
      ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
      HypothesisB1 G V P p ∧ HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t)) (hst3 : orderOf (s * t) = 3)
    (_hL_le_R1 : L ≤ R1)
    (hW_cent_L : W ≤ Subgroup.centralizer (L : Set G))
    (hP_not_cent_L : ¬ P ≤ Subgroup.centralizer (L : Set G))
    (hcenterLV : (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
      Z1 ⊔ Sigma)
    (homega : ∀ x : G, x ∈ L ⊔ V →
      (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P))
    (hA_le_R1 : Z1 ⊔ P ⊔ Sigma ≤ R1)
    (hsecond : ∀ x y : G, x ∈ Z1 ⊔ P ⊔ Sigma → y ∈ R1 →
      x * y * x⁻¹ * y⁻¹ ∈ R1 ⊓ Subgroup.centralizer (R1 : Set G))
    (hcenterR1 : R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1) :
    ∀ X : Subgroup G, X ≤ Z1 ⊔ P ⊔ Sigma → Nat.card X = 3 →
      (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) → X = Z1 := by
  classical
  let A : Subgroup G := Z1 ⊔ P ⊔ Sigma
  let B : Subgroup G := P ⊔ Sigma
  have hPcard : Nat.card P = 3 := by simpa [hp3] using hch.B1.P_card
  have hZ1card : Nat.card Z1 = 3 := by rw [hZ1, Nat.card_zpowers, hst3]
  have hSigma_le_V : Sigma ≤ V := by
    rw [hSigma]
    exact inf_le_left.trans hch.section3.section2.W_le_V
  have hB_le_V : B ≤ V := sup_le hch.B1.P_le_V hSigma_le_V
  have hB_le_LV : B ≤ L ⊔ V := hB_le_V.trans le_sup_right
  have hB_le_A : B ≤ A := by
    dsimp [A, B]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hZ1_le_A : Z1 ≤ A := le_sup_left.trans le_sup_left
  have hAcomm : IsMulCommutative A := by
    simpa [A] using chapter2_claim16_claim16_commutative P Sigma Z1 (L ⊔ V)
      hPcard (hch.B1.P_le_V.trans le_sup_right) hcenterLV
  letI : IsMulCommutative A := hAcomm
  have hA_le_CA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAcomm
  have hZstrong := chapter2_claim16_Z1_stronglyReal Z1 s t hZ1 hst3
    hch.section3.2.2.1 hch.section3.section2.hA.A1.involution_t
  intro X hX_le hXcard hXstrong
  by_cases hX_le_Z1 : X ≤ Z1
  · exact Subgroup.eq_of_le_of_card_ge hX_le_Z1 (by rw [hXcard, hZ1card])
  have hXdisjZ1 : Disjoint X Z1 :=
    chapter2_claim16_disjoint_of_card_three_of_not_le X Z1 hXcard hX_le_Z1
  let E : Subgroup G := Z1 ⊔ X
  have hX_le_CZ1 : X ≤ Subgroup.centralizer (Z1 : Set G) := by
    intro x hx
    have hxA : x ∈ A := hX_le hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hA_le_CA hxA)) z (hZ1_le_A hz)
  have hEcard : Nat.card E = 9 := by
    dsimp [E]
    rw [chapter2_claim16_natCard_sup_eq_mul_of_disjoint_of_le_normalizer Z1 X
      (hX_le_CZ1.trans (chapter2_claim16_centralizer_le_normalizer Z1)) hXdisjZ1.symm,
      hZ1card, hXcard]
  have hE_le_A : E ≤ A := sup_le hZ1_le_A hX_le
  have hEstrong : ∀ e : G, e ∈ E → e ≠ 1 → IsStronglyReal e := by
    intro e he hene
    have hX_le_NZ1 : X ≤ Subgroup.normalizer (Z1 : Set G) :=
      hX_le_CZ1.trans (chapter2_claim16_centralizer_le_normalizer Z1)
    have heprod : e ∈ (Z1 : Set G) * (X : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Z1 X hX_le_NZ1]
      exact he
    rcases heprod with ⟨z, hz, x, hx, rfl⟩
    by_cases hxone : x = 1
    · subst x
      simpa using hZstrong z hz (by simpa using hene)
    · exact chapter2_claim16_z_mul_three_element_stronglyReal R1 Z1 X hZ1card hXcard
        (hX_le.trans hA_le_R1) hcenterR1
        (fun x y hx hy => hsecond x y (hX_le hx) hy)
        hX_le_Z1 hXstrong z x hz hx hxone
  have hP_not_le_Sigma : ¬ P ≤ Sigma := by
    intro hP_le
    apply hP_not_cent_L
    exact hP_le.trans ((by rw [hSigma]; exact inf_le_left : Sigma ≤ W).trans hW_cent_L)
  have hPdisjSigma : Disjoint P Sigma :=
    chapter2_claim16_disjoint_of_card_three_of_not_le P Sigma hPcard hP_not_le_Sigma
  have hSigma_le_CP : Sigma ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    have hxA : x ∈ A := Subgroup.mem_sup_right hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hA_le_CA hxA)) y
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))
  have hBcard : Nat.card B = 9 := by
    dsimp [B]
    rw [chapter2_claim16_natCard_sup_eq_mul_of_disjoint_of_le_normalizer P Sigma
      (hSigma_le_CP.trans (chapter2_claim16_centralizer_le_normalizer P)) hPdisjSigma,
      hPcard, hSigmaCard]
  have hBpow : ∀ b : G, b ∈ B → b ^ 3 = 1 := by
    intro b hb
    apply (homega b (hB_le_LV hb)).mpr
    rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl]
    exact hB_le_A hb
  have hZ1disjB : Disjoint Z1 B := by
    rw [disjoint_iff_inf_le]
    intro z hz
    by_contra hzne
    have hzV : z ∈ V := hB_le_V hz.2
    have hzpow : z ^ 3 = 1 := hBpow z hz.2
    exact (chapter2_claim16_not_stronglyReal_of_mem_peterfalviV_order_three
      H D Q K V W Q0 S Q1 t s z hch.section3 hzV hzne hzpow)
      (hZstrong z hz.1 hzne)
  have hB_le_CZ1 : B ≤ Subgroup.centralizer (Z1 : Set G) := by
    intro b hb
    have hbA := hB_le_A hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hA_le_CA hbA)) z
      (hZ1_le_A hz)
  have hAcard : Nat.card A = 27 := by
    have hZA : Z1 ⊔ B = A := by
      dsimp [A, B]
      ac_rfl
    rw [← hZA, chapter2_claim16_natCard_sup_eq_mul_of_disjoint_of_le_normalizer Z1 B
      (hB_le_CZ1.trans (chapter2_claim16_centralizer_le_normalizer Z1)) hZ1disjB,
      hZ1card, hBcard]
  have hB_le_CE : B ≤ Subgroup.centralizer (E : Set G) := by
    intro b hb
    have hbA := hB_le_A hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hA_le_CA hbA)) e (hE_le_A he)
  have hnotdisj : ¬ Disjoint E B := by
    intro hdisj
    have hsupcard : Nat.card (E ⊔ B : Subgroup G) = 81 := by
      rw [chapter2_claim16_natCard_sup_eq_mul_of_disjoint_of_le_normalizer E B
        (hB_le_CE.trans (chapter2_claim16_centralizer_le_normalizer E)) hdisj,
        hEcard, hBcard]
    have hsup_le : E ⊔ B ≤ A := sup_le hE_le_A hB_le_A
    have hle := Subgroup.card_le_of_le hsup_le
    rw [hsupcard, hAcard] at hle
    omega
  have hInf_ne : E ⊓ B ≠ ⊥ := by
    intro hInf
    apply hnotdisj
    rw [disjoint_iff_inf_le, hInf]
  obtain ⟨q, hqne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hInf_ne
  have hqE : (q : G) ∈ E := q.property.1
  have hqB : (q : G) ∈ B := q.property.2
  have hqStrong : IsStronglyReal (q : G) := hEstrong q hqE (by
    intro h
    apply hqne
    exact Subtype.ext h)
  exact False.elim ((chapter2_claim16_not_stronglyReal_of_mem_peterfalviV_order_three
    H D Q K V W Q0 S Q1 t s (q : G) hch.section3 (hB_le_V hqB)
    (by intro h; apply hqne; exact Subtype.ext h) (hBpow q hqB)) hqStrong)


private theorem chapter2_claim16_normalizer_ZPSigma_eq
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R1 R2 L : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧ W ≤ V ∧
      W = peterfalviW V (K : Set G) ∧ Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
      ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
      HypothesisB1 G V P p ∧ HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (h15 : L ≤ R1 ∧
      (Nat.card L = 9 ∧ IsCyclic L) ∧
      (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
      V ≤ Subgroup.normalizer (L : Set G) ∧
      W ≤ Subgroup.centralizer (L : Set G) ∧
      ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
      L ⊔ V ≤ R2 ∧ Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
      (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
        Z1 ⊔ Sigma ∧
      ∀ x : G, x ∈ L ⊔ V → (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P))
    (hR2p : IsPGroup 3 R2)
    (huniq : ∀ X : Subgroup G, X ≤ Z1 ⊔ P ⊔ Sigma →
      Nat.card X = 3 →
      (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) → X = Z1)
    (hnormZ1 :
      Subgroup.normalizer (Z1 : Set G) =
        R2 ⊔ Subgroup.closure ({s} : Set G)) :
    Subgroup.normalizer ((Z1 ⊔ P ⊔ Sigma : Subgroup G) : Set G) =
      Subgroup.normalizer (Z1 : Set G) := by
  classical
  let A : Subgroup G := Z1 ⊔ P ⊔ Sigma
  let LV : Subgroup G := L ⊔ V
  have hZ1card : Nat.card Z1 = 3 := by
    rw [hZ1, Nat.card_zpowers, hst3]
  have hZstrong := chapter2_claim16_Z1_stronglyReal Z1 s t hZ1 hst3
    hch.section3.2.2.1 hch.section3.section2.hA.A1.involution_t
  have hZ1_le_A : Z1 ≤ A := le_sup_left.trans le_sup_left
  have hforward :
      Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (Z1 : Set G) := by
    intro g hg
    let X : Subgroup G := rightConjugate Z1 g
    have hX_le_A : X ≤ A := by
      intro x hx
      change x ∈ rightConjugate Z1 g at hx
      rcases hx with ⟨z, hz, rfl⟩
      have hginv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
        (Subgroup.normalizer (A : Set G)).inv_mem hg
      exact (Subgroup.mem_normalizer_iff.mp hginv z).1 (hZ1_le_A hz)
    have hXcard : Nat.card X = 3 := by
      dsimp [X]
      rw [chapter2_claim16_natCard_rightConjugate, hZ1card]
    have hXstrong :
        ∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x := by
      intro x hx hxne
      change x ∈ rightConjugate Z1 g at hx
      rcases hx with ⟨z, hz, rfl⟩
      have hzne : z ≠ 1 := by
        intro hz1
        subst z
        simp at hxne
      simpa [rightConjugateElem, MulAut.conj_apply] using
        (chapter2_claim16_stronglyReal_rightConjugateElem g (hZstrong z hz hzne))
    have hXeq : X = Z1 := huniq X (by simpa [A] using hX_le_A) hXcard hXstrong
    exact chapter2_claim16_mem_normalizer_of_rightConjugate_eq_self (by simpa [X] using hXeq)
  have hZS_le_LV : Z1 ⊔ Sigma ≤ LV := by
    dsimp [LV]
    rw [← h15.2.2.2.2.2.2.2.2.1]
    exact inf_le_left
  have hA_le_LV : A ≤ LV := by
    have hP_le_LV : P ≤ LV := hch.B1.P_le_V.trans le_sup_right
    rw [show A = (Z1 ⊔ Sigma) ⊔ P by dsimp [A]; ac_rfl]
    exact sup_le hZS_le_LV hP_le_LV
  have hLV_le_R2 : LV ≤ R2 := h15.2.2.2.2.2.2.1
  have hLVindex : (LV.subgroupOf R2).index = 3 := by
    have hmul := (LV.subgroupOf R2).index_mul_card
    rw [natCard_subgroupOf_eq LV R2 hLV_le_R2,
      h15.2.2.2.2.2.2.2.1] at hmul
    exact Nat.mul_right_cancel (Nat.card_pos (α := LV)) hmul
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLVnormal : (LV.subgroupOf R2).Normal :=
    chapter2_claim16_normal_of_index_eq_prime_of_isPGroup hR2p (LV.subgroupOf R2) hLVindex
  have hR2_norm_LV : R2 ≤ Subgroup.normalizer (LV : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLV_le_R2).mp hLVnormal
  have hR2_norm_A : R2 ≤ Subgroup.normalizer (A : Set G) := by
    intro r hr
    have hrLV := hR2_norm_LV hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxLV : x ∈ LV := hA_le_LV hx
      have hconjLV : r * x * r⁻¹ ∈ LV :=
        (Subgroup.mem_normalizer_iff.mp hrLV x).1 hxLV
      have hxpow : x ^ 3 = 1 := by
        apply (h15.2.2.2.2.2.2.2.2.2 x hxLV).mpr
        rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl]
        exact hx
      have hconjpow : (r * x * r⁻¹) ^ 3 = 1 := by
        calc
          (r * x * r⁻¹) ^ 3 = r * x ^ 3 * r⁻¹ := by
            simpa [MulAut.conj_apply] using
              (map_pow (MulAut.conj r) x 3).symm
          _ = 1 := by rw [hxpow]; simp
      have hmem := (h15.2.2.2.2.2.2.2.2.2 (r * x * r⁻¹) hconjLV).mp hconjpow
      rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl] at hmem
      exact hmem
    · intro hx
      have hconjLV : r * x * r⁻¹ ∈ LV := hA_le_LV hx
      have hxLV : x ∈ LV :=
        (Subgroup.mem_normalizer_iff.mp hrLV x).mpr hconjLV
      have hconjpow : (r * x * r⁻¹) ^ 3 = 1 := by
        apply (h15.2.2.2.2.2.2.2.2.2 (r * x * r⁻¹) hconjLV).mpr
        rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl]
        exact hx
      have hmapPow : (r * x * r⁻¹) ^ 3 = r * x ^ 3 * r⁻¹ := by
        simpa [MulAut.conj_apply] using
          (map_pow (MulAut.conj r) x 3).symm
      have hconj_xpow : r * x ^ 3 * r⁻¹ = 1 := hmapPow.symm.trans hconjpow
      have hxpow : x ^ 3 = 1 := by
        have h := congrArg (fun z : G => r⁻¹ * z * r) hconj_xpow
        simpa [mul_assoc] using h
      have hmem := (h15.2.2.2.2.2.2.2.2.2 x hxLV).mp hxpow
      rw [show Z1 ⊔ Sigma ⊔ P = A by dsimp [A]; ac_rfl] at hmem
      exact hmem
  have hs_norm_Z1 : s ∈ Subgroup.normalizer (Z1 : Set G) := by
    rw [hnormZ1]
    exact Subgroup.mem_sup_right
      (Subgroup.subset_closure (Set.mem_singleton s))
  have hV_eq : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    calc
      V = peterfalviV D t := hch.section3.section2.V_eq
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
        (proposition_5 H D Q t s hch.section3.section2.hA.A1
          hch.section3.2.1 hch.section3.2.2.1 hch.section3.2.2.2).1
  have hsC_V : s ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvCs : v ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [hV_eq] at hv
      exact hv.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hvCs
  have hs_norm_P : s ∈ Subgroup.normalizer (P : Set G) :=
    chapter2_claim16_centralizer_le_normalizer P (by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hsC_V) x (hch.B1.P_le_V hx))
  have hSigma_le_V : Sigma ≤ V := by
    rw [hSigma]
    exact inf_le_left.trans hch.section3.section2.W_le_V
  have hs_norm_Sigma : s ∈ Subgroup.normalizer (Sigma : Set G) :=
    chapter2_claim16_centralizer_le_normalizer Sigma (by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hsC_V) x (hSigma_le_V hx))
  have hs_norm_A : s ∈ Subgroup.normalizer (A : Set G) := by
    dsimp [A]
    exact chapter2_claim16_mem_normalizer_sup
      (chapter2_claim16_mem_normalizer_sup hs_norm_Z1 hs_norm_P) hs_norm_Sigma
  have hreverse :
      Subgroup.normalizer (Z1 : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hnormZ1]
    refine sup_le hR2_norm_A ?_
    rw [Subgroup.closure_le]
    simpa [Set.singleton_subset_iff] using hs_norm_A
  exact le_antisymm (by simpa [A] using hforward) (by simpa [A] using hreverse)


/-- Peterfalvi, Part II, Chapter II, Claim (16). -/
public theorem claim_16
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
      (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧ W ≤ V ∧
      W = peterfalviW V (K : Set G) ∧ Q0 ≤ Q ∧
      (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
      S ≤ Q ∧ Q1 ≤ Q ∧
      (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
      Odd (Nat.card Q1) ∧ Disjoint S Q1 ∧
      (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
      S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
      ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
      HypothesisB1 G V P p ∧ HypothesisB2 G p))
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
      Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
      (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
        Z1 ⊔ P ∧
      R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
      R ⊔ Sigma ≤ R1 ∧ R2 = Subgroup.centralizer (Z1 : Set G) ∧ R1 ≤ R2)
    (h15 : L ≤ R1 ∧ (Nat.card L = 9 ∧ IsCyclic L) ∧
      (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
      V ≤ Subgroup.normalizer (L : Set G) ∧
      W ≤ Subgroup.centralizer (L : Set G) ∧
      ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
      L ⊔ V ≤ R2 ∧ Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
      (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
        Z1 ⊔ Sigma ∧
      ∀ x : G, x ∈ L ⊔ V → (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hR1p : IsPGroup 3 R1) (hR2p : IsPGroup 3 R2)
    (hcenterR1 : R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1) :
    Z1 ⊔ P ⊔ Sigma ≤ R1 ∧
      (∀ x y : G, x ∈ Z1 ⊔ P ⊔ Sigma → y ∈ R1 →
        x * y * x⁻¹ * y⁻¹ ∈
          R1 ⊓ Subgroup.centralizer (R1 : Set G)) ∧
      (∀ X : Subgroup G,
        X ≤ Z1 ⊔ P ⊔ Sigma →
          Nat.card X = 3 →
            (∀ x : G, x ∈ X → x ≠ 1 → IsStronglyReal x) →
              X = Z1) ∧
        Subgroup.normalizer ((Z1 ⊔ P ⊔ Sigma : Subgroup G) : Set G) =
          Subgroup.normalizer (Z1 : Set G) ∧
          Subgroup.normalizer (Z1 : Set G) =
            R2 ⊔ Subgroup.closure ({s} : Set G) := by
  have hZPSigma_le : Z1 ⊔ P ⊔ Sigma ≤ R1 := by
    refine sup_le ?_ ?_
    · exact
        le_trans (le_trans h14.2.2.2.1 inf_le_left)
          (le_trans le_sup_left h14.2.2.2.2.2.2.1)
    · exact le_trans le_sup_right h14.2.2.2.2.2.2.1
  have hsecond :=
    chapter2_claim16_claim16_second_center H D Q K V W Q0 S Q1 P Sigma Z1
      R R1 R2 L t s p hch hSigma hp3 hSigmaCard hZ1 hst3 h14 h15
      hR1p hR2p hcenterR1
  have hunique :=
    chapter2_claim16_claim16_unique H D Q K V W Q0 S Q1 P Sigma Z1 R1 L
      t s p hch hSigma hp3 hSigmaCard hZ1 hst3 h15.1
      h15.2.2.2.2.1 h15.2.2.2.2.2.1
      h15.2.2.2.2.2.2.2.2.1 h15.2.2.2.2.2.2.2.2.2
      hZPSigma_le hsecond hcenterR1
  have hZ1card : Nat.card Z1 = 3 := by
    rw [hZ1, Nat.card_zpowers, hst3]
  have hnormZ1 :=
    chapter2_claim16_normalizer_Z1_eq Z1 R2 s t hZ1 hZ1card
      hch.section3.2.2.1 hch.section3.section2.hA.A1.involution_t
      h14.2.2.2.2.2.2.2.1
  have hnormSigma :=
    chapter2_claim16_normalizer_ZPSigma_eq H D Q K V W Q0 S Q1 P Sigma Z1
      R1 R2 L t s p hch hSigma hZ1 hst3 h15 hR2p hunique hnormZ1
  exact ⟨hZPSigma_le, hsecond, hunique, hnormSigma, hnormZ1⟩


end CFSG.BenderSuzuki.PFchapter2
