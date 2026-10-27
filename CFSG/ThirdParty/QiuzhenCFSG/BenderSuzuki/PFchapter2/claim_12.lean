module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_10
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.theorem_14_4_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_3
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

universe u v

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open scoped Pointwise commutatorElement

/-!
# Peterfalvi, Part II, Chapter II, Claim (12)
-/

private theorem claim_12_B2_excludes_normal_index_p
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hN : ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p) :
    False := by
  rcases hN with ⟨N, hNnormal, hNindex⟩
  exact hch.B2 N hNnormal hNindex

/-- Transport a local index-`p` quotient across the Hall residual quotient
equivalence and lift it to a normal index-`p` subgroup of the ambient group. -/
private theorem chapter2_claim12_global_index_from_local_hall_data
    {G H A : Type*} [Group G] [Finite G] [Group H] [Group A]
    (p : ℕ) (K : Subgroup G) [K.Normal] (L : Subgroup H) [L.Normal]
    (hquot : Nonempty ((G ⧸ K) ≃* (H ⧸ L)))
    (φ : (H ⧸ L) →* A) (hφ : Function.Surjective φ)
    (hcard : Nat.card A = p) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p := by
  classical
  let e : (G ⧸ K) ≃* (H ⧸ L) := Classical.choice hquot
  let ψ : G →* A :=
    φ.comp (e.toMonoidHom.comp (QuotientGroup.mk' K))
  have hψ : Function.Surjective ψ :=
    hφ.comp (e.surjective.comp (QuotientGroup.mk'_surjective K))
  refine ⟨ψ.ker, inferInstance, ?_⟩
  exact
    (Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv).trans hcard

/-- A normal subgroup with quotient cardinality coprime to every generator of
Hall's `p`-residual contains that residual. -/
private theorem chapter2_claim12_hallPResidual_le_of_quotient_card_eq
    {H : Type*} [Group H] (p : ℕ) (M : Subgroup H) [M.Normal]
    (hcard : Nat.card (H ⧸ M) = p) :
    External.hallPResidual p H ≤ M := by
  change Subgroup.closure {x : H | Nat.Coprime p (orderOf x)} ≤ M
  rw [Subgroup.closure_le]
  intro x hx
  change Nat.Coprime p (orderOf x) at hx
  let q : H →* H ⧸ M := QuotientGroup.mk' M
  have hq_dvd_p : orderOf (q x) ∣ p := by
    rw [← hcard]
    exact orderOf_dvd_natCard (q x)
  have hq_dvd_x : orderOf (q x) ∣ orderOf x :=
    orderOf_map_dvd q x
  have hq_dvd_one : orderOf (q x) ∣ 1 := by
    rw [← hx.gcd_eq_one]
    exact Nat.dvd_gcd hq_dvd_p hq_dvd_x
  have hq_order : orderOf (q x) = 1 := Nat.dvd_one.mp hq_dvd_one
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hq_order)

/-- A finite group of order `p^3` has nilpotency class at most two, hence
reaches the Hall--Wielandt upper-central-series bound for odd `p`. -/
private theorem chapter2_claim12_upperCentralSeries_of_card_prime_cube
    {P : Type*} [Group P] [Finite P] (p : ℕ) [Fact (Nat.Prime p)]
    (hcard : Nat.card P = p ^ 3) (hp3 : 3 ≤ p) :
    (⊤ : Subgroup P) ≤ Subgroup.upperCentralSeries P (p - 1) := by
  have hPp : IsPGroup p P := IsPGroup.of_card hcard
  obtain ⟨k, hkpos, hcenterCard⟩ :=
    IsPGroup.card_center_eq_prime_pow hcard (by norm_num)
  have hk_dvd : p ^ k ∣ p ^ 3 := by
    rw [← hcenterCard, ← hcard]
    simpa using
      (Subgroup.card_dvd_of_le (show Subgroup.center P ≤ (⊤ : Subgroup P) from le_top))
  have hk_le : k ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right
      ((Fact.out : Nat.Prime p).one_lt)).mp hk_dvd
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  let Z : Subgroup P := Subgroup.center P
  let Q := P ⧸ Z
  have hQcard : Nat.card Q = p ^ (3 - k) := by
    have hmul := Z.card_mul_index
    rw [hcenterCard, hcard] at hmul
    have hindex : Z.index = p ^ (3 - k) := by
      apply Nat.eq_of_mul_eq_mul_left
        (pow_pos ((Fact.out : Nat.Prime p).pos) k)
      calc
        p ^ k * Z.index = p ^ 3 := hmul
        _ = p ^ k * p ^ (3 - k) := by
          rw [← pow_add, Nat.add_sub_of_le hk_le]
    calc
      Nat.card Q = Z.index := (Subgroup.index_eq_card Z).symm
      _ = p ^ (3 - k) := hindex
  have hQcomm : IsMulCommutative Q := by
    rcases hkCases with hk1 | hk23
    · have hQcard2 : Nat.card Q = p ^ 2 := by simpa [hk1] using hQcard
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hQcard2
    · rcases hk23 with hk2 | hk3
      · have hQcard1 : Nat.card Q = p := by simpa [hk2] using hQcard
        exact (isCyclic_of_prime_card hQcard1).isMulCommutative
      · have hQcardOne : Nat.card Q = 1 := by simpa [hk3] using hQcard
        have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hQcardOne).1
        exact IsMulCommutative.of_comm fun _ _ => Subsingleton.elim _ _
  have hcomm_le : _root_.commutator P ≤ Subgroup.center P :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hQcomm
  have hlowerTwo : Subgroup.lowerCentralSeries (⊤ : Subgroup P) 2 = ⊥ := by
    apply Subgroup.lowerCentralSeries_succ_eq_bot (G := P) (n := 1)
    simpa [_root_.commutator_def] using hcomm_le
  let : Group.IsNilpotent P := hPp.isNilpotent
  have hclass : Group.nilpotencyClass P ≤ 2 :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hlowerTwo
  have hupperTwo : Subgroup.upperCentralSeries P 2 = ⊤ :=
    Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr hclass
  have htwo_le : 2 ≤ p - 1 := by omega
  rw [← hupperTwo]
  exact Subgroup.upperCentralSeries_mono P htwo_le

/-- Hall--Wielandt for a Sylow subgroup that reaches the required term of
its upper central series.  A Sylow subgroup is weakly closed in itself. -/
private theorem chapter2_claim12_hallWielandt_of_upperCentralSeries
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact (Nat.Prime p)]
    (P : Sylow p G) (H : Subgroup G)
    (hH : H = Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hupper : (⊤ : Subgroup P) ≤ Subgroup.upperCentralSeries P (p - 1)) :
    letI : (External.hallPResidual p G).Normal :=
      External.hallPResidual_normal p G
    letI : (External.hallPResidual p H).Normal :=
      External.hallPResidual_normal p H
    Nonempty ((G ⧸ External.hallPResidual p G) ≃*
      (H ⧸ External.hallPResidual p H)) := by
  classical
  have hweak : External.WeaklyClosedIn (P : Subgroup G) (P : Subgroup G) := by
    refine ⟨le_rfl, ?_⟩
    intro g hg
    apply Subgroup.eq_of_le_of_card_ge hg
    rw [rightConjugate]
    exact (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).ge
  have hupper' :
      (P : Subgroup G).subgroupOf (P : Subgroup G) ≤
        Subgroup.upperCentralSeries P (p - 1) := by
    simpa using hupper
  exact (External.hallWielandt_residual_intersection
    p P (P : Subgroup G) H hH hweak (Or.inr (Or.inr hupper'))).2

private theorem chapter2_claim12_normal_of_index_eq_prime_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hGp : IsPGroup p G) (A : Subgroup G) (hindex : A.index = p) :
    A.Normal := by
  rcases hGp.exists_card_eq with ⟨n, hGcard⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    have hcard_one : Nat.card G = 1 := by simpa [hn] using hGcard
    have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard_one).1
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

private lemma chapter2_claim12_normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (K.map H.subtype : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, g.property⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

private theorem chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
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

private theorem chapter2_claim12_stronglyReal_rightConjugateElem
    {G : Type*} [Group G] {x : G} (g : G) (hx : IsStronglyReal x) :
    IsStronglyReal (rightConjugateElem x g) := by
  rcases hx with ⟨u, v, hu, hv, huv⟩
  refine ⟨rightConjugateElem u g, rightConjugateElem v g,
    isInvolution_rightConjugateElem hu, isInvolution_rightConjugateElem hv, ?_⟩
  calc
    rightConjugateElem x g = rightConjugateElem (u * v) g := by rw [huv]
    _ = rightConjugateElem u g * rightConjugateElem v g := by
      simp [rightConjugateElem, mul_assoc]

private theorem chapter2_claim12_stronglyReal_of_inverted_by_involution
    {G : Type*} [Group G] {x s : G} (hs : IsInvolution s)
    (hx2 : x ^ 2 ≠ 1) (hinv : rightConjugateElem x s = x⁻¹) :
    IsStronglyReal x := by
  have hsInv : s⁻¹ = s := hs.inv_eq_self
  have hsSq : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
  have hsxs : s * x * s = x⁻¹ := by
    simpa [rightConjugateElem, hsInv, mul_assoc] using hinv
  have hsxSq : (s * x) ^ 2 = 1 := by
    calc
      (s * x) ^ 2 = s * x * s * x := by simp [pow_two, mul_assoc]
      _ = x⁻¹ * x := by rw [hsxs]
      _ = 1 := by simp
  have hsxNe : s * x ≠ 1 := by
    intro hsx
    have hxEq : x = s⁻¹ := by
      calc
        x = s⁻¹ * (s * x) := by simp
        _ = s⁻¹ := by rw [hsx, mul_one]
    apply hx2
    rw [hxEq, hsInv]
    exact hs.sq_eq_one
  refine ⟨s, s * x, hs, ⟨hsxNe, hsxSq⟩, ?_⟩
  rw [← mul_assoc, hsSq, one_mul]

private theorem chapter2_claim12_not_stronglyReal_of_mem_peterfalviV
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
    (hxV : x ∈ V) (hx2 : x ^ 2 ≠ 1) :
    ¬ IsStronglyReal x := by
  intro hxstrong
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

/-- The normalizer orbit in source lines 334--344 has cardinality `p^m`.
Comparing its `p`-part with case (10.1) forces `m = 1`. -/
private theorem chapter2_claim12_orbit_forces_m_eq_one
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P R T : Subgroup G) (t s : G) (p m : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = peterfalviV D t ∧
        W ≤ V ∧
          W = peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  HypothesisB1 G V P p ∧ HypothesisB2 G p))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m)
    (hR : R = T ⊔ P ∧
        Disjoint T P ∧
          T ≤ Subgroup.centralizer (P : Set G) ∧
            (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
              W ⊓ Subgroup.centralizer (P : Set G)) ≤
                Subgroup.normalizer (T : Set G) ∧
              Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
                ∀ A B : Subgroup G,
                  A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                      ∃! c : G,
                        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                          B = rightConjugate A c)
    (hT_inverted : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    (hCaseOne :
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
        Nat.card R = p ^ (m + 1) ∧
          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
            p ^ m ∧
          ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
            (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
              R.subgroupOf (Subgroup.centralizer (P : Set G)))
    (hcase10_1 :
      ∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧
        Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u) :
    m = 1 ∧
      Nat.card (Subgroup.normalizer (R : Set G)) =
        p ^ m * Nat.card (Subgroup.centralizer (P : Set G)) ∧
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (T : Set G) := by
  classical
  let : Fact (Nat.Prime p) := ⟨hch.B1.p_prime⟩
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let NR : Subgroup G := Subgroup.normalizer (R : Set G)
  let CQ : Subgroup G := Q ⊓ Subgroup.centralizer (P : Set G)
  rcases hCaseOne with ⟨hC_le_NR, hRcard, hCQcard, RC, hRC⟩
  rcases hcase10_1 with ⟨_k, u, _hk, hGcard, hu⟩
  have hP_le_C : P ≤ C := by
    let : IsMulCommutative P :=
      (isCyclic_of_prime_card hch.B1.P_card).isMulCommutative
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hP_le_R : P ≤ R := by
    rw [hR.1]
    exact le_sup_right
  have hR_le_C : R ≤ C := by
    rw [hR.1]
    exact sup_le hR.2.2.1 hP_le_C
  have hRp : IsPGroup p R := IsPGroup.of_card hRcard
  have hRindex : R.index = p * u := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hch.B1.p_prime.pos (m + 1))
    calc
      p ^ (m + 1) * R.index = Nat.card R * R.index := by rw [hRcard]
      _ = Nat.card G := R.card_mul_index
      _ = p ^ (m + 2) * u := hGcard
      _ = p ^ (m + 1) * (p * u) := by rw [pow_succ']; ac_rfl
  have hp_dvd_Rindex : p ∣ R.index := by rw [hRindex]; exact dvd_mul_right p u
  have hNR_not_le_C : ¬ NR ≤ C := by
    intro hNR_le_C
    obtain ⟨RG, hRG⟩ :=
      claim_11_sylow_of_subgroupOf_sylow_of_normalizer_le
        R C hRp RC hRC hNR_le_C
    have hnot : ¬ p ∣ R.index := by
      simpa [hRG] using RG.not_dvd_index
    exact hnot hp_dvd_Rindex
  obtain ⟨g, hgNR, hgC⟩ :=
    SetLike.exists_of_lt (show C < NR from ⟨hC_le_NR, hNR_not_le_C⟩)
  let gNR : NR := ⟨g, hgNR⟩
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let : MulAction NR (Subgroup G) := MulAction.compHom _ NR.subtype
  let : Fintype NR := Fintype.ofFinite NR
  have hstabG :
      MulAction.stabilizer G P = Subgroup.normalizer (P : Set G) := by
    ext a
    change a • P = P ↔ a ∈ Subgroup.normalizer (P : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer P),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact
      forall_congr' fun x =>
        iff_congr Iff.rfl
          ⟨fun ⟨y, hy, heq⟩ => heq ▸ by simpa [mul_assoc] using hy,
            fun hx => ⟨(MulAut.conj a)⁻¹ x, hx,
              MulAut.apply_inv_self G (MulAut.conj a) x⟩⟩
  have hPodd : Odd (Nat.card P) := by
    have hP_le_D : P ≤ D := by
      refine hch.B1.P_le_V.trans ?_
      rw [hch.section3.section2.V_eq]
      exact inf_le_left
    exact hch.section3.section2.hA.A1.D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le hP_le_D)
  have hconj_data (a : NR) :
      let A : Subgroup G := a • P
      A ≤ R ∧ Nat.card A = p ∧ ¬ A ≤ T := by
    dsimp only
    have hA_le_R : a • P ≤ R := by
      intro x hx
      change x ∈ P.map (MulAut.conj (a : G)).toMonoidHom at hx
      rcases hx with ⟨y, hyP, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp a.property y).1 (hP_le_R hyP)
    have hAcard : Nat.card (a • P : Subgroup G) = p := by
      change Nat.card (P.map (MulAut.conj (a : G)).toMonoidHom) = p
      rw [Subgroup.card_map_of_injective (MulAut.conj (a : G)).injective,
        hch.B1.P_card]
    refine ⟨hA_le_R, hAcard, ?_⟩
    intro hA_le_T
    have hAne : (a • P : Subgroup G) ≠ ⊥ := by
      intro hbot
      have hcardOne : Nat.card (a • P : Subgroup G) = 1 := by simp [hbot]
      exact hch.B1.p_prime.ne_one (hAcard ▸ hcardOne)
    obtain ⟨xA, hxAne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    let x : G := xA
    have hxA : x ∈ (a • P : Subgroup G) := xA.property
    have hxne : x ≠ 1 := by
      intro hxone
      apply hxAne
      apply Subtype.ext
      exact hxone
    have hxT : x ∈ T := hA_le_T hxA
    have hAodd : Odd (Nat.card (a • P : Subgroup G)) := by
      simpa [hAcard, hch.B1.P_card] using hPodd
    have hx2 : x ^ 2 ≠ 1 := by
      intro hxSq
      exact (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
        (a • P : Subgroup G) hAodd hxA) ⟨hxne, hxSq⟩
    have hxstrong : IsStronglyReal x :=
      chapter2_claim12_stronglyReal_of_inverted_by_involution
        hch.section3.2.2.1 hx2 (hT_inverted x hxT)
    change x ∈ P.map (MulAut.conj (a : G)).toMonoidHom at hxA
    rcases hxA with ⟨y, hyP, hyx⟩
    have hyne : y ≠ 1 := by
      intro hyone
      apply hxne
      rw [← hyx, hyone]
      simp
    have hy2 : y ^ 2 ≠ 1 := by
      intro hySq
      exact (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
        P hPodd hyP) ⟨hyne, hySq⟩
    have hystrong : IsStronglyReal y := by
      have hback : rightConjugateElem x (a : G) = y := by
        rw [← hyx]
        simp [rightConjugateElem, MulAut.conj_apply, mul_assoc]
      simpa [hback] using
        chapter2_claim12_stronglyReal_rightConjugateElem (a : G) hxstrong
    exact (chapter2_claim12_not_stronglyReal_of_mem_peterfalviV
      H D Q K V W Q0 S Q1 t s y hch.section3
        (hch.B1.P_le_V hyP) hy2) hystrong
  let P1 : Subgroup G := gNR • P
  have hP1data := hconj_data gNR
  have hP1_le_R : P1 ≤ R := by simpa [P1] using hP1data.1
  have hP1card : Nat.card P1 = p := by simpa [P1] using hP1data.2.1
  have hP1_not_le_T : ¬ P1 ≤ T := by simpa [P1] using hP1data.2.2
  have hP1_ne_P : P1 ≠ P := by
    intro hP1P
    have hgStab : g ∈ MulAction.stabilizer G P := by
      rw [MulAction.mem_stabilizer_iff]
      change g • P = P at hP1P
      exact hP1P
    rw [hstabG, (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.2.1] at hgStab
    exact hgC hgStab
  let X := MulAction.orbit NR P
  have hP1orbit : P1 ∈ MulAction.orbit NR P := by
    exact ⟨gNR, rfl⟩
  let base : X := ⟨P, MulAction.mem_orbit_self P⟩
  let p1 : X := ⟨P1, hP1orbit⟩
  have horbit_data (A : X) :
      (A : Subgroup G) ≤ R ∧ Nat.card (A : Subgroup G) = p ∧
        ¬ (A : Subgroup G) ≤ T := by
    rcases A.property with ⟨a, ha⟩
    rw [← ha]
    exact hconj_data a
  have hNormP_eq_C : Subgroup.normalizer (P : Set G) = C :=
    (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.2.1
  have hC_le_NR' : C ≤ NR := by simpa [C, NR] using hC_le_NR
  let cNR : CQ → NR := fun c =>
    ⟨(c : G), hC_le_NR' (by simpa [C, CQ] using c.property.2)⟩
  have hcfix (c : CQ) : cNR c • P = P := by
    have hcNorm : (c : G) ∈ Subgroup.normalizer (P : Set G) :=
      centralizer_le_normalizer P c.property.2
    have hcStab : (c : G) ∈ MulAction.stabilizer G P := by
      rwa [hstabG]
    rw [MulAction.mem_stabilizer_iff] at hcStab
    change (c : G) • P = P
    exact hcStab
  let f : Option CQ → X
    | none => base
    | some c =>
        ⟨(cNR c)⁻¹ • P1, by
          refine ⟨(cNR c)⁻¹ * gNR, ?_⟩
          simp [P1, mul_smul]⟩
  have hf_some (c : CQ) :
      ((f (some c) : X) : Subgroup G) = rightConjugate P1 (c : G) := by
    change P1.map (MulAut.conj ((c : G)⁻¹)).toMonoidHom =
      P1.map (MulAut.conj ((c : G)⁻¹)).toMonoidHom
    rfl
  have hf_some_ne (c : CQ) :
      ((f (some c) : X) : Subgroup G) ≠ P := by
    intro heq
    apply hP1_ne_P
    calc
      P1 = cNR c • ((cNR c)⁻¹ • P1) := (smul_inv_smul (cNR c) P1).symm
      _ = cNR c • P := by simpa [f] using congrArg (fun A : Subgroup G => cNR c • A) heq
      _ = P := hcfix c
  have hf_injective : Function.Injective f := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some c =>
            exfalso
            exact hf_some_ne c (congrArg Subtype.val hxy).symm
    | some c =>
        cases y with
        | none =>
            exfalso
            exact hf_some_ne c (congrArg Subtype.val hxy)
        | some d =>
            have hBdata := horbit_data (f (some c))
            have hreg := hR.2.2.2.2.2 P1 ((f (some c) : X) : Subgroup G)
              hP1_le_R hBdata.1 hP1card hBdata.2.1 hP1_not_le_T hBdata.2.2
              hP1_ne_P (hf_some_ne c)
            congr 1
            apply Subtype.ext
            exact hreg.unique
              ⟨c.property, (hf_some c).symm⟩
              ⟨d.property, by
                calc
                  ((f (some c) : X) : Subgroup G) =
                      ((f (some d) : X) : Subgroup G) := congrArg Subtype.val hxy
                  _ = rightConjugate P1 (d : G) := hf_some d⟩
  have hf_surjective : Function.Surjective f := by
    intro A
    by_cases hAP : (A : Subgroup G) = P
    · exact ⟨none, Subtype.ext hAP.symm⟩
    · have hAdata := horbit_data A
      rcases hR.2.2.2.2.2 P1 (A : Subgroup G)
          hP1_le_R hAdata.1 hP1card hAdata.2.1 hP1_not_le_T hAdata.2.2
          hP1_ne_P hAP with ⟨c, hc, _hcUnique⟩
      let cCQ : CQ := ⟨c, hc.1⟩
      refine ⟨some cCQ, ?_⟩
      apply Subtype.ext
      calc
        ((f (some cCQ) : X) : Subgroup G) = rightConjugate P1 c := hf_some cCQ
        _ = (A : Subgroup G) := hc.2.symm
  let e : Option CQ ≃ X := Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  have hXcard : Nat.card X = p ^ m := by
    calc
      Nat.card X = Nat.card (Option CQ) := Nat.card_congr e.symm
      _ = Nat.card CQ + 1 := by simp
      _ = p ^ m := by simpa [CQ] using hCQcard
  have hstabNR :
      MulAction.stabilizer NR P = C.subgroupOf NR := by
    ext a
    change ((a : G) • P = P) ↔ (a : G) ∈ C
    rw [← MulAction.mem_stabilizer_iff, hstabG, hNormP_eq_C]
  have hstabCard : Nat.card (MulAction.stabilizer NR P) = Nat.card C := by
    rw [hstabNR]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_NR').toEquiv
  let : Fintype X := Fintype.ofFinite X
  have hOrbitMul :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group NR P
  have hXcardF : Fintype.card X = p ^ m := by
    simpa [Nat.card_eq_fintype_card] using hXcard
  have hstabCardF : Fintype.card (MulAction.stabilizer NR P) = Nat.card C := by
    simpa [Nat.card_eq_fintype_card] using hstabCard
  have hNRcard : Nat.card NR = p ^ m * Nat.card C := by
    rw [hXcardF, hstabCardF] at hOrbitMul
    simpa [Nat.card_eq_fintype_card] using hOrbitMul.symm
  have hRcard_dvd_C : p ^ (m + 1) ∣ Nat.card C := by
    rw [← hRcard]
    exact Subgroup.card_dvd_of_le hR_le_C
  rcases hRcard_dvd_C with ⟨c, hc⟩
  have hpow_dvd_NR : p ^ (2 * m + 1) ∣ Nat.card NR := by
    rw [hNRcard, hc]
    refine ⟨c, ?_⟩
    calc
      p ^ m * (p ^ (m + 1) * c) = (p ^ m * p ^ (m + 1)) * c := by ac_rfl
      _ = p ^ (m + (m + 1)) * c := by rw [← pow_add]
      _ = p ^ (2 * m + 1) * c := by
        congr 2
        omega
  have hpow_dvd_G : p ^ (2 * m + 1) ∣ Nat.card G :=
    hpow_dvd_NR.trans (Subgroup.card_subgroup_dvd_card NR)
  have hpow_dvd_main : p ^ (2 * m + 1) ∣ p ^ (m + 2) := by
    have hcop : Nat.Coprime (p ^ (2 * m + 1)) u :=
      Nat.Coprime.pow_left (2 * m + 1)
        (hch.B1.p_prime.coprime_iff_not_dvd.mpr hu)
    apply hcop.dvd_of_dvd_mul_right
    simpa [hGcard] using hpow_dvd_G
  have hm_le : 2 * m + 1 ≤ m + 2 :=
    (Nat.pow_dvd_pow_iff_le_right hch.B1.p_prime.one_lt).mp hpow_dvd_main
  have hm_pos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hcardPos : 0 < Nat.card (nearFieldStar Q P) := Nat.card_pos
    rw [hm0, pow_zero] at hStarComm_order
    omega
  have hm1 : m = 1 := by omega
  have hP_le_normalizer_T : P ≤ Subgroup.normalizer (T : Set G) := by
    intro y hyP
    apply centralizer_le_normalizer T
    rw [Subgroup.mem_centralizer_iff]
    intro x hxT
    exact ((Subgroup.mem_centralizer_iff.mp (hR.2.2.1 hxT)) y hyP).symm
  have hTcard : Nat.card T = p := by
    have hprod : Nat.card R = Nat.card T * Nat.card P := by
      rw [hR.1]
      exact chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        T P hP_le_normalizer_T hR.2.1
    apply Nat.eq_of_mul_eq_mul_right hch.B1.p_prime.pos
    calc
      Nat.card T * p = Nat.card T * Nat.card P := by rw [hch.B1.P_card]
      _ = Nat.card R := hprod.symm
      _ = p ^ (m + 1) := hRcard
      _ = p ^ 2 := by rw [hm1]
      _ = p * p := by rw [pow_two]
  have hTnotOrbit : T ∉ MulAction.orbit NR P := by
    intro hTorb
    exact (horbit_data ⟨T, hTorb⟩).2.2 le_rfl
  have hconjT_data (a : NR) :
      (a • T : Subgroup G) ≤ R ∧ Nat.card (a • T : Subgroup G) = p := by
    constructor
    · intro x hx
      change x ∈ T.map (MulAut.conj (a : G)).toMonoidHom at hx
      rcases hx with ⟨y, hyT, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp a.property y).1
        (hR.1.symm ▸ Subgroup.mem_sup_left hyT)
    · change Nat.card (T.map (MulAut.conj (a : G)).toMonoidHom) = p
      rw [Subgroup.card_map_of_injective (MulAut.conj (a : G)).injective, hTcard]
  have hNRfixT (a : NR) : a • T = T := by
    by_contra hne
    have hTg_not_le : ¬ (a • T : Subgroup G) ≤ T := by
      intro hle
      apply hne
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [(hconjT_data a).2, hTcard]
    have hTgOrbit : (a • T : Subgroup G) ∈ MulAction.orbit NR P := by
      by_cases hEqP : (a • T : Subgroup G) = P
      · rw [hEqP]
        exact MulAction.mem_orbit_self P
      · rcases hR.2.2.2.2.2 P1 (a • T : Subgroup G)
            hP1_le_R (hconjT_data a).1 hP1card (hconjT_data a).2
            hP1_not_le_T hTg_not_le hP1_ne_P hEqP with
          ⟨c, hc, _hcUnique⟩
        let cCQ : CQ := ⟨c, hc.1⟩
        have heq : (a • T : Subgroup G) = ((f (some cCQ) : X) : Subgroup G) := by
          calc
            (a • T : Subgroup G) = rightConjugate P1 c := hc.2
            _ = ((f (some cCQ) : X) : Subgroup G) := (hf_some cCQ).symm
        rw [heq]
        exact (f (some cCQ)).property
    apply hTnotOrbit
    rcases hTgOrbit with ⟨b, hb⟩
    refine ⟨a⁻¹ * b, ?_⟩
    calc
      (a⁻¹ * b) • P = a⁻¹ • (b • P) := by rw [mul_smul]
      _ = a⁻¹ • (a • T) := congrArg (fun A : Subgroup G => a⁻¹ • A) hb
      _ = T := inv_smul_smul a T
  have hstabT :
      MulAction.stabilizer G T = Subgroup.normalizer (T : Set G) := by
    ext a
    change a • T = T ↔ a ∈ Subgroup.normalizer (T : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer T),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact
      forall_congr' fun x =>
        iff_congr Iff.rfl
          ⟨fun ⟨y, hy, heq⟩ => heq ▸ by simpa [mul_assoc] using hy,
            fun hx => ⟨(MulAut.conj a)⁻¹ x, hx,
              MulAut.apply_inv_self G (MulAut.conj a) x⟩⟩
  have hNR_le_normalizer_T : NR ≤ Subgroup.normalizer (T : Set G) := by
    intro a ha
    let aNR : NR := ⟨a, ha⟩
    have haStab : a ∈ MulAction.stabilizer G T := by
      rw [MulAction.mem_stabilizer_iff]
      have hfix := hNRfixT aNR
      change a • T = T at hfix
      exact hfix
    rwa [hstabT] at haStab
  exact ⟨hm1, by simpa [NR, C] using hNRcard, by simpa [NR] using hNR_le_normalizer_T⟩

private lemma chapter2_claim12_commutatorElement_mem_center_of_commutator_le_center
    {K : Type*} [Group K]
    (hcomm : _root_.commutator K ≤ Subgroup.center K) (x y : K) :
    ⁅x, y⁆ ∈ Subgroup.center K := by
  exact hcomm <|
    Subgroup.commutator_mem_commutator
      (show x ∈ (⊤ : Subgroup K) by trivial)
      (show y ∈ (⊤ : Subgroup K) by trivial)

private lemma chapter2_claim12_commutatorElement_mul_left_of_commutator_le_center
    {K : Type*} [Group K]
    (hcomm : _root_.commutator K ≤ Subgroup.center K) (x y z : K) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hyz_cent : ⁅y, z⁆ ∈ Subgroup.center K :=
    chapter2_claim12_commutatorElement_mem_center_of_commutator_le_center
      hcomm y z
  have hleft : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    calc
      x * ⁅y, z⁆ * x⁻¹ = (⁅y, z⁆ * x) * x⁻¹ := by
        rw [(Subgroup.mem_center_iff.mp hyz_cent x).symm]
      _ = ⁅y, z⁆ := by simp [mul_assoc]
  have hEq : ⁅x * y, z⁆ * ⁅z, x⁆ = ⁅y, z⁆ := by
    calc
      ⁅x * y, z⁆ * ⁅z, x⁆ = x * ⁅y, z⁆ * x⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      _ = ⁅y, z⁆ := hleft
  have hyz_comm : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
    ((Subgroup.mem_center_iff.mp hyz_cent) ⁅x, z⁆).symm
  have hzx_one : ⁅z, x⁆ * ⁅x, z⁆ = 1 := by
    simpa [commutatorElement_inv] using (mul_inv_cancel (⁅z, x⁆))
  calc
    ⁅x * y, z⁆ = ⁅x * y, z⁆ * 1 := by simp
    _ = ⁅x * y, z⁆ * (⁅z, x⁆ * ⁅x, z⁆) := by rw [hzx_one]
    _ = (⁅x * y, z⁆ * ⁅z, x⁆) * ⁅x, z⁆ := by simp [mul_assoc]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [hEq]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hyz_comm

private theorem chapter2_claim12_commutator_quotient_hom
    {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hcomm_le : _root_.commutator K ≤ N)
    (hcenter : N ≤ Subgroup.center K) (y : K) :
    ∃ φ : (K ⧸ N) →* N,
      ∀ x : K,
        φ (QuotientGroup.mk' N x) =
          ⟨⁅x, y⁆, hcomm_le (by
            simpa [_root_.commutator_def] using
              (Subgroup.commutator_mem_commutator
                (show x ∈ (⊤ : Subgroup K) by trivial)
                (show y ∈ (⊤ : Subgroup K) by trivial)))⟩ := by
  have hcomm_center : _root_.commutator K ≤ Subgroup.center K :=
    hcomm_le.trans hcenter
  let f : K →* N :=
    { toFun := fun x =>
        ⟨⁅x, y⁆, hcomm_le (by
          simpa [_root_.commutator_def] using
            (Subgroup.commutator_mem_commutator
              (show x ∈ (⊤ : Subgroup K) by trivial)
              (show y ∈ (⊤ : Subgroup K) by trivial)))⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x z
        apply Subtype.ext
        exact chapter2_claim12_commutatorElement_mul_left_of_commutator_le_center
          hcomm_center x z y }
  have hN_le_ker : N ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcenter hx) y).symm
  let φ : (K ⧸ N) →* N := QuotientGroup.lift N f hN_le_ker
  refine ⟨φ, ?_⟩
  intro x
  rfl

private theorem chapter2_claim12_disjoint_of_ne_of_card_eq_prime
    {E : Type*} [Group E] [Finite E] (p : ℕ) [Fact p.Prime]
    {L K : Subgroup E} (hLcard : Nat.card L = p)
    (hKcard : Nat.card K = p) (hne : L ≠ K) : Disjoint L K := by
  rw [disjoint_iff]
  let I : Subgroup E := L ⊓ K
  have hIleL : I ≤ L := inf_le_left
  let IL : Subgroup L := I.subgroupOf L
  let : Fact (Nat.Prime (Nat.card L)) :=
    ⟨hLcard ▸ (Fact.out : Nat.Prime p)⟩
  change I = ⊥
  rcases IL.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · apply le_antisymm
    · intro x hxI
      let xL : L := ⟨x, hIleL hxI⟩
      have hxIL : xL ∈ IL := hxI
      rw [hbot] at hxIL
      exact Subgroup.mem_bot.mpr
        (congrArg Subtype.val (Subgroup.mem_bot.mp hxIL))
    · exact bot_le
  · exfalso
    apply hne
    have hLK : L ≤ K :=
      (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
    apply Subgroup.eq_of_le_of_card_ge hLK
    rw [hLcard, hKcard]

private theorem chapter2_claim12_prime_order_subgroups_card_of_elementaryAbelian_prime_sq
    {E : Type*} [Group E] [Finite E] (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p E] (hEcard : Nat.card E = p ^ 2) :
    Nat.card {X : Subgroup E // Nat.card X = p} = p + 1 := by
  classical
  let : IsMulCommutative E :=
    (inferInstance : IsElementaryAbelian p E).toIsMulCommutative
  let : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm := mul_comm' }
  let eta : Subgroup E ≃o Submodule (ZMod p) (Additive E) :=
    Subgroup.toAddSubgroup.trans
      (AddSubgroup.toZModSubmodule (n := p))
  have hcard_submodule (X : Subgroup E) :
      Nat.card (eta X) = Nat.card X := by
    let eEta : (eta X) ≃ Subgroup.toAddSubgroup X :=
      { toFun := fun x => ⟨x.1, by
          have hx : x.1 ∈ AddSubgroup.toZModSubmodule
              (n := p) (Subgroup.toAddSubgroup X) := x.property
          exact hx⟩
        invFun := fun x => ⟨x.1, by
          have hx : x.1 ∈ Subgroup.toAddSubgroup X := x.property
          exact hx⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
    let eX : Subgroup.toAddSubgroup X ≃ X :=
      { toFun := fun x =>
          ⟨Additive.toMul x.1,
            (Additive.mem_toAddSubgroup X x.1).1 x.property⟩
        invFun := fun x =>
          ⟨Additive.ofMul (x : E),
            (Additive.mem_toAddSubgroup X _).2 x.property⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
    exact (Nat.card_congr eEta).trans (Nat.card_congr eX)
  have hfinrank_iff (X : Subgroup E) :
      Module.finrank (ZMod p) (eta X) = 1 ↔ Nat.card X = p := by
    have hnat : Nat.card (eta X) =
        p ^ Module.finrank (ZMod p) (eta X) := by
      simpa [ZMod.card] using
        Module.natCard_eq_pow_finrank (K := ZMod p) (V := eta X)
    constructor
    · intro hdim
      rw [← hcard_submodule X, hnat, hdim, pow_one]
    · intro hcard
      have hpow :
          p ^ Module.finrank (ZMod p) (eta X) = p ^ 1 := by
        rw [← hnat, hcard_submodule X, hcard, pow_one]
      exact Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt hpow
  let eSub :
      {X : Subgroup E // Nat.card X = p} ≃
        {L : Submodule (ZMod p) (Additive E) //
          Module.finrank (ZMod p) L = 1} :=
    { toFun := fun X => ⟨eta X.1, (hfinrank_iff X.1).2 X.2⟩
      invFun := fun L =>
        ⟨eta.symm L.1,
          (hfinrank_iff (eta.symm L.1)).1 (by
            rw [eta.apply_symm_apply]
            exact L.2)⟩
      left_inv := fun X => Subtype.ext (eta.symm_apply_apply X.1)
      right_inv := fun L => Subtype.ext (eta.apply_symm_apply L.1) }
  have hdimE : Module.finrank (ZMod p) (Additive E) = 2 := by
    have hnat := Module.natCard_eq_pow_finrank
      (K := ZMod p) (V := Additive E)
    have hEcardAdd : Nat.card (Additive E) = p ^ 2 := by
      calc
        Nat.card (Additive E) = Nat.card E :=
          Nat.card_congr Additive.toMul
        _ = p ^ 2 := hEcard
    have hpow : p ^ Module.finrank (ZMod p) (Additive E) = p ^ 2 := by
      simpa [ZMod.card, hEcardAdd] using hnat.symm
    exact Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt hpow
  calc
    Nat.card {X : Subgroup E // Nat.card X = p} =
        Nat.card {L : Submodule (ZMod p) (Additive E) //
          Module.finrank (ZMod p) L = 1} := Nat.card_congr eSub
    _ = Nat.card (Projectivization (ZMod p) (Additive E)) := by
      exact Nat.card_congr
        (Projectivization.equivSubmodule (ZMod p) (Additive E)).symm
    _ = p + 1 := by
      simpa [ZMod.card] using
        Projectivization.card_of_finrank_two
          (ZMod p) (Additive E) hdimE

private theorem chapter2_claim12_prime_order_subgroups_ne_card
    {E : Type*} [Group E] [Finite E] (p : ℕ) [Fact p.Prime]
    (Z : Subgroup E) (hZcard : Nat.card Z = p)
    (hall : Nat.card {X : Subgroup E // Nat.card X = p} = p + 1) :
    Nat.card {X : Subgroup E // Nat.card X = p ∧ X ≠ Z} = p := by
  classical
  let Omega := {X : Subgroup E // Nat.card X = p}
  let zOmega : Omega := ⟨Z, hZcard⟩
  let e : {X : Subgroup E // Nat.card X = p ∧ X ≠ Z} ≃
      {X : Omega // X ≠ zOmega} :=
    { toFun := fun X => ⟨⟨X.1, X.2.1⟩, by
          intro h
          exact X.2.2 (congrArg Subtype.val h)⟩
      invFun := fun X => ⟨X.1.1, X.1.2, by
          intro h
          exact X.2 (Subtype.ext h)⟩
      left_inv := fun X => Subtype.ext rfl
      right_inv := fun X => Subtype.ext (Subtype.ext rfl) }
  calc
    Nat.card {X : Subgroup E // Nat.card X = p ∧ X ≠ Z} =
        Nat.card {X : Omega // X ≠ zOmega} := Nat.card_congr e
    _ = p := by
      have : Fintype Omega := Fintype.ofFinite Omega
      have : Fintype {X : Omega // X ≠ zOmega} := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq]
      rw [← Nat.card_eq_fintype_card, hall]
      omega

private theorem chapter2_claim12_third_line_stabilizer_eq_one
    {U C : Type*} [Group U] [Finite U] [Group C]
    [MulDistribMulAction C U]
    (p : ℕ) [Fact p.Prime] (F J L : Subgroup U) (c : C)
    (hFcard : Nat.card F = p) (hJcard : Nat.card J = p)
    (hLcard : Nat.card L = p) (hFJcompl : F.IsComplement' J)
    (hLneF : L ≠ F) (hLneJ : L ≠ J)
    (hfixF : ∀ {u : U}, u ∈ F → c • u = u)
    (hdeltaJ : ∀ u : U, (c • u) * u⁻¹ ∈ J)
    (hLinv : ∀ {u : U}, u ∈ L → c • u ∈ L)
    (hfaithfulJ : (∀ j : J, c • (j : U) = (j : U)) → c = 1) :
    c = 1 := by
  classical
  have hLJdisj : Disjoint L J :=
    chapter2_claim12_disjoint_of_ne_of_card_eq_prime
      p hLcard hJcard hLneJ
  have hLFdisj : Disjoint L F :=
    chapter2_claim12_disjoint_of_ne_of_card_eq_prime
      p hLcard hFcard hLneF
  have hLneBot : L ≠ ⊥ := by
    intro hbot
    have hpOne : p = 1 := by rw [← hLcard, hbot]; simp
    exact (Fact.out : Nat.Prime p).ne_one hpOne
  obtain ⟨xL, hxNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hLneBot
  let x : U := xL
  have hxL : x ∈ L := xL.property
  have hcxL : c • x ∈ L := hLinv hxL
  have hdeltaL : (c • x) * x⁻¹ ∈ L :=
    L.mul_mem hcxL (L.inv_mem hxL)
  have hdeltaBot : (c • x) * x⁻¹ ∈ (⊥ : Subgroup U) :=
    (Subgroup.disjoint_def.mp hLJdisj) hdeltaL (hdeltaJ x)
  have hcx : c • x = x := by
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hdeltaBot)
  rcases (hFJcompl.existsUnique x).exists with ⟨⟨f, j⟩, hfj⟩
  have hjNe : (j : U) ≠ 1 := by
    intro hjOne
    have hxF : x ∈ F := by
      rw [← hfj, hjOne, mul_one]
      exact f.property
    have hxBot : x ∈ (⊥ : Subgroup U) :=
      (Subgroup.disjoint_def.mp hLFdisj) hxL hxF
    exact hxNe (Subtype.ext (Subgroup.mem_bot.mp hxBot))
  have hcf : c • (f : U) = (f : U) := hfixF f.property
  have hcj : c • (j : U) = (j : U) := by
    have hmul : (f : U) * (c • (j : U)) = (f : U) * (j : U) := by
      calc
        (f : U) * (c • (j : U)) = c • ((f : U) * (j : U)) := by
          calc
            (f : U) * (c • (j : U)) =
                (c • (f : U)) * (c • (j : U)) :=
              congrArg (fun z : U => z * (c • (j : U))) hcf.symm
            _ = c • ((f : U) * (j : U)) :=
              (map_mul (MulDistribMulAction.toMonoidEnd C U c)
                (f : U) (j : U)).symm
        _ = c • x := by rw [hfj]
        _ = x := hcx
        _ = (f : U) * (j : U) := hfj.symm
    exact mul_left_cancel hmul
  apply hfaithfulJ
  intro k
  have hzpow := mem_zpowers_of_prime_card
    (G := J) (p := p) hJcard (g := j) (g' := k) (by
      intro hjOneSub
      exact hjNe (congrArg Subtype.val hjOneSub))
  rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨n, hn⟩
  have hnU : (j : U) ^ n = (k : U) := congrArg Subtype.val hn
  calc
    c • (k : U) = c • ((j : U) ^ n) := by rw [hnU]
    _ = (c • (j : U)) ^ n := by
      exact map_zpow (MulDistribMulAction.toMonoidEnd C U c) (j : U) n
    _ = (j : U) ^ n := by rw [hcj]
    _ = (k : U) := hnU

set_option backward.isDefEq.respectTransparency false in
private theorem chapter2_claim12_regular_complement_action_faithful
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (T P R CQ : Subgroup G)
    (hTcard : Nat.card T = p)
    (hPcard : Nat.card P = p)
    (hR_eq : R = T ⊔ P)
    (hTPdisj : Disjoint T P)
    (hTcentralP : T ≤ Subgroup.centralizer (P : Set G))
    (hCQcentralP : CQ ≤ Subgroup.centralizer (P : Set G))
    (hreg : ∀ A B : Subgroup G,
      A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
        ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
          ∃! d : G, d ∈ CQ ∧ B = rightConjugate A d)
    (yP : P) (hyPne : yP ≠ 1) (c : CQ)
    (hfixT : ∀ x : G, x ∈ T → (c : G) * x * (c : G)⁻¹ = x) :
    c = 1 := by
  classical
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply (Fact.out : Nat.Prime p).ne_one
    calc
      p = Nat.card T := hTcard.symm
      _ = 1 := by simp [hbot]
  obtain ⟨xT, hxTne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have hxPow : (xT : G) ^ p = 1 := by
    have hd : orderOf xT ∣ p := by
      have hd0 := orderOf_dvd_natCard xT
      rw [hTcard] at hd0
      exact hd0
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
  have hyPow : (yP : G) ^ p = 1 := by
    have hd : orderOf yP ∣ p := by
      have hd0 := orderOf_dvd_natCard yP
      rw [hPcard] at hd0
      exact hd0
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
  have hxy : Commute (xT : G) (yP : G) :=
    (Subgroup.mem_centralizer_iff.mp
      (hTcentralP xT.property) (yP : G) yP.property).symm
  let z : G := (xT : G) * (yP : G)
  have hzPow : z ^ p = 1 := by
    dsimp [z]
    rw [hxy.mul_pow, hxPow, hyPow]
    simp
  have hzNe : z ≠ 1 := by
    intro hz
    have hxEq : (xT : G) = (yP : G)⁻¹ := eq_inv_of_mul_eq_one_left hz
    have hxP : (xT : G) ∈ P := by
      rw [hxEq]
      exact P.inv_mem yP.property
    have hxBot : (xT : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hTPdisj) xT.property hxP
    exact hxTne (Subtype.ext (Subgroup.mem_bot.mp hxBot))
  have hzOrder : orderOf z = p := orderOf_eq_prime hzPow hzNe
  let B : Subgroup G := Subgroup.zpowers z
  have hBcard : Nat.card B = p := by
    change Nat.card (Subgroup.zpowers z) = p
    rw [Nat.card_zpowers, hzOrder]
  have hB_le_R : B ≤ R := by
    change Subgroup.zpowers z ≤ R
    rw [Subgroup.zpowers_le, hR_eq]
    exact Subgroup.mul_mem_sup xT.property yP.property
  have hB_not_le_T : ¬ B ≤ T := by
    intro hBT
    have hzT : z ∈ T := hBT (Subgroup.mem_zpowers z)
    have hyT : (yP : G) ∈ T := by
      have heq : (xT : G)⁻¹ * z = (yP : G) := by
        simp [z]
      rw [← heq]
      exact T.mul_mem (T.inv_mem xT.property) hzT
    have hyBot : (yP : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hTPdisj) hyT yP.property
    exact hyPne (Subtype.ext (Subgroup.mem_bot.mp hyBot))
  have hB_ne_P : B ≠ P := by
    intro hBP
    have hzP : z ∈ P := by
      rw [← hBP]
      exact Subgroup.mem_zpowers z
    have hxP : (xT : G) ∈ P := by
      have heq : z * (yP : G)⁻¹ = (xT : G) := by
        simp [z]
      rw [← heq]
      exact P.mul_mem hzP (P.inv_mem yP.property)
    have hxBot : (xT : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hTPdisj) xT.property hxP
    exact hxTne (Subtype.ext (Subgroup.mem_bot.mp hxBot))
  have hcx : Commute (c : G) (xT : G) := by
    calc
      (c : G) * (xT : G) =
          ((c : G) * (xT : G) * (c : G)⁻¹) * (c : G) := by group
      _ = (xT : G) * (c : G) := by rw [hfixT (xT : G) xT.property]
  have hcy : Commute (c : G) (yP : G) :=
    (Subgroup.mem_centralizer_iff.mp
      (hCQcentralP c.property) (yP : G) yP.property).symm
  have hcz : Commute (c : G) z := by
    dsimp [z]
    exact hcx.mul_right hcy
  have hzRight : rightConjugateElem z (c : G) = z := by
    rw [rightConjugateElem]
    calc
      (c : G)⁻¹ * z * (c : G) = (c : G)⁻¹ * (z * (c : G)) := by
        rw [mul_assoc]
      _ = (c : G)⁻¹ * ((c : G) * z) := by rw [← hcz.eq]
      _ = z := by simp
  have hBfix : rightConjugate B (c : G) = B := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    rw [show B = Subgroup.zpowers z from rfl]
    apply congrArg Subgroup.zpowers
    simpa [MulAut.conj_apply, rightConjugateElem] using hzRight
  have hregB := hreg B B hB_le_R hB_le_R hBcard hBcard
    hB_not_le_T hB_not_le_T hB_ne_P hB_ne_P
  have hOne : (1 : G) ∈ CQ ∧ B = rightConjugate B (1 : G) := by
    constructor
    · exact CQ.one_mem
    · change B = B.conjBy (1 : G)⁻¹
      simpa using (Subgroup.conjBy_one B).symm
  have hcWitness : (c : G) ∈ CQ ∧ B = rightConjugate B (c : G) :=
    ⟨c.property, hBfix.symm⟩
  have hcOne : (c : G) = 1 :=
    @ExistsUnique.unique G
      (fun d => d ∈ CQ ∧ B = rightConjugate B d)
      hregB (c : G) (1 : G) hcWitness hOne
  exact Subtype.ext hcOne

private theorem chapter2_claim12_map_eq_self_of_fixed
    {G : Type*} [Group G] (H : Subgroup G) (e : G ≃* G)
    (hfix : ∀ {x : G}, x ∈ H → e x = x) :
    H.map e.toMonoidHom = H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have heq : e.toMonoidHom y = y := hfix hy
    rw [heq]
    exact hy
  · intro hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    have heq : e.toMonoidHom x = x := hfix hx
    exact heq

private theorem chapter2_claim12_mem_normalizer_of_conj_mem
    {G : Type*} [Group G] (R : Subgroup G) (a : G)
    (hforward : ∀ x : G, x ∈ R → a * x * a⁻¹ ∈ R)
    (hbackward : ∀ x : G, x ∈ R → a⁻¹ * x * (a⁻¹)⁻¹ ∈ R) :
    a ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward x
  · intro hx
    have h := hbackward (a * x * a⁻¹) hx
    simpa [mul_assoc] using h

private theorem chapter2_claim12_mem_normalizer_sup
    {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← Subgroup.conjAct_pointwise_smul_iff]
  rw [Subgroup.pointwise_smul_def]
  change Subgroup.map (MulAut.conj x).toMonoidHom (A ⊔ B) = A ⊔ B
  rw [Subgroup.map_sup]
  change ConjAct.toConjAct x • A ⊔ ConjAct.toConjAct x • B = A ⊔ B
  rw [Subgroup.conjAct_pointwise_smul_eq_self hA,
    Subgroup.conjAct_pointwise_smul_eq_self hB]


private theorem chapter2_claim12_mulDistrib_compHom_smul
    {A B X : Type*} [Monoid A] [Monoid B] [Group X]
    [MulDistribMulAction B X] (f : A →* B) (a : A) (x : X) :
    letI : MulDistribMulAction A X := MulDistribMulAction.compHom X f
    a • x = f a • x := rfl

private theorem chapter2_claim12_subgroup_compHom_smul_eq_self_of_fixed
    {A G : Type*} [Monoid A] [Group G]
    (f : A →* MulAut G) (H : Subgroup G) (a : A)
    (hfix : ∀ {x : G}, x ∈ H → f a x = x) :
    letI : MulAction A (Subgroup G) := MulAction.compHom _ f
    a • H = H := by
  change H.map (f a).toMonoidHom = H
  exact chapter2_claim12_map_eq_self_of_fixed H (f a) hfix

private theorem chapter2_claim12_prime_four_not_dvd_prime_cube_mul
    (p u : ℕ) (hp : p.Prime) (hu : ¬ p ∣ u) :
    ¬ p ^ 4 ∣ p ^ 3 * u := by
  intro hdiv
  have hcop : Nat.Coprime (p ^ 4) u :=
    Nat.Coprime.pow_left 4 (hp.coprime_iff_not_dvd.mpr hu)
  have hpow : p ^ 4 ∣ p ^ 3 := hcop.dvd_of_dvd_mul_right hdiv
  have hle : 4 ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow
  omega

private theorem chapter2_claim12_smul_mem_smul_subgroup
    {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]
    (a : A) (H : Subgroup G) {x : G} (hx : x ∈ H) :
    a • x ∈ a • H :=
  Subgroup.smul_mem_pointwise_smul x a H hx

private theorem chapter2_claim12_third_line_stabilizer_eq_one_of_subgroup_fix
    {U H C : Type*} [Group U] [Finite U] [Group H] [Group C]
    [MulDistribMulAction H U] [MulDistribMulAction C U]
    [MulAction H (Subgroup U)]
    (incl : C →* H) (p : ℕ) [Fact p.Prime]
    (F J L : Subgroup U) (c : C)
    (hFcard : Nat.card F = p) (hJcard : Nat.card J = p)
    (hLcard : Nat.card L = p) (hFJcompl : F.IsComplement' J)
    (hLneF : L ≠ F) (hLneJ : L ≠ J)
    (hfixF : ∀ {u : U}, u ∈ F → c • u = u)
    (hdeltaJ : ∀ u : U, (c • u) * u⁻¹ ∈ J)
    (hfaithfulJ : (∀ j : J, c • (j : U) = (j : U)) → c = 1)
    (hagree : ∀ (d : C) (u : U), incl d • u = d • u)
    (hfix : incl c • L = L)
    (hsmul_mem : ∀ {u : U}, u ∈ L → incl c • u ∈ incl c • L) :
    c = 1 := by
  apply chapter2_claim12_third_line_stabilizer_eq_one
    p F J L c hFcard hJcard hLcard hFJcompl hLneF hLneJ hfixF hdeltaJ
  · intro u hu
    have huMap := hsmul_mem hu
    rw [hfix] at huMap
    rw [hagree c u] at huMap
    exact huMap
  · exact hfaithfulJ

private theorem chapter2_claim12_smul_coe_sq_ne_one
    {G A : Type*} [Group G] [Group A] (R : Subgroup G)
    [MulDistribMulAction A R] (a : A) (x : R)
    (hx : (x : G) ^ 2 ≠ 1) : (((a • x : R) : G) ^ 2) ≠ 1 := by
  intro hsqG
  have hsqR : (a • x : R) ^ 2 = 1 := Subtype.ext hsqG
  let beta : R ≃* R := MulDistribMulAction.toMulAut A R a
  have hback := congrArg beta.symm hsqR
  apply hx
  exact congrArg Subtype.val (by simpa [beta] using hback)

private theorem chapter2_claim12_orbit_avoids_inverted_line
    {G U : Type*} [Group G] [Finite G] [Group U]
    (H12 R1 V P : Subgroup G)
    [MulDistribMulAction H12 R1] [MulDistribMulAction H12 U]
    (qU : R1 →* U) (PR1 : Subgroup R1)
    (Pbar Jcomm : Subgroup U) (T1R : Subgroup R1) (T1 : Subgroup G)
    (yR1 : R1) (yP : P) (s : G)
    (hPbar : Pbar = PR1.map qU) (hyPR1 : yR1 ∈ PR1)
    (hT1R : T1R = Jcomm.comap qU)
    (hT1 : T1 = T1R.map R1.subtype)
    (hqcompat : ∀ (a : H12) (x : R1), a • qU x = qU (a • x))
    (hsmul_coe : ∀ (a : H12) (x : R1),
      (((a • x : R1) : G)) = (a : G) * (x : G) * (a : G)⁻¹)
    (hycoe : (yR1 : G) = (yP : G)) (hyPne : yP ≠ 1)
    (hPodd : Odd (Nat.card P)) (hP_le_V : P ≤ V)
    (hnotStrong : ∀ x : G, x ∈ V → x ^ 2 ≠ 1 → ¬ IsStronglyReal x)
    (hs : IsInvolution s)
    (hT1_inverted : ∀ x : G, x ∈ T1 → rightConjugateElem x s = x⁻¹) :
    let h12AutHom : H12 →* MulAut U :=
      MulDistribMulAction.toMulAut H12 U
    letI : MulAction H12 (Subgroup U) := MulAction.compHom _ h12AutHom
    ∀ a : H12, a • Pbar ≠ Jcomm := by
  dsimp only
  let h12AutHom : H12 →* MulAut U :=
    MulDistribMulAction.toMulAut H12 U
  let : MulAction H12 (Subgroup U) := MulAction.compHom _ h12AutHom
  intro a heq
  have hqyPbar : qU yR1 ∈ Pbar := by
    rw [hPbar]
    exact Subgroup.mem_map.mpr ⟨yR1, hyPR1, rfl⟩
  have hqConjAction : a • qU yR1 ∈ a • Pbar :=
    by
      change a • qU yR1 ∈ Pbar.map (h12AutHom a).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨qU yR1, hqyPbar, rfl⟩
  rw [heq] at hqConjAction
  have hqConjJ : qU (a • yR1) ∈ Jcomm := by
    rw [← hqcompat a yR1]
    exact hqConjAction
  have hyConjT1R : a • yR1 ∈ T1R := by
    rw [hT1R]
    exact hqConjJ
  have hyConjT1 : ((a • yR1 : R1) : G) ∈ T1 := by
    rw [hT1]
    exact Subgroup.mem_map.mpr ⟨a • yR1, hyConjT1R, rfl⟩
  have hyPneG : (yP : G) ≠ 1 := by
    intro hy
    exact hyPne (Subtype.ext hy)
  have hyP2 : (yP : G) ^ 2 ≠ 1 := by
    intro hySq
    exact (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
      (G := G) P hPodd yP.property) ⟨hyPneG, hySq⟩
  have hyR1P2 : (yR1 : G) ^ 2 ≠ 1 := by simpa [hycoe] using hyP2
  have hyConj2 : (((a • yR1 : R1) : G) ^ 2) ≠ 1 :=
    chapter2_claim12_smul_coe_sq_ne_one (G := G) (A := H12)
      R1 a yR1 hyR1P2
  have hyStrong : IsStronglyReal (((a • yR1 : R1) : G)) :=
    chapter2_claim12_stronglyReal_of_inverted_by_involution
      hs hyConj2 (hT1_inverted ((a • yR1 : R1) : G) hyConjT1)
  have hback : rightConjugateElem (((a • yR1 : R1) : G)) (a : G) =
      (yP : G) := by
    rw [hsmul_coe, hycoe]
    simp [rightConjugateElem, mul_assoc]
  have hyPStrong : IsStronglyReal (yP : G) := by
    simpa [hback] using
      chapter2_claim12_stronglyReal_rightConjugateElem (a : G) hyStrong
  exact (hnotStrong (yP : G) (hP_le_V yP.property) hyP2) hyPStrong

private theorem chapter2_claim12_le_normalizer_map_of_isInvariant
    {G : Type*} [Group G] (A R : Subgroup G) [MulDistribMulAction A R]
    (K : Subgroup R) (hK : IsInvariant A R K)
    (hsmul_coe : ∀ (a : A) (x : R),
      (((a • x : R) : G)) = (a : G) * (x : G) * (a : G)⁻¹) :
    A ≤ Subgroup.normalizer (K.map R.subtype : Set G) := by
  have hforward (a : A) (x : G)
      (hx : x ∈ K.map R.subtype) : (a : G) * x * (a : G)⁻¹ ∈ K.map R.subtype := by
    rcases Subgroup.mem_map.mp hx with ⟨xR, hxK, hxval⟩
    have hxInv : a • xR ∈ K :=
      (IsInvariant.invariant (A := A) (G := R) (H := K) a xR).1 hxK
    refine Subgroup.mem_map.mpr ⟨a • xR, hxInv, ?_⟩
    calc
      R.subtype (a • xR) = (a : G) * (xR : G) * (a : G)⁻¹ := hsmul_coe a xR
      _ = (a : G) * x * (a : G)⁻¹ := by
        have hxval' : (xR : G) = x := hxval
        exact congrArg (fun z : G => (a : G) * z * (a : G)⁻¹) hxval'
  intro a ha
  let aA : A := ⟨a, ha⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward aA x
  · intro hx
    have hback := hforward aA⁻¹ (a * x * a⁻¹) hx
    simpa [aA, mul_assoc] using hback

private theorem chapter2_claim12_projective_orbit_forces_normalizers_eq
    {G U : Type*} [Group G] [Finite G] [Group U] [Finite U]
    (p : ℕ) [Fact p.Prime] (H12 NR R1 CQ : Subgroup G)
    [MulDistribMulAction H12 U] [MulDistribMulAction CQ U]
    (incl : CQ →* H12) (Pbar Jcomm Ffix : Subgroup U)
    (hNR_le_H12 : NR ≤ H12) (hPbarcard : Nat.card Pbar = p)
    (hLinesCard : Nat.card {L : Subgroup U // Nat.card L = p ∧ L ≠ Jcomm} = p)
    (hCQcard : Nat.card CQ = p - 1)
    (hFfixcard : Nat.card Ffix = p) (hJcommcard : Nat.card Jcomm = p)
    (hFJcompl : Ffix.IsComplement' Jcomm) (hFfix_eq_Pbar : Ffix = Pbar)
    (hCQ_fixed_Ffix : ∀ (c : CQ) {u : U}, u ∈ Ffix → c • u = u)
    (hCQ_delta_mem_Jcomm : ∀ (c : CQ) (u : U), (c • u) * u⁻¹ ∈ Jcomm)
    (hCQ_faithful_Jcomm : ∀ c : CQ,
      (∀ j : Jcomm, c • (j : U) = (j : U)) → c = 1)
    (hCQ_actions_agree : ∀ (c : CQ) (u : U), incl c • u = c • u)
    (hR1card : Nat.card R1 = p ^ 3) (hR1_le_NR : R1 ≤ NR)
    (m u : ℕ) (hm1 : m = 1)
    (hGcard : Nat.card G = p ^ (m + 2) * u) (hu : ¬ p ∣ u) :
    let h12AutHom : H12 →* MulAut U := MulDistribMulAction.toMulAut H12 U
    letI : MulAction H12 (Subgroup U) := MulAction.compHom _ h12AutHom
    (∀ c : CQ, incl c • Pbar = Pbar) →
    (∀ a : H12, a • Pbar = Pbar ↔ (a : G) ∈ NR) →
    (∀ a : H12, a • Pbar ≠ Jcomm) → H12 = NR := by
  dsimp only
  let h12AutHom : H12 →* MulAut U := MulDistribMulAction.toMulAut H12 U
  let : MulAction H12 (Subgroup U) := MulAction.compHom _ h12AutHom
  intro hCQ_fix_Pbar hfixPbar_iff_mem_NR horbit_avoids_J
  apply le_antisymm
  · by_contra hnotLe
    have hNRlt : NR < H12 := ⟨hNR_le_H12, hnotLe⟩
    have hCQ_free_third (c : CQ) (L0 : Subgroup U)
        (hLcard : Nat.card L0 = p) (hLneP : L0 ≠ Pbar)
        (hLneJ : L0 ≠ Jcomm) (hfix : incl c • L0 = L0) : c = 1 := by
      exact chapter2_claim12_third_line_stabilizer_eq_one_of_subgroup_fix
        incl p Ffix Jcomm L0 c hFfixcard hJcommcard hLcard hFJcompl
          (by intro heq; apply hLneP; rw [← hFfix_eq_Pbar, heq]) hLneJ
          (hCQ_fixed_Ffix c) (hCQ_delta_mem_Jcomm c)
          (hCQ_faithful_Jcomm c) hCQ_actions_agree hfix
          (fun {_z} hz => chapter2_claim12_smul_mem_smul_subgroup (incl c) L0 hz)
    obtain ⟨g, hgH12, hgNR⟩ := SetLike.exists_of_lt hNRlt
    let gH : H12 := ⟨g, hgH12⟩
    let A0 : Subgroup U := Pbar.map (h12AutHom gH).toMonoidHom
    have hA0_eq : gH • Pbar = A0 := rfl
    have hA0card : Nat.card A0 = p := by
      calc
        Nat.card A0 = Nat.card Pbar := by
          dsimp [A0]
          exact Nat.card_congr ((h12AutHom gH).subgroupMap Pbar).toEquiv.symm
        _ = p := hPbarcard
    have hA0neP : A0 ≠ Pbar := by
      intro heq
      exact hgNR ((hfixPbar_iff_mem_NR gH).mp (hA0_eq.trans heq))
    have hA0neJ : A0 ≠ Jcomm := by
      intro heq
      exact horbit_avoids_J gH (hA0_eq.trans heq)
    let X := MulAction.orbit H12 Pbar
    let base : X := ⟨Pbar, MulAction.mem_orbit_self Pbar⟩
    have hA0orbit : A0 ∈ X := ⟨gH, hA0_eq⟩
    have hXdata (B : X) :
        Nat.card (B : Subgroup U) = p ∧ (B : Subgroup U) ≠ Jcomm := by
      rcases B.property with ⟨a, ha⟩
      constructor
      · rw [← ha]
        change Nat.card ((h12AutHom a) • Pbar : Subgroup U) = p
        calc
          Nat.card ((h12AutHom a) • Pbar : Subgroup U) = Nat.card Pbar :=
            Nat.card_congr ((h12AutHom a).subgroupMap Pbar).toEquiv.symm
          _ = p := hPbarcard
      · rw [← ha]
        exact horbit_avoids_J a
    let Lines := {L : Subgroup U // Nat.card L = p ∧ L ≠ Jcomm}
    let toLines : X → Lines := fun B => ⟨B, (hXdata B).1, (hXdata B).2⟩
    have htoLinesInj : Function.Injective toLines := by
      intro B C hBC
      apply Subtype.ext
      exact congrArg (fun z : Lines => (z.1 : Subgroup U)) hBC
    have hXcard_le : Nat.card X ≤ p := by
      calc
        Nat.card X ≤ Nat.card Lines := Nat.card_le_card_of_injective toLines htoLinesInj
        _ = p := by simpa [Lines] using hLinesCard
    let f : Option CQ → X
      | none => base
      | some c => ⟨incl c • A0, by
          refine ⟨incl c * gH, ?_⟩
          change (incl c * gH) • Pbar = incl c • A0
          rw [mul_smul, hA0_eq]⟩
    have hf_some_ne (c : CQ) : f (some c) ≠ base := by
      intro heq
      have heq0 : incl c • A0 = Pbar := congrArg Subtype.val heq
      apply hA0neP
      calc
        A0 = (incl c)⁻¹ • (incl c • A0) := (inv_smul_smul (incl c) A0).symm
        _ = (incl c)⁻¹ • Pbar := by rw [heq0]
        _ = incl c⁻¹ • Pbar :=
          congrArg (fun a : H12 => a • Pbar) (map_inv incl c).symm
        _ = Pbar := hCQ_fix_Pbar c⁻¹
    have hf_injective : Function.Injective f := by
      intro x y hxy
      cases x with
      | none =>
          cases y with
          | none => rfl
          | some c => exact (hf_some_ne c hxy.symm).elim
      | some c =>
          cases y with
          | none => exact (hf_some_ne c hxy).elim
          | some d =>
              congr 1
              apply Subtype.ext
              have heq0 : incl c • A0 = incl d • A0 := congrArg Subtype.val hxy
              have hstab : incl (d⁻¹ * c) • A0 = A0 := by
                calc
                  incl (d⁻¹ * c) • A0 = incl d⁻¹ • (incl c • A0) := by simp [mul_smul]
                  _ = incl d⁻¹ • (incl d • A0) := by rw [heq0]
                  _ = A0 := by simp
              have hdc : d⁻¹ * c = 1 :=
                hCQ_free_third (d⁻¹ * c) A0 hA0card hA0neP hA0neJ hstab
              exact congrArg Subtype.val (eq_of_inv_mul_eq_one hdc).symm
    have hp_le_X : p ≤ Nat.card X := by
      have hcard := Nat.card_le_card_of_injective f hf_injective
      have hopt : Nat.card (Option CQ) = p := by
        calc
          Nat.card (Option CQ) = Nat.card CQ + 1 := Finite.card_option
          _ = (p - 1) + 1 := by rw [hCQcard]
          _ = p := Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le
      calc
        p = Nat.card (Option CQ) := hopt.symm
        _ ≤ Nat.card X := hcard
    have hXcard : Nat.card X = p := le_antisymm hXcard_le hp_le_X
    let : Fintype H12 := Fintype.ofFinite H12
    let : Fintype X := Fintype.ofFinite X
    let : Fintype (MulAction.stabilizer H12 Pbar) := Fintype.ofFinite _
    have hOrbitMul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H12 Pbar
    have hXcardF : Fintype.card X = p := by
      simpa [Nat.card_eq_fintype_card] using hXcard
    rw [hXcardF] at hOrbitMul
    have hR1_le_H12 : R1 ≤ H12 := hR1_le_NR.trans hNR_le_H12
    let R1H : Subgroup H12 := R1.subgroupOf H12
    have hR1Hcard : Nat.card R1H = p ^ 3 := by
      calc
        Nat.card R1H = Nat.card R1 :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR1_le_H12).toEquiv
        _ = p ^ 3 := hR1card
    have hR1H_le_stab : R1H ≤ MulAction.stabilizer H12 Pbar := by
      intro r hr
      rw [MulAction.mem_stabilizer_iff]
      apply (hfixPbar_iff_mem_NR r).mpr
      exact hR1_le_NR hr
    have hp3_dvd_stab : p ^ 3 ∣ Nat.card (MulAction.stabilizer H12 Pbar) := by
      rw [← hR1Hcard]
      exact Subgroup.card_dvd_of_le hR1H_le_stab
    have hH12cardEq : Nat.card H12 = p * Nat.card (MulAction.stabilizer H12 Pbar) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact hOrbitMul.symm
    have hp4_dvd_H12 : p ^ 4 ∣ Nat.card H12 := by
      rw [hH12cardEq]
      convert Nat.mul_dvd_mul_left p hp3_dvd_stab using 1
      ring
    have hp4_dvd_G : p ^ 4 ∣ Nat.card G :=
      hp4_dvd_H12.trans (Subgroup.card_subgroup_dvd_card H12)
    have hp4_dvd_p3u : p ^ 4 ∣ p ^ 3 * u := by
      simpa [hm1, hGcard] using hp4_dvd_G
    exact (chapter2_claim12_prime_four_not_dvd_prime_cube_mul
      p u (Fact.out : Nat.Prime p) hu) hp4_dvd_p3u
  · exact hNR_le_H12

private theorem chapter2_claim12_delta_mem_right_complement
    {A U : Type*} [Group A] [Group U] [MulDistribMulAction A U]
    [IsMulCommutative U] (F J : Subgroup U) [IsInvariant A U J]
    (hcompl : F.IsComplement' J)
    (hfixed : ∀ (a : A) {u : U}, u ∈ F → a • u = u)
    (a : A) (u : U) : (a • u) * u⁻¹ ∈ J := by
  rcases (hcompl.existsUnique u).exists with ⟨⟨f, j⟩, hfj⟩
  have hcf : a • (f : U) = (f : U) := hfixed a f.property
  have hcj : a • (j : U) ∈ J :=
    (IsInvariant.invariant (A := A) (G := U) (H := J) a (j : U)).1
      j.property
  have hEq : (a • u) * u⁻¹ = (a • (j : U)) * ((j : U)⁻¹) := by
    rw [← hfj, smul_mul', hcf, mul_inv_rev]
    calc
      (f : U) * (a • (j : U)) * ((j : U)⁻¹ * (f : U)⁻¹) =
          ((f : U) * (f : U)⁻¹) *
            ((a • (j : U)) * (j : U)⁻¹) := by ac_rfl
      _ = (a • (j : U)) * ((j : U)⁻¹) := by simp
  rw [hEq]
  exact J.mul_mem hcj (J.inv_mem j.property)

private theorem chapter2_claim12_faithful_of_surjective_commutator
    {G U : Type*} [Group G] [Finite G] [Group U]
    (p : ℕ) [Fact p.Prime]
    (T P R CQ : Subgroup G) (R1 : Sylow p G) (TR1 : Subgroup R1)
    [MulDistribMulAction CQ R1] [MulDistribMulAction CQ U]
    (J : Subgroup U) (phi : U →* TR1)
    (hTcard : Nat.card T = p) (hPcard : Nat.card P = p)
    (hR_eq : R = T ⊔ P) (hTPdisj : Disjoint T P)
    (hTcentralP : T ≤ Subgroup.centralizer (P : Set G))
    (hCQcentralP : CQ ≤ Subgroup.centralizer (P : Set G))
    (hreg : ∀ A B : Subgroup G,
      A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
        ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
          ∃! d : G, d ∈ CQ ∧ B = rightConjugate A d)
    (hT_le_R1 : T ≤ (R1 : Subgroup G))
    (hTR1 : TR1 = T.subgroupOf (R1 : Subgroup G))
    (hphiJ_surj : ∀ z : TR1, ∃ j : J, phi (j : U) = z)
    (hphi_CQ : ∀ (c : CQ) (u : U),
      ((phi (c • u) : TR1) : R1) = c • ((phi u : TR1) : R1))
    (hsmul_coe : ∀ (c : CQ) (x : R1),
      ((c • x : R1) : G) = (c : G) * (x : G) * (c : G)⁻¹)
    (yP : P) (hyPne : yP ≠ 1) (c : CQ)
    (hfix : ∀ j : J, c • (j : U) = (j : U)) : c = 1 := by
  have hfixTR1 (z : TR1) : c • (z : R1) = (z : R1) := by
    rcases hphiJ_surj z with ⟨j, hj⟩
    calc
      c • (z : R1) = c • ((phi (j : U) : TR1) : R1) :=
        congrArg (fun w : R1 => c • w) (congrArg Subtype.val hj.symm)
      _ = ((phi (c • (j : U)) : TR1) : R1) := (hphi_CQ c (j : U)).symm
      _ = ((phi (j : U) : TR1) : R1) :=
        congrArg (fun u : U => ((phi u : TR1) : R1)) (hfix j)
      _ = (z : R1) := congrArg Subtype.val hj
  have hfixT (x : G) (hxT : x ∈ T) :
      (c : G) * x * (c : G)⁻¹ = x := by
    let xR1 : R1 := ⟨x, hT_le_R1 hxT⟩
    let xTR1 : TR1 := ⟨xR1, by rw [hTR1]; exact hxT⟩
    have hxR1 : c • xR1 = xR1 := hfixTR1 xTR1
    calc
      (c : G) * x * (c : G)⁻¹ = ((c • xR1 : R1) : G) :=
        (hsmul_coe c xR1).symm
      _ = (xR1 : G) := congrArg (fun z : R1 => (z : G)) hxR1
      _ = x := rfl
  exact chapter2_claim12_regular_complement_action_faithful
    p T P R CQ hTcard hPcard hR_eq hTPdisj hTcentralP hCQcentralP
      hreg yP hyPne c hfixT

private theorem chapter2_claim12_le_normalizer_map_comap_quotient
    {G U : Type*} [Group G] [Group U] (A R : Subgroup G)
    [MulDistribMulAction A R] [MulDistribMulAction A U]
    (q : R →* U) (J : Subgroup U) [IsInvariant A U J]
    (hcompat : ∀ (a : A) (x : R),
      a • q x = q (a • x))
    (hsmul_coe : ∀ (a : A) (x : R),
      (((a • x : R) : G)) = (a : G) * (x : G) * (a : G)⁻¹) :
    A ≤ Subgroup.normalizer
      ((J.comap q).map R.subtype : Set G) := by
  have hInv : IsInvariant A R (J.comap q) := by
    constructor
    intro a x
    change q x ∈ J ↔ q (a • x) ∈ J
    rw [← hcompat]
    exact IsInvariant.invariant (A := A) (G := U) (H := J) a (q x)
  exact chapter2_claim12_le_normalizer_map_of_isInvariant
    A R (J.comap q) hInv hsmul_coe

private theorem chapter2_claim12_subgroup_ne_complement_of_prime_card
    {U : Type*} [Group U] (p : ℕ) [Fact p.Prime]
    (L F J : Subgroup U) (hLcard : Nat.card L = p)
    (hL_le_F : L ≤ F) (hFJcompl : IsCompl F J) : L ≠ J := by
  intro heq
  have hL_le_J : L ≤ J := by rw [heq]
  have hdisjLJ : Disjoint L J := hFJcompl.disjoint.mono hL_le_F le_rfl
  have hLbot : L = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxInf : x ∈ L ⊓ J := ⟨hx, hL_le_J hx⟩
      rw [disjoint_iff.mp hdisjLJ] at hxInf
      exact hxInf
    · exact bot_le
  have hpOne : p = 1 := by rw [← hLcard, hLbot]; simp
  exact (Fact.out : p.Prime).ne_one hpOne

private theorem chapter2_claim12_fix_image_iff_mem_normalizer
    {G U : Type*} [Group G] [Group U] [Finite U]
    (H R K : Subgroup G)
    [MulDistribMulAction H K] [MulDistribMulAction H U]
    [MulAction H (Subgroup U)]
    (q : K →* U) (L : Subgroup U)
    (hR_le_K : R ≤ K)
    (hpre : L.comap q = R.subgroupOf K)
    (hcompat : ∀ (a : H) (x : K), a • q x = q (a • x))
    (hsmul_coe : ∀ (a : H) (x : K),
      ((a • x : K) : G) = (a : G) * (x : G) * (a : G)⁻¹)
    (hq_surj : Function.Surjective q)
    (hsmul_mem : ∀ (a : H) {u : U}, u ∈ L → a • u ∈ a • L)
    (hmem_smul : ∀ (a : H) {u : U}, u ∈ a • L →
      ∃ v : U, v ∈ L ∧ u = a • v)
    (hcard_smul : ∀ a : H, Nat.card (a • L : Subgroup U) = Nat.card L)
    (a : H) : a • L = L ↔ (a : G) ∈ Subgroup.normalizer (R : Set G) := by
  have hforward (b : H) (hbfix : b • L = L) :
      ∀ x : G, x ∈ R → (b : G) * x * (b : G)⁻¹ ∈ R := by
    intro x hxR
    let xK : K := ⟨x, hR_le_K hxR⟩
    have hxPre : xK ∈ L.comap q := by
      rw [hpre]
      exact hxR
    have hqMem : b • q xK ∈ L := by
      have hmem := hsmul_mem b hxPre
      rwa [hbfix] at hmem
    rw [hcompat] at hqMem
    have hbPre : b • xK ∈ L.comap q := hqMem
    rw [hpre] at hbPre
    change ((b • xK : K) : G) ∈ R at hbPre
    rw [hsmul_coe] at hbPre
    exact hbPre
  constructor
  · intro hfix
    have hfixInv : a⁻¹ • L = L := by
      calc
        a⁻¹ • L = a⁻¹ • (a • L) := by rw [hfix]
        _ = L := inv_smul_smul a L
    apply chapter2_claim12_mem_normalizer_of_conj_mem R (a : G)
    · exact hforward a hfix
    · exact hforward a⁻¹ hfixInv
  · intro haNorm
    apply Subgroup.eq_of_le_of_card_ge
    · intro u hu
      rcases hmem_smul a hu with ⟨v, hv, rfl⟩
      obtain ⟨x, rfl⟩ := hq_surj v
      rw [hcompat]
      have hxPre : x ∈ L.comap q := hv
      rw [hpre] at hxPre
      have hconjR : (a : G) * (x : G) * (a : G)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp haNorm (x : G)).1 hxPre
      change a • x ∈ L.comap q
      rw [hpre]
      change ((a • x : K) : G) ∈ R
      rw [hsmul_coe]
      exact hconjR
    · exact (hcard_smul a).symm.le

private theorem chapter2_claim12_fix_image_iff_mem_normalizer_compHom
    {G U : Type*} [Group G] [Group U] [Finite U]
    (H R K : Subgroup G)
    [MulDistribMulAction H K] [MulDistribMulAction H U]
    (aut : H →* MulAut U) (haut : ∀ (a : H) (u : U), aut a u = a • u)
    (q : K →* U) (L : Subgroup U)
    (hR_le_K : R ≤ K) (hpre : L.comap q = R.subgroupOf K)
    (hcompat : ∀ (a : H) (x : K), a • q x = q (a • x))
    (hsmul_coe : ∀ (a : H) (x : K),
      ((a • x : K) : G) = (a : G) * (x : G) * (a : G)⁻¹)
    (hq_surj : Function.Surjective q) (a : H) :
    letI : MulAction H (Subgroup U) := MulAction.compHom _ aut
    a • L = L ↔ (a : G) ∈ Subgroup.normalizer (R : Set G) := by
  let : MulAction H (Subgroup U) := MulAction.compHom _ aut
  exact chapter2_claim12_fix_image_iff_mem_normalizer
    H R K q L hR_le_K hpre hcompat hsmul_coe hq_surj
      (fun b u hu => by
        change b • u ∈ L.map (aut b).toMonoidHom
        exact Subgroup.mem_map.mpr ⟨u, hu, haut b u⟩)
      (fun b u hu => by
        change u ∈ L.map (aut b).toMonoidHom at hu
        rcases Subgroup.mem_map.mp hu with ⟨v, hv, hvu⟩
        refine ⟨v, hv, ?_⟩
        exact hvu.symm.trans (haut b v))
      (fun b => Nat.card_congr ((aut b).subgroupMap L).toEquiv.symm) a

private theorem chapter2_claim12_comap_map_quotient_eq_subgroupOf_sup
    {G : Type*} [Group G] (K T P R : Subgroup G)
    (N A : Subgroup K) [N.Normal]
    (hN : N = T.subgroupOf K) (hA : A = P.subgroupOf K)
    (hT_le_K : T ≤ K) (hP_le_K : P ≤ K) (hR : R = T ⊔ P) :
    (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) =
      R.subgroupOf K := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', hN, hA, sup_comm,
    ← Subgroup.subgroupOf_sup hT_le_K hP_le_K, ← hR]

private theorem chapter2_claim12_restrict_surjective_of_complement_ker
    {U T : Type*} [Group U] [Finite U] [Group T] [Finite T]
    (F J : Subgroup U) (phi : U →* T)
    (hker : phi.ker = F) (hcompl : IsCompl F J)
    (hcard : Nat.card J = Nat.card T) :
    Function.Surjective (phi.comp J.subtype) := by
  have hinj : Function.Injective (phi.comp J.subtype) := by
    intro a b hab
    change phi (a : U) = phi (b : U) at hab
    have hdiffKer : (a : U) * (b : U)⁻¹ ∈ phi.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    have hdiffF : (a : U) * (b : U)⁻¹ ∈ F := by
      rw [← hker]
      exact hdiffKer
    have hdiffJ : (a : U) * (b : U)⁻¹ ∈ J :=
      J.mul_mem a.property (J.inv_mem b.property)
    have hdiffBot : (a : U) * (b : U)⁻¹ ∈ (⊥ : Subgroup U) :=
      (Subgroup.disjoint_def.mp hcompl.disjoint) hdiffF hdiffJ
    exact Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hdiffBot))
  exact ((Nat.bijective_iff_injective_and_card (phi.comp J.subtype)).2
    ⟨hinj, hcard⟩).2

private theorem chapter2_claim12_construct_local_index_subgroup
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (H12 NR R1 T1 P CQ : Subgroup G)
    (hH12_eq_NR : H12 = NR) (hNR_le_H12 : NR ≤ H12)
    (hR1_le_NR : R1 ≤ NR) (hCQ_le_NR : CQ ≤ NR)
    (hCQ_le_normalizer_R1 : CQ ≤ Subgroup.normalizer (R1 : Set G))
    (hT1_le_R1 : T1 ≤ R1)
    (hR1card : Nat.card R1 = p ^ 3) (hCQcard : Nat.card CQ = p - 1)
    (hNRcard : Nat.card NR = p ^ 3 * (p - 1))
    (hR1_eq_T1_sup_P : R1 = T1 ⊔ P) (hP_le_R1 : P ≤ R1)
    (hR1_le_normalizer_T1 : R1 ≤ Subgroup.normalizer (T1 : Set G))
    (hCQ_le_normalizer_T1 : CQ ≤ Subgroup.normalizer (T1 : Set G))
    (hCQ_le_centralizer_P : CQ ≤ Subgroup.centralizer (P : Set G))
    (hT1card : Nat.card T1 = p ^ 2) :
    ∃ M : Subgroup H12, M.Normal ∧ Nat.card (H12 ⧸ M) = p := by
  have hpPredPos : 0 < p - 1 := by
    have hp2 := (Fact.out : p.Prime).two_le
    omega
  have hpPredLt : p - 1 < p := by
    have hp2 := (Fact.out : p.Prime).two_le
    omega
  have hCQ_le_H12 : CQ ≤ H12 := hCQ_le_NR.trans hNR_le_H12
  have hR1_le_H12 : R1 ≤ H12 := hR1_le_NR.trans hNR_le_H12
  have hT1_le_H12 : T1 ≤ H12 := hT1_le_R1.trans hR1_le_H12
  have hR1_disj_CQ : Disjoint R1 CQ := by
    rw [disjoint_iff]
    let I : Subgroup G := R1 ⊓ CQ
    have hIdvdR1 : Nat.card I ∣ p ^ 3 := by
      rw [← hR1card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hIdvdCQ : Nat.card I ∣ p - 1 := by
      rw [← hCQcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (p ^ 3) (p - 1) :=
      Nat.Coprime.pow_left 3
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt hpPredPos hpPredLt))
    exact Subgroup.card_eq_one.mp
      (Nat.eq_one_of_dvd_coprimes hcop hIdvdR1 hIdvdCQ)
  have hR1_sup_CQ_card :
      Nat.card (R1 ⊔ CQ : Subgroup G) = p ^ 3 * (p - 1) := by
    calc
      Nat.card (R1 ⊔ CQ : Subgroup G) = Nat.card R1 * Nat.card CQ :=
        chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          R1 CQ hCQ_le_normalizer_R1 hR1_disj_CQ
      _ = p ^ 3 * (p - 1) := by rw [hR1card, hCQcard]
  have hNR_eq_R1_sup_CQ : NR = R1 ⊔ CQ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le hR1_le_NR hCQ_le_NR
    · rw [hR1_sup_CQ_card, hNRcard]
  let M0 : Subgroup G := T1 ⊔ CQ
  have hM0_le_H12 : M0 ≤ H12 := sup_le hT1_le_H12 hCQ_le_H12
  have hP_le_normalizer_CQ : P ≤ Subgroup.normalizer (CQ : Set G) := by
    intro x hxP
    apply centralizer_le_normalizer CQ
    rw [Subgroup.mem_centralizer_iff]
    intro c hcCQ
    exact (Subgroup.mem_centralizer_iff.mp
      (hCQ_le_centralizer_P hcCQ) x hxP).symm
  have hP_le_normalizer_M0 : P ≤ Subgroup.normalizer (M0 : Set G) := by
    intro x hxP
    exact chapter2_claim12_mem_normalizer_sup
      (hR1_le_normalizer_T1 (hP_le_R1 hxP))
      (hP_le_normalizer_CQ hxP)
  have hT1_le_normalizer_M0 : T1 ≤ Subgroup.normalizer (M0 : Set G) :=
    le_sup_left.trans (Subgroup.le_normalizer (H := M0))
  have hCQ_le_normalizer_M0 : CQ ≤ Subgroup.normalizer (M0 : Set G) := by
    intro c hc
    exact chapter2_claim12_mem_normalizer_sup (hCQ_le_normalizer_T1 hc)
      (Subgroup.le_normalizer (H := CQ) hc)
  have hR1_le_normalizer_M0 : R1 ≤ Subgroup.normalizer (M0 : Set G) := by
    rw [hR1_eq_T1_sup_P]
    exact sup_le hT1_le_normalizer_M0 hP_le_normalizer_M0
  have hH12_le_normalizer_M0 : H12 ≤ Subgroup.normalizer (M0 : Set G) := by
    rw [hH12_eq_NR, hNR_eq_R1_sup_CQ]
    exact sup_le hR1_le_normalizer_M0 hCQ_le_normalizer_M0
  have hM0normal : (M0.subgroupOf H12).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM0_le_H12).2
      hH12_le_normalizer_M0
  have hT1_disj_CQ : Disjoint T1 CQ := hR1_disj_CQ.mono hT1_le_R1 le_rfl
  have hM0card : Nat.card M0 = p ^ 2 * (p - 1) := by
    calc
      Nat.card M0 = Nat.card T1 * Nat.card CQ :=
        chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          T1 CQ hCQ_le_normalizer_T1 hT1_disj_CQ
      _ = p ^ 2 * (p - 1) := by rw [hT1card, hCQcard]
  let M : Subgroup H12 := M0.subgroupOf H12
  have hMcard : Nat.card M = p ^ 2 * (p - 1) := by
    calc
      Nat.card M = Nat.card M0 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM0_le_H12).toEquiv
      _ = p ^ 2 * (p - 1) := hM0card
  have hH12card : Nat.card H12 = p ^ 3 * (p - 1) := by
    rw [hH12_eq_NR]
    exact hNRcard
  have hMindex : M.index = p := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := M))
    calc
      Nat.card M * M.index = Nat.card H12 := M.card_mul_index
      _ = p ^ 3 * (p - 1) := hH12card
      _ = (p ^ 2 * (p - 1)) * p := by ring
      _ = Nat.card M * p := congrArg (fun n : ℕ => n * p) hMcard.symm
  refine ⟨M, hM0normal, ?_⟩
  calc
    Nat.card (H12 ⧸ M) = M.index := (Subgroup.index_eq_card M).symm
    _ = p := hMindex

set_option backward.isDefEq.respectTransparency false in
/-- After the Sylow subgroup and Hall--Wielandt quotient are fixed, construct
the local normal subgroup of index `p`. -/
private theorem chapter2_claim12_local_index_after_sylow
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma R T : Subgroup G) (t s : G) (p m : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (_hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (_hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m)
    (hR : R = T ⊔ P ∧
        Disjoint T P ∧
          T ≤ Subgroup.centralizer (P : Set G) ∧
            (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
              W ⊓ Subgroup.centralizer (P : Set G)) ≤
                Subgroup.normalizer (T : Set G) ∧
              Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
                ∀ A B : Subgroup G,
                  A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                      ∃! c : G,
                        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                          B = rightConjugate A c)
    (hT_inverted : ∀ x : G, x ∈ T →
      rightConjugateElem x s = x⁻¹)
    (hCaseOne :
      Subgroup.centralizer (P : Set G) ≤
          Subgroup.normalizer (R : Set G) ∧
        Nat.card R = p ^ (m + 1) ∧
          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
            p ^ m ∧
          ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
            (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
              R.subgroupOf (Subgroup.centralizer (P : Set G)))
    (hCaseOneMOne :
      m = 1 →
        s ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
          (∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (P : Set G) →
            q * s = s * q) ∧
          (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = ⊥ ∧
          ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
            ∃ r q : G, r ∈ R ∧
              q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ g = r * q)
    (hcase10_1 :
      ¬ p ∣ Nat.card Sigma ∧ (∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧ Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u))
    (hm1 : m = 1)
    (hNRcardFactor : Nat.card (Subgroup.normalizer (R : Set G)) =
      p ^ m * Nat.card (Subgroup.centralizer (P : Set G)))
    (hNR_le_normalizer_T : Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (T : Set G))
    (R1 : Sylow p G) (hR_le_R1 : R ≤ (R1 : Subgroup G))
    (hR1card : Nat.card R1 = p ^ 3) :
    let H12 : Subgroup G := Subgroup.normalizer ((R1 : Subgroup G) : Set G)
    ∃ M : Subgroup H12, M.Normal ∧ Nat.card (H12 ⧸ M) = p := by
  let H12 : Subgroup G := Subgroup.normalizer ((R1 : Subgroup G) : Set G)
  change ∃ M : Subgroup H12, M.Normal ∧ Nat.card (H12 ⧸ M) = p
  classical
  let : Fact (Nat.Prime p) := ⟨hch.B1.p_prime⟩
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let NR : Subgroup G := Subgroup.normalizer (R : Set G)
  let CQ : Subgroup G := Q ⊓ Subgroup.centralizer (P : Set G)
  have hp2 : 2 ≤ p := hch.B1.p_prime.two_le
  have hpPredPos : 0 < p - 1 := by omega
  have hpPredLt : p - 1 < p := by omega
  rcases hCaseOneMOne hm1 with
    ⟨hsCQ, hCQCommS, hSigmaBot, hCdecomp⟩
  have hP_le_C : P ≤ C := by
    let : IsMulCommutative P :=
      (isCyclic_of_prime_card hch.B1.P_card).isMulCommutative
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hP_le_R : P ≤ R := by rw [hR.1]; exact le_sup_right
  have hR_le_C : R ≤ C := by
    rw [hR.1]
    exact sup_le hR.2.2.1 hP_le_C
  have hC_le_NR : C ≤ NR := by simpa [C, NR] using hCaseOne.1
  have hP_le_normalizer_T : P ≤ Subgroup.normalizer (T : Set G) := by
    intro y hyP
    apply centralizer_le_normalizer T
    rw [Subgroup.mem_centralizer_iff]
    intro x hxT
    exact ((Subgroup.mem_centralizer_iff.mp (hR.2.2.1 hxT)) y hyP).symm
  have hTcard : Nat.card T = p := by
    have hprod : Nat.card R = Nat.card T * Nat.card P := by
      rw [hR.1]
      exact chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        T P hP_le_normalizer_T hR.2.1
    apply Nat.eq_of_mul_eq_mul_right hch.B1.p_prime.pos
    calc
      Nat.card T * p = Nat.card T * Nat.card P := by rw [hch.B1.P_card]
      _ = Nat.card R := hprod.symm
      _ = p ^ (m + 1) := hCaseOne.2.1
      _ = p ^ 2 := by rw [hm1]
      _ = p * p := by rw [pow_two]
  have hCQcard : Nat.card CQ = p - 1 := by
    have h := hCaseOne.2.2.1
    change Nat.card CQ + 1 = p ^ m at h
    rw [hm1, pow_one] at h
    omega
  have hRcardTwo : Nat.card R = p ^ 2 := by
    simpa [hm1] using hCaseOne.2.1
  have hR_disj_CQ : Disjoint R CQ := by
    let I : Subgroup G := R ⊓ CQ
    have hIdvdR : Nat.card I ∣ p ^ 2 := by
      rw [← hRcardTwo]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hIdvdCQ : Nat.card I ∣ p - 1 := by
      rw [← hCQcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hpNotDvdPred : ¬ p ∣ p - 1 :=
      Nat.not_dvd_of_pos_of_lt hpPredPos hpPredLt
    have hcop : Nat.Coprime (p ^ 2) (p - 1) :=
      Nat.Coprime.pow_left 2
        (hch.B1.p_prime.coprime_iff_not_dvd.mpr hpNotDvdPred)
    have hIcard : Nat.card I = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hIdvdR hIdvdCQ
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp hIcard
  have hCQ_le_C : CQ ≤ C := by exact inf_le_right
  have hCQ_le_NR : CQ ≤ NR := hCQ_le_C.trans hC_le_NR
  have hsupC : R ⊔ CQ = C := by
    apply le_antisymm (sup_le hR_le_C hCQ_le_C)
    intro g hgC
    rcases hCdecomp g (by simpa [C] using hgC) with ⟨r, q, hrR, hqCQ, rfl⟩
    exact Subgroup.mul_mem_sup hrR hqCQ
  have hCcard : Nat.card C = p ^ 2 * (p - 1) := by
    calc
      Nat.card C = Nat.card (R ⊔ CQ : Subgroup G) := by rw [hsupC]
      _ = Nat.card R * Nat.card CQ :=
        chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          R CQ hCQ_le_NR hR_disj_CQ
      _ = p ^ 2 * (p - 1) := by rw [hRcardTwo, hCQcard]
  have hNRcard : Nat.card NR = p ^ 3 * (p - 1) := by
    calc
      Nat.card NR = p ^ m * Nat.card C := by
        simpa [NR, C] using hNRcardFactor
      _ = p ^ 1 * (p ^ 2 * (p - 1)) := by rw [hm1, hCcard]
      _ = p ^ 3 * (p - 1) := by ring
  let RR1 : Subgroup R1 := R.subgroupOf (R1 : Subgroup G)
  have hRR1card : Nat.card RR1 = p ^ 2 := by
    calc
      Nat.card RR1 = Nat.card R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le_R1).toEquiv
      _ = p ^ 2 := hRcardTwo
  have hRR1index : RR1.index = p := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hch.B1.p_prime.pos 2)
    calc
      p ^ 2 * RR1.index = Nat.card RR1 * RR1.index := by rw [hRR1card]
      _ = Nat.card R1 := RR1.card_mul_index
      _ = p ^ 3 := hR1card
      _ = p ^ 2 * p := by rw [pow_succ]
  have hRR1normal : RR1.Normal :=
    chapter2_claim12_normal_of_index_eq_prime_of_isPGroup
      R1.isPGroup' RR1 hRR1index
  have hR1_le_NR : (R1 : Subgroup G) ≤ NR := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hR_le_R1).mp hRR1normal
  let R1N : Subgroup NR := (R1 : Subgroup G).subgroupOf NR
  have hR1Ncard : Nat.card R1N = p ^ 3 := by
    calc
      Nat.card R1N = Nat.card R1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR1_le_NR).toEquiv
      _ = p ^ 3 := hR1card
  have hR1Nindex : R1N.index = p - 1 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hch.B1.p_prime.pos 3)
    calc
      p ^ 3 * R1N.index = Nat.card R1N * R1N.index := by rw [hR1Ncard]
      _ = Nat.card NR := R1N.card_mul_index
      _ = p ^ 3 * (p - 1) := hNRcard
  have hpNotDvdPred : ¬ p ∣ p - 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hR1Np : IsPGroup p R1N := IsPGroup.of_card hR1Ncard
  let R1Syl : Sylow p NR := hR1Np.toSylow (by simpa [hR1Nindex] using hpNotDvdPred)
  have hSylowCard : Nat.card (Sylow p NR) = 1 := by
    have hdiv : Nat.card (Sylow p NR) ∣ p - 1 := by
      simpa [R1Syl, hR1Nindex] using R1Syl.card_dvd_index
    have hle : Nat.card (Sylow p NR) ≤ p - 1 :=
      Nat.le_of_dvd hpPredPos hdiv
    have hlt : Nat.card (Sylow p NR) < p := hle.trans_lt hpPredLt
    exact (card_sylow_modEq_one p NR).eq_of_lt_of_lt hlt hch.B1.p_prime.one_lt
  let : Subsingleton (Sylow p NR) := (Nat.card_eq_one_iff_unique.mp hSylowCard).1
  have hR1Nnormal : R1N.Normal := by
    simpa [R1Syl] using Sylow.normal_of_subsingleton R1Syl
  have hNR_le_H12 : NR ≤ H12 := by
    change NR ≤ Subgroup.normalizer ((R1 : Subgroup G) : Set G)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hR1_le_NR).mp hR1Nnormal
  have hT_le_R1 : T ≤ (R1 : Subgroup G) :=
    (show T ≤ R from hR.1.symm ▸ le_sup_left).trans hR_le_R1
  have hR1_le_normalizer_T :
      (R1 : Subgroup G) ≤ Subgroup.normalizer (T : Set G) :=
    hR1_le_NR.trans hNR_le_normalizer_T
  let TR1 : Subgroup R1 := T.subgroupOf (R1 : Subgroup G)
  have hTR1normal : TR1.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT_le_R1).mpr
      hR1_le_normalizer_T
  let : TR1.Normal := hTR1normal
  have hTR1card : Nat.card TR1 = p := by
    calc
      Nat.card TR1 = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_R1).toEquiv
      _ = p := hTcard
  have hR1_not_le_C : ¬ (R1 : Subgroup G) ≤ C := by
    intro hR1_le_C
    rcases hCaseOne.2.2.2 with ⟨RC, hRC⟩
    let R1C : Subgroup C := (R1 : Subgroup G).subgroupOf C
    have hR1Ccard : Nat.card R1C = p ^ 3 := by
      calc
        Nat.card R1C = Nat.card R1 :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR1_le_C).toEquiv
        _ = p ^ 3 := hR1card
    have hR1Cp : IsPGroup p R1C := IsPGroup.of_card hR1Ccard
    have hRC_le_R1C : (RC : Subgroup C) ≤ R1C := by
      rw [hRC]
      intro x hxR
      exact hR_le_R1 hxR
    have hEq : R1C = (RC : Subgroup C) :=
      RC.is_maximal' hR1Cp hRC_le_R1C
    have hcardEq := congrArg (fun A : Subgroup C => Nat.card A) hEq
    have hRCcard : Nat.card (RC : Subgroup C) = p ^ 2 := by
      calc
        Nat.card (RC : Subgroup C) = Nat.card (R.subgroupOf C) := by rw [hRC]
        _ = Nat.card R :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le_C).toEquiv
        _ = p ^ 2 := hRcardTwo
    change Nat.card R1C = Nat.card (RC : Subgroup C) at hcardEq
    rw [hR1Ccard, hRCcard] at hcardEq
    have h32 : (3 : ℕ) = 2 :=
      Nat.pow_right_injective hch.B1.p_prime.one_lt hcardEq
    omega
  have hR1noncomm : ¬ IsMulCommutative R1 := by
    intro hcomm
    apply hR1_not_le_C
    let : IsMulCommutative R1 := hcomm
    intro x hxR1
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    let xR1 : R1 := ⟨x, hxR1⟩
    let yR1 : R1 := ⟨y, hR_le_R1 (hP_le_R hyP)⟩
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := R1)).comm xR1 yR1)).symm
  have hTR1index : TR1.index = p ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hch.B1.p_prime.pos
    calc
      p * TR1.index = Nat.card TR1 * TR1.index := by rw [hTR1card]
      _ = Nat.card R1 := TR1.card_mul_index
      _ = p ^ 3 := hR1card
      _ = p * p ^ 2 := by rw [pow_succ']
  let U := R1 ⧸ TR1
  have hUcard : Nat.card U = p ^ 2 := by
    calc
      Nat.card U = TR1.index := (Subgroup.index_eq_card TR1).symm
      _ = p ^ 2 := hTR1index
  have hUcomm : IsMulCommutative U :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hUcard
  have hcomm_le : _root_.commutator R1 ≤ TR1 :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hUcomm
  let Kcomm : Subgroup TR1 := (_root_.commutator R1).subgroupOf TR1
  have hcomm_ne_bot : _root_.commutator R1 ≠ ⊥ := by
    intro hbot
    apply hR1noncomm
    have htop_le_center :
        (⊤ : Subgroup R1) ≤ Subgroup.centralizer (⊤ : Subgroup R1) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      simpa [_root_.commutator_def] using hbot
    refine ⟨⟨fun a b => ?_⟩⟩
    exact ((Subgroup.mem_centralizer_iff.mp
      (htop_le_center (by trivial))) b (by trivial)).symm
  have hKcomm_ne_bot : Kcomm ≠ ⊥ := by
    intro hKbot
    apply hcomm_ne_bot
    apply le_antisymm ?_ bot_le
    intro x hx
    let xT : TR1 := ⟨x, hcomm_le hx⟩
    have hxK : xT ∈ Kcomm := hx
    have hxT_one : xT = 1 := by
      rw [hKbot] at hxK
      simpa using hxK
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxT_one)
  let : Fact (Nat.Prime (Nat.card TR1)) := ⟨by rw [hTR1card]; exact hch.B1.p_prime⟩
  have hKcomm_top : Kcomm = ⊤ :=
    (Kcomm.eq_bot_or_eq_top_of_prime_card).resolve_left hKcomm_ne_bot
  have hcomm_eq_TR1 : _root_.commutator R1 = TR1 := by
    apply le_antisymm hcomm_le
    intro x hxT
    let xT : TR1 := ⟨x, hxT⟩
    have hxK : xT ∈ Kcomm := by rw [hKcomm_top]; trivial
    exact hxK
  have hT_eq_commutator_map :
      T = (_root_.commutator R1).map (R1 : Subgroup G).subtype := by
    rw [hcomm_eq_TR1, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hT_le_R1]
  have hH12_le_normalizer_T : H12 ≤ Subgroup.normalizer (T : Set G) := by
    change Subgroup.normalizer ((R1 : Subgroup G) : Set G) ≤
      Subgroup.normalizer (T : Set G)
    rw [hT_eq_commutator_map]
    exact chapter2_claim12_normalizer_le_normalizer_map_subtype_of_characteristic
      (R1 : Subgroup G) (_root_.commutator R1)
  let : Fact (IsPGroup p R1) := ⟨R1.isPGroup'⟩
  have hTR1center : TR1 ≤ Subgroup.center R1 :=
    normal_subgroup_card_eq_prime_le_center TR1 hTR1card
  have hsNR : s ∈ NR := hCQ_le_NR hsCQ
  have hsH12 : s ∈ H12 := hNR_le_H12 hsNR
  let A : Subgroup G := Subgroup.zpowers s
  have hA_le_H12 : A ≤ H12 := by
    rw [Subgroup.zpowers_le]
    exact hsH12
  have hA_norm_R1 : A ≤ Subgroup.normalizer ((R1 : Subgroup G) : Set G) := by
    simpa [H12] using hA_le_H12
  have hA_norm_T : A ≤ Subgroup.normalizer (T : Set G) :=
    hA_le_H12.trans hH12_le_normalizer_T
  let : Subgroup.Normalizes A (R1 : Subgroup G) := ⟨hA_norm_R1⟩
  have hTR1invA : IsInvariant A R1 TR1 :=
    isInvariant_subgroupOf_of_le_normalizer
      hA_norm_R1 hA_norm_T hT_le_R1
  let : MulDistribMulAction A U :=
    quotientMulDistribMulAction (A := A) (G := R1) TR1 hTR1invA
  let : IsMulCommutative U := hUcomm
  have hsOrder : orderOf s = 2 :=
    orderOf_eq_prime_iff.mpr
      ⟨hch.section3.s_involution.sq_eq_one,
        hch.section3.s_involution.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    rw [Nat.card_zpowers, hsOrder]
  have hpOdd : Odd p := by
    have hP_le_D : P ≤ D := by
      refine hch.B1.P_le_V.trans ?_
      rw [hch.section3.section2.V_eq]
      exact inf_le_left
    simpa [hch.B1.P_card] using
      hch.section3.section2.hA.A1.D_odd.of_dvd_nat
        (Subgroup.card_dvd_of_le hP_le_D)
  have hUodd : Odd (Nat.card U) := by
    rw [hUcard]
    exact hpOdd.pow
  have hcopAU : Nat.Coprime (Nat.card A) (Nat.card U) := by
    rw [hAcard]
    exact hUodd.coprime_two_left
  let : IsMulCommutative U := hUcomm
  have hsolvU : Group.IsSolvable U := by
    exact Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  let Ffix : Subgroup U := fixedPointSubgroup A U
  let Jcomm : Subgroup U := commutatorAction (A := A) (G := U)
  have hFJcompl : IsCompl Ffix Jcomm := by
    simpa [Ffix, Jcomm] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := U) (A := A) hsolvU hcopAU (inferInstance : IsMulCommutative U))
  let qU : R1 →* U := QuotientGroup.mk' TR1
  have hP_le_R1 : P ≤ (R1 : Subgroup G) := hP_le_R.trans hR_le_R1
  let PR1 : Subgroup R1 := P.subgroupOf (R1 : Subgroup G)
  have hPR1card : Nat.card PR1 = p := by
    calc
      Nat.card PR1 = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_R1).toEquiv
      _ = p := hch.B1.P_card
  have hTR1_disj_PR1 : Disjoint TR1 PR1 := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxP
    apply Subtype.ext
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hR.2.1) hxT hxP
    simpa using hxbot
  let Pbar : Subgroup U := PR1.map qU
  have hqU_inj_PR1 : Function.Injective (fun x : PR1 => qU x) := by
    intro x y hxy
    apply Subtype.ext
    have hdivT : (x : R1) / (y : R1) ∈ TR1 :=
      QuotientGroup.eq_iff_div_mem.mp hxy
    have hdivP : (x : R1) / (y : R1) ∈ PR1 :=
      PR1.div_mem x.property y.property
    have hdivBot : (x : R1) / (y : R1) ∈ (⊥ : Subgroup R1) :=
      (Subgroup.disjoint_def.mp hTR1_disj_PR1) hdivT hdivP
    exact div_eq_one.mp (Subgroup.mem_bot.mp hdivBot)
  have hPbarcard : Nat.card Pbar = p := by
    let toPbar : PR1 → Pbar := fun x =>
      ⟨qU x, Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩
    have hto_inj : Function.Injective toPbar := by
      intro x y hxy
      exact hqU_inj_PR1 (congrArg Subtype.val hxy)
    have hto_surj : Function.Surjective toPbar := by
      intro z
      rcases z.property with ⟨x, hx, hzx⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hzx
    calc
      Nat.card Pbar = Nat.card PR1 :=
        Nat.card_congr (Equiv.ofBijective toPbar ⟨hto_inj, hto_surj⟩).symm
      _ = p := hPR1card
  have hPbar_le_Ffix : Pbar ≤ Ffix := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hxP, rfl⟩
    change ∀ a : A, a • qU x = qU x
    intro a
    let sA : A := ⟨s, Subgroup.mem_zpowers s⟩
    apply smul_eq_self_of_mem_zpowers (y := sA) ?_ ?_
    · rcases Subgroup.mem_zpowers_iff.mp a.property with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    · change qU (sA • x) = qU x
      apply congrArg qU
      apply Subtype.ext
      change s * (x : G) * s⁻¹ = (x : G)
      have hsComm : s * (x : G) = (x : G) * s :=
        ((Subgroup.mem_centralizer_iff.mp hsCQ.2) (x : G) hxP).symm
      rw [hsComm]
      simp [mul_assoc]
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hpOne : p = 1 := by
      rw [← hch.B1.P_card, hPbot]
      simp
    exact hch.B1.p_prime.ne_one hpOne
  obtain ⟨yP, hyPne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let : IsMulCommutative P :=
    (isCyclic_of_prime_card hch.B1.P_card).isMulCommutative
  let yR1 : R1 := ⟨(yP : G), hP_le_R1 yP.property⟩
  obtain ⟨phi, hphi⟩ :=
    chapter2_claim12_commutator_quotient_hom TR1
      (by rw [hcomm_eq_TR1]) hTR1center yR1
  have hphi_range_ne_bot : phi.range ≠ ⊥ := by
    intro hrange
    apply hR1_not_le_C
    intro x hxR1
    rw [Subgroup.mem_centralizer_iff]
    intro z hzP
    let xR1 : R1 := ⟨x, hxR1⟩
    have hphi_mem : phi (qU xR1) ∈ phi.range := ⟨qU xR1, rfl⟩
    have hphi_one : phi (qU xR1) = 1 := by
      rw [hrange] at hphi_mem
      exact Subgroup.mem_bot.mp hphi_mem
    have hcomm_one : ⁅xR1, yR1⁆ = 1 := by
      rw [hphi xR1] at hphi_one
      exact congrArg Subtype.val hphi_one
    have hxy : x * (yP : G) = (yP : G) * x := by
      simpa [xR1, yR1] using congrArg Subtype.val
        (commutatorElement_eq_one_iff_mul_comm.mp hcomm_one)
    have hzpow : (⟨z, hzP⟩ : P) ∈ Subgroup.zpowers yP :=
      mem_zpowers_of_prime_card (G := P) (p := p) hch.B1.P_card
        (g := yP) (g' := ⟨z, hzP⟩) hyPne
    rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨n, hnP⟩
    have hn : (yP : G) ^ n = z := congrArg Subtype.val hnP
    have hcommxy : Commute x (yP : G) := hxy
    have hcommPow := hcommxy.zpow_right n
    simpa [hn] using hcommPow.eq.symm
  have hphi_range_top : phi.range = ⊤ :=
    (phi.range.eq_bot_or_eq_top_of_prime_card).resolve_left hphi_range_ne_bot
  have hphi_surj : Function.Surjective phi := by
    intro z
    have hz : z ∈ phi.range := by rw [hphi_range_top]; trivial
    rcases hz with ⟨u, hu⟩
    exact ⟨u, hu⟩
  have hphi_ker_card : Nat.card phi.ker = p := by
    have hquotCard : Nat.card (U ⧸ phi.ker) = p := by
      calc
        Nat.card (U ⧸ phi.ker) = Nat.card phi.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange phi).toEquiv
        _ = Nat.card TR1 := by rw [hphi_range_top]; simp
        _ = p := hTR1card
    apply Nat.eq_of_mul_eq_mul_left hch.B1.p_prime.pos
    calc
      p * Nat.card phi.ker = Nat.card (U ⧸ phi.ker) * Nat.card phi.ker := by
        rw [hquotCard]
      _ = Nat.card U :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := phi.ker)).symm
      _ = p ^ 2 := hUcard
      _ = p * p := by rw [pow_two]
  have hPbar_le_ker : Pbar ≤ phi.ker := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hxP, rfl⟩
    rw [MonoidHom.mem_ker, hphi]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr <| by
      let xP : P := ⟨(x : G), hxP⟩
      apply Subtype.ext
      simpa [xP, yR1] using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := P)).comm xP yP)
  have hphi_ker_eq_Pbar : phi.ker = Pbar := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hPbar_le_ker
    rw [hPbarcard, hphi_ker_card]
  let sA : A := ⟨s, Subgroup.mem_zpowers s⟩
  have hsA_sq : sA * sA = 1 := by
    apply Subtype.ext
    change s * s = 1
    simpa only [pow_two] using hch.section3.s_involution.sq_eq_one
  have hphi_smul (u : U) : phi (sA • u) = (phi u)⁻¹ := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective TR1 u
    change phi (qU (sA • x)) = (phi (qU x))⁻¹
    rw [hphi, hphi]
    apply Subtype.ext
    let alpha : R1 ≃* R1 := MulDistribMulAction.toMulAut A R1 sA
    have hyfix : alpha yR1 = yR1 := by
      apply Subtype.ext
      change s * (yP : G) * s⁻¹ = (yP : G)
      have hsy : s * (yP : G) = (yP : G) * s :=
        ((Subgroup.mem_centralizer_iff.mp hsCQ.2)
          (yP : G) yP.property).symm
      rw [hsy]
      simp [mul_assoc]
    have hmap : ⁅alpha x, yR1⁆ = alpha ⁅x, yR1⁆ := by
      calc
        ⁅alpha x, yR1⁆ = ⁅alpha x, alpha yR1⁆ := by rw [hyfix]
        _ = alpha ⁅x, yR1⁆ :=
          (map_commutatorElement
            (f := alpha.toMonoidHom) (g₁ := x) (g₂ := yR1)).symm
    have hcommT : ((⁅x, yR1⁆ : R1) : G) ∈ T := by
      have hmem : ⁅x, yR1⁆ ∈ _root_.commutator R1 := by
        simpa [_root_.commutator_def] using
          (Subgroup.commutator_mem_commutator
            (show x ∈ (⊤ : Subgroup R1) by trivial)
            (show yR1 ∈ (⊤ : Subgroup R1) by trivial))
      rw [hcomm_eq_TR1] at hmem
      exact hmem
    have hinv := hT_inverted ((⁅x, yR1⁆ : R1) : G) hcommT
    have halpha_inv : alpha ⁅x, yR1⁆ = ⁅x, yR1⁆⁻¹ := by
      apply Subtype.ext
      change s * ((⁅x, yR1⁆ : R1) : G) * s⁻¹ =
        (((⁅x, yR1⁆ : R1) : G))⁻¹
      simpa [rightConjugateElem, hch.section3.s_involution.inv_eq_self]
        using hinv
    exact hmap.trans halpha_inv
  have hFfix_le_ker : Ffix ≤ phi.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    have hsfix : sA • u = u := hu sA
    have huInv : phi u = (phi u)⁻¹ := by
      calc
        phi u = phi (sA • u) := congrArg phi hsfix.symm
        _ = (phi u)⁻¹ := hphi_smul u
    by_contra huOne
    have huSq : (phi u) ^ 2 = 1 := by
      calc
        (phi u) ^ 2 = phi u * phi u := pow_two _
        _ = phi u * (phi u)⁻¹ := congrArg (fun z => phi u * z) huInv
        _ = 1 := by simp
    have htopOdd : Odd (Nat.card (⊤ : Subgroup TR1)) := by
      simpa [hTR1card] using hpOdd
    exact (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
      (⊤ : Subgroup TR1) htopOdd (show phi u ∈ (⊤ : Subgroup TR1) by trivial))
      ⟨huOne, huSq⟩
  have hFfix_eq_Pbar : Ffix = Pbar := by
    apply le_antisymm
    · rw [← hphi_ker_eq_Pbar]
      exact hFfix_le_ker
    · exact hPbar_le_Ffix
  have hFfixcard : Nat.card Ffix = p := by
    rw [hFfix_eq_Pbar, hPbarcard]
  have hJcomm_le_normalizer_Ffix :
      Jcomm ≤ Subgroup.normalizer (Ffix : Set U) := by
    intro j hj
    apply centralizer_le_normalizer Ffix
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (IsMulCommutative.is_comm (M := U)).comm f j
  have hJcommcard : Nat.card Jcomm = p := by
    have hsupCard : Nat.card (Ffix ⊔ Jcomm : Subgroup U) =
        Nat.card Ffix * Nat.card Jcomm :=
      chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        Ffix Jcomm hJcomm_le_normalizer_Ffix hFJcompl.disjoint
    rw [hFJcompl.codisjoint.eq_top, Subgroup.card_top, hUcard,
      hFfixcard] at hsupCard
    apply Nat.eq_of_mul_eq_mul_left hch.B1.p_prime.pos
    calc
      p * Nat.card Jcomm = p ^ 2 := hsupCard.symm
      _ = p * p := by rw [pow_two]
  let T1R : Subgroup R1 := Jcomm.comap qU
  have hTR1_le_T1R : TR1 ≤ T1R := by
    intro x hx
    change qU x ∈ Jcomm
    have : qU x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [this]
    exact Jcomm.one_mem
  have hT1Rcard : Nat.card T1R = p ^ 2 := by
    have hqUker : qU.ker = TR1 := by
      change (QuotientGroup.mk' TR1).ker = TR1
      exact QuotientGroup.ker_mk' TR1
    have hker_le_T1R : qU.ker ≤ T1R := by
      rw [hqUker]
      exact hTR1_le_T1R
    let K1 : Subgroup T1R := qU.ker.subgroupOf T1R
    have hK1card : Nat.card K1 = p := by
      calc
        Nat.card K1 = Nat.card qU.ker :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hker_le_T1R).toEquiv
        _ = Nat.card TR1 := by rw [hqUker]
        _ = p := hTR1card
    have hquotT1 : Nat.card (T1R ⧸ K1) = p := by
      have hq := card_quotient_subgroupOf_comap_eq
        (f := qU) (hf := QuotientGroup.mk'_surjective TR1) Jcomm
      simpa [T1R, K1, qU, hJcommcard] using hq
    calc
      Nat.card T1R = Nat.card (T1R ⧸ K1) * Nat.card K1 :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := K1)
      _ = p * p := by rw [hquotT1, hK1card]
      _ = p ^ 2 := by rw [pow_two]
  let : Jcomm.Normal := commutatorAction_normal (A := A) (G := U)
  have hT1Rnormal : T1R.Normal := by
    dsimp [T1R]
    infer_instance
  let : T1R.Normal := hT1Rnormal
  have hT1R_disj_PR1 : Disjoint T1R PR1 := by
    rw [Subgroup.disjoint_def]
    intro x hxT1 hxP
    have hqxJ : qU x ∈ Jcomm := hxT1
    have hqxP : qU x ∈ Pbar :=
      Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
    have hqxBot : qU x ∈ (⊥ : Subgroup U) :=
      (Subgroup.disjoint_def.mp hFJcompl.disjoint)
        (hPbar_le_Ffix hqxP) hqxJ
    have hqxOne : qU x = 1 := Subgroup.mem_bot.mp hqxBot
    have hxTR : x ∈ TR1 := (QuotientGroup.eq_one_iff x).mp hqxOne
    exact (Subgroup.disjoint_def.mp hTR1_disj_PR1) hxTR hxP
  have hPR1_le_normalizer_T1R :
      PR1 ≤ Subgroup.normalizer (T1R : Set R1) := by
    rw [T1R.normalizer_eq_top]
    exact le_top
  have hT1R_sup_PR1_top : T1R ⊔ PR1 = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    calc
      Nat.card (T1R ⊔ PR1 : Subgroup R1) =
          Nat.card T1R * Nat.card PR1 :=
        chapter2_claim12_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          T1R PR1 hPR1_le_normalizer_T1R hT1R_disj_PR1
      _ = p ^ 2 * p := by rw [hT1Rcard, hPR1card]
      _ = p ^ 3 := by ring
      _ = Nat.card R1 := hR1card.symm
  let T1 : Subgroup G := T1R.map (R1 : Subgroup G).subtype
  have hT1card : Nat.card T1 = p ^ 2 := by
    calc
      Nat.card T1 = Nat.card T1R :=
        Subgroup.card_map_of_injective (R1 : Subgroup G).subtype_injective
      _ = p ^ 2 := hT1Rcard
  have hT1_le_R1 : T1 ≤ (R1 : Subgroup G) :=
    Subgroup.map_subtype_le T1R
  have hT_le_T1 : T ≤ T1 := by
    intro x hxT
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hT_le_R1 hxT⟩, hTR1_le_T1R hxT, rfl⟩
  have hT1_disj_P : Disjoint T1 P := by
    rw [Subgroup.disjoint_def]
    intro x hxT1 hxP
    rcases Subgroup.mem_map.mp hxT1 with ⟨xR1, hxT1R, hxval⟩
    have hxPR1 : xR1 ∈ PR1 := by
      change (xR1 : G) ∈ P
      have hxval' : (xR1 : G) = x := hxval
      exact hxval'.symm ▸ hxP
    have hxBot : xR1 ∈ (⊥ : Subgroup R1) :=
      (Subgroup.disjoint_def.mp hT1R_disj_PR1) hxT1R hxPR1
    have hxOne : xR1 = 1 := Subgroup.mem_bot.mp hxBot
    simp [← hxval, hxOne]
  have hR1_eq_T1_sup_P : (R1 : Subgroup G) = T1 ⊔ P := by
    have hmapPR1 : PR1.map (R1 : Subgroup G).subtype = P :=
      Subgroup.map_subgroupOf_eq_of_le hP_le_R1
    have hmapTop : (⊤ : Subgroup R1).map (R1 : Subgroup G).subtype =
        (R1 : Subgroup G) := by
      simpa [MonoidHom.range_eq_map] using
        (Subgroup.range_subtype (H := (R1 : Subgroup G)))
    symm
    calc
      T1 ⊔ P = T1R.map (R1 : Subgroup G).subtype ⊔
          PR1.map (R1 : Subgroup G).subtype := by
        change T1R.map (R1 : Subgroup G).subtype ⊔ P =
          T1R.map (R1 : Subgroup G).subtype ⊔
            PR1.map (R1 : Subgroup G).subtype
        rw [hmapPR1]
      _ = (T1R ⊔ PR1).map (R1 : Subgroup G).subtype := by
        rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup R1).map (R1 : Subgroup G).subtype := by
        rw [hT1R_sup_PR1_top]
      _ = (R1 : Subgroup G) := hmapTop
  have hR1_le_normalizer_T1 :
      (R1 : Subgroup G) ≤ Subgroup.normalizer (T1 : Set G) := by
    have hT1sub : T1.subgroupOf (R1 : Subgroup G) = T1R := by
      simpa [T1] using
        (subgroupOf_map_subtype_eq (K := (R1 : Subgroup G)) T1R)
    have hnormalSub : (T1.subgroupOf (R1 : Subgroup G)).Normal := by
      rw [hT1sub]
      exact hT1Rnormal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hT1_le_R1).mp
      hnormalSub
  let : IsInvariant A U Jcomm :=
    commutatorAction_isInvariant (A := A) (G := U)
  let : MulDistribMulAction A R1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer
      A (R1 : Subgroup G) hA_norm_R1
  have hqU_compat (a : A) (x : R1) : a • qU x = qU (a • x) := by
    change a • (x : U) = ((a • x : R1) : U)
    exact MulAction.Quotient.smul_coe TR1 a x
  have hT1RinvA : IsInvariant A R1 T1R := by
    exact isInvariant_comap_quotient (A := A) (G := R1)
      (N := TR1) Jcomm hqU_compat
  let : IsInvariant A R1 T1R := hT1RinvA
  have hJcomm_inverted {u : U} (hu : u ∈ Jcomm) : sA • u = u⁻¹ := by
    let v : U := u * (sA • u)
    have hvJ : v ∈ Jcomm := by
      exact Jcomm.mul_mem hu ((IsInvariant.invariant sA u).mp hu)
    have hvFixedGen : sA • v = v := by
      simp only [v, smul_mul', smul_smul, hsA_sq, one_smul]
      exact mul_comm' _ _
    have hvF : v ∈ Ffix := by
      change ∀ a : A, a • v = v
      intro a
      apply smul_eq_self_of_mem_zpowers (y := sA) ?_ hvFixedGen
      rcases Subgroup.mem_zpowers_iff.mp a.property with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    have hvBot : v ∈ (⊥ : Subgroup U) :=
      (Subgroup.disjoint_def.mp hFJcompl.disjoint) hvF hvJ
    have hvOne : v = 1 := Subgroup.mem_bot.mp hvBot
    exact eq_inv_of_mul_eq_one_right hvOne
  have hs_fixed_T1R_eq_one {x : T1R} (hxfix : sA • x = x) : x = 1 := by
    have hqxJ : qU (x : R1) ∈ Jcomm := x.property
    have hqxFix : sA • qU (x : R1) = qU (x : R1) := by
      rw [hqU_compat]
      exact congrArg qU (congrArg Subtype.val hxfix)
    have hqxF : qU (x : R1) ∈ Ffix := by
      change ∀ a : A, a • qU (x : R1) = qU (x : R1)
      intro a
      apply smul_eq_self_of_mem_zpowers (y := sA) ?_ hqxFix
      rcases Subgroup.mem_zpowers_iff.mp a.property with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    have hqxBot : qU (x : R1) ∈ (⊥ : Subgroup U) :=
      (Subgroup.disjoint_def.mp hFJcompl.disjoint) hqxF hqxJ
    have hqxOne : qU (x : R1) = 1 := Subgroup.mem_bot.mp hqxBot
    have hxTR : (x : R1) ∈ TR1 :=
      (QuotientGroup.eq_one_iff (x : R1)).mp hqxOne
    have hxFixedG : s * ((x : R1) : G) * s⁻¹ = ((x : R1) : G) := by
      exact congrArg (fun z : T1R => (((z : R1) : G))) hxfix
    have hxInvG : rightConjugateElem (((x : R1) : G)) s =
        (((x : R1) : G))⁻¹ := hT_inverted _ hxTR
    have hxEqInv : x = x⁻¹ := by
      apply Subtype.ext
      apply Subtype.ext
      calc
        ((x : R1) : G) = s * ((x : R1) : G) * s⁻¹ := hxFixedG.symm
        _ = rightConjugateElem (((x : R1) : G)) s := by
          simp [rightConjugateElem,
            hch.section3.s_involution.inv_eq_self]
        _ = (((x : R1) : G))⁻¹ := hxInvG
    by_contra hxOne
    have hxSq : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (fun z => x * z) hxEqInv
        _ = 1 := by simp
    have htopOdd : Odd (Nat.card (⊤ : Subgroup T1R)) := by
      simpa [hT1Rcard] using hpOdd.pow
    exact (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
      (⊤ : Subgroup T1R) htopOdd (show x ∈ (⊤ : Subgroup T1R) by trivial))
      ⟨hxOne, hxSq⟩
  have hT1R_inverted (x : T1R) : sA • x = x⁻¹ := by
    let v : T1R := x * (sA • x)
    have hvfix : sA • v = v := by
      let : IsMulCommutative T1R :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq hT1Rcard
      simp only [v, smul_mul', smul_smul, hsA_sq, one_smul]
      exact mul_comm' _ _
    have hvOne : v = 1 := hs_fixed_T1R_eq_one hvfix
    exact eq_inv_of_mul_eq_one_right hvOne
  have hT1_inverted : ∀ x : G, x ∈ T1 →
      rightConjugateElem x s = x⁻¹ := by
    intro x hxT1
    rcases Subgroup.mem_map.mp hxT1 with ⟨xR1, hxT1R, hxval⟩
    let xT1R : T1R := ⟨xR1, hxT1R⟩
    have hxInv := hT1R_inverted xT1R
    have hxInvG := congrArg (fun z : T1R => (((z : R1) : G))) hxInv
    have hxConj : s * (xR1 : G) * s⁻¹ = ((xR1 : G))⁻¹ := by
      change s * (xR1 : G) * s⁻¹ = ((xR1 : G))⁻¹ at hxInvG
      exact hxInvG
    rw [← hxval]
    simpa [rightConjugateElem,
      hch.section3.s_involution.inv_eq_self] using hxConj
  have hFJisComplement : Ffix.IsComplement' Jcomm := by
    apply Subgroup.isComplement'_of_card_mul_and_disjoint
    · rw [hFfixcard, hJcommcard, hUcard, pow_two]
    · exact hFJcompl.disjoint
  have hJcomm_mem_iff_inverted {u : U} :
      u ∈ Jcomm ↔ sA • u = u⁻¹ := by
    constructor
    · exact hJcomm_inverted
    · intro huInv
      have hFnormal : Ffix.Normal := by
        constructor
        intro x hx g
        have hxcomm := (IsMulCommutative.is_comm (M := U)).comm g x
        simpa [hxcomm, mul_assoc] using hx
      let : Ffix.Normal := hFnormal
      have huSup : u ∈ Ffix ⊔ Jcomm := by
        rw [hFJcompl.codisjoint.eq_top]
        trivial
      rcases Subgroup.mem_sup_of_normal_left.mp huSup with
        ⟨f, hfF, j, hjJ, hfj⟩
      have hfFix : sA • f = f := hfF sA
      have hjInv : sA • j = j⁻¹ := hJcomm_inverted hjJ
      have hEq : f * j⁻¹ = f⁻¹ * j⁻¹ := by
        calc
          f * j⁻¹ = (sA • f) * (sA • j) := by rw [hfFix, hjInv]
          _ = sA • (f * j) := by
            exact (map_mul (MulDistribMulAction.toMonoidEnd A U sA) f j).symm
          _ = sA • u := by rw [hfj]
          _ = u⁻¹ := huInv
          _ = (f * j)⁻¹ := by rw [hfj]
          _ = f⁻¹ * j⁻¹ := by
            rw [mul_inv_rev, mul_comm']
      have hfEqInv : f = f⁻¹ := mul_right_cancel hEq
      have hfOne : f = 1 := by
        by_contra hfNe
        have hfSq : f ^ 2 = 1 := by
          calc
            f ^ 2 = f * f := pow_two f
            _ = f * f⁻¹ := congrArg (fun z => f * z) hfEqInv
            _ = 1 := by simp
        have hFodd : Odd (Nat.card Ffix) := by
          rw [hFfixcard]
          exact hpOdd
        exact (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
          Ffix hFodd hfF) ⟨hfNe, hfSq⟩
      rw [← hfj, hfOne, one_mul]
      exact hjJ
  have hUpow (u : U) : u ^ p = 1 := by
    have hFnormal : Ffix.Normal := by
      constructor
      intro x hx g
      have hxcomm := (IsMulCommutative.is_comm (M := U)).comm g x
      simpa [hxcomm, mul_assoc] using hx
    let : Ffix.Normal := hFnormal
    have huSup : u ∈ Ffix ⊔ Jcomm := by
      rw [hFJcompl.codisjoint.eq_top]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp huSup with
      ⟨f, hfF, j, hjJ, hfj⟩
    let fF : Ffix := ⟨f, hfF⟩
    let jJ : Jcomm := ⟨j, hjJ⟩
    have hfPowSub : fF ^ p = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by
        simpa only [hFfixcard] using orderOf_dvd_natCard fF)
    have hjPowSub : jJ ^ p = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by
        simpa only [hJcommcard] using orderOf_dvd_natCard jJ)
    have hfPow : f ^ p = 1 := congrArg Subtype.val hfPowSub
    have hjPow : j ^ p = 1 := congrArg Subtype.val hjPowSub
    have hfj_comm : Commute f j := mul_comm' f j
    rw [← hfj, hfj_comm.mul_pow, hfPow, hjPow, one_mul]
  let : IsElementaryAbelian p U :=
    { is_comm := hUcomm.is_comm
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hUpow }
  have hLinesAll : Nat.card {L : Subgroup U // Nat.card L = p} = p + 1 :=
    chapter2_claim12_prime_order_subgroups_card_of_elementaryAbelian_prime_sq
      p hUcard
  let Lines := {L : Subgroup U // Nat.card L = p ∧ L ≠ Jcomm}
  have hLinesCard : Nat.card Lines = p := by
    change Nat.card {L : Subgroup U // Nat.card L = p ∧ L ≠ Jcomm} = p
    exact chapter2_claim12_prime_order_subgroups_ne_card
      p Jcomm hJcommcard hLinesAll
  have hCQ_le_H12_pre : CQ ≤ H12 := hCQ_le_NR.trans hNR_le_H12
  have hCQ_norm_R1 : CQ ≤ Subgroup.normalizer ((R1 : Subgroup G) : Set G) := by
    simpa [H12] using hCQ_le_H12_pre
  have hCQ_norm_T : CQ ≤ Subgroup.normalizer (T : Set G) :=
    hCQ_le_NR.trans hNR_le_normalizer_T
  have hH12_norm_R1 :
      H12 ≤ Subgroup.normalizer ((R1 : Subgroup G) : Set G) := by
    simp [H12]
  let : Subgroup.Normalizes H12 (R1 : Subgroup G) := ⟨hH12_norm_R1⟩
  let : MulDistribMulAction H12 R1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer
      H12 (R1 : Subgroup G) hH12_norm_R1
  have hTR1invH12 : IsInvariant H12 R1 TR1 :=
    isInvariant_subgroupOf_of_le_normalizer
      hH12_norm_R1 hH12_le_normalizer_T hT_le_R1
  let h12ActionU : MulDistribMulAction H12 U :=
    quotientMulDistribMulAction (A := H12) (G := R1) TR1 hTR1invH12
  let : MulDistribMulAction H12 U := h12ActionU
  have hqU_compat_H12 (a : H12) (x : R1) : a • qU x = qU (a • x) := by
    change a • (x : U) = ((a • x : R1) : U)
    exact MulAction.Quotient.smul_coe TR1 a x
  let h12AutHom : H12 →* MulAut U := MulDistribMulAction.toMulAut H12 U
  let : MulAction H12 (Subgroup U) := MulAction.compHom _ h12AutHom
  let inclCQH : CQ →* H12 := Subgroup.inclusion hCQ_le_H12_pre
  let : Subgroup.Normalizes CQ (R1 : Subgroup G) := ⟨hCQ_norm_R1⟩
  let : MulDistribMulAction CQ R1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer
      CQ (R1 : Subgroup G) hCQ_norm_R1
  have hTR1invCQ : IsInvariant CQ R1 TR1 :=
    isInvariant_subgroupOf_of_le_normalizer
      hCQ_norm_R1 hCQ_norm_T hT_le_R1
  let : MulDistribMulAction CQ U :=
    MulDistribMulAction.compHom U inclCQH
  have hqU_compat_CQ (c : CQ) (x : R1) : c • qU x = qU (c • x) := by
    change inclCQH c • qU x = qU (c • x)
    rw [hqU_compat_H12]
    rfl
  have hactions_commute (c : CQ) (u : U) :
      sA • (c • u) = c • (sA • u) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective TR1 u
    rw [hqU_compat_CQ, hqU_compat, hqU_compat, hqU_compat_CQ]
    apply congrArg qU
    apply Subtype.ext
    change s * ((c : G) * (x : G) * (c : G)⁻¹) * s⁻¹ =
      (c : G) * (s * (x : G) * s⁻¹) * (c : G)⁻¹
    have hcs : (c : G) * s = s * (c : G) := hCQCommS c c.property
    have hinv : (c : G)⁻¹ * s⁻¹ = s⁻¹ * (c : G)⁻¹ := by
      simpa using (congrArg Inv.inv hcs).symm
    calc
      s * ((c : G) * (x : G) * (c : G)⁻¹) * s⁻¹ =
          (s * (c : G)) * (x : G) * ((c : G)⁻¹ * s⁻¹) := by group
      _ = ((c : G) * s) * (x : G) * (s⁻¹ * (c : G)⁻¹) := by
        rw [hcs.symm, hinv]
      _ = (c : G) * (s * (x : G) * s⁻¹) * (c : G)⁻¹ := by group
  have hJcomm_forward (c : CQ) {u : U} (hu : u ∈ Jcomm) :
      c • u ∈ Jcomm := by
    rw [hJcomm_mem_iff_inverted]
    calc
      sA • (c • u) = c • (sA • u) := hactions_commute c u
      _ = c • u⁻¹ := by rw [hJcomm_inverted hu]
      _ = (c • u)⁻¹ := by simp
  have hJcomm_invCQ : IsInvariant CQ U Jcomm := by
    refine ⟨?_⟩
    intro c u
    constructor
    · exact hJcomm_forward c
    · intro hcu
      have hback := hJcomm_forward c⁻¹ hcu
      simpa using hback
  let : IsInvariant CQ U Jcomm := hJcomm_invCQ
  let : IsInvariant CQ R1 TR1 := hTR1invCQ
  let phiJ : Jcomm →* TR1 := phi.comp Jcomm.subtype
  have hphiJ_surj : Function.Surjective phiJ := by
    exact chapter2_claim12_restrict_surjective_of_complement_ker
      Ffix Jcomm phi (hphi_ker_eq_Pbar.trans hFfix_eq_Pbar.symm)
        hFJcompl (hJcommcard.trans hTR1card.symm)
  have hphi_CQ (c : CQ) (u : U) :
      ((phi (c • u) : TR1) : R1) = c • ((phi u : TR1) : R1) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective TR1 u
    rw [hqU_compat_CQ, hphi, hphi]
    let beta : R1 ≃* R1 := MulDistribMulAction.toMulAut CQ R1 c
    have hyfix : beta yR1 = yR1 := by
      apply Subtype.ext
      change (c : G) * (yP : G) * (c : G)⁻¹ = (yP : G)
      have hcy : (c : G) * (yP : G) = (yP : G) * (c : G) :=
        (Subgroup.mem_centralizer_iff.mp c.property.2 (yP : G) yP.property).symm
      rw [hcy]
      simp [mul_assoc]
    have hmap : ⁅beta x, yR1⁆ = beta ⁅x, yR1⁆ := by
      calc
        ⁅beta x, yR1⁆ = ⁅beta x, beta yR1⁆ := by rw [hyfix]
        _ = beta ⁅x, yR1⁆ :=
          (map_commutatorElement
            (f := beta.toMonoidHom) (g₁ := x) (g₂ := yR1)).symm
    change ⁅c • x, yR1⁆ = c • ⁅x, yR1⁆
    change ⁅beta x, yR1⁆ = beta ⁅x, yR1⁆
    exact hmap
  have hCQ_fixed_Ffix (c : CQ) {u : U} (hu : u ∈ Ffix) : c • u = u := by
    rw [hFfix_eq_Pbar] at hu
    rcases Subgroup.mem_map.mp hu with ⟨x, hxP, rfl⟩
    rw [hqU_compat_CQ]
    apply congrArg qU
    apply Subtype.ext
    change (c : G) * (x : G) * (c : G)⁻¹ = (x : G)
    have hxPG : (x : G) ∈ P := hxP
    have hxc : (x : G) * (c : G) = (c : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp c.property.2 (x : G) hxPG
    calc
      (c : G) * (x : G) * (c : G)⁻¹ =
          ((x : G) * (c : G)) * (c : G)⁻¹ := by rw [hxc]
      _ = (x : G) := by simp [mul_assoc]
  have hCQ_delta_mem_Jcomm (c : CQ) (u : U) :
      (c • u) * u⁻¹ ∈ Jcomm := by
    exact chapter2_claim12_delta_mem_right_complement
      Ffix Jcomm hFJisComplement hCQ_fixed_Ffix c u
  have hCQ_faithful_Jcomm (c : CQ)
      (hfix : ∀ j : Jcomm, c • (j : U) = (j : U)) : c = 1 := by
    exact chapter2_claim12_faithful_of_surjective_commutator
      p T P R CQ R1 TR1 Jcomm phi hTcard hch.B1.P_card hR.1 hR.2.1
        hR.2.2.1 inf_le_right hR.2.2.2.2.2 hT_le_R1 rfl
          (fun z => by
            rcases hphiJ_surj z with ⟨j, hj⟩
            exact ⟨j, hj⟩)
          hphi_CQ
          (fun _ _ => rfl)
          yP hyPne c hfix
  have hCQ_le_normalizer_T1 : CQ ≤ Subgroup.normalizer (T1 : Set G) := by
    simpa [T1, T1R, qU] using
      chapter2_claim12_le_normalizer_map_comap_quotient
        CQ (R1 : Subgroup G) qU Jcomm hqU_compat_CQ (fun _ _ => rfl)
  have hH12_eq_NR : H12 = NR := by
    by_contra hne
    obtain ⟨_kH, uH, _hkH, hGcardH, huH⟩ := hcase10_1.2
    have hNRlt : NR < H12 :=
      ⟨hNR_le_H12, fun hrev => hne (le_antisymm hNR_le_H12 hrev).symm⟩
    have hCQH_fix_Pbar (c : CQ) : inclCQH c • Pbar = Pbar := by
      exact chapter2_claim12_subgroup_compHom_smul_eq_self_of_fixed
        h12AutHom Pbar (inclCQH c)
          (fun hu => hCQ_fixed_Ffix c (hPbar_le_Ffix hu))
    have hPbar_ne_Jcomm : Pbar ≠ Jcomm :=
      chapter2_claim12_subgroup_ne_complement_of_prime_card
        p Pbar Ffix Jcomm hPbarcard hPbar_le_Ffix hFJcompl
    have hprePbar : Pbar.comap qU = RR1 := by
      change (PR1.map (QuotientGroup.mk' TR1)).comap
        (QuotientGroup.mk' TR1) = R.subgroupOf (R1 : Subgroup G)
      exact chapter2_claim12_comap_map_quotient_eq_subgroupOf_sup
        (R1 : Subgroup G) T P R TR1 PR1 rfl rfl
          hT_le_R1 hP_le_R1 hR.1
    have hfixPbar_iff_mem_NR (a : H12) :
        a • Pbar = Pbar ↔ (a : G) ∈ NR := by
      change a • Pbar = Pbar ↔
        (a : G) ∈ Subgroup.normalizer (R : Set G)
      exact chapter2_claim12_fix_image_iff_mem_normalizer_compHom
        H12 R (R1 : Subgroup G) h12AutHom (fun _ _ => rfl) qU Pbar
          hR_le_R1 hprePbar hqU_compat_H12 (fun _ _ => rfl)
            (QuotientGroup.mk'_surjective TR1) a
    have horbit_avoids_J : ∀ a : H12, a • Pbar ≠ Jcomm :=
      chapter2_claim12_orbit_avoids_inverted_line (G := G) (U := U)
        H12 (R1 : Subgroup G) V P qU PR1 Pbar Jcomm T1R T1 yR1 yP s
          rfl (by exact yP.property) rfl rfl hqU_compat_H12
            (fun a x => by
              simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe])
            rfl hyPne (by simpa [hch.B1.P_card] using hpOdd) hch.B1.P_le_V
              (fun x =>
                chapter2_claim12_not_stronglyReal_of_mem_peterfalviV
                  (G := G) (Ω := Ω)
                  H D Q K V W Q0 S Q1 t s x hch.section3)
              hch.section3.2.2.1 hT1_inverted
    apply hne
    exact chapter2_claim12_projective_orbit_forces_normalizers_eq
      p H12 NR (R1 : Subgroup G) CQ inclCQH Pbar Jcomm Ffix hNR_le_H12
        hPbarcard hLinesCard hCQcard hFfixcard
          hJcommcard hFJisComplement hFfix_eq_Pbar hCQ_fixed_Ffix
            hCQ_delta_mem_Jcomm hCQ_faithful_Jcomm
              (fun c u =>
                (chapter2_claim12_mulDistrib_compHom_smul inclCQH c u).symm)
              hR1card hR1_le_NR m uH hm1 hGcardH huH
                hCQH_fix_Pbar hfixPbar_iff_mem_NR horbit_avoids_J

  exact chapter2_claim12_construct_local_index_subgroup
    p H12 NR (R1 : Subgroup G) T1 P CQ hH12_eq_NR hNR_le_H12
      hR1_le_NR hCQ_le_NR hCQ_norm_R1 hT1_le_R1 hR1card hCQcard hNRcard
        hR1_eq_T1_sup_P hP_le_R1 hR1_le_normalizer_T1
          hCQ_le_normalizer_T1 inf_le_right hT1card

set_option backward.isDefEq.respectTransparency false in
/-- The source-specific endpoint of TeX lines 334-372: Hall-Wielandt gives the
ambient/local residual quotient equivalence, and the local normalizer has a
normal subgroup of index `p`. -/
private theorem chapter2_claim12_case_10_1_local_hall_index_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma R T : Subgroup G) (t s : G) (p m : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m)
    (hR : R = T ⊔ P ∧
        Disjoint T P ∧
          T ≤ Subgroup.centralizer (P : Set G) ∧
            (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
              W ⊓ Subgroup.centralizer (P : Set G)) ≤
                Subgroup.normalizer (T : Set G) ∧
              Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
                ∀ A B : Subgroup G,
                  A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                      ∃! c : G,
                        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                          B = rightConjugate A c)
    (hT_inverted : ∀ x : G, x ∈ T →
      rightConjugateElem x s = x⁻¹)
    (hCaseOne :
      Subgroup.centralizer (P : Set G) ≤
          Subgroup.normalizer (R : Set G) ∧
        Nat.card R = p ^ (m + 1) ∧
          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
            p ^ m ∧
          ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
            (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
              R.subgroupOf (Subgroup.centralizer (P : Set G)))
    (hCaseOneMOne :
      m = 1 →
        s ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
          (∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (P : Set G) →
            q * s = s * q) ∧
          (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = ⊥ ∧
          ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
            ∃ r q : G, r ∈ R ∧
              q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ g = r * q)
    (hcase10_1 :
      ¬ p ∣ Nat.card Sigma ∧ (∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧ Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u)) :
    ∃ H12 : Subgroup G,
      letI : (External.hallPResidual p G).Normal :=
        External.hallPResidual_normal p G
      letI : (External.hallPResidual p H12).Normal :=
        External.hallPResidual_normal p H12
      Nonempty ((G ⧸ External.hallPResidual p G) ≃*
        (H12 ⧸ External.hallPResidual p H12)) ∧
        ∃ M : Subgroup H12, M.Normal ∧ Nat.card (H12 ⧸ M) = p := by
  have hOrbitConclusion :=
    chapter2_claim12_orbit_forces_m_eq_one
      H D Q K V W Q0 S Q1 P R T t s p m hch hStarComm_order hR
        hT_inverted hCaseOne hcase10_1.2
  have hm1 : m = 1 := hOrbitConclusion.1
  have hNRcardFactor := hOrbitConclusion.2.1
  have hNR_le_normalizer_T := hOrbitConclusion.2.2
  have hquotient_step :
      ∃ R1 : Sylow p G,
        m = 1 ∧ R ≤ (R1 : Subgroup G) ∧ Nat.card R1 = p ^ 3 ∧
          let H12 : Subgroup G := Subgroup.normalizer ((R1 : Subgroup G) : Set G)
          letI : (External.hallPResidual p G).Normal :=
            External.hallPResidual_normal p G
          letI : (External.hallPResidual p H12).Normal :=
            External.hallPResidual_normal p H12
          Nonempty ((G ⧸ External.hallPResidual p G) ≃*
            (H12 ⧸ External.hallPResidual p H12)) := by
    classical
    let : Fact (Nat.Prime p) := ⟨hch.B1.p_prime⟩
    have hRp : IsPGroup p R := IsPGroup.of_card hCaseOne.2.1
    obtain ⟨R1, hR_le_R1⟩ := hRp.exists_le_sylow
    rcases hcase10_1.2 with ⟨_k, u, _hk, hGcard, hu⟩
    have hune : u ≠ 0 := by
      intro hu0
      apply hu
      rw [hu0]
      exact dvd_zero p
    have hpowne : p ^ 3 ≠ 0 := pow_ne_zero 3 hch.B1.p_prime.ne_zero
    have hfac : (Nat.card G).factorization p = 3 := by
      rw [hGcard, hm1]
      rw [Nat.factorization_mul hpowne hune, Nat.factorization_pow]
      simp [hch.B1.p_prime.factorization,
        Nat.factorization_eq_zero_of_not_dvd hu]
    have hR1card : Nat.card R1 = p ^ 3 := by
      rw [R1.card_eq_multiplicity, hfac]
    have hpOdd : Odd p := by
      have hP_le_D : P ≤ D := by
        refine hch.B1.P_le_V.trans ?_
        rw [hch.section3.section2.V_eq]
        exact inf_le_left
      simpa [hch.B1.P_card] using
        hch.section3.section2.hA.A1.D_odd.of_dvd_nat
          (Subgroup.card_dvd_of_le hP_le_D)
    have hp3 : 3 ≤ p := by
      have hp2 := hch.B1.p_prime.two_le
      have hpne2 : p ≠ 2 := by
        intro hpEq
        subst p
        exact hpOdd.not_two_dvd_nat (dvd_refl 2)
      omega
    have hupper :
        (⊤ : Subgroup R1) ≤ Subgroup.upperCentralSeries R1 (p - 1) :=
      chapter2_claim12_upperCentralSeries_of_card_prime_cube p hR1card hp3
    let H12 : Subgroup G := Subgroup.normalizer ((R1 : Subgroup G) : Set G)
    refine ⟨R1, hm1, hR_le_R1, hR1card, ?_⟩
    exact chapter2_claim12_hallWielandt_of_upperCentralSeries
      p R1 H12 rfl hupper
  obtain ⟨R1, _hm1, hR_le_R1, hR1card, hquot⟩ := hquotient_step
  let H12 : Subgroup G := Subgroup.normalizer ((R1 : Subgroup G) : Set G)
  let : (External.hallPResidual p G).Normal :=
    External.hallPResidual_normal p G
  let : (External.hallPResidual p H12).Normal :=
    External.hallPResidual_normal p H12
  have hlocal_index :
      ∃ M : Subgroup H12, M.Normal ∧ Nat.card (H12 ⧸ M) = p :=
    chapter2_claim12_local_index_after_sylow
      H D Q K V W Q0 S Q1 P Sigma R T t s p m hch hSigma
        hStarComm_order hR hT_inverted hCaseOne hCaseOneMOne hcase10_1
          hm1 hNRcardFactor hNR_le_normalizer_T R1 hR_le_R1 hR1card
  exact ⟨H12, hquot, hlocal_index⟩

/- Claim (12): from case (10.1), Claim (11)'s `R` data, and Peterfalvi's
Appendix II/Hall-Wielandt argument, construct the normal subgroup of index
`p` later contradicted by hypothesis `(B2)`. -/
private theorem chapter2_claim12_case_10_1_hallWielandt_normal_index_witness
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma R T : Subgroup G) (t s : G) (p m : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m)
    (hR : R = T ⊔ P ∧
        Disjoint T P ∧
          T ≤ Subgroup.centralizer (P : Set G) ∧
            (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
              W ⊓ Subgroup.centralizer (P : Set G)) ≤
                Subgroup.normalizer (T : Set G) ∧
              Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
                ∀ A B : Subgroup G,
                  A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                      ∃! c : G,
                        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                          B = rightConjugate A c)
    (hT_inverted : ∀ x : G, x ∈ T →
      rightConjugateElem x s = x⁻¹)
    (hCaseOne :
      Subgroup.centralizer (P : Set G) ≤
          Subgroup.normalizer (R : Set G) ∧
        Nat.card R = p ^ (m + 1) ∧
          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
            p ^ m ∧
          ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
            (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
              R.subgroupOf (Subgroup.centralizer (P : Set G)))
    (hCaseOneMOne :
      m = 1 →
        s ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
          (∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (P : Set G) →
            q * s = s * q) ∧
          (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = ⊥ ∧
          ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
            ∃ r q : G, r ∈ R ∧
              q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ g = r * q)
    (hcase10_1 :
      ¬ p ∣ Nat.card Sigma ∧ (∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧ Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u)) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p := by
  rcases chapter2_claim12_case_10_1_local_hall_index_source_interface
      H D Q K V W Q0 S Q1 P Sigma R T t s p m hch hSigma hStarComm_order hR
        hT_inverted hCaseOne hCaseOneMOne hcase10_1 with
    ⟨H12, hquot, M, hMnormal, hMindex⟩
  let : (External.hallPResidual p G).Normal :=
    External.hallPResidual_normal p G
  let : (External.hallPResidual p H12).Normal :=
    External.hallPResidual_normal p H12
  let : M.Normal := hMnormal
  have hres_le : External.hallPResidual p H12 ≤ M :=
    chapter2_claim12_hallPResidual_le_of_quotient_card_eq p M hMindex
  have hres_le' :
      External.hallPResidual p H12 ≤ M.comap (MonoidHom.id H12) := by
    simpa [Subgroup.comap_id] using hres_le
  let φ : (H12 ⧸ External.hallPResidual p H12) →* (H12 ⧸ M) :=
    QuotientGroup.map (External.hallPResidual p H12) M (MonoidHom.id H12) hres_le'
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M y
    exact ⟨QuotientGroup.mk' (External.hallPResidual p H12) x, rfl⟩
  exact
    chapter2_claim12_global_index_from_local_hall_data
      p (External.hallPResidual p G) (External.hallPResidual p H12)
        hquot φ hφ hMindex

private theorem claim_12_case_10_1_contradicts_B2
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma R T : Subgroup G) (t s : G) (p m : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m)
    (hR : R = T ⊔ P ∧
        Disjoint T P ∧
          T ≤ Subgroup.centralizer (P : Set G) ∧
            (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
              W ⊓ Subgroup.centralizer (P : Set G)) ≤
                Subgroup.normalizer (T : Set G) ∧
              Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
                ∀ A B : Subgroup G,
                  A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                      ∃! c : G,
                        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                          B = rightConjugate A c)
    (hT_inverted : ∀ x : G, x ∈ T →
      rightConjugateElem x s = x⁻¹)
    (hCaseOne :
      Subgroup.centralizer (P : Set G) ≤
          Subgroup.normalizer (R : Set G) ∧
        Nat.card R = p ^ (m + 1) ∧
          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
            p ^ m ∧
          ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
            (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
              R.subgroupOf (Subgroup.centralizer (P : Set G)))
    (hCaseOneMOne :
      m = 1 →
        s ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
          (∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (P : Set G) →
            q * s = s * q) ∧
          (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = ⊥ ∧
          ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
            ∃ r q : G, r ∈ R ∧
              q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ g = r * q)
    (hcase10_1 :
      ¬ p ∣ Nat.card Sigma ∧ (∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧ Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u)) :
    False := by
  exact
    claim_12_B2_excludes_normal_index_p H D Q K V W Q0 S Q1 P t s p hch
      (chapter2_claim12_case_10_1_hallWielandt_normal_index_witness
        H D Q K V W Q0 S Q1 P Sigma R T t s p m hch hSigma hStarComm_order hR
          hT_inverted hCaseOne hCaseOneMOne hcase10_1)

public theorem claim_12
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p m : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m) :
    p = 3 ∧ Nat.card Sigma = 3 ∧
      Nat.card (nearFieldStar Q P) = 8 ∧ IsCyclic W ∧
        (Nat.card W = 3 ∨ Nat.card W = 9) ∧
          (∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
            Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u) ∧
            ∃ (F : Type v) (_ : PFAppendixII.RightNearField F) (_ : Finite F)
                (_ : Nontrivial F),
              PFAppendixII.IsDicksonIndexTwoModel F 3 1 ∧
                Nonempty (nearFieldStar Q P ≃* Fˣ) := by
  have hcase10 :=
    claim_10 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P Sigma t s p m hch
      hind hSigma hStarComm_order
  rcases hcase10 with h10_1 | h10_2
  · rcases claim_11 H D Q K V W Q0 S Q1 P t s p hch hind with
      ⟨R, T, hR, hModel⟩
    rcases hModel with
      ⟨_N, _F, _hFnear, _hFfinite, _hFnontrivial, _addEquiv, _unitEquiv,
        _hN, _hRcentral, _hinverse, hT_inverted, _hst_mem_T, _hconjugation,
        _hchar, _hExceptionalLocal, h11CaseOneLocal, h11CaseOneMOne⟩
    exact False.elim
      (claim_12_case_10_1_contradicts_B2
        H D Q K V W Q0 S Q1 P Sigma R T t s p m hch hSigma hStarComm_order hR
          hT_inverted
            (h11CaseOneLocal m hStarComm_order (by simpa [hSigma] using h10_1.1))
            (h11CaseOneMOne m hStarComm_order
              (by simpa [hSigma] using h10_1.1)) h10_1)
  · exact h10_2

end PFchapter2
end CFSG.BenderSuzuki
