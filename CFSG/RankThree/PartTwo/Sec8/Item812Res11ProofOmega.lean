module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaCent
public import CFSG.RankThree.PartTwo.Sec8.Item812Res9ProofG2Two
public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmegaG2
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)


namespace Item812Res11

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_involution_of_g2 (hG2 : KFG2Ord3Inv) {A : Subgroup G}
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : Nat.card A = 81) {e : G} (heA : e ∈ A)
    (he1 : e ≠ 1) {Le : Subgroup G} (hLe : Le ∈ thetaComponentsAt 3 e)
    (hAN : A ≤ Subgroup.normalizer (Le : Set G)) {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (3 * m))
    (E : Le ⧸ aschbacherSolvableCore 3 Le ≃* adjointGroup .G2 K) {x : G} (hxA : x ∈ A)
    (hxout : InducesOuterTheta x Le) {w : G}
    (hw : w ∈ Late.sectionCentralizer A Le ((aschbacherSolvableCore 3 Le).map Le.subtype))
    (hwe : w ∉ Subgroup.zpowers e) :
    ∃ j : Le ⧸ aschbacherSolvableCore 3 Le, orderOf j = 2 ∧
      ∀ (u : G) (hu : u ∈ Subgroup.normalizer (Le : Set G)), u ∈ A →
        thetaQuotMulAut Le (compAction Le ⟨u, hu⟩) j = j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : A →* MulAut (Le ⧸ aschbacherSolvableCore 3 Le) :=
    (thetaQuotMulAut Le).comp ((compAction Le).comp (Subgroup.inclusion hAN)) with hρ
  have hρapply : ∀ y : A, ρ y = thetaQuotMulAut Le (compAction Le ⟨y, hAN y.2⟩) :=
    fun y => rfl
  have hekr : ρ ⟨e, heA⟩ = 1 := by
    rw [hρapply]
    have h1 : compAction Le ⟨e, hAN heA⟩ = 1 := by
      refine MulEquiv.ext fun z => Subtype.ext ?_
      change e * (z : G) * e⁻¹ = (z : G)
      have hze : (z : G) * e = e * z :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_mem_thetaComponentsAt_three hLe z.2)
      rw [← hze, mul_inv_cancel_right]
    rw [h1, map_one]
  have hwA : w ∈ A := hw.1
  have hwkr : ρ ⟨w, hwA⟩ = 1 := by
    rw [hρapply, Item812Res8.thetaQuotMulAut_eq_one_of_mem_sectionCentralizer hw (hAN hwA)]
  have he3 : e ^ 3 = 1 := hAab.2 e heA
  have heord : orderOf (⟨e, heA⟩ : A) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using he3))
      (fun h1 => he1 (by simpa using congrArg Subtype.val h1))
  have hkercard : 9 ≤ Nat.card ρ.ker := by
    have hdvd : Nat.card ρ.ker ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = Nat.card A by rw [hA81]; norm_num]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hgt : 3 < Nat.card ρ.ker := by
      by_contra hle
      push Not at hle
      have heq : Subgroup.zpowers (⟨e, heA⟩ : A) = ρ.ker :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := ρ.ker)).mpr hekr)
          (by rw [Nat.card_zpowers, heord]; exact hle)
      have hwmem : (⟨w, hwA⟩ : A) ∈ Subgroup.zpowers (⟨e, heA⟩ : A) := heq ▸ hwkr
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwmem
      exact hwe ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [hieq] at hgt ⊢
    interval_cases i <;> simp_all
  have hrangecard : Nat.card ρ.range ≤ 9 := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hA81] at h1
    have h2 : 9 * Nat.card ρ.range ≤ 81 := h1 ▸ Nat.mul_le_mul_right _ hkercard
    omega
  have hcomm : ∀ β ∈ ρ.range, ∀ γ ∈ ρ.range, β * γ = γ * β := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [← map_mul, ← map_mul, hAab.1.is_comm.comm y y']
  have h3 : ∀ β ∈ ρ.range, β ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using hAab.2 y y.2), map_one]
  set α := ρ ⟨x, hxA⟩ with hα
  have hαout : ¬ IsInnerAut α := by
    obtain ⟨hxN, hnot⟩ := hxout
    exact hnot
  have hx3 : x ^ 3 = 1 := hAab.2 x hxA
  have hchar : ringChar K = 2 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨p, hp, k, hpr, hk⟩ := FiniteField.card' K
    have h1 : p ∣ 2 ^ (3 * m) := by
      rw [← hK, Nat.card_eq_fintype_card, hk]
      exact dvd_pow_self p k.ne_zero
    have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h1)
    subst h2
    exact ringChar.eq K 2
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  have hZ : Subgroup.center (Le ⧸ aschbacherSolvableCore 3 Le) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd E.symm center_adjointGroup_eq_bot
  have htri : ∀ γ ∈ ρ.range, IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α) := by
    intro γ hγ
    have hα3' : MulAut.congr E α ^ 3 = 1 := by rw [← map_pow, h3 α ⟨_, rfl⟩, map_one]
    have hγ3' : MulAut.congr E γ ^ 3 = 1 := by rw [← map_pow, h3 γ hγ, map_one]
    have hαout' : ¬ IsInnerAut (MulAut.congr E α) := by
      rwa [KFacts.isInnerAut_congr]
    rcases Item812Res11.g2_trichotomy hK3 hK4 hα3' hαout' hγ3' with h | h | h
    · exact Or.inl ((KFacts.isInnerAut_congr E γ).mp h)
    · rw [← map_inv, ← map_mul, KFacts.isInnerAut_congr] at h
      exact Or.inr (Or.inl h)
    · rw [← map_mul, KFacts.isInnerAut_congr] at h
      exact Or.inr (Or.inr h)
  obtain ⟨-, k, _, _, hk, ⟨ι⟩⟩ :=
    KFacts.barCentralizer_mulEquiv_g2 (by omega : m ≠ 0) hK hx3 hxout E
  set F := barCentralizer (Subgroup.zpowers x) Le with hFdef
  have hF : ∀ z, z ∈ F ↔ α z = z := fun z =>
    KFacts.mem_barCentralizer_zpowers_iff (hAN hxA) z
  have hF2 : ∃ j ∈ F, orderOf j = 2 := by
    have hcard : 2 ∣ Nat.card (adjointGroup .G2 k) := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk, CFSG.Open.ordG2]
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
      exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 hcard
    refine ⟨(ι.symm s : Le ⧸ aschbacherSolvableCore 3 Le), (ι.symm s).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hs]
  have hF3 : ∀ d ∈ F, orderOf d = 3 → ∃ s ∈ F, orderOf s = 2 ∧ s * d = d * s := by
    intro d hd hd3
    have hι3 : orderOf (ι ⟨d, hd⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hd3
    obtain ⟨s, hs1, hs2, hsd⟩ := hG2 m hm k hk (ι ⟨d, hd⟩) hι3
    refine ⟨(ι.symm s : Le ⧸ aschbacherSolvableCore 3 Le), (ι.symm s).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hs2 hs1
    · have h1 : ι.symm s * ⟨d, hd⟩ = ⟨d, hd⟩ * ι.symm s := by
        apply ι.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hsd]
      exact congrArg Subtype.val h1
  obtain ⟨j, hj2, hjfix⟩ := Item812Res11.exists_fixed_involution_of_trichotomy hZ ρ.range hcomm h3
    hrangecard ⟨_, rfl⟩ hαout htri F hF hF2 hF3
  refine ⟨j, hj2, fun u hu huA => ?_⟩
  exact hjfix _ ⟨⟨u, huA⟩, rfl⟩

end Item812Res11

@[expose] def KF89OmegaFixInvD4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, (∃ m : ℕ, IsoTrialityD4 (p.2 ⧸ aschbacherSolvableCore 3 p.2) m) →
      ∀ w ∈ Late.sectionCentralizer A p.2 ((aschbacherSolvableCore 3 p.2).map p.2.subtype),
        w ∉ Subgroup.zpowers p.1 →
        ∃ j : p.2 ⧸ aschbacherSolvableCore 3 p.2, orderOf j = 2 ∧
          ∀ (u : G) (hu : u ∈ Subgroup.normalizer (p.2 : Set G)), u ∈ A →
            thetaQuotMulAut p.2 (compAction p.2 ⟨u, hu⟩) j = j

@[expose] def KF89OmegaFixInvRee : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, (∃ m : ℕ, IsGammaTypeRee (p.2 ⧸ aschbacherSolvableCore 3 p.2) m) →
      ∀ w ∈ Late.sectionCentralizer A p.2 ((aschbacherSolvableCore 3 p.2).map p.2.subtype),
        w ∉ Subgroup.zpowers p.1 →
        ∃ j : p.2 ⧸ aschbacherSolvableCore 3 p.2, orderOf j = 2 ∧
          ∀ (u : G) (hu : u ∈ Subgroup.normalizer (p.2 : Set G)), u ∈ A →
            thetaQuotMulAut p.2 (compAction p.2 ⟨u, hu⟩) j = j

@[expose] def KF89OmegaFixInvUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, (∃ k : ℕ, IsUnitaryTwo (p.2 ⧸ aschbacherSolvableCore 3 p.2) k) →
      ∀ w ∈ Late.sectionCentralizer A p.2 ((aschbacherSolvableCore 3 p.2).map p.2.subtype),
        w ∉ Subgroup.zpowers p.1 →
        ∃ j : p.2 ⧸ aschbacherSolvableCore 3 p.2, orderOf j = 2 ∧
          ∀ (u : G) (hu : u ∈ Subgroup.normalizer (p.2 : Set G)), u ∈ A →
            thetaQuotMulAut p.2 (compAction p.2 ⟨u, hu⟩) j = j

open Item812Res11

theorem kF89OmegaFixInvNonSp_of (h45 : Sec4.Item4_5) (hG2 : KFG2Ord3Inv)
    (hD4 : KF89OmegaFixInvD4) (hRee : KF89OmegaFixInvRee) (hU : KF89OmegaFixInvUnitary) :
    KF89OmegaFixInvNonSp := by
  intro G _ _ A c L a b X n h p hp hSp w hw hwe
  obtain ⟨e, Le⟩ := p
  have hΩ := hp
  obtain ⟨heA, he1, hLe, ⟨x, hxA, hxk⟩, -, ⟨d, m, hdm⟩⟩ := hp
  obtain ⟨-, -, hm, hcase⟩ := Item87Proof.isGammaIndex_cases hdm
  rcases hcase with ⟨hRee', -⟩ | ⟨hL2, -⟩
  · exact hRee G A c L a b X n h (e, Le) hΩ ⟨m, hRee'⟩ w hw hwe
  rcases hL2 with hD | ⟨q, hq2, hqe, hG⟩ | hPSU | hSU | hSp'
  · exact hD4 G A c L a b X n h (e, Le) hΩ ⟨m, hD⟩ w hw hwe
  ·
    obtain ⟨K, _, _, hK, ⟨E⟩⟩ := Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hG
    have hAab := h.mem_partTwoF.1
    have h3A : ∀ u ∈ A, u ^ 3 = 1 := hAab.2
    have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
      congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h3A u u.2)⟩
    have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hz e heA)
    have hAN : A ≤ Subgroup.normalizer (Le : Set G) :=
      Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp (h3A e heA) he1
        hA3 hAe Le hLe
    have hxout : InducesOuterTheta x Le := by
      rcases hxk with hk | hk
      · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
    exact exists_fixed_involution_of_g2 hG2 hAab h.card_eq heA he1 hLe hAN hm hK E hxA hxout hw
      hwe
  · exact hU G A c L a b X n h (e, Le) hΩ ⟨3 * m, Or.inl hPSU⟩ w hw hwe
  · exact hU G A c L a b X n h (e, Le) hΩ ⟨3 * m, Or.inr hSU⟩ w hw hwe
  · obtain ⟨φ⟩ := hSp'
    exact ((hSp m).false φ).elim

theorem kF89OmegaFixInvNonSp_of_minus
    (h45 : Sec4.Item4_5) (hMinus : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus)
    (hD4 : KF89OmegaFixInvD4) (hRee : KF89OmegaFixInvRee) (hU : KF89OmegaFixInvUnitary) :
    KF89OmegaFixInvNonSp :=
  kF89OmegaFixInvNonSp_of h45 (kFG2Ord3Inv_of_minus hMinus) hD4 hRee hU

end CFSG.RankThree.PartTwo.Sec8
