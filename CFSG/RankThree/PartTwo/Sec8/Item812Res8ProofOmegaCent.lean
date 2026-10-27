module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofOmega
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (projSp)

namespace Item812Res8

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_eq_one_of_mem_sectionCentralizer {A L : Subgroup G} {w : G}
    (hw : w ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype))
    (hwN : w ∈ Subgroup.normalizer (L : Set G)) :
    thetaQuotMulAut L (compAction L ⟨w, hwN⟩) = 1 := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H y =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
    obtain ⟨t, ht, hte⟩ := hw.2 y y.2
    have h1 : (compAction L ⟨w, hwN⟩ y : L) = t * y := by
      apply Subtype.ext
      change w * (y : G) * w⁻¹ = (t : G) * y
      have hte' : (t : G) = w * y * w⁻¹ * (y : G)⁻¹ := hte
      rw [hte']
      group
    rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).mpr ht, one_mul]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem exists_fixed_involution_of_projSp {A : Subgroup G}
    (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (hA81 : Nat.card A = 81) {e : G} (heA : e ∈ A) (he1 : e ≠ 1) {Le : Subgroup G}
    (hLe : Le ∈ thetaComponentsAt 3 e) (hAN : A ≤ Subgroup.normalizer (Le : Set G)) {k : ℕ}
    (hk : 1 ≤ k) {F : Type} [Field F] [Finite F] [CharP F 2] (hFc : Nat.card F = 2 ^ k)
    (hX : Nonempty (Le ⧸ aschbacherSolvableCore 3 Le ≃* projSp 2 F))
    {x : G} (hxA : x ∈ A) (hxout : InducesOuterTheta x Le) {w : G}
    (hw : w ∈ Late.sectionCentralizer A Le ((aschbacherSolvableCore 3 Le).map Le.subtype))
    (hwe : w ∉ Subgroup.zpowers e) :
    ∃ j : Le ⧸ aschbacherSolvableCore 3 Le, orderOf j = 2 ∧
      ∀ (u : G) (hu : u ∈ Subgroup.normalizer (Le : Set G)), u ∈ A →
        thetaQuotMulAut Le (compAction Le ⟨u, hu⟩) j = j := by
  classical
  set e₀ : Le ⧸ aschbacherSolvableCore 3 Le ≃* StatedProj (StatedSp 2 F) :=
    hX.some.trans (Sec4.projSpEquivStatedProj 2 F) with he₀
  set ρ : A →* MulAut (StatedProj (StatedSp 2 F)) :=
    (KFacts.inducedAutHom Le e₀).comp (Subgroup.inclusion hAN) with hρ
  have hρapply : ∀ y : A, ρ y =
      MulAut.congr e₀ (thetaQuotMulAut Le (compAction Le ⟨y, hAN y.2⟩)) := fun y => rfl
  have hekr : ρ ⟨e, heA⟩ = 1 := by
    rw [hρapply]
    have h1 : compAction Le ⟨e, hAN heA⟩ = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      change e * (x : G) * e⁻¹ = (x : G)
      have hxe : (x : G) * e = e * x :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_mem_thetaComponentsAt_three hLe x.2)
      rw [← hxe, mul_inv_cancel_right]
    rw [h1, map_one, map_one]
  have hwA : w ∈ A := hw.1
  have hwkr : ρ ⟨w, hwA⟩ = 1 := by
    rw [hρapply, thetaQuotMulAut_eq_one_of_mem_sectionCentralizer hw (hAN hwA), map_one]
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
  have hρx : ¬ KFacts.IsInnerAut (ρ ⟨x, hxA⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff Le e₀ (hAN hxA)).mpr hxout
  have hcomm : ∀ β ∈ ρ.range, ∀ γ ∈ ρ.range, β * γ = γ * β := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [← map_mul, ← map_mul, hAab.1.is_comm.comm y y']
  have h3 : ∀ β ∈ ρ.range, β ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using hAab.2 y y.2), map_one]
  obtain ⟨J, hJ2, hJfix⟩ := Item812Res2.exists_fixed_involution_of_card_le_nine (m := k)
    hk hFc ρ.range hcomm h3 hrangecard ⟨⟨x, hxA⟩, rfl⟩ hρx
  refine ⟨e₀.symm J, by rw [MulEquiv.orderOf_eq, hJ2], fun u hu huA => ?_⟩
  have h1 : e₀ (thetaQuotMulAut Le (compAction Le ⟨u, hAN huA⟩) (e₀.symm J)) = J :=
    hJfix _ ⟨⟨u, huA⟩, rfl⟩
  apply e₀.injective
  rw [show (⟨u, hu⟩ : Subgroup.normalizer (Le : Set G)) = ⟨u, hAN huA⟩ from rfl, h1,
    MulEquiv.apply_symm_apply]

end Item812Res8


@[expose] def KF89OmegaFixInvNonSp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A,
      (∀ m : ℕ, IsEmpty (p.2 ⧸ aschbacherSolvableCore 3 p.2 ≃* projSp 2 (GaloisField 2 (3 * m)))) →
      ∀ w ∈ Late.sectionCentralizer A p.2 ((aschbacherSolvableCore 3 p.2).map p.2.subtype),
        w ∉ Subgroup.zpowers p.1 →
        ∃ j : p.2 ⧸ aschbacherSolvableCore 3 p.2, orderOf j = 2 ∧
          ∀ (u : G) (hu : u ∈ Subgroup.normalizer (p.2 : Set G)), u ∈ A →
            thetaQuotMulAut p.2 (compAction p.2 ⟨u, hu⟩) j = j


open Item812Res8

theorem pair89OmegaCent_of (h45 : Sec4.Item4_5) (hF : KF89OmegaFixInvNonSp) :
    Pair89OmegaCent := by
  intro G _ _ A c L a b X n h p hp
  classical
  obtain ⟨e, Le⟩ := p
  have hΩ := hp
  obtain ⟨heA, he1, hLe, ⟨x, hxA, hxk⟩, -, ⟨d, m, hdm⟩⟩ := hp
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
  refine Set.Subset.antisymm (fun w hw => ?_)
    (Item86ResProof.zpowers_subset_sectionCentralizer heA
      (le_centralizer_of_mem_thetaComponentsAt_three hLe))
  by_contra hwe
  have hxout : InducesOuterTheta x Le := by
    rcases hxk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
  obtain ⟨j, hj2, hjfix⟩ : ∃ j : Le ⧸ aschbacherSolvableCore 3 Le, orderOf j = 2 ∧
      ∀ (u : G) (hu : u ∈ Subgroup.normalizer (Le : Set G)), u ∈ A →
        thetaQuotMulAut Le (compAction Le ⟨u, hu⟩) j = j := by
    by_cases hSp : ∃ m' : ℕ,
        Nonempty (Le ⧸ aschbacherSolvableCore 3 Le ≃* projSp 2 (GaloisField 2 (3 * m')))
    · obtain ⟨m', hX⟩ := hSp
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk, hFc⟩ : ∃ k : ℕ, 1 ≤ k ∧ Nat.card (GaloisField 2 (3 * m')) = 2 ^ k := by
        rcases Nat.eq_zero_or_pos m' with rfl | h'
        · exact ⟨1, le_rfl, by rw [mul_zero, Sec21.natCard_galoisField_two_zero, pow_one]⟩
        · exact ⟨3 * m', by omega, GaloisField.card 2 (3 * m') (by omega)⟩
      have : CharP (GaloisField 2 (3 * m')) 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
          hk hFc
      exact exists_fixed_involution_of_projSp hAab h.card_eq heA he1 hLe hAN hk hFc hX hxA hxout
        hw hwe
    · have hE : ∀ m' : ℕ,
          IsEmpty (Le ⧸ aschbacherSolvableCore 3 Le ≃* projSp 2 (GaloisField 2 (3 * m'))) :=
        fun m' => ⟨fun φ => hSp ⟨m', ⟨φ⟩⟩⟩
      exact hF G A c L a b X n h (e, Le) hΩ hE w hw hwe
  have h4 := Item812Res2.four_le_localRank_of_fixed_involution hAab h.card_eq hAN hj2
    (fun u hu => hjfix u (hAN hu) hu)
  have h3 := h.toTheoremFourHyp.localRank_three
  omega

end CFSG.RankThree.PartTwo.Sec8
