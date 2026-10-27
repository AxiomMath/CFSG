module

public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofTheta419
public import CFSG.RankThree.PartTwo.Sec6.BThreeFromLBalance
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools
import CFSG.RankThree.PartTwo.Sec8.Standing
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open scoped commutatorElement

section KFacts


@[expose] def KF89JCentType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (a : G) (m : ℕ), 1 ≤ m →
    IsGammaType (X ⧸ aschbacherSolvableCore 3 X) m →
    (∀ k : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) k) → a ^ 3 = 1 →
    (KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField) →
    (∀ k : ℕ, Sec8PairGTwo X a k) →
      Sec4.IsType419Theta (perfectResidual (barCentralizer (Subgroup.zpowers a) X)) ∧
        3 ∣ Nat.card (perfectResidual (barCentralizer (Subgroup.zpowers a) X))

end KFacts

@[expose] def KF89JMult : Prop :=
  ∀ (P R : Type) [Group P] [Finite P] [Group R] (f : P →* R), Function.Surjective f →
    Group.IsPerfect P → f.ker ≤ Subgroup.center P → Nat.Coprime (Nat.card f.ker) 6 →
    Sec4.IsType419Theta R → Function.Injective f

namespace Item89Res2

variable {G : Type} [Group G] [Finite G]

theorem ker_modThetaOnto_eq {L K : Subgroup G} (hKL : K ≤ L)
    (hθ : ∀ N : Subgroup (imageModTheta L K), N.Normal → Group.IsSolvable N →
      ¬ 3 ∣ Nat.card N → N = ⊥) :
    (Item87Proof.modThetaOnto hKL).ker = aschbacherSolvableCore 3 K := by
  obtain ⟨hθs, -, hθ3, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set ρ := Item87Proof.modThetaOnto hKL with hρ
  have hρs : Function.Surjective ρ := Item87Proof.modThetaOnto_surjective hKL
  have hkθ : ρ.ker ≤ aschbacherSolvableCore 3 K :=
    hθmax _ (MonoidHom.normal_ker ρ) (Item87Proof.isSolvable_ker_modThetaOnto hKL)
      (Item87Proof.not_three_dvd_card_ker_modThetaOnto hKL)
  set M := (aschbacherSolvableCore 3 K).map ρ with hM
  have hMn : M.Normal := by
    have : (aschbacherSolvableCore 3 K).Normal := inferInstance
    exact this.map ρ hρs
  have hMs : Group.IsSolvable M := by
    have := hθs
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hM1 : M = ⊥ := hθ M hMn hMs hM3
  refine le_antisymm hkθ ?_
  intro k hk
  rw [MonoidHom.mem_ker]
  have : ρ k ∈ M := Subgroup.mem_map_of_mem ρ hk
  rwa [hM1, Subgroup.mem_bot] at this

theorem exists_factor {J P R : Type*} [Group J] [Group P] [Group R] (f₁ : J →* P) (f₂ : J →* R)
    (h1 : Function.Surjective f₁) (h2 : Function.Surjective f₂) (hle : f₁.ker ≤ f₂.ker) :
    ∃ g : P →* R, (∀ j, g (f₁ j) = f₂ j) ∧ Function.Surjective g ∧ g.ker = f₂.ker.map f₁ := by
  set e := QuotientGroup.quotientKerEquivOfSurjective f₁ h1 with he
  set g : P →* R := (QuotientGroup.lift f₁.ker f₂ hle).comp e.symm.toMonoidHom with hg
  have hgf : ∀ j, g (f₁ j) = f₂ j := by
    intro j
    have h : e.symm (f₁ j) = (j : J ⧸ f₁.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [hg, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h,
      QuotientGroup.lift_mk]
  refine ⟨g, hgf, fun r => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := h2 r
    exact ⟨f₁ j, hgf j⟩
  · ext p
    obtain ⟨j, rfl⟩ := h1 p
    rw [MonoidHom.mem_ker, hgf, Subgroup.mem_map]
    constructor
    · intro hj
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j', hj', hjj'⟩
      have hk : j'⁻¹ * j ∈ f₁.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hjj', inv_mul_cancel]
      have hk2 := hle hk
      rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp hj', inv_one, one_mul] at hk2
      exact hk2

theorem eq_bot_of_normal_of_isSolvable {S : Type} [Group S] [IsSimpleGroup S]
    (hS : Group.IsPerfect S) (N : Subgroup S) (hN : N.Normal) (hNs : Group.IsSolvable N) :
    N = ⊥ := by
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hs : Group.IsSolvable S := by
      have e : (⊤ : Subgroup S) ≃* S := Subgroup.topEquiv
      rw [h] at hNs
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact Sec4.Item419ThetaProof.not_isSolvable_of_isPerfect hS hs

theorem coprime_six_of_odd {n : ℕ} (hodd : Odd n) (h3 : ¬ 3 ∣ n) : Nat.Coprime n 6 := by
  have h2 : Nat.Coprime n 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])).symm
  have h3' : Nat.Coprime n 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3 |>.symm
  have : (6 : ℕ) = 2 * 3 := by norm_num
  rw [this]
  exact Nat.Coprime.mul_right h2 h3'

end Item89Res2

theorem kF89JCompNe_of (h45 : Sec4.Item4_5) (h84 : Pair84A) (hGW : Sec6.GWLBalanceStatement)
    (hT : KF89JCentType) (hM : KF89JMult) : KF89JCompNe := by
  intro G _ _ A c L a b X n h hJ
  set H := Subgroup.centralizer ({a} : Set G) with hH
  intro Y₀ hY₀ hIJ hb
  have hG := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hk := h84 G A c L a b X n h
  have haN : a ∈ Subgroup.normalizer (X : Set G) := by
    rcases hk with h' | h'
    · exact h'.mem_normalizer
    · exact h'.mem_normalizer
  obtain ⟨-, -, -, -, -, e, m, hem⟩ := h.mem_pairOmega
  have hm : 1 ≤ m := hem.2.2.1
  obtain ⟨htype, hR3⟩ := hT G X a m hm (Item87Proof.isGammaType_of_isGammaIndex hem)
    h.not_unitary ha3 hk h.gTwoPartner
  set C := barCentralizer (Subgroup.zpowers a) X with hC
  set J := sec8J X a with hJdef
  have hJeq : J = inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) := rfl
  have hJX : J ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hJa : J ≤ Subgroup.centralizer ({a} : Set G) :=
    (Item87Proof.residual_le _).trans inf_le_right
  have hJperf : Group.IsPerfect J := Item87Proof.isPerfect_residual _
  have himg : imageModTheta X J = inSubgroup perfectResidual C :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by rwa [pow_one]⟩
  set R' := imageModTheta X J with hR'
  have eR : R' ≃* perfectResidual C :=
    (MulEquiv.subgroupCongr himg).trans
      ((perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm
  have htype' : Sec4.IsType419Theta R' := Sec4.Item419ThetaProof.isType419Theta_of_mulEquiv eR htype
  have hR'perf : Group.IsPerfect R' := by
    have := hJperf
    exact Group.IsPerfect.ofSurjective (f := Item87Proof.modThetaOnto hJX)
      (Item87Proof.modThetaOnto_surjective hJX)
  have hR'simple : IsSimpleGroup R' :=
    Sec4.Item419ThetaProof.isSimpleGroup_of_isType419Theta htype' hR'perf
  have hR'q : IsQuasisimple R' :=
    Sec4.Item419ThetaProof.isQuasisimple_of_isType419Theta htype' hR'perf
  have hθR' : ∀ N : Subgroup R', N.Normal → Group.IsSolvable N → ¬ 3 ∣ Nat.card N → N = ⊥ :=
    fun N hN hNs _ => Item89Res2.eq_bot_of_normal_of_isSolvable hR'perf N hN hNs
  have hkerJ := Item89Res2.ker_modThetaOnto_eq hJX hθR'
  obtain ⟨eJ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hJX hθR'
  have hJq : IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J) :=
    LocalCores.isQuasisimple_of_mulEquiv eJ.symm hR'q
  have hJ3 : 3 ∣ Nat.card J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 J),
      Nat.card_congr eJ.toEquiv, Nat.card_congr eR.toEquiv]
    exact Dvd.dvd.mul_right hR3 _
  have hJmem : J ∈ thetaComponentsIn (Subgroup.centralizer {b} ⊓ Subgroup.centralizer {a}) :=
    Item87Proof.mem_thetaComponentsIn_residual hX hJq
  set N := aschbacherSolvableCore 3 ↥H with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hNs : Group.IsSolvable N := Sec4.Item419ThetaProof.isSolvable_theta _
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three).2.2.1
  set Y := Y₀.map H.subtype with hYdef
  have hYH : Y ≤ H := Subgroup.map_subtype_le _
  have hYat : Y ∈ thetaComponentsAt 3 a := ⟨Y₀, hY₀, rfl⟩
  have hJY : J ≤ Y := le_sup_right.trans hIJ
  have hJb : J ≤ Subgroup.centralizer ({b} : Set G) := hJX.trans hXb
  have hJYb : J ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) := le_inf hJY hJb
  have hYbCab : Y ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer {b} ⊓ Subgroup.centralizer {a} :=
    le_inf inf_le_right (inf_le_left.trans hYH)
  have hJYbmem := PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hJYb hYbCab
    (mem_thetaComponentsIn_iff.mp hJmem).2
  have hS4 : SectionFourHyp ↥H := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG ha1)
  have hB3 := Sec6.bThreeProperty_of_three_dvd hGW hS4 (X := Y) ⟨Y₀, hY₀, rfl⟩ hb hb3 hJYb
    hJperf hJYbmem.2.1 hJq hJ3
  have hθY : inSubgroup (aschbacherSolvableCore 3) Y ≤ inSubgroup (aschbacherSolvableCore 3) H := by
    rw [PartOne.theta_eq_inf_of_mem_thetaComponentsAt Nat.prime_three hYat]
    exact inf_le_right
  set K' := (J.subgroupOf H).map π with hK'
  have hJH : J ≤ H := hJa
  set f₁ : J →* K' := (π.comp (Subgroup.inclusion hJH)).codRestrict K' (fun j =>
    ⟨Subgroup.inclusion hJH j, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩) with hf₁
  have hf₁s : Function.Surjective f₁ := by
    rintro ⟨q, ⟨y, hy, rfl⟩⟩
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hf₁ker : ∀ j : J, j ∈ f₁.ker ↔ (j : G) ∈ inSubgroup (aschbacherSolvableCore 3) H := by
    intro j
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 := congrArg Subtype.val h1
      change π (Subgroup.inclusion hJH j) = 1 at h2
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact ⟨_, h2, rfl⟩
    · rintro ⟨y, hy, hyj⟩
      apply Subtype.ext
      change π (Subgroup.inclusion hJH j) = 1
      have : Subgroup.inclusion hJH j = y := Subtype.ext hyj.symm
      rw [this, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy
  set f₂ := Item87Proof.modThetaOnto hJX with hf₂
  have hf₂s : Function.Surjective f₂ := Item87Proof.modThetaOnto_surjective hJX
  have hker12 : f₁.ker ≤ f₂.ker := by
    rw [hkerJ]
    obtain ⟨-, -, -, hθmax, -⟩ :=
      solvable_prime_complement_core_characterization (H := J) Nat.prime_three
    let ι : f₁.ker →* N :=
      { toFun := fun j => ⟨Subgroup.inclusion hJH j, by
          obtain ⟨y, hy, hyj⟩ := (hf₁ker j).mp j.2
          have : Subgroup.inclusion hJH (j : J) = y := Subtype.ext hyj.symm
          rw [this]
          exact hy⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro u v huv
      have h' := congrArg (fun w : N => ((w : H) : G)) huv
      exact Subtype.ext (Subtype.ext h')
    refine hθmax _ (MonoidHom.normal_ker f₁) ?_ ?_
    · have := hNs
      exact Group.isSolvable_of_isSolvable_injective hι
    · exact fun h3 => hN3 (h3.trans (Subgroup.card_dvd_of_injective ι hι))
  obtain ⟨g, hgf, hgs, hgker⟩ := Item89Res2.exists_factor f₁ f₂ hf₁s hf₂s hker12
  have hK'perf : Group.IsPerfect K' := by
    have := hJperf
    exact Group.IsPerfect.ofSurjective (f := f₁) hf₁s
  have hcen : g.ker ≤ Subgroup.center K' := by
    rw [hgker, hkerJ]
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k'
    obtain ⟨j, rfl⟩ := hf₁s k'
    have htJ : (t : G) ∈ inSubgroup (aschbacherSolvableCore 3) J := ⟨t, ht, rfl⟩
    have hcomm : (⁅t, j⁆ : J) ∈ f₁.ker := by
      rw [hf₁ker]
      apply hθY
      apply hB3
      exact Subgroup.commutator_mem_commutator htJ j.2
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      at hcomm
    have h1 : f₁ t * f₁ j * (f₁ t)⁻¹ = f₁ j := mul_inv_eq_one.mp hcomm
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hcop : Nat.Coprime (Nat.card g.ker) 6 := by
    have hAb : A ≤ Subgroup.centralizer ({b} : Set G) :=
      Item87Proof.le_centralizer_of_isElemAbelian hAel hbA
    have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
      Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45
        (hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hb1)) hAb hAel
        ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩ X h.pairRel.2.2.1
    have hAθ := PartOne.le_normalizer_theta_of_le_normalizer Nat.prime_three hAX
    have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 X) :=
      (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
    have hcardθ : Nat.card (inSubgroup (aschbacherSolvableCore 3) X) =
        Nat.card (aschbacherSolvableCore 3 X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    have hodd := odd_card_of_le_normalizer hG.localRank_three.le hAel h.card_eq
      (by rwa [hcardθ]) hAθ
    rw [hcardθ] at hodd
    have hcopX := Item89Res2.coprime_six_of_odd hodd hθ3
    have hd1 : Nat.card g.ker ∣ Nat.card (aschbacherSolvableCore 3 J) := by
      rw [hgker, hkerJ]
      exact Subgroup.card_map_dvd _ _
    have hd2 : Nat.card (aschbacherSolvableCore 3 J) ∣ Nat.card (aschbacherSolvableCore 3 X) := by
      rw [← hkerJ]
      exact Subgroup.card_dvd_of_injective _ (Item87Proof.kerModThetaEmb_injective hJX)
    exact Nat.Coprime.coprime_dvd_left (hd1.trans hd2) hcopX
  have hginj := hM K' R' g hgs hK'perf hcen hcop htype'
  set eK : K' ≃* R' := MulEquiv.ofBijective g ⟨hginj, hgs⟩ with heK
  have htypeK : Sec4.IsType419Theta K' :=
    Sec4.Item419ThetaProof.isType419Theta_of_mulEquiv eK htype'
  have hK'q : IsQuasisimple K' :=
    Sec4.Item419ThetaProof.isQuasisimple_of_isType419Theta htypeK hK'perf
  set b' : H := ⟨b, hb⟩ with hb'
  set M₀ := Subgroup.centralizer ({b'} : Set H) with hM₀
  have hM₀map : M₀.map H.subtype = Subgroup.centralizer {b} ⊓ Subgroup.centralizer {a} := by
    rw [hM₀, GroupTheory.SteinbergBY.map_subtype_centralizer_singleton H b', inf_comm]
  have hJ'mem : J.subgroupOf H ∈ thetaComponentsIn M₀ :=
    Item87Proof.subgroupOf_mem_thetaComponentsIn hM₀map hJmem
  have hK'mem := Sec4.Item419ThetaProof.map_mem_thetaComponentsIn_quotient N hNs hN3 hJ'mem
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hpg : IsPGroup 3 (Subgroup.zpowers b') := by
    refine IsPGroup.iff_card.mpr ⟨1, ?_⟩
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hb'3 (fun h1 => hb1 (congrArg Subtype.val h1))
  have hkerπ : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hN3
  have hCmap : M₀.map π = Subgroup.centralizer ({π b'} : Set (H ⧸ N)) := by
    have h' :=
      RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
        3 Nat.prime_three π (QuotientGroup.mk'_surjective _) hkerπ _ hpg
    rwa [← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
      MonoidHom.map_zpowers,
      ← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at h'
  rw [hCmap] at hK'mem
  obtain ⟨hK'C, hK'C'⟩ := mem_thetaComponentsIn_iff.mp hK'mem
  have hK'Y : K' ≤ Y₀.map π := by
    rintro _ ⟨y, hy, rfl⟩
    have hyY : (y : G) ∈ Y := hJY (Subgroup.mem_subgroupOf.mp hy)
    obtain ⟨y', hy', hyy'⟩ := hyY
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact ⟨y', hy', rfl⟩
  have hK'le : K' ≤ Y₀.map π ⊓ Subgroup.centralizer ({π b'} : Set (H ⧸ N)) := le_inf hK'Y hK'C
  have hK'sub := PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hK'le inf_le_right
    hK'C'
  refine ⟨⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'le).symm hK'q,
    hK'sub.2.1⟩, ?_, ?_⟩
  · exact Sec4.Item419ThetaProof.isType419Theta_of_mulEquiv (eK.trans eR) htype
  · rintro ⟨e6⟩
    exact ⟨(eK.trans eR).symm.trans e6⟩

end CFSG.RankThree.PartTwo.Sec8
