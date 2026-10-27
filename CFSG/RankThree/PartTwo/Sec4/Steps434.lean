module

public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.RankThree.PartTwo.Source.NormalizedElementarySubgroup
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_mem_centralizer_of_gamma_le {A M : Subgroup G} (hA : Late.IsE27 A)
    (hM : gamma 2 A ≤ M) (hM3 : CFSG.Open.pRank 3 M = 3) {x : G}
    (hx : x ∈ Subgroup.centralizer (A : Set G)) (hx3 : x ^ 3 = 1) : x ∈ A := by
  by_contra hxA
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : IsMulCommutative A := hA.1.1
  have hcomm : ∀ a ∈ A, a * x = x * a := fun a ha => Subgroup.mem_centralizer_iff.mp hx a ha
  obtain ⟨hBc, hBcard⟩ := sup_zpowers_card (p := 3) hAc hxA hx3 hcomm
  have hBexp : ∀ y ∈ A ⊔ Subgroup.zpowers x, y ^ 3 = 1 := by
    have hle : A ⊔ Subgroup.zpowers x ≤ Source.omegaSubgroup (A ⊔ Subgroup.zpowers x) hBc 3 :=
      sup_le (fun a ha => ⟨Subgroup.mem_sup_left ha, hA.1.2 a ha⟩)
        (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers x), hx3⟩)
    exact fun y hy => (hle hy).2
  have hBN : A ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (A : Set G) hx))
  have hNM : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [hA.pRank_eq]; norm_num)).trans hM
  have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three M)
      ⟨A ⊔ Subgroup.zpowers x, hBN.trans hNM, ⟨hBc, hBexp⟩, by rw [hBcard, hA.2]; norm_num⟩
  omega

theorem Ctx434.rank3II_4_35 {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434 G A M Q) {x : G} (hx : x ∈ Subgroup.centralizer (A : Set G)) (hx3 : x ^ 3 = 1) :
    x ∈ A :=
  mem_of_mem_centralizer_of_gamma_le h.isE27 h.gamma_le h.pRank_eq hx hx3

theorem le_aschbacherSolvableCore_of_isPGroup {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {N : Subgroup G} (hN : N.Normal) (hNp : IsPGroup p N) : N ≤ aschbacherSolvableCore 3 G :=
  (le_sSup ⟨hN, hNp⟩ : N ≤ CFSG.pCore p G).trans
    ((solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.2.2.2 p hp hp3)

theorem pCore_three_le_centralizer_layer :
    CFSG.pCore 3 G ≤ Subgroup.centralizer (layer G : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsolv : Group.IsSolvable (CFSG.pCore 3 G) := by
    have := IsPGroup.isNilpotent (CFSG.pCore_isPGroup (p := 3) (G := G))
    infer_instance
  have h := (component_solvable_centralizer hsolv
    (CFSG.pCore_normal (p := 3) (G := G)).isSubnormal).2
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)

omit [Finite G] in
theorem layer_centralizer_layer_eq_bot :
    layer (Subgroup.centralizer (layer G : Set G)) = ⊥ := by
  set C := Subgroup.centralizer (layer G : Set G) with hC
  have hCn : C.Normal := by
    have : (layer G).Characteristic := layer_characteristic
    exact Subgroup.normal_centralizer (H := layer G)
  apply layer_eq_bot_of_forall
  intro K hK
  set K' := K.map C.subtype with hK'
  have hK'c : IsComponent K' :=
    ⟨isQuasisimple_of_mulEquiv (K.equivMapOfInjective _ C.subtype_injective) hK.1,
      hK.2.trans' hCn.isSubnormal⟩
  have hle1 : K' ≤ layer G := component_le_layer hK'c
  have hle2 : K' ≤ C := Subgroup.map_subtype_le K
  have hcomm : ∀ a b : K', a * b = b * a := by
    intro a b
    apply Subtype.ext
    have hb : (b : G) ∈ C := hle2 b.2
    show (a : G) * b = b * a
    exact Subgroup.mem_centralizer_iff.mp hb a (hle1 a.2)
  have : Nontrivial K' := isQuasisimple_nontrivial hK'c.1
  have : Group.IsPerfect K' := hK'c.1.1
  exact Group.IsPerfect.not_isSolvable K' (Group.isSolvable_of_comm hcomm)

theorem fittingSubgroup_centralizer_layer (hθ : aschbacherSolvableCore 3 G = ⊥) :
    fittingSubgroup (Subgroup.centralizer (layer G : Set G)) =
      CFSG.pCore 3 (Subgroup.centralizer (layer G : Set G)) := by
  set C := Subgroup.centralizer (layer G : Set G) with hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCn : C.Normal := by
    have : (layer G).Characteristic := layer_characteristic
    exact Subgroup.normal_centralizer (H := layer G)
  refine le_antisymm ?_ (pCore_le_fitting C 3)
  rw [fitting_eq_sup_pCore C]
  refine iSup_le fun p => ?_
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  by_cases hp3 : p.1.1 = 3
  · rw [hp3]
  ·
    have : Fact p.1.1.Prime := ⟨hp⟩
    have hnorm : ((CFSG.pCore p.1.1 C).map C.subtype).Normal := inferInstance
    have hpg : IsPGroup p.1.1 ((CFSG.pCore p.1.1 C).map C.subtype) :=
      (CFSG.pCore_isPGroup (p := p.1.1) (G := C)).map C.subtype
    have hle := le_aschbacherSolvableCore_of_isPGroup hp hp3 hnorm hpg
    rw [hθ, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at hle
    rw [hle]
    exact bot_le

theorem generalizedFitting_centralizer_layer (hθ : aschbacherSolvableCore 3 G = ⊥) :
    inSubgroup generalizedFitting (Subgroup.centralizer (layer G : Set G)) = CFSG.pCore 3 G := by
  set C := Subgroup.centralizer (layer G : Set G) with hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCn : C.Normal := by
    have : (layer G).Characteristic := layer_characteristic
    exact Subgroup.normal_centralizer (H := layer G)
  have hF := fittingSubgroup_centralizer_layer hθ
  have hE := layer_centralizer_layer_eq_bot (G := G)
  rw [inSubgroup, generalizedFitting, hF, hE, sup_bot_eq]
  apply le_antisymm
  ·
    have hnorm : ((CFSG.pCore 3 C).map C.subtype).Normal := inferInstance
    exact le_sSup ⟨hnorm, (CFSG.pCore_isPGroup (p := 3) (G := C)).map C.subtype⟩
  ·
    have hOC : CFSG.pCore 3 G ≤ C := pCore_three_le_centralizer_layer
    have hsub : (CFSG.pCore 3 G).subgroupOf C ≤ CFSG.pCore 3 C := by
      refine le_sSup ⟨?_, ?_⟩
      · exact Subgroup.normal_subgroupOf (H := C) (N := CFSG.pCore 3 G)
      · exact (CFSG.pCore_isPGroup (p := 3) (G := G)).comap_of_injective C.subtype
          C.subtype_injective
    calc CFSG.pCore 3 G = ((CFSG.pCore 3 G).subgroupOf C).map C.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hOC).symm
      _ ≤ (CFSG.pCore 3 C).map C.subtype := Subgroup.map_mono hsub

theorem Ctx434.rank3II_4_36 {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434 G A M Q) :
    inSubgroup generalizedFitting (Subgroup.centralizer (layer G : Set G)) = CFSG.pCore 3 G :=
  generalizedFitting_centralizer_layer h.theta_eq_bot

theorem fittingSubgroup_eq_bot (hθ : aschbacherSolvableCore 3 G = ⊥)
    (hO : CFSG.pCore 3 G = ⊥) : fittingSubgroup G = ⊥ := by
  rw [fitting_eq_sup_pCore G, eq_bot_iff]
  refine iSup_le fun p => ?_
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  by_cases hp3 : p.1.1 = 3
  · rw [hp3, hO]
  · rw [← hθ]
    exact le_aschbacherSolvableCore_of_isPGroup hp hp3 (CFSG.pCore_normal (p := p.1.1) (G := G))
      (CFSG.pCore_isPGroup (p := p.1.1) (G := G))

theorem isSimpleGroup_layer (hθ : aschbacherSolvableCore 3 G = ⊥) (hO : CFSG.pCore 3 G = ⊥)
    (hL : IsQuasisimple (layer G)) : IsSimpleGroup (layer G) := by
  have hF := fittingSubgroup_eq_bot hθ hO
  have : (layer G).Characteristic := layer_characteristic
  have hZ : Subgroup.center (layer G) = ⊥ := by
    have hnorm : ((Subgroup.center (layer G)).map (layer G).subtype).Normal := inferInstance
    have hcomm : IsMulCommutative ((Subgroup.center (layer G)).map (layer G).subtype) := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      change (a : G) * b = b * a
      rw [← ha, ← hb]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' b').symm
    have hle : (Subgroup.center (layer G)).map (layer G).subtype ≤ fittingSubgroup G :=
      le_sSup ⟨hnorm, inferInstance⟩
    rw [hF, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (layer G).subtype_injective]
      at hle
    exact hle
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center (layer G))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have e := MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (layer G)))
    ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hL.2.1
  have : Nontrivial (layer G) := isQuasisimple_nontrivial hL
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem inf_ne_bot_of_gamma_le {A M : Subgroup G} (hA : Late.IsE27 A) (hM : gamma 2 A ≤ M)
    (hM3 : CFSG.Open.pRank 3 M = 3) {N : Subgroup G} [N.Normal] (hN : IsPGroup 3 N)
    (hN1 : N ≠ ⊥) : A ⊓ N ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal : G →* MulAut N).comp A.subtype)
  have hdvd : 3 ∣ Nat.card N := by
    rcases hN.card_eq_or_dvd with hc | hc
    · exact absurd (Subgroup.card_eq_one.mp hc) hN1
    · exact hc
  have hone : (1 : N) ∈ MulAction.fixedPoints A N := fun a => smul_one a
  obtain ⟨y, hy, hy1⟩ :=
    hA.isPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd hone
  have hyc : ∀ a ∈ A, a * (y : G) = y * a := by
    intro a ha
    have h1 : (a : G) * y * a⁻¹ = y := congrArg Subtype.val (hy ⟨a, ha⟩)
    calc a * (y : G) = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [h1]
  have hy1' : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h.symm)
  have hord : 3 ∣ Nat.card (Subgroup.zpowers (y : G)) := by
    rw [Nat.card_zpowers]
    obtain ⟨k, hk⟩ := (hN.to_le (Subgroup.zpowers_le.mpr y.2)).exists_card_eq
    rw [Nat.card_zpowers] at hk
    rw [hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hy1' (orderOf_eq_one_iff.mp (by simpa using hk))
    exact dvd_pow_self 3 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers (y : G)) 3 hord
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
  have hz3 : (z : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : G) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    omega
  have hzC : (z : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hk]
    exact (Commute.zpow_right (show Commute a (y : G) from hyc a ha) k).eq
  have hzA : (z : G) ∈ A := mem_of_mem_centralizer_of_gamma_le hA hM hM3 hzC hz3
  have hzN : (z : G) ∈ N := by
    rw [← hk]
    exact N.zpow_mem y.2 k
  intro hbot
  apply hz1
  have : (z : G) ∈ A ⊓ N := ⟨hzA, hzN⟩
  rw [hbot] at this
  exact this

theorem card_inf_centralizer_layer_le {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434 G A M Q) :
    Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := A ⊓ Subgroup.centralizer (layer G : Set G) with hD
  obtain ⟨k, hk⟩ := (h.isE27.isPGroup.to_le (inf_le_left : D ≤ A)).exists_card_eq
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> simp_all
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := D) (n := 2)
    (by rw [hk]; exact pow_dvd_pow 3 hk2)
  set B := K.map D.subtype with hB
  have hBD : B ≤ D := Subgroup.map_subtype_le K
  have hB9 : Nat.card B = 3 ^ 2 := by
    rw [hB, Subgroup.card_map_of_injective D.subtype_injective, hK]
  have hBA : B ≤ A := hBD.trans inf_le_left
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Source.isElemAbelian_of_le h.isE27.1 hBA
  have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
      ⟨B, le_rfl, hBe, hB9⟩
  apply h.not_le
  have hLB : layer G ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mp (hBD.trans inf_le_right)
  exact hLB.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((normalizer_le_gamma hBA hB2).trans h.gamma_le))

theorem Ctx434.rank3II_4_38 {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434 G A M Q) :
    (CFSG.pCore 3 G = ⊥ ∧ generalizedFitting G = layer G ∧ IsSimpleGroup (layer G)) ∨
      (A ⊓ CFSG.pCore 3 G = A ⊓ Subgroup.centralizer (layer G : Set G) ∧
        Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hO : CFSG.pCore 3 G = ⊥
  · left
    refine ⟨hO, ?_, isSimpleGroup_layer h.theta_eq_bot hO h.isQuasisimple⟩
    rw [generalizedFitting, fittingSubgroup_eq_bot h.theta_eq_bot hO, bot_sup_eq]
  · right
    have : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal
    have hne := inf_ne_bot_of_gamma_le h.isE27 h.gamma_le h.pRank_eq
      (CFSG.pCore_isPGroup (p := 3) (G := G)) hO
    have hle : A ⊓ CFSG.pCore 3 G ≤ A ⊓ Subgroup.centralizer (layer G : Set G) :=
      inf_le_inf_left _ pCore_three_le_centralizer_layer
    have hcard := card_inf_centralizer_layer_le h
    have h3 : 3 ≤ Nat.card (A ⊓ CFSG.pCore 3 G : Subgroup G) := by
      rcases ((CFSG.pCore_isPGroup (p := 3) (G := G)).to_le (inf_le_right :
          A ⊓ CFSG.pCore 3 G ≤ CFSG.pCore 3 G)).card_eq_or_dvd with hc | hc
      · exact absurd (Subgroup.card_eq_one.mp hc) hne
      · exact Nat.le_of_dvd Nat.card_pos hc
    have heq : A ⊓ CFSG.pCore 3 G = A ⊓ Subgroup.centralizer (layer G : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (hcard.trans h3)
    exact ⟨heq, le_antisymm hcard (heq ▸ h3)⟩

end CFSG.RankThree.PartTwo.Sec4
