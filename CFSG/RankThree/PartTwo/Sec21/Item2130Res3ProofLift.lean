module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofThree
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.GroupTheory.SolvableHallNodes
import CFSG.Assembly.ComponentTypeDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.KFacts.K72Lift
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)

namespace Item2130Res3Proof

theorem map_centralizer_eq_of_coprime {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {N : Subgroup L} [N.Normal] (hNsol : Group.IsSolvable N) (hN3 : ¬ 3 ∣ Nat.card N) {b : G}
    (hbL : b ∈ L) (hb : IsPGroup 3 (Subgroup.zpowers b)) :
    Subgroup.centralizer ({((⟨b, hbL⟩ : L) : L ⧸ N)} : Set (L ⧸ N)) =
      (Subgroup.centralizer ({(⟨b, hbL⟩ : L)} : Set L)).map (QuotientGroup.mk' N) := by
  set D := Subgroup.zpowers b with hD
  have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hbL)
  let : MulDistribMulAction D L :=
    MulDistribMulAction.compHom L (L.normalizerMonoidHom.comp (Subgroup.inclusion hDL))
  have hsmul : ∀ (d : D) (l : L), ((d • l : L) : G) = d * l * (d : G)⁻¹ := fun _ _ => rfl
  have hNinv : IsInvariant D L N := by
    refine ⟨fun d g => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp d.2
    have he : d • g = ⟨b, hbL⟩ ^ k * g * (⟨b, hbL⟩ ^ k)⁻¹ := by
      apply Subtype.ext
      rw [hsmul, ← hk]
      simp
    rw [he]
    constructor
    · intro hg
      exact ‹N.Normal›.conj_mem g hg _
    · intro hg
      have := ‹N.Normal›.conj_mem _ hg (⟨b, hbL⟩ ^ k)⁻¹
      simpa [mul_assoc] using this
  have hcop : Nat.Coprime (Nat.card D) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hb
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting N hNinv hNsol hcop
  let : MulDistribMulAction D (L ⧸ N) :=
    CFSG.quotientMulDistribMulAction (A := D) (G := L) N hNinv
  let : MulAction.QuotientAction D N := CFSG.quotientAction_of_isInvariant (A := D) N hNinv
  have hfixL : fixedPointSubgroup D L = Subgroup.centralizer ({(⟨b, hbL⟩ : L)} : Set L) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h := congrArg Subtype.val (hx ⟨b, Subgroup.mem_zpowers b⟩)
      rw [hsmul] at h
      apply Subtype.ext
      change (x : G) * b = b * x
      calc (x : G) * b = b * x * b⁻¹ * b := by rw [h]
        _ = b * x := by group
    · intro hx d
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp d.2
      apply Subtype.ext
      rw [hsmul, ← hk]
      have hc : Commute b (x : G) := (congrArg Subtype.val hx).symm
      rw [(hc.zpow_left k).eq, mul_inv_cancel_right]
  have hfixQ : fixedPointSubgroup D (L ⧸ N) =
      Subgroup.centralizer ({((⟨b, hbL⟩ : L) : L ⧸ N)} : Set (L ⧸ N)) := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsq : ∀ (d : D), d • (x : L ⧸ N) = ((d • x : L) : L ⧸ N) := fun d =>
      MulAction.Quotient.smul_coe (H := N) d x
    constructor
    · intro hx
      have h := hx ⟨b, Subgroup.mem_zpowers b⟩
      rw [hsq] at h
      have he : (⟨b, Subgroup.mem_zpowers b⟩ : D) • x = ⟨b, hbL⟩ * x * (⟨b, hbL⟩)⁻¹ :=
        Subtype.ext (hsmul _ _)
      rw [he, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h
      calc (x : L ⧸ N) * ((⟨b, hbL⟩ : L) : L ⧸ N) =
          ((⟨b, hbL⟩ : L) : L ⧸ N) * x * ((⟨b, hbL⟩ : L) : L ⧸ N)⁻¹ *
            ((⟨b, hbL⟩ : L) : L ⧸ N) := by rw [h]
        _ = ((⟨b, hbL⟩ : L) : L ⧸ N) * x := by group
    · intro hx d
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp d.2
      rw [hsq]
      have he : d • x = ⟨b, hbL⟩ ^ k * x * (⟨b, hbL⟩ ^ k)⁻¹ := by
        apply Subtype.ext
        rw [hsmul, ← hk]
        simp
      rw [he, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow]
      have hc : Commute ((⟨b, hbL⟩ : L) : L ⧸ N) (x : L ⧸ N) := hx.symm
      rw [(hc.zpow_left k).eq, mul_inv_cancel_right]
  rw [← hfixQ, ← hfixL]
  exact hlift

theorem theta_eq_ker_of_surjective {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
    (f : P →* Q) (hf : Function.Surjective f) (hθQ : aschbacherSolvableCore 3 Q = ⊥)
    (hks : Group.IsSolvable f.ker) (hk3 : ¬ 3 ∣ Nat.card f.ker) :
    aschbacherSolvableCore 3 P = f.ker := by
  obtain ⟨hθs, -, hθ3, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := P) Nat.prime_three
  apply le_antisymm
  · obtain ⟨-, -, -, hmaxQ, -⟩ :=
      solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
    have himgN : ((aschbacherSolvableCore 3 P).map f).Normal :=
      Subgroup.Normal.map inferInstance f hf
    have himgS : Group.IsSolvable ((aschbacherSolvableCore 3 P).map f) := by
      have := hθs
      exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
    have himg3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 P).map f) :=
      fun h => hθ3 (h.trans (Subgroup.card_map_dvd _ f))
    have hle := hmaxQ _ himgN himgS himg3
    rw [hθQ] at hle
    intro x hx
    rw [MonoidHom.mem_ker]
    exact Subgroup.mem_bot.mp (hle ⟨x, hx, rfl⟩)
  · exact hmax _ (MonoidHom.normal_ker f) hks hk3

theorem mem_zpowers_of_eq_mul {X : Type*} [Group X] [Finite X] {b i t : X} (hb3 : b ^ 3 = 1)
    (hbit : b = i * t) (hbt : Commute b t) (ht : Nat.Coprime (orderOf t) 3) :
    b ∈ Subgroup.zpowers i := by
  set m := orderOf t with hm
  have hi : i = b * t⁻¹ := by rw [hbit]; group
  have him : i ^ m = b ^ m := by
    rw [hi, (hbt.inv_right).mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one]
  have hcop : m.Coprime (orderOf b) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hb3) ht
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hk, ← him, ← pow_mul]
  exact Subgroup.npow_mem_zpowers i (m * k)

theorem inSubgroup_pCore_eq {G : Type*} [Group G] [Finite G] {I : Subgroup G} {b : G}
    (hbI : b ∈ I) (hbC : b ∈ Subgroup.centralizer (I : Set G)) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hZ : Nat.card (Subgroup.center (I ⧸ aschbacherSolvableCore 3 I)) = 3) :
    inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) = Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := I ⊓ Subgroup.centralizer (I : Set G) with hZdef
  set O := inSubgroup (CFSG.pCore 3) Z with hO
  have hbZ : b ∈ Z := ⟨hbI, hbC⟩
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  have hbO : Subgroup.zpowers b ≤ O := by
    rw [Subgroup.zpowers_le]
    have hnorm : (Subgroup.zpowers (⟨b, hbZ⟩ : Z)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have : g * x * g⁻¹ = x := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hZcomm _ g.2 _ x.2, mul_inv_cancel_right]
      rw [this]
      exact hx
    have h3 : IsPGroup 3 (Subgroup.zpowers (⟨b, hbZ⟩ : Z)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_eq_prime hb3 hb1, pow_one])
    have hP : (⟨b, hbZ⟩ : Z) ∈ CFSG.pCore 3 Z :=
      (le_sSup ⟨hnorm, h3⟩ : Subgroup.zpowers (⟨b, hbZ⟩ : Z) ≤ CFSG.pCore 3 Z)
        (Subgroup.mem_zpowers _)
    exact ⟨_, hP, rfl⟩
  have hOI : O ≤ I := (Subgroup.map_subtype_le _).trans inf_le_left
  have hOC : O ≤ Subgroup.centralizer (I : Set G) := (Subgroup.map_subtype_le _).trans inf_le_right
  have hO3 : IsPGroup 3 O := (CFSG.pCore_isPGroup).map _
  have hO3' : IsPGroup 3 (O.subgroupOf I) := hO3.comap_subtype
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hO3'
  have hcard : Nat.card ((O.subgroupOf I).map (QuotientGroup.mk' (aschbacherSolvableCore 3 I))) =
      Nat.card O := by
    have hinj' : Function.Injective
        ((QuotientGroup.mk' (aschbacherSolvableCore 3 I)).comp (O.subgroupOf I).subtype) :=
      fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
    calc Nat.card ((O.subgroupOf I).map (QuotientGroup.mk' (aschbacherSolvableCore 3 I)))
        = Nat.card ((QuotientGroup.mk' (aschbacherSolvableCore 3 I)).comp
            (O.subgroupOf I).subtype).range := by
          rw [MonoidHom.range_comp, Subgroup.range_subtype]
      _ = Nat.card (O.subgroupOf I) := Nat.card_range_of_injective hinj'
      _ = Nat.card O := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOI).toEquiv
  have hle : (O.subgroupOf I).map (QuotientGroup.mk' (aschbacherSolvableCore 3 I)) ≤
      Subgroup.center (I ⧸ aschbacherSolvableCore 3 I) := by
    rintro _ ⟨o, ho, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    change (y : I ⧸ aschbacherSolvableCore 3 I) * (o : I ⧸ _) = (o : I ⧸ _) * (y : I ⧸ _)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hoC := hOC (Subgroup.mem_subgroupOf.mp ho)
    exact (Subgroup.mem_centralizer_iff.mp hoC y y.2)
  have hOle : Nat.card O ≤ 3 := by
    have h := Subgroup.card_le_of_le hle
    rw [hcard, hZ] at h
    exact h
  symm
  refine Subgroup.eq_of_le_of_card_ge hbO ?_
  rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  exact hOle

theorem map_inSubgroup_perfectResidual_of_finite {X Y : Type*} [Group X] [Finite X] [Group Y]
    [Finite Y] (f : X →* Y) (K : Subgroup X) :
    (inSubgroup perfectResidual K).map f = inSubgroup perfectResidual (K.map f) := by
  have h : (perfectResidual K).map (f.subgroupMap K) = perfectResidual (K.map f) :=
    RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq (f.subgroupMap K)
      (f.subgroupMap_surjective K)
  change ((perfectResidual K).map K.subtype).map f =
    (perfectResidual (K.map f)).map (K.map f).subtype
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

end Item2130Res3Proof

open Item2130Res3Proof

end CFSG.RankThree.PartTwo.Sec21
