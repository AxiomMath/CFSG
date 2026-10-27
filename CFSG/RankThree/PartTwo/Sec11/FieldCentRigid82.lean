module

public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

namespace FieldCentRigid82

theorem center_eq_bot_of_isType424 {X : Type} [Group X] (hX : IsType424 X) :
    Subgroup.center X = ⊥ := by
  rcases hX with ⟨n, -, ⟨e⟩⟩ | ⟨p, n, hp, -, -, ⟨e⟩⟩ | ⟨n, hn, ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩⟩
  · exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (Sec4.projSLEquivPSL _))
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  · exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (Sec4.projSLEquivPSL _))
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  · have h : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, hn, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
    have hn2 : 2 ≤ n := by
      by_contra hn2
      obtain rfl : n = 1 := by omega
      norm_num at hq
    have hq2 : 2 < 2 ^ n :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
    exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans φ.symm)
      (KFacts.center_unitaryPSU_three_eq_bot h hq2)
  · obtain ⟨φ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
    exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans φ)
      (KFacts.center_projectiveSL_three_eq_bot (by rwa [GaloisField.card 2 n (by omega)]))

theorem isFieldCentClassical_of_projSL_two {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 2 F) : IsFieldCentClassical X :=
  Or.inl ⟨F, inferInstance, inferInstance, ⟨e.trans (Sec4.projSLEquivPSL F)⟩⟩

theorem isFieldCentClassical_of_isoLThreeMinusPi {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec8.IsoLThreeMinusPi X 2 n) : IsFieldCentClassical X := by
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · have h : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, hn, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
    have hn2 : 2 ≤ n := by
      by_contra hn2
      obtain rfl : n = 1 := by omega
      norm_num at hq
    have hq2 : 2 < 2 ^ n :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
    exact Or.inr (Or.inr ⟨2, n, GaloisField 2 (2 * n), inferInstance, h, hq, hq2,
      ⟨e.trans φ.symm⟩⟩)
  · obtain ⟨φ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
    exact Or.inr (Or.inl ⟨GaloisField 2 n, inferInstance, inferInstance,
      by rwa [GaloisField.card 2 n (by omega)], ⟨e.trans φ⟩⟩)

theorem isSolvable_of_isSLThreePiAt_two {X : Type} [Group X]
    (hX : Sec4.IsSLThreePiAt X (2 ^ 1)) : Group.IsSolvable X := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := KFacts.exists_slPi_of_isSLThreePiAt_two_pow le_rfl hX
  cases π with
  | false =>
    have := Sec13.isSolvable_slPi_two hK (by norm_num)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  | true => exact absurd (show 2 ^ 1 % 3 = 1 from hq) (by norm_num)

theorem eq_top_of_isSubnormal_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.IsSubnormal) (hNp : Group.IsPerfect N) (hN1 : N ≠ ⊥) : N = ⊤ := by
  have hcentral : ¬ N ≤ Subgroup.center Q := by
    intro hle
    apply hN1
    have hcomm : ⁅N, N⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro n hn m _
      exact Subgroup.mem_center_iff.mp (hle hn) m
    rw [← Subgroup.isPerfect_iff.mp hNp, hcomm]
  have h1 : (N.map (QuotientGroup.mk' (Subgroup.center Q))).IsSubnormal :=
    hN.map (QuotientGroup.mk'_surjective _)
  rcases h1.eq_bot_or_top_of_isSimpleGroup hQ.2.1 with hbot | htop
  · exfalso
    apply hcentral
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  · have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
    have hNn : N.Normal := by
      constructor
      intro m hm q
      have hq : q ∈ N ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top q
      obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hq
      have hzm : z * m * z⁻¹ = m := by
        rw [← Subgroup.mem_center_iff.mp hz m, mul_inv_cancel_right]
      have e : n * z * m * (n * z)⁻¹ = n * (z * m * z⁻¹) * n⁻¹ := by group
      rw [e, hzm]
      exact N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ N with hle | htop
    · exact absurd hle hcentral
    · exact htop

end FieldCentRigid82

namespace FieldCentRigid82

variable {G : Type} [Group G] [Finite G]

theorem barCentralizer_eq_eqLocus {Y : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) :
    Sec8.barCentralizer (Subgroup.zpowers c) Y =
      (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y)) := by
  ext z
  exact KFacts.mem_barCentralizer_zpowers_iff hcN z

theorem false_of_card_center_eq_three {Y K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hQ : CFSG.IsQuasisimple ((Sec4.thetaQuotMulAut Y
      (Sec4.compAction Y ⟨c, hcN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y))))
    (hZ3 : Nat.card (Subgroup.center ((Sec4.thetaQuotMulAut Y
      (Sec4.compAction Y ⟨c, hcN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y)))) = 3)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) : False := by
  set α := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hα
  set F := α.toMonoidHom.eqLocus (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y)) with hF
  set M := (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) with hM
  obtain ⟨K', hK', rfl⟩ := hK
  have hrange : (cMap Y c).range = F := range_cMap hcN hc3
  have hmem : ∀ m, cMap Y c m ∈ F := fun m => hrange ▸ ⟨m, rfl⟩
  set ψ : M →* F := (cMap Y c).codRestrict F hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [← hrange] at hz
    obtain ⟨m, rfl⟩ := hz
    exact ⟨m, rfl⟩
  have hne : K'.map ψ ≠ ⊥ := by
    intro hbot
    apply fieldCent_map_cMap_ne_bot hK'
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : ψ k ∈ K'.map ψ := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have : Group.IsPerfect K' := hK'.1
  have htop : K'.map ψ = ⊤ :=
    eq_top_of_isSubnormal_of_isQuasisimple hQ (hK'.2.1.map hψs) (Group.IsPerfect.map _) hne
  set χ : K' →* F := ψ.comp K'.subtype with hχ
  have hχs : Function.Surjective χ := by
    intro z
    have hz : z ∈ K'.map ψ := htop ▸ Subgroup.mem_top z
    obtain ⟨k, hk, rfl⟩ := hz
    exact ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨-, -, hθ3, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K') Nat.prime_three
  obtain ⟨-, -, hθY3, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  have hkker : ∀ k : χ.ker, Subgroup.inclusion (inf_le_left : M ≤ Y) ((k : K') : M) ∈
      aschbacherSolvableCore 3 Y := fun k => by
    have h1 : χ (k : K') = 1 := MonoidHom.mem_ker.mp k.2
    have h2 : cMap Y c ((k : K') : M) = 1 := congrArg Subtype.val h1
    change QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
      (Subgroup.inclusion inf_le_left ((k : K') : M)) = 1 at h2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  set f : χ.ker →* aschbacherSolvableCore 3 Y :=
    ((Subgroup.inclusion (inf_le_left : M ≤ Y)).comp (K'.subtype.comp χ.ker.subtype)).codRestrict
      _ hkker with hf
  have hfinj : Function.Injective f := fun y z hyz => Subtype.ext (Subtype.ext (Subtype.ext (by
    have := congrArg (fun w : aschbacherSolvableCore 3 Y => ((w : Y) : G)) hyz
    exact this)))
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
    (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  have hker : χ.ker ≤ aschbacherSolvableCore 3 K' := by
    refine hmax _ inferInstance (Group.isSolvable_of_isSolvable_injective hfinj) ?_
    intro h3
    apply hθY3
    rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv] at h3
    exact h3.trans (Subgroup.card_subgroup_dvd_card _)
  have hZ1 : Subgroup.center F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hz3 : orderOf z ∣ 3 := by
    have h := orderOf_dvd_natCard (⟨z, hzZ⟩ : Subgroup.center F)
    rwa [hZ3, Subgroup.orderOf_mk] at h
  obtain ⟨k, rfl⟩ := hχs z
  have hkc : (k : K' ⧸ aschbacherSolvableCore 3 K') ∈
      Subgroup.center (K' ⧸ aschbacherSolvableCore 3 K') := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H k' =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
        Subgroup.mem_center_iff.mp hzZ (χ k'), inv_mul_cancel]
  have hk1 : (k : K' ⧸ aschbacherSolvableCore 3 K') ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    apply hz1'
    have hcop : Nat.Coprime 3 (Nat.card (aschbacherSolvableCore 3 K')) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
    have hdvd : orderOf (χ k) ∣ Nat.card (aschbacherSolvableCore 3 K') :=
      (orderOf_map_dvd χ k).trans (Subgroup.orderOf_dvd_natCard _ h1)
    exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left hz3 hcop).eq_one_of_dvd hdvd)
  set e : K' ≃* K'.map M.subtype := K'.equivMapOfInjective M.subtype M.subtype_injective with he
  have hZ' : Subgroup.center (K' ⧸ aschbacherSolvableCore 3 K') = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)) hZK
  rw [hZ', Subgroup.mem_bot] at hkc
  exact hk1 hkc

end FieldCentRigid82

section Main


theorem FieldCentRigid82.false_of_isSLThreePiAt {G : Type} [Group G] [Finite G] {Y K : Subgroup G}
    {c : G} {m : ℕ} (hm : 1 ≤ m)
    (hY : Sec4.IsSLThreePiAt (Y ⧸ aschbacherSolvableCore 3 Y) (2 ^ (3 * m)))
    (hf : KFacts.InducesStdKind Y c .field) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K)) : False := by
  have hcN := hf.mem_normalizer
  have hBF := FieldCentRigid82.barCentralizer_eq_eqLocus hcN
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    have hsol := FieldCentRigid82.isSolvable_of_isSLThreePiAt_two
      (KFacts.isSLThreePiAt_barCentralizer_of_field le_rfl hY hc3 (Or.inl hf))
    rw [hBF] at hsol
    exact fieldCent_false_of_isSolvable hcN hc3 hK hsol
  · obtain ⟨hQ, hZ3, -⟩ := KFacts.barCentralizer_facts_of_field hm2 hY hcN hc3 (Or.inl hf)
    rw [hBF] at hQ hZ3
    exact FieldCentRigid82.false_of_card_center_eq_three hcN hc3 hQ hZ3 hK
      (FieldCentRigid82.center_eq_bot_of_isType424 hT)

@[expose] def FieldCentRigid82 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c t : G),
    KFacts.InducesStdKind Y c .field → Sec8.IsList82One (Y ⧸ aschbacherSolvableCore 3 Y) →
    c ^ 3 = 1 → K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    t ∈ Subgroup.normalizer (Y : Set G) → (∃ k : ℕ, t ^ 3 ^ k = 1) → t * c = c * t →
    (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) →
      ∃ i : ℕ, t * c ^ i ∈ Sec4.thetaQuotCentralizer Y

theorem fieldCentRigid82 : FieldCentRigid82 := by
  intro G _ _ Y K c t hf hY hc3 hK hT htN _ _ htK
  have hout := KFacts.InducesStdKind.inducesOuterTheta Y hf (by decide)
  have hcl : IsFieldCentClassical (Y ⧸ aschbacherSolvableCore 3 Y) →
      ∃ i : ℕ, t * c ^ i ∈ Sec4.thetaQuotCentralizer Y := fun hcl =>
    exists_mul_pow_mem_thetaQuotCentralizer_of_classical hcl hout hc3 hK htN htK
  rcases hY with ⟨⟨e⟩⟩ | ⟨p, n, hp, -, -, ⟨e⟩⟩ | ⟨m, hm, ⟨⟨e⟩⟩ | hL | hL⟩
  · exact hcl (FieldCentRigid82.isFieldCentClassical_of_projSL_two e)
  · exact hcl (FieldCentRigid82.isFieldCentClassical_of_projSL_two e)
  · exact hcl (FieldCentRigid82.isFieldCentClassical_of_projSL_two e)
  · exact hcl (FieldCentRigid82.isFieldCentClassical_of_isoLThreeMinusPi (by omega) hL)
  · exact (FieldCentRigid82.false_of_isSLThreePiAt hm hL hf hc3 hK hT).elim

end Main

end CFSG.RankThree.PartTwo.Sec11
