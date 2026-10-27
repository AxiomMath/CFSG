module

import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem center_eq_bot_of_mulEquiv_five {Q : Type*} [Group Q] (hq : IsQuasisimple Q)
    (e : Q ≃* alternatingGroup (Fin 5)) : Subgroup.center Q = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup Q := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨-, hs', -⟩ := hq
    have := hs'.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hx ((QuotientGroup.eq_one_iff y).mpr (h ▸ Subgroup.mem_top y))

theorem isPGroup_center_of_type {Q : Type*} [Group Q] (hq : IsQuasisimple Q)
    (htype : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover Q (alternatingGroup (Fin 6))) :
    IsPGroup 3 (Subgroup.center Q) := by
  rcases htype with he | h6
  · obtain ⟨e⟩ := he
    rw [center_eq_bot_of_mulEquiv_five hq e]
    exact IsPGroup.of_bot
  · exact IsPGroup.of_card (n := 1) (by rw [h6.1, pow_one])

theorem card_of_type {Q : Type*} [Group Q] [Finite Q]
    (htype : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover Q (alternatingGroup (Fin 6))) :
    Nat.card Q = 60 ∨ Nat.card Q = 1080 := by
  rcases htype with he | h6
  · obtain ⟨e⟩ := he
    left
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
  · right
    rw [card_of_isTripleCover h6, card_alternatingGroup_six]

theorem three_dvd_card_quot_center_of_type {Q : Type*} [Group Q] [Finite Q]
    (hq : IsQuasisimple Q)
    (htype : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover Q (alternatingGroup (Fin 6))) :
    3 ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
  rcases htype with he | h6
  · obtain ⟨e⟩ := he
    have hZ1 : Nat.card (Subgroup.center Q) = 1 := by
      rw [center_eq_bot_of_mulEquiv_five hq e, Subgroup.card_bot]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)
    rw [hZ1, mul_one, Nat.card_congr e.toEquiv, card_alternatingGroup_five] at h
    rw [← h]
    norm_num
  · obtain ⟨-, ⟨e⟩⟩ := h6
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
    norm_num

theorem theta_eq_pCore_two_of_type {Y : Type*} [Group Y] [Finite Y]
    (hq : IsQuasisimple (Y ⧸ CFSG.pCore 2 Y))
    (htype : Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (Y ⧸ CFSG.pCore 2 Y) (alternatingGroup (Fin 6))) :
    aschbacherSolvableCore 3 Y = CFSG.pCore 2 Y := by
  have hθ := solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  refine le_antisymm ?_ (hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num))
  have h3 : 3 ∣ Nat.card (Y ⧸ CFSG.pCore 2 Y) := by
    rcases card_of_type htype with h | h <;> rw [h] <;> norm_num
  have hcore := pPrimeCore_three_eq_pCore_two
    (pPrimeCore_three_eq_bot_of_isQuasisimple hq h3 (isPGroup_center_of_type hq htype))
  rw [← hcore]
  have : (aschbacherSolvableCore 3 Y).Normal := by
    have := hθ.2.1
    infer_instance
  exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ.2.2.1⟩

theorem inSubgroup_theta_eq_pCoreOf_of_type {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hq : IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X))
    (htype : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥X ⧸ CFSG.pCore 2 ↥X) (alternatingGroup (Fin 6))) :
    inSubgroup (aschbacherSolvableCore 3) X = CFSG.Open.pCoreOf 2 X := by
  rw [CFSG.Open.pCoreOf, inSubgroup, theta_eq_pCore_two_of_type hq htype]

theorem isQuasisimple_theta_of_type {Y : Type*} [Group Y] [Finite Y]
    (hq : IsQuasisimple (Y ⧸ CFSG.pCore 2 Y))
    (htype : Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (Y ⧸ CFSG.pCore 2 Y) (alternatingGroup (Fin 6))) :
    IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (theta_eq_pCore_two_of_type hq htype)).symm hq

theorem type_theta_of_type {Y : Type*} [Group Y] [Finite Y]
    (hq : IsQuasisimple (Y ⧸ CFSG.pCore 2 Y))
    (htype : Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (Y ⧸ CFSG.pCore 2 Y) (alternatingGroup (Fin 6))) :
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (Y ⧸ aschbacherSolvableCore 3 Y) (alternatingGroup (Fin 6)) := by
  have e := QuotientGroup.quotientMulEquivOfEq (theta_eq_pCore_two_of_type hq htype)
  rcases htype with he5 | h6
  · obtain ⟨e5⟩ := he5
    exact Or.inl ⟨e.trans e5⟩
  · exact Or.inr (KFacts.KS14.isTripleCover_congr e.symm h6)

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaQuotCentralizer_of_mem_sectionCentralizer {A X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) {a : G}
    (ha : a ∈ Late.sectionCentralizer A X (inSubgroup (aschbacherSolvableCore 3) X)) :
    a ∈ Sec4.thetaQuotCentralizer X := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX ha.1, fun l hl => ?_⟩
  have h1 := ha.2 l hl
  have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta X (inv_mem hl)) _).mp h1
  have he : l⁻¹ * (a * l * a⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (a * l * a⁻¹) := by group
  rw [he] at h2
  exact h2

theorem mem_sectionCentralizer_of_mem_thetaQuotCentralizer {A X : Subgroup G} {a : G}
    (haA : a ∈ A) (ha : a ∈ Sec4.thetaQuotCentralizer X) :
    a ∈ Late.sectionCentralizer A X (inSubgroup (aschbacherSolvableCore 3) X) := by
  obtain ⟨-, hal⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp ha
  refine ⟨haA, fun l hl => ?_⟩
  have h1 := hal l hl
  have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta X hl) _).mp h1
  have he : l * (l⁻¹ * (a * l * a⁻¹)) * l⁻¹ = a * l * a⁻¹ * l⁻¹ := by group
  rw [he] at h2
  exact h2

theorem eq_one_of_inv_mul_mem_center {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q)
    (σ : MulAut Q) (h : ∀ x : Q, (σ x)⁻¹ * x ∈ Subgroup.center Q) : σ = 1 := by
  let f : Q →* Subgroup.center Q :=
    { toFun := fun x => ⟨(σ x)⁻¹ * x, h x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hc := Subgroup.mem_center_iff.mp (h x) ((σ y)⁻¹)
        change (σ (x * y))⁻¹ * (x * y) = (σ x)⁻¹ * x * ((σ y)⁻¹ * y)
        rw [map_mul, mul_inv_rev]
        calc (σ y)⁻¹ * (σ x)⁻¹ * (x * y) = ((σ y)⁻¹ * ((σ x)⁻¹ * x)) * y := by group
          _ = ((σ x)⁻¹ * x) * (σ y)⁻¹ * y := by rw [hc]
          _ = (σ x)⁻¹ * x * ((σ y)⁻¹ * y) := by group) }
  have hker : commutator Q ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hQ.commutator_eq_top] at hker
  ext x
  have hx : f x = 1 := hker (Subgroup.mem_top x)
  have hx' : (σ x)⁻¹ * x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact inv_mul_eq_one.mp hx'

theorem exists_isPerfect_map_eq_top {P Q : Type*} [Group P] [Finite P] [Group Q]
    (f : P →* Q) (hf : Function.Surjective f) (hQ : Group.IsPerfect Q) :
    ∃ D : Subgroup P, Group.IsPerfect D ∧ D.map f = ⊤ := by
  obtain ⟨D, -, hD⟩ := Finite.exists_le_minimal (p := fun D : Subgroup P => D.map f = ⊤)
    (a := ⊤) (by rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf])
  have hcomm : ⁅D, D⁆ = D := by
    refine le_antisymm (Subgroup.commutator_le_self D) (hD.2 ?_ (Subgroup.commutator_le_self D))
    change (⁅D, D⁆).map f = ⊤
    rw [Subgroup.map_commutator, hD.prop, ← commutator_def]
    exact hQ.commutator_eq_top
  refine ⟨D, ⟨Subgroup.map_injective D.subtype_injective ?_⟩, hD.prop⟩
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    hcomm]

theorem isPerfect_alternatingGroup_five : Group.IsPerfect (alternatingGroup (Fin 5)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5))) with
    h | h
  · exfalso
    let a : alternatingGroup (Fin 5) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
        rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul]⟩
    let b : alternatingGroup (Fin 5) :=
      ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by
        rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul]⟩
    have hab : a * b ≠ b * a := by
      intro hh
      have := congrArg Subtype.val hh
      revert this
      decide
    apply hab
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ commutator (alternatingGroup (Fin 5)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact h

theorem exists_isPerfect_card_sixty_alternating_six :
    ∃ K : Subgroup (alternatingGroup (Fin 6)), Group.IsPerfect K ∧ Nat.card K = 60 := by
  set φ : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 6) :=
    Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb with hφ
  have hsign : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign (φ σ) = Equiv.Perm.sign σ := by
    intro σ
    rw [hφ, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
    convert Equiv.Perm.sign_extendDomain σ _
  let ψ : alternatingGroup (Fin 5) →* alternatingGroup (Fin 6) :=
    (φ.comp (alternatingGroup (Fin 5)).subtype).codRestrict (alternatingGroup (Fin 6))
      (fun σ => by
        rw [MonoidHom.comp_apply, Equiv.Perm.mem_alternatingGroup, hsign]
        exact Equiv.Perm.mem_alternatingGroup.mp σ.2)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective _ h)
  refine ⟨ψ.range, ?_, ?_⟩
  · have := isPerfect_alternatingGroup_five
    rw [MonoidHom.range_eq_map]
    exact Group.IsPerfect.map _
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, card_alternatingGroup_five]

theorem exists_isPerfect_card_sixty_of_quotient_six {C : Type*} [Group C] [Finite C]
    (Z : Subgroup C) [Z.Normal] (hZc : Z ≤ Subgroup.center C) (hZ3 : Nat.card Z = 3)
    (e : C ⧸ Z ≃* alternatingGroup (Fin 6)) :
    ∃ F : Subgroup C, Group.IsPerfect F ∧ Nat.card F = 60 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKp, hK60⟩ := exists_isPerfect_card_sixty_alternating_six
  set K' : Subgroup (C ⧸ Z) := K.map e.symm.toMonoidHom with hK'
  have hK'60 : Nat.card K' = 60 := by
    rw [hK', Subgroup.card_map_of_injective e.symm.injective, hK60]
  have hK'p : Group.IsPerfect K' := by
    rw [hK']
    exact Group.IsPerfect.map _
  set P : Subgroup C := K'.comap (QuotientGroup.mk' Z) with hP
  let f : ↥P →* ↥K' :=
    ((QuotientGroup.mk' Z).comp P.subtype).codRestrict K' (fun x => Subgroup.mem_comap.mp x.2)
  have hfs : Function.Surjective f := by
    rintro ⟨k, hk⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Z k
    exact ⟨⟨c, Subgroup.mem_comap.mpr hk⟩, rfl⟩
  obtain ⟨D, hDp, hDtop⟩ := exists_isPerfect_map_eq_top f hfs hK'p
  let g : ↥D →* ↥K' := f.comp D.subtype
  have hgr : g.range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hDtop]
  have hcardD : Nat.card g.ker * 60 = Nat.card D := by
    have h := Subgroup.card_mul_index g.ker
    rw [Subgroup.index_ker, hgr, Subgroup.card_top, hK'60] at h
    exact h
  let ι : ↥D →* C := P.subtype.comp D.subtype
  have hι : Function.Injective ι := P.subtype_injective.comp D.subtype_injective
  have hkerZ : g.ker.map ι ≤ Z := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : f (x : ↥P) = 1 := hx
    have h2 : QuotientGroup.mk' Z ((x : ↥P) : C) = 1 := congrArg Subtype.val hx1
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hkdvd : Nat.card g.ker ∣ 3 := by
    rw [← hZ3, ← Subgroup.card_map_of_injective hι]
    exact Subgroup.card_dvd_of_le hkerZ
  rcases (Nat.dvd_prime Nat.prime_three).mp hkdvd with h1 | h3
  · refine ⟨D.map P.subtype, isPerfect_map_subtype hDp, ?_⟩
    rw [Subgroup.card_map_of_injective P.subtype_injective, ← hcardD, h1, one_mul]
  · exfalso
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := g.ker) 3 (by rw [h3])
    have hwZ : ι (w : ↥D) ∈ Z := hkerZ ⟨w, w.2, rfl⟩
    have hwc : (w : ↥D) ∈ Subgroup.center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := Subgroup.mem_center_iff.mp (hZc hwZ) (ι y)
      apply hι
      rw [map_mul, map_mul]
      exact h
    have hw3 : orderOf (w : ↥D) = 3 := by rw [Subgroup.orderOf_coe, hw]
    have hw1 : (w : ↥D) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hw3
      omega
    have hw3' : (w : ↥D) ^ 3 = 1 := by rw [← hw3, pow_orderOf_eq_one]
    obtain ⟨S⟩ : Nonempty (Sylow 3 ↥D) := inferInstance
    have hD180 : Nat.card D = 180 := by rw [← hcardD, h3]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have hSidx := Subgroup.card_mul_index (S : Subgroup ↥D)
    have hnd : ¬ 3 ∣ (S : Subgroup ↥D).index := Sylow.not_dvd_index S
    rw [hk, hD180] at hSidx
    have hk2 : k = 2 := by
      have hk4 : k < 5 := by
        by_contra hk5
        have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 3 ^ k ≤ 180 := Nat.le_of_dvd (by norm_num) ⟨_, hSidx.symm⟩
        omega
      interval_cases k <;> omega
    have hS9 : Nat.card (S : Subgroup ↥D) = 3 ^ 2 := by rw [hk, hk2]
    exact KFacts.K412.not_isMulCommutative_sylow hDp.commutator_eq_top hwc hw1 hw3' S
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq hS9)

end CFSG.RankThree.PartTwo.Sec15.Proof156
