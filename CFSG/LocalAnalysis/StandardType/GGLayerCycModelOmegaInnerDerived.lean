module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInner
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeB2der
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.StandardType

namespace LayerCyc

open CFSG.Assembly Equiv

theorem card_centralizer_perm_six_of_orderOf_eq_three {σ : Perm (Fin 6)} (hσ : orderOf σ = 3) :
    Nat.card (Subgroup.centralizer {σ}) = 18 := by
  have hp : (orderOf σ).Prime := hσ ▸ Nat.prime_three
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [hσ] at hn
  have hsum : σ.cycleType.sum ≤ 6 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hn1 : n ≤ 1 := by omega
  rw [Equiv.Perm.nat_card_centralizer, hn]
  interval_cases n <;> decide

theorem isSolvable_centralizer_perm_six {σ : Perm (Fin 6)} (hσ : orderOf σ = 3) :
    Group.IsSolvable (Subgroup.centralizer {σ}) := by
  classical
  have : Fintype (Subgroup.centralizer {σ}) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (a := 1) (b := 2)
    (by rw [← Nat.card_eq_fintype_card, card_centralizer_perm_six_of_orderOf_eq_three hσ]; norm_num)

section B2der

open CFSG.ComponentClassification.PresentationLocal TableB

theorem isSolvable_ggFix_matConj_of_perm {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Sp H : Subgroup (GL ι K)} (E : Sp ≃* Perm (Fin 6)) (hHSp : H ≤ Sp)
    (hconj : ∀ B ∈ Sp, ∀ h ∈ H, B * h * B⁻¹ ∈ H)
    (hscal : LargeEvenScalars ι K = ⊥) {S : Set (GL ι K)} (hS : S ⊆ Sp)
    {φ : MulAut (LargeEvenProj H)}
    (hφI : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S) (hφ1 : φ ≠ 1)
    (hφ3 : φ ^ 3 = 1) : Group.IsSolvable (ggFix φ) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hAS, hφ⟩ := hφI
  have hASp : A ∈ Sp := hS hAS
  have hπinj : Function.Injective (LargeEvenProjMk H) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenProjMk, QuotientGroup.ker_mk', hscal,
      Subgroup.bot_subgroupOf]
  have hπsurj : Function.Surjective (LargeEvenProjMk H) := QuotientGroup.mk'_surjective _
  have hiter : ∀ (n : ℕ) (h : H), (φ ^ n) (LargeEvenProjMk H h) =
      LargeEvenProjMk H ⟨A ^ n * h * (A ^ n)⁻¹, hconj _ (Sp.pow_mem hASp n) h h.2⟩ := by
    intro n
    induction n with
    | zero =>
      intro h
      rw [pow_zero φ, MulAut.one_apply]
      congr 1
      exact Subtype.ext (by simp)
    | succ n ih =>
      intro h
      rw [pow_succ' φ n, MulAut.mul_apply, ih h,
        hφ ⟨A ^ n * h * (A ^ n)⁻¹, hconj _ (Sp.pow_mem hASp n) h h.2⟩
          ⟨A * (A ^ n * h * (A ^ n)⁻¹) * A⁻¹,
            hconj _ hASp _ (hconj _ (Sp.pow_mem hASp n) h h.2)⟩ rfl]
      congr 1
      apply Subtype.ext
      show A * (A ^ n * (h : GL ι K) * (A ^ n)⁻¹) * A⁻¹ = A ^ (n + 1) * h * (A ^ (n + 1))⁻¹
      rw [pow_succ']
      group
  have hAk : A ^ orderOf (E ⟨A, hASp⟩) = 1 := by
    have h1 : (⟨A, hASp⟩ : Sp) ^ orderOf (E ⟨A, hASp⟩) = 1 := by
      rw [MulEquiv.orderOf_eq]
      exact pow_orderOf_eq_one _
    have h2 := congrArg Subtype.val h1
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
  have hφk : φ ^ orderOf (E ⟨A, hASp⟩) = 1 := by
    ext x
    obtain ⟨h, rfl⟩ := hπsurj x
    rw [MulAut.one_apply, hiter]
    congr 1
    apply Subtype.ext
    simp only [hAk, one_mul, inv_one, mul_one]
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have h3k : 3 ∣ orderOf (E ⟨A, hASp⟩) := hord ▸ orderOf_dvd_of_pow_eq_one hφk
  have hk0 : orderOf (E ⟨A, hASp⟩) ≠ 0 := (orderOf_pos _).ne'
  have hk3 : orderOf (E ⟨A, hASp⟩) / 3 ≠ 0 := by
    have := Nat.le_of_dvd (orderOf_pos (E ⟨A, hASp⟩)) h3k
    omega
  have hσ3 : orderOf (E ⟨A, hASp⟩ ^ (orderOf (E ⟨A, hASp⟩) / 3)) = 3 := by
    rw [orderOf_pow_of_dvd hk3 (Nat.div_dvd_of_dvd h3k), Nat.div_div_self h3k hk0]
  let eπ : H ≃* LargeEvenProj H :=
    MulEquiv.ofBijective (LargeEvenProjMk H) ⟨hπinj, hπsurj⟩
  let f : ggFix φ →* Perm (Fin 6) := E.toMonoidHom.comp
    ((Subgroup.inclusion hHSp).comp (eπ.symm.toMonoidHom.comp (ggFix φ).subtype))
  have hf : Function.Injective f := E.injective.comp ((Subgroup.inclusion_injective hHSp).comp
    (eπ.symm.injective.comp Subtype.val_injective))
  have hmem : ∀ x : ggFix φ,
      f x ∈ Subgroup.centralizer {E ⟨A, hASp⟩ ^ (orderOf (E ⟨A, hASp⟩) / 3)} := by
    intro x
    have hπh : LargeEvenProjMk H (eπ.symm (x : LargeEvenProj H)) = x :=
      eπ.apply_symm_apply _
    have hfix : φ (LargeEvenProjMk H (eπ.symm (x : LargeEvenProj H))) =
        LargeEvenProjMk H (eπ.symm (x : LargeEvenProj H)) := by
      rw [hπh]
      exact x.2
    have h1 := (hφ (eπ.symm (x : LargeEvenProj H))
      ⟨A * (eπ.symm (x : LargeEvenProj H) : GL ι K) * A⁻¹,
        hconj _ hASp _ (eπ.symm (x : LargeEvenProj H)).2⟩ rfl).symm.trans hfix
    have h2 : A * (eπ.symm (x : LargeEvenProj H) : GL ι K) * A⁻¹ =
        (eπ.symm (x : LargeEvenProj H) : GL ι K) :=
      congrArg Subtype.val (hπinj h1)
    have h3 : (⟨A, hASp⟩ : Sp) * Subgroup.inclusion hHSp (eπ.symm (x : LargeEvenProj H)) =
        Subgroup.inclusion hHSp (eπ.symm (x : LargeEvenProj H)) * ⟨A, hASp⟩ := by
      apply Subtype.ext
      show A * (eπ.symm (x : LargeEvenProj H) : GL ι K) =
        (eπ.symm (x : LargeEvenProj H) : GL ι K) * A
      calc A * (eπ.symm (x : LargeEvenProj H) : GL ι K)
          = A * (eπ.symm (x : LargeEvenProj H) : GL ι K) * A⁻¹ * A := by group
        _ = (eπ.symm (x : LargeEvenProj H) : GL ι K) * A := by rw [h2]
    have h4 : Commute (E ⟨A, hASp⟩) (f x) := by
      show E ⟨A, hASp⟩ * E (Subgroup.inclusion hHSp (eπ.symm (x : LargeEvenProj H))) =
        E (Subgroup.inclusion hHSp (eπ.symm (x : LargeEvenProj H))) * E ⟨A, hASp⟩
      rw [← map_mul, ← map_mul, h3]
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((h4.pow_left _).symm).eq
  have := isSolvable_centralizer_perm_six hσ3
  exact Group.isSolvable_of_isSolvable_injective (f := f.codRestrict _ hmem)
    fun x y hxy => hf (congrArg Subtype.val hxy)

variable {K : Type} [Field K] [Finite K]

theorem isSolvable_ggFix_b2der (hK : Nat.card K = 2)
    {φ : MulAut (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)}
    (hφI : φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) (LargeEvenGSpSet K 2))
    (hφ1 : φ ≠ 1) (hφ3 : φ ^ 3 = 1) : Group.IsSolvable (ggFix φ) := by
  obtain ⟨e⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hK
  exact isSolvable_ggFix_matConj_of_perm
    (e.trans (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩))
    (LayerFacts.ggCommutator_self_le _)
    (fun B hB h hh => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_commutator hB) h).mp hh)
    (TwoThree.largeEvenScalars_eq_bot hK) (fun _ hA => mem_largeEvenSpGroup_of_gsp hK hA) hφI
    hφ1 hφ3

theorem largeEvenLabelAll_fixSolvable_b2der {lab : LargeEvenLabel} (ht : lab.tag = .B2der) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun _R _ I _ =>
      ∀ φ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → Group.IsSolvable (ggFix φ)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, fun _ _ φ hφ hφ1 hφ3 => isSolvable_ggFix_b2der hK hφ hφ1 hφ3⟩

end B2der

section Inner

theorem isSolvable_centralizer_of_forall_not_commute {M : Type*} [Group M] [Finite M] {g : M}
    (h : ∀ x : M, (orderOf x).Prime → 3 < orderOf x → g * x ≠ x * g) :
    Group.IsSolvable (Subgroup.centralizer {g}) :=
  LayerCores.OrthRegular.isSolvable_of_no_prime_gt_three' fun c ℓ hℓ h3 hc => by
    have hc' : orderOf (c : M) = ℓ := by rwa [Subgroup.orderOf_coe]
    exact h c (hc' ▸ hℓ) (hc' ▸ h3) (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm

theorem isSolvable_ggFix_of_subset_inn {R M : Type*} [Group R] [Group M] [Finite M] (e : R ≃* M)
    (hZ : Subgroup.center M = ⊥)
    (hM : ∀ g x : M, orderOf g = 3 → (orderOf x).Prime → 3 < orderOf x → g * x ≠ x * g)
    {I : Set (MulAut R)} (hI : I ⊆ (MulAut.conj : R →* MulAut R).range) {φ : MulAut R}
    (hφI : φ ∈ I) (hφ1 : φ ≠ 1) (hφ3 : φ ^ 3 = 1) : Group.IsSolvable (ggFix φ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, rfl⟩ := hI hφI
  have hr3 : r ^ 3 = 1 := by
    have hc : ∀ y : R, r ^ 3 * y = y * r ^ 3 := fun y => by
      have h1 : MulAut.conj (r ^ 3) y = y := by rw [map_pow, hφ3, MulAut.one_apply]
      rwa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
    apply e.injective
    rw [map_one]
    have hz : e (r ^ 3) ∈ Subgroup.center M := Subgroup.mem_center_iff.mpr fun m => by
      obtain ⟨y, rfl⟩ := e.surjective m
      rw [← map_mul, ← map_mul, hc y]
    rw [hZ] at hz
    exact Subgroup.mem_bot.mp hz
  have hr1 : r ≠ 1 := fun h => hφ1 (by rw [h, map_one])
  have hord : orderOf (e r) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hr3 hr1
  have hmem : ∀ x : ggFix (MulAut.conj r), e x ∈ Subgroup.centralizer {e r} := by
    intro x
    have hx : r * (x : R) * r⁻¹ = x := by
      have := x.2
      rwa [mem_ggFix, MulAut.conj_apply] at this
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    calc (x : R) * r = r * x * r⁻¹ * r := by rw [hx]
      _ = r * x := by group
  have := isSolvable_centralizer_of_forall_not_commute fun x => hM (e r) x hord
  exact Group.isSolvable_of_isSolvable_injective
    (f := (e.toMonoidHom.comp (ggFix (MulAut.conj r)).subtype).codRestrict _ hmem)
    fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy))

end Inner

end LayerCyc

open LayerCyc CFSG.Assembly CFSG.Assembly.LowTwoRank

@[expose] def GGSU33ThreeCentInput : Prop :=
  ∀ g x : StatedSU 3 3 CFSG.Quasithin.G2U.F9, orderOf g = 3 → (orderOf x).Prime → 3 < orderOf x →
    g * x ≠ x * g

@[expose] def GGTitsThreeCentInput : Prop :=
  ∀ g x : CFSG.Sporadic.Schreier.Tits.titsD, orderOf g = 3 → (orderOf x).Prime →
    3 < orderOf x → g * x ≠ x * g

theorem largeEvenLabelAll_fixSolvable_G2der
    (hSU : GGSU33ThreeCentInput) {lab : LargeEvenLabel}
    (ht : lab.tag = .G2der) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun _R _ I _ =>
      ∀ φ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → Group.IsSolvable (ggFix φ)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun _ _ φ hφ hφ1 hφ3 => ?_⟩
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  exact isSolvable_ggFix_of_subset_inn e TableBExcSmallRest.center_su3_eq_bot hSU
    (chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanG2)
      (LargeEvenChevH LargeEvenCartanG2 K true)) hφ hφ1 hφ3

section Tits

theorem largeEvenLabelAll_fixSolvable_twF4der (hT : GGTitsThreeCentInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4der) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun _R _ I _ =>
      ∀ φ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → Group.IsSolvable (ggFix φ)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hn : n = 1 := hlab.2.2
  subst hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun _ _ φ hφ hφ1 hφ3 => ?_⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hm : CFSG.Blueprint.ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK2
  exact isSolvable_ggFix_of_subset_inn e CFSG.Sporadic.Schreier.Tits.titsD_center hT
    (chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanF4) (LargeEvenTwF4H 0 K)) hφ
    hφ1 hφ3


theorem ggLayerDerivedFixSolvableInput_of (hSU : GGSU33ThreeCentInput)
    (hT : GGTitsThreeCentInput) : GGLayerDerivedFixSolvableInput := by
  intro lab hlab hd
  rcases hd with h | h | h
  · exact largeEvenLabelAll_fixSolvable_b2der h
  · exact largeEvenLabelAll_fixSolvable_G2der hSU h
  · exact largeEvenLabelAll_fixSolvable_twF4der hT hlab h

theorem ggLayerCenterCyclicInput_of_su33_tits_exc
    (hSU : GGSU33ThreeCentInput) (hT : GGTitsThreeCentInput) (hexc : GGLayerCenterCyclicExcInput) :
    GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_derived_exc (ggLayerDerivedFixSolvableInput_of hSU hT) hexc

end Tits

end CFSG.StandardType

end
