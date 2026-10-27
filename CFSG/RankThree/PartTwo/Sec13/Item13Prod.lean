module

public import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Prod

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem Sec13Data.A_le_normalizer_zpowers (h : Sec13Data G A c L) :
    A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
  h.A_le_centralizer.trans (centralizer_le_normalizer_zpowers c)

@[expose] noncomputable def aBarHom (h : Sec13Data G A c L) : A →* lBarA c L A where
  toFun a := ⟨QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
      ⟨(a : G), h.A_le_normalizer_zpowers a.2⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right a.2))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul]; rfl)

theorem aBarHom_apply (h : Sec13Data G A c L) (a : A) :
    ((aBarHom h a : lBarA c L A) : _) =
      QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
        ⟨(a : G), h.A_le_normalizer_zpowers a.2⟩ :=
  rfl

theorem aBarHom_injective (h : Sec13Data G A c L) : Function.Injective (aBarHom h) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 := congrArg Subtype.val ha
  simp only [aBarHom_apply, Subgroup.coe_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  have h3 : (⟨(a : G), h.A_le_normalizer_zpowers a.2⟩ :
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using h.isElemAbelian.2 _ a.2)
  have hdvd1 := orderOf_dvd_of_pow_eq_one h3
  have hdvd2 := Subgroup.orderOf_dvd_natCard _ h1
  have hord : orderOf (⟨(a : G), h.A_le_normalizer_zpowers a.2⟩ :
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd1 with h' | h'
    · exact h'
    · exact absurd (h' ▸ hdvd2) (solvable_prime_complement_core_characterization
        (H := Subgroup.normalizer (Subgroup.zpowers c : Set G)) Nat.prime_three).2.2.1
  have := orderOf_eq_one_iff.mp hord
  exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem lBar_sup_range_aBarHom (h : Sec13Data G A c L) :
    (Sec12.lBar c L).subgroupOf (lBarA c L A) ⊔ (aBarHom h).range = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨_, ⟨z, hz0, rfl⟩⟩ -
  have hLN := le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt
  have hz : z ∈ L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    rw [← Subgroup.subgroupOf_sup hLN h.A_le_normalizer_zpowers]
    exact hz0
  have hnorm : A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      Subgroup.normalizer ((L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
        Subgroup _) : Set (Subgroup.normalizer (Subgroup.zpowers c : Set G))) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (h.le_normalizer (Subgroup.mem_subgroupOf.mp hy)) x
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  rw [sup_comm] at hz
  have hz' : z ∈ ((A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
        Subgroup (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
          Set (Subgroup.normalizer (Subgroup.zpowers c : Set G))) := hz
  rw [hmul] at hz'
  obtain ⟨y, hy, x, hx, rfl⟩ := hz'
  have hxl : (⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))⟩ : lBarA c L A) ∈
      (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hx)
  have hya : (⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)))⟩ : lBarA c L A) ∈
      (aBarHom h).range :=
    ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have e : (⟨QuotientGroup.mk' _ (y * x), Subgroup.mem_map_of_mem _ hz0⟩ : lBarA c L A) =
      ⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)))⟩ *
      ⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])
  show (⟨QuotientGroup.mk' _ (y * x), Subgroup.mem_map_of_mem _ hz0⟩ : lBarA c L A) ∈ _
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hya hxl

theorem commutator_lBarA_le (h : Sec13Data G A c L) :
    commutator (lBarA c L A) ≤ (Sec12.lBar c L).subgroupOf (lBarA c L A) := by
  have := lBar_normal h
  refine Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (lBar_sup_range_aBarHom h) ⟨⟨?_⟩⟩
  rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩
  apply Subtype.ext
  show aBarHom h a * aBarHom h b = aBarHom h b * aBarHom h a
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h.commute a.2 b.2)

theorem lBar_le_commutator (h : Sec13Data G A c L) :
    (Sec12.lBar c L).subgroupOf (lBarA c L A) ≤ commutator (lBarA c L A) := by
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hΛperf : Group.IsPerfect Λ := by
    have := isPerfect_lBar h
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective
  have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
    _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
    _ ≤ commutator (lBarA c L A) := Subgroup.commutator_mono le_top le_top

theorem commutator_zthree_prod (S : Type*) [Group S] :
    commutator (Multiplicative (ZMod 3) × S) =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) := by
  rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, commutator_def]
  congr 1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x _
  rw [Subgroup.mem_centralizer_iff]
  intro y _
  exact mul_comm y x

theorem map_lBar_eq_commutator (h : Sec13Data G A c L) {S : Type*} [Group S]
    (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) :
    ((Sec12.lBar c L).subgroupOf (lBarA c L A)).map φ.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) := by
  have hcX : (commutator (lBarA c L A)).map φ.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) := by
    rw [← commutator_zthree_prod, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ φ.surjective, commutator_def]
  rw [← hcX]
  exact le_antisymm (Subgroup.map_mono (lBar_le_commutator h))
    (Subgroup.map_mono (commutator_lBarA_le h))

theorem nonempty_lBar_equiv (h : Sec13Data G A c L) {S : Type*} [Group S]
    (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) :
    Nonempty (Sec12.lBar c L ≃* commutator S) := by
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A)
  have e1 : Sec12.lBar c L ≃* Λ := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm
  have e2 : Λ ≃* Λ.map φ.toMonoidHom := Λ.equivMapOfInjective _ φ.injective
  have e3 : (Λ.map φ.toMonoidHom : Subgroup _) ≃*
      ((⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) : Subgroup _) :=
    MulEquiv.subgroupCongr (map_lBar_eq_commutator h φ)
  have e4 : ((⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) : Subgroup _) ≃*
      (⊥ : Subgroup (Multiplicative (ZMod 3))) × commutator S := Subgroup.prodEquiv _ _
  have e5 : (⊥ : Subgroup (Multiplicative (ZMod 3))) × commutator S ≃* commutator S :=
    MulEquiv.uniqueProd
  exact ⟨e1.trans (e2.trans (e3.trans (e4.trans e5)))⟩

theorem not_mem_of_center_inf_commutator (h : Sec13Data G A c L) {S : Type*} [Group S]
    (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S)
    (hZ : Subgroup.center S ⊓ commutator S = ⊥) : c ∉ L := by
  intro hcL
  have hmem : mkC (L := L) h.mem_A ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
    Subgroup.mem_subgroupOf.mpr ⟨⟨c, le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt hcL⟩,
      Subgroup.mem_subgroupOf.mpr hcL, rfl⟩
  have h1 : φ (mkC h.mem_A) ∈ (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) := by
    rw [← map_lBar_eq_commutator h φ]
    exact Subgroup.mem_map_of_mem _ hmem
  have h2 : φ (mkC h.mem_A) ∈ Subgroup.center (Multiplicative (ZMod 3) × S) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.mp (mkC_mem_center h) (φ.symm y)
    have h3 := congrArg φ this
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  have h4 : (φ (mkC h.mem_A)).2 ∈ Subgroup.center S ⊓ commutator S := by
    refine ⟨Subgroup.mem_center_iff.mpr fun s => ?_, h1.2⟩
    have := Subgroup.mem_center_iff.mp h2 (1, s)
    exact congrArg Prod.snd this
  rw [hZ, Subgroup.mem_bot] at h4
  have h5 : φ (mkC h.mem_A) = 1 := Prod.ext (Subgroup.mem_bot.mp h1.1) h4
  exact mkC_ne_one h ((MulEquiv.map_eq_one_iff φ).mp h5)

theorem index_lBar_of_isPerfect (h : Sec13Data G A c L) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) :
    ((Sec12.lBar c L).subgroupOf (lBarA c L A)).index = 3 := by
  rw [← Subgroup.index_map_equiv _ φ]
  have h1 := map_lBar_eq_commutator h φ
  rw [hS.commutator_eq_top] at h1
  change (((Sec12.lBar c L).subgroupOf (lBarA c L A)).map φ.toMonoidHom).index = 3
  rw [h1, Subgroup.index_prod, Subgroup.index_bot, Subgroup.index_top, mul_one, Nat.card_congr
    (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]

theorem card_inf_eq_nine (h : Sec13Data G A c L) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) :
    Nat.card (A ⊓ L : Subgroup G) = 9 := by
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set ψ := aBarHom h with hψ
  have := lBar_normal h
  have hR : Nat.card ψ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective h)).toEquiv, h.card_eq]
  have hrel : Λ.relIndex ψ.range = 3 := by
    rw [← Subgroup.relIndex_sup_right, sup_comm, lBar_sup_range_aBarHom h,
      Subgroup.relIndex_top_right, index_lBar_of_isPerfect h hS φ]
  have hinf : Nat.card (Λ ⊓ ψ.range : Subgroup (lBarA c L A)) = 9 := by
    have := Subgroup.relIndex_mul_card Λ ψ.range
    rw [hrel, hR] at this
    omega
  have hcomap : Λ.comap ψ = (A ⊓ L).subgroupOf A := by
    ext a
    show ((ψ a : lBarA c L A) : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∈
        Sec12.lBar c L ↔ (a : G) ∈ A ⊓ L
    constructor
    · intro ha
      refine ⟨a.2, ?_⟩
      have h3 : (⟨(a : G), h.A_le_normalizer_zpowers a.2⟩ :
          Subgroup.normalizer (Subgroup.zpowers c : Set G)) ^ 3 ^ 1 = 1 :=
        Subtype.ext (by simpa using h.isElemAbelian.2 _ a.2)
      exact mem_of_mk_mem_lBar h.mem_thetaComponentsAt h3 ha
    · rintro ⟨-, haL⟩
      exact ⟨⟨(a : G), le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt haL⟩,
        Subgroup.mem_subgroupOf.mpr haL, rfl⟩
  have hmap : (Λ.comap ψ).map ψ = ψ.range ⊓ Λ := Subgroup.map_comap_eq ψ Λ
  have h1 : Nat.card ((Λ.comap ψ).map ψ) = Nat.card (Λ.comap ψ) :=
    Subgroup.card_map_of_injective (aBarHom_injective h)
  rw [hmap, inf_comm, hinf, hcomap] at h1
  rw [h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv.symm

theorem nonempty_thetaQuot_equiv (h : Sec13Data G A c L) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) :
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* S) := by
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  obtain ⟨e⟩ := nonempty_lBar_equiv h φ
  exact ⟨η.trans (e.trans ((MulEquiv.subgroupCongr hS.commutator_eq_top).trans
    Subgroup.topEquiv))⟩

theorem nonempty_lBarA_equiv_prod (h : Sec13Data G A c L) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) :
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
  obtain ⟨e⟩ := nonempty_lBar_equiv h φ
  exact ⟨φ.trans (MulEquiv.prodCongr (MulEquiv.refl _)
    ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hS.commutator_eq_top.symm)).trans
      e.symm))⟩

end Prod

end CFSG.RankThree.PartTwo.Sec13
