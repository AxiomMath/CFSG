module

public import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item13Prod

public section

namespace CFSG.RankThree.PartTwo.Sec12.Proof128

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (lBarA)

section Bar

variable {G : Type} [Group G] [Finite G] {A K : Subgroup G} {a : G}

omit [Finite G] in
theorem le_normalizer_zpowers_of_isElemAbelian (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := fun x hx =>
  Sec13.centralizer_le_normalizer_zpowers a (Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩)))

@[expose] noncomputable def aBar (K : Subgroup G)
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) : A →* lBarA a K A where
  toFun x := ⟨QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers a : Set G))) ⟨(x : G), hAH x.2⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right x.2))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul]; rfl)

omit [Finite G] in
theorem aBar_apply (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) (x : A) :
    ((aBar K hAH x : lBarA a K A) : _) =
      QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers a : Set G))) ⟨(x : G), hAH x.2⟩ :=
  rfl

theorem aBar_injective (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    Function.Injective (aBar K hAH) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 := congrArg Subtype.val hx
  simp only [aBar_apply, Subgroup.coe_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  have h3 : (⟨(x : G), hAH x.2⟩ : Subgroup.normalizer (Subgroup.zpowers a : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hA.2 _ x.2)
  have hdvd1 := orderOf_dvd_of_pow_eq_one h3
  have hdvd2 := Subgroup.orderOf_dvd_natCard _ h1
  have hord :
      orderOf (⟨(x : G), hAH x.2⟩ : Subgroup.normalizer (Subgroup.zpowers a : Set G)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd1 with h' | h'
    · exact h'
    · exact absurd (h' ▸ hdvd2) (solvable_prime_complement_core_characterization
        (H := Subgroup.normalizer (Subgroup.zpowers a : Set G)) Nat.prime_three).2.2.1
  have := orderOf_eq_one_iff.mp hord
  exact Subtype.ext (by simpa using congrArg Subtype.val this)

omit [Finite G] in
theorem aBar_mem_center (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hK : K ∈ thetaComponentsAt 3 a)
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    aBar K hAH ⟨a, haA⟩ ∈ Subgroup.center (lBarA a K A) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, ⟨z, hz, rfl⟩⟩
  apply Subtype.ext
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  have hzC : (z : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    sup_le (Sec6.le_centralizer_of_mem_thetaComponentsAt hK) hAa (Subgroup.mem_subgroupOf.mp hz)
  have hcomm : z * ⟨a, hAH haA⟩ = ⟨a, hAH haA⟩ * z :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzC)
  simp only [aBar_apply, Subgroup.coe_mul, ← map_mul, hcomm]

omit [Finite G] in
theorem lBar_normal (hAN : A ≤ Subgroup.normalizer (K : Set G)) :
    ((Sec12.lBar a K).subgroupOf (lBarA a K A)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨_, ⟨z, hz, rfl⟩⟩ := g
  obtain ⟨l, hl, hlx⟩ := hx
  have hzN : (z : G) ∈ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hAN (Subgroup.mem_subgroupOf.mp hz)
  refine ⟨z * l * z⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hzN _).mp (Subgroup.mem_subgroupOf.mp hl)
  · simp only [map_mul, map_inv, hlx, Subgroup.coe_mul, Subgroup.coe_inv]

omit [Finite G] in
theorem isPerfect_lBar (hK : K ∈ thetaComponentsAt 3 a) : Group.IsPerfect (Sec12.lBar a K) := by
  have hKp : Group.IsPerfect K := Sec6.isPerfect_of_mem_thetaComponentsAt hK
  have hKN := Sec13.le_normalizer_zpowers_of_mem hK
  set e : K ≃* K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G)) :=
    (Subgroup.subgroupOfEquivOfLe hKN).symm
  have : Group.IsPerfect (K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G))) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.ofSurjective
    (f := (QuotientGroup.mk' _).subgroupMap (K.subgroupOf _))
    ((QuotientGroup.mk' _).subgroupMap_surjective _)

theorem lBar_ne_bot (hK : K ∈ thetaComponentsAt 3 a) : Sec12.lBar a K ≠ ⊥ := by
  obtain ⟨η, -⟩ := Sec13.exists_lBarEquiv hK
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have : IsSimpleGroup ((K ⧸ aschbacherSolvableCore 3 K) ⧸
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) := hq.2.1
  have : Nontrivial (K ⧸ aschbacherSolvableCore 3 K) :=
    (QuotientGroup.mk_surjective
      (s := Subgroup.center (K ⧸ aschbacherSolvableCore 3 K))).nontrivial
  have : Nontrivial (Sec12.lBar a K) := η.symm.surjective.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this

omit [Finite G] in
theorem lBar_sup_range_aBar (hK : K ∈ thetaComponentsAt 3 a)
    (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    (Sec12.lBar a K).subgroupOf (lBarA a K A) ⊔ (aBar K hAH).range = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨_, ⟨z, hz0, rfl⟩⟩ -
  have hKN := Sec13.le_normalizer_zpowers_of_mem hK
  have hz : z ∈ K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G)) ⊔
      A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G)) := by
    rw [← Subgroup.subgroupOf_sup hKN hAH]
    exact hz0
  have hnorm : A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G)) ≤
      Subgroup.normalizer ((K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
        Subgroup _) : Set (Subgroup.normalizer (Subgroup.zpowers a : Set G))) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hAN (Subgroup.mem_subgroupOf.mp hy)) x
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  rw [sup_comm] at hz
  have hz' : z ∈ ((A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G)) ⊔
      K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
        Subgroup (Subgroup.normalizer (Subgroup.zpowers a : Set G))) :
          Set (Subgroup.normalizer (Subgroup.zpowers a : Set G))) := hz
  rw [hmul] at hz'
  obtain ⟨y, hy, x, hx, rfl⟩ := hz'
  have hxl : (⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))⟩ : lBarA a K A) ∈
      (Sec12.lBar a K).subgroupOf (lBarA a K A) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hx)
  have hya : (⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)))⟩ : lBarA a K A) ∈
      (aBar K hAH).range :=
    ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have e : (⟨QuotientGroup.mk' _ (y * x), Subgroup.mem_map_of_mem _ hz0⟩ : lBarA a K A) =
      ⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy)))⟩ *
      ⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])
  show (⟨QuotientGroup.mk' _ (y * x), Subgroup.mem_map_of_mem _ hz0⟩ : lBarA a K A) ∈ _
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hya hxl

omit [Finite G] in
theorem commutator_lBarA_le (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hK : K ∈ thetaComponentsAt 3 a) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    commutator (lBarA a K A) ≤ (Sec12.lBar a K).subgroupOf (lBarA a K A) := by
  have := lBar_normal (a := a) hAN
  refine Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (lBar_sup_range_aBar hK hAN hAH) ⟨⟨?_⟩⟩
  rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
  apply Subtype.ext
  show aBar K hAH x * aBar K hAH y = aBar K hAH y * aBar K hAH x
  rw [← map_mul, ← map_mul]
  congr 1
  exact hA.1.is_comm.comm x y

omit [Finite G] in
theorem lBar_le_commutator (hK : K ∈ thetaComponentsAt 3 a) :
    (Sec12.lBar a K).subgroupOf (lBarA a K A) ≤ commutator (lBarA a K A) := by
  set Λ := (Sec12.lBar a K).subgroupOf (lBarA a K A) with hΛ
  have hΛperf : Group.IsPerfect Λ := by
    have := isPerfect_lBar hK
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe Sec13.lBar_le_lBarA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe Sec13.lBar_le_lBarA).symm.surjective
  have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
    _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
    _ ≤ commutator (lBarA a K A) := Subgroup.commutator_mono le_top le_top

omit [Finite G] in
theorem map_lBar_eq_commutator (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hK : K ∈ thetaComponentsAt 3 a) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) {S : Type*} [Group S]
    (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × S) :
    ((Sec12.lBar a K).subgroupOf (lBarA a K A)).map φ.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) := by
  have hcX : (commutator (lBarA a K A)).map φ.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) := by
    rw [← Sec13.commutator_zthree_prod, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ φ.surjective, commutator_def]
  rw [← hcX]
  exact le_antisymm (Subgroup.map_mono (lBar_le_commutator hK))
    (Subgroup.map_mono (commutator_lBarA_le hA hK hAN hAH))

omit [Finite G] in
theorem nonempty_lBar_equiv (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hK : K ∈ thetaComponentsAt 3 a) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) {S : Type*} [Group S]
    (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × S) :
    Nonempty (Sec12.lBar a K ≃* commutator S) := by
  set Λ := (Sec12.lBar a K).subgroupOf (lBarA a K A)
  have e1 : Sec12.lBar a K ≃* Λ := (Subgroup.subgroupOfEquivOfLe Sec13.lBar_le_lBarA).symm
  have e2 : Λ ≃* Λ.map φ.toMonoidHom := Λ.equivMapOfInjective _ φ.injective
  have e3 : (Λ.map φ.toMonoidHom : Subgroup _) ≃*
      ((⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) : Subgroup _) :=
    MulEquiv.subgroupCongr (map_lBar_eq_commutator hA hK hAN hAH φ)
  have e4 : ((⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator S) : Subgroup _) ≃*
      (⊥ : Subgroup (Multiplicative (ZMod 3))) × commutator S := Subgroup.prodEquiv _ _
  have e5 : (⊥ : Subgroup (Multiplicative (ZMod 3))) × commutator S ≃* commutator S :=
    MulEquiv.uniqueProd
  exact ⟨e1.trans (e2.trans (e3.trans (e4.trans e5)))⟩

omit [Finite G] in
theorem index_lBar_of_isPerfect (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hK : K ∈ thetaComponentsAt 3 a) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × S) :
    ((Sec12.lBar a K).subgroupOf (lBarA a K A)).index = 3 := by
  rw [← Subgroup.index_map_equiv _ φ]
  have h1 := map_lBar_eq_commutator hA hK hAN hAH φ
  rw [hS.commutator_eq_top] at h1
  change (((Sec12.lBar a K).subgroupOf (lBarA a K A)).map φ.toMonoidHom).index = 3
  rw [h1, Subgroup.index_prod, Subgroup.index_bot, Subgroup.index_top, mul_one, Nat.card_congr
    (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]

theorem card_lBar_inf_range (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hK : K ∈ thetaComponentsAt 3 a)
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    Nat.card ((Sec12.lBar a K).subgroupOf (lBarA a K A) ⊓ (aBar K hAH).range :
      Subgroup (lBarA a K A)) = Nat.card (A ⊓ K : Subgroup G) := by
  set Λ := (Sec12.lBar a K).subgroupOf (lBarA a K A) with hΛ
  set ψ := aBar K hAH with hψ
  have hcomap : Λ.comap ψ = (A ⊓ K).subgroupOf A := by
    ext x
    show ((ψ x : lBarA a K A) : Subgroup.normalizer (Subgroup.zpowers a : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers a : Set G))) ∈
        Sec12.lBar a K ↔ (x : G) ∈ A ⊓ K
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have h3 : (⟨(x : G), hAH x.2⟩ : Subgroup.normalizer (Subgroup.zpowers a : Set G)) ^ 3 ^ 1 =
          1 := Subtype.ext (by simpa using hA.2 _ x.2)
      exact Sec13.mem_of_mk_mem_lBar hK h3 hx
    · rintro ⟨-, hxK⟩
      exact ⟨⟨(x : G), Sec13.le_normalizer_zpowers_of_mem hK hxK⟩,
        Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
  have hmap : (Λ.comap ψ).map ψ = ψ.range ⊓ Λ := Subgroup.map_comap_eq ψ Λ
  have h1 : Nat.card ((Λ.comap ψ).map ψ) = Nat.card (Λ.comap ψ) :=
    Subgroup.card_map_of_injective (aBar_injective hA hAH)
  rw [hmap, inf_comm, hcomap] at h1
  rw [h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_inf_eq_nine (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (hK : K ∈ thetaComponentsAt 3 a) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × S) :
    Nat.card (A ⊓ K : Subgroup G) = 9 := by
  set Λ := (Sec12.lBar a K).subgroupOf (lBarA a K A) with hΛ
  set ψ := aBar K hAH with hψ
  have := lBar_normal (a := a) hAN
  have hR : Nat.card ψ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (aBar_injective hA hAH)).toEquiv, h27]
  have hrel : Λ.relIndex ψ.range = 3 := by
    rw [← Subgroup.relIndex_sup_right, sup_comm, lBar_sup_range_aBar hK hAN hAH,
      Subgroup.relIndex_top_right, index_lBar_of_isPerfect hA hK hAN hAH hS φ]
  have hinf : Nat.card (Λ ⊓ ψ.range : Subgroup (lBarA a K A)) = 9 := by
    have := Subgroup.relIndex_mul_card Λ ψ.range
    rw [hrel, hR] at this
    omega
  have hcomap : Λ.comap ψ = (A ⊓ K).subgroupOf A := by
    ext x
    show ((ψ x : lBarA a K A) : Subgroup.normalizer (Subgroup.zpowers a : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers a : Set G))) ∈
        Sec12.lBar a K ↔ (x : G) ∈ A ⊓ K
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have h3 : (⟨(x : G), hAH x.2⟩ : Subgroup.normalizer (Subgroup.zpowers a : Set G)) ^ 3 ^ 1 =
          1 := Subtype.ext (by simpa using hA.2 _ x.2)
      exact Sec13.mem_of_mk_mem_lBar hK h3 hx
    · rintro ⟨-, hxK⟩
      exact ⟨⟨(x : G), Sec13.le_normalizer_zpowers_of_mem hK hxK⟩,
        Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
  have hmap : (Λ.comap ψ).map ψ = ψ.range ⊓ Λ := Subgroup.map_comap_eq ψ Λ
  have h1 : Nat.card ((Λ.comap ψ).map ψ) = Nat.card (Λ.comap ψ) :=
    Subgroup.card_map_of_injective (aBar_injective hA hAH)
  rw [hmap, inf_comm, hinf, hcomap] at h1
  rw [h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv.symm

theorem nonempty_thetaQuot_equiv (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hK : K ∈ thetaComponentsAt 3 a) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) {S : Type*} [Group S]
    (hS : Group.IsPerfect S) (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × S) :
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* S) := by
  obtain ⟨η, -⟩ := Sec13.exists_lBarEquiv hK
  obtain ⟨e⟩ := nonempty_lBar_equiv hA hK hAN hAH φ
  exact ⟨η.trans (e.trans ((MulEquiv.subgroupCongr hS.commutator_eq_top).trans
    Subgroup.topEquiv))⟩

end Bar

end CFSG.RankThree.PartTwo.Sec12.Proof128
