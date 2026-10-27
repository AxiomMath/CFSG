module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec17.Item176ProofOne
import CFSG.RankThree.PartTwo.Sec17.Item175ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Base
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def KS1622GTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsoGTwoPrime X →
    ∃ x y : X, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set X))

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Proof1622

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof (exists_isSylowOf_le
  exists_conj_of_isSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isPGroup {A R : Subgroup G} (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (hR : IsPGroup 3 R) (hAR : A ≤ R) : R ≤ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  set P : Subgroup R := (Subgroup.normalizer (A : Set G)).subgroupOf R with hP
  have hself : Subgroup.normalizer (P : Set R) = P := by
    refine le_antisymm (fun y hy => ?_) Subgroup.le_normalizer
    rw [hP, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have haP : (⟨a, hAR ha⟩ : R) ∈ P :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.le_normalizer ha)
    have h1 := (Subgroup.mem_normalizer_iff.mp hy _).mp haP
    rw [hP, Subgroup.mem_subgroupOf] at h1
    refine h1617 _ (by simpa using h1) ?_
    rw [conj_pow, hA3 a ha, mul_one, mul_inv_cancel]
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := R))) P hself
  intro x hx
  have hx' : (⟨x, hx⟩ : R) ∈ P := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hx'

theorem mem_of_isPGroup {A R : Subgroup G} (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (hR : IsPGroup 3 R) (hAR : A ≤ R) {x : G} (hx : x ∈ R) (hx3 : x ^ 3 = 1) : x ∈ A :=
  h1617 x (le_normalizer_of_isPGroup hA3 h1617 hR hAR hx) hx3

omit [Finite G] in
theorem inv_conj_pow_three (g z : G) : (g⁻¹ * z * g) ^ 3 = g⁻¹ * z ^ 3 * g := by
  simp only [pow_succ, pow_zero, one_mul]
  group

theorem commute_of_isPGroup {A R : Subgroup G} (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA : IsPGroup 3 A)
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (hR : IsPGroup 3 R) {x y : G} (hx : x ∈ R) (hy : y ∈ R) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) : x * y = y * x := by
  obtain ⟨S, hS, hRS⟩ := exists_isSylowOf_le (le_top : R ≤ ⊤) hR
  obtain ⟨S', hS', hAS'⟩ := exists_isSylowOf_le (le_top : A ≤ ⊤) hA
  obtain ⟨g, -, hSg⟩ := exists_conj_of_isSylowOf hS' hS
  have key : ∀ z ∈ R, z ^ 3 = 1 → g⁻¹ * z * g ∈ A := by
    intro z hz hz3
    have hzS : z ∈ S'.map (MulAut.conj g).toMonoidHom := hSg ▸ hRS hz
    obtain ⟨w, hw, hwz⟩ := hzS
    have hw' : g⁻¹ * z * g = w := by
      rw [← hwz]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hw']
    refine mem_of_isPGroup hA3 h1617 hS'.isPGroup hAS' hw ?_
    rw [← hw', inv_conj_pow_three, hz3, mul_one, inv_mul_cancel]
  have h := hAab _ (key x hx hx3) _ (key y hy hy3)
  have h2 : g⁻¹ * (x * y) * g = g⁻¹ * (y * x) * g := by
    calc g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
      _ = (g⁻¹ * y * g) * (g⁻¹ * x * g) := h
      _ = g⁻¹ * (y * x) * g := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem zpowers_eq_of_conj_mem_centralizer {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (h1618 : ∀ g : G, g * c * g⁻¹ ∈ A → Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c)
    {g : G} (hg : g * c * g⁻¹ ∈ Subgroup.centralizer ({c} : Set G)) :
    Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c := by
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [h.card_eq]; norm_num)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := h.isElemAbelian.2
  obtain ⟨S, hS, hAS⟩ := exists_isSylowOf_le h.A_le_centralizer hA
  set y := g * c * g⁻¹ with hy
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hyord : orderOf y = 3 := by
    rw [hy, show g * c * g⁻¹ = (MulAut.conj g) c from rfl, MulEquiv.orderOf_eq, h.orderOf_eq]
  have hyP : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord, pow_one])
  obtain ⟨Q, hQ, hyQ⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hg) hyP
  obtain ⟨m, hmC, hQm⟩ := exists_conj_of_isSylowOf hS hQ
  have hyS : y ∈ S.map (MulAut.conj m).toMonoidHom := hQm ▸ hyQ (Subgroup.mem_zpowers y)
  obtain ⟨w, hwS, hwy⟩ := hyS
  have hwy' : m * w * m⁻¹ = y := hwy
  have hw : w = (m⁻¹ * g) * c * (m⁻¹ * g)⁻¹ := by
    rw [hy] at hwy'
    calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
      _ = (m⁻¹ * g) * c * (m⁻¹ * g)⁻¹ := by rw [hwy']; group
  have hwA : w ∈ A := mem_of_isPGroup hA3 h1617 hS.isPGroup hAS hwS (by
    rw [hw, conj_pow, hc3, mul_one, mul_inv_cancel])
  have h1 := h1618 (m⁻¹ * g) (hw ▸ hwA)
  have hmc : m * c * m⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hmC, mul_inv_cancel_right]
  calc Subgroup.zpowers y = Subgroup.zpowers (m * w * m⁻¹) := by rw [hwy']
    _ = (Subgroup.zpowers w).map (MulAut.conj m).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        rfl
    _ = (Subgroup.zpowers c).map (MulAut.conj m).toMonoidHom := by rw [hw, h1]
    _ = Subgroup.zpowers (m * c * m⁻¹) := by
        rw [MonoidHom.map_zpowers]
        rfl
    _ = Subgroup.zpowers c := by rw [hmc]

theorem weaklyClosed_of_steps {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (h1618 : ∀ g : G, g * c * g⁻¹ ∈ A → Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c) :
    ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c := by
  intro g hg
  have hmap : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * c * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hmap] at hg ⊢
  have hN : g * c * g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hg (Subgroup.mem_zpowers _)
  have hc3 : (g * c * g⁻¹) ^ 3 ^ 1 = 1 := by
    rw [pow_one, conj_pow, h.isElemAbelian.2 c h.mem_A, mul_one, mul_inv_cancel]
  exact zpowers_eq_of_conj_mem_centralizer h h1617 h1618
    (Sec17.Proof175.mem_centralizer_of_mem_normalizer h.orderOf_eq hN hc3)

theorem false_of_noncomm_quot {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (h1617 : ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A) {M : Subgroup G}
    {X : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)}
    (hX : ∃ x y : ↥X, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set ↥X))) : False := by
  obtain ⟨x, y, hx3, hy3, hxy, hQ⟩ := hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥M with hN
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hQ' : IsPGroup 3 ((Subgroup.closure ({x, y} : Set ↥X)).map X.subtype) := hQ.map _
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  obtain ⟨R, rfl⟩ := Sylow.mapSurjective_surjective hπs 3 S
  have hmem : ∀ z ∈ ({x, y} : Set ↥X), (z : ↥M ⧸ N) ∈ (R : Subgroup ↥M).map π := by
    intro z hz
    have := hS ⟨z, Subgroup.subset_closure hz, rfl⟩
    rwa [Sylow.coe_mapSurjective] at this
  obtain ⟨x', hx'R, hx'⟩ := hmem x (by simp)
  obtain ⟨y', hy'R, hy'⟩ := hmem y (by simp)
  have hinj := Sec17.Proof176.injOn_mk_pPrimeCore (K := M) R.isPGroup'
  have hx'3 : x' ^ 3 = 1 := hinj (pow_mem hx'R 3) (one_mem _) (by
    rw [map_pow, map_one, hx']
    exact congrArg Subtype.val hx3)
  have hy'3 : y' ^ 3 = 1 := hinj (pow_mem hy'R 3) (one_mem _) (by
    rw [map_pow, map_one, hy']
    exact congrArg Subtype.val hy3)
  have hRG : IsPGroup 3 ((R : Subgroup ↥M).map M.subtype) := R.isPGroup'.map _
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [h.card_eq]; norm_num)
  have hcomm := commute_of_isPGroup h.isElemAbelian.2 (fun a ha b hb => h.commute ha hb) hA
    h1617 hRG ⟨x', hx'R, rfl⟩ ⟨y', hy'R, rfl⟩
    (by rw [← map_pow, hx'3, map_one])
    (by rw [← map_pow, hy'3, map_one])
  have hcomm' : x' * y' = y' * x' := Subtype.ext (by simpa using hcomm)
  apply hxy
  apply Subtype.ext
  have := congrArg π hcomm'
  rw [map_mul, map_mul, hx', hy'] at this
  simpa using this

theorem exists_noncomm_three_of_j2
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ x y : X, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set X)) := by
  obtain ⟨e0⟩ := hX
  set e : X ≃* Sec4.Sporadic.J2.GJ :=
    e0.trans CFSG.ComponentClassification.J2Cover.nativeEquivP with he
  refine ⟨e.symm Sec4.Sporadic.J2.xJ, e.symm Sec4.Sporadic.J2.yJ, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, Sec4.Sporadic.J2.x_cube, map_one]
  · rw [← map_pow, Sec4.Sporadic.J2.y_cube, map_one]
  · intro hc
    apply Sec4.Sporadic.J2.z_ne_one
    rw [commutatorElement_eq_one_iff_mul_comm]
    have h1 := congrArg e hc
    simpa using h1
  · have hcl : Subgroup.closure ({e.symm Sec4.Sporadic.J2.xJ, e.symm Sec4.Sporadic.J2.yJ} :
        Set X) = Sec4.Sporadic.J2.P3.map e.symm.toMonoidHom := by
      rw [Sec4.Sporadic.J2.P3, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [hcl]
    exact IsPGroup.of_card (n := 3) (by
      rw [Subgroup.card_map_of_injective e.symm.injective, Sec4.Sporadic.J2.card_P3]
      norm_num)

omit [Finite G] in
theorem normalClosureSub_le_normalClosureIn (M : Subgroup G) (c : G) :
    normalClosureSub M (Subgroup.zpowers c) ≤ normalClosureIn M c := by
  rw [normalClosureSub, Subgroup.map_le_iff_le_comap]
  have hnorm : ((normalClosureIn M c).comap M.subtype).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have hle : (normalClosureIn M c).map (MulAut.conj (m : G)).toMonoidHom ≤
        normalClosureIn M c := by
      rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, ⟨m', hm', rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨m * m', mul_mem m.2 hm', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have := hle ⟨n, hn, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hc : c ∈ normalClosureIn M c :=
    Subgroup.subset_closure ⟨1, M.one_mem, by group⟩
  refine Subgroup.normalClosure_le_normal (N := (normalClosureIn M c).comap M.subtype) ?_
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  exact (Subgroup.zpowers_le.mpr hc) hx

theorem isCyclic_of_open_pRank_le_one {D : Subgroup G} (hD : CFSG.Open.pRank 3 D ≤ 1)
    (P : Sylow 3 ↥D) : IsCyclic ↥(P : Subgroup ↥D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥(P : Subgroup ↥D)) := ⟨P.isPGroup'⟩
  by_contra hnc
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  set E' : Subgroup G := (E.map (P : Subgroup ↥D).subtype).map D.subtype with hE'
  have hE'D : E' ≤ D := Subgroup.map_subtype_le _
  have hE'el : CFSG.Open.IsElemAbelian 3 E' :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mp hel) _) _
  have hE'card : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective D.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]
  have := CFSG.SectionRank.le_pRank (by norm_num) hE'D hE'el hE'card
  omega

end CFSG.RankThree.PartTwo.Sec16.Proof1622

