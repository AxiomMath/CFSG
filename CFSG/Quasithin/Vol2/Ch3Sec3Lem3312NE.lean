module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312B

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L3312.NQ

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem mem_zpowers_iff_of_sq {G : Type} [Group G] {w : G} (hw : w * w = 1) {x : G} :
    x ∈ Subgroup.zpowers w ↔ x = 1 ∨ x = w := by
  constructor
  · rintro ⟨k, rfl⟩
    have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two, hw]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      show w ^ k = 1
      rw [hm, zpow_mul, hw2, one_zpow]
    · right
      show w ^ k = w
      rw [hm, zpow_add, zpow_mul, hw2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem center_eq_zpowers {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {w : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)} (hw : w * w = 1) (hw1 : w ≠ 1) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = Subgroup.zpowers w := by
  have h2 := CFSG.SectionRank.Ccomm.two_ne_zero_zmod hp
  have hwm : (w : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
    have hsq : (w : Matrix (Fin 2) (Fin 2) (ZMod p)) * w = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hw, Matrix.SpecialLinearGroup.coe_one]
    rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one h2 w.2 hsq with h | h
    · exact absurd (Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm)) hw1
    · exact h
  apply le_antisymm
  · intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin, pow_two, mul_self_eq_one_iff] at hr
    rw [mem_zpowers_iff_of_sq hw]
    rcases hr with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hrA, map_one, Matrix.SpecialLinearGroup.coe_one]
    · right
      apply Subtype.ext
      rw [← hrA, hwm, map_neg, map_one]
  · rw [Subgroup.zpowers_le, Matrix.SpecialLinearGroup.mem_center_iff]
    exact ⟨-1, by rw [Fintype.card_fin, neg_one_sq], by rw [hwm, map_neg, map_one]⟩

theorem isPSL_of_equiv {X Y : Type} [Group X] [Group Y] {n p e : ℕ} (f : X ≃* Y)
    (h : IsPSL n p e Y) : IsPSL n p e X := by
  obtain ⟨hadm, K, hK, hfin, hcard, ⟨g⟩⟩ := h
  exact ⟨hadm, K, hK, hfin, hcard, ⟨f.trans g⟩⟩

theorem isPSL_of_surjective {Y : Type} [Group Y] {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (π : Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hπ : Function.Surjective π)
    (M : Subgroup Y) [M.Normal] (hM : M = (Subgroup.center _).comap π) :
    IsPSL 2 p 1 (Y ⧸ M) := by
  let φ := (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))).comp π
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hπ
  have hker : M = φ.ker := by
    rw [hM, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e : Y ⧸ M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  refine ⟨⟨hp.out, le_rfl, le_rfl, ?_, ?_⟩, ZMod p, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod p))⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only [pow_one] at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only [pow_one] at this
    omega

theorem isAlt_five_of_isPSL {X : Type} [Group X]
    (h : IsPSL 2 5 1 X) : IsAlt 5 X := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr (by rw [hcard, pow_one]))
  exact ⟨e.trans e5⟩

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem characteristic_sup {O : Subgroup Q} [O.Characteristic]
    (huniq : ∀ t t' : Q, t * t = 1 → t' * t' = 1 → t ∉ O → t' ∉ O → t'⁻¹ * t ∈ O)
    {z : Q} (hz2 : z * z = 1) (hzO : z ∉ O) : (O ⊔ Subgroup.zpowers z).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro a
  rw [Subgroup.map_sup, sup_le_iff, MonoidHom.map_zpowers,
    Subgroup.characteristic_iff_map_eq.mp ‹O.Characteristic› a, Subgroup.zpowers_le]
  refine ⟨le_sup_left, ?_⟩
  have haz2 : a z * a z = 1 := by rw [← map_mul, hz2, map_one]
  have hazO : a z ∉ O := by
    intro h
    apply hzO
    have := Subgroup.characteristic_iff_map_eq.mp ‹O.Characteristic› a⁻¹
    rw [← this]
    exact ⟨a z, h, by simp⟩
  have h := huniq (a z) z haz2 hz2 hazO hzO
  have : a.toMonoidHom z = z * (z⁻¹ * a z) := by
    rw [mul_inv_cancel_left]
    rfl
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    (Subgroup.mem_sup_left h)

omit [Finite Q] in
@[expose] noncomputable def quotAut (M : Subgroup Q) [M.Characteristic] :
    MulAut Q →* MulAut (Q ⧸ M) where
  toFun a := QuotientGroup.congr M M a (Subgroup.characteristic_iff_map_eq.mp inferInstance a)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

omit [Finite Q] in
theorem quotAut_mk (M : Subgroup Q) [M.Characteristic] (a : MulAut Q) (x : Q) :
    quotAut M a (x : Q ⧸ M) = ((a x : Q) : Q ⧸ M) :=
  rfl

omit [Finite Q] in
theorem quotAut_conj (M : Subgroup Q) [M.Characteristic] (q : Q) :
    quotAut M (MulAut.conj q) = MulAut.conj (q : Q ⧸ M) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [quotAut_mk, MulAut.conj_apply, MulAut.conj_apply]
    rfl

omit [Finite Q] in
theorem map_quotAut_map (M : Subgroup Q) [M.Characteristic] (a : MulAut Q) (B : Subgroup Q) :
    (B.map (QuotientGroup.mk' M)).map (quotAut M a).toMonoidHom =
      (B.map a.toMonoidHom).map (QuotientGroup.mk' M) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowTwoOf_map {G K : Type} [Group G] [Group K] {A S : Subgroup G}
    (hS : IsSylowTwoOf S A) (f : G →* K) : IsSylowTwoOf (S.map f) (A.map f) := by
  refine ⟨Subgroup.map_mono hS.1, hS.2.1.map f, ?_⟩
  have h1 : (S.map f).subgroupOf (A.map f) = (S.subgroupOf A).map (f.subgroupMap A) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, hsy⟩
      exact ⟨⟨s, hS.1 hs⟩, hs, Subtype.ext hsy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  intro hd
  apply hS.2.2
  rw [h1] at hd
  exact hd.trans (Subgroup.index_map_dvd _ (f.subgroupMap_surjective A))

omit [Finite Q] in
theorem map_le_sup_of_oddNorm_quot {M : Subgroup Q} [M.Characteristic] {B : Subgroup Q}
    (hN : OddNorm (Q ⧸ M) (B.map (QuotientGroup.mk' M))) {A S : Subgroup (MulAut Q)}
    (hInn : (MulAut.conj : Q →* MulAut Q).range ≤ A) (hS : IsSylowTwoOf S A)
    (hSB : S ≤ MulAction.stabilizer (MulAut Q) B) {d : MulAut Q}
    (hd : d ∈ Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A) (hodd : Odd (orderOf d)) :
    B.map d.toMonoidHom ≤ B ⊔ M := by
  have hInn' : (MulAut.conj : Q ⧸ M →* MulAut (Q ⧸ M)).range ≤ A.map (quotAut M) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨MulAut.conj q, hInn ⟨q, rfl⟩, quotAut_conj M q⟩
  have hSB' : S.map (quotAut M) ≤
      MulAction.stabilizer (MulAut (Q ⧸ M)) (B.map (QuotientGroup.mk' M)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_stabilizer_subgroup_iff, map_quotAut_map, mem_stabilizer_subgroup_iff.mp (hSB hs)]
  have hd' : quotAut M d ∈ Subgroup.normalizer ((S.map (quotAut M) : Subgroup _) :
      Set (MulAut (Q ⧸ M))) ⊓ A.map (quotAut M) :=
    ⟨Subgroup.le_normalizer_map _ ⟨d, hd.1, rfl⟩, ⟨d, hd.2, rfl⟩⟩
  have hodd' : Odd (orderOf (quotAut M d)) := Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)
  have h := hN _ _ hInn' (isSylowTwoOf_map hS _) hSB' _ hd' hodd'
  rw [mem_stabilizer_subgroup_iff, map_quotAut_map] at h
  intro x hx
  have hx' : QuotientGroup.mk' M x ∈ B.map (QuotientGroup.mk' M) := by
    rw [← h]
    exact ⟨x, hx, rfl⟩
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hx'
  exact hx'

omit [Finite Q] in
theorem isAlt_five_map {B M : Subgroup Q} [M.Normal]
    (e : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) {z : Q} (hzB : z ∈ B)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hBM : ∀ x ∈ B, x ∈ M ↔ x = 1 ∨ x = z) :
    IsAlt 5 ↥(B.map (QuotientGroup.mk' M)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f := (QuotientGroup.mk' M).comp B.subtype
  have hrange : B.map (QuotientGroup.mk' M) = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hz2' : e ⟨z, hzB⟩ * e ⟨z, hzB⟩ = 1 := by
    rw [← map_mul]
    exact (MulEquiv.map_eq_one_iff e).mpr (Subtype.ext hz2)
  have hz1' : e ⟨z, hzB⟩ ≠ 1 := fun h =>
    hz1 (congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).mp h))
  have hker : f.ker = (Subgroup.center _).comap e.toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, center_eq_zpowers (by norm_num) hz2' hz1',
      mem_zpowers_iff_of_sq hz2']
    change (QuotientGroup.mk' M) (x : Q) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hBM x x.2,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, e.injective.eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have hpsl := isPSL_of_surjective le_rfl e.toMonoidHom e.surjective f.ker hker
  exact isAlt_five_of_isPSL (isPSL_of_equiv
    ((MulEquiv.subgroupCongr hrange).trans (QuotientGroup.quotientKerEquivRange f).symm) hpsl)

end CFSG.Quasithin.H13.L3312.NQ
