module

public import CFSG.Quasithin.Vol2.Ch10SecB4Lift
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_map_range {K : Type*} [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) : IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, fun hd => hS.2.2 ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range = (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h1] at hd
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

omit [Finite G] in
theorem isSylowOf_of_isSylowTwoOf {S H : Subgroup G} (hS : IsSylowTwoOf S H) :
    CFSG.ABGLocalTools.IsSylowOf 2 S H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2, ?_⟩
  show (S.subgroupOf H).map H.subtype = S
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS.1]

@[expose] noncomputable def conjLBar (L T : Subgroup G)
    (h : L ⊔ T ≤ Subgroup.normalizer (L : Set G)) :
    ↥(L ⊔ T) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
  (SteinbergBS.conjQuotientHom L (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion h)

omit [Finite G] in
theorem conjLBar_mk {L T : Subgroup G} (h : L ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (g : ↥(L ⊔ T)) {l : G} (hl : l ∈ L) :
    conjLBar L T h g (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp (h g.2) l).mp hl⟩ := by
  rfl

omit [Finite G] in
theorem center_lbar_eq_bot {L : Subgroup G} {k : ℕ}
    (hk : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL k 2 1) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hk
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  set e' := e.trans (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two k K hK2)
  have hc := QuasithinUnique.Setup.Family.center_specialLinear_eq_bot_of_card_two k (ZMod 2)
    (by rw [Nat.card_zmod])
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => e'.injective ?_
  rw [map_one]
  have hz' : e' z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := e'.surjective w
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz w')]
  rw [hc] at hz'
  exact hz'

omit [Finite G] in
theorem isPGroup_quotient_sup {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    [(L.subgroupOf (L ⊔ T)).Normal] : IsPGroup 2 (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hg : (g : G) ∈ ((L ⊔ T : Subgroup G) : Set G) := g.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTL] at hg
    obtain ⟨l, hl, s, hs, hgls⟩ := Set.mem_mul.mp hg
    obtain ⟨j, hj⟩ := hT ⟨s, hs⟩
    have hj' : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
    refine ⟨j, ?_⟩
    have e : g = ⟨l, le_sup_left (a := L) hl⟩ * ⟨s, le_sup_right (b := T) hs⟩ :=
      Subtype.ext hgls.symm
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, e]
    obtain ⟨l', hl', hpow⟩ := A4.exists_pow_mul_eq hl (hTL hs) (2 ^ j)
    show (l * s) ^ 2 ^ j ∈ L
    rw [hpow, hj', mul_one]
    exact hl'

theorem ker_conjLBar {H T L : Subgroup G} (hT : IsSylowTwoOf T H) (hLH : L ≤ H)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hcl : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥)
    (hEN : L ⊔ T ≤ Subgroup.normalizer (L : Set G)) :
    (conjLBar L T hEN).ker = CFSG.pCore 2 ↥(L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (L.subgroupOf (L ⊔ T)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  have hTE : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hT.2.1, fun hd =>
    hT.2.2 (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T (L ⊔ T) H le_sup_right
      (sup_le hLH hT.1))))⟩
  have hPT : inSubgroup (CFSG.pCore 2) (L ⊔ T) ≤ T :=
    IsSylowIn.le_of_normal (p := 2) hTE (Subgroup.map_subtype_le _)
      (by
        rw [inSubgroup, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective]
        exact CFSG.pCore_normal)
      ((CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥(L ⊔ T))).map _)
  obtain ⟨-, hC, -⟩ := SteinbergBS.centerless_two_residual_has_original_two_core_centralizer
    (E := L ⊔ T) (L := L) (B := L ⊔ T) (T := T) le_sup_left
    (isPGroup_quotient_sup hT.2.1 hTL) le_sup_right (isSylowOf_of_isSylowTwoOf hTE) hPT hcl hEN
  ext g
  have hmem : (g : G) ∈ SteinbergBS.quotientCentralizer (L ⊔ T) L (CFSG.pCore 2 ↥L) ↔
      g ∈ CFSG.pCore 2 ↥(L ⊔ T) := by
    rw [hC, inSubgroup]
    constructor
    · rintro ⟨y, hy, hyg⟩
      rwa [Subtype.ext hyg] at hy
    · intro h
      exact ⟨g, h, rfl⟩
  rw [← hmem, SteinbergBS.mem_quotientCentralizer_iff, MonoidHom.mem_ker]
  constructor
  · intro h1
    refine ⟨g.2, hEN g.2, fun l hl => ?_⟩
    have h2 := DFunLike.congr_fun h1 (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩)
    rw [conjLBar_mk, MulAut.one_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem] at h2
    exact ⟨_, h2, by simp [div_eq_mul_inv]⟩
  · rintro ⟨-, -, h2⟩
    ext q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [conjLBar_mk, MulAut.one_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem]
    obtain ⟨k, hk, hkx⟩ := h2 l hl
    have hkx' : (k : G) = g * l * g⁻¹ * l⁻¹ := hkx
    have hkl : (⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hEN g.2) l).mp hl⟩ : ↥L) /
        ⟨l, hl⟩ = k := by
      apply Subtype.ext
      simp [div_eq_mul_inv, hkx']
    rw [hkl]
    exact hk

theorem nonempty_aut_of (hF : FactL4L5) {H T L X : Subgroup G} (hT : IsSylowTwoOf T H)
    (hL : L ∈ cComp H) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {k : ℕ} (hk45 : k = 4 ∨ k = 5)
    (hk : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL k 2 1)
    (hXL : X ≤ L) (hX : X = oTwoUpper X) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hpow : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) (hrel : (pCoreOf 2 X).relIndex X = 9)
    (hnc : ∃ a ∈ T, ∃ b ∈ T, ∃ y ∈ X,
      a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∉ pCoreOf 2 X) :
    Nonempty (↥(L ⊔ T) ⧸ CFSG.pCore 2 ↥(L ⊔ T) ≃*
      MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) := by
  have hEN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hLH : L ≤ H := le_of_mem_cComp hL
  set φ := conjLBar L T hEN with hφdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hTE : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hT.2.1, fun hd =>
    hT.2.2 (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T (L ⊔ T) H le_sup_right
      (sup_le hLH hT.1))))⟩
  have hinn : ∀ q : ↥L ⧸ CFSG.pCore 2 ↥L, MulAut.conj q ∈ φ.range := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
    refine ⟨⟨l, le_sup_left (a := L) hl⟩, ?_⟩
    ext r
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) r
    rw [hφdef, conjLBar_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hSY : ∀ α ∈ (T.subgroupOf (L ⊔ T)).map φ, ∀ y ∈ imgO2 L X, α y ∈ imgO2 L X := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨⟨x, hxL⟩, hx, rfl⟩
    have hsT : (s : G) ∈ T := hs
    have hx' : (x : G) ∈ X := hx
    rw [hφdef, conjLBar_mk]
    exact mk_mem_imgO2 _ ((Subgroup.mem_normalizer_iff.mp (hTX hsT) _).mp hx')
  have hpow' : ∀ q ∈ imgO2 L X, q ^ 3 ∈ pCoreOf 2 (imgO2 L X) := by
    rintro _ ⟨⟨y, hyL⟩, hyX, rfl⟩
    rw [← map_pow]
    exact map_pCoreOf_le hXL ⟨⟨y ^ 3, L.pow_mem hyL 3⟩, hpow y hyX, rfl⟩
  have hnc' : ∃ α ∈ (T.subgroupOf (L ⊔ T)).map φ, ∃ β ∈ (T.subgroupOf (L ⊔ T)).map φ,
      ∃ y ∈ imgO2 L X, (α * β) y * ((β * α) y)⁻¹ ∉ pCoreOf 2 (imgO2 L X) := by
    obtain ⟨a, ha, b, hb, y, hy, hne⟩ := hnc
    refine ⟨φ ⟨a, le_sup_right (b := T) ha⟩, ⟨_, ha, rfl⟩, φ ⟨b, le_sup_right (b := T) hb⟩,
      ⟨_, hb, rfl⟩, π ⟨y, hXL hy⟩, mk_mem_imgO2 _ hy, fun hmem => hne ?_⟩
    have hz : a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∈ X := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hTX (T.mul_mem ha hb)) y).mp hy
      have h2 := (Subgroup.mem_normalizer_iff.mp (hTX (T.mul_mem hb ha)) y).mp hy
      exact X.mul_mem h1 (X.inv_mem h2)
    refine mem_pCoreOf_of_mk hXL hz ?_
    convert hmem using 1
    rw [MulAut.mul_apply, MulAut.mul_apply, hφdef, conjLBar_mk, conjLBar_mk, conjLBar_mk,
      conjLBar_mk, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hA := hF _ k hk45 hk φ.range ((T.subgroupOf (L ⊔ T)).map φ) (imgO2 L X) hinn
    (isSylowTwoOf_map_range hTE φ) (imgO2_eq_oTwoUpper hXL hX) hSY hpow'
    (by rw [relIndex_imgO2 hXL, hrel]) hnc'
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hA
  have hker := ker_conjLBar hT hLH hTL (center_lbar_eq_bot hk) hEN
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hk
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hsurj).trans
      (MulAut.congr (e.trans
        (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two k K hK2))))⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
