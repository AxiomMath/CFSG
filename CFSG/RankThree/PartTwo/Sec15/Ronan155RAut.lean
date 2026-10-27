module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155RCore
public import CFSG.RankThree.PartTwo.Sec15.Ronan155RKFact
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXTools
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155R

open CFSG

variable {G : Type} [Group G]

theorem le_or_eq_of_normal [Finite G] {J V W : Subgroup G} (hJp : Group.IsPerfect ↥J)
    [(V.subgroupOf J).Normal] (hs : IsSimpleGroup (↥J ⧸ V.subgroupOf J)) (hVJ : V ≤ J)
    (hV2 : IsPGroup 2 V) (hWJ : W ≤ J) (hJW : J ≤ Subgroup.normalizer (W : Set G)) :
    W ≤ V ∨ W = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' := W.subgroupOf J with hW'
  haveI hW'n : W'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWJ).mpr hJW
  set π := QuotientGroup.mk' (V.subgroupOf J) with hπ
  haveI hn : (W'.map π).Normal := Subgroup.Normal.map hW'n π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W'.map π) with h | h
  · left
    intro w hw
    have hw' : (⟨w, hWJ hw⟩ : ↥J) ∈ W' := Subgroup.mem_subgroupOf.mpr hw
    have h1 : π ⟨w, hWJ hw⟩ ∈ W'.map π := Subgroup.mem_map_of_mem _ hw'
    rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · right
    have hV2' : IsPGroup 2 (V.subgroupOf J) :=
      hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVJ).symm
    have hq : IsPGroup 2 (↥J ⧸ W') := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx : π x ∈ W'.map π := h ▸ Subgroup.mem_top _
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
      have hv : w⁻¹ * x ∈ V.subgroupOf J := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hwx
        exact QuotientGroup.eq.mp hwx
      obtain ⟨k, hk⟩ := hV2' ⟨w⁻¹ * x, hv⟩
      refine ⟨k, ?_⟩
      have hk' : (w⁻¹ * x) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have hxq : ((x : ↥J) : ↥J ⧸ W') = ((w⁻¹ * x : ↥J) : ↥J ⧸ W') := by
        rw [QuotientGroup.eq]
        have : x⁻¹ * (w⁻¹ * x) = x⁻¹ * w⁻¹ * x⁻¹⁻¹ := by group
        rw [this]
        exact hW'n.conj_mem _ (W'.inv_mem hw) _
      rw [hxq, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    have htop := CFSG.RankThree.PartTwo.Sec15.Proof152Gen.eq_top_of_isPerfect_of_isPGroup_quotient
      hJp W' hq
    refine le_antisymm hWJ fun j hj => ?_
    have : (⟨j, hj⟩ : ↥J) ∈ W' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

section Action

variable (J V : Subgroup G)

noncomputable abbrev conjJ
    (g : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G))) : MulAut ↥J :=
  Subgroup.normalizerMonoidHom J ⟨g, (Subgroup.mem_inf.mp g.2).1⟩

theorem conjJ_apply_coe
    (g : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G))) (x : ↥J) :
    ((conjJ J V g x : ↥J) : G) = (g : G) * x * (g : G)⁻¹ := by
  simp [conjJ]

theorem map_conjJ (g : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G))) :
    (V.subgroupOf J).map (conjJ J V g : ↥J →* ↥J) = V.subgroupOf J := by
  have hgJ := (Subgroup.mem_inf.mp g.2).1
  have hgV := (Subgroup.mem_inf.mp g.2).2
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf, MonoidHom.coe_coe, conjJ_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hgV _).mp hx
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hy : (g : G)⁻¹ * x * (g : G)⁻¹⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgJ) x).mp x.2
    refine ⟨⟨(g : G)⁻¹ * x * (g : G)⁻¹⁻¹, hy⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) x).mp hx
    · apply Subtype.ext
      rw [MonoidHom.coe_coe, conjJ_apply_coe]
      group

variable [(V.subgroupOf J).Normal]

@[expose] noncomputable def conjQuot :
    ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G)) →*
      MulAut (↥J ⧸ V.subgroupOf J) where
  toFun g := QuotientGroup.congr (V.subgroupOf J) (V.subgroupOf J) (conjJ J V g) (map_conjJ J V g)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [conjJ_apply_coe]
      simp
  map_mul' g h := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      congr 1
      apply Subtype.ext
      rw [conjJ_apply_coe, conjJ_apply_coe, conjJ_apply_coe]
      simp only [Subgroup.coe_mul]
      group

theorem conjQuot_mk (g : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G)))
    (x : ↥J) : conjQuot J V g (x : ↥J ⧸ V.subgroupOf J) =
      ((conjJ J V g x : ↥J) : ↥J ⧸ V.subgroupOf J) :=
  QuotientGroup.congr_mk (V.subgroupOf J) (V.subgroupOf J) (conjJ J V g) (map_conjJ J V g) x

@[expose] noncomputable def betaAut {S : Type*} [Group S] (φ : ↥J ⧸ V.subgroupOf J ≃* S) :
    ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G)) →* MulAut S :=
  (MulAut.congr φ).toMonoidHom.comp (conjQuot J V)

theorem betaAut_mk {S : Type*} [Group S] (φ : ↥J ⧸ V.subgroupOf J ≃* S)
    (g : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G))) (x : ↥J) :
    betaAut J V φ g (φ (x : ↥J ⧸ V.subgroupOf J)) =
      φ ((conjJ J V g x : ↥J) : ↥J ⧸ V.subgroupOf J) := by
  simp only [betaAut, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [conjQuot_mk]

end Action

section Transfer

variable {J V : Subgroup G} [(V.subgroupOf J).Normal] {S : Type*} [Group S]

theorem mem_secCent_of_betaAut_eq_one (φ : ↥J ⧸ V.subgroupOf J ≃* S) {R : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) {r : G} (hr : r ∈ R)
    (hrN : r ∈ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G))
    (h1 : betaAut J V φ ⟨r, hrN⟩ = 1) : r ∈ secCent R J V := by
  refine ⟨hr, (Subgroup.mem_inf.mp hrN).2, fun j hj => ?_⟩
  have h := congrArg (fun β : MulAut S => β (φ ((⟨j, hj⟩ : ↥J) : ↥J ⧸ V.subgroupOf J))) h1
  simp only [MulAut.one_apply] at h
  rw [betaAut_mk] at h
  have h' := φ.injective h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjJ_apply_coe] at h'
  have e : r * j * r⁻¹ * j⁻¹ = j * ((r * j * r⁻¹)⁻¹ * j)⁻¹ * j⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hJV hj) _).mp (V.inv_mem h')

theorem betaAut_fix (φ : ↥J ⧸ V.subgroupOf J ≃* S) (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (g : ↥(Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G))) (x : ↥J)
    (hx : (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ ∈ V) :
    betaAut J V φ g (φ (x : ↥J ⧸ V.subgroupOf J)) = φ (x : ↥J ⧸ V.subgroupOf J) := by
  rw [betaAut_mk]
  congr 1
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjJ_apply_coe]
  have e : ((g : G) * x * (g : G)⁻¹)⁻¹ * x =
      (x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹ * (x : G)⁻¹)⁻¹ * (x : G)⁻¹⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hJV (J.inv_mem x.2)) _).mp (V.inv_mem hx)

theorem betaAut_facts (φ : ↥J ⧸ V.subgroupOf J ≃* S) {R X : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hRJ : R ≤ Subgroup.normalizer (J : Set G))
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (hRX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ V)
    {H : Subgroup S} (hH : ∀ h ∈ H, ∃ x : ↥J, (x : G) ∈ X ∧ φ (x : ↥J ⧸ V.subgroupOf J) = h) :
    ∃ hmem : ∀ r ∈ R, r ∈ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G),
      (∀ r (hr : r ∈ R), ∀ h ∈ H, betaAut J V φ ⟨r, hmem r hr⟩ h = h) ∧
      (∀ r (hr : r ∈ R), r ^ 2 = 1 → betaAut J V φ ⟨r, hmem r hr⟩ ^ 2 = 1) ∧
      (∀ r (hr : r ∈ R), r ∉ secCent R J V → betaAut J V φ ⟨r, hmem r hr⟩ ≠ 1) := by
  have hmem : ∀ r ∈ R, r ∈ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    fun r hr => Subgroup.mem_inf.mpr ⟨hRJ hr, hRV hr⟩
  refine ⟨hmem, fun r hr h hh => ?_, fun r hr hr2 => ?_, fun r hr hn h => ?_⟩
  · obtain ⟨x, hxX, rfl⟩ := hH h hh
    exact betaAut_fix φ hJV _ x (hRX r hr x hxX)
  · rw [← map_pow]
    have : (⟨r, hmem r hr⟩ : ↥(Subgroup.normalizer (J : Set G) ⊓
        Subgroup.normalizer (V : Set G))) ^ 2 = 1 := Subtype.ext (by simpa using hr2)
    rw [this, map_one]
  · exact hn (mem_secCent_of_betaAut_eq_one φ hJV hr (hmem r hr) h)

theorem h3_of_iii (φ : ↥J ⧸ V.subgroupOf J ≃* S) {R X : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hRJ : R ≤ Subgroup.normalizer (J : Set G))
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (hRX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ V)
    {H : Subgroup S} (hH : ∀ h ∈ H, ∃ x : ↥J, (x : G) ∈ X ∧ φ (x : ↥J ⧸ V.subgroupOf J) = h)
    (hiii : ∀ α β : MulAut S, α ^ 2 = 1 → β ^ 2 = 1 → α ≠ 1 → β ≠ 1 →
      (∀ h ∈ H, α h = h) → (∀ h ∈ H, β h = h) → α = β) :
    ∀ b₁ ∈ R, ∀ b₂ ∈ R, b₁ ^ 2 = 1 → b₂ ^ 2 = 1 → b₁ ∉ secCent R J V →
      b₂ ∉ secCent R J V → b₁ * b₂ ∈ secCent R J V := by
  intro b₁ hb₁ b₂ hb₂ h1 h2 hn1 hn2
  obtain ⟨hmem, hfix, hsq, hne⟩ := betaAut_facts φ hJV hRJ hRV hRX hH
  have heq := hiii _ _ (hsq b₁ hb₁ h1) (hsq b₂ hb₂ h2) (hne b₁ hb₁ hn1) (hne b₂ hb₂ hn2)
    (hfix b₁ hb₁) (hfix b₂ hb₂)
  have hb12 : b₁ * b₂ ∈ R := R.mul_mem hb₁ hb₂
  apply mem_secCent_of_betaAut_eq_one φ hJV hb12 (hmem _ hb12)
  have : (⟨b₁ * b₂, hmem _ hb12⟩ : ↥(Subgroup.normalizer (J : Set G) ⊓
      Subgroup.normalizer (V : Set G))) = ⟨b₁, hmem b₁ hb₁⟩ * ⟨b₂, hmem b₂ hb₂⟩ := rfl
  rw [this, map_mul, ← heq, ← pow_two, hsq b₁ hb₁ h1]

theorem h4_of_iv (φ : ↥J ⧸ V.subgroupOf J ≃* S) {R X : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hRJ : R ≤ Subgroup.normalizer (J : Set G))
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (hRX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ V)
    {H : Subgroup S} (hH : ∀ h ∈ H, ∃ x : ↥J, (x : G) ∈ X ∧ φ (x : ↥J ⧸ V.subgroupOf J) = h)
    (hiv : ∀ β : MulAut S, β ^ 2 = 1 → β ≠ 1 → (∀ h ∈ H, β h = h) → ∃ j, (β j * j⁻¹) ^ 12 ≠ 1) :
    ∀ b ∈ R, b ^ 2 = 1 → b ∉ secCent R J V → ∃ j ∈ J, (b * j * b⁻¹ * j⁻¹) ^ 12 ∉ V := by
  intro b hb hb2 hbn
  obtain ⟨hmem, hfix, hsq, hne⟩ := betaAut_facts φ hJV hRJ hRV hRX hH
  obtain ⟨s, hs⟩ := hiv _ (hsq b hb hb2) (hne b hb hbn) (hfix b hb)
  obtain ⟨q, rfl⟩ := φ.surjective s
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨x, x.2, fun hV => hs ?_⟩
  rw [betaAut_mk, ← map_inv, ← map_mul, ← map_pow, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  rw [(QuotientGroup.eq_one_iff _).mpr, map_one]
  rw [Subgroup.mem_subgroupOf]
  simpa [conjJ_apply_coe] using hV

end Transfer

section Image

variable {J V X : Subgroup G} [(V.subgroupOf J).Normal] {S : Type*} [Group S]

@[expose] noncomputable def secHom (hXJ : X ≤ J) (φ : ↥J ⧸ V.subgroupOf J ≃* S) : ↥X →* S :=
  (φ.toMonoidHom.comp (QuotientGroup.mk' (V.subgroupOf J))).comp (Subgroup.inclusion hXJ)

theorem secHom_apply (hXJ : X ≤ J) (φ : ↥J ⧸ V.subgroupOf J ≃* S) (x : ↥X) :
    secHom hXJ φ x = φ ((Subgroup.inclusion hXJ x : ↥J) : ↥J ⧸ V.subgroupOf J) :=
  rfl

theorem mem_ker_secHom (hXJ : X ≤ J) (φ : ↥J ⧸ V.subgroupOf J ≃* S) (x : ↥X) :
    x ∈ (secHom hXJ φ).ker ↔ (x : G) ∈ V := by
  rw [MonoidHom.mem_ker, secHom_apply, map_eq_one_iff _ φ.injective, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  rfl

theorem exists_of_mem_range_secHom (hXJ : X ≤ J) (φ : ↥J ⧸ V.subgroupOf J ≃* S) {h : S}
    (hh : h ∈ (secHom hXJ φ).range) :
    ∃ x : ↥J, (x : G) ∈ X ∧ φ (x : ↥J ⧸ V.subgroupOf J) = h := by
  obtain ⟨x, rfl⟩ := hh
  exact ⟨Subgroup.inclusion hXJ x, x.2, rfl⟩

theorem commutator_range_secHom (hXJ : X ≤ J) (φ : ↥J ⧸ V.subgroupOf J ≃* S)
    (hXp : Group.IsPerfect ↥X) :
    ⁅(secHom hXJ φ).range, (secHom hXJ φ).range⁆ = (secHom hXJ φ).range := by
  have : Group.IsPerfect ↥(secHom hXJ φ).range :=
    Group.IsPerfect.ofSurjective (f := (secHom hXJ φ).rangeRestrict)
      (secHom hXJ φ).rangeRestrict_surjective
  exact Subgroup.isPerfect_iff.mp this

theorem map_subgroupOf_range {S' : Type*} [Group S'] {Y : Type*} [Group Y] (f : Y →* S')
    (K : Subgroup Y) : (K.map f).subgroupOf f.range = K.map f.rangeRestrict := by
  ext ⟨h, hh⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, Subtype.ext rfl⟩
  · rintro ⟨k, hk, hkh⟩
    exact ⟨k, hk, congrArg Subtype.val hkh⟩

scoped instance normal_subgroupOf_range {S' : Type*} [Group S'] {Y : Type*} [Group Y] (f : Y →* S')
    (K : Subgroup Y) [K.Normal] : ((K.map f).subgroupOf f.range).Normal := by
  rw [map_subgroupOf_range]
  exact Subgroup.Normal.map inferInstance _ f.rangeRestrict_surjective

theorem nonempty_mulEquiv_secHom [Finite G] (hXJ : X ≤ J) (φ : ↥J ⧸ V.subgroupOf J ≃* S)
    (hXV : X ⊓ V ≤ CFSG.Open.pCoreOf 2 X) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(secHom hXJ φ).range ⧸
      ((CFSG.pCore 2 ↥X).map (secHom hXJ φ)).subgroupOf (secHom hXJ φ).range) := by
  set g := secHom hXJ φ with hg
  set χ : ↥X →* ↥g.range ⧸ ((CFSG.pCore 2 ↥X).map g).subgroupOf g.range :=
    (QuotientGroup.mk' _).comp g.rangeRestrict with hχ
  have hχs : Function.Surjective χ :=
    (QuotientGroup.mk'_surjective _).comp g.rangeRestrict_surjective
  have hker : χ.ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, map_subgroupOf_range, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : g y = g x := congrArg Subtype.val hyx
      have hk : y⁻¹ * x ∈ g.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx', inv_mul_cancel]
      rw [hg, mem_ker_secHom] at hk
      have hkX : ((y⁻¹ * x : ↥X) : G) ∈ CFSG.Open.pCoreOf 2 X :=
        hXV (Subgroup.mem_inf.mpr ⟨(y⁻¹ * x).2, hk⟩)
      rw [CFSG.mem_openPCoreOf_iff] at hkX
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy hkX
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hχs)⟩

end Image

end CFSG.RankThree.PartTwo.Sec15.Ronan155R
