module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAux616
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxGeom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Conj

public section

open CFSG.Open
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

structure NT {G : Type u} [Group G] (A : Subgroup G) (θ : G → Subgroup G) (a : G) : Prop where
  mem : a ∈ A
  ne_one : a ≠ 1
  not_solvable : ¬ Group.IsSolvable (θ a)

section NoFinite

variable {G : Type u} [Group G] {A : Subgroup G} {θ : G → Subgroup G}

@[expose] def FN (A : Subgroup G) (θ : G → Subgroup G) (a : G) : Subgroup G :=
  A ⊓ ⨅ J ∈ lcal (θ a), Subgroup.normalizer (J : Set G)

theorem mem_FN_iff {a x : G} :
    x ∈ FN A θ a ↔ x ∈ A ∧ ∀ J ∈ lcal (θ a), x ∈ Subgroup.normalizer (J : Set G) := by
  simp [FN, Subgroup.mem_inf, Subgroup.mem_iInf]

theorem FN_le (a : G) : FN A θ a ≤ A := inf_le_left

end NoFinite

section Section

variable {G : Type u} [Group G]

theorem isSolvable_of_inf_of_section {X H K : Subgroup G} (hXH : X ≤ H)
    (hnor : H ≤ Subgroup.normalizer (K : Set G)) (hsec : IsSolvableSection H K)
    (hXK : Group.IsSolvable ↥(X ⊓ K)) : Group.IsSolvable ↥X := by
  obtain ⟨n, hn⟩ := hsec
  have hXKn : X ≤ Subgroup.normalizer ((X ⊓ K : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hnor (hXH hx)⟩
  have : ((X ⊓ K).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hXKn
  have hq : Group.IsSolvable (↥X ⧸ (X ⊓ K).subgroupOf X) := by
    refine ⟨n, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective ((X ⊓ K).subgroupOf X)) n]
    refine le_bot_iff.mp ?_
    have hle : derivedSeries ↥X n ≤ (X ⊓ K).subgroupOf X := by
      intro x hx
      have h1 : (Subgroup.inclusion hXH x) ∈ derivedSeries ↥H n := by
        have := map_derivedSeries_le_derivedSeries (Subgroup.inclusion hXH) n
        exact this ⟨x, hx, rfl⟩
      have h2 := hn h1
      rw [Subgroup.mem_subgroupOf] at h2 ⊢
      exact ⟨x.2, h2⟩
    calc (derivedSeries ↥X n).map (QuotientGroup.mk' ((X ⊓ K).subgroupOf X))
        ≤ ((X ⊓ K).subgroupOf X).map (QuotientGroup.mk' ((X ⊓ K).subgroupOf X)) :=
          Subgroup.map_mono hle
      _ = ⊥ := QuotientGroup.map_mk'_self _
  have hN : Group.IsSolvable ↥((X ⊓ K).subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ K ≤ X)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ K ≤ X)).injective
  exact Group.isSolvable_of_ker_le_range ((X ⊓ K).subgroupOf X).subtype
    (QuotientGroup.mk' ((X ⊓ K).subgroupOf X)) (by simp)

end Section

section NT

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

variable (h : Counterexample p A θ)

include h

theorem NT.zpowers_mem
    {a : G} (ha : NT A θ a) : Subgroup.zpowers a ∈ rSetN p A θ 1 :=
  (h.zpowers_mem_rSetN_one_iff).mpr ⟨ha.mem, ha.ne_one, ha.not_solvable⟩

theorem NT.of_mem_rSetN_two
    {B : Subgroup G} (hB : B ∈ rSetN p A θ 2) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : NT A θ b := by
  have hBR := hB.1
  obtain ⟨-, hBA, -⟩ := h.mem_rSet_iff.mp hBR
  have hzR : Subgroup.zpowers b ∈ rSet p A θ :=
    h.rSet_mono hBR (Subgroup.zpowers_le.mpr hb)
      (fun hbot => hb1 (Subgroup.zpowers_eq_bot.mp hbot))
  obtain ⟨-, hzA, hzns⟩ := h.mem_rSet_iff.mp hzR
  refine ⟨hBA hb, hb1, ?_⟩
  rwa [h.hyp.isFunctor.thetaOf_zpowers (hBA hb) hb1] at hzns

theorem NT.zpowers_mem_rSet
    {a : G} (ha : NT A θ a) : Subgroup.zpowers a ∈ rSet p A θ :=
  (ha.zpowers_mem h).1

theorem NT.sol_eq_bot
    {a : G} (ha : NT A θ a) : sol (θ a) = ⊥ :=
  sol_apply_eq_bot h ha.mem ha.ne_one ha.not_solvable

omit h in
theorem NT.kOf_ne_bot {a : G} (ha : NT A θ a) : kOf (θ a) ≠ ⊥ :=
  Counterexample.kOf_ne_bot_of_not_isSolvable ha.not_solvable

theorem NT.isDirectProduct
    {a : G} (ha : NT A θ a) :
    IsDirectProduct (lcal (θ a)) (kOf (θ a)) :=
  isDirectProduct_lcal_kOf (ha.sol_eq_bot h)

theorem NT.lcal_kOf_eq
    {a : G} (ha : NT A θ a) : lcal (kOf (θ a)) = lcal (θ a) := by
  have hss : IsSemisimple (kOf (θ a)) := isSemisimple_kOf (ha.sol_eq_bot h)
  rw [hss.lcal_eq, simpleComponents_kOf (ha.sol_eq_bot h)]

theorem NT.lcal_nonempty
    {a : G} (ha : NT A θ a) : (lcal (θ a)).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have := (ha.isDirectProduct h).sSup_eq
  rw [hne, sSup_empty] at this
  exact ha.kOf_ne_bot this.symm

theorem NT.semisimpleAction
    {a : G} (ha : NT A θ a) :
    SemisimpleAction p A (kOf (θ a)) where
  prime := h.hyp.prime
  odd := h.hyp.odd
  elemAbelian := h.hyp.elemAbelian
  admits := Nonsolv.le_normalizer_kOf_of_le_normalizer
    (h.hyp.isFunctor.normalized a ha.mem ha.ne_one)
  nearPSolvable := signalizerNearPSolvable_of_le (kOf_le _) (h.hyp.near a ha.mem ha.ne_one).1
  solvable_cen := by
    have := (h.hyp.near a ha.mem ha.ne_one).2
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_inf_right _ (kOf_le (θ a)) :
        cenIn (kOf (θ a)) A ≤ θ a ⊓ Subgroup.centralizer (A : Set G)))
  semisimple := isSemisimple_kOf (ha.sol_eq_bot h)
  ne_bot := ha.kOf_ne_bot

theorem NT.normalizes_lcal
    {a : G} (ha : NT A θ a) {x : G} (hx : x ∈ θ a) :
    ∀ J ∈ lcal (θ a), x ∈ Subgroup.normalizer (J : Set G) :=
  mem_normalizer_of_mem_theta h ha.mem ha.ne_one ha.not_solvable hx

theorem NT.exists_conj_A
    {a : G} (ha : NT A θ a) {J J' : Subgroup G} (hJ : J ∈ lcal (θ a))
    (hJ' : J' ∈ lcal (θ a)) : ∃ g ∈ A, J' = J.map (MulAut.conj g).toMonoidHom := by
  have hθ := h.hyp.nearFunctor
  have hcset := h.apply_mem_cset_bot ha.mem ha.ne_one ha.not_solvable
  have hl := ha.lcal_kOf_eq h
  obtain ⟨g, hg, hgJ⟩ := h.exists_conj_eq_of_mem_lcal_kOf hcset (hl ▸ hJ) (hl ▸ hJ')
  have hAD : A ≤ Subgroup.normalizer (dsub A θ : Set G) := admits_dsub hθ
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (dsub A θ) A hAD
  have hg' : g ∈ ((dsub A θ : Set G) * (A : Set G)) := by
    rw [← hmul]
    exact hg
  obtain ⟨d, hd, a', ha', rfl⟩ := hg'
  refine ⟨a', ha', ?_⟩
  rw [hgJ]
  have hJa : J.map (MulAut.conj a').toMonoidHom ∈ lcal (θ a) :=
    map_conj_mem_lcal hJ (h.hyp.isFunctor.normalized a ha.mem ha.ne_one ha')
  have hdN : d ∈ Subgroup.normalizer ((J.map (MulAut.conj a').toMonoidHom : Subgroup G) : Set G) :=
    ha.normalizes_lcal h (dsub_le_apply ha.mem ha.ne_one hd) _ hJa
  rw [← Thm210.map_conj_map_conj, Nonsolv.L69.map_conj_eq_self_iff.mpr hdN]

theorem NT.FN_eq
    {a : G} (ha : NT A θ a) {J : Subgroup G} (hJ : J ∈ lcal (θ a)) :
    FN A θ a = A ⊓ Subgroup.normalizer (J : Set G) := by
  ext x
  rw [mem_FN_iff, Subgroup.mem_inf]
  refine and_congr_right fun hxA => ⟨fun hall => hall J hJ, fun hxJ J' hJ' => ?_⟩
  obtain ⟨g, hgA, rfl⟩ := ha.exists_conj_A h hJ hJ'
  exact Nonsolv.L69.mem_normalizer_map_conj hxJ
    (comm_of_mem_of_isMulCommutative h.hyp.elemAbelian.1 hxA hgA)

theorem NT.mem_centralizer_iff
    {a : G} (ha : NT A θ a) {J J' : Subgroup G} (hJ : J ∈ lcal (θ a))
    (hJ' : J' ∈ lcal (θ a)) {β : G} (hβ : β ∈ A) :
    β ∈ Subgroup.centralizer (J : Set G) ↔ β ∈ Subgroup.centralizer (J' : Set G) := by
  have key : ∀ J J' : Subgroup G, J ∈ lcal (θ a) → J' ∈ lcal (θ a) →
      β ∈ Subgroup.centralizer (J : Set G) → β ∈ Subgroup.centralizer (J' : Set G) := by
    intro J J' hJ hJ' hβJ
    obtain ⟨g, hgA, rfl⟩ := ha.exists_conj_A h hJ hJ'
    exact Nonsolv.L69.mem_centralizer_map_conj hβJ
      (comm_of_mem_of_isMulCommutative h.hyp.elemAbelian.1 hβ hgA)
  exact ⟨key J J' hJ hJ', key J' J hJ' hJ⟩

theorem NT.mem_centralizer_kOf
    {a : G} (ha : NT A θ a) {J : Subgroup G} (hJ : J ∈ lcal (θ a))
    {β : G} (hβ : β ∈ A) (hβJ : β ∈ Subgroup.centralizer (J : Set G)) :
    β ∈ Subgroup.centralizer (kOf (θ a) : Set G) := by
  have hK := (ha.isDirectProduct h).sSup_eq
  have h1 : kOf (θ a) ≤ Subgroup.centralizer ({β} : Set G) := by
    rw [← hK]
    refine sSup_le fun J' hJ' x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp ((ha.mem_centralizer_iff h hJ hJ' hβ).mp hβJ) x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hk)

theorem NT.nearSimple
    {a : G} (ha : NT A θ a) {J : Subgroup G} (hJ : J ∈ lcal (θ a)) :
    NearSimple p ↥J :=
  (ha.semisimpleAction h).nearSimple (ha.lcal_kOf_eq h ▸ hJ)

theorem NT.frame
    {a : G} (ha : NT A θ a) {J : Subgroup G} (hJ : J ∈ lcal (θ a)) :
    ∃ (a₀ : G) (f : MulAut ↥J), a₀ ∈ A ⊓ Subgroup.normalizer (J : Set G) ∧
      (∀ x : ↥J, ((f x : ↥J) : G) = a₀ * x * a₀⁻¹) ∧ orderOf f = p ∧
      (∀ b ∈ A ⊓ Subgroup.normalizer (J : Set G),
        ∃ k : ℕ, ∀ x : ↥J, b * x * b⁻¹ = (((f ^ k) x : ↥J) : G)) ∧
      (signalizerFixedSubgroup f).map J.subtype =
        J ⊓ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) :=
  (ha.semisimpleAction h).exists_frame (ha.lcal_kOf_eq h ▸ hJ)

theorem NT.exists_noncentral
    {a : G} (ha : NT A θ a) {J : Subgroup G} (hJ : J ∈ lcal (θ a)) :
    ∃ g ∈ A ⊓ Subgroup.normalizer (J : Set G), g ∉ Subgroup.centralizer (J : Set G) := by
  obtain ⟨a₀, f, ha₀, hfa, hord, -, -⟩ := ha.frame h hJ
  refine ⟨a₀, ha₀, fun hc => ?_⟩
  have hf1 : f = 1 := by
    ext x
    have h1 := hfa x
    have h2 := Subgroup.mem_centralizer_iff.mp hc (x : G) x.2
    have : a₀ * (x : G) * a₀⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h2.symm
    exact congrArg (fun y : G => y) (h1.trans this)
  rw [hf1, orderOf_one] at hord
  exact h.hyp.prime.ne_one hord.symm

theorem NT.cenIn_singleton_eq
    {a : G} (ha : NT A θ a) {J : Subgroup G} (hJ : J ∈ lcal (θ a))
    {β : G} (hβ : β ∈ A ⊓ Subgroup.normalizer (J : Set G))
    (hβc : β ∉ Subgroup.centralizer (J : Set G)) :
    J ⊓ Subgroup.centralizer ({β} : Set G) =
      J ⊓ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) := by
  obtain ⟨a₀, f, ha₀, hfa, hord, hpow, hfix⟩ := ha.frame h hJ
  have hp := h.hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  ext x
  constructor
  · rintro ⟨hxJ, hxβ⟩
    obtain ⟨k₀, hk₀⟩ := hpow β hβ
    have hk1 : f ^ k₀ ≠ 1 := by
      intro h1
      apply hβc
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hk₀ ⟨y, hy⟩
      rw [h1] at this
      have h3 : β * y * β⁻¹ = y := this
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    have hfixk : (f ^ k₀) ⟨x, hxJ⟩ = ⟨x, hxJ⟩ := by
      apply Subtype.ext
      rw [← hk₀ ⟨x, hxJ⟩]
      have := Subgroup.mem_centralizer_singleton_iff.mp hxβ
      change β * x * β⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have hordk : orderOf (f ^ k₀) = p := by
      refine orderOf_eq_prime ?_ hk1
      rw [← pow_mul, mul_comm, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    have hzle : Subgroup.zpowers (f ^ k₀) ≤ Subgroup.zpowers f :=
      Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers f) k₀)
    have hzeq : Subgroup.zpowers (f ^ k₀) = Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge hzle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hordk, hord])
    have hst : Subgroup.zpowers (f ^ k₀) ≤ MulAction.stabilizer (MulAut ↥J) (⟨x, hxJ⟩ : ↥J) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hfixk)
    have hfst : f ∈ MulAction.stabilizer (MulAut ↥J) (⟨x, hxJ⟩ : ↥J) :=
      hst (hzeq ▸ Subgroup.mem_zpowers f)
    have hfx : f ⟨x, hxJ⟩ = ⟨x, hxJ⟩ := MulAction.mem_stabilizer_iff.mp hfst
    have hmem : x ∈ (signalizerFixedSubgroup f).map J.subtype := ⟨⟨x, hxJ⟩, hfx, rfl⟩
    rw [hfix] at hmem
    exact hmem
  · rintro ⟨hxJ, hxc⟩
    exact ⟨hxJ, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hβ) hxc⟩

theorem NT.isSolvable_cenIn_norIn
    {a : G} (ha : NT A θ a) {J : Subgroup G}
    (hJ : J ∈ lcal (θ a)) :
    Group.IsSolvable ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G)) :=
  (ha.semisimpleAction h).isSolvable_cenIn_norIn (ha.lcal_kOf_eq h ▸ hJ)

theorem NT.not_isMulCommutative_cenIn_norIn
    {a : G} (ha : NT A θ a) {J : Subgroup G}
    (hJ : J ∈ lcal (θ a)) :
    ¬ IsMulCommutative ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G)) := by
  intro hcomm
  obtain ⟨a₀, f, ha₀, hfa, hord, hpow, hfix⟩ := ha.frame h hJ
  obtain ⟨-, ⟨hK0, hKC, -, V, hV0, hVC, -, -, hfr⟩, -⟩ :=
    near_frobenius (ha.nearSimple h hJ) hord
  obtain ⟨⟨k, hkK⟩, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK0
  obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV0
  have hk1' : k ≠ 1 := fun h' => hk1 (Subtype.ext h')
  have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
  have hkmem : ((k : ↥J) : G) ∈ J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) := by
    rw [← hfix]
    exact ⟨k, hKC hkK, rfl⟩
  have hvmem : ((v : ↥J) : G) ∈ J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) := by
    rw [← hfix]
    exact ⟨v, hVC hvV, rfl⟩
  have hc := comm_of_mem_of_isMulCommutative hcomm hvmem hkmem
  have hc' : v * k = k * v := Subtype.ext hc
  exact hk1' (hfr v hvV hv1' k hkK hc')

theorem NT.conj_mem_lcal {a : G} (ha : NT A θ a) {g : G} (hg : g ∈ A) {J : Subgroup G}
    (hJ : J ∈ lcal (θ a)) : J.map (MulAut.conj g).toMonoidHom ∈ lcal (θ a) :=
  _root_.CFSG.SignalizerFunctorTheorem.McBride.map_conj_mem_lcal hJ
    (h.hyp.isFunctor.normalized a ha.mem ha.ne_one hg)

theorem NT.mem_FN_of_isSolvable
    {a x : G} (ha : NT A θ a) (hx : x ∈ A) (hx1 : x ≠ 1)
    (hsolv : Group.IsSolvable (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers x))) :
    x ∈ FN A θ a := by
  have hθ := h.hyp.nearFunctor
  rw [mem_FN_iff]
  refine ⟨hx, fun J hJ => ?_⟩
  by_contra hxJ
  have hL := ha.isDirectProduct h
  have hA' : ∀ g ∈ Subgroup.zpowers x, ∀ J' ∈ lcal (θ a),
      J'.map (MulAut.conj g).toMonoidHom ∈ lcal (θ a) := fun g hg J' hJ' =>
    ha.conj_mem_lcal h (Subgroup.zpowers_le.mpr hx hg) hJ'
  have hproj := projIn_centralizer_eq hL hA' hJ
  have hbot : Subgroup.normalizer (J : Set G) ⊓ Subgroup.zpowers x = ⊥ :=
    CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le h.hyp.prime
      ((zpowers_mem_E1 h hx hx1).2.trans (pow_one p))
      (fun hle => hxJ (hle (Subgroup.mem_zpowers x)))
  have hbot' : Subgroup.zpowers x ⊓ Subgroup.normalizer (J : Set G) = ⊥ := by
    rw [inf_comm]
    exact hbot
  rw [hbot'] at hproj
  have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr fun y hy => by
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
      rw [hy]
      exact one_mem _
  rw [htop, inf_top_eq] at hproj
  have hXsol : Group.IsSolvable ↥(kOf (θ a) ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    have hle : kOf (θ a) ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤
        thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers x) := by
      rw [← hθ.isFunctor.inf_centralizer_eq_thetaOf ha.mem ha.ne_one (Subgroup.zpowers_le.mpr hx)]
      exact inf_le_inf_right _ (kOf_le _)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hsolJ := Thm210.isSolvable_projIn hL hJ inf_le_left hXsol
  rw [hproj] at hsolJ
  exact not_isSolvable_of_mem_lcal hJ hsolJ

theorem NT.isSolvable_of_mem_FN
    {a x : G} (ha : NT A θ a) (hx : x ∈ FN A θ a) {J : Subgroup G}
    (hJ : J ∈ lcal (θ a)) (hxc : x ∉ Subgroup.centralizer (J : Set G)) :
    Group.IsSolvable (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers x)) := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨hxA, hxN⟩ := mem_FN_iff.mp hx
  have hL := ha.isDirectProduct h
  have hA' : ∀ g ∈ Subgroup.zpowers x, ∀ J' ∈ lcal (θ a),
      J'.map (MulAut.conj g).toMonoidHom ∈ lcal (θ a) := fun g hg J' hJ' =>
    ha.conj_mem_lcal h (Subgroup.zpowers_le.mpr hxA hg) hJ'
  have hΓ : thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers x) =
      θ a ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    (hθ.isFunctor.inf_centralizer_eq_thetaOf ha.mem ha.ne_one
      (Subgroup.zpowers_le.mpr hxA)).symm
  have hXsol : Group.IsSolvable ↥(kOf (θ a) ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    refine Thm210.isSolvable_of_forall_projIn hL inf_le_left fun J' hJ' => ?_
    rw [projIn_centralizer_eq hL hA' hJ']
    have h1 : Subgroup.zpowers x ⊓ Subgroup.normalizer (J' : Set G) = Subgroup.zpowers x :=
      inf_eq_left.mpr (Subgroup.zpowers_le.mpr (hxN J' hJ'))
    rw [h1, centralizer_zpowers_eq_singleton, ha.cenIn_singleton_eq h hJ'
      ⟨hxA, hxN J' hJ'⟩ (fun hc => hxc ((ha.mem_centralizer_iff h hJ' hJ hxA).mp hc))]
    exact ha.isSolvable_cenIn_norIn h hJ'
  have hzR := ha.zpowers_mem_rSet h
  obtain ⟨hz1, hzA, hzns⟩ := (h.mem_rSet_iff).mp hzR
  have hsec := h.lemma63a hz1 hzA hzns
  rw [hθ.isFunctor.thetaOf_zpowers ha.mem ha.ne_one] at hsec
  refine isSolvable_of_inf_of_section (K := kOf (θ a)) ?_ (Nonsolv.le_normalizer_kOf (θ a)) hsec ?_
  · rw [hΓ]
    exact inf_le_left
  · have hle : thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers x) ⊓ kOf (θ a) ≤
        kOf (θ a) ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [hΓ]
      intro y hy
      exact ⟨hy.2, hy.1.2⟩
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end NT

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
