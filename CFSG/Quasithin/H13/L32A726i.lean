module

public import CFSG.Quasithin.H13.L32A726h
public import CFSG.Quasithin.H13.L32A726Q
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_726 {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem isQuasisimple_of_isSimpleGroup_726 {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsQuasisimple Q := by
  have hZ := center_eq_bot_726 hnab
  have hperf : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · obtain ⟨a, b, hab⟩ := hnab
      have hab' := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab'
      exact absurd hab' hab
    · exact h
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨hperf⟩, (MulEquiv.isSimpleGroup_congr e).mpr inferInstance, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩

omit [Finite G] in
theorem pCoreOf_subgroupOf_726 (X : Subgroup G) :
    (pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X := CFSG.openPCoreOf_subgroupOf 2 X

omit [Finite G] in
theorem mem_pCoreOf_of_mem_726 {X : Subgroup G} {g : ↥X} (h : g ∈ CFSG.pCore 2 ↥X) :
    (g : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff g).mpr h

theorem isSimpleGroup_quot_726 {G0 L0 : Subgroup G} (hodd : OddCoreModTwoTrivial G0)
    (hL0 : L0 ∈ cComp G0) :
    IsSimpleGroup (↥L0 ⧸ CFSG.pCore 2 ↥L0) ∧
      ∃ a b : ↥L0 ⧸ CFSG.pCore 2 ↥L0, a * b ≠ b * a := by
  obtain ⟨-, ⟨hs, a, b, hab⟩, -⟩ := cComp_structure hL0
  have h : (solvRad L0).subgroupOf L0 = CFSG.pCore 2 ↥L0 := by
    rw [solvRad_eq_pCoreOf_of_mem_cComp hodd hL0, pCoreOf_subgroupOf_726]
  let e := QuotientGroup.quotientMulEquivOfEq h
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mp hs, e a, e b, fun h' => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h']

section Action

variable {A : Type*} [Group A]

@[expose] noncomputable def autQuot_726 (N : Subgroup A) [hN : N.Characteristic] :
    MulAut A →* MulAut (A ⧸ N) where
  toFun α := QuotientGroup.congr N N α (Subgroup.characteristic_iff_map_eq.1 hN α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

end Action

@[expose] noncomputable def actQuot_726 {G0 L0 : Subgroup G}
    (hn : G0 ≤ Subgroup.normalizer (L0 : Set G)) :
    ↥G0 →* MulAut (↥L0 ⧸ CFSG.pCore 2 ↥L0) :=
  (autQuot_726 (CFSG.pCore 2 ↥L0)).comp
    ((Subgroup.normalizerMonoidHom L0).comp (Subgroup.inclusion hn))

omit [Finite G] in
theorem actQuot_mk_726 {G0 L0 : Subgroup G} (hn : G0 ≤ Subgroup.normalizer (L0 : Set G))
    (g : ↥G0) (ℓ : ↥L0) :
    actQuot_726 hn g (ℓ : ↥L0 ⧸ CFSG.pCore 2 ↥L0) =
      ((⟨(g : G) * ℓ * (g : G)⁻¹, (hn g.2 ℓ).mp ℓ.2⟩ : ↥L0) : ↥L0 ⧸ CFSG.pCore 2 ↥L0) := rfl

omit [Finite G] in
theorem actQuot_of_mem_726 {G0 L0 : Subgroup G} (hn : G0 ≤ Subgroup.normalizer (L0 : Set G))
    {g : ↥G0} (hg : (g : G) ∈ L0) :
    actQuot_726 hn g =
      MulAut.conj ((⟨(g : G), hg⟩ : ↥L0) : ↥L0 ⧸ CFSG.pCore 2 ↥L0) := by
  ext q
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [actQuot_mk_726, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  rfl

omit [Finite G] in
theorem actQuot_ne_one_726 {G0 L0 : Subgroup G} (hn : G0 ≤ Subgroup.normalizer (L0 : Set G))
    (hZ : Subgroup.center (↥L0 ⧸ CFSG.pCore 2 ↥L0) = ⊥) {g : ↥G0} (hg : (g : G) ∈ L0)
    (hg2 : (g : G) ∉ pCoreOf 2 L0) : actQuot_726 hn g ≠ 1 := by
  intro h1
  rw [actQuot_of_mem_726 hn hg] at h1
  set q₀ : ↥L0 ⧸ CFSG.pCore 2 ↥L0 := ((⟨(g : G), hg⟩ : ↥L0) : ↥L0 ⧸ CFSG.pCore 2 ↥L0)
    with hq₀
  have hc : q₀ ∈ Subgroup.center (↥L0 ⧸ CFSG.pCore 2 ↥L0) := by
    rw [Subgroup.mem_center_iff]
    intro q
    have h2 := congrArg (fun φ : MulAut (↥L0 ⧸ CFSG.pCore 2 ↥L0) => φ q) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc q * q₀ = q₀ * q * q₀⁻¹ * q₀ := by rw [h2]
      _ = q₀ * q := by group
  rw [hZ, Subgroup.mem_bot, hq₀, QuotientGroup.eq_one_iff] at hc
  exact hg2 (mem_pCoreOf_of_mem_726 hc)

omit [Finite G] in
theorem not_two_dvd_index_range_726 {G0 Hd S : Subgroup G} (hS : IsSylowTwoOf S G0)
    (hSHd : S ≤ Hd) (hHdG0 : Hd ≤ G0) {A₀ : Type*} [Group A₀] (φ : ↥G0 →* A₀) :
    ¬ 2 ∣ ((φ.comp (Subgroup.inclusion hHdG0)).range.subgroupOf φ.range).index := by
  have hodd2 : ¬ 2 ∣ (Hd.subgroupOf G0).index := fun h2 => hS.2.2 (h2.trans
    (Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ _ G0 hSHd hHdG0)))
  have heq : (φ.comp (Subgroup.inclusion hHdG0)).range.subgroupOf φ.range =
      (Hd.subgroupOf G0).map φ.rangeRestrict := by
    ext ⟨a, ha⟩
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨Subgroup.inclusion hHdG0 h, h.2, Subtype.ext hh⟩
    · rintro ⟨g, hg, hga⟩
      exact ⟨⟨g, hg⟩, congrArg Subtype.val hga⟩
  rw [heq]
  exact fun h2 => hodd2 (h2.trans (Subgroup.index_map_dvd _ φ.rangeRestrict_surjective))

omit [Finite G] in
theorem orderOf_map_eq_three_726 {X : Subgroup G} {x : G} (hx3 : orderOf x = 3) (hxX : x ∈ X)
    {A₀ : Type*} [Group A₀] (ψ : ↥X →* A₀) (hne : ψ ⟨x, hxX⟩ ≠ 1) :
    orderOf (ψ ⟨x, hxX⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ hne
  have hx3' : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hpow : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hx3')
  rw [← map_pow, hpow, map_one]

section Ctx

variable {T L V H D : Subgroup G}

theorem false_of_charTwo_726 (hC129 : ASC129Statement G) (h121 : Id2519.Prop121Three)
    (hC27 : KG14726C27C) (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t)
    {G0 : Subgroup G} (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) (hG0H : ¬ G0 ≤ H)
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) (hchar : CharTwo G0) :
    False := by
  obtain ⟨x, Y, E₁, E₂, hX⟩ := exists_xData_726 hc
  obtain ⟨hodd, L₀, hL₀, hxL₀, hn⟩ :=
    exists_cComp_726 hC129 h121 hc hdD hdV hd2 htT htd hHdG0 hG0 hG0H hQ hchar hX
  obtain ⟨hs, hnab⟩ := isSimpleGroup_quot_726 hodd hL₀
  have := hs
  have hL₀G0 := le_of_mem_cComp hL₀
  have hxHd : x ∈ H ⊓ Subgroup.centralizer ({d} : Set G) :=
    k_le_hd_726 hc hdD (l1_le_k_726 hc hX.x_mem)
  set φ := actQuot_726 hn with hφ
  set ψ : ↥(H ⊓ Subgroup.centralizer ({d} : Set G)) →* MulAut (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) :=
    φ.comp (Subgroup.inclusion hHdG0) with hψ
  have hψx : ∀ hx : x ∈ H ⊓ Subgroup.centralizer ({d} : Set G), ψ ⟨x, hx⟩ ≠ 1 := fun hx' =>
    actQuot_ne_one_726 hn (center_eq_bot_726 hnab) (g := ⟨x, hHdG0 hx'⟩) hxL₀
      (not_mem_pCoreOf_726 hX.x_order)
  have hInn : (MulAut.conj : (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) →*
      MulAut (↥L₀ ⧸ CFSG.pCore 2 ↥L₀)).range ≤ φ.range := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨ℓ, hL₀G0 ℓ.2⟩, actQuot_of_mem_726 hn (g := ⟨ℓ, hL₀G0 ℓ.2⟩) ℓ.2⟩
  have hBA : ψ.range ≤ φ.range := by
    rintro _ ⟨h, rfl⟩
    exact ⟨_, rfl⟩
  have hBAidx : ¬ 2 ∣ (ψ.range.subgroupOf φ.range).index :=
    not_two_dvd_index_range_726 (isSylowTwoOf_td_g0_726 hc hdD hdV htT htd hHdG0 hG0)
      (td_le_hd_726 hc d) hHdG0 φ
  have hxInn : ψ ⟨x, hxHd⟩ ∈ (MulAut.conj : (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) →*
      MulAut (↥L₀ ⧸ CFSG.pCore 2 ↥L₀)).range :=
    ⟨_, (actQuot_of_mem_726 hn (g := ⟨x, hHdG0 hxHd⟩) hxL₀).symm⟩
  have hx3 : orderOf (ψ ⟨x, hxHd⟩) = 3 := orderOf_map_eq_three_726 hX.x_order hxHd ψ (hψx hxHd)
  have hF4 : ∀ k : ↥L₀, (k : G) ∈ H ⊓ Subgroup.centralizer ({d} : Set G) →
      MulAut.conj (QuotientGroup.mk k : ↥L₀ ⧸ CFSG.pCore 2 ↥L₀) ∈ ψ.range := fun k hk =>
    ⟨⟨k, hk⟩, actQuot_of_mem_726 hn (g := ⟨k, hHdG0 hk⟩) k.2⟩
  exact hC27 G G0 (pCoreOf 2 H) (H ⊓ Subgroup.centralizer ({d} : Set G)) L₀
    (hypC23_726 hc hdD hdV hd2 hHdG0 hG0 hQ) hL₀ (isQuasisimple_of_isSimpleGroup_726 hnab)
    (CharTwo.of_normal hchar hL₀G0
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hL₀G0).mpr hn))
    (fun h => not_le_h_of_mem_cComp_726 hc hL₀ (h.trans inf_le_left))
    (((hQ.trans (td_le_hd_726 hc d)).trans hHdG0).trans hn)
    φ.range hInn ψ.range hBA hBAidx (card_range_726 hc hdD hX rfl ψ hψx)
    ⟨ψ ⟨x, hxHd⟩, hxInn, hx3, ⟨⟨x, hxHd⟩, rfl⟩,
      range_le_normalizer_726 hc hdD hdV hQ hX rfl ψ hψx hxHd⟩
    hF4 (isPOnePlusTwo_range_726 hc hdD hX rfl ψ hψx)

end Ctx

end CFSG.Quasithin.H13.L32A
