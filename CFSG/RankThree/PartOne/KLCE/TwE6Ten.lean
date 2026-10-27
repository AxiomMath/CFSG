module

public import CFSG.RankThree.PartOne.KLCE.TwE6Layer
public import CFSG.RankThree.PartOne.KLC.TwE6
public import CFSG.RankThree.PartOne.S11d.FixedFactsE6TwDescent
public import CFSG.RankThree.PartOne.KLCE.EngineG

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.Chevalley (exhaustionPhi)


section Algebra

theorem exists_nat_powers_of_zpow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a b : G}
    (ha : a ^ p = 1) (hb : b ^ p = 1) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) (h : b = a ^ s) :
    (∃ t : ℕ, b = a ^ t) ∧ ∃ t' : ℕ, a = b ^ t' := by
  have hfa : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, ha⟩
  have hfb : IsOfFinOrder b := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hb⟩
  refine ⟨?_, ?_⟩
  · have hm : a ^ s ∈ Submonoid.powers a :=
      (hfa.mem_powers_iff_mem_zpowers).2 (Subgroup.mem_zpowers_iff.2 ⟨s, rfl⟩)
    obtain ⟨t, ht⟩ := (Submonoid.mem_powers_iff _ _).1 hm
    exact ⟨t, by rw [h, ← ht]⟩
  · have hcop : IsCoprime (p : ℤ) s := by
      have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      exact (Prime.coprime_iff_not_dvd hpi).2 hs
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : a = b ^ v := by
      calc a = a ^ ((p : ℤ) * u + s * v) := by
            rw [mul_comm (p : ℤ) u, mul_comm s v, huv, zpow_one]
        _ = (a ^ (p : ℤ)) ^ u * (a ^ s) ^ v := by
          rw [zpow_add, zpow_mul, zpow_mul]
        _ = b ^ v := by rw [zpow_natCast, ha, one_zpow, one_mul, ← h]
    have hm : b ^ v ∈ Submonoid.powers b :=
      (hfb.mem_powers_iff_mem_zpowers).2 (Subgroup.mem_zpowers_iff.2 ⟨v, rfl⟩)
    obtain ⟨t', ht'⟩ := (Submonoid.mem_powers_iff _ _).1 hm
    exact ⟨t', by rw [h1, ← ht']⟩

end Algebra

section Fields

theorem twE6_nu_eq {p f₀ : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * f₀ * p)) (σ ε : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ (f₀ * p)) (hε : ∀ c, ε c = c ^ 2 ^ (f₀ * (p + 1))) (c : K) :
    ε (σ c) = c ^ 2 ^ f₀ := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (2 * f₀ * p) := by rw [← Nat.card_eq_fintype_card, hK]
  have h1 : c ^ (2 ^ (2 * f₀ * p)) = c := by
    have := FiniteField.pow_card c
    rwa [hcard] at this
  rw [hε, hσ, ← pow_mul, show 2 ^ (f₀ * p) * 2 ^ (f₀ * (p + 1)) =
      2 ^ (2 * f₀ * p) * 2 ^ f₀ by rw [← pow_add, ← pow_add]; congr 1; ring, pow_mul, h1]

theorem eps_fixes_subfield {p f₀ : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {K : Type} [Field K]
    (κ ε : K ≃+* K) (hκ : ∀ c, κ c = c ^ 2 ^ (2 * f₀))
    (hε : ∀ c, ε c = c ^ 2 ^ (f₀ * (p + 1))) (c : K) (hc : c ∈ fixSubfield κ) : ε c = c := by
  have hc' : c ^ 2 ^ (2 * f₀) = c := by rw [← hκ]; exact hc
  obtain ⟨j, hj⟩ := (hp.odd_of_ne_two hp2).add_one
  have key : ∀ j : ℕ, c ^ 2 ^ (2 * f₀ * j) = c := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show 2 * f₀ * (j + 1) = 2 * f₀ * j + 2 * f₀ by ring, pow_add, pow_mul, ih, hc']
  rw [hε, show f₀ * (p + 1) = 2 * f₀ * (j) by rw [hj]; ring]
  exact key j

end Fields

section Iterate

variable {L : Type} [Field L]

theorem twistHom_E6_iterate [CharP L 2] (f₀ : ℕ) {p : ℕ} (hp : Odd p) (h : ModGL TwistTag.E6.tag L) :
    (⇑(twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀)))^[p] h =
      twistHom TwistTag.E6 L (iterateFrobenius L 2 (f₀ * p)) h := by
  obtain ⟨m, rfl⟩ := hp
  exact twistE6_iterate_odd 2 f₀ m h

theorem twistedTorusOf_le_normSeq {τ : Tag} {n₀ : ModGL τ L} {F₀ Φ : ModGL τ L →* ModGL τ L}
    (p : ℕ) (hΦ : ∀ u, Φ u = (⇑F₀)^[p] u) :
    twistedTorusOf n₀ F₀ ≤ twistedTorusOf (normSeq n₀ F₀ p) Φ := by
  intro u hu
  obtain ⟨hH, hfix⟩ := mem_twistedTorusOf.1 hu
  refine mem_twistedTorusOf.2 ⟨hH, ?_⟩
  rw [hΦ]
  exact normSeq_conj_fixed hfix p

theorem e6HRn_mem_adjointGroup : e6HRn L ∈ adjointGroup TwistTag.E6.tag L := by
  obtain ⟨-, -, -, -, -, -, ⟨hn, -, -, -⟩, -⟩ :=
    E6_highest_root_graph_fixed_and_signed_order_five_descent L
  exact monomialSubgroup_le_adjointGroup' hn

end Iterate

section Compat


theorem twE6_actor_compat {p f₀ : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * f₀ * p)) (σ ε : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ (f₀ * p)) (hε : ∀ c, ε c = c ^ 2 ^ (f₀ * (p + 1)))
    {L : Type} [Field L] [Algebra K L] [CharP L 2] (y : twistedE6RootGroup K σ) :
    baseChangeGL (algebraMap K L)
        ((fieldActor σ ε y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀)
        (baseChangeGL (algebraMap K L) (y : ModGL TwistTag.E6.tag K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ν : K →+* K := ε.toRingHom.comp σ.toRingHom with hν
  have hνc : ∀ c, ν c = c ^ 2 ^ f₀ := fun c => twE6_nu_eq hK σ ε hσ hε c
  have hcomm : (algebraMap K L).comp ν = (iterateFrobenius L 2 f₀).comp (algebraMap K L) :=
    RingHom.ext fun c => by
      change algebraMap K L (ν c) = iterateFrobenius L 2 f₀ (algebraMap K L c)
      rw [hνc, iterateFrobenius_def, map_pow]
  rw [twistHom_baseChangeGL (algebraMap K L) hcomm]
  congr 1
  have hy : twistHom TwistTag.E6 K σ.toRingHom (y : ModGL TwistTag.E6.tag K) = y :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ y.2)).2
  have hP : diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K = 1 := diagramMap_E6_mul_self
  have hPi : (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K :=
    inv_eq_of_mul_eq_one_right hP
  have hPe : Units.map (entrywiseHom ε.toRingHom) (diagramMap TwistTag.E6 K) =
      diagramMap TwistTag.E6 K := units_map_entrywiseHom_diagramMap ε.toRingHom
  rw [twistHom_apply, hPi] at hy
  rw [twistHom_apply, hPi, coe_fieldActor, hν, ← units_map_entrywiseHom_comp]
  have hσy : Units.map (entrywiseHom σ.toRingHom) (y : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * y * diagramMap TwistTag.E6 K := by
    calc _ = diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K *
          Units.map (entrywiseHom σ.toRingHom) (y : ModGL TwistTag.E6.tag K) *
          diagramMap TwistTag.E6 K) * diagramMap TwistTag.E6 K := by
            rw [← mul_assoc, ← mul_assoc, hP, one_mul, mul_assoc, hP, mul_one]
      _ = _ := by rw [hy]
  rw [hσy, map_mul, map_mul, hPe]
  symm
  calc diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom ε.toRingHom) (y : ModGL TwistTag.E6.tag K) *
        diagramMap TwistTag.E6 K) * diagramMap TwistTag.E6 K
      = (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K) *
        Units.map (entrywiseHom ε.toRingHom) (y : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K) := by group
    _ = _ := by rw [hP, one_mul, mul_one]

end Compat

section Conjugacy


theorem twE6_conj_data {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hf₀ : 1 ≤ f₀)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 10).eval (((2 ^ f₀ : ℕ)) : ℤ))
    {K : Type} [Field K] [Finite K] (σ κ ε : K ≃+* K)
    (σ₀ : fixSubfield κ ≃+* fixSubfield κ)
    (hκ : ∀ c, κ c = c ^ 2 ^ (2 * f₀)) (hε : ∀ c, ε c = c ^ 2 ^ (f₀ * (p + 1)))
    (hσ₀ : ∀ c : fixSubfield κ, (σ₀ c : K) = (c : K) ^ 2 ^ f₀)
    (hcard : Nat.card (fixSubfield κ) = 2 ^ (2 * f₀))
    (hJC : subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]
    (y : twistedE6RootGroup K σ) (hyp : orderOf y = p)
    (hyJ : (y : ModGL TwistTag.E6.tag K) ∈
      subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) :
    7 < p ∧ ¬ p ∣ Nat.card (WeylGroup TwistTag.E6.tag) ∧
    (∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ subtorusA1 (e6HRn L)
        (twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀)) e6O5Theta →
      orderOf (rootDiagUnit TwistTag.E6.tag b) = p →
      rootCharKernel b ⊆ {e6O5Theta, -e6O5Theta}) ∧
    ∃ g₀ : ModGL TwistTag.E6.tag L, g₀ ∈ adjointGroup TwistTag.E6.tag L ∧
      twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀) g₀ = g₀ * e6HRn L ∧
      ∃ c : twistedE6RootGroup K σ, fieldActor σ ε c = c ∧
        g₀⁻¹ * ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype)
          (c * y * c⁻¹) * g₀ ∈
          subtorusA1 (e6HRn L) (twistHom TwistTag.E6 L (iterateFrobenius L 2 f₀)) e6O5Theta := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have : CharP (fixSubfield κ) 2 := ⟨fun x => by
    rw [← (algebraMap (fixSubfield κ) L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  obtain ⟨_, hst, hac⟩ := exists_tower_algebra (K₀ := fixSubfield κ) (K := K) (L := L)
  have hK₀card : Nat.card (fixSubfield κ) = (2 ^ f₀) ^ 2 := by rw [hcard, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ (2 ^ f₀) := fun c => Subtype.ext (by
    rw [hσ₀, SubmonoidClass.coe_pow])
  obtain ⟨hp7, hordW, hkerZ, hconjall⟩ := twE6_frame (ℓ := 2) hf₀ (fixSubfield κ) hK₀card σ₀ hσ₀' L
    hp hp5 hpf
  refine ⟨hp7, hordW, hkerZ, ?_⟩
  obtain ⟨g₀, hg₀C, hg₀⟩ := KE.lang_conjugator_twisted_gen (fixSubfield κ) (ℓ := 2) (f := f₀) hf₀ L
    (e6HRn L) e6HRn_mem_adjointGroup
  refine ⟨g₀, hg₀C, hg₀, ?_⟩
  obtain ⟨y₀, hy₀, hy₀y⟩ := Subgroup.mem_map.1 hyJ
  let μ : twistedE6RootGroup (fixSubfield κ) σ₀ →* twistedE6RootGroup K σ :=
    ((baseChangeGL (fixSubfield κ).subtype).comp
      (twistedE6RootGroup (fixSubfield κ) σ₀).subtype).codRestrict (twistedE6RootGroup K σ)
      (fun z => hJC (Subgroup.mem_map_of_mem _ z.2))
  have hμ : ∀ z, ((μ z : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (fixSubfield κ).subtype (z : ModGL TwistTag.E6.tag (fixSubfield κ)) :=
    fun z => rfl
  have hμinj : Function.Injective μ := fun a b h => Subtype.ext (baseChangeGL_injective _
    (by rw [← hμ, ← hμ, h]))
  let y₀' : twistedE6RootGroup (fixSubfield κ) σ₀ := ⟨y₀, hy₀⟩
  have hμy : μ y₀' = y := Subtype.ext (by rw [hμ]; exact hy₀y)
  have hy₀ord : orderOf y₀' = p := by
    rw [← orderOf_injective μ hμinj y₀', hμy, hyp]
  obtain ⟨c₀, hc₀⟩ := hconjall g₀ hg₀C hg₀ y₀' hy₀ord
  rw [mem_subtorusImage_iff] at hc₀
  have hιμ : ∀ z : twistedE6RootGroup (fixSubfield κ) σ₀,
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) (μ z) =
      ((baseChangeGL (algebraMap (fixSubfield κ) L)).comp
        (twistedE6RootGroup (fixSubfield κ) σ₀).subtype) z := fun z => by
    change baseChangeGL (algebraMap K L) ((μ z : twistedE6RootGroup K σ) :
      ModGL TwistTag.E6.tag K) = _
    rw [hμ]
    have hcomp : (algebraMap K L).comp (fixSubfield κ).subtype =
        algebraMap (fixSubfield κ) L := (IsScalarTower.algebraMap_eq (fixSubfield κ) K L).symm
    rw [baseChangeGL_baseChangeGL, hcomp]
    rfl
  refine ⟨μ c₀, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_fieldActor, hμ]
    change baseChangeGL ε.toRingHom (baseChangeGL (fixSubfield κ).subtype _) = _
    rw [baseChangeGL_baseChangeGL]
    congr 2
    exact RingHom.ext fun a => eps_fixes_subfield hp2 hp κ ε hκ hε a a.2
  · have : μ c₀ * y * (μ c₀)⁻¹ = μ (c₀ * y₀' * c₀⁻¹) := by
      rw [map_mul, map_mul, map_inv, hμy]
    rw [this, hιμ]
    exact hc₀

end Conjugacy

section Layer


theorem twE6_layerData {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hf₀ : 1 ≤ f₀)
    (hpΦ : (p : ℤ) ∣ (exhaustionPhi 10).eval ((2 : ℤ) ^ (p * f₀)))
    {K : Type} [Field K] [Finite K] (σ κ ε : K ≃+* K) (σ₀ : fixSubfield κ ≃+* fixSubfield κ)
    (hK : Nat.card K = 2 ^ (2 * f₀ * p)) (hσ : ∀ c, σ c = c ^ 2 ^ (f₀ * p))
    (hκ : ∀ c, κ c = c ^ 2 ^ (2 * f₀)) (hε : ∀ c, ε c = c ^ 2 ^ (f₀ * (p + 1)))
    (hσ₀ : ∀ c : fixSubfield κ, (σ₀ c : K) = (c : K) ^ 2 ^ f₀)
    (hcard : Nat.card (fixSubfield κ) = 2 ^ (2 * f₀))
    (hJC : subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hεord : orderOf (fieldActor (t := TwistTag.E6) σ ε) = p)
    (hpr : CFSG.pRank p (twistedE6RootGroup K σ) = 1)
    (y : twistedE6RootGroup K σ) (hyp : orderOf y = p)
    (hyJ : (y : ModGL TwistTag.E6.tag K) ∈
      subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) :
    KLC.LieLayerData p (fieldActor σ ε)
      (Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpf : 1 ≤ f₀ * p := Nat.mul_pos hf₀ hp.pos
  have hpf2 : 1 ≤ 2 * f₀ * p := Nat.mul_pos (by omega) hp.pos
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf2
      hK
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  set F₀ := twistHom TwistTag.E6 L Φ₀ with hF₀def
  set n₀ := e6HRn L with hn₀def
  set N := normSeq n₀ F₀ p with hNdef
  have hpf₀ : (p : ℤ) ∣ (exhaustionPhi 10).eval (((2 ^ f₀ : ℕ)) : ℤ) := by
    refine dvd_eval_of_dvd_eval_pow hp (exhaustionPhi 10) ?_
    have : (((2 ^ f₀ : ℕ) : ℤ)) ^ p = (2 : ℤ) ^ (p * f₀) := by
      push_cast
      rw [← pow_mul, mul_comm]
    rw [this]
    exact hpΦ
  obtain ⟨hp7, hordW, hkerZ, g₀, hg₀C, hg₀F, c, hcα, hc'⟩ :=
    twE6_conj_data hp hp5 hf₀ hpf₀ σ κ ε σ₀ hκ hε hσ₀ hcard hJC (L := L) y hyp hyJ
  have hι : Function.Injective
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hyΓ : ∀ z : twistedE6RootGroup K σ,
      (z : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    fun z => graphFixedRootGroup_le _ _ _ z.2
  have hιC : ∀ z, ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) z ∈
      adjointGroup TwistTag.E6.tag L := fun z =>
    baseChangeGL_mem_adjointGroup _ ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ z)).1
  have hα₀ : ∀ z, ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype)
      (fieldActor σ ε z) =
      F₀ (((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) z) :=
    fun z => twE6_actor_compat hK σ ε hσ hε z
  have hα₀p : fieldActor (t := TwistTag.E6) σ ε ^ p = 1 := by
    rw [← hεord]
    exact pow_orderOf_eq_one _
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun a => by
      change algebraMap K L (σ a) = Fr (algebraMap K L a)
      rw [hσ, hFrdef, iterateFrobenius_def, map_pow]
  have hιΦ : ∀ z, twistHom TwistTag.E6 L Fr
      (((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) z) =
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) z := fun z => by
    change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L)
      (z : ModGL TwistTag.E6.tag K)) = baseChangeGL (algebraMap K L) (z : ModGL TwistTag.E6.tag K)
    rw [twistHom_baseChangeGL (algebraMap K L) hcomm,
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ z)).2]
  have hodd : ∀ h ∈ torusGroup TwistTag.E6.tag L, ∃ m : ℕ, Odd m ∧ h ^ m = 1 := fun h hh =>
    exists_odd_pow_eq_one_of_mem_torusGroup (K := K) hh
  have hΦit : ∀ u, twistHom TwistTag.E6 L Fr u = (⇑F₀)^[p] u := fun u =>
    (twistHom_E6_iterate f₀ hpodd u).symm
  have hg₀ : twistHom TwistTag.E6 L Fr g₀ = g₀ * N := by
    rw [hΦit, iterate_lang_normSeq hg₀F]
  have hK2 : Nat.card K = (2 ^ (f₀ * p)) ^ 2 := by
    rw [hK, ← pow_mul]
    congr 1
    ring
  obtain ⟨k, hrat, -⟩ := twE6_rational (ℓ := 2) hpf K hK2 σ hσ L
  have hperf : ∀ Y : Subgroup (ModGL TwistTag.E6.tag L), Finite Y →
      Y ≤ adjointGroup TwistTag.E6.tag L → (∀ u ∈ Y, twistHom TwistTag.E6 L Fr u = u) →
      ⁅Y, Y⁆ = Y →
      Y ≤ ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range :=
    fun Y hY hYC hYF hYp => (hrat Y hYC hYF).2.2 Y le_rfl hYp
  have hstab : ∀ a : Fin TwistTag.E6.tag.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit TwistTag.E6.tag a ∈ twistedTorusOf N (twistHom TwistTag.E6 L Fr) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup TwistTag.E6.tag)) :=
    fun a hap ha1 _ => rootCharStabilizer_subset_closure hp hordW hap ha1
  obtain ⟨kk, _, _, _, hkk⟩ := exists_finite_field_into 2 (f₀ * p) hpf L
  obtain ⟨P, hfam, hjoin, hLD⟩ := twE6_layer_family (L := L) hp hp5 hf₀ kk hkk
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hθ : IsRoot TwistTag.E6.tag e6O5Theta :=
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
  have hS : ∀ α ∈ ({e6O5Theta, -e6O5Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hθ, IsRoot.neg hθ]
  have hSn : ∀ α ∈ ({e6O5Theta, -e6O5Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      -α ∈ ({e6O5Theta, -e6O5Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) := by
    intro α hα
    rcases hα with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  have hZle : subtorusA1 n₀ F₀ e6O5Theta ≤
      subtorusSigma N (twistHom TwistTag.E6 L Fr) {e6O5Theta, -e6O5Theta} := by
    intro z hz
    refine ⟨twistedTorusOf_le_normSeq p hΦit hz.1, ?_⟩
    have h2 : rootSpan TwistTag.E6.tag L
        ({e6O5Theta, -e6O5Theta} : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
        (rootSL2 TwistTag.E6.tag L e6O5Theta).range := rootSpan_pm_eq_range hθ
    rw [h2]
    exact hz.2
  have hcI : c * y * c⁻¹ ∈ subtorusImage
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) g₀
      (subtorusSigma N (twistHom TwistTag.E6 L Fr) {e6O5Theta, -e6O5Theta}) :=
    (mem_subtorusImage_iff _ _ _ _).2 (hZle hc')
  have hker : ∀ a : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag a = g₀⁻¹ *
        ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype)
          (c * y * c⁻¹) * g₀ → rootCharKernel a ⊆ {e6O5Theta, -e6O5Theta} := by
    intro a ha
    have hord' : orderOf (rootDiagUnit TwistTag.E6.tag a) = p := by
      rw [ha, ← psiG_apply, orderOf_injective _ (psiG_injective hι g₀ c) y, hyp]
    exact hkerZ a (ha ▸ hc') hord'
  exact lieLayerData_of_descent
    ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) hι hιC F₀
    (twistHom TwistTag.E6 L Fr) (fieldActor σ ε) hα₀ hp hα₀p hιΦ hodd n₀ N g₀ hg₀C hg₀F hg₀
    hperf hstab hS hSn P ⟨()⟩ hPfin hPq hPQ hPR hPadj hPnorm hPcent hjoin
    (fun i j hij => absurd (Subsingleton.elim i j) hij) (fun _ => hLD) hyp hpr c hcα
    hcI hker

end Layer

section Main


theorem twistedE6TenLayer : KLC.TwistedE6TenLayer := by
  intro T _ _ p hp hp5 hLR hpr f₀ hf₀ hM α hαp hαinn hLRA hX hpΦ x hxp hx1 hαx
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, σ, κ, ε, σ₀, φ, hK, hσ, hκ, hε, hσ₀, ⟨s, hs, hcongr⟩, hfix, hcanon, hPq, -,
    -⟩ := FieldFix.twistedE6_descent hp (by omega) hf₀ hM α hαp hαinn
  obtain ⟨-, hcard, hJC, hεord, -⟩ := hcanon
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set y : twistedE6RootGroup K σ := φ x with hy
  have hyord : orderOf y = p := by
    rw [hy, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hxp hx1
  have hβy : MulAut.congr φ α y = y := by
    rw [hy, MulAut.congr_apply]
    simp [hαx]
  have hα₁y : MulAut.congr φ α y = y → fieldActor (t := TwistTag.E6) σ ε y = y := fun h => by
    rw [← Sec66T.mem_fixSub, ← hfix]
    exact Sec66T.mem_fixSub.2 h
  have hyJ := hPq p hp (by omega) y (Sec66T.mem_fixSub.2 (hα₁y hβy)) ⟨1, by rw [pow_one]; exact hyord⟩
  have hprK : CFSG.pRank p (twistedE6RootGroup K σ) = 1 := by
    rw [← KLC.pRank_congr_mulEquiv φ hp.one_lt]
    exact hpr
  have hLL := twE6_layerData hp hp5 hf₀ hpΦ σ κ ε σ₀ hK hσ hκ hε hσ₀ hcard hJC hεord hprK y hyord
    hyJ
  have hβp : MulAut.congr φ α ^ p = 1 := by
    rw [← map_pow, hαp, map_one]
  have hα₁p : fieldActor (t := TwistTag.E6) σ ε ^ p = 1 := by
    rw [← hεord]
    exact pow_orderOf_eq_one _
  obtain ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩ := exists_nat_powers_of_zpow hp hα₁p hβp hs hcongr
  exact KLC.LieLayerData.conclusion_of_mulEquiv φ α x (lieLayerData_of_power ⟨t, ht⟩ ⟨t', ht'⟩ hLL)

end Main

end CFSG.RankThree.PartOne.KLCE
