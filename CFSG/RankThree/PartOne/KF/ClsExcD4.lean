module

public import CFSG.RankThree.PartOne.KF.ClsExcRank
public import CFSG.RankThree.PartOne.KF.ClsFixedLevi
public import CFSG.RankThree.PartOne.KF.ClsD4Torus
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizesFixed
public import CFSG.LieType.BorelTits.Twisted
public import CFSG.Quasithin.Vol2.F134LieD4Cells

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.Quasithin.SteinbergCD CFSG.Quasithin.F134.LieD4
open CFSG.Assembly.RankThreeEven (localRank)

section Arithmetic

theorem cube_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Nat.sub_eq_of_eq_add (by ring)

theorem cube_add_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 + 1 = (q ^ 2 + q + 1) * (q - 1) + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem not_dvd_one_add_pow {p q d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (h3 : p ∣ q ^ 2 + q + 1) (hd : d = 1 ∨ d = 3) : ¬ p ∣ 1 + q ^ d := by
  intro h
  rcases hd with rfl | rfl
  · have h1 : p ∣ (q ^ 2 + q + 1) - q * (1 + q ^ 1) := by
      exact Nat.dvd_sub h3 (dvd_mul_of_dvd_right h q)
    have : (q ^ 2 + q + 1) - q * (1 + q ^ 1) = 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      have : (m + 1) * (1 + (m + 1) ^ 1) = (m + 1) ^ 2 + (m + 1) := by ring
      omega
    rw [this] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  · have h1 : p ∣ q ^ 3 + 1 := by rwa [add_comm]
    rw [cube_add_one q hq] at h1
    have h2 : p ∣ 2 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h3 _)).1 h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem odd_card_sub_one_of_card_eq {K : Type} {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) : Odd (Nat.card K - 1) := by
  rw [hK, ← pow_mul]
  exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one

end Arithmetic

section Group

theorem exists_conj_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B E : Subgroup G} (hE : IsPGroup p E) (hB : ¬ p ∣ B.index) :
    ∃ g : G, ∀ e ∈ E, g⁻¹ * e * g ∈ B := by
  classical
  let _ : MulAction E (G ⧸ B) := MulAction.compHom _ E.subtype
  have hmod := hE.card_modEq_card_fixedPoints (G ⧸ B)
  have hne : Nat.card (MulAction.fixedPoints E (G ⧸ B)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hB ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, fun e he => ?_⟩
  have h1 := (MulAction.mem_fixedPoints.1 hx) ⟨e⁻¹, E.inv_mem he⟩
  have h2 : ((e⁻¹ * g : G) : G ⧸ B) = (g : G ⧸ B) := h1
  have h3 := QuotientGroup.eq.1 h2
  simpa [mul_assoc] using h3

end Group

section Main

theorem not_dvd_card_graphFixedRootTorus_D4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ n - 1) (h3 : ¬ p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    ¬ p ∣ Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hq : 0 < 2 ^ n := by positivity
  have hodd := odd_card_sub_one_of_card_eq hn hK
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    rw [hK, cube_sub_one _ Nat.one_le_two_pow]
    exact fun h => (hp.dvd_mul.1 h).elim hpq h3
  set x' : ModGL TwistTag.D4.tag K := (x : ModGL TwistTag.D4.tag K) with hx'
  have hxp : x' ^ p = 1 := by
    have : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    exact congrArg Subtype.val this
  have hPle : Subgroup.zpowers x' ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    (Subgroup.zpowers_le).2 x.2
  have hPexp : ∀ y ∈ Subgroup.zpowers x', y ^ p = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  obtain ⟨g, hginj, hgp⟩ := exists_injective_of_le_graphFixedRootTorus_D4 σ.toRingHom
    σ.surjective hq (fun c => hσc c) hodd hp hpq hPle hPexp
  have hx1 : x' = 1 := by
    have h1 : g ⟨x', Subgroup.mem_zpowers x'⟩ = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd hp hpK (hgp _)
    exact congrArg Subtype.val (hginj (h1.trans (map_one g).symm))
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  exact hp.one_lt.ne hx

theorem no_plane_D4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n))
    (hH : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ n - 1)
    {U E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hEp : ∀ g ∈ E, g ^ p = 1) (hEc : Nat.card E = p ^ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK3
  have hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hq : 0 < 2 ^ n := by positivity
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd := odd_card_sub_one_of_card_eq hn hK
  obtain ⟨J, φ, hJ, hφ, hmem⟩ :=
    exists_hom_into_graphFixedParabolic_of_normalizes TwistTag.D4 σ hH hU hU2 hE
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hex : ∀ i : Fin TwistTag.D4.foldedTag.rank, ∃ j : Fin TwistTag.D4.foldedTag.rank,
      ∀ k, k ≠ i → k = j := by decide
  obtain ⟨a, ha⟩ := hex i
  have hsub : J ⊆ {a} := fun k hk => ha k (fun h => hi (h ▸ hk))
  have hle : graphFixedParabolic TwistTag.D4 K σ.toRingHom J ≤
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
    ((fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 J {a}).2 hsub
  have hEφle : φ.range ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
    rintro _ ⟨e, rfl⟩
    exact hle (hmem e)
  have hEp' : ∀ e : E, e ^ p = 1 := fun e => Subtype.ext (hEp e e.2)
  have hEpg : IsPGroup p E := IsPGroup.of_card hEc
  have hEφp : IsPGroup p φ.range :=
    hEpg.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  by_cases h3 : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1
  ·
    have hrel : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) =
        1 + (2 ^ n) ^ (TwistTag.D4.orbit a).card := by
      have h3' := Subgroup.relIndex_mul_card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
      rw [inf_eq_left.2 (graphFixedRootBorel_le_graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}),
        card_graphFixedParabolic_singleton hσ a,
        card_graphFixedInversionUnipotent_D4 σ hn hK hσc a] at h3'
      have hB0 : 0 < Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hB0 (by rw [h3', mul_comm])
    have hd : (TwistTag.D4.orbit a).card = 1 ∨ (TwistTag.D4.orbit a).card = 3 := by
      have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
          (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
      exact this a
    have hidx : ¬ p ∣ ((graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})).index := by
      change ¬ p ∣ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
      rw [hrel]
      exact not_dvd_one_add_pow hp hp2 hq1 h3 hd
    obtain ⟨g, hg⟩ := exists_conj_le_of_not_dvd_index (p := p)
      (G := graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
      (B := (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}))
      (E := φ.range.subgroupOf (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}))
      (hEφp.of_equiv (Subgroup.subgroupOfEquivOfLe hEφle).symm) hidx
    set ψ : E →* ModGL TwistTag.D4.tag K :=
      (MulAut.conj (g : ModGL TwistTag.D4.tag K)⁻¹).toMonoidHom.comp φ with hψ
    have hψinj : Function.Injective ψ := (MulAut.conj _).injective.comp hφ
    have hψB : ∀ e, ψ e ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := fun e => by
      have h1 : (⟨φ e, hEφle ⟨e, rfl⟩⟩ : graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) ∈
          φ.range.subgroupOf (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := ⟨e, rfl⟩
      have h2 : (g : ModGL TwistTag.D4.tag K)⁻¹ * φ e * g ∈
          graphFixedRootBorel TwistTag.D4 K σ.toRingHom := hg _ h1
      have h3 : ψ e = (g : ModGL TwistTag.D4.tag K)⁻¹ * φ e * g := by
        show (MulAut.conj (g : ModGL TwistTag.D4.tag K)⁻¹) (φ e) = _
        rw [MulAut.conj_apply, inv_inv]
      rw [h3]
      exact h2
    have hBle : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊔
          graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
      intro b hb
      have hb' : b ∈ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom :
          Set (ModGL TwistTag.D4.tag K)) := hb
      rw [graphFixedRootBorel_eq_mul hσ] at hb'
      obtain ⟨h, hh, u, hu, rfl⟩ := hb'
      exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu)
    have hE₁p : IsPGroup p ψ.range := hEpg.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hU2' : IsPGroup 2 (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
      (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le inf_le_left
    have hE₁U : ψ.range ⊓ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom = ⊥ :=
      (IsPGroup.disjoint_of_ne p 2 hp2 ψ.range _ hE₁p hU2').eq_bot
    obtain ⟨κ, hκ⟩ := exists_injective_of_le_sup
      (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent (t := TwistTag.D4) (K := K)
        (σ := σ.toRingHom))
      (by rw [inf_comm]; exact graphFixedRootTorus_inf_graphFixedPosUnipotent)
      ((show ψ.range ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom by
        rintro _ ⟨e, rfl⟩; exact hψB e).trans hBle) hE₁U
    set θ : E →* ModGL TwistTag.D4.tag K :=
      ((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subtype.comp κ).comp ψ.rangeRestrict
      with hθ
    have hθinj : Function.Injective θ :=
      (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subtype_injective.comp
        (hκ.comp (MonoidHom.rangeRestrict_injective_iff.2 hψinj))
    have hθle : θ.range ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
      rintro _ ⟨e, rfl⟩
      exact (κ (ψ.rangeRestrict e)).2
    have hθexp : ∀ x ∈ θ.range, x ^ p = 1 := by
      rintro _ ⟨e, rfl⟩
      rw [← map_pow, hEp' e, map_one]
    obtain ⟨g', hg'inj, -⟩ := exists_injective_of_le_graphFixedRootTorus_D4 σ.toRingHom hσ hq
      (fun c => hσc c) hodd hp hpq hθle hθexp
    have hcyc : IsCyclic E :=
      isCyclic_of_injective (g'.comp (MonoidHom.ofInjective hθinj).toMonoidHom)
        (hg'inj.comp (MonoidHom.ofInjective hθinj).injective)
    exact not_isCyclic_of_pow_eq_one hp hEc hEp' hcyc
  ·
    have hrT := not_dvd_card_graphFixedRootTorus_D4 σ hn hK hσc hp hpq h3
    have hcyc : IsCyclic φ.range :=
      isCyclic_of_le_graphFixedParabolic_singleton σ a hp2 hrT hEφle hEφp
    have hEcyc : IsCyclic E :=
      isCyclic_of_surjective (MonoidHom.ofInjective hφ).symm.toMonoidHom
        (MonoidHom.ofInjective hφ).symm.surjective
    exact not_isCyclic_of_pow_eq_one hp hEc hEp' hEcyc

end Main

end CFSG.RankThree.PartOne.KFU

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
open CFSG.Assembly.RankThreeEven (localRank)

theorem kf123ExcD4NoRankTwo : KF123ExcD4NoRankTwo := by
  intro X _ _ f hch p hp hp5 hpq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hch.1.2.1
  have hmodel : TwistedChevalleyModel X TwistTag.D4 (2 ^ f) := hch.2
  have hH : Holds X 2 := holds_of_twistedChevalleyModel hf hmodel
  obtain ⟨K, _, _, hK, σ₀, hσc, ⟨e₀⟩⟩ := hmodel
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = σ₀ :=
    ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩,
      RingHom.ext fun _ => rfl⟩
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  let e : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e₀.trans (CFSG.TauCetiBridge.Twisted.nativeEquiv Nat.prime_two hf hK hσc)
  have hH' : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 2 := hH.of_mulEquiv e
  by_contra hrank
  push Not at hrank
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) (by omega : 2 ≤ localRank p X)
  have : IsElementaryAbelian p E := hEel
  refine KFU.no_plane_D4 σ hf hK3 (fun c => hσc c) hH' hp (by omega) hpq
    (U := U.map e.toMonoidHom) (E := E.map e.toMonoidHom) ?_ (hU2.map e.toMonoidHom) ?_ ?_ ?_
  · intro hbot
    exact hU0 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hbot)
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hEU
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian g hg, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hEc

end CFSG.RankThree.PartOne
