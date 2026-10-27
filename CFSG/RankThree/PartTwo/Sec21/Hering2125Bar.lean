module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125CharTwo
import CFSG.RankThree.PartTwo.Sec21.Hering2125L3
import CFSG.RankThree.PartTwo.Sec21.Hering2125Lift
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofQuasi
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projImage projSL)
open CFSG.Open (IsCharTwoType pCoreOf)
open Matrix (ProjGenLinGroup)

namespace Hering2125

@[expose] def InducesTypeTwoL2 {G : Type} [Group G] [Finite G] (Y : Subgroup G) (x : G) : Prop :=
  ∃ (hx : x ∈ Subgroup.normalizer (Y : Set G)) (n : ℕ) (_ : 0 < n) (_ : Even n)
    (e : Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 3 (GaloisField 2 n))
    (y : GL (Fin 3) (GaloisField 2 n)), Sec4.Type123 true (2 ^ n) (GaloisField 2 n) y 2 ∧
      ∀ z : Y ⧸ aschbacherSolvableCore 3 Y,
        ((e (Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨x, hx⟩) z) :
            ProjGenLinGroup (Fin 3) (GaloisField 2 n))) =
          ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) (GaloisField 2 n)) *
            (ProjGenLinGroup.mk y)⁻¹

@[expose] def InducesInnerBar {G : Type} [Group G] [Finite G] (Y : Subgroup G) (x : G) : Prop :=
  ∃ hx : x ∈ Subgroup.normalizer (Y : Set G),
    Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨x, hx⟩) ∈
      (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →*
        MulAut (Y ⧸ aschbacherSolvableCore 3 Y)).range

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def imageI (Y I : Subgroup G) :
    Subgroup (Y ⧸ aschbacherSolvableCore 3 Y) :=
  (I.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))

theorem two_lt_pow_of_modThree {n : ℕ} (hn : 1 ≤ n) (hq : Sec4.ModThree true (2 ^ n)) :
    2 < 2 ^ n := by
  rcases Nat.lt_or_ge 1 n with h | h
  · calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
  · have : n = 1 := by omega
    subst this
    exact absurd hq (by simp [Sec4.ModThree])

theorem piField_galois {n : ℕ} (hn : 0 < n) : Sec4.PiField true 2 n (GaloisField 2 n) :=
  ⟨Nat.prime_two, hn, by rw [GaloisField.card 2 n hn.ne']; rfl⟩

theorem modThree_of_even {n : ℕ} (hev : Even n) : Sec4.ModThree true (2 ^ n) := by
  obtain ⟨k, rfl⟩ := hev
  show 2 ^ (k + k) % 3 = 1
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : e z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro h
    rw [← e.apply_symm_apply h, ← map_mul, ← map_mul, hz]
  rw [hB, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
  exact this

theorem center_eq_bot_of_typeTwo {Y : Subgroup G} {c : G} (hT : InducesTypeTwoL2 Y c) :
    Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
  obtain ⟨-, n, hn, hev, e, -⟩ := hT
  have hK := piField_galois hn
  have hq := modThree_of_even hev
  exact center_eq_bot_of_equiv
    (e.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage (2 ^ n) (GaloisField 2 n))))
    (Sec13.center_projImage_slPi hK hq (two_lt_pow_of_modThree hK.one_le hq))

theorem center_bar_eq_bot {Y : Type} [Group Y] [Finite Y]
    (h3 : ∀ z ∈ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y), ¬ 3 ∣ orderOf z) :
    Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hs, -, hnd, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)) 3 h
    apply h3 (z : Y ⧸ aschbacherSolvableCore 3 Y) z.2
    rw [Subgroup.orderOf_coe, hz]
  have hP := Item21EarlyProof.not_dvd_card_centerPre (aschbacherSolvableCore 3 Y) Nat.prime_three
    hnd hZ3
  have hPle := hmax _ inferInstance (Item21EarlyProof.isSolvable_centerPre _ hs) hP
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  have hy : y ∈ Item21EarlyProof.centerPre (aschbacherSolvableCore 3 Y) := hz
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr (hPle hy))

theorem bar_four_group {Y U₁ : Subgroup G} (hU₁Y : U₁ ≤ Y)
    (hUθ : U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y = ⊥)
    (hU₁ab : IsElemAbelian 2 U₁) (hU₁card : Nat.card U₁ = 4) :
    Nat.card ((U₁.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) = 4 ∧
      ∀ u ∈ (U₁.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)), u * u = 1 := by
  set θH : Subgroup Y := aschbacherSolvableCore 3 Y with hθH
  set π := QuotientGroup.mk' θH with hπ
  set U : Subgroup Y := U₁.subgroupOf Y with hU
  have hmemU : ∀ u : Y, u ∈ U ↔ (u : G) ∈ U₁ := fun u => Subgroup.mem_subgroupOf
  have hUcard : Nat.card U = 4 := by
    rw [hU, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₁Y).toEquiv]
    exact hU₁card
  have hmemθ : ∀ t : Y, t ∈ θH ↔ (t : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    intro t
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t', ht', htt'⟩
      have : t' = t := Subtype.ext htt'
      rwa [← this]
  have hUθ' : ∀ u ∈ U, u ∈ θH → u = 1 := by
    intro u hu hθ
    have : (u : G) ∈ U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y :=
      ⟨(hmemU u).mp hu, (hmemθ u).mp hθ⟩
    rw [hUθ, Subgroup.mem_bot] at this
    exact Subtype.ext this
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (π.subgroupMap U) := by
      intro a b hab
      have h1 : π (a : Y) = π (b : Y) := congrArg Subtype.val hab
      have h2 : (a : Y)⁻¹ * (b : Y) ∈ θH := by
        rw [← QuotientGroup.eq]
        exact h1
      have h3 := hUθ' _ (U.mul_mem (U.inv_mem a.2) b.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    rw [← hUcard]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, π.subgroupMap_surjective U⟩)).symm
  · intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← map_mul]
    have h2 : ((u₀ * u₀ : Y) : G) = 1 := by
      have := hU₁ab.2 (u₀ : G) ((hmemU u₀).mp hu₀)
      rw [Subgroup.coe_mul, ← pow_two]
      exact this
    rw [show u₀ * u₀ = 1 from Subtype.ext h2, map_one]

theorem isPGroup_two_of_card_four {X : Type*} [Group X] {U : Subgroup X} (h : Nat.card U = 4) :
    IsPGroup 2 U ∧ U ≠ ⊥ := by
  refine ⟨IsPGroup.of_card (n := 2) (by rw [h]; norm_num), fun hb => ?_⟩
  rw [hb, Subgroup.card_bot] at h
  omega

theorem center_bar_eq_bot_of_charTwo {Y : Type} [Group Y] [Finite Y]
    (hX : IsCharTwoType (Y ⧸ aschbacherSolvableCore 3 Y))
    {Ub : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)} (hcard : Nat.card Ub = 4) :
    Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
  obtain ⟨hU2, hU1⟩ := isPGroup_two_of_card_four hcard
  refine center_bar_eq_bot fun z hz h3 => ?_
  obtain ⟨k, hk⟩ := exists_two_pow_of_mem_center hX hU2 hU1 hz
  have hord : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h4 : 3 ∣ 2 ^ k := h3.trans hord
  have h5 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
  omega

theorem map_centralizer_equiv {Q X : Type*} [Group Q] [Group X] (e : Q ≃* X) (S : Subgroup Q) :
    (Subgroup.centralizer (S : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup X) : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    have := Subgroup.mem_centralizer_iff.mp hy s₀ hs₀
    show e s₀ * e y = e y * e s₀
    rw [← map_mul, ← map_mul, this]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hx (e s) ⟨s, hs, rfl⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1

theorem moved_of_charTwo_transport {Q X : Type} [Group Q] [Finite Q] [Group X]
    (hX : IsCharTwoType X) (e : Q ≃* X) (σ : MulAut Q) (g : X)
    (hσ : ∀ z : Q, e (σ z) = g * e z * g⁻¹) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (Ub : Subgroup Q) (hcard : Nat.card Ub = 4) (hfix : ∀ u ∈ Ub, σ u = u) :
    ∃ xb ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Ub : Set Q)), σ xb ≠ xb := by
  haveI : Finite X := Finite.of_equiv Q e.toEquiv
  set U : Subgroup X := Ub.map e.toMonoidHom with hU
  have hUcard : Nat.card U = 4 := by
    rw [hU, Subgroup.card_map_of_injective e.injective]
    exact hcard
  obtain ⟨hU2, hU1⟩ := isPGroup_two_of_card_four hUcard
  have hgU : g ∈ Subgroup.centralizer (U : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    have h1 := hσ u₀
    rw [hfix u₀ hu₀] at h1
    show e u₀ * g = g * e u₀
    calc e u₀ * g = (g * e u₀ * g⁻¹) * g := by rw [← h1]
      _ = g * e u₀ := by group
  obtain ⟨x, hx, hne⟩ := exists_moved_of_charTwo hX hU2 hU1 hgU hg3 hg1
  refine ⟨e.symm x, ?_, fun h => hne ?_⟩
  · have h1 : x ∈ pCoreOf 2 ((Subgroup.centralizer (Ub : Set Q)).map e.toMonoidHom) := by
      rw [map_centralizer_equiv e Ub]
      exact hx
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : e.symm x = y := by rw [← hyx]; simp
    rw [this]
    exact hy
  · have := hσ (e.symm x)
    rw [h, MulEquiv.apply_symm_apply] at this
    exact this.symm

theorem map_pCore_centralizer_of_fixed {Q : Type} [Group Q] (σ : MulAut Q) (Ub : Subgroup Q)
    (hfix : ∀ u ∈ Ub, σ u = u) {z : Q}
    (hz : z ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Ub : Set Q))) :
    σ z ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Ub : Set Q)) := by
  have hU : Ub.map (σ : Q ≃* Q).toMonoidHom = Ub := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      show σ v ∈ Ub
      rw [hfix v hv]
      exact hv
    · intro hu
      exact ⟨u, hu, hfix u hu⟩
  have hC : (Subgroup.centralizer (Ub : Set Q)).map (σ : Q ≃* Q).toMonoidHom =
      Subgroup.centralizer (Ub : Set Q) := by
    rw [map_centralizer_equiv (σ : Q ≃* Q) Ub, hU]
  have h1 := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (σ : Q ≃* Q)
    (Subgroup.centralizer (Ub : Set Q))
  rw [hC] at h1
  have h2 : σ z ∈ (pCoreOf 2 (Subgroup.centralizer (Ub : Set Q))).map
      (σ : Q ≃* Q).toMonoidHom := ⟨z, hz, rfl⟩
  rw [← h1] at h2
  exact h2

theorem exists_pCore_not_theta_of_bar {Y U₁ : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1) (hU₁Y : U₁ ≤ Y)
    (hUθ : U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y = ⊥)
    (hU₁ab : IsElemAbelian 2 U₁) (hU₁card : Nat.card U₁ = 4)
    (hcU₁ : c ∈ Subgroup.centralizer (U₁ : Set G))
    (hθc : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, ∀ y ∈ Y, t * y = y * t)
    (hθ2 : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, t * t = 1 → c * t * c⁻¹ = t)
    (hbar : ∀ Ub : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y), Nat.card Ub = 4 →
      (∀ u ∈ Ub, u * u = 1) →
      (∀ u ∈ Ub, Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨c, hcN⟩) u = u) →
      ∃ xb ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Ub : Set _)),
        Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨c, hcN⟩) xb ≠ xb) :
    ∃ x ∈ inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)),
      x * c * x⁻¹ * c⁻¹ ∉ inSubgroup (aschbacherSolvableCore 3) Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θH : Subgroup Y := aschbacherSolvableCore 3 Y with hθH
  set π := QuotientGroup.mk' θH with hπ
  set U : Subgroup Y := U₁.subgroupOf Y with hU
  have hmemU : ∀ u : Y, u ∈ U ↔ (u : G) ∈ U₁ := fun u => Subgroup.mem_subgroupOf
  have hUcard : Nat.card U = 4 := by
    rw [hU, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₁Y).toEquiv]
    exact hU₁card
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  have hmemθ : ∀ t : Y, t ∈ θH ↔ (t : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    intro t
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t', ht', htt'⟩
      have : t' = t := Subtype.ext htt'
      rwa [← this]
  have hθHc : ∀ t ∈ θH, ∀ h : Y, t * h = h * t := fun t ht h =>
    Subtype.ext (hθc t ((hmemθ t).mp ht) h h.2)
  set Ub : Subgroup (Y ⧸ θH) := U.map π with hUb
  obtain ⟨hUbcard, hUbexp⟩ := bar_four_group hU₁Y hUθ hU₁ab hU₁card
  set σY : MulAut Y := Y.normalizerMonoidHom ⟨c, hcN⟩ with hσY
  set σb : MulAut (Y ⧸ θH) := Sec4.thetaQuotMulAut Y σY with hσb
  have hσ : ∀ u₀ ∈ U, σY u₀ = u₀ := by
    intro u₀ hu₀
    apply Subtype.ext
    have h1 : c * (u₀ : G) = (u₀ : G) * c :=
      (Subgroup.mem_centralizer_iff.mp hcU₁ _ ((hmemU u₀).mp hu₀)).symm
    show c * (u₀ : G) * c⁻¹ = u₀
    rw [h1]
    group
  have hσ2 : ∀ t ∈ θH, t * t = 1 → σY t = t := by
    intro t ht ht2
    apply Subtype.ext
    have h1 : ((t * t : Y) : G) = 1 := by rw [ht2]; rfl
    exact hθ2 t ((hmemθ t).mp ht) (by simpa using h1)
  have hmk : ∀ w : Y, σb (π w) = π (σY w) := fun w => Sec4.thetaQuotMulAut_mk σY w
  have hfix : ∀ u ∈ Ub, σb u = u := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    rw [hmk, hσ u₀ hu₀]
  obtain ⟨xb, hxb, hne⟩ := hbar Ub hUbcard hUbexp hfix
  have hσb3 : σb ^ 3 = 1 := by
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [hσb, hσY, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσxb := map_pCore_centralizer_of_fixed σb Ub hfix hxb
  set R : Subgroup (Y ⧸ θH) :=
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Ub : Set (Y ⧸ θH))) with hR
  have hyR : xb * (σb xb)⁻¹ ∈ R := R.mul_mem hxb (R.inv_mem hσxb)
  have hyne : σb (xb * (σb xb)⁻¹) ≠ xb * (σb xb)⁻¹ := by
    intro hy1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer (Ub : Set (Y ⧸ θH))) ⟨_, hyR⟩
    have hk' : (xb * (σb xb)⁻¹) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : σb (σb (σb xb)) = xb := by
      have := congrArg (fun φ : MulAut (Y ⧸ θH) => φ xb) hσb3
      simpa [pow_succ, MulAut.mul_apply] using this
    have e1 : σb (xb * (σb xb)⁻¹) = σb xb * (σb (σb xb))⁻¹ := by rw [map_mul, map_inv]
    have e2 : σb (σb xb * (σb (σb xb))⁻¹) = σb (σb xb) * xb⁻¹ := by
      rw [map_mul, map_inv, h3]
    have hy2 : xb * (σb xb)⁻¹ = σb xb * (σb (σb xb))⁻¹ := by rw [← e1]; exact hy1.symm
    have hy3 : xb * (σb xb)⁻¹ = σb (σb xb) * xb⁻¹ := by
      rw [← e2, ← e1, hy1, hy1]
    have hcube : (xb * (σb xb)⁻¹) ^ 3 = 1 := by
      calc (xb * (σb xb)⁻¹) ^ 3 = (xb * (σb xb)⁻¹) * (xb * (σb xb)⁻¹) * (xb * (σb xb)⁻¹) := by
            simp only [pow_succ, pow_zero, one_mul]
        _ = (xb * (σb xb)⁻¹) * (σb xb * (σb (σb xb))⁻¹) * (σb (σb xb) * xb⁻¹) := by
            rw [← hy2, ← hy3]
        _ = 1 := by group
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h1 : xb * (σb xb)⁻¹ = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hk', hcube⟩
    exact hne (mul_inv_eq_one.mp h1).symm
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective θH xb
  have hxbC : xb ∈ Subgroup.centralizer (Ub : Set (Y ⧸ θH)) := (Subgroup.map_subtype_le _) hxb
  have hx₁C : a * (σY a)⁻¹ ∈ Subgroup.centralizer (U : Set Y) := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    obtain ⟨t, ht⟩ : ∃ t : Y, t = a * u * a⁻¹ * u⁻¹ := ⟨_, rfl⟩
    have hu2 : u * u = 1 := by
      apply Subtype.ext
      have := hU₁ab.2 (u : G) ((hmemU u).mp hu)
      rw [Subgroup.coe_mul, ← pow_two]
      exact this
    have htθ : t ∈ θH := by
      have h1 : π u * xb = xb * π u :=
        Subgroup.mem_centralizer_iff.mp hxbC (π u) ⟨u, hu, rfl⟩
      rw [← QuotientGroup.ker_mk' θH, MonoidHom.mem_ker, ht]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha]
      calc xb * π u * (xb)⁻¹ * (π u)⁻¹ = (π u * xb) * (xb)⁻¹ * (π u)⁻¹ := by rw [h1]
        _ = 1 := by group
    have htc : ∀ g : Y, t * g = g * t := hθHc t htθ
    have e1 : a * u = t * u * a := by rw [ht]; group
    have ht2 : t * t = 1 := by
      have h1 : (t * u) * (t * u) = 1 := by
        calc (t * u) * (t * u) = (a * u * a⁻¹) * (a * u * a⁻¹) := by
              rw [show t * u = a * u * a⁻¹ by rw [ht]; group]
          _ = a * (u * u) * a⁻¹ := by group
          _ = 1 := by rw [hu2]; group
      calc t * t = t * t * (u * u) := by rw [hu2, mul_one]
        _ = t * (t * u) * u := by group
        _ = t * (u * t) * u := by rw [htc u]
        _ = (t * u) * (t * u) := by group
        _ = 1 := h1
    have hσt : σY t = t := hσ2 t htθ ht2
    have hb : σY a * u * (σY a)⁻¹ * u⁻¹ = t := by
      have h1 : σY (a * u * a⁻¹ * u⁻¹) = t := by rw [← ht]; exact hσt
      rwa [map_mul, map_mul, map_mul, map_inv, map_inv, hσ u hu] at h1
    have e2 : σY a * u = t * u * σY a := by rw [← hb]; group
    have e3 : u * a = t⁻¹ * (a * u) := by rw [e1]; group
    have e4 : u * (σY a)⁻¹ = (σY a)⁻¹ * (t * u) := by
      calc u * (σY a)⁻¹ = (σY a)⁻¹ * (σY a * u) * (σY a)⁻¹ := by group
        _ = (σY a)⁻¹ * (t * u * σY a) * (σY a)⁻¹ := by rw [e2]
        _ = (σY a)⁻¹ * (t * u) := by group
    calc u * (a * (σY a)⁻¹) = (u * a) * (σY a)⁻¹ := by group
      _ = t⁻¹ * (a * u) * (σY a)⁻¹ := by rw [e3]
      _ = t⁻¹ * a * (u * (σY a)⁻¹) := by group
      _ = t⁻¹ * a * ((σY a)⁻¹ * (t * u)) := by rw [e4]
      _ = a * (σY a)⁻¹ * u := by
        calc t⁻¹ * a * ((σY a)⁻¹ * (t * u)) = t⁻¹ * (a * ((σY a)⁻¹ * t) * u) := by group
          _ = t⁻¹ * (a * (t * (σY a)⁻¹) * u) := by rw [← htc (σY a)⁻¹]
          _ = (t⁻¹ * (a * t)) * (σY a)⁻¹ * u := by group
          _ = (t⁻¹ * (t * a)) * (σY a)⁻¹ * u := by rw [htc a]
          _ = a * (σY a)⁻¹ * u := by group
  have hπx₁ : π (a * (σY a)⁻¹) = xb * (σb xb)⁻¹ := by
    rw [map_mul, map_inv, ha, ← hmk, ha]
  obtain ⟨xH, hxH, hπxH⟩ := lift_pCore_of_lift θH hθHc U _ hyR ⟨_, hx₁C, hπx₁⟩
  refine ⟨(xH : G), coe_mem_inSubgroup_pCore hU₁Y hxH, ?_⟩
  intro hz
  obtain ⟨z', hz', hzeq⟩ := hz
  set xc : Y := σY xH with hxc
  have hz'eq : z' = xH * xc⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have : ((xc : Y) : G) = c * (xH : G) * c⁻¹ := rfl
    rw [this]
    simp only [Subgroup.coe_subtype] at hzeq
    rw [hzeq]
    group
  have h1 : π xH = π xc := by
    have hmem : xH * xc⁻¹ ∈ θH := hz'eq ▸ hz'
    have h0 : π (xH * xc⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rwa [map_mul, map_inv, mul_inv_eq_one] at h0
  apply hyne
  rw [← hπxH, hmk, ← h1]

theorem exists_pCore_not_theta {Y U₁ : Subgroup G} {c : G}
    (hT : InducesTypeTwoL2 Y c) (hc3 : c ^ 3 = 1) (hU₁Y : U₁ ≤ Y)
    (hUθ : U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y = ⊥)
    (hU₁ab : IsElemAbelian 2 U₁) (hU₁card : Nat.card U₁ = 4)
    (hcU₁ : c ∈ Subgroup.centralizer (U₁ : Set G))
    (hθc : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, ∀ y ∈ Y, t * y = y * t)
    (hθ2 : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, t * t = 1 → c * t * c⁻¹ = t) :
    ∃ x ∈ inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)),
      x * c * x⁻¹ * c⁻¹ ∉ inSubgroup (aschbacherSolvableCore 3) Y := by
  obtain ⟨hcN, n, hn, hev, e, y, hy, hact⟩ := hT
  have hK := piField_galois hn
  have hq := modThree_of_even hev
  refine exists_pCore_not_theta_of_bar hcN hc3 hU₁Y hUθ hU₁ab hU₁card hcU₁ hθc hθ2 ?_
  intro Ub hcard hexp hfix
  set e' := e.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage (2 ^ n) (GaloisField 2 n)))
    with he'
  have hfix' : ∀ u ∈ Ub, ProjGenLinGroup.mk y * (e' u : ProjGenLinGroup (Fin 3) (GaloisField 2 n)) *
      (ProjGenLinGroup.mk y)⁻¹ = (e' u : ProjGenLinGroup (Fin 3) (GaloisField 2 n)) := by
    intro u hu
    have h1 := hact u
    rw [hfix u hu] at h1
    exact h1.symm
  obtain ⟨xb, hxb, hne⟩ := l3_exists_moved hK hq hy e' Ub hcard hexp hfix'
  refine ⟨xb, hxb, fun h => hne ?_⟩
  have h3 := hact xb
  rw [h] at h3
  exact h3.symm

theorem not_commutator_le_theta {Y U₁ B : Subgroup G} {c : G}
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hcB : c ∈ B) (hBN : B ≤ Subgroup.normalizer (Y : Set G))
    (hx : ∃ x ∈ inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)),
      x * c * x⁻¹ * c⁻¹ ∉ inSubgroup (aschbacherSolvableCore 3) Y) :
    ¬ ⁅Y, ⁅inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)), B⁆⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) Y := by
  intro h
  obtain ⟨x, hxP, hxθ⟩ := hx
  set P := inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)) with hP
  have hPY : P ≤ Y := (Subgroup.map_subtype_le _).trans inf_le_left
  have hPN : P ≤ Subgroup.normalizer (Y : Set G) := hPY.trans Subgroup.le_normalizer
  have hN : ⁅P, B⁆ ≤ Subgroup.normalizer (Y : Set G) := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPN ha) (hBN hb))
      (Subgroup.inv_mem _ (hPN ha))) (Subgroup.inv_mem _ (hBN hb))
  have hPB : ⁅P, B⁆ ≤ Sec4.thetaQuotCentralizer Y := (Sec6.commutator_le_theta_iff hN).mp h
  have hz : x * c * x⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
    have := Subgroup.commutator_mem_commutator hxP hcB
    rw [commutatorElement_def] at this
    exact hPB this
  have hxY : x ∈ Y := hPY hxP
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hBN hcB
  have hzY : x * c * x⁻¹ * c⁻¹ ∈ Y := by
    have h1 : c * x⁻¹ * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hcN x⁻¹).mp (Y.inv_mem hxY)
    have : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [this]
    exact Y.mul_mem hxY h1
  apply hxθ
  set zY : Y := ⟨x * c * x⁻¹ * c⁻¹, hzY⟩ with hzY'
  have hcenter : (zY : Y ⧸ aschbacherSolvableCore 3 Y) ∈
      Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hz).2 (l : G) l.2
      obtain ⟨t, ht, hteq⟩ := h1
      have h2 : l⁻¹ * (zY * l * zY⁻¹) = t := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, zY]
        exact hteq.symm
      have h3 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (l⁻¹ * (zY * l * zY⁻¹)) = 1 := by
        rw [h2]
        exact (QuotientGroup.eq_one_iff t).mpr ht
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h3
      show (l : Y ⧸ aschbacherSolvableCore 3 Y) * (zY : Y ⧸ aschbacherSolvableCore 3 Y) =
        (zY : Y ⧸ aschbacherSolvableCore 3 Y) * l
      have h4 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) l =
          QuotientGroup.mk' (aschbacherSolvableCore 3 Y) zY *
            QuotientGroup.mk' (aschbacherSolvableCore 3 Y) l *
              (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) zY)⁻¹ := h3
      calc (l : Y ⧸ aschbacherSolvableCore 3 Y) * (zY : Y ⧸ aschbacherSolvableCore 3 Y)
          = (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) zY *
            QuotientGroup.mk' (aschbacherSolvableCore 3 Y) l *
              (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) zY)⁻¹) *
                QuotientGroup.mk' (aschbacherSolvableCore 3 Y) zY := by rw [← h4]; rfl
        _ = (zY : Y ⧸ aschbacherSolvableCore 3 Y) * l := by group; rfl
  rw [hZ, Subgroup.mem_bot] at hcenter
  have hzθ : zY ∈ aschbacherSolvableCore 3 Y := (QuotientGroup.eq_one_iff zY).mp hcenter
  exact ⟨zY, hzθ, rfl⟩

theorem not_commutator_of_inner {Y U₁ B : Subgroup G} {c : G}
    (hX : IsCharTwoType (Y ⧸ aschbacherSolvableCore 3 Y))
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hin : InducesInnerBar Y c) (hBN : B ≤ Subgroup.normalizer (Y : Set G)) (hcB : c ∈ B)
    (hc3 : c ^ 3 = 1) (hcnt : c ∉ Sec4.thetaQuotCentralizer Y) (hU₁Y : U₁ ≤ Y)
    (hUθ : U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y = ⊥)
    (hU₁ab : IsElemAbelian 2 U₁) (hU₁card : Nat.card U₁ = 4)
    (hcU₁ : c ∈ Subgroup.centralizer (U₁ : Set G))
    (hθc : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, ∀ y ∈ Y, t * y = y * t)
    (hθ2 : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, t * t = 1 → c * t * c⁻¹ = t) :
    ¬ ⁅Y, ⁅inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)), B⁆⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) Y := by
  obtain ⟨hcN, g, hg⟩ := hin
  set σ := Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨c, hcN⟩) with hσ
  have hact : ∀ z : Y ⧸ aschbacherSolvableCore 3 Y, σ z = g * z * g⁻¹ := by
    intro z
    rw [← hg, MulAut.conj_apply]
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hpow : ∀ (k : ℕ) (z : Y ⧸ aschbacherSolvableCore 3 Y),
      (σ ^ k) z = g ^ k * z * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [pow_succ', MulAut.mul_apply, hact, ih]
      group
  have hg3 : g ^ 3 = 1 := by
    have hg3c : g ^ 3 ∈ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := hpow 3 x
      rw [hσ3, MulAut.one_apply] at h1
      calc x * g ^ 3 = (g ^ 3 * x * (g ^ 3)⁻¹) * g ^ 3 := by rw [← h1]
        _ = g ^ 3 * x := by group
    rw [hZ, Subgroup.mem_bot] at hg3c
    exact hg3c
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hcnt
    refine ⟨⟨c, hcN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    ext z
    have h1 := hact z
    simp only [one_mul, inv_one, mul_one] at h1
    exact congrArg (fun w => (w : Y ⧸ aschbacherSolvableCore 3 Y)) h1
  refine not_commutator_le_theta hZ hcB hBN
    (exists_pCore_not_theta_of_bar hcN hc3 hU₁Y hUθ hU₁ab hU₁card hcU₁ hθc hθ2 ?_)
  intro Ub hcard _ hfix
  exact moved_of_charTwo_transport hX (MulEquiv.refl _) σ g hact hg3 hg1 Ub hcard hfix

theorem sl2five_sq_eq_one {v : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)} (hv : v * v = 1) :
    v = 1 ∨ v = -1 := by
  revert v
  decide +kernel

theorem sl2five_no_klein (V : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))
    (h4 : Nat.card V = 4) (hV : ∀ v ∈ V, v * v = 1) : False := by
  have hle : V ≤ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
    intro v hv
    rcases sl2five_sq_eq_one (hV v hv) with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hdvd := Subgroup.card_dvd_of_le hle
  have hord : orderOf (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · decide +kernel
    · decide +kernel
  rw [Nat.card_zpowers, hord, h4] at hdvd
  omega

theorem false_of_sl2five {Y U₁ I : Subgroup G} (hU₁Y : U₁ ≤ Y)
    (hUθ : U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y = ⊥)
    (hU₁ab : IsElemAbelian 2 U₁) (hU₁card : Nat.card U₁ = 4) (hU₁I : U₁ ≤ I)
    (hSL : Nonempty (imageI Y I ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) : False := by
  obtain ⟨f⟩ := hSL
  obtain ⟨hcard, hexp⟩ := bar_four_group hU₁Y hUθ hU₁ab hU₁card
  set Ub := (U₁.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) with hUb
  have hle : Ub ≤ imageI Y I := Subgroup.map_mono fun u hu =>
    Subgroup.mem_subgroupOf.mpr (hU₁I (Subgroup.mem_subgroupOf.mp hu))
  set W : Subgroup (imageI Y I) := Ub.subgroupOf (imageI Y I) with hW
  have hWcard : Nat.card W = 4 := by
    rw [hW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hcard
  refine sl2five_no_klein (W.map f.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective f.injective]; exact hWcard) ?_
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  rw [← map_mul]
  have : w * w = 1 := Subtype.ext (hexp _ (Subgroup.mem_subgroupOf.mp hw))
  rw [this, map_one]

end Hering2125

end CFSG.RankThree.PartTwo.Sec21
