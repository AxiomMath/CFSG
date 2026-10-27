module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec16.KS16ProofSec
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.PartOne.KE.SuzukiDescent
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec16.KS1619SzFixProof

open CFSG CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_injective)
open CFSG.RankThree.PartTwo.Sec16.Proof1619 (isPerfect_and_two_dvd_of_suzukiModel)

section Fix

variable {M M' : Type*} [Group M] [Group M']

abbrev fixOf (τ : MulAut M) : Subgroup M :=
  τ.toMonoidHom.eqLocus (MonoidHom.id M)

theorem mem_fixOf {τ : MulAut M} {x : M} : x ∈ fixOf τ ↔ τ x = x :=
  Iff.rfl

def fixEquiv (e : M ≃* M') (τ : MulAut M) : fixOf τ ≃* fixOf (MulAut.congr e τ) where
  toFun x := ⟨e x, by
    have hx : τ x = x := x.2
    change e (τ (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]⟩
  invFun y := ⟨e.symm y, by
    have h : e (τ (e.symm y)) = y := y.2
    change τ (e.symm y) = e.symm y
    exact e.injective (by rw [h, MulEquiv.apply_symm_apply])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : M) y)

theorem le_derivedSeries_of_isPerfect {H : Subgroup M} (hH : Group.IsPerfect H) (m : ℕ) :
    H ≤ derivedSeries M m := by
  induction m with
  | zero => exact le_top
  | succ m ih =>
    rw [derivedSeries_succ]
    calc H = ⁅H, H⁆ := (Subgroup.isPerfect_iff.1 hH).symm
      _ ≤ ⁅derivedSeries M m, derivedSeries M m⁆ := Subgroup.commutator_mono ih ih

theorem isPerfect_and_two_dvd_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Group.IsPerfect Y ∧ 2 ∣ Nat.card Y) : Group.IsPerfect X ∧ 2 ∣ Nat.card X := by
  have := h.1
  exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    by rw [Nat.card_congr e.toEquiv]; exact h.2⟩

end Fix

theorem fix_perfect_even {a : ℕ} {F : Type} [Field F] [Finite F]
    (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1)) (h3 : 3 < 2 * a + 1)
    {β : MulAut (suzukiGroup a F)} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    Group.IsPerfect (fixOf β) ∧ 2 ∣ Nat.card (fixOf β) := by
  have hmodel : SuzukiModel (suzukiGroup a F) 2 (2 * a + 1) :=
    ⟨rfl, a, ha, F, inferInstance, inferInstance, rfl, hF, ⟨MulEquiv.refl _⟩⟩
  have : Finite (suzukiGroup a F) := KFacts.KP7.finite_of_suzukiModel hmodel
  have hout : ¬ KFacts.IsInnerAut β := by
    rintro ⟨g, rfl⟩
    have h3g : ¬ 3 ∣ orderOf g := fun h =>
      KFacts.not_three_dvd_card_suzukiGroup hF (h.trans (orderOf_dvd_natCard g))
    have hd1 : orderOf (MulAut.conj g) ∣ orderOf g := orderOf_map_dvd _ _
    have hd2 : orderOf (MulAut.conj g) ∣ 3 := orderOf_dvd_of_pow_eq_one hβ3
    have h1 : orderOf (MulAut.conj g) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hd2 with h | h
      · exact h
      · exact absurd (h ▸ hd1) h3g
    exact hβ1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨_, ⟨σ, rfl⟩, hφ1, _, ⟨g, rfl⟩, hβ⟩ :=
    KFacts.isField_sz_of_pow_three_eq_one ha hF hβ3 hout
  have hφ3 : szFieldAut a F σ ^ 3 = 1 := by
    have h := hβ3
    rw [hβ, conj_pow] at h
    exact conj_eq_one_iff.mp h
  have hσ3 : σ ^ 3 = 1 := szFieldAut_injective (by rw [map_pow, hφ3, map_one])
  have hσ1 : σ ≠ 1 := fun h => hφ1 (by rw [h, map_one])
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega : 1 ≤ 2 * a + 1) hF σ
  rw [hσo] at hdvd hcard
  obtain ⟨m, hm⟩ := hdvd
  have hmodd : m % 2 = 1 := by omega
  set b := m / 2 with hb
  have hmb : m = 2 * b + 1 := by omega
  have hb1 : 1 ≤ b := by omega
  have hk : Nat.card (CFSG.RankThree.PartOne.KE.fixField σ) = 2 ^ (2 * b + 1) := by
    have h1 : (2 * a + 1) / 3 = 2 * b + 1 := by omega
    rw [← h1]
    exact hcard
  obtain ⟨eφ⟩ := CFSG.RankThree.PartOne.KE.fixed_szFieldAut_equiv hF hk
    (show a = b + (2 * b + 1) * 1 by omega)
  have hkfin : Finite (CFSG.RankThree.PartOne.KE.fixField σ) :=
    Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hφ : Group.IsPerfect (fixOf (szFieldAut a F σ)) ∧
      2 ∣ Nat.card (fixOf (szFieldAut a F σ)) :=
    isPerfect_and_two_dvd_of_mulEquiv eφ (isPerfect_and_two_dvd_of_suzukiModel
      ⟨rfl, b, hb1, CFSG.RankThree.PartOne.KE.fixField σ, inferInstance, hkfin, rfl, hk,
        ⟨MulEquiv.refl _⟩⟩)
  have hβ' : MulAut.conj g * szFieldAut a F σ * (MulAut.conj g)⁻¹ =
      MulAut.congr (MulAut.conj g) (szFieldAut a F σ) := by
    ext x
    rfl
  rw [hβ, hβ']
  exact isPerfect_and_two_dvd_of_mulEquiv (fixEquiv (MulAut.conj g) (szFieldAut a F σ)).symm hφ

end CFSG.RankThree.PartTwo.Sec16.KS1619SzFixProof

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.Blueprint KS1619SzFixProof
open CFSG.RankThree.PartTwo.Sec16.Proof1619 (conjQuot conjQuot_mk conjQuot_pow_three
  isPerfect_and_two_dvd_of_suzukiModel)
open CFSG.RankThree.PartTwo.Sec16.KS1619SecProof (exists_fixed_mem_coset)

theorem ks1619SzFix : KS1619SzFix := by
  intro G _ _ K c n hcK hc3 hK3 hSz hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥K with hNdef
  set π := QuotientGroup.mk' N with hπ
  set α := conjQuot K hcK with hαdef
  have hα3 : α ^ 3 = 1 := conjQuot_pow_three K hcK hc3
  have hY : Group.IsPerfect (fixOf α) ∧ 2 ∣ Nat.card (fixOf α) := by
    by_cases hα1 : α = 1
    · have htop : fixOf α = ⊤ := eq_top_iff.mpr fun y _ => by
        rw [mem_fixOf, hα1]
        rfl
      rw [htop]
      exact isPerfect_and_two_dvd_of_mulEquiv Subgroup.topEquiv
        (isPerfect_and_two_dvd_of_suzukiModel hSz)
    · obtain ⟨-, a, ha, F, _, _, rfl, hF, ⟨e⟩⟩ := hSz
      have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
      have hβ1 : MulAut.congr e α ≠ 1 := fun h =>
        hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
      exact isPerfect_and_two_dvd_of_mulEquiv (fixEquiv e α) (fix_perfect_even ha hF hn hβ3 hβ1)
  obtain ⟨hYperf, hY2⟩ := hY
  set X := K ⊓ Subgroup.centralizer ({c} : Set G) with hX
  set fX : ↥X →* ↥K ⧸ N := π.comp (Subgroup.inclusion inf_le_left) with hfX
  have hmemK : ∀ (j : ℕ) (k : K), c ^ j * (k : G) * (c ^ j)⁻¹ ∈ K := fun j k =>
    (Subgroup.mem_normalizer_iff.mp (pow_mem hcK j) k).mp k.2
  have hαpow : ∀ (j : ℕ) (k : K), (α ^ j) (π k) = π ⟨c ^ j * k * (c ^ j)⁻¹, hmemK j k⟩ := by
    intro j
    induction j with
    | zero =>
      intro k
      rw [pow_zero, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      simp
    | succ j ih =>
      intro k
      rw [pow_succ', MulAut.mul_apply, ih, hαdef, hπ, QuotientGroup.mk'_apply, conjQuot_mk]
      congr 1
      apply Subtype.ext
      change c * (c ^ j * (k : G) * (c ^ j)⁻¹) * c⁻¹ = c ^ (j + 1) * k * (c ^ (j + 1))⁻¹
      rw [pow_succ']
      group
  have hN2 : IsPGroup 2 (N.map K.subtype) := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map _
  have hNf : ¬ 3 ∣ Nat.card (N.map K.subtype) := by
    obtain ⟨j, hj⟩ := hN2.exists_card_eq
    rw [hj]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hBp : IsPGroup 3 (Subgroup.zpowers c) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc3) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hcN : c ∈ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨k, hk, rfl⟩ := hg
    have hmap : N.map (K.normalizerMonoidHom ⟨c, hcK⟩).toMonoidHom = N :=
      CFSG.pCore_map_iso 2 _
    have h1 : K.normalizerMonoidHom ⟨c, hcK⟩ k ∈ N := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hk
    exact ⟨_, h1, rfl⟩
  have hcover : fixOf α ≤ fX.range := by
    intro y hy
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hfix : α (π k₀) = π k₀ := hy
    have hfixpow : ∀ j : ℕ, (α ^ j) (π k₀) = π k₀ := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, hfix]
    have hk : ∀ b ∈ Subgroup.zpowers c,
        (k₀ : G)⁻¹ * (b * k₀ * b⁻¹) ∈ N.map K.subtype := by
      intro b hb
      obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hb)
      have h1 := (hαpow j k₀).symm.trans (hfixpow j)
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq] at h1
      exact ⟨_, h1, rfl⟩
    obtain ⟨y', hy', hyc⟩ := exists_fixed_mem_coset hBp hNf (Subgroup.zpowers_le.mpr hcN) hk
    obtain ⟨φ, hφ, hφy⟩ := hy'
    have hy'K : y' ∈ K := by
      have h1 : y' = (k₀ : G) * ((k₀ : G)⁻¹ * y') := by group
      rw [h1, ← hφy]
      exact K.mul_mem k₀.2 φ.2
    have hy'C : y' ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hyc c (Subgroup.mem_zpowers c)).symm
    refine ⟨⟨y', hy'K, hy'C⟩, ?_⟩
    change π ⟨y', hy'K⟩ = π k₀
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    have h1 : k₀⁻¹ * ⟨y', hy'K⟩ = φ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hφy.symm)
    rw [h1]
    exact hφ
  obtain ⟨m, hm, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥X)
  set f' : ↥X →* ↥fX.range := fX.rangeRestrict with hf'
  have hf'surj : Function.Surjective f' := fX.rangeRestrict_surjective
  have eY : (fixOf α).subgroupOf fX.range ≃* fixOf α := Subgroup.subgroupOfEquivOfLe hcover
  have hY'perf : Group.IsPerfect ((fixOf α).subgroupOf fX.range) :=
    (isPerfect_and_two_dvd_of_mulEquiv eY ⟨hYperf, hY2⟩).1
  have hY'le := le_derivedSeries_of_isPerfect hY'perf m
  have hmap : (derivedSeries ↥X m).map f' = derivedSeries ↥fX.range m :=
    map_derivedSeries_eq hf'surj m
  have hdvd1 : Nat.card ((fixOf α).subgroupOf fX.range) ∣ Nat.card (derivedSeries ↥fX.range m) :=
    Subgroup.card_dvd_of_le hY'le
  have hdvd2 : Nat.card (derivedSeries ↥fX.range m) ∣ Nat.card (derivedSeries ↥X m) := by
    rw [← hmap]
    exact Subgroup.card_map_dvd _ _
  rw [inSubgroup, Subgroup.card_map_of_injective X.subtype_injective, hm]
  rw [Nat.card_congr eY.toEquiv] at hdvd1
  exact hY2.trans (hdvd1.trans hdvd2)

end CFSG.RankThree.PartTwo.Sec16
