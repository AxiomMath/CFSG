module

import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Models.PGLOrders
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedSp StatedSL StatedProj)
open CFSG.Assembly.RankThreeEven (localRank projSp projSL)

namespace Item812Res2

section Card

theorem card_eq_card_ker_mul_card_map {A M : Type*} [Group A] [Group M] [Finite A]
    (ρ : A →* M) (H : Subgroup A) (hker : ρ.ker ≤ H) :
    Nat.card H = Nat.card ρ.ker * Nat.card (H.map ρ) := by
  set ρ' := ρ.comp H.subtype with hρ'
  have h1 := Subgroup.card_mul_index ρ'.ker
  rw [Subgroup.index_ker] at h1
  have hrange : ρ'.range = H.map ρ := by
    rw [hρ', MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerc : Nat.card ρ'.ker = Nat.card ρ.ker := by
    have hk : ρ'.ker = ρ.ker.subgroupOf H := by
      ext y
      simp [hρ', MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [← h1, hrange, hkerc]

theorem card_projSp_two_one : Nat.card (projSp 2 (GaloisField 2 1)) = 720 :=
  CFSG.PGLModel.card_projSp_two_two

theorem card_projSp_two_three : Nat.card (projSp 2 (GaloisField 2 3)) = 1056706560 :=
  CFSG.PGLModel.card_projSp_two_eight

theorem card_projSL_two {e : ℕ} (he : 1 ≤ e) :
    Nat.card (projSL 2 (GaloisField 2 e)) = 2 ^ e * ((2 ^ e) ^ 2 - 1) := by
  let φ : StatedProj (StatedSL 2 (GaloisField 2 e)) ≃* projSL 2 (GaloisField 2 e) :=
    (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 2 _))
  rw [← Nat.card_congr φ.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
    GaloisField.card 2 e (by omega)]
  have hgcd : Nat.gcd 2 (2 ^ e - 1) = 1 := by
    have hodd : Odd (2 ^ e - 1) := by
      have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      have h2 : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
      obtain ⟨r, hr⟩ := h2
      exact ⟨r - 1, by omega⟩
    exact (Nat.coprime_two_left.mpr hodd)
  rw [hgcd, Nat.div_one, show (2 : ℕ) * (2 - 1) / 2 = 1 by rfl, pow_one,
    show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton]

theorem not_dvd_seven_twenty {m : ℕ} (hm : 1 ≤ m) :
    ¬ 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) ∣ 720 := by
  intro h
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · interval_cases m
    norm_num at h
  · have h64 : 64 ≤ 2 ^ (3 * m) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ (2 ^ (3 * m)) ^ 2 - 1 := by
      have : 64 * 64 ≤ (2 ^ (3 * m)) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul h64 h64
      omega
    have hle := Nat.le_of_dvd (by norm_num) h
    have : 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) ≥ 64 * ((64 * 64) - 1) := by
      have h65 : 64 * 64 - 1 ≤ (2 ^ (3 * m)) ^ 2 - 1 := by
        have : 64 * 64 ≤ (2 ^ (3 * m)) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul h64 h64
        omega
      exact Nat.mul_le_mul h64 h65
    omega

end Card

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem thetaQuotMulAut_compAction_of_mem {y : G} (hy : y ∈ L)
    (hN : y ∈ Subgroup.normalizer (L : Set G)) :
    thetaQuotMulAut L (compAction L ⟨y, hN⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hy⟩) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H w =>
    rw [thetaQuotMulAut_mk, MulAut.conj_apply]
    change QuotientGroup.mk' (aschbacherSolvableCore 3 L) (compAction L ⟨y, hN⟩ w) = _
    have hw : compAction L ⟨y, hN⟩ w = ⟨y, hy⟩ * w * ⟨y, hy⟩⁻¹ :=
      Subtype.ext (normalizerMonoidHom_apply_coe hN w)
    rw [hw, map_mul, map_mul, map_inv]
    rfl

omit [Finite G] in
theorem mem_normalizer_of_mem {y : G} (hy : y ∈ L) : y ∈ Subgroup.normalizer (L : Set G) :=
  Subgroup.le_normalizer hy

theorem mem_sup_thetaQuotCentralizer_iff {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    a ∈ L ⊔ thetaQuotCentralizer L ↔
      KFacts.IsInnerAut (thetaQuotMulAut L (compAction L ⟨a, ha⟩)) := by
  set φ := (thetaQuotMulAut L).comp (compAction L) with hφ
  set I : Subgroup G := ((MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range.comap φ).map
    (Subgroup.normalizer (L : Set G)).subtype with hI
  have hmemI : ∀ b (hb : b ∈ Subgroup.normalizer (L : Set G)), b ∈ I ↔
      KFacts.IsInnerAut (thetaQuotMulAut L (compAction L ⟨b, hb⟩)) := by
    intro b hb
    constructor
    · rintro ⟨b', hb', hbb'⟩
      have : b' = ⟨b, hb⟩ := Subtype.ext hbb'
      subst this
      exact hb'
    · intro h
      exact ⟨⟨b, hb⟩, h, rfl⟩
  constructor
  · intro hmem
    have hle : L ⊔ thetaQuotCentralizer L ≤ I := by
      refine sup_le (fun y hy => ?_) (fun c hc => ?_)
      · rw [hmemI y (mem_normalizer_of_mem hy), thetaQuotMulAut_compAction_of_mem hy]
        exact KFacts.isInnerAut_conj _
      · obtain ⟨c', hc', rfl⟩ := hc
        refine (hmemI _ c'.2).mpr ?_
        have h1 : thetaQuotMulAut L (compAction L ⟨(c' : G), c'.2⟩) = 1 := hc'
        rw [h1]
        exact ⟨1, map_one _⟩
    exact (hmemI a ha).mp (hle hmem)
  · rintro ⟨w, hw⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) w
    have hyN := mem_normalizer_of_mem y.2
    have hc : (y : G)⁻¹ * a ∈ thetaQuotCentralizer L := by
      have hN : (y : G)⁻¹ * a ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) ha
      refine ⟨⟨_, hN⟩, ?_, rfl⟩
      change thetaQuotMulAut L (compAction L ⟨(y : G)⁻¹ * a, hN⟩) = 1
      have hsplit : (⟨(y : G)⁻¹ * a, hN⟩ : Subgroup.normalizer (L : Set G)) =
          (⟨(y : G), hyN⟩)⁻¹ * ⟨a, ha⟩ := rfl
      rw [hsplit, map_mul, map_mul, map_inv, map_inv, ← hw,
        thetaQuotMulAut_compAction_of_mem y.2 hyN]
      exact inv_mul_cancel _
    have : a = (y : G) * ((y : G)⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y.2) (Subgroup.mem_sup_right hc)

theorem barCentralizer_zpowers_eq_centralizer {y : G} (hy : y ∈ L) :
    barCentralizer (Subgroup.zpowers y) L =
      Subgroup.centralizer {QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hy⟩} := by
  ext z
  rw [KFacts.mem_barCentralizer_zpowers_iff (mem_normalizer_of_mem hy),
    thetaQuotMulAut_compAction_of_mem hy, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hy⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hy⟩ * z *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hy⟩)⁻¹ *
            QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hy⟩ := by rw [h]
      _ = _ := by group
  · intro h
    rw [← h]
    group

end Inner

section Coprime

variable {G : Type*} [Group G]

theorem mem_of_pow_mem_of_coprime_three {H : Subgroup G} {x : G} {n : ℕ} (hn : Nat.Coprime n 3)
    (hxn : x ^ n ∈ H) (hx3 : x ^ 3 = 1) : x ∈ H := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime hn
  have h1 : x = (x ^ n) ^ u * (x ^ 3) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast x 3, ← zpow_mul, ← zpow_mul, ← zpow_add]
    conv_lhs => rw [← zpow_one x]
    congr 1
    linear_combination (-1 : ℤ) * huv
  rw [h1, hx3, one_zpow, mul_one]
  exact Subgroup.zpow_mem _ hxn u

theorem mul_zpow_mem_of_mem_normalizer {K : Subgroup G} {k d : G} (hk : k ∈ K)
    (hd : d ∈ Subgroup.normalizer (K : Set G)) (j : ℕ) :
    (k⁻¹ * d) ^ j * (d ^ j)⁻¹ ∈ K := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hdj : d ^ j ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hd j
    have h2 : d ^ j * k⁻¹ * (d ^ j)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hdj k⁻¹).mp (K.inv_mem hk)
    have e : (k⁻¹ * d) ^ (j + 1) * (d ^ (j + 1))⁻¹ =
        ((k⁻¹ * d) ^ j * (d ^ j)⁻¹) * (d ^ j * k⁻¹ * (d ^ j)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact K.mul_mem ih h2

theorem mem_of_mul_mem_of_coprime {K : Subgroup G} {d k t : G} (hd3 : d ^ 3 = 1)
    (hd : d ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) (hdkt : d = k * t)
    (ht : Nat.Coprime (orderOf t) 3) : d ∈ K := by
  have htd : t = k⁻¹ * d := by rw [hdkt]; group
  have h1 := mul_zpow_mem_of_mem_normalizer hk hd (orderOf t)
  rw [← htd, pow_orderOf_eq_one, one_mul] at h1
  exact mem_of_pow_mem_of_coprime_three ht (by simpa using K.inv_mem h1) hd3

theorem mem_normalizer_inSubgroup_perfectResidual [Finite G] {H : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (H : Set G)) :
    d ∈ Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  have hchar := (CFSG.perfect_residual_characterization (G := H)).2.1
  have key : ∀ x ∈ Subgroup.normalizer (H : Set G), ∀ k ∈ inSubgroup perfectResidual H,
      x * k * x⁻¹ ∈ inSubgroup perfectResidual H := by
    intro x hx k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    set σ := H.normalizerMonoidHom ⟨x, hx⟩ with hσ
    have hmap := (Subgroup.characteristic_iff_map_eq.mp hchar) σ
    refine ⟨σ k₀, ?_, rfl⟩
    rw [← hmap]
    exact ⟨k₀, hk₀, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key d hd k, fun h => ?_⟩
  have := key d⁻¹ ((Subgroup.normalizer _).inv_mem hd) _ h
  simpa [mul_assoc] using this

end Coprime

section Max

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_sup_of_commute {A S : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hS : CFSG.Assembly.IsElemAbelian 3 S) (hAS : ∀ a ∈ A, ∀ s ∈ S, a * s = s * a) :
    CFSG.Assembly.IsElemAbelian 3 (A ⊔ S) := CFSG.Open.IsElemAbelian.sup_of_commute hA hS hAS

theorem exists_le_of_fixed {A L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hY : CFSG.Assembly.IsElemAbelian 3 Y)
    (hfix : ∀ (a : G) (ha : a ∈ A), ∀ y ∈ Y,
      thetaQuotMulAut L (compAction L ⟨a, hAN ha⟩) y = y) :
    ∃ S₀ : Subgroup L, S₀.map L.subtype ≤ A ∧
      S₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) = Y ∧
      Disjoint S₀ (aschbacherSolvableCore 3 L) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  set Y₀ := Y.comap q with hY₀
  set D := Y₀.map L.subtype with hD
  have hconj : ∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
    intro a ha d hd
    obtain ⟨x, hx, rfl⟩ := hd
    have hτx : ((compAction L ⟨a, hAN ha⟩ x : L) : G) = a * x * a⁻¹ :=
      normalizerMonoidHom_apply_coe (hAN ha) x
    refine ⟨compAction L ⟨a, hAN ha⟩ x, ?_, hτx⟩
    change q (compAction L ⟨a, hAN ha⟩ x) ∈ Y
    have h1 : q (compAction L ⟨a, hAN ha⟩ x) = thetaQuotMulAut L (compAction L ⟨a, hAN ha⟩) (q x) :=
      rfl
    rw [h1, hfix a ha _ hx]
    exact hx
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨hconj a ha d, fun hd => ?_⟩
    have := hconj a⁻¹ (A.inv_mem ha) _ hd
    simpa [mul_assoc] using this
  let φ : A →* MulAut D := D.normalizerMonoidHom.comp (Subgroup.inclusion hAD)
  let _ : MulDistribMulAction A D := MulDistribMulAction.compHom D φ
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  have hcardSyl : ¬ 3 ∣ Nat.card (Sylow 3 D) := by
    intro h
    have h1 := card_sylow_modEq_one 3 D
    have h2 : Nat.card (Sylow 3 D) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq] at h1
    omega
  obtain ⟨S, hS⟩ := hAp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 D) hcardSyl
  have hSinv : ∀ a : A, ∀ s ∈ (S : Subgroup D), a • s ∈ (S : Subgroup D) := by
    intro a s hs
    have hmem : a • s ∈ ((a • S : Sylow 3 D) : Subgroup D) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨s, hs, rfl⟩
    rwa [hS a] at hmem
  set S' := (S : Subgroup D).map D.subtype with hS'
  have hS'D : S' ≤ D := Subgroup.map_subtype_le _
  have hDL : D ≤ L := Subgroup.map_subtype_le _
  set S₀ := S'.subgroupOf L with hS₀
  have hS₀map : S₀.map L.subtype = S' := by
    rw [hS₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hS'D.trans hDL)]
  have hYp : IsPGroup 3 Y := fun g => ⟨1, Subtype.ext (by simpa using hY.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hYp
  have hDcard : Nat.card D = Nat.card (aschbacherSolvableCore 3 L) * 3 ^ k := by
    rw [hD, Subgroup.card_map_of_injective L.subtype_injective, ← hk]
    exact QuotientGroup.card_preimage_mk (aschbacherSolvableCore 3 L) (Y : Set _)
  have hScard : Nat.card S = 3 ^ k := by
    rw [Sylow.card_eq_multiplicity, hDcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN3, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  have hS'card : Nat.card S' = 3 ^ k := by
    rw [hS', Subgroup.card_map_of_injective D.subtype_injective, hScard]
  have hS₀card : Nat.card S₀ = 3 ^ k := by
    rw [← hS'card, ← hS₀map, Subgroup.card_map_of_injective L.subtype_injective]
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
  have hdisj : Disjoint S₀ (aschbacherSolvableCore 3 L) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hS₀card]; exact hcop)
  have hqinj : ∀ s ∈ S₀, ∀ t ∈ S₀, q s = q t → s = t := by
    intro s hs t ht hst
    have h1 : t⁻¹ * s ∈ aschbacherSolvableCore 3 L := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
      have := (aschbacherSolvableCore 3 L).inv_mem hst
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : t⁻¹ * s ∈ S₀ ⊓ aschbacherSolvableCore 3 L :=
      ⟨S₀.mul_mem (S₀.inv_mem ht) hs, h1⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  have hS₀Y : ∀ s ∈ S₀, q s ∈ Y := by
    intro s hs
    have hsS' : (s : G) ∈ S' := hs
    obtain ⟨d, -, hd⟩ := hsS'
    have hdD : (d : G) ∈ D := d.2
    obtain ⟨x, hx, hxd⟩ := hdD
    have : x = s := Subtype.ext (hxd.trans hd)
    rw [← this]
    exact hx
  have hmapY : S₀.map q = Y := by
    refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨s, hs, hsq⟩ => hsq ▸ hS₀Y s hs) ?_
    rw [hk, ← hS₀card]
    refine Nat.card_le_card_of_injective
      (fun s : S₀ => (⟨q s, Subgroup.mem_map_of_mem q s.2⟩ : S₀.map q)) ?_
    intro s t hst
    exact Subtype.ext (hqinj s s.2 t t.2 (congrArg Subtype.val hst))
  refine ⟨S₀, ?_, hmapY, hdisj⟩
  have hAS'N : ∀ a ∈ A, ∀ s ∈ S', a * s * a⁻¹ ∈ S' := by
    rintro a ha _ ⟨s, hs, rfl⟩
    exact ⟨_, hSinv ⟨a, ha⟩ s hs, rfl⟩
  have hcent : ∀ a ∈ A, ∀ s ∈ S', a * s = s * a := by
    intro a ha s hs
    have hsL : s ∈ L := hS'D.trans hDL hs
    have has : a * s * a⁻¹ ∈ S' := hAS'N a ha s hs
    have hasL : a * s * a⁻¹ ∈ L := hS'D.trans hDL has
    have hq1 : q ⟨a * s * a⁻¹, hasL⟩ = q ⟨s, hsL⟩ := by
      have h1 : (⟨a * s * a⁻¹, hasL⟩ : L) = compAction L ⟨a, hAN ha⟩ ⟨s, hsL⟩ :=
        Subtype.ext (normalizerMonoidHom_apply_coe (hAN ha) ⟨s, hsL⟩).symm
      rw [h1]
      exact hfix a ha _ (hS₀Y ⟨s, hsL⟩ hs)
    have h2 := hqinj ⟨a * s * a⁻¹, hasL⟩ has ⟨s, hsL⟩ hs hq1
    have h3 : a * s * a⁻¹ = s := congrArg Subtype.val h2
    calc a * s = a * s * a⁻¹ * a := by group
      _ = s * a := by rw [h3]
  have hS'ab : CFSG.Assembly.IsElemAbelian 3 S' := by
    have hS'L : S' ≤ L := hS'D.trans hDL
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hx : (x : G) ∈ S₀.map L.subtype := by rw [hS₀map]; exact x.2
      have hy : (y : G) ∈ S₀.map L.subtype := by rw [hS₀map]; exact y.2
      obtain ⟨x', hx', hxx⟩ := hx
      obtain ⟨y', hy', hyy⟩ := hy
      simp only [Subgroup.coe_mul]
      rw [← hxx, ← hyy]
      have hc : x' * y' = y' * x' := by
        refine hqinj _ (S₀.mul_mem hx' hy') _ (S₀.mul_mem hy' hx') ?_
        rw [map_mul, map_mul]
        exact congrArg Subtype.val
          (hY.1.is_comm.comm ⟨q x', hS₀Y x' hx'⟩ ⟨q y', hS₀Y y' hy'⟩)
      exact congrArg Subtype.val hc
    · have hx' : x ∈ S₀.map L.subtype := by rw [hS₀map]; exact hx
      obtain ⟨x'', hx'', rfl⟩ := hx'
      have hc : x'' ^ 3 = 1 := by
        refine hqinj _ (S₀.pow_mem hx'' 3) _ S₀.one_mem ?_
        rw [map_pow, map_one]
        exact hY.2 _ (hS₀Y x'' hx'')
      simpa using congrArg Subtype.val hc
  have hsup := hAmax (A ⊔ S') (isElemAbelian_sup_of_commute hA hS'ab hcent) le_sup_left
  rw [hS₀map]
  exact le_sup_right.trans hsup.le

end Max

end Item812Res2

end CFSG.RankThree.PartTwo.Sec8
