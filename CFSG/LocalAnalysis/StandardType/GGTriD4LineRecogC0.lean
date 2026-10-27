module

public import CFSG.LieType.Chevalley.GraphFixedData
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGTriD4LineSL2
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofSL2
import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Short
import CFSG.Timmesfeld.Orders.Bang
import CFSG.ClassicalInvolution.Asc77.AscT3CLate10C
import CFSG.GroupTheory.ZModSqElemAbelianNine
import CFSG.Quasithin.Vol2.Ch10SecCWA
import CFSG.LieType.Chevalley.C2E6RootOperators
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.Quasithin.Background.B1Basic
import CFSG.Quasithin.Background.B2FactorizationResidual
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.H13.StatementsL6
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.RankThree.Chevalley.EvenFourCommutingSL2
import CFSG.RankThree.PartOne.KE.A1Action
import CFSG.RankThree.PartOne.KE.A1Levi
import CFSG.RankThree.PartOne.KE.A1Torus
import CFSG.RankThree.PartOne.KE.A1TwistedE6
import CFSG.RankThree.PartOne.KE.SigmaUntwisted
import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec11

private abbrev d4Root (K : Type) [Field K]
    (σ : K →+* K) : Type :=
  ↥(graphFixedRootGroup TwistTag.D4 K σ)

private noncomputable def conjAutOn {G : Type*} [Group G] (S C : Subgroup G) (hSC : S ≤ C)
    (hN : C ≤ Subgroup.normalizer (S : Set G)) : C →* MulAut S := by
  haveI : (S.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSC).mpr hN
  exact (MulAut.congr (Subgroup.subgroupOfEquivOfLe hSC)).toMonoidHom.comp
    (MulAut.conjNormal : C →* MulAut (S.subgroupOf C))

private lemma conjAutOn_apply {G : Type*} [Group G] (S C : Subgroup G) (hSC : S ≤ C)
    (hN : C ≤ Subgroup.normalizer (S : Set G)) (b : C) (u : S) :
    ((conjAutOn S C hSC hN b) u : G) = b * u * b⁻¹ := by
  simp only [conjAutOn, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulAut.conjNormal_apply, Subgroup.subgroupOfEquivOfLe_apply_coe]
  rfl

private lemma conjAutOn_eq_one_iff {G : Type*} [Group G] (S C : Subgroup G) (hSC : S ≤ C)
    (hN : C ≤ Subgroup.normalizer (S : Set G)) (b : C) :
    conjAutOn S C hSC hN b = 1 ↔ ∀ u : S, b * (u : G) * b⁻¹ = u := by
  constructor
  · intro h u
    rw [← conjAutOn_apply S C hSC hN b u, h]
    rfl
  · intro h
    ext u
    rw [conjAutOn_apply S C hSC hN b u, h u]
    rfl

private lemma map_conj_centralizer {G : Type*} [Group G] (g x : G) :
    Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g * x * g⁻¹) * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hz]
      _ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group
  · intro hy
    refine ⟨(MulAut.conj g)⁻¹ y, ?_, ?_⟩
    · rw [← map_inv (MulAut.conj) g, MulAut.conj_apply, inv_inv]
      have h1 : g⁻¹ * ((g * x * g⁻¹) * y) * g = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [hy]
      calc x * (g⁻¹ * y * g)
          = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := h1
        _ = (g⁻¹ * y * g) * x := by group
    · exact MulEquiv.apply_symm_apply _ y

private lemma card_commutator_conj {G : Type*} [Group G] (g x : G) :
    Nat.card ↥(commutator ↥(Subgroup.centralizer ({x} : Set G))) =
      Nat.card ↥(commutator ↥(Subgroup.centralizer ({g * x * g⁻¹} : Set G))) := by
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set Cy : Subgroup G := Subgroup.centralizer ({g * x * g⁻¹} : Set G) with hCy
  have hmap := map_conj_centralizer g x
  have eC : ↥Cx ≃* ↥Cy :=
    (Subgroup.equivMapOfInjective Cx (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hmap)
  have hmapc : Subgroup.map eC.toMonoidHom (commutator ↥Cx) = commutator ↥Cy := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr eC.surjective]
  exact Nat.card_congr ((Subgroup.equivMapOfInjective (commutator ↥Cx) eC.toMonoidHom
    eC.injective).trans (MulEquiv.subgroupCongr hmapc)).toEquiv

private lemma conj_pow_eq_one {G : Type*} [Group G] (g x : G) {n : ℕ} (hx : x ^ n = 1) :
    (g * x * g⁻¹) ^ n = 1 := by
  rw [show g * x * g⁻¹ = MulAut.conj g x by rw [MulAut.conj_apply], ← map_pow, hx, map_one]

private lemma conj_ne_one {G : Type*} [Group G] (g x : G) (hx : x ≠ 1) : g * x * g⁻¹ ≠ 1 := by
  intro h
  refine hx ((MulAut.conj g).injective ?_)
  have h' : MulAut.conj g x = 1 := by rw [MulAut.conj_apply]; exact h
  rw [h', map_one]

private lemma map_pow_eq_one {M N : Type*} [Group M] [Group N] (e : M ≃* N) {x : M} {n : ℕ}
    (hx : x ^ n = 1) : (e x) ^ n = 1 := by rw [← map_pow, hx, map_one]

private lemma map_ne_one {M N : Type*} [Group M] [Group N] (e : M ≃* N) {x : M} (hx : x ≠ 1) :
    e x ≠ 1 := fun h => hx (e.injective (by rw [h, map_one]))

private lemma exists_good_prime (n : ℕ) (hn : 2 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∧
      ¬ r ∣ (2 ^ n) ^ 2 - 1 ∧ ¬ r ∣ 3 * n := by
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    subst hn2
    exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · have hk2 : 2 ≤ 3 * n := by omega
    have hk6 : 3 * n ≠ 6 := by omega
    obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 3 * n) hk2 hk6
    have hp3n : 0 < 3 * n := by omega
    have hp2 : p ≠ 2 := hp.ne_two hp3n
    have hfac : 2 ^ (3 * n) - 1 = (2 ^ n - 1) * ((2 ^ n) ^ 2 + 2 ^ n + 1) := by
      rw [show 2 ^ (3 * n) = (2 ^ n) ^ 3 by rw [mul_comm 3 n, pow_mul]]
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub (one_le_pow₀ (Nat.one_le_two_pow (n := n))), Nat.cast_mul,
        Nat.cast_sub (Nat.one_le_two_pow (n := n))]
      push_cast
      ring
    have hpn : ¬ p ∣ 2 ^ n - 1 := by
      rw [hp.dvd_sub_one_iff hp3n n]
      exact fun h => absurd (Nat.le_of_dvd (by omega : 0 < n) h) (by omega)
    have hpm : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 := by
      have h1 : p ∣ (2 ^ n - 1) * ((2 ^ n) ^ 2 + 2 ^ n + 1) := hfac ▸ hp.dvd
      exact (hp.prime.dvd_mul.mp h1).resolve_left hpn
    have hp22 : ¬ p ∣ (2 ^ n) ^ 2 - 1 := by
      rw [show (2 ^ n) ^ 2 - 1 = 2 ^ (2 * n) - 1 by rw [← pow_mul, mul_comm],
        hp.dvd_sub_one_iff hp3n (2 * n)]
      exact fun h => absurd (Nat.le_of_dvd (by omega : 0 < 2 * n) h) (by omega)
    have hp3n' : ¬ p ∣ 3 * n := by
      haveI : Fact p.Prime := ⟨hp.prime⟩
      have hpow : (2 : ZMod p) ^ (3 * n) = 1 :=
        (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (3 * n)).mp hp.dvd
      have hdvd : orderOf (2 : ZMod p) ∣ 3 * n := orderOf_dvd_of_pow_eq_one hpow
      have hdvd' : 3 * n ∣ orderOf (2 : ZMod p) := by
        rw [← hp.dvd_sub_one_iff hp3n]
        exact (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mpr (pow_orderOf_eq_one _)
      have hord : orderOf (2 : ZMod p) = 3 * n := Nat.dvd_antisymm hdvd hdvd'
      have hdiv : orderOf (2 : ZMod p) ∣ p - 1 :=
        ZMod.orderOf_dvd_card_sub_one (CFSG.Timmesfeld.Bang.two_ne_zero_zmod hp2)
      have hle : 3 * n ≤ p - 1 := by
        rw [← hord]
        exact Nat.le_of_dvd (by have := hp.prime.two_le; omega) hdiv
      exact fun h => absurd (Nat.le_of_dvd hp3n h) (by omega)
    exact ⟨p, hp.prime, hp2, hpm, hp22, hp3n'⟩

theorem triD4Line_conj_z0_of_torus_C0
    (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (z₀ e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hz3 : orderOf z₀ = 3)
    (he : orderOf e = 3)
    (hz₀' : ¬ Nat.card (commutator (Subgroup.centralizer {z₀})) ∣
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1))
    (T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hT : T ≤ Subgroup.centralizer {e})
    (hTiso : Nonempty (T ≃* Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1)) ×
      Multiplicative (ZMod ((2 ^ n) ^ 2 + 2 ^ n + 1)))) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g * e * g⁻¹ = z₀ := by
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite (d4Root K σ.toRingHom) := Subtype.finite
  haveI : Fintype K := Fintype.ofFinite K
  set q : ℕ := 2 ^ n with hq
  have h3q : ¬ 3 ∣ q := by
    rw [hq]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hF : Nat.card K = 2 ^ (3 * n) := by
    rw [hK, hq, ← pow_mul, show n * 3 = 3 * n by ring]
  haveI : CharP K 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := 3 * n)
    rw [← Nat.card_eq_fintype_card, hF]
  have h3K : (3 : K) ≠ 0 := fun h =>
    (by norm_num : ¬ (2 ∣ 3)) ((CharP.cast_eq_zero_iff K 2 3).mp h)
  have hσ3 : σ ^ 3 = 1 := by
    apply RingEquiv.ext
    intro c
    rw [ringEquiv_pow_three_apply]
    change σ (σ (σ c)) = c
    calc σ (σ (σ c)) = σ (σ (c ^ q)) := by rw [hσ c]
      _ = σ ((c ^ q) ^ q) := by rw [hσ (c ^ q)]
      _ = ((c ^ q) ^ q) ^ q := by rw [hσ ((c ^ q) ^ q)]
      _ = c ^ (q * (q * q)) := by rw [← pow_mul, ← pow_mul]
      _ = c ^ Nat.card K := by congr 1; rw [hK]; ring
      _ = c := by rw [Nat.card_eq_fintype_card]; exact FiniteField.pow_card c
  obtain ⟨ε⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148B.Res148BD4.nonempty_sl2_equiv_short (K := K) hσ3
  let S : Subgroup (d4Root K σ.toRingHom) := KS11Lie4Proof.d4ShortSL2 K σ.toRingHom
  have hcardS : Nat.card S = q ^ 3 * (q ^ 6 - 1) := by
    change Nat.card (KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) = q ^ 3 * (q ^ 6 - 1)
    rw [← Nat.card_congr ε.toEquiv, CFSG.ClassicalInvolution.Asc77.T3CII.card_sl2_eq, hK,
      show ((q ^ 3) ^ 2) = q ^ 6 by ring]
  have hz3' : z₀ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hz3])
  have hz1 : z₀ ≠ 1 := by rintro rfl; rw [orderOf_one] at hz3; omega
  have hzS : ∃ g : (d4Root K σ.toRingHom), g * z₀ * g⁻¹ ∈ S := by
    obtain ⟨g₀, hg₀⟩ := KS11Lie6Proof.d4ThreeConj_holds K q σ hK hσ h3q z₀ hz3' hz1
    rcases hg₀ with hmemS | hmemC
    · exact ⟨g₀, hmemS⟩
    · exfalso
      let s : (d4Root K σ.toRingHom) := g₀ * z₀ * g₀⁻¹
      let C : Subgroup (d4Root K σ.toRingHom) := Subgroup.centralizer ({s} : Set _)
      have hsC : s ∈ Subgroup.centralizer (S : Set _) := hmemC
      have hs3 : s ^ 3 = 1 := conj_pow_eq_one g₀ z₀ hz3'
      have hs1 : s ≠ 1 := conj_ne_one g₀ z₀ hz1
      have hBC := (KS11Lie6Proof.d4ThreeBCent_holds K q σ hK hσ h3q s hsC hs3 hs1).1
      have hmap_comm : Subgroup.map C.subtype (commutator ↥C) = ⁅C, C⁆ := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      have hle : Subgroup.map C.subtype (commutator ↥C) ≤ S := by
        rw [hmap_comm, Subgroup.commutator_le]
        exact fun x hx y hy => by rw [commutatorElement_def]; exact hBC x hx y hy
      have hdvd : Nat.card ↥(commutator ↥C) ∣ Nat.card S := by
        rw [← Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      have hcard_eq : Nat.card ↥(commutator ↥(Subgroup.centralizer ({z₀} : Set _))) =
          Nat.card ↥(commutator ↥C) := card_commutator_conj g₀ z₀
      apply hz₀'
      rw [hcard_eq]
      rwa [hcardS] at hdvd
  obtain ⟨r, hr, hr2, hrm, hrq2, hr3n⟩ := exists_good_prime n hn
  have he3' : e ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [he])
  have he1 : e ≠ 1 := by rintro rfl; rw [orderOf_one] at he; omega
  have heS : ∃ g : (d4Root K σ.toRingHom), g * e * g⁻¹ ∈ S := by
    obtain ⟨g₁, hg₁⟩ := KS11Lie6Proof.d4ThreeConj_holds K q σ hK hσ h3q e he3' he1
    rcases hg₁ with hmemS | hmemC
    · exact ⟨g₁, hmemS⟩
    · exfalso
      let s : (d4Root K σ.toRingHom) := g₁ * e * g₁⁻¹
      let C : Subgroup (d4Root K σ.toRingHom) := Subgroup.centralizer ({s} : Set _)
      have hsC : s ∈ Subgroup.centralizer (S : Set _) := hmemC
      have hs3 : s ^ 3 = 1 := conj_pow_eq_one g₁ e he3'
      have hs1 : s ≠ 1 := conj_ne_one g₁ e he1
      have hBC := KS11Lie6Proof.d4ThreeBCent_holds K q σ hK hσ h3q s hsC hs3 hs1
      have hcomm := hBC.1
      have hexp := hBC.2
      have hSC : S ≤ C := fun u hu =>
        Subgroup.mem_centralizer_iff.mpr (fun h hh => by
          rw [Set.mem_singleton_iff] at hh; subst hh
          exact ((Subgroup.mem_centralizer_iff.mp hsC) u hu).symm)
      have hCN : C ≤ Subgroup.normalizer (S : Set _) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        refine fun u => ⟨fun hu => ?_, fun hu => ?_⟩
        · have hcu := hcomm x hx u (hSC hu)
          rw [show x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u by group]
          exact S.mul_mem hcu hu
        · have hvC : x * u * x⁻¹ ∈ C := hSC hu
          have hcu := hcomm x⁻¹ (inv_mem hx) (x * u * x⁻¹) hvC
          have h1 : x⁻¹ * (x * u * x⁻¹) * x ∈ S := by
            rw [show x⁻¹ * (x * u * x⁻¹) * x =
              (x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ * (x * u * x⁻¹)⁻¹) *
                (x * u * x⁻¹) by group]
            exact S.mul_mem hcu hu
          rwa [show x⁻¹ * (x * u * x⁻¹) * x = u by group] at h1
      let ρ : C →* MulAut S := conjAutOn S C hSC hCN
      let ρ' : C →* MulAut (Matrix.SpecialLinearGroup (Fin 2) K) :=
        (MulAut.congr ε.symm).toMonoidHom.comp ρ
      let A : Subgroup (d4Root K σ.toRingHom) := Subgroup.map (MulAut.conj g₁).toMonoidHom T
      have hA_le : A ≤ C := by
        intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨t, htT, rfl⟩ := hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        change (g₁ * t * g₁⁻¹) * s = s * (g₁ * t * g₁⁻¹)
        have ht := Subgroup.mem_centralizer_singleton_iff.mp (hT htT)
        calc (g₁ * t * g₁⁻¹) * s = g₁ * (t * e) * g₁⁻¹ := by
              rw [show s = g₁ * e * g₁⁻¹ from rfl]; group
          _ = g₁ * (e * t) * g₁⁻¹ := by rw [ht]
          _ = s * (g₁ * t * g₁⁻¹) := by
              rw [show s = g₁ * e * g₁⁻¹ from rfl]; group
      have eA : ↥A ≃* Multiplicative (ZMod (q ^ 2 + q + 1) × ZMod (q ^ 2 + q + 1)) :=
        (Subgroup.equivMapOfInjective T (MulAut.conj g₁).toMonoidHom
          (MulAut.conj g₁).injective).symm.trans
          (hTiso.some.trans (MulEquiv.prodMultiplicative (ZMod (q ^ 2 + q + 1))
            (ZMod (q ^ 2 + q + 1))).symm)
      obtain ⟨E, hEA, hEel, hEcard⟩ :=
        CFSG.GroupTheory.exists_isElemAbelian_card_prime_sq_of_mulEquiv_zmod_sq eA hr hrm
      have hEC : E ≤ C := hEA.trans hA_le
      haveI : Fact r.Prime := ⟨hr⟩
      have hexpE : ∀ x : E, x ^ r = 1 := fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hEel.2 x x.2)
      obtain ⟨eE⟩ := CFSG.Quasithin.Vol2.Ch10.CW.nonempty_mulEquiv_zmod_prod hEcard hexpE
      let eE' : Multiplicative (ZMod r) × Multiplicative (ZMod r) ≃* E :=
        (MulEquiv.prodMultiplicative (ZMod r) (ZMod r)).symm.trans eE.symm
      let ι : Multiplicative (ZMod r) × Multiplicative (ZMod r) →* C :=
        (Subgroup.inclusion hEC).comp eE'.toMonoidHom
      let φ : Multiplicative (ZMod r) × Multiplicative (ZMod r) →*
          MulAut (Matrix.SpecialLinearGroup (Fin 2) K) := ρ'.comp ι
      have hφinj : Function.Injective φ := by
        rw [injective_iff_map_eq_one]
        intro a ha
        have hρa : ρ (ι a) = 1 := by
          have h1 : (MulAut.congr ε.symm) (ρ (ι a)) = 1 := by show φ a = 1; exact ha
          exact (MulAut.congr ε.symm).injective (by rw [h1, map_one])
        have hcen := (conjAutOn_eq_one_iff S C hSC hCN (ι a)).mp hρa
        have hb : (ι a : (d4Root K σ.toRingHom)) ∈ Subgroup.centralizer (S : Set _) := by
          rw [Subgroup.mem_centralizer_iff]
          intro u hu
          calc u * (ι a : (d4Root K σ.toRingHom))
              = ((ι a) * u * (ι a)⁻¹) * (ι a) := by rw [hcen ⟨u, hu⟩]
            _ = (ι a) * u := by simp only [Subgroup.coe_inv]; group
        have hbq : (ι a : (d4Root K σ.toRingHom)) ^ (q ^ 2 - 1) = 1 := hexp (ι a) (ι a).2 hb
        have hbr : (ι a : (d4Root K σ.toRingHom)) ^ r = 1 := by
          have h4 : (eE' a) ^ r = 1 := hexpE (eE' a)
          have h5 : ((eE' a : E) : (d4Root K σ.toRingHom)) ^ r = 1 := by
            rw [← Subgroup.coe_pow, h4, Subgroup.coe_one]
          rw [show ((ι a : C) : (d4Root K σ.toRingHom)) =
            ((eE' a : E) : (d4Root K σ.toRingHom)) from rfl]
          exact h5
        have hcop : Nat.Coprime r (q ^ 2 - 1) := (hr.coprime_iff_not_dvd).mpr hrq2
        have hb1 : (ι a : (d4Root K σ.toRingHom)) = 1 := by
          have hdvd : orderOf (ι a : (d4Root K σ.toRingHom)) ∣ Nat.gcd r (q ^ 2 - 1) :=
            Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hbr) (orderOf_dvd_of_pow_eq_one hbq)
          rw [hcop.gcd_eq_one] at hdvd
          exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
        have hιa : ι a = 1 := Subtype.ext hb1
        have hι₁a : eE' a = 1 := by
          apply Subtype.ext
          exact congrArg (fun x : C => (x : (d4Root K σ.toRingHom))) hιa
        exact eE'.injective (by rw [hι₁a, map_one])
      exact (triD4Line_not_injective_mulAut_SL2 K (3 * n) hF r hr hr2 hr3n φ) hφinj
  obtain ⟨g₀, hg₀S⟩ := hzS
  obtain ⟨g₁, hg₁S⟩ := heS
  let s₀ : (d4Root K σ.toRingHom) := g₀ * z₀ * g₀⁻¹
  let s₁ : (d4Root K σ.toRingHom) := g₁ * e * g₁⁻¹
  have hs₀3 : s₀ ^ 3 = 1 := conj_pow_eq_one g₀ z₀ hz3'
  have hs₀1 : s₀ ≠ 1 := conj_ne_one g₀ z₀ hz1
  have hs₁3 : s₁ ^ 3 = 1 := conj_pow_eq_one g₁ e he3'
  have hs₁1 : s₁ ≠ 1 := conj_ne_one g₁ e he1
  let S₀ : S := ⟨s₀, hg₀S⟩
  let S₁ : S := ⟨s₁, hg₁S⟩
  have hS₀3 : S₀ ^ 3 = 1 := by
    apply Subtype.ext; rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hs₀3
  have hS₀1 : S₀ ≠ 1 := fun h => hs₀1 (congrArg Subtype.val h)
  have hS₁3 : S₁ ^ 3 = 1 := by
    apply Subtype.ext; rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hs₁3
  have hS₁1 : S₁ ≠ 1 := fun h => hs₁1 (congrArg Subtype.val h)
  let B₀ : Matrix.SpecialLinearGroup (Fin 2) K := ε.symm S₀
  let B₁ : Matrix.SpecialLinearGroup (Fin 2) K := ε.symm S₁
  have hB₀3 : B₀ ^ 3 = 1 := map_pow_eq_one ε.symm hS₀3
  have hB₀1 : B₀ ≠ 1 := map_ne_one ε.symm hS₀1
  have hB₁3 : B₁ ^ 3 = 1 := map_pow_eq_one ε.symm hS₁3
  have hB₁1 : B₁ ≠ 1 := map_ne_one ε.symm hS₁1
  obtain ⟨A, hA⟩ :=
    Item1118Res3Proof.exists_conj_of_pow_three (F := K) h3K hB₁3 hB₁1 hB₀3 hB₀1
  let u : (d4Root K σ.toRingHom) := ε A
  have hB₀coe : ((ε B₀ : S) : (d4Root K σ.toRingHom)) = s₀ := by
    rw [show B₀ = ε.symm S₀ from rfl, MulEquiv.apply_symm_apply]
  have hB₁coe : ((ε B₁ : S) : (d4Root K σ.toRingHom)) = s₁ := by
    rw [show B₁ = ε.symm S₁ from rfl, MulEquiv.apply_symm_apply]
  have hus : u * s₁ * u⁻¹ = s₀ := by
    have h2 : ((ε (A * B₁ * A⁻¹) : S) : (d4Root K σ.toRingHom)) =
        ((ε B₀ : S) : (d4Root K σ.toRingHom)) :=
      congrArg Subtype.val (congrArg (fun x => ε x) hA)
    rw [show (ε (A * B₁ * A⁻¹) : S) = ε A * ε B₁ * (ε A)⁻¹ by
      rw [map_mul, map_mul, map_inv]] at h2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hB₀coe, hB₁coe] at h2
    exact h2
  refine ⟨g₀⁻¹ * u * g₁, ?_⟩
  calc (g₀⁻¹ * u * g₁) * e * (g₀⁻¹ * u * g₁)⁻¹
      = g₀⁻¹ * u * (g₁ * e * g₁⁻¹) * u⁻¹ * g₀ := by group
    _ = g₀⁻¹ * u * s₁ * u⁻¹ * g₀ := by rw [show s₁ = g₁ * e * g₁⁻¹ from rfl]
    _ = g₀⁻¹ * s₀ * g₀ := by rw [← hus]; group
    _ = z₀ := by rw [show s₀ = g₀ * z₀ * g₀⁻¹ from rfl]; group

end CFSG.StandardType
