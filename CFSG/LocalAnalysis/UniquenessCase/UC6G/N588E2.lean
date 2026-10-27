module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E1
public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588D1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.GorensteinWalter (IsComponentOf generalizedFittingSubgroupOf componentLayerOf)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

abbrev OH : Subgroup ↥m.H := CFSG.pPrimeCore m.r ↥m.H

abbrev Hbar : Type := ↥m.H ⧸ m.OH

noncomputable abbrev piH : ↥m.H →* m.Hbar := QuotientGroup.mk' m.OH

@[expose] noncomputable def bar (X : Subgroup G) : Subgroup m.Hbar :=
  (X.subgroupOf m.H).map m.piH

@[expose] noncomputable def pre (Y : Subgroup m.Hbar) : Subgroup G :=
  (Y.comap m.piH).map m.H.subtype

@[expose] noncomputable def OHG : Subgroup G := m.OH.map m.H.subtype

theorem pre_le_H (Y : Subgroup m.Hbar) : m.pre Y ≤ m.H := map_subtype_le _

theorem mem_pre {Y : Subgroup m.Hbar} {x : G} :
    x ∈ m.pre Y ↔ ∃ hx : x ∈ m.H, m.piH ⟨x, hx⟩ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨x, hx⟩, hy, rfl⟩

theorem H_le_normalizer_pre {Y : Subgroup m.Hbar} (hY : Y.Normal) :
    m.H ≤ normalizer ((m.pre Y : Subgroup G) : Set G) := by
  intro h hh
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxH, hxY⟩ := (m.mem_pre).1 hx
  refine (m.mem_pre).2 ⟨m.H.mul_mem (m.H.mul_mem hh hxH) (m.H.inv_mem hh), ?_⟩
  have : m.piH ⟨h * x * h⁻¹, m.H.mul_mem (m.H.mul_mem hh hxH) (m.H.inv_mem hh)⟩ =
      m.piH ⟨h, hh⟩ * m.piH ⟨x, hxH⟩ * (m.piH ⟨h, hh⟩)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  rw [this]
  exact hY.conj_mem _ hxY _

theorem E_le_normalizer_OHG : m.E ≤ normalizer ((m.OHG : Subgroup G) : Set G) := fun e he =>
  N588.mem_normalizer_map_of_characteristic
    (Subgroup.le_normalizer (m.hZ.E_le_centralizer he))

theorem OHG_le_M : m.OHG ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  refine m.le_M_of_coprime m.E_le_normalizer_OHG ?_
  rw [OHG, Subgroup.card_map_of_injective m.H.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd m.hr).1 CFSG.pPrimeCore_coprime_card

theorem pPrimeCore_Hbar : CFSG.pPrimeCore m.r m.Hbar = ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot m.r

theorem inf_OH_eq_bot {X : Subgroup ↥m.H} (hX : IsPGroup m.r X) : X ⊓ m.OH = ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  rw [eq_bot_iff]
  intro x hx
  have h1 : orderOf x ∣ Nat.card (m.OH) := Subgroup.orderOf_dvd_natCard _ hx.2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hX ⟨x, hx.1⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at h1
  have hcop : Nat.Coprime (m.r ^ k) (Nat.card m.OH) :=
    Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
  have h2 : m.r ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop h1
  rw [h2] at hk
  exact (mem_bot).2 (orderOf_eq_one_iff.1 hk)

theorem piH_injOn {X : Subgroup ↥m.H} (hX : IsPGroup m.r X) {x y : ↥m.H} (hx : x ∈ X)
    (hy : y ∈ X) (h : m.piH x = m.piH y) : x = y := by
  have h1 : x⁻¹ * y ∈ m.OH := by
    rw [← QuotientGroup.eq]
    exact h
  have h2 : x⁻¹ * y ∈ X ⊓ m.OH := ⟨X.mul_mem (X.inv_mem hx) hy, h1⟩
  rw [m.inf_OH_eq_bot hX, mem_bot] at h2
  calc x = x * (x⁻¹ * y) := by rw [h2, mul_one]
    _ = y := by group

theorem card_bar {X : Subgroup G} (hXH : X ≤ m.H) (hX : IsPGroup m.r X) :
    Nat.card (m.bar X) = Nat.card X := by
  have hX' : IsPGroup m.r (X.subgroupOf m.H) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  have hinj : Function.Injective (m.piH.comp (X.subgroupOf m.H).subtype) := by
    intro a b hab
    exact Subtype.ext (m.piH_injOn hX' a.2 b.2 hab)
  have h1 : m.bar X = (m.piH.comp (X.subgroupOf m.H).subtype).range := by
    rw [bar, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv

theorem bar_mono {X Y : Subgroup G} (h : X ≤ Y) : m.bar X ≤ m.bar Y :=
  Subgroup.map_mono fun _ hx => h hx

theorem mem_bar_of_mem {X : Subgroup G} {x : ↥m.H} (hx : (x : G) ∈ X) : m.piH x ∈ m.bar X :=
  ⟨x, hx, rfl⟩

theorem R_le_H (h69 : R6_9 Dat) : m.R ≤ m.H :=
  m.hZ.R_le_centralizer h69

theorem R_sylow_H (h69 : R6_9 Dat) : IsSylowOf m.r m.R m.H :=
  m.hZ.R_sylow (m.R_le_H h69)

theorem bar_R_sylow (h69 : R6_9 Dat) :
    IsSylowOf m.r (m.bar m.R) ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hRH := m.R_le_H h69
  have hsyl := m.R_sylow_H h69
  refine isSylowOf_of_card le_top ?_
  rw [m.card_bar hRH hsyl.isPGroup, hsyl.card_eq, Subgroup.card_top]
  congr 1
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (m.OH)
  have hne1 : Nat.card m.Hbar ≠ 0 := Nat.card_pos.ne'
  have hne2 : Nat.card m.OH ≠ 0 := Nat.card_pos.ne'
  have hnd : ¬ m.r ∣ Nat.card m.OH :=
    (Nat.Prime.coprime_iff_not_dvd m.hr).1 CFSG.pPrimeCore_coprime_card
  rw [show Nat.card ↥m.H = Nat.card m.Hbar * Nat.card m.OH from h1,
    Nat.factorization_mul hne1 hne2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

theorem mem_bar_A_of_pow (h69 : R6_9 Dat) {x : m.Hbar}
    (hx : x ∈ m.bar m.R) (hxr : x ^ m.r = 1) : x ∈ m.bar m.A := by
  obtain ⟨y, hyR, rfl⟩ := hx
  have hRp : IsPGroup m.r (m.R.subgroupOf m.H) :=
    (m.R_sylow_H h69).isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe (m.R_le_H h69)).symm
  have hy1 : y ^ m.r = 1 := by
    have h1 : m.piH (y ^ m.r) = m.piH 1 := by rw [map_pow, hxr, map_one]
    exact m.piH_injOn hRp (pow_mem hyR _) (Subgroup.one_mem _) h1
  have hyA : (y : G) ∈ m.A := (m.hZ.sixteen h69).2 y hyR (by
    simpa using congrArg Subtype.val hy1)
  exact m.mem_bar_of_mem hyA

theorem bar_A_comm (h69 : R6_9 Dat) {a x : m.Hbar}
    (ha : a ∈ m.bar m.A) (hx : x ∈ m.bar m.R) : a * x = x * a := by
  obtain ⟨a, haA, rfl⟩ := ha
  obtain ⟨x, hxR, rfl⟩ := hx
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext ((m.hZ.sixteen h69).1 a haA x hxR)

theorem bar_Z_comm {z : m.Hbar} (hz : z ∈ m.bar m.Z) (x : m.Hbar) : z * x = x * z := by
  obtain ⟨z, hzZ, rfl⟩ := hz
  induction x using QuotientGroup.induction_on with | H x =>
  show m.piH z * m.piH x = m.piH x * m.piH z
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.1 x.2 z hzZ)

theorem isPGroup_A : IsPGroup m.r m.A := IsPGroup.of_card (n := 3) m.card_A

theorem card_bar_A : Nat.card (m.bar m.A) = m.r ^ 3 := by
  rw [m.card_bar m.A_le_H m.isPGroup_A, m.card_A]

theorem card_bar_E : Nat.card (m.bar m.E) = m.r ^ 2 := by
  rw [m.card_bar m.hZ.E_le_centralizer (m.isPGroup_A.to_le m.E_le_A), m.d.E_card]

theorem card_bar_Z : Nat.card (m.bar m.Z) = m.r := by
  rw [m.card_bar m.Z_le_H (m.isPGroup_A.to_le m.Z_le_A), m.card_Z]

theorem centralizer_le_M_of_mem_E {e : G} (he : e ∈ m.E) (he1 : e ≠ 1) :
    centralizer ({e} : Set G) ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hEp : IsPGroup m.r m.E := m.isPGroup_A.to_le m.E_le_A
  have hp : IsPGroup m.r (zpowers e) := hEp.to_le (zpowers_le.2 he)
  have hne : zpowers e ≠ ⊥ := by rwa [Ne, zpowers_eq_bot]
  have h1 : centralizer ({e} : Set G) ≤ normalizer ((zpowers e : Subgroup G) : Set G) := by
    intro c hc
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx
    have hce : c * e = e * c := (mem_centralizer_iff.1 hc e rfl).symm
    rw [((Commute.zpow_right hce j)).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers e) j
  exact h1.trans ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 m.r m.E _
    (zpowers_le.2 he) (one_le_pRank_of_ne_bot m.hr hp hne)).trans m.d.E_gamma)

theorem pre_le_M {e : G} (he : e ∈ m.E) (he1 : e ≠ 1) {Y : Subgroup m.Hbar}
    (hY : ∀ y ∈ Y, y * m.piH ⟨e, m.hZ.E_le_centralizer he⟩ =
      m.piH ⟨e, m.hZ.E_le_centralizer he⟩ * y) : m.pre Y ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set e' : ↥m.H := ⟨e, m.hZ.E_le_centralizer he⟩ with he'
  have he'r : orderOf e' = m.r := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (m.isElemAbelian_A.2 e (m.E_le_A he)) he1
  have hQ : IsPGroup m.r (zpowers e') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he'r, pow_one])
  have hnd : ¬ m.r ∣ Nat.card m.OH :=
    (Nat.Prime.coprime_iff_not_dvd m.hr).1 CFSG.pPrimeCore_coprime_card
  have hC := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (N := m.OH) hnd hQ
  intro x hx
  obtain ⟨hxH, hxY⟩ := (m.mem_pre).1 hx
  have hxc : m.piH ⟨x, hxH⟩ ∈ centralizer (((zpowers e').map m.piH : Subgroup m.Hbar) :
      Set m.Hbar) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
    rw [map_zpow]
    exact (Commute.zpow_right (hY _ hxY) j).symm.eq
  rw [hC] at hxc
  obtain ⟨c, hc, hcx⟩ := hxc
  have hco : c⁻¹ * ⟨x, hxH⟩ ∈ m.OH := by
    rw [← QuotientGroup.eq]
    exact hcx
  have hcM : (c : G) ∈ m.M := by
    apply m.centralizer_le_M_of_mem_E he he1
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have := mem_centralizer_iff.1 hc e' (mem_zpowers e')
    exact congrArg Subtype.val this
  have hoM : ((c⁻¹ * ⟨x, hxH⟩ : ↥m.H) : G) ∈ m.M := m.OHG_le_M ⟨_, hco, rfl⟩
  have : x = (c : G) * ((c⁻¹ * ⟨x, hxH⟩ : ↥m.H) : G) := by simp
  rw [this]
  exact m.M.mul_mem hcM hoM

theorem exists_conj_le_bar_R (h69 : R6_9 Dat) {T : Subgroup m.Hbar}
    (hT : IsPGroup m.r T) : ∃ k : m.Hbar, ∀ x ∈ T, k⁻¹ * x * k ∈ m.bar m.R := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨T', hT', hTT'⟩ := exists_isSylowOf_ge (le_top : T ≤ ⊤) hT
  obtain ⟨k, -, hk⟩ := (m.bar_R_sylow h69).exists_mem_conj hT'
  exact ⟨k, fun x hx => (hk x).1 (hTT' hx)⟩

theorem conj_pow_inv (k x : m.Hbar) (n : ℕ) : (k⁻¹ * x * k) ^ n = k⁻¹ * x ^ n * k := by
  have h := map_pow (MulAut.conj k⁻¹) x n
  simpa [MulAut.conj_apply] using h.symm

theorem comm_of_pow_eq_one (h69 : R6_9 Dat) {T : Subgroup m.Hbar}
    (hT : IsPGroup m.r T) {x y : m.Hbar} (hx : x ∈ T) (hy : y ∈ T) (hxr : x ^ m.r = 1) :
    x * y = y * x := by
  obtain ⟨k, hk⟩ := m.exists_conj_le_bar_R h69 hT
  have hxA : k⁻¹ * x * k ∈ m.bar m.A := m.mem_bar_A_of_pow h69 (hk x hx) (by
    rw [m.conj_pow_inv, hxr, mul_one, inv_mul_cancel])
  have h1 := m.bar_A_comm h69 hxA (hk y hy)
  have h2 : k⁻¹ * (x * y) * k = k⁻¹ * (y * x) * k := by
    calc k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
      _ = (k⁻¹ * y * k) * (k⁻¹ * x * k) := h1
      _ = k⁻¹ * (y * x) * k := by group
  simpa using h2

theorem card_le_of_elemAbelian (h69 : R6_9 Dat) {B : Subgroup m.Hbar}
    (hB : IsElemAbelian m.r B) : Nat.card B ≤ m.r ^ 3 := by
  obtain ⟨k, hk⟩ := m.exists_conj_le_bar_R h69 (IsElemAbelian.isPGroup hB)
  have hle : B.map (MulAut.conj k⁻¹).toMonoidHom ≤ m.bar m.A := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (MulAut.conj k⁻¹).toMonoidHom x = k⁻¹ * x * k := by
      simp [MulAut.conj_apply]
    rw [hx']
    exact m.mem_bar_A_of_pow h69 (hk x hx) (by
      rw [m.conj_pow_inv, hB.2 x hx, mul_one, inv_mul_cancel])
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, m.card_bar_A] at h1
  exact h1

theorem pRank_Hbar_le_three (h69 : R6_9 Dat) (X : Subgroup m.Hbar) :
    CFSG.Open.pRank m.r X ≤ 3 := by
  refine csSup_le ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by
    rw [(mem_bot).1 hx, one_pow]⟩, by simp⟩ ?_
  rintro k ⟨B, -, hB, hcard⟩
  have h1 := m.card_le_of_elemAbelian h69 hB
  rw [hcard] at h1
  exact (Nat.pow_le_pow_iff_right m.hr.one_lt).1 h1

theorem fittingSubgroupOf_le_pCore :
    CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar) ≤
      (CFSG.pCore m.r ↥(⊤ : Subgroup m.Hbar)).map (⊤ : Subgroup m.Hbar).subtype := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  rw [CFSG.fittingSubgroupOf, CFSG.fitting_eq_sup_pCore]
  refine Subgroup.map_mono (iSup_le fun q => ?_)
  obtain ⟨⟨q, hqmem⟩, -⟩ := q
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  by_cases hqr : q = m.r
  · subst hqr
    exact le_rfl
  · haveI : Fact q.Prime := ⟨hq⟩
    have hQp : IsPGroup q (CFSG.pCore q ↥(⊤ : Subgroup m.Hbar)) := CFSG.pCore_isPGroup
    have hmap : (CFSG.pCore q ↥(⊤ : Subgroup m.Hbar)).map (⊤ : Subgroup m.Hbar).subtype ≤
        CFSG.pPrimeCore m.r m.Hbar := by
      refine le_sSup ⟨?_, ?_⟩
      · exact (inferInstance : (CFSG.pCore q ↥(⊤ : Subgroup m.Hbar)).Normal).map _
          (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
      · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hQp.map (⊤ : Subgroup m.Hbar).subtype)
        rw [hn]
        exact Nat.Coprime.pow_right n ((Nat.coprime_primes m.hr hq).2 (Ne.symm hqr))
    rw [m.pPrimeCore_Hbar] at hmap
    have hbot : CFSG.pCore q ↥(⊤ : Subgroup m.Hbar) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (⊤ : Subgroup m.Hbar).subtype_injective).1
        (le_bot_iff.1 hmap)
    rw [hbot]
    exact bot_le

theorem isPGroup_fittingSubgroupOf : IsPGroup m.r (CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar)) :=
  (CFSG.pCore_isPGroup.map _).to_le m.fittingSubgroupOf_le_pCore

theorem layer_ne_bot (h69 : R6_9 Dat) :
    componentLayerOf (⊤ : Subgroup m.Hbar) ≠ ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  intro hE
  have hF : generalizedFittingSubgroupOf (⊤ : Subgroup m.Hbar) =
      CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar) := by
    rw [generalizedFittingSubgroupOf, hE, sup_bot_eq]
    rfl
  have hC : centralizer (CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar) : Set m.Hbar) ≤
      CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar) := by
    have := CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le (G := m.Hbar)
    rwa [hF] at this
  have hcon : CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint (G := ↥m.H) m.r :=
    ⟨CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar),
      CFSG.fittingSubgroupOf_normal ⊤ inferInstance, m.isPGroup_fittingSubgroupOf, hC⟩
  have hX := CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_of_hasPrimeConstraint hcon
  exact m.hZ.not_le (m.toMc614.le_M_of_isPConstrained m.hZ h69 m.hZ.E_le_centralizer hX)

theorem le_bar_pre (Y : Subgroup m.Hbar) : Y ≤ m.bar (m.pre Y) := by
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective m.OH y
  exact ⟨x, ⟨x, hy, rfl⟩, rfl⟩

theorem pre_bar_le {W : Subgroup G} (hWH : W ≤ m.H) : m.pre (m.bar W) ≤ W ⊔ m.OHG := by
  intro x hx
  obtain ⟨hxH, hxW⟩ := (m.mem_pre).1 hx
  obtain ⟨w, hw, hwx⟩ := hxW
  have h1 : w⁻¹ * ⟨x, hxH⟩ ∈ m.OH := by
    rw [← QuotientGroup.eq]
    exact hwx
  have : x = (w : G) * ((w⁻¹ * ⟨x, hxH⟩ : ↥m.H) : G) := by simp
  rw [this]
  exact (W ⊔ m.OHG).mul_mem (mem_sup_left hw) (mem_sup_right ⟨_, h1, rfl⟩)

theorem H_ne_top_n588 : m.H ≠ ⊤ := by
  have hZ : m.Z ≠ ⊥ := by
    intro h
    have := m.card_Z
    rw [h, Subgroup.card_bot] at this
    exact m.hr.one_lt.ne this
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  intro htop
  apply centralizer_singleton_ne_top Dat.standing.simple Dat.standing.nonab hz1'
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ m.H := htop ▸ mem_top x
  rw [H, mem_centralizer_iff] at hx
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hx z hz

theorem isKGroup_Hbar : CFSG.Open.IsKGroup m.Hbar :=
  (Dat.standing.kProper.isKGroup m.H m.H_ne_top_n588).quotient m.OH

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
