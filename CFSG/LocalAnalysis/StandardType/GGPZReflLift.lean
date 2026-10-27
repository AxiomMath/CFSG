module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pzl_relIndex_top {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    H.relIndex ⊤ = H.index := by
  have h1 : H.relIndex ⊤ * Nat.card ↥H = Nat.card G := by
    have h := Subgroup.relIndex_mul_card H (⊤ : Subgroup G)
    rwa [inf_top_eq, Subgroup.card_top] at h
  have h2 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have hcomm : Nat.card ↥H * H.relIndex ⊤ = Nat.card ↥H * H.index := by
    rw [Nat.mul_comm (Nat.card ↥H) (H.relIndex ⊤), h1, h2]
  exact Nat.mul_left_cancel hpos hcomm

private theorem pzl_mem_core_of_mem_coreOf {G : Type} [Group G] {p : ℕ} {J : Subgroup G}
    {x : ↥J} (hx : (x : G) ∈ LargeEvenPPrimeCoreOf p J) :
    x ∈ LargeEvenPPrimeCore p ↥J := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  rwa [show y = x from Subtype.ext hyx] at hy

private theorem pzl_coreOf_le_center_map {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {J : Subgroup G} (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hpJ : p ∣ Nat.card ↥J) :
    LargeEvenPPrimeCoreOf p J ≤ (Subgroup.center ↥J).map J.subtype := by
  have hle : LargeEvenPPrimeCoreOf p J ≤ J := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hnorm : J ≤ Subgroup.normalizer (LargeEvenPPrimeCoreOf p J : Set G) :=
    (Subgroup.le_normalizer (H := J)).trans (ggNormalizer_le_normalizer_pPrimeCoreOf p J)
  rcases ggLe_center_or_eq_of_normalized hJq hle hnorm with hcent | heq
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hle hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcent hx) (k : G) k.2
  · exfalso
    have hcard : Nat.card ↥J = Nat.card (LargeEvenPPrimeCoreOf p J) :=
      (congrArg (fun K : Subgroup G => Nat.card ↥K) heq).symm
    have hcop : Nat.Coprime p (Nat.card ↥J) := by
      rw [hcard]
      exact ggPPrimeCoreOf_coprime J
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop hpJ

private theorem pzl_core_le_center {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {J : Subgroup G} (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hpJ : p ∣ Nat.card ↥J) :
    LargeEvenPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
  have hmap := pzl_coreOf_le_center_map hJq hpJ
  intro x hx
  have hxcore : (x : G) ∈ LargeEvenPPrimeCoreOf p J :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp (hmap hxcore)
  rwa [show c = x from Subtype.ext hcx] at hc

private theorem pzl_mem_center_of_commutator_le_center {K : Type} [Group K] {a : K}
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hcommZ : ∀ k : K, ⁅a, k⁆ ∈ Subgroup.center K) :
    a ∈ Subgroup.center K := by
  let Z := Subgroup.center K
  have hZcomm : ∀ u v : Z, u * v = v * u := by
    intro u v
    exact Subtype.ext (Subgroup.mem_center_iff.mp v.2 (u : K))
  let φ : K →* Z :=
    { toFun := fun k => ⟨⁅a, k⁆, hcommZ k⟩
      map_one' := by
        apply Subtype.ext
        show ⁅a, 1⁆ = 1
        rw [commutatorElement_def]
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show ⁅a, x * y⁆ = ⁅a, x⁆ * ⁅a, y⁆
        have h : x * ⁅a, y⁆ * x⁻¹ = ⁅a, y⁆ := by
          have h2 := Subgroup.mem_center_iff.mp (hcommZ y) x
          rw [h2, mul_assoc, mul_inv_cancel, mul_one]
        have hid : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [hid, h] }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff]
    rw [← hperf]
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker]
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hZcomm (φ x) (φ y))
  rw [Subgroup.mem_center_iff]
  intro j
  have hj : φ j = 1 := by
    have hmem : j ∈ φ.ker := by rw [hker]; exact Subgroup.mem_top j
    exact MonoidHom.mem_ker.mp hmem
  have hval : ⁅a, j⁆ = 1 := by
    have hcoe := congrArg (fun z : Z => (z : K)) hj
    simpa [φ] using hcoe
  exact (commutatorElement_eq_one_iff_mul_comm.mp hval).symm

theorem ggPZ_reflLift {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E J Y : Subgroup G} {z g : G} (hE : IsElemAbelian p E)
    (hY : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) Y) (hJY : J ≤ Y)
    (hJq : IsQuasisimple ↥J) (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hl : p ^ 2 ≤ Nat.card ↥(E ⊓ J)) (hgz : g ∈ Subgroup.centralizer ({z} : Set G))
    (hrefl : Nat.card {b : ↥E // g * (b : G) * g⁻¹ = (b : G)} * p = Nat.card ↥E) :
    g ∈ Subgroup.normalizer (Y : Set G) := by
  classical
  by_contra hgY
  let H : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let Y' : Subgroup G := Y.map (MulAut.conj g).toMonoidHom
  have hY' : LargeEvenPComponent p H Y' := by
    have h := largeEvenPComponent_map_conj' hY g
    rwa [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgz)] at h
  have hne : Y' ≠ Y := fun h => hgY (mem_normalizer_iff_map_conj.mpr h)
  let FE : Subgroup ↥E :=
    { carrier := {b : ↥E | g * (b : G) * g⁻¹ = (b : G)}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        show g * ((x : G) * (y : G)) * g⁻¹ = (x : G) * (y : G)
        calc g * ((x : G) * (y : G)) * g⁻¹
            = (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹) := by group
          _ = (x : G) * (y : G) := by rw [hx, hy]
      inv_mem' := by
        intro x hx
        show g * ((x : G)⁻¹) * g⁻¹ = ((x : G)⁻¹)
        calc g * ((x : G)⁻¹) * g⁻¹ = (g * (x : G) * g⁻¹)⁻¹ := by group
          _ = ((x : G))⁻¹ := by rw [hx] }
  have hFEcard : Nat.card ↥FE * p = Nat.card ↥E := by simpa [FE] using hrefl
  have hFEindex : FE.index = p := by
    have hcard := Subgroup.card_mul_index FE
    exact Nat.mul_left_cancel Nat.card_pos (hcard.trans hFEcard.symm)
  let AE : Subgroup ↥E := (E ⊓ J).subgroupOf E
  have hcardAE : Nat.card ↥AE = Nat.card ↥(E ⊓ J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ J ≤ E)).toEquiv
  have hreltop : FE.relIndex ⊤ = FE.index := pzl_relIndex_top FE
  have hrelle : FE.relIndex AE ≤ p := by
    have h1 : FE.relIndex AE ≤ FE.relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right (K := AE) (L := ⊤) le_top (by
        rw [hreltop, hFEindex]
        exact (Fact.out : p.Prime).ne_zero)
    rwa [hreltop, hFEindex] at h1
  have hrelcard := Subgroup.relIndex_mul_card (FE ⊓ AE) AE
  have hinf : (FE ⊓ AE) ⊓ AE = FE ⊓ AE := by
    rw [inf_assoc, inf_idem]
  have hr : (FE ⊓ AE).relIndex AE ≤ p := by
    rw [Subgroup.inf_relIndex_right FE AE]
    exact hrelle
  have hbig : p * p ≤ (FE ⊓ AE).relIndex AE * Nat.card ↥(FE ⊓ AE) := by
    have h := hrelcard
    rw [hinf] at h
    calc p * p = p ^ 2 := by rw [pow_two]
      _ ≤ Nat.card ↥(E ⊓ J) := hl
      _ = Nat.card ↥AE := hcardAE.symm
      _ = (FE ⊓ AE).relIndex AE * Nat.card ↥(FE ⊓ AE) := h.symm
  have hcard_ge : p ≤ Nat.card ↥(FE ⊓ AE) := by
    have h1 : (FE ⊓ AE).relIndex AE * Nat.card ↥(FE ⊓ AE) ≤
        p * Nat.card ↥(FE ⊓ AE) := Nat.mul_le_mul_right _ hr
    exact Nat.le_of_mul_le_mul_left (le_trans hbig h1) (Fact.out : p.Prime).pos
  have hcard2 : 2 ≤ Nat.card ↥(FE ⊓ AE) := (Fact.out : p.Prime).two_le.trans hcard_ge
  haveI : Fintype ↥(FE ⊓ AE) := Fintype.ofFinite _
  have hfintype : 1 < Fintype.card ↥(FE ⊓ AE) := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨b, hbne⟩ := Fintype.exists_ne_of_one_lt_card hfintype (1 : ↥(FE ⊓ AE))
  obtain ⟨hbFE, hbAE⟩ := Subgroup.mem_inf.mp b.2
  set a : G := (b : G) with ha
  have haE : a ∈ E := by simpa [ha] using (b : ↥E).2
  have haAJ : a ∈ E ⊓ J := by simpa [ha] using Subgroup.mem_subgroupOf.mp hbAE
  have haJ : a ∈ J := haAJ.2
  have haFix : g * a * g⁻¹ = a := by simpa [FE, ha] using hbFE
  have ha1 : a ≠ 1 := by
    intro h
    apply hbne
    apply Subtype.ext
    apply Subtype.ext
    simpa [ha] using h
  have hap : a ^ p = 1 := hE.2 a haE
  have haY' : a ∈ Y' := by
    rw [← haFix]
    exact Subgroup.mem_map.mpr ⟨a, hJY haJ, rfl⟩
  have hcomm_all : ∀ j ∈ J, ⁅a, j⁆ ∈ LargeEvenPPrimeCoreOf p J :=
    commutator_mem_largeEvenPPrimeCoreOf_of_mem_inf hY hY' hne.symm hJY haJ haY'
  let aJ : ↥J := ⟨a, haJ⟩
  have hcommN : ∀ j : ↥J, ⁅aJ, j⁆ ∈ LargeEvenPPrimeCore p ↥J := by
    intro j
    apply pzl_mem_core_of_mem_coreOf
    have h := hcomm_all (j : G) j.2
    simpa [aJ, commutatorElement_def] using h
  have hJqA : CFSG.Assembly.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mpr hJq
  have hpJ : p ∣ Nat.card ↥J := by
    have hord : orderOf a = p := orderOf_eq_prime hap ha1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard J haJ
  have hNZ : LargeEvenPPrimeCore p ↥J ≤ Subgroup.center ↥J :=
    pzl_core_le_center hJqA hpJ
  have haCenter : aJ ∈ Subgroup.center ↥J := by
    refine pzl_mem_center_of_commutator_le_center (a := aJ) ?_ ?_
    · simpa [commutator_def] using hJqA.1
    · intro j
      exact hNZ (hcommN j)
  have hdvd : p ∣ Nat.card ↥(Subgroup.center ↥J) := by
    have hord : orderOf aJ = p := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        simpa [aJ] using hap
      · intro h
        apply ha1
        simpa [aJ] using congrArg Subtype.val h
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard (Subgroup.center ↥J) haCenter
  exact hZ hdvd

end CFSG.StandardType

end
