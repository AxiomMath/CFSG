module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.GroupTheory.PCore.FixedSubgroupCore
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k891hcompex_pprimeCore_sup_eq_bot {E : Type*} [Group E] [Finite E]
    (p : ℕ) [Fact p.Prime] (A : Subgroup E) (hA : A ≤ Subgroup.center E)
    (hAp : IsPGroup p A) :
    let : A.Normal := Subgroup.normal_of_le_center hA
    let : (pPrimeCore p E ⊔ A).Normal := Subgroup.sup_normal _ _
    pPrimeCore p (E ⧸ (pPrimeCore p E ⊔ A)) = ⊥ := by
  let : A.Normal := Subgroup.normal_of_le_center hA
  let : (pPrimeCore p E ⊔ A).Normal := Subgroup.sup_normal _ _
  let q : E →* E ⧸ pPrimeCore p E := QuotientGroup.mk' (pPrimeCore p E)
  set Abar : Subgroup (E ⧸ pPrimeCore p E) := A.map q with hAbar
  have hAbar_center : Abar ≤ Subgroup.center (E ⧸ pPrimeCore p E) := by
    rw [hAbar]
    exact (Subgroup.map_mono hA).trans
      (Subgroup.map_center_le_center (f := q) (QuotientGroup.mk'_surjective (pPrimeCore p E)))
  have hAbar_p : IsPGroup p Abar := by
    rw [hAbar]
    exact hAp.map q
  have hVcore : pPrimeCore p (E ⧸ pPrimeCore p E) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Fact.out
  have hcore : pPrimeCore p ((E ⧸ pPrimeCore p E) ⧸ Abar) = ⊥ :=
    CFSG.Semidihedral.OddCoreQuotient.pPrimeCore_quotient_eq_bot_of_central p Abar
      hAbar_center hAbar_p hVcore
  have hAbar_eq : Abar = (pPrimeCore p E ⊔ A).map q := by
    rw [hAbar, Subgroup.map_sup]
    have hVbot : (pPrimeCore p E).map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hVbot, bot_sup_eq]
  let e : (E ⧸ pPrimeCore p E) ⧸ Abar ≃* E ⧸ (pPrimeCore p E ⊔ A) :=
    (QuotientGroup.quotientMulEquivOfEq hAbar_eq).trans
      (QuotientGroup.quotientQuotientEquivQuotient (pPrimeCore p E) (pPrimeCore p E ⊔ A)
        le_sup_left)
  exact pPrimeCore_eq_bot_of_mulEquiv p e hcore

private theorem k891hcompex_star_pprimeCore {G : Type} [Group G] [Finite G] (H Z : Subgroup G)
    (hZH : Z ≤ H) (hZcent : Z ≤ Subgroup.centralizer (H : Set G))
    (hZ3 : Nat.card Z = 3) :
    pPrimeCore 3 (↥H ⧸ R891Ker H Z) = ⊥ := by
  let V : Subgroup ↥H := pPrimeCore 3 ↥H
  let Zs : Subgroup ↥H := Z.subgroupOf H
  have hZs_center : Zs ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hZcent (Subgroup.mem_subgroupOf.mp hz))
      (h : G) h.2)
  have : Zs.Normal := Subgroup.normal_of_le_center hZs_center
  have hcard : Nat.card Zs = 3 := by
    rw [show Nat.card Zs = Nat.card Z from CFSG.natCard_subgroupOf_eq Z H hZH, hZ3]
  have hZs_p : IsPGroup 3 Zs := IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hker : R891Ker H Z = V ⊔ Zs := by
    unfold R891Ker
    rw [normalClosure_union, normalClosure_eq_self, normalClosure_eq_self]
  have hcore : pPrimeCore 3 (↥H ⧸ (V ⊔ Zs)) = ⊥ := by
    have : (V ⊔ Zs).Normal := Subgroup.sup_normal V Zs
    exact k891hcompex_pprimeCore_sup_eq_bot 3 Zs hZs_center hZs_p
  have e : (↥H ⧸ R891Ker H Z) ≃* (↥H ⧸ (V ⊔ Zs)) :=
    QuotientGroup.quotientMulEquivOfEq hker
  exact pPrimeCore_eq_bot_of_mulEquiv 3 e.symm hcore

private theorem k891hcompex_cQ_eq_map_Z {G : Type} [Group G] [Finite G]
    (X Z : Subgroup G) (hZX : Z ≤ X) (hZcX : Z ≤ Subgroup.centralizer (X : Set G))
    (_hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) (hZ3 : Nat.card Z = 3) :
    Subgroup.center (Bar2 X) =
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Z.subgroupOf X) := by
  set O2X : Subgroup ↥X := CFSG.pCore 2 ↥X with hO2X
  set Zi : Subgroup ↥X := Z.subgroupOf X with hZi
  let q : ↥X →* Bar2 X := QuotientGroup.mk' O2X
  have hZi_center : Zi ≤ Subgroup.center ↥X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hZcX (Subgroup.mem_subgroupOf.mp hz)) (x : G) x.2)
  have hmap_le : Zi.map q ≤ Subgroup.center (Bar2 X) := by
    rw [hZi]
    exact ((Subgroup.map_mono hZi_center).trans
      (Subgroup.map_center_le_center (f := q) (QuotientGroup.mk'_surjective O2X)))
  have hZi_card : Nat.card Zi = 3 := by
    rw [hZi, CFSG.natCard_subgroupOf_eq _ _ hZX, hZ3]
  have hmap_card_dvd : Nat.card (Zi.map q) ∣ 3 := by
    rw [← hZi_card]
    exact Subgroup.card_map_dvd Zi q
  have hmap_card_ne_one : Nat.card (Zi.map q) ≠ 1 := by
    intro h1
    have hbot : Zi.map q = ⊥ := Subgroup.eq_bot_of_card_eq (H := Zi.map q) h1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
    have h3dvd : 3 ∣ Nat.card O2X := by
      have h := Subgroup.card_dvd_of_le hbot
      rwa [hZi_card] at h
    rw [hk] at h3dvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3dvd) (by norm_num)
  have hmap_card : Nat.card (Zi.map q) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hmap_card_dvd with h | h
    · exact absurd h hmap_card_ne_one
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hmap_card, hcQ3])).symm

private theorem k891hcompex_inf_pprimeCore_le_pCore {G : Type} [Group G] [Finite G]
    (H X : Subgroup G) (hXH : X ≤ H)
    (hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) :
    ((CFSG.pPrimeCore 3 ↥H).map H.subtype).subgroupOf X ≤ CFSG.pCore 2 ↥X := by
  set Vg : Subgroup G := (CFSG.pPrimeCore 3 ↥H).map H.subtype with hVg
  let q : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  set M : Subgroup (Bar2 X) := (Vg.subgroupOf X).map q with hM
  have hconjV : ∀ h ∈ H, ∀ v ∈ Vg, h * v * h⁻¹ ∈ Vg := by
    intro h hh v hv
    rw [hVg] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    have := CFSG.pPrimeCore_normal.conj_mem w hw (⟨h, hh⟩ : ↥H)
    exact Subgroup.mem_map_of_mem H.subtype this
  have hsubXNorm : (Vg.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconjV (g : G) (hXH g.2) (n : G) hn
  have hMnorm : M.Normal := by
    rw [hM]
    exact hsubXNorm.map q (QuotientGroup.mk'_surjective _)
  have hVcop : Nat.Coprime 3 (Nat.card Vg) := by
    rw [hVg, Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
  have hMcard_cop : Nat.Coprime 3 (Nat.card M) := by
    have hcard1 : Nat.card M ∣ Nat.card (Vg.subgroupOf X) := Subgroup.card_map_dvd _ q
    have hcard2 : Nat.card (Vg.subgroupOf X) = Nat.card ↥(Vg ⊓ X) := by
      have h := Subgroup.card_map_of_injective (K := Vg.subgroupOf X) (f := X.subtype)
        X.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype Vg X] at h
      exact h.symm
    have hcard3 : Nat.card ↥(Vg ⊓ X) ∣ Nat.card Vg := Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.of_dvd_right (hcard1.trans (hcard2 ▸ hcard3)) hVcop
  have h3dvdQ : 3 ∣ Nat.card (Bar2 X) := by
    rw [← hcQ3, ← Subgroup.card_top (G := Bar2 X)]
    exact Subgroup.card_dvd_of_le (le_top : Subgroup.center (Bar2 X) ≤ ⊤)
  have hQ' : CFSG.IsQuasisimple (Bar2 X) :=
    ⟨Group.isPerfect_def.2 hQ.1, hQ.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hQ⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ' hMnorm with htop | hcen
  · exfalso
    have hcopQ : Nat.Coprime 3 (Nat.card (Bar2 X)) := by
      rw [← Subgroup.card_top (G := Bar2 X)]
      rw [htop] at hMcard_cop
      exact hMcard_cop
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hcopQ) h3dvdQ
  · have hMcard_dvd : Nat.card M ∣ 3 := by
      rw [← hcQ3]
      exact Subgroup.card_dvd_of_le hcen
    have hMcard : Nat.card M = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hMcard_dvd with h | h
      · exact h
      · exfalso
        rw [h] at hMcard_cop
        exact (Nat.prime_three.coprime_iff_not_dvd.mp hMcard_cop) dvd_rfl
    have hMbot : M = ⊥ := Subgroup.eq_bot_of_card_eq (H := M) hMcard
    rw [hM] at hMbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hMbot
    exact hMbot

private theorem k891hcompex_fker_le_gker {G : Type} [Group G] [Finite G]
    (H X Z : Subgroup G) (hXH : X ≤ H) (hZX : Z ≤ X)
    (hZcX : Z ≤ Subgroup.centralizer (X : Set G))
    (hZcH : Z ≤ Subgroup.centralizer (H : Set G)) (hZ3 : Nat.card Z = 3)
    (hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) :
    ((QuotientGroup.mk' (R891Ker H Z)).comp (Subgroup.inclusion hXH)).ker ≤
      ((QuotientGroup.mk' (Subgroup.center (Bar2 X))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).ker := by
  intro x hx
  have hxN : (⟨(x : G), hXH x.2⟩ : ↥H) ∈ R891Ker H Z := by
    have h := MonoidHom.mem_ker.mp hx
    rw [MonoidHom.comp_apply] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  let V : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let Zs : Subgroup ↥H := Z.subgroupOf H
  have : V.Normal := CFSG.pPrimeCore_normal
  have hZs_center : Zs ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hZcH (Subgroup.mem_subgroupOf.mp hz)) (h : G) h.2)
  have : Zs.Normal := Subgroup.normal_of_le_center hZs_center
  have hkerN : R891Ker H Z = V ⊔ Zs := by
    unfold R891Ker
    rw [normalClosure_union, normalClosure_eq_self, normalClosure_eq_self]
  rw [hkerN] at hxN
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hxN
  have hbZ : (b : G) ∈ Z := Subgroup.mem_subgroupOf.mp hb
  have haV : (a : G) ∈ V.map H.subtype := Subgroup.mem_map_of_mem H.subtype ha
  have habG : (a : G) * (b : G) = (x : G) := by
    have := congrArg (fun y : ↥H => (y : G)) hab
    simpa using this
  have haX : (a : G) ∈ X := by
    have h : (a : G) = (x : G) * (b : G)⁻¹ := by rw [← habG]; group
    rw [h]
    exact X.mul_mem x.2 (X.inv_mem (hZX hbZ))
  have hbX : (b : G) ∈ X := hZX hbZ
  let a' : ↥X := ⟨(a : G), haX⟩
  let b' : ↥X := ⟨(b : G), hbX⟩
  have habX : a' * b' = x := by
    apply Subtype.ext
    simpa [a', b'] using habG
  have ha'O : a' ∈ CFSG.pCore 2 ↥X := by
    refine k891hcompex_inf_pprimeCore_le_pCore H X hXH hQ hcQ3 ?_
    rw [Subgroup.mem_subgroupOf]
    exact haV
  have hb'cQ : QuotientGroup.mk' (CFSG.pCore 2 ↥X) b' ∈ Subgroup.center (Bar2 X) := by
    have hb'Zi : b' ∈ Z.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      exact hbZ
    rw [k891hcompex_cQ_eq_map_Z X Z hZX hZcX hQ hcQ3 hZ3]
    exact Subgroup.mem_map_of_mem _ hb'Zi
  have hqa : QuotientGroup.mk' (CFSG.pCore 2 ↥X) a' = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ha'O
  have hqx : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈ Subgroup.center (Bar2 X) := by
    rw [← habX, map_mul, hqa, one_mul]
    exact hb'cQ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact (QuotientGroup.eq_one_iff _).mpr hqx

private theorem k891hcompex_gker_eq {G : Type} [Group G] [Finite G]
    (X Z : Subgroup G) (hZX : Z ≤ X) (hZcX : Z ≤ Subgroup.centralizer (X : Set G))
    (hQ : CFSG.Open.IsQuasisimple (Bar2 X))
    (hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3) (hZ3 : Nat.card Z = 3) :
    ((QuotientGroup.mk' (Subgroup.center (Bar2 X))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).ker =
      CFSG.pCore 2 ↥X ⊔ Z.subgroupOf X := by
  have hcQ := k891hcompex_cQ_eq_map_Z X Z hZX hZcX hQ hcQ3 hZ3
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcQ,
    Subgroup.comap_map_eq (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Z.subgroupOf X),
    QuotientGroup.ker_mk', sup_comm]

private theorem k891hcompex_X_le_H {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (_hst : R891State D L S R A n) :
    R891X L (R891Z L S) n ≤ R891H L S := by
  have hn1 : n ≠ 1 := by omega
  rw [R891X, if_neg hn1]
  exact (Subgroup.map_subtype_le _).trans inf_le_right

private theorem k891hcompex_Z_le_X {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (_hn : 2 ≤ n) (hst : R891State D L S R A n) :
    R891Z L S ≤ R891X L (R891Z L S) n :=
  hst.ctx.xShape.zLe.trans hst.ctx.xShape.rLe

private theorem k891hcompex_X_perfect {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (_hst : R891State D L S R A n) :
    Group.IsPerfect ↥(R891X L (R891Z L S) n) := by
  have hn1 : n ≠ 1 := by omega
  rw [R891X, if_neg hn1]
  have hperf : Group.IsPerfect ↥((⨅ k : ℕ, derivedSeries
      ↥(L ⊓ Subgroup.centralizer (R891Z L S : Set G)) k) :
        Subgroup ↥(L ⊓ Subgroup.centralizer (R891Z L S : Set G))) :=
    CFSG.perfect_residual_characterization.2.2.1
  have := hperf
  exact Group.IsPerfect.map (L ⊓ Subgroup.centralizer (R891Z L S : Set G)).subtype

private theorem k891hcompex_Bar2_quasisimple {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    CFSG.Open.IsQuasisimple (Bar2 (R891X L (R891Z L S) n)) := by
  rcases hst.ctx.xShape.xShape with ⟨h1, -⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩
  · omega
  · exact hc.1
  · exact hc.1

private theorem k891hcompex_center_Bar2_card {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    Nat.card (Subgroup.center (Bar2 (R891X L (R891Z L S) n))) = 3 := by
  rcases hst.ctx.xShape.xShape with ⟨h1, -⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩
  · omega
  · exact hc.2.1
  · exact hc.2.1

private theorem k891hcompex_f_range {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    ((QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))).comp
        (Subgroup.inclusion (k891hcompex_X_le_H D L S R A n hn hst))).range =
      R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, hxy⟩

private theorem k891hcompex_phi {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    ∃ φ : ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) →*
        (Bar2 (R891X L (R891Z L S) n) ⧸
          Subgroup.center (Bar2 (R891X L (R891Z L S) n))),
      Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := R891H L S with hH
  set Z : Subgroup G := R891Z L S with hZ
  set X : Subgroup G := R891X L Z n with hX
  set N : Subgroup ↥H := R891Ker H Z with hN
  have hXH : X ≤ H := k891hcompex_X_le_H D L S R A n hn hst
  have hZX : Z ≤ X := k891hcompex_Z_le_X D L S R A n hn hst
  have hZcH : Z ≤ Subgroup.centralizer (H : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hH] at hh
    exact (Subgroup.mem_centralizer_iff.mp hh z hz).symm
  have hZcX : Z ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hXH hx) z hz).symm
  have hZ3 : Nat.card Z = 3 := hst.basic.zOrder
  have hQ : CFSG.Open.IsQuasisimple (Bar2 X) := k891hcompex_Bar2_quasisimple D L S R A n hn hst
  have hcQ3 : Nat.card (Subgroup.center (Bar2 X)) = 3 :=
    k891hcompex_center_Bar2_card D L S R A n hn hst
  let f : ↥X →* (↥H ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.inclusion hXH)
  have hfmem : ∀ x : ↥X, f x ∈ R891Img H Z X := fun x =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hfrange : f.range = R891Img H Z X := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hfmem x
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, hxy⟩
  let g : ↥X →* (Bar2 X ⧸ Subgroup.center (Bar2 X)) :=
    (QuotientGroup.mk' (Subgroup.center (Bar2 X))).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  have hle : f.ker ≤ g.ker := k891hcompex_fker_le_gker H X Z hXH hZX hZcX hZcH hZ3 hQ hcQ3
  let he : (↥X ⧸ f.ker) ≃* ↥(R891Img H Z X) :=
    (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange)
  have hZs_center : Z.subgroupOf H ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hZcH (Subgroup.mem_subgroupOf.mp hz)) (h : G) h.2)
  have : (Z.subgroupOf H).Normal := Subgroup.normal_of_le_center hZs_center
  have hkerN : R891Ker H Z = CFSG.pPrimeCore 3 ↥H ⊔ Z.subgroupOf H := by
    unfold R891Ker
    rw [normalClosure_union, normalClosure_eq_self, normalClosure_eq_self]
  have hZi_le_fker : Z.subgroupOf X ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    have : (CFSG.pPrimeCore 3 ↥H).Normal := CFSG.pPrimeCore_normal
    have hzN : (⟨(z : G), hXH z.2⟩ : ↥H) ∈ R891Ker H Z := by
      rw [hkerN]
      refine Subgroup.mem_sup_of_normal_left.mpr ⟨1, Subgroup.one_mem _, ?_⟩
      refine ⟨⟨(z : G), hXH z.2⟩, ?_, ?_⟩
      · exact hz
      · simp
    exact hzN
  have he_apply : ∀ x : ↥X, (he (QuotientGroup.mk' f.ker x) : R891Star H Z) = f x :=
    fun x => rfl
  let gbar : (↥X ⧸ f.ker) →* (Bar2 X ⧸ Subgroup.center (Bar2 X)) :=
    QuotientGroup.lift f.ker g hle
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Bar2 X)) y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) z
    exact ⟨x, rfl⟩
  have hgbar : Function.Surjective gbar :=
    QuotientGroup.lift_surjective_of_surjective (N := f.ker) g hg hle
  let φ : ↥(R891Img H Z X) →* (Bar2 X ⧸ Subgroup.center (Bar2 X)) :=
    gbar.comp he.symm.toMonoidHom
  have hφ_surj : Function.Surjective φ := hgbar.comp he.symm.surjective
  have hφ_apply : ∀ x : ↥X, φ ⟨f x, hfmem x⟩ = g x := by
    intro x
    have h1 : he.symm ⟨f x, hfmem x⟩ = QuotientGroup.mk' f.ker x := by
      apply he.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact he_apply x
    change gbar (he.symm ⟨f x, hfmem x⟩) = g x
    rw [h1]
    rfl
  have hgker : g.ker = CFSG.pCore 2 ↥X ⊔ Z.subgroupOf X :=
    k891hcompex_gker_eq X Z hZX hZcX hQ hcQ3 hZ3
  have hφker_le : φ.ker ≤ ((CFSG.pCore 2 ↥X).map f).subgroupOf (R891Img H Z X) := by
    intro y hy
    have hyval : (y : R891Star H Z) ∈ f.range := by
      rw [hfrange]; exact y.2
    obtain ⟨x, hxy⟩ := MonoidHom.mem_range.mp hyval
    have hy_eq : y = ⟨f x, hfmem x⟩ := by
      apply Subtype.ext
      exact hxy.symm
    have hgx : g x = 1 := by
      have := MonoidHom.mem_ker.mp hy
      rw [hy_eq, hφ_apply] at this
      exact this
    have hx_gker : x ∈ g.ker := MonoidHom.mem_ker.mpr hgx
    rw [hgker] at hx_gker
    have hfx_mem : f x ∈ (CFSG.pCore 2 ↥X).map f := by
      have h := Subgroup.mem_map_of_mem f hx_gker
      rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff (H := Z.subgroupOf X) (f := f)).mpr hZi_le_fker, sup_bot_eq] at h
    rw [Subgroup.mem_subgroupOf]
    rw [← hxy]
    exact hfx_mem
  have hO2le : (CFSG.pCore 2 ↥X).map f ≤ R891Img H Z X :=
    (Subgroup.map_le_range _ _).trans (le_of_eq hfrange)
  have hO2sub_2 : IsPGroup 2 (((CFSG.pCore 2 ↥X).map f).subgroupOf (R891Img H Z X)) := by
    have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map f
    exact h.of_equiv (Subgroup.subgroupOfEquivOfLe hO2le).symm
  exact ⟨φ, hφ_surj, hO2sub_2.to_le hφker_le⟩

private theorem k891hcompex_Xstar_ne_bot {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≠ ⊥ := by
  obtain ⟨φ, hφ, -⟩ := k891hcompex_phi D L S R A n hn hst
  intro hbot
  have hSnonab : ∃ a b : (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))), a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
      (k891hcompex_Bar2_quasisimple D L S R A n hn hst)
  obtain ⟨a, b, hab⟩ := hSnonab
  obtain ⟨y, hy⟩ := hφ a
  have : Subsingleton ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)) := by
    rw [hbot]; infer_instance
  have hy1 : y = 1 := Subsingleton.elim y 1
  have ha1 : a = 1 := by rw [← hy, hy1, map_one]
  obtain ⟨w, hw⟩ := hφ b
  have hw1 : w = 1 := Subsingleton.elim w 1
  have hb1 : b = 1 := by rw [← hw, hw1, map_one]
  exact hab (by rw [ha1, hb1])

private theorem k891hcompex_Xstar_inf_pCore_eq_bot {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ⊓
      CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S)) = ⊥ := by
  classical
  obtain ⟨ψ, hψ, hψker⟩ := k891hcompex_phi D L S R A n hn hst
  let Xstar : Subgroup (R891Star (R891H L S) (R891Z L S)) :=
    R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)
  let P3 : Subgroup ↥Xstar :=
    (CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S))).subgroupOf Xstar
  have hP3_3 : IsPGroup 3 P3 := by
    refine (CFSG.pCore_isPGroup (p := 3) (G := R891Star (R891H L S) (R891Z L S))).of_injective
      { toFun := fun y => ⟨(y : ↥Xstar).val, y.2⟩, map_one' := rfl,
        map_mul' := fun x y => rfl } ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg
      (fun z : ↥(CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S))) =>
        (z : R891Star (R891H L S) (R891Z L S))) h))
  have : P3.Normal := inferInstance
  have hSsimple : IsSimpleGroup (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) :=
    (k891hcompex_Bar2_quasisimple D L S R A n hn hst).2
  have hSnonab : ∃ a b : (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))), a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
      (k891hcompex_Bar2_quasisimple D L S R A n hn hst)
  have hnot3S : ¬ IsPGroup 3 (Bar2 (R891X L (R891Z L S) n) ⧸
      Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := by
    intro hp3
    have : IsSimpleGroup (Bar2 (R891X L (R891Z L S) n) ⧸
        Subgroup.center (Bar2 (R891X L (R891Z L S) n))) := hSsimple
    have hcenter_ne : Subgroup.center (Bar2 (R891X L (R891Z L S) n) ⧸
        Subgroup.center (Bar2 (R891X L (R891Z L S) n))) ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).mp (hp3.center_nontrivial)
    have hcenter_top : Subgroup.center (Bar2 (R891X L (R891Z L S) n) ⧸
        Subgroup.center (Bar2 (R891X L (R891Z L S) n))) = ⊤ := by
      rcases hSsimple.eq_bot_or_eq_top_of_normal
        (Subgroup.center (Bar2 (R891X L (R891Z L S) n) ⧸
          Subgroup.center (Bar2 (R891X L (R891Z L S) n)))) with h | h
      · exact absurd h hcenter_ne
      · exact h
    have hcomm : IsMulCommutative (Bar2 (R891X L (R891Z L S) n) ⧸
        Subgroup.center (Bar2 (R891X L (R891Z L S) n))) :=
      Subgroup.center_eq_top_iff.mp hcenter_top
    obtain ⟨a, b, hab⟩ := hSnonab
    exact hab ((isMulCommutative_iff.mp hcomm) a b)
  have himg_bot : (P3.map ψ) = ⊥ := by
    have hnorm : (P3.map ψ).Normal := (inferInstance : P3.Normal).map ψ hψ
    have : (P3.map ψ).Normal := hnorm
    rcases hSsimple.eq_bot_or_eq_top_of_normal (P3.map ψ) with h | h
    · exact h
    · exfalso
      exact hnot3S ((h ▸ hP3_3.map ψ).of_equiv (Subgroup.topEquiv))
  have hP3bot : P3 = ⊥ := by
    have hle : P3 ≤ ψ.ker := (Subgroup.map_eq_bot_iff (H := P3) (f := ψ)).mp himg_bot
    have hP3_2 : IsPGroup 2 P3 := hψker.to_le hle
    obtain ⟨a, ha⟩ := hP3_3.exists_card_eq
    obtain ⟨b, hb⟩ := hP3_2.exists_card_eq
    have hcard : Nat.card P3 = 1 := by
      have h : 3 ^ a = 2 ^ b := by rw [← ha, ← hb]
      have hb0 : b = 0 := by
        by_contra hb0
        have hdvd : 2 ∣ 3 ^ a := by rw [h]; exact dvd_pow_self 2 hb0
        exact absurd (Nat.prime_two.dvd_of_dvd_pow hdvd) (by norm_num)
      have ha0 : a = 0 := by
        by_contra ha0
        have hdvd : 3 ∣ 2 ^ b := by rw [← h]; exact dvd_pow_self 3 ha0
        exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)
      rw [ha0, pow_zero] at ha
      exact ha
    exact Subgroup.eq_bot_of_card_eq (H := P3) hcard
  have hTstar_bot : Xstar ⊓ CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, (Subgroup.mem_inf.mp hy).1⟩ : ↥Xstar) ∈ P3 := by
      show (y : R891Star (R891H L S) (R891Z L S)) ∈
        CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S))
      exact (Subgroup.mem_inf.mp hy).2
    rw [hP3bot] at hy'
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hy')
  exact hTstar_bot

private theorem k891hcompex_pCore_le_Mstar {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n) :
    CFSG.pCore 3 (R891Star (R891H L S) (R891Z L S)) ≤
      R891Img (R891H L S) (R891Z L S) D.M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := R891H L S with hH
  set Z : Subgroup G := R891Z L S with hZ
  set Ker : Subgroup ↥H := R891Ker H Z with hKer
  have hAH : A ≤ H := hst.ctx.aLeR.trans (hst.ctx.xShape.rLe.trans
    (k891hcompex_X_le_H D L S R A n hn hst))
  have hA3 : IsPGroup 3 ↥(A.subgroupOf H) :=
    (IsPGroup.of_card (n := 1) (by rw [hst.ctx.classes.aOrder]; norm_num)).comap_of_injective
      H.subtype H.subtype_injective
  obtain ⟨Q, hAQ⟩ := hA3.exists_le_sylow
  let P : Subgroup G := (Q : Subgroup ↥H).map H.subtype
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 P H := ⟨Q, rfl⟩
  have hAP : A ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAH]
    exact Subgroup.map_mono hAQ
  have hPM : P ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hst.uniq hAP hP.isPGroup
  have hQeq : (Q : Subgroup ↥H) = P.subgroupOf H := by
    rw [show P = (Q : Subgroup ↥H).map H.subtype from rfl, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hQleDM : (Q : Subgroup ↥H) ≤ D.M.subgroupOf H := by
    rw [hQeq]
    intro x hx
    exact hPM (Subgroup.mem_subgroupOf.mp hx)
  let Qs : Sylow 3 (R891Star H Z) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective Ker) Q
  have hpc : CFSG.pCore 3 (R891Star H Z) ≤ (Qs : Subgroup (R891Star H Z)) :=
    CFSG.Glauberman.pCore_le_sylow Qs
  have hcoe : (Qs : Subgroup (R891Star H Z)) =
      (Q : Subgroup ↥H).map (QuotientGroup.mk' Ker) := rfl
  rw [hcoe] at hpc
  exact hpc.trans (Subgroup.map_mono hQleDM)

theorem s891_h_comp_ex {G : Type} [Group G] [Finite G] (D : Data G) (L S R A : Subgroup G) (n : ℕ)
    (hn : 2 ≤ n) (hst : R891State D L S R A n) (hnorm : R891Norm895 D L S n) :
    ∃ Ys : Subgroup (R891Star (R891H L S) (R891Z L S)), IsComponentOf Ys ⊤ ∧ 3 ∣ Nat.card Ys ∧
      ¬ R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ centralizer ((Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) : Set (R891Star (R891H L S) (R891Z L S))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := R891H L S with hH
  set Z : Subgroup G := R891Z L S with hZ
  set X : Subgroup G := R891X L Z n with hX
  set Xstar : Subgroup (R891Star H Z) := R891Img H Z X with hXstar
  have hZH : Z ≤ H := by
    intro z hz
    rw [hH, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hZ] at hz
    exact (Subgroup.mem_centralizer_iff.mp hw.2 z hz.1).symm
  have hZcH : Z ≤ Subgroup.centralizer (H : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hH] at hh
    exact (Subgroup.mem_centralizer_iff.mp hh z hz).symm
  have hZ3 : Nat.card Z = 3 := hst.basic.zOrder
  have hcore : CFSG.pPrimeCore 3 (R891Star H Z) = ⊥ :=
    k891hcompex_star_pprimeCore H Z hZH hZcH hZ3
  by_contra hcon
  push Not at hcon
  have h3comp : ∀ Ys : Subgroup (R891Star H Z), IsComponentOf Ys ⊤ → 3 ∣ Nat.card Ys := by
    intro Ys hYs
    by_contra h3
    have hcop : Nat.Coprime 3 (Nat.card Ys) := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    have hcomp : CFSG.IsComponent Ys := (CFSG.isComponent_iff_open Ys).mpr hYs
    have hle : Ys ≤ CFSG.pPrimeCore 3 (R891Star H Z) :=
      CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hcomp.2 hcop
    rw [hcore] at hle
    have hbot : Ys = ⊥ := le_bot_iff.mp hle
    have hnt : Nontrivial ↥Ys := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
    exact (Subgroup.nontrivial_iff_ne_bot Ys).mp hnt hbot
  have hcentE : Xstar ≤ Subgroup.centralizer (CFSG.layer (R891Star H Z) : Set (R891Star H Z)) := by
    rw [CFSG.layer.eq_sSup, Subgroup.le_centralizer_iff]
    refine sSup_le fun K hK => ?_
    exact (Subgroup.le_centralizer_iff).mpr
      (hcon K ((CFSG.isComponent_iff_open K).mp hK) (h3comp K ((CFSG.isComponent_iff_open K).mp hK)))
  have hcentOp : Xstar ≤ Subgroup.centralizer
      (CFSG.pCore 3 (R891Star H Z) : Set (R891Star H Z)) := by
    have : (CFSG.pCore 3 (R891Star H Z)).Normal := CFSG.pCore_normal
    have hle_inf : Xstar ⊓ CFSG.pCore 3 (R891Star H Z) = ⊥ :=
      k891hcompex_Xstar_inf_pCore_eq_bot D L S R A n hn hst
    have hMnorm : R891Img H Z D.M ≤ Subgroup.normalizer (Xstar : Set (R891Star H Z)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hnorm.1).mp hnorm.2
    have hcore_le_M : CFSG.pCore 3 (R891Star H Z) ≤ R891Img H Z D.M :=
      k891hcompex_pCore_le_Mstar D L S R A n hn hst
    have hcomm : ⁅Xstar, CFSG.pCore 3 (R891Star H Z)⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [Subgroup.commutator_le]
      intro g hg k hk
      have hkx : ⁅g, k⁆ ∈ Xstar := by
        have hkM : k ∈ R891Img H Z D.M := hcore_le_M hk
        have hconj : k * g⁻¹ * k⁻¹ ∈ Xstar :=
          (Subgroup.mem_normalizer_iff.mp (hMnorm hkM) g⁻¹).1 (Xstar.inv_mem hg)
        have hdef : ⁅g, k⁆ = g * (k * g⁻¹ * k⁻¹) := by
          rw [commutatorElement_def]; group
        rw [hdef]
        exact Xstar.mul_mem hg hconj
      have hkp : ⁅g, k⁆ ∈ CFSG.pCore 3 (R891Star H Z) := by
        have hle : ⁅Xstar, CFSG.pCore 3 (R891Star H Z)⁆ ≤ CFSG.pCore 3 (R891Star H Z) :=
          Subgroup.commutator_le_right Xstar (CFSG.pCore 3 (R891Star H Z))
        exact hle (Subgroup.commutator_mem_commutator hg hk)
      have hmem : ⁅g, k⁆ ∈ Xstar ⊓ CFSG.pCore 3 (R891Star H Z) := ⟨hkx, hkp⟩
      rw [hle_inf] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcentF : Xstar ≤ Subgroup.centralizer
      (CFSG.fittingSubgroup (R891Star H Z) : Set (R891Star H Z)) := by
    rw [CFSG.Fitting_eq_pcore (R891Star H Z) 3 hcore]
    exact hcentOp
  have hcentGF : Xstar ≤ Subgroup.centralizer
      (CFSG.generalizedFitting (R891Star H Z) : Set (R891Star H Z)) := by
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.le_centralizer_iff]
    exact sup_le ((Subgroup.le_centralizer_iff).mpr hcentF)
      ((Subgroup.le_centralizer_iff).mpr hcentE)
  have hXF : Xstar ≤ CFSG.generalizedFitting (R891Star H Z) :=
    hcentGF.trans (CFSG.centralizer_generalizedFitting_le (R891Star H Z))
  have hcomm_self : Xstar ≤ Subgroup.centralizer (Xstar : Set (R891Star H Z)) :=
    hcentGF.trans (Subgroup.centralizer_le (by intro x hx; exact hXF hx))
  have hperfect : Group.IsPerfect ↥(R891Img (R891H L S) (R891Z L S)
      (R891X L (R891Z L S) n)) := by
    have hXperf : Group.IsPerfect ↥X := k891hcompex_X_perfect D L S R A n hn hst
    have := hXperf
    have hXH : X ≤ H := k891hcompex_X_le_H D L S R A n hn hst
    let f0 : ↥X →* (↥H ⧸ R891Ker H Z) :=
      (QuotientGroup.mk' (R891Ker H Z)).comp (Subgroup.inclusion hXH)
    let f' : ↥X →* ↥(R891Img H Z X) := f0.codRestrict _ fun x =>
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
    have hf'surj : Function.Surjective f' := by
      intro y
      have hy : (y : R891Star H Z) ∈ f0.range := by
        rw [show f0.range = R891Img H Z X from k891hcompex_f_range D L S R A n hn hst]
        exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
    have h := Group.IsPerfect.ofSurjective hf'surj
    change Group.IsPerfect ↥(R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n))
    exact h
  have hbot : Xstar = ⊥ := by
    have h1 : ⁅Xstar, Xstar⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm_self
    have h2 : ⁅Xstar, Xstar⁆ = Xstar := Subgroup.isPerfect_iff.mp hperfect
    rw [← h2, h1]
  exact k891hcompex_Xstar_ne_bot D L S R A n hn hst hbot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
