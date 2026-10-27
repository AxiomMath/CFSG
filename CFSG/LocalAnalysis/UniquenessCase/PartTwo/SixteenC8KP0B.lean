module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KE64
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeElementLifting
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (I9 Hbar9 BarO3)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

private lemma c8k_card_elemAbelian {P : Type} [Group P] (N : Subgroup P)
    (hN : IsElemAbelianOfRank 2 6 ↥N) : Nat.card N = 64 := by
  obtain ⟨e⟩ := hN
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

private lemma c8k_conj_mem_Opp (p : ℕ) {Y : Subgroup G} {y : G} (hy : y ∈ Y)
    {x : G} (hx : x ∈ Opp p Y) : y * x * y⁻¹ ∈ Opp p Y := by
  have h1 : Opp p Y ≤ (Opp p Y).comap (MulAut.conj y).toMonoidHom := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    obtain ⟨hzY, n, hn⟩ := hz
    exact ⟨by
        show y * z * y⁻¹ ∈ Y
        exact Y.mul_mem (Y.mul_mem hy hzY) (Y.inv_mem hy),
      n, (MulEquiv.orderOf_eq (MulAut.conj y) z).trans hn⟩
  have h2 := Subgroup.mem_comap.mp (h1 hx)
  show y * x * y⁻¹ ∈ Opp p Y
  exact h2

private lemma c8k_Opp_subgroupOf_normal (p : ℕ) (Y : Subgroup G) :
    ((Opp p Y).subgroupOf Y).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact c8k_conj_mem_Opp p y.2 hx

theorem c8k_x_l3 {Y C : Subgroup G} (hCY : C ≤ Y) (hC3 : ¬ 3 ∣ Nat.card C) (hP : C8P0 Y C) :
    LieModel (BarO3 (Opp 3 Y)) .PSL 3 2 1 := by
  classical
  obtain ⟨P, _, φ, hφs, hφk, ⟨N, hNn, hN64, hL3⟩, -⟩ := hP
  haveI := hNn
  haveI : Finite P := Finite.of_surjective φ hφs
  have hL3' : LieModel (P ⧸ N) .PSL 3 2 1 := hL3
  have hsimple :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hL3'
  have hLcard : Nat.card (P ⧸ N) = 168 := hsimple.2
  have hsimp : IsSimpleGroup (P ⧸ N) := hsimple.1
  let θ : ↥Y →* P ⧸ N := (QuotientGroup.mk' N).comp φ
  have hθs : Function.Surjective θ := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨y, hy⟩ := hφs p
    exact ⟨y, by dsimp only [θ]; rw [MonoidHom.comp_apply, hy]⟩
  have hθker : Nat.card θ.ker = Nat.card C * 64 := by
    have h1 : Nat.card θ.ker * Nat.card (P ⧸ N) = Nat.card ↥Y :=
      Subgroup.card_ker_mul_card_of_surjective (f := θ) hθs
    have h2 : Nat.card φ.ker * Nat.card P = Nat.card ↥Y :=
      Subgroup.card_ker_mul_card_of_surjective (f := φ) hφs
    have hφker : Nat.card φ.ker = Nat.card C := by
      rw [hφk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY).toEquiv
    have hPcard : Nat.card P = Nat.card (P ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hLcard] at h1
    rw [hφker, hPcard, c8k_card_elemAbelian N hN64, hLcard] at h2
    have hcancel : Nat.card θ.ker * 168 = (Nat.card C * 64) * 168 := by
      rw [h1, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hcancel
  have hθker3 : ¬ 3 ∣ Nat.card θ.ker := by
    rw [hθker]
    intro h
    rcases (Nat.prime_three.dvd_mul.mp h) with h | h
    · exact hC3 h
    · exact absurd h (by norm_num)
  have hXY : Opp 3 Y ≤ Y := (Subgroup.closure_le Y).mpr fun _ hz => hz.1
  let ψ : ↥(Opp 3 Y) →* P ⧸ N := θ.comp (Subgroup.inclusion hXY)
  have hψrange : ψ.range = ((Opp 3 Y).subgroupOf Y).map θ := by
    dsimp only [ψ]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range hXY]
  have hψrange_normal : ψ.range.Normal := by
    rw [hψrange]
    exact (c8k_Opp_subgroupOf_normal 3 Y).map θ hθs
  have hψrange_top : ψ.range = ⊤ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases hsimp.eq_bot_or_eq_top_of_normal ψ.range with h | h
    · exfalso
      have h3dvd : 3 ∣ Nat.card (P ⧸ N) := by rw [hLcard]; norm_num
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ N) 3 h3dvd
      obtain ⟨g, hg, j, hgj⟩ :=
        CFSG.RankThreeEvenClassification.Helpers.prime_power_element_lifts_surjective
          3 Nat.prime_three θ hθs z 1 (by rw [pow_one, ← hz]; exact pow_orderOf_eq_one z)
      have hgX : (g : G) ∈ Opp 3 Y := by
        obtain ⟨i, -, hi⟩ :=
          (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hgj)
        refine Subgroup.subset_closure ⟨g.2, i, ?_⟩
        rw [Subgroup.orderOf_coe]
        exact hi
      have hzmem : z ∈ ψ.range := by
        refine MonoidHom.mem_range.mpr ⟨⟨(g : G), hgX⟩, ?_⟩
        have hincl : Subgroup.inclusion hXY ⟨(g : G), hgX⟩ = g := Subtype.ext rfl
        dsimp only [ψ]
        rw [MonoidHom.comp_apply, hincl, hg]
      have hz1 : z = 1 := by
        rw [h] at hzmem
        simpa using hzmem
      rw [hz1, orderOf_one] at hz
      norm_num at hz
    · exact h
  have hψ : Function.Surjective ψ := MonoidHom.range_eq_top.mp hψrange_top
  have hψker_le : ψ.ker.map (Subgroup.inclusion hXY) ≤ θ.ker := by
    rintro x ⟨y, hy, rfl⟩
    refine MonoidHom.mem_ker.mpr ?_
    simpa only [ψ, MonoidHom.comp_apply] using MonoidHom.mem_ker.mp hy
  have hψker_dvd : Nat.card ψ.ker ∣ Nat.card θ.ker := by
    rw [← Subgroup.card_map_of_injective (f := Subgroup.inclusion hXY)
      (Subgroup.inclusion_injective hXY)]
    exact Subgroup.card_dvd_of_le hψker_le
  have hψker3 : ¬ 3 ∣ Nat.card ψ.ker := fun h => hθker3 (h.trans hψker_dvd)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcore_bot : CFSG.pPrimeCore 3 (P ⧸ N) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hcop
    haveI : K.Normal := hK
    rcases hsimp.eq_bot_or_eq_top_of_normal K with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top, hLcard] at hcop
      exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop) (by norm_num)
  have hcore_comap := CFSG.prime_complement_kernel_core_preimage ψ hψ hψker3
  have hcore_eq_ker : CFSG.pPrimeCore 3 ↥(Opp 3 Y) = ψ.ker := by
    calc CFSG.pPrimeCore 3 ↥(Opp 3 Y)
        = (CFSG.pPrimeCore 3 (P ⧸ N)).comap ψ := hcore_comap.1.symm
      _ = (⊥ : Subgroup (P ⧸ N)).comap ψ := by rw [hcore_bot]
      _ = ψ.ker := MonoidHom.comap_bot ψ
  let e : BarO3 (Opp 3 Y) ≃* (P ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hcore_eq_ker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL3'

theorem c8k_l3_of_prod {Y H C : Subgroup G} (hYH : Y ≤ H) (hCY : C ≤ Y)
    (hprod : H = Y ⊔ I9 H) (hC3 : ¬ 3 ∣ Nat.card C) (hP : C8P0 Y C) :
    IsL3 (Hbar9 H) 1 := by
  classical
  obtain ⟨P, _, φ, hφs, hφk, ⟨N, hNn, hN64, hL3⟩, -⟩ := hP
  haveI := hNn
  haveI : Finite P := Finite.of_surjective φ hφs
  have hL3' : LieModel (P ⧸ N) .PSL 3 2 1 := hL3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  haveI : I.Normal := CFSG.pPrimeCore_normal
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' I
  have hkerπ : π.ker = I := QuotientGroup.ker_mk' I
  let ρ : ↥Y →* Hbar9 H := π.comp (Subgroup.inclusion hYH)
  have hsup : Y.subgroupOf H ⊔ I = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    have hI : I.map H.subtype = I9 H := rfl
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYH, hI, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hprod.symm
  have hρs : Function.Surjective ρ := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective I x
    have hh : h ∈ Y.subgroupOf H ⊔ I := by rw [hsup]; trivial
    rw [Subgroup.mem_sup_of_normal_right] at hh
    obtain ⟨y, hy, z, hzI, hyz⟩ := hh
    refine ⟨⟨(y : G), hy⟩, ?_⟩
    have hπz : π z = 1 := by
      change QuotientGroup.mk' I z = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' I]
      exact hzI
    have hincl : Subgroup.inclusion hYH ⟨(y : G), hy⟩ = y := Subtype.ext rfl
    change QuotientGroup.mk' I (Subgroup.inclusion hYH ⟨(y : G), hy⟩)
        = QuotientGroup.mk' I h
    rw [hincl, show h = y * z from hyz.symm, map_mul, hπz, mul_one]
  have hcorebot : CFSG.pPrimeCore 3 (Hbar9 H) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (G := ↥H) Nat.prime_three
  have hsubC_normal : (C.subgroupOf Y).Normal := by
    rw [← hφk]
    exact MonoidHom.normal_ker φ
  have hmapC_bot : (C.subgroupOf Y).map ρ = ⊥ := by
    have hno3 : ¬ 3 ∣ Nat.card ((C.subgroupOf Y).map ρ) := by
      intro h3
      have h3C : 3 ∣ Nat.card (C.subgroupOf Y) :=
        h3.trans (Subgroup.card_map_dvd (C.subgroupOf Y) ρ)
      have hcardC : Nat.card (C.subgroupOf Y) = Nat.card C :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY).toEquiv
      rw [hcardC] at h3C
      exact hC3 h3C
    exact (CFSG.pPrimeCore_eq_bot_iff.mp hcorebot) ((C.subgroupOf Y).map ρ)
      (hsubC_normal.map ρ hρs) (Nat.prime_three.coprime_iff_not_dvd.mpr hno3)
  have hker_le : φ.ker ≤ ρ.ker := by
    have hmap : (φ.ker).map ρ = ⊥ := by
      rw [hφk]
      exact hmapC_bot
    exact (Subgroup.map_eq_bot_iff (φ.ker)).mp hmap
  let ρbar : P →* Hbar9 H :=
    (QuotientGroup.lift φ.ker ρ hker_le).comp
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.toMonoidHom
  have hΦmk : ∀ y : ↥Y,
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs) (QuotientGroup.mk' φ.ker y)
        = φ y := by
    intro y
    change (QuotientGroup.kerLift φ) (QuotientGroup.mk' φ.ker y) = φ y
    exact QuotientGroup.kerLift_mk φ y
  have hρbar_φ : ∀ y : ↥Y, ρbar (φ y) = ρ y := by
    intro y
    have hsymm : (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm (φ y)
        = QuotientGroup.mk' φ.ker y := by
      apply (QuotientGroup.quotientKerEquivOfSurjective φ hφs).injective
      rw [MulEquiv.apply_symm_apply]
      exact (hΦmk y).symm
    change QuotientGroup.lift φ.ker ρ hker_le
        ((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm (φ y)) = ρ y
    rw [hsymm]
    exact QuotientGroup.lift_mk' φ.ker hker_le y
  have hρbars : Function.Surjective ρbar :=
    (QuotientGroup.lift_surjective_of_surjective φ.ker ρ hρs hker_le).comp
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.surjective
  have hkerbar_le_N : ρbar.ker ≤ N := by
    refine c8_e64_le_of_no_three hL3' (MonoidHom.normal_ker ρbar) ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨y, rfl⟩ := hφs x
    rw [hρbar_φ y] at hx
    have hyI : (Subgroup.inclusion hYH y : ↥H) ∈ I := by
      have hmem : (Subgroup.inclusion hYH y) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        change ρ y = 1
        exact hx
      rwa [hkerπ] at hmem
    have h3I : ¬ 3 ∣ Nat.card I :=
      Nat.prime_three.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card
    have horder : orderOf y ∣ Nat.card I := by
      rw [← orderOf_injective (Subgroup.inclusion hYH) (Subgroup.inclusion_injective hYH) y]
      exact Subgroup.orderOf_dvd_natCard I hyI
    intro h3
    exact h3I ((h3.trans (orderOf_map_dvd φ y)).trans horder)
  have hN_le_kerbar : N ≤ ρbar.ker := by
    have hNmap_bot : N.map ρbar = ⊥ := by
      have hno3 : ¬ 3 ∣ Nat.card (N.map ρbar) := by
        intro h3
        have h3N : 3 ∣ Nat.card N := h3.trans (Subgroup.card_map_dvd N ρbar)
        rw [c8k_card_elemAbelian N hN64] at h3N
        exact absurd h3N (by norm_num)
      exact (CFSG.pPrimeCore_eq_bot_iff.mp hcorebot) (N.map ρbar)
        (hNn.map ρbar hρbars) (Nat.prime_three.coprime_iff_not_dvd.mpr hno3)
    exact (Subgroup.map_eq_bot_iff N).mp hNmap_bot
  have hkerbar : ρbar.ker = N := le_antisymm hkerbar_le_N hN_le_kerbar
  let e : Hbar9 H ≃* P ⧸ N :=
    (QuotientGroup.quotientKerEquivOfSurjective ρbar hρbars).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerbar)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL3'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
