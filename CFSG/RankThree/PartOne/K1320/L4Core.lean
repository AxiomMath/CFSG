module

public import CFSG.RankThree.PartOne.K1320.L4Comm
public import CFSG.RankThree.PartOne.K1320.L4R
public import CFSG.RankThree.PartOne.K1320.L4CT

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

namespace Row8Frame

variable {p : ℕ} {A L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

structure Core (fr : Row8Frame p A L E f K) (c : G) (r : ℕ) (zs : MulAut E) : Prop where
  mem : zs ∈ reflectionSet p E
  comm : ∀ g ∈ torusImage E L, g * zs = zs * g
  notL : zs ∉ torusImage E L
  mov : autMovedInG E zs = Subgroup.zpowers c
  conj : ∃ g ∈ reflectionGroup p E, g * fr.r₁ * g⁻¹ = zs
  kfAt : KFAt p E (2 * f) zs
  cent₀ : kZero p E zs ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G)
  cent₀' : kZero p E zs ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G)
  R_le : fr.lft (Rr K r) ≤ kZero p E zs
  R_norm : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)),
    conjAut E y hy ∈ reflectionGroup p E → conjBy y (fr.lft (Rr K r)) = fr.lft (Rr K r)

theorem row8_core (hS : SchreierFor InCatalog) (hRe : Sec13Reinst)
    (fr : Row8Frame p A L E f K) {c : G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A)
    (hZ : Subgroup.center L = ⊥) (hcard : Nat.card E = p ^ 3) (B : Bridge p E) {z : MulAut E}
    (hz : Inverter p E z) (hf2 : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (eL : ↥(torusImage E L) ≃* DihedralGroup 4) {r : ℕ} (hr : r.Prime) (hrf : r ∣ 2 ^ f - 1)
    (hM7 : ∀ g : ↥(M8 K), g ∈ (blk8M (K := K)).range →
      g ∈ Subgroup.centralizer (T8 p K : Set ↥(M8 K)) → g ^ r = 1 → g ∈ Rr K r)
    (hDist : ∀ t ∈ reflectionSet p E, KFLiftAt p E t → HasTwoSub E (kZero p E t) →
      fr.r₀ * t = t * fr.r₀ → DistinctCommute p fr.r₀ t) :
    ∃ zs : MulAut E, fr.Core c r zs := by
  have hp := h.prime
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hrq : r ∣ Nat.card K - 1 := by rw [fr.hK]; exact hrf
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd hq1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hrf)
  obtain ⟨hcomm₀, hu2, hu1, hucen⟩ := fr.u_data h hF13 hZ eL
  have huL : fr.r₀ * fr.r₀' ∈ torusImage E L :=
    (torusImage E L).mul_mem fr.mem₀L fr.mem₀'L
  obtain ⟨hfixu, hmovu⟩ := fixS_u h hF hcard hZ huL hu2 hu1 hucen
  obtain ⟨zs, -, hzs2, hzsrefl, hzsX, hzsc, hzsinv, hzsmov, hzsfix, hzsL⟩ :=
    exists_zstar h hF hcard hz huL hu2 hu1 hucen hmovu (hcE := hcE) hfixu
  have hzs : zs ∈ reflectionSet p E := by
    obtain ⟨g, hg⟩ := B.surj zs hzsX
    rw [← hg]
    exact (B.refl_iff g).1 (hg ▸ hzsrefl)
  obtain ⟨hRL, hR0, hR0', hRE⟩ := fr.R_data h hF hF13 hZ hEA (Rm := Rr K r)
    (by rintro _ ⟨ζ, -, rfl⟩; exact ⟨ζ, rfl⟩)
  have hRcard : Nat.card (fr.lft (Rr K r)) = r := by
    rw [fr.lft_card hZ]
    exact rootsOfUnity_card hr hrq
  have he : CFSG.twoLocalOddRank G = 3 := h.setup.2.2.2.2.1
  have hpg : p ∣ 2 ^ (2 * f) - 1 := by
    have h1 : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have hsq : 2 ^ (2 * f) = 2 ^ f * 2 ^ f := by rw [two_mul, pow_add]
      have hpos2 : 1 ≤ 2 ^ f * 2 ^ f := Nat.mul_pos hpos hpos
      rw [hsq]
      zify [hpos, hpos2]
      ring
    rw [h1]
    exact Dvd.dvd.mul_left hpf _
  have hkfs : KFAt p E (2 * f) zs :=
    fr.kfAt_zstar h hF hF13 hZ hcard B hcomm₀ hzs hzsc hzsL hzsmov hpf hr hrf hRcard hR0 hR0' hRE
      he
  have hnot := fr.not_conj_zstar h hF hF13 hZ hcard B hcomm₀ hzs hzsc hzsL hzsmov hpf hr hrf hRcard
    hR0 hR0' hRE he
  have hL₀ := fr.mem₀L
  have hL₁ := fr.mem₁L
  have hmem : ∀ x ∈ torusImage E L, zs ≠ x := fun x hx h1 => hzsL (h1 ▸ hx)
  have hcls := B.zstar_class h hcard fr.mem₀ fr.mem₁ hzs fr.ord₀₁ (hzsc _ hL₀) (hzsc _ hL₁)
    (hmem _ hL₀) (hmem _ hL₁)
    (hmem _ ((torusImage E L).mul_mem ((torusImage E L).mul_mem hL₀ hL₁)
      ((torusImage E L).inv_mem hL₀)))
    (hmem _ ((torusImage E L).mul_mem ((torusImage E L).mul_mem hL₁ hL₀)
      ((torusImage E L).inv_mem hL₁)))
  have hzsconj : ∃ g ∈ reflectionGroup p E, g * fr.r₁ * g⁻¹ = zs :=
    hcls.resolve_left fun ⟨g, hgX, hg⟩ => hnot g hgX hg
  obtain ⟨g, hgX, hg⟩ := hzsconj
  obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hgX)
  have hty : zs = conjAut E y hy * fr.r₁ * (conjAut E y hy)⁻¹ := by rw [hyg]; exact hg.symm
  have hc1 := comm_clause_row8 hS hRe h hF13 hT hEA hpf hz
    fr.mem₀ fr.mem₀L fr.mem₁ fr.mem₁L hy hty fr.kf₀ hkfs hzsmov
    (fun h1 => hzsL (h1 ▸ fr.mem₀L)) (hzsc _ fr.mem₀L) hnot
    (hDist zs hzs (KFAt.toLiftAt hkfs) (K1320X.hasTwoSub_of_kfAt h hF13 hzs hkfs hpg)
      (hzsc _ fr.mem₀L))
  have hxL : conjAut E fr.w fr.wE ∈ torusImage E L :=
    Sec12Three.mem_torusImage_iff.2 ⟨fr.w, fr.wL, fr.wE, rfl⟩
  have hc1' := commClause_conj (p := p) fr.wE hc1
  rw [← fr.hw] at hc1'
  have hzw : conjAut E fr.w fr.wE * zs * (conjAut E fr.w fr.wE)⁻¹ = zs := by
    rw [hzsc _ hxL]
    group
  rw [hzw] at hc1'
  have hcent₀ := le_centralizer_symm hc1.1
  have hcent₀' := le_centralizer_symm hc1'.1
  have hRzs : fr.lft (Rr K r) ≤ kZero p E zs :=
    R_le_kZero hr hr2 hrf hRcard fr.kf₀ fr.kf₀' hkfs hcent₀ hcent₀'
      (fr.kz_comm h hF13 hZ).1 hRE hR0 hR0' he
  have hRn := fr.R_normal h hF hF13 hZ hEA B hcard hr hrq hM7 hzs hzsc hzsL ⟨g, hgX, hg⟩ hRzs
  exact ⟨zs, ⟨hzs, hzsc, hzsL, hzsmov, ⟨g, hgX, hg⟩, hkfs, hcent₀, hcent₀', hRzs, hRn⟩⟩

theorem lieGenerated_le (fr : Row8Frame p A L E f K) {c : G} (h : Sec12Hyp G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hcard : Nat.card E = p ^ 3) (B : Bridge p E) {r : ℕ}
    {zs : MulAut E} (hcore : fr.Core c r zs) {I₀ J : Subgroup G} (hLI : L ≤ I₀)
    (h3I : kZero p E zs ≤ I₀) (hJI : J ≤ I₀) (hK₁J : kZero p E fr.r₀ ≤ J)
    (hJnorm : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)),
      conjAut E y hy ∈ reflectionGroup p E → conjBy y J = J) :
    lieGenerated p E ≤ I₀ := by
  refine sSup_le ?_
  rintro K ⟨t, ht, hKt⟩
  have hL₀ := fr.mem₀L
  have hL₁ := fr.mem₁L
  rcases B.classes h hcard fr.mem₀ fr.mem₁ fr.ord₀₁ ht with ⟨g, hgX, hg⟩ | ⟨g, hgX, hg⟩
  · obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hgX)
    have hty : t = conjAut E y hy * fr.r₀ * (conjAut E y hy)⁻¹ := by rw [hyg]; exact hg.symm
    have hkf : KFAt p E f t := by rw [hty]; exact fr.kf₀.conj hy
    have hK : K = kZero p E t := (kfKt_of_kfAt hkf).2.1 K hKt
    have hyX : conjAut E y hy ∈ reflectionGroup p E := by rw [hyg]; exact hgX
    rw [hK, hty, kZero_conj p fr.r₀ hy]
    have h1 : conjBy y (kZero p E fr.r₀) ≤ conjBy y J := Subgroup.map_mono hK₁J
    rw [hJnorm y hy hyX] at h1
    exact h1.trans hJI
  · obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hgX)
    have hty : t = conjAut E y hy * fr.r₁ * (conjAut E y hy)⁻¹ := by rw [hyg]; exact hg.symm
    have hkf : KFAt p E (2 * f) t := by rw [hty]; exact fr.kf₁.conj hy
    have hK : K = kZero p E t := (kfKt_of_kfAt hkf).2.1 K hKt
    have hzsr₀ : zs ≠ fr.r₀ := fun h1 => hcore.notL (h1 ▸ hL₀)
    have hzsr₁ : zs ≠ fr.r₁ := fun h1 => hcore.notL (h1 ▸ hL₁)
    have hzs1 : zs ≠ fr.r₀ * fr.r₁ * fr.r₀⁻¹ := fun h1 =>
      hcore.notL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₀ hL₁)
        ((torusImage E L).inv_mem hL₀))
    have hzs2 : zs ≠ fr.r₁ * fr.r₀ * fr.r₁⁻¹ := fun h1 =>
      hcore.notL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₁ hL₀)
        ((torusImage E L).inv_mem hL₁))
    have hcl := B.vclass h hcard fr.mem₀ fr.mem₁ hcore.mem fr.ord₀₁ (hcore.comm _ hL₀)
      (hcore.comm _ hL₁) hzsr₀ hzsr₁ hzs1 hzs2 hcore.conj g hgX
    rw [hg] at hcl
    rcases hcl with h1 | h1 | h1
    · rw [hK, h1]
      exact (kZero_le_of_reflection h hF13 fr.mem₁ hL₁).trans hLI
    · rw [hK, h1]
      exact (kZero_le_of_reflection h hF13 (h1 ▸ ht) (h1 ▸ ((torusImage E L).mul_mem
        ((torusImage E L).mul_mem hL₀ hL₁) ((torusImage E L).inv_mem hL₀)))).trans hLI
    · rw [hK, h1]
      exact h3I

end Row8Frame

end CFSG.RankThree.PartOne.K1320
