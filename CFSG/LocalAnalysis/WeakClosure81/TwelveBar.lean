module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.Holt.PointHullTwoGroupBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer
public import CFSG.Foundations
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Holt.Centralizer
public import CFSG.Holt.MaximalFixer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.WeakClosure81.TenFive
public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open scoped MatrixGroups
open CFSG.Assembly.LowTwoRank CFSG.ClassicalModels CFSG.ShultStronglyClosedTI

theorem rankOne_stronglyEmbedded_normalizer {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL 2 2 n Y ∨ CFSG.Quasithin.IsSz n Y) (Q : Sylow 2 Y) :
    fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup Y) : Set Y)) := by
  rcases h with h | h
  · obtain ⟨hadm, K, _, _, hcard, ⟨e⟩⟩ := h
    have hn1 : 1 ≤ n := hadm.2.1
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact hadm.2.2.2.1 (by simp)
    let e' : Y ≃* PSL(2, GaloisField 2 n) :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        (projectiveSpecialLinearFieldEquiv (finiteFieldEquivGaloisField K 2 n (by omega) hcard)
          (Fin 2)))
    have : Finite PSL(2, GaloisField 2 n) := Finite.of_equiv Y e'.toEquiv
    exact ((bender_psl2_borel_full n hn2).map_mulEquiv e'.symm Q).1
  · obtain ⟨-, a, ha, K, _, _, hn, hcard, ⟨e⟩⟩ := h
    subst hn
    let e' : Y ≃* Sz a :=
      e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
        (glaSzEquivNative a ha hcard))
    have : Finite (Sz a) := Finite.of_equiv Y e'.toEquiv
    exact ((bender_suzuki_borel_full a ha).map_mulEquiv e'.symm Q).1

theorem b12_TwelveBar_conj_r {Y : Type} [Group Y] {t s : Y} (ht : t * t = 1) (hs : s * s = 1)
    (w : Y) (hw : w ∈ Subgroup.closure ({t, s} : Set Y)) :
    ∃ ε : ℤ, ε * ε = 1 ∧ w * (t * s) * w⁻¹ = (t * s) ^ ε := by
  have hri : (t * s)⁻¹ = s * t := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right hs]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  refine Subgroup.closure_induction (p := fun z _ =>
    ∃ ε : ℤ, ε * ε = 1 ∧ z * (t * s) * z⁻¹ = (t * s) ^ ε) ?_ ?_ ?_ ?_ hw
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      refine ⟨-1, by norm_num, ?_⟩
      rw [zpow_neg_one, hri, htinv]
      calc t * (t * s) * t = (t * t) * (s * t) := by group
        _ = s * t := by rw [ht, one_mul]
    · rw [hx]
      refine ⟨-1, by norm_num, ?_⟩
      rw [zpow_neg_one, hri, hsinv]
      calc s * (t * s) * s = (s * t) * (s * s) := by group
        _ = s * t := by rw [hs, mul_one]
  · exact ⟨1, by norm_num, by rw [zpow_one]; simp⟩
  · intro x y hx hy ihx ihy
    obtain ⟨ε₁, hε₁, h₁⟩ := ihx
    obtain ⟨ε₂, hε₂, h₂⟩ := ihy
    refine ⟨ε₁ * ε₂, ?_, ?_⟩
    · have : (ε₁ * ε₂) * (ε₁ * ε₂) = (ε₁ * ε₁) * (ε₂ * ε₂) := by ring
      rw [this, hε₁, hε₂, one_mul]
    · calc (x * y) * (t * s) * (x * y)⁻¹ = x * (y * (t * s) * y⁻¹) * x⁻¹ := by group
        _ = x * (t * s) ^ ε₂ * x⁻¹ := by rw [h₂]
        _ = (x * (t * s) * x⁻¹) ^ ε₂ :=
            (conj_zpow (a := x) (b := t * s) (i := ε₂)).symm
        _ = ((t * s) ^ ε₁) ^ ε₂ := by rw [h₁]
        _ = (t * s) ^ (ε₁ * ε₂) := (zpow_mul (t * s) ε₁ ε₂).symm
  · intro x hx ihx
    obtain ⟨ε, hε, hεx⟩ := ihx
    refine ⟨ε, hε, ?_⟩
    rw [inv_inv]
    have hmain2 : x⁻¹ * (t * s) ^ ε * x = (x⁻¹ * (t * s) * x) ^ ε := by
      simpa using (conj_zpow (a := x⁻¹) (b := t * s) (i := ε)).symm
    have hmain : (x⁻¹ * (t * s) * x) ^ ε = t * s := by
      have hh := congrArg (fun z => x⁻¹ * z * x) hεx
      rw [show x⁻¹ * (x * (t * s) * x⁻¹) * x = t * s by group, hmain2] at hh
      exact hh.symm
    calc x⁻¹ * (t * s) * x = (x⁻¹ * (t * s) * x) ^ (1 : ℤ) := (zpow_one _).symm
      _ = (x⁻¹ * (t * s) * x) ^ (ε * ε) := by rw [hε]
      _ = ((x⁻¹ * (t * s) * x) ^ ε) ^ ε := zpow_mul _ ε ε
      _ = (t * s) ^ ε := by rw [hmain]

theorem b12_TwelveBar_isSolvable_closure_pair {Y : Type} [Group Y] {t s : Y}
    (ht : t * t = 1) (hs : s * s = 1) : Group.IsSolvable ↥(Subgroup.closure {t, s}) := by
  let D : Subgroup Y := Subgroup.closure {t, s}
  show Group.IsSolvable ↥D
  have htD : t ∈ D := Subgroup.subset_closure (by simp)
  have hsD : s ∈ D := Subgroup.subset_closure (by simp)
  have hrD : t * s ∈ D := D.mul_mem htD hsD
  let rD : ↥D := ⟨t * s, hrD⟩
  let R : Subgroup ↥D := Subgroup.zpowers rD
  have hconj : ∀ k : ↥D, ∃ ε : ℤ, ε * ε = 1 ∧ k * rD * k⁻¹ = rD ^ ε := by
    intro k
    obtain ⟨ε, hε, hεk⟩ := b12_TwelveBar_conj_r ht hs (k : Y) k.2
    refine ⟨ε, hε, Subtype.ext ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] using hεk
  have hRnorm : R.Normal := by
    refine ⟨fun n hn k => ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hn
    obtain ⟨ε, -, hkε⟩ := hconj k
    refine Subgroup.mem_zpowers_iff.mpr ⟨ε * j, ?_⟩
    calc rD ^ (ε * j) = (rD ^ ε) ^ j := zpow_mul rD ε j
      _ = (k * rD * k⁻¹) ^ j := by rw [hkε]
      _ = k * rD ^ j * k⁻¹ := conj_zpow (a := k) (b := rD) (i := j)
      _ = k * n * k⁻¹ := by rw [hj]
  haveI : R.Normal := hRnorm
  have hquot : Group.IsSolvable (↥D ⧸ R) := by
    let tD : ↥D := ⟨t, htD⟩
    let sD : ↥D := ⟨s, hsD⟩
    have hgen : Subgroup.closure ({tD, sD} : Set ↥D) = ⊤ := by
      apply Subgroup.map_injective D.subtype_injective
      rw [MonoidHom.map_closure]
      have himg : D.subtype '' ({tD, sD} : Set ↥D) = ({t, s} : Set Y) := by
        ext x
        simp [tD, sD]
      rw [himg, Subgroup.map_top, Subgroup.range_subtype]
    have h1 : QuotientGroup.mk' R (tD * sD) = (1 : ↥D ⧸ R) := by
      rw [show tD * sD = rD by exact Subtype.ext rfl]
      exact (QuotientGroup.eq_one_iff rD).mpr (Subgroup.mem_zpowers rD)
    have h2 : QuotientGroup.mk' R (sD * tD) = (1 : ↥D ⧸ R) := by
      have hst : sD * tD = rD⁻¹ := by
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right hs]
      rw [hst]
      exact (QuotientGroup.eq_one_iff rD⁻¹).mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers rD))
    have hts : Commute (QuotientGroup.mk' R tD) (QuotientGroup.mk' R sD) := by
      rw [commute_iff_eq, ← map_mul, ← map_mul, h1, h2]
    have hcomm_gen :
        ({QuotientGroup.mk' R tD, QuotientGroup.mk' R sD} : Set (↥D ⧸ R)).Pairwise Commute := by
      intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hts
      · exact hts.symm
      · exact (hab rfl).elim
    haveI : IsMulCommutative
        ↥(Subgroup.closure ({QuotientGroup.mk' R tD, QuotientGroup.mk' R sD} : Set (↥D ⧸ R))) :=
      Subgroup.isMulCommutative_closure hcomm_gen
    have hHtop : Subgroup.closure
        ({QuotientGroup.mk' R tD, QuotientGroup.mk' R sD} : Set (↥D ⧸ R)) = ⊤ := by
      have hmap2 : (Subgroup.closure ({tD, sD} : Set ↥D)).map (QuotientGroup.mk' R) =
          Subgroup.closure ({QuotientGroup.mk' R tD, QuotientGroup.mk' R sD} :
            Set (↥D ⧸ R)) := by
        rw [MonoidHom.map_closure, Set.image_pair]
      rw [← hmap2, hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)]
    refine Group.isSolvable_of_surjective
      (f := (Subgroup.closure
        ({QuotientGroup.mk' R tD, QuotientGroup.mk' R sD} : Set (↥D ⧸ R))).subtype) ?_
    rw [← MonoidHom.range_eq_top, Subgroup.range_subtype, hHtop]
  haveI : Group.IsSolvable (↥D ⧸ R) := hquot
  exact Group.isSolvable_of_subgroup_quotient R

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem b12_TwelveBar_mem_map_iff (h : Setting12Two A M n) {g : G} :
    g ∈ M ↔ QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) g ∈
      M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) := by
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  have hK : π.ker ≤ M := by
    rw [show π.ker = CFSG.Quasithin.kerIn M ⊤ from QuotientGroup.ker_mk' _]
    exact CFSG.Quasithin.kerIn_le
  constructor
  · intro hg
    exact Subgroup.mem_map_of_mem π hg
  · intro hg
    rw [← Subgroup.comap_map_eq_self (f := π) (H := M) hK]
    exact hg

theorem b12_TwelveBar_map_eq_top_iff (h : Setting12Two A M n) :
    M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) = ⊤ ↔ M = ⊤ := by
  have hK : (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)).ker ≤ M := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.Quasithin.kerIn_le
  constructor
  · intro htop
    have hh := Subgroup.comap_map_eq_self
      (f := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) (H := M) hK
    rw [htop, Subgroup.comap_top] at hh
    exact hh.symm
  · intro htop
    rw [htop]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem b12_TwelveBar_map_ne_top (h : Setting12Two A M n) :
    M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) ≠ ⊤ :=
  fun htop => h.M_ne ((b12_TwelveBar_map_eq_top_iff h).mp htop)

theorem b12_TwelveBar_le_map_of_ne_top (h : Setting12Two A M n)
    {Nbar : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)}
    (hA : A.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) ≤ Nbar) (hN : Nbar ≠ ⊤) :
    Nbar ≤ M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) := by
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  have hNle : Nbar.comap π ≤ M := by
    refine h.unique_max (Nbar.comap π) ?_ ?_
    · intro a ha
      exact hA (Subgroup.mem_map_of_mem π ha)
    · intro htop
      apply hN
      calc Nbar = (Nbar.comap π).map π :=
            (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Nbar).symm
        _ = (⊤ : Subgroup G).map π := by rw [htop]
        _ = ⊤ := Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  calc Nbar = (Nbar.comap π).map π :=
        (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Nbar).symm
    _ ≤ M.map π := Subgroup.map_mono hNle

theorem Setting12Two.stronglyEmbedded_map (h : Setting12Two A M n) :
    fusionStronglyEmbedded (M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤))) := by
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  have hA2 : IsPGroup 2 (A.map π) := h.A_two.map π
  obtain ⟨S, hAS⟩ := hA2.exists_le_sylow
  let B : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤) :=
    Subgroup.normalizer ((S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) :
      Set (G ⧸ CFSG.Quasithin.kerIn M ⊤))
  have hSleB : (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ≤ B := Subgroup.le_normalizer
  have hB : fusionStronglyEmbedded B := rankOne_stronglyEmbedded_normalizer h.type S
  have hBne : B ≠ ⊤ := hB.1
  obtain hBtop | ⟨Hbar, hHcoatom, hBH⟩ := IsCoatomic.eq_top_or_exists_le_coatom B
  · exact absurd hBtop hBne
  have hHB : Hbar ≠ ⊤ := hHcoatom.1
  have hAH : A.map π ≤ Hbar := hAS.trans (hSleB.trans hBH)
  have hBM : B ≤ M.map π := hBH.trans (b12_TwelveBar_le_map_of_ne_top h hAH hHB)
  exact CFSG.Holt.PointHull.fusionStronglyEmbedded_of_le hBM hB
    (b12_TwelveBar_map_ne_top h) hSleB

theorem Setting12Two.mem_ker_of_mem_inf_conj (h : Setting12Two A M n) {g x : G} (hg : g ∉ M)
    (hxM : x ∈ M) (hxMg : x ∈ M.map (MulAut.conj g).toMonoidHom) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x ∈ CFSG.Quasithin.kerIn M ⊤ := by
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  have hSE : fusionStronglyEmbedded (M.map π) := h.stronglyEmbedded_map
  have hg' : (π g)⁻¹ ∉ M.map π := fun hmem =>
    hg ((b12_TwelveBar_mem_map_iff h).mpr (by simpa [π] using Subgroup.inv_mem _ hmem))
  have hodd : Odd (Nat.card ↥(M.map π ⊓ (M.map π).map (MulAut.conj (π g)).toMonoidHom)) := by
    simpa using hSE.2.2 (π g)⁻¹ hg'
  have hxMem : π x ∈ M.map π ⊓ (M.map π).map (MulAut.conj (π g)).toMonoidHom := by
    refine ⟨Subgroup.mem_map_of_mem π hxM, ?_⟩
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hxMg
    refine Subgroup.mem_map.mpr ⟨π m, Subgroup.mem_map_of_mem π hm, ?_⟩
    rw [← hmx]
    simp [MulAut.conj_apply, map_mul]
  have hdvdCard : orderOf (π x) ∣
      Nat.card ↥(M.map π ⊓ (M.map π).map (MulAut.conj (π g)).toMonoidHom) :=
    (M.map π ⊓ (M.map π).map (MulAut.conj (π g)).toMonoidHom).orderOf_dvd_natCard hxMem
  obtain ⟨k, hk⟩ := hx
  have hpow : (π x) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hdvdPow : orderOf (π x) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hpow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdPow
  have hj0 : j = 0 := by
    by_contra hjne
    have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
    have h2dvdOrder : 2 ∣ orderOf (π x) := by
      rw [hj]
      exact dvd_pow_self 2 (by omega)
    have h2dvdCard : 2 ∣
        Nat.card ↥(M.map π ⊓ (M.map π).map (MulAut.conj (π g)).toMonoidHom) :=
      h2dvdOrder.trans hdvdCard
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvdCard)
  have horder1 : orderOf (π x) = 1 := by rw [hj, hj0, pow_zero]
  have hxone : π x = 1 := orderOf_eq_one_iff.mp horder1
  have hxker : x ∈ π.ker := MonoidHom.mem_ker.mpr hxone
  rw [show π.ker = CFSG.Quasithin.kerIn M ⊤ from QuotientGroup.ker_mk' _] at hxker
  exact hxker

theorem b12_TwelveBar_not_isSolvable (h : Setting12Two A M n) :
    ¬ Group.IsSolvable (G ⧸ CFSG.Quasithin.kerIn M ⊤) := by
  haveI : IsSimpleGroup (G ⧸ CFSG.Quasithin.kerIn M ⊤) :=
    CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz h.type
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  obtain ⟨a, b, hab⟩ := CFSG.Quasithin.E2.nonabelian_of_psl_or_sz h.one_lt_n h.type
  exact fun hc => hab (hc a b)

theorem Setting12Two.not_le_ker (h : Setting12Two A M n) : ¬ A ≤ CFSG.Quasithin.kerIn M ⊤ := by
  intro hAK
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  have hAmap : A.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨a, ha, rfl⟩
    have : π a = 1 := by
      rw [← MonoidHom.mem_ker,
        show π.ker = CFSG.Quasithin.kerIn M ⊤ from QuotientGroup.ker_mk' _]
      exact hAK ha
    rw [this]
    exact Subgroup.mem_bot.mpr rfl
  have hMtop : M.map π = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy : Subgroup.zpowers y = ⊤
    · exfalso
      haveI : IsCyclic (G ⧸ CFSG.Quasithin.kerIn M ⊤) :=
        isCyclic_iff_exists_zpowers_eq_top.mpr ⟨y, hy⟩
      haveI : IsMulCommutative (G ⧸ CFSG.Quasithin.kerIn M ⊤) := IsCyclic.isMulCommutative
      exact b12_TwelveBar_not_isSolvable h inferInstance
    · exact b12_TwelveBar_le_map_of_ne_top h (by rw [hAmap]; exact bot_le) hy
        (Subgroup.mem_zpowers y)
  exact h.M_ne ((b12_TwelveBar_map_eq_top_iff h).mp hMtop)

theorem Setting12Two.not_isCyclic_map (h : Setting12Two A M n) (hA : IsElemAbelian 2 A) :
    ¬ IsCyclic ↥(A.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤))) := by
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  intro hcyc
  have hAbot : A.map π ≠ ⊥ := by
    intro hbot
    apply h.not_le_ker
    intro a ha
    have hmem : π a ∈ A.map π := Subgroup.mem_map_of_mem π ha
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [← MonoidHom.mem_ker,
      show π.ker = CFSG.Quasithin.kerIn M ⊤ from QuotientGroup.ker_mk' _] at hmem
    exact hmem
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  let t : G ⧸ CFSG.Quasithin.kerIn M ⊤ := g
  have hAle : A.map π ≤ Subgroup.zpowers t := by
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥(A.map π)) ∈ Subgroup.zpowers g := by rw [hg]; trivial
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa [t] using congrArg (Subtype.val) hj⟩
  have ht2 : t * t = 1 := by
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp g.2
    have ha2 : a * a = 1 := by
      simpa [pow_two] using hA.2 a ha
    have ht_eq : t = (g : G ⧸ CFSG.Quasithin.kerIn M ⊤) := rfl
    rw [ht_eq, ← haeq, ← map_mul, ha2, map_one]
  have htne : t ≠ 1 := by
    intro ht1
    apply hAbot
    rw [eq_bot_iff]
    intro y hy
    have h := hAle hy
    rw [ht1, Subgroup.zpowers_one_eq_bot] at h
    exact h
  have hconj : ∀ y : G ⧸ CFSG.Quasithin.kerIn M ⊤, y * t * y⁻¹ ∈ M.map π := by
    intro y
    set s : G ⧸ CFSG.Quasithin.kerIn M ⊤ := y * t * y⁻¹ with hs
    have hs2 : s * s = 1 := by
      rw [hs]
      calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hsolv : Group.IsSolvable
        ↥(Subgroup.closure ({t, s} : Set (G ⧸ CFSG.Quasithin.kerIn M ⊤))) :=
      b12_TwelveBar_isSolvable_closure_pair ht2 hs2
    have hAle' : A.map π ≤ Subgroup.closure ({t, s} : Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)) :=
      hAle.trans (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    have hne : Subgroup.closure ({t, s} : Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ≠ ⊤ := by
      intro htop
      haveI : Group.IsSolvable ↥(⊤ : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) := htop ▸ hsolv
      exact b12_TwelveBar_not_isSolvable h
        (Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv (G := G ⧸ CFSG.Quasithin.kerIn M ⊤)).toMonoidHom)
          (Subgroup.topEquiv (G := G ⧸ CFSG.Quasithin.kerIn M ⊤)).surjective)
    exact (b12_TwelveBar_le_map_of_ne_top h hAle' hne) (Subgroup.subset_closure (by simp))
  have hnorm : Subgroup.normalClosure ({t} : Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)) ≤ M.map π := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj'⟩ := hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj'
    rw [← hc]
    exact hconj c
  haveI : IsSimpleGroup (G ⧸ CFSG.Quasithin.kerIn M ⊤) :=
    CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz h.type
  have htop : Subgroup.normalClosure ({t} : Set (G ⧸ CFSG.Quasithin.kerIn M ⊤)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ({t} : Set (G ⧸ CFSG.Quasithin.kerIn M ⊤))) with hbot | htop
    · exfalso
      have ht1 : t = 1 := by
        have hmem := Subgroup.subset_normalClosure (Set.mem_singleton t)
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact htne ht1
    · exact htop
  exact b12_TwelveBar_map_ne_top h (top_le_iff.mp (htop ▸ hnorm))

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81
