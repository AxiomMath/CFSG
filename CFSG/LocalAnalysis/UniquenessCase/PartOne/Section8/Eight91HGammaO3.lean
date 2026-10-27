module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpCoreSylow
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.RankThree.PartOne.S12.Sec15Frattini
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups

private theorem k891hgammao3_mem_uniqueSet_map_conj {G : Type} [Group G] [Finite G]
    {M A : Subgroup G} (_hM : rankThreeIsMaxTwoLocal M) (hA : A ∈ uniqueSet M) {l : G}
    (hl : l ∈ M) : A.map (MulAut.conj l).toMonoidHom ∈ uniqueSet M := by
  have hMl : M.map (MulAut.conj l).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)
  refine ⟨?_, ?_⟩
  · calc A.map (MulAut.conj l).toMonoidHom ≤ M.map (MulAut.conj l).toMonoidHom := map_mono hA.1
      _ = M := hMl
  · intro g hg
    have h2 : A ≤ M.map (MulAut.conj (l⁻¹ * g)).toMonoidHom := by
      calc A = (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom := by
              rw [Subgroup.map_map]
              ext x
              simp [MulAut.conj_apply, mul_assoc]
        _ ≤ (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom :=
              map_mono hg
        _ = M.map (MulAut.conj (l⁻¹ * g)).toMonoidHom := by
              rw [Subgroup.map_map]
              ext x
              simp [MulAut.conj_apply, mul_assoc]
    have h3 := hA.2 (l⁻¹ * g) h2
    calc M.map (MulAut.conj g).toMonoidHom
        = (M.map (MulAut.conj (l⁻¹ * g)).toMonoidHom).map (MulAut.conj l).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply, mul_assoc]
      _ = M.map (MulAut.conj l).toMonoidHom := by rw [h3]
      _ = M := hMl

private theorem k891hgammao3_mem_uniqueSet_of_gt_Z {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    {Y : Subgroup G} (hZY : R891Z L S ≤ Y) (hYR : Y ≤ R) (hne : Y ≠ R891Z L S) :
    Y ∈ uniqueSet D.M := by
  classical
  have hLleM : L ≤ D.M := CFSG.Open.IsSubnormal.le hst.set.mem.1
  have hRL : R ≤ L := hst.ctx.xShape.rSylow.trans inf_le_right
  have hRYM : Y ≤ D.M := hYR.trans (hRL.trans hLleM)
  obtain ⟨y, hyY, hyZ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hZY (Ne.symm hne))
  have hyR : y ∈ R := hYR hyY
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ (R891Z L S).one_mem)
  have hExtra := hst.ctx.xShape.rExtra
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hExtra
  have hExp : Monoid.exponent ↥R = 3 := hExtra.2.1
  have hy3 : y ^ 3 = 1 := by
    have h := Subgroup.pow_exponent_eq_one (H := R) hyR
    rwa [hExp] at h
  have hyord : orderOf y = 3 := by
    have hdv : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdv with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  let B : Subgroup G := Subgroup.zpowers y
  have hBcard : Nat.card B = 3 := by
    show Nat.card (Subgroup.zpowers y) = 3
    rw [Nat.card_zpowers, hyord]
  have hBleR : B ≤ R := Subgroup.zpowers_le.mpr hyR
  have hyB : y ∈ B := Subgroup.mem_zpowers y
  have hBne : B ≠ R891Z L S := fun h => hyZ (h ▸ hyB)
  have hBuniq : B ∈ uniqueSet D.M := by
    have hBL : B ≤ L := hBleR.trans hRL
    rcases hst.ctx.classes.classes B hBL hBcard with ⟨l, hlL, hBl⟩ | ⟨l, hlL, hBl⟩
    · have hlM : l ∈ D.M := hLleM hlL
      have hleX : (R891Z L S).map (MulAut.conj l).toMonoidHom ≤
          R891X L (R891Z L S) n := by
        rw [← hBl]
        exact hBleR.trans hst.ctx.xShape.rLe
      have hfix := hst.ctx.xShape.zWeak l hlM hleX
      exact absurd (by rw [hBl, hfix]) hBne
    · rw [hBl]
      exact k891hgammao3_mem_uniqueSet_map_conj D.maxLocal hst.uniq (hLleM hlL)
  exact mem_uniqueSet_of_le hBuniq (Subgroup.zpowers_le.mpr hyY) hRYM

private theorem k891hgammao3_exists_normalizer_grows {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P B : Subgroup G} (hP : IsPGroup p P) (hBP : B ≤ P)
    (hne : B ≠ P) : ∃ x ∈ P, x ∈ normalizer (B : Set G) ∧ x ∉ B := by
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : B.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hBP ?_)
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ B.subgroupOf P := by rw [h]; trivial
    exact this
  obtain ⟨x, hxn, hxnot⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥P) _ hlt)
  refine ⟨x, x.2, ?_, fun hx => hxnot hx⟩
  have : x ∈ (Subgroup.normalizer (B : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hBP]
    exact hxn
  exact this

private theorem k891hgammao3_mem_uniqueSet_of_le_pgroup {G : Type} [Group G] [Finite G]
    {M P B : Subgroup G} {p : ℕ} [Fact p.Prime] (hM : rankThreeIsMaxTwoLocal M)
    (hP : IsPGroup p P) (hBP : B ≤ P) (hB : B ∈ uniqueSet M) : P ∈ uniqueSet M := by
  have key : ∀ n, ∀ B : Subgroup G, B ≤ P → Nat.card P - Nat.card B = n →
      B ∈ uniqueSet M → P ∈ uniqueSet M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hBP hcard hB
      by_cases hBeq : B = P
      · rwa [hBeq] at hB
      · obtain ⟨x, hxP, hxN, hxB⟩ := k891hgammao3_exists_normalizer_grows hP hBP hBeq
        let B' : Subgroup G := normalizer (B : Set G) ⊓ P
        have hBB' : B ≤ B' := le_inf Subgroup.le_normalizer hBP
        have hB'M : B' ≤ M := inf_le_left.trans (normalizer_le_of_mem_uniqueSet hM hB)
        have hB'uniq : B' ∈ uniqueSet M := mem_uniqueSet_of_le hB hBB' hB'M
        have hB'P : B' ≤ P := inf_le_right
        have hBlt : B < B' := lt_of_le_of_ne hBB' (by
          intro h
          exact hxB (h ▸ (show x ∈ B' from ⟨hxN, hxP⟩)))
        have hcard' : Nat.card P - Nat.card B' < n := by
          rw [← hcard]
          have h1 : Nat.card B < Nat.card B' := Subgroup.card_lt_of_lt hBlt
          have h2 : Nat.card B' ≤ Nat.card P := Subgroup.card_le_of_le hB'P
          omega
        exact ih (Nat.card P - Nat.card B') hcard' B' hB'P rfl hB'uniq
  exact key (Nat.card P - Nat.card B) B hBP rfl hB

private theorem k891hgammao3_pCoreOf_three_le {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n) :
    pCoreOf 3 (R891H L S) ≤ D.M := by
  classical
  set H := R891H L S with hH
  have hRL : R ≤ L := hst.ctx.xShape.rSylow.trans inf_le_right
  have hRH : R ≤ H :=
    hst.ctx.xShape.rSylow.trans
      (Subgroup.le_centralizer_iff.mpr (inf_le_right : R891Z L S ≤ centralizer (S ⊓ L)))
  have hExtra := hst.ctx.xShape.rExtra
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hExtra
  have hR3 : IsPGroup 3 ↥R := IsPGroup.of_card (n := 3) (by simpa using hExtra.1)
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow (p := 3) (hR3.comap_subtype (K := H))
  let P : Subgroup G := (Q : Subgroup ↥H).map H.subtype
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P H := ⟨Q, rfl⟩
  have hRP : R ≤ P := by
    intro r hr
    exact Subgroup.mem_map_of_mem H.subtype
      (hRQ (show (⟨r, hRH hr⟩ : ↥H) ∈ R.subgroupOf H from hr))
  have hP3 : IsPGroup 3 P := hPsyl.isPGroup
  have hPuniq : P ∈ uniqueSet D.M :=
    k891hgammao3_mem_uniqueSet_of_le_pgroup D.maxLocal hP3
      (hst.ctx.aLeR.trans hRP) hst.uniq
  have hPM : P ≤ D.M := hPuniq.1
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section12.pCoreOf_le_of_isSylowOf_le hPsyl hPM

private theorem k891hgammao3_pPrimeCore_map_le {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n) :
    (CFSG.pPrimeCore 3 ↥(R891H L S)).map (R891H L S).subtype ≤ D.M := by
  classical
  set H := R891H L S with hH
  set Z := R891Z L S with hZ
  have hZR : Z ≤ R := hst.ctx.xShape.zLe
  have hRH : R ≤ H :=
    hst.ctx.xShape.rSylow.trans
      (Subgroup.le_centralizer_iff.mpr (inf_le_right : Z ≤ centralizer (S ⊓ L)))
  let ZR : Subgroup ↥R := Z.subgroupOf R
  have hZRcard : Nat.card ZR = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv]
    exact hst.basic.zOrder
  have hZR_center : ZR ≤ Subgroup.center ↥R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp ((inf_le_right : Z ≤ centralizer (S ⊓ L)) hz)
      (y : G) (hst.ctx.xShape.rSylow y.2)
  have hZRnormal : ZR.Normal := Subgroup.normal_of_le_center hZR_center
  let T : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  have hTnormal : T.Normal := CFSG.pPrimeCore_normal
  let φR : ↥R →* MulAut ↥T :=
    (MulAut.conjNormal (H := T)).comp (Subgroup.inclusion hRH)
  have hker : ZR ≤ φR.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    ext t
    have hcz : (z : G) * (t : G) = (t : G) * (z : G) :=
      Subgroup.mem_centralizer_iff.mp (show (t : G) ∈ centralizer (Z : Set G) from
        (t : ↥H).2) (z : G) hz
    change ((MulAut.conjNormal (Subgroup.inclusion hRH z)) t : G) = (t : G)
    rw [MulAut.conjNormal_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [hcz]
    group
  let ψ : (↥R ⧸ ZR) →* MulAut ↥T := QuotientGroup.lift ZR φR hker
  let : MulDistribMulAction (↥R ⧸ ZR) ↥T := MulDistribMulAction.compHom ↥T ψ
  have hExtra := hst.ctx.xShape.rExtra
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hExtra
  have hcenter_eq : Subgroup.center ↥R = ZR :=
    (Subgroup.eq_of_le_of_card_ge hZR_center (by rw [hExtra.2.2.2, hZRcard])).symm
  have hcomm_le : commutator ↥R ≤ ZR := by rw [hExtra.2.2.1, hcenter_eq]
  have : IsMulCommutative (↥R ⧸ ZR) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le
  let : CommGroup (↥R ⧸ ZR) := IsMulCommutative.instCommGroup
  have hQrcard : Nat.card (↥R ⧸ ZR) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ZR
    have hRcard : Nat.card ↥R = 27 := by rw [hExtra.1]; norm_num
    have h27 : Nat.card (↥R ⧸ ZR) * 3 = 27 := by
      rw [← hZRcard, ← h, hRcard]
    have h99 : Nat.card (↥R ⧸ ZR) * 3 = 9 * 3 := by rw [h27]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h99
  have hQrP : IsPGroup 3 (↥R ⧸ ZR) := IsPGroup.of_card (n := 2) (by rw [hQrcard]; norm_num)
  have hexpQr : ∀ a : ↥R ⧸ ZR, a ^ 3 = 1 := by
    intro a
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective ZR a
    have hr3 : r ^ 3 = 1 := by
      have := Monoid.pow_exponent_eq_one r
      rwa [hExtra.2.1] at this
    rw [← map_pow, hr3, map_one]
  have hnotcyc : ¬ IsCyclic (↥R ⧸ ZR) := by
    intro hcyc
    let := hcyc
    obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥R ⧸ ZR)
    have h9 : orderOf a = 9 := by rw [ha, hQrcard]
    have h3 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hexpQr a)
    rw [h9] at h3
    exact absurd h3 (by norm_num)
  have hcop : Nat.Coprime 3 (Nat.card ↥T) := CFSG.pPrimeCore_coprime_card
  have : Fact (IsPGroup 3 (↥R ⧸ ZR)) := ⟨hQrP⟩
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := ↥T) (A := ↥R ⧸ ZR) 3 hcop hnotcyc
  have hle : (⊤ : Subgroup ↥T) ≤ (D.M.subgroupOf H).comap T.subtype := by
    rw [← hgen]
    refine iSup₂_le fun a ha => ?_
    intro t ht
    rw [Subgroup.mem_comap]
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective ZR a
    have hfix : (QuotientGroup.mk' ZR r) • t = t := by
      rw [FixedPoints.mem_subgroup] at ht
      exact ht ⟨QuotientGroup.mk' ZR r, Subgroup.mem_zpowers _⟩
    have hpsi : ψ (QuotientGroup.mk' ZR r) = φR r := by
      rw [show ψ (QuotientGroup.mk' ZR r) =
        QuotientGroup.lift ZR φR hker (QuotientGroup.mk r) from rfl]
      exact QuotientGroup.lift_mk' (N := ZR) (φ := φR) hker r
    have hfixφ : φR r t = t := by rw [← hpsi]; exact hfix
    have hcoe : (r : G) * (t : G) * (r : G)⁻¹ = (t : G) := by
      have h := congrArg (fun x : ↥T => ((x : ↥H) : G)) hfixφ
      simpa [φR, MulAut.conjNormal_apply] using h
    have hcomm : (t : G) * (r : G) = (r : G) * (t : G) := by
      calc (t : G) * (r : G) = ((r : G) * (t : G) * (r : G)⁻¹) * (r : G) := by rw [hcoe]
        _ = (r : G) * (t : G) := by group
    have htr : (t : G) * (r : G) * (t : G)⁻¹ = (r : G) := by rw [hcomm]; group
    have htN_Z : (t : G) ∈ normalizer (Z : Set G) :=
      Subgroup.centralizer_le_normalizer (Z : Set G)
        (show (t : G) ∈ centralizer (Z : Set G) from (t : ↥H).2)
    have hZmap : Z.map (MulAut.conj (t : G)).toMonoidHom = Z :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htN_Z
    let Y : Subgroup G := Subgroup.zpowers (r : G) ⊔ Z
    have hZY : Z ≤ Y := le_sup_right
    have hYR : Y ≤ R := sup_le (Subgroup.zpowers_le.mpr r.2) hZR
    have hneY : Y ≠ Z := by
      intro heq
      have hrmem : (r : G) ∈ Z := by
        have : (r : G) ∈ Y :=
          (le_sup_left : Subgroup.zpowers (r : G) ≤ Y) (Subgroup.mem_zpowers (r : G))
        rwa [heq] at this
      have hrZR : r ∈ ZR := hrmem
      exact ha ((QuotientGroup.eq_one_iff (N := ZR) r).mpr hrZR)
    have hYuniq : Y ∈ uniqueSet D.M :=
      k891hgammao3_mem_uniqueSet_of_gt_Z D L S R A n hst hZY hYR hneY
    have hNYM : normalizer (Y : Set G) ≤ D.M :=
      normalizer_le_of_mem_uniqueSet D.maxLocal hYuniq
    have hYmap : Y.map (MulAut.conj (t : G)).toMonoidHom = Y := by
      show (Subgroup.zpowers (r : G) ⊔ Z).map (MulAut.conj (t : G)).toMonoidHom = _
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      have htr' : (MulAut.conj (t : G)).toMonoidHom (r : G) = (r : G) := by
        simpa [MulAut.conj_apply] using htr
      rw [htr', hZmap]
    exact hNYM (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hYmap)
  have hTleM : T ≤ D.M.subgroupOf H := by
    intro t ht
    exact hle (Subgroup.mem_top (⟨t, ht⟩ : ↥T))
  rw [Subgroup.map_le_iff_le_comap]
  exact hTleM

private theorem k891hgammao3_R_le_M {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n) :
    R ≤ D.M := by
  have hExtra := hst.ctx.xShape.rExtra
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hExtra
  have hRcard : Nat.card ↥R = 27 := by rw [hExtra.1]; norm_num
  have hne : R ≠ R891Z L S := by
    intro h
    have hcard : Nat.card ↥R = Nat.card (R891Z L S) := by rw [h]
    rw [hRcard, hst.basic.zOrder] at hcard
    norm_num at hcard
  have huniq : R ∈ uniqueSet D.M :=
    k891hgammao3_mem_uniqueSet_of_gt_Z D L S R A n hst hst.ctx.xShape.zLe le_rfl hne
  exact le_trans Subgroup.le_normalizer (normalizer_le_of_mem_uniqueSet D.maxLocal huniq)

private theorem k891hgammao3_ker_eq_sup {G : Type} [Group G] [Finite G]
    (H Z : Subgroup G) (hZH : Z.subgroupOf H ≤ Subgroup.center ↥H) :
    R891Ker H Z = (CFSG.pPrimeCore 3 ↥H) ⊔ (Z.subgroupOf H) := by
  unfold R891Ker
  have hO : (CFSG.pPrimeCore 3 ↥H).Normal := CFSG.pPrimeCore_normal
  have hZ : (Z.subgroupOf H).Normal := Subgroup.normal_of_le_center hZH
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right hx
  · refine sup_le ?_ ?_
    · exact fun x hx => Subgroup.subset_normalClosure (Set.mem_union_left _ hx)
    · exact fun x hx => Subgroup.subset_normalClosure (Set.mem_union_right _ hx)

private theorem k891hgammao3_rank_le {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n) :
    rankThreeGamma 1 3 (R891Img (R891H L S) (R891Z L S) R) ≤
      R891Img (R891H L S) (R891Z L S) D.M := by
  let H := R891H L S
  let Z := R891Z L S
  let K := R891Ker H Z
  let π : ↥H →* R891Star H Z := QuotientGroup.mk' K
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hRH : R ≤ H :=
    hst.ctx.xShape.rSylow.trans
      (Subgroup.le_centralizer_iff.mpr (inf_le_right : Z ≤ centralizer (S ⊓ L)))
  have hZH : Z.subgroupOf H ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (show (y : G) ∈ centralizer (Z : Set G) from
      (y : ↥H).2) (z : G) hz).symm
  have hK_eq : K = (CFSG.pPrimeCore 3 ↥H) ⊔ (Z.subgroupOf H) :=
    k891hgammao3_ker_eq_sup H Z hZH
  have hRM : R ≤ D.M := k891hgammao3_R_le_M D L S R A n hst
  rw [rankThreeGamma]
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall (p := 3) (k := 1) ?_
  intro Q hQ _hRank
  let Qhat : Subgroup ↥H := Q.comap π
  let RH : Subgroup ↥H := R.subgroupOf H
  let YH : Subgroup ↥H := Qhat ⊓ RH
  let Y : Subgroup G := YH.map H.subtype
  have hK_le_Qhat : K ≤ Qhat := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact (MonoidHom.mem_ker.mp (hker ▸ hx)) ▸ Q.one_mem
  have hQhat_K_sup : Qhat = K ⊔ YH := by
    refine le_antisymm ?_ (sup_le hK_le_Qhat inf_le_left)
    intro q hq
    have hqR : π q ∈ (R.subgroupOf H).map π := hQ hq
    obtain ⟨r, hr, hrq⟩ := hqR
    have hrK : r⁻¹ * q ∈ K := by
      apply (QuotientGroup.eq_one_iff (N := K) (r⁻¹ * q)).mp
      change (QuotientGroup.mk' K) (r⁻¹ * q) = 1
      rw [map_mul, map_inv, hrq, inv_mul_cancel]
    have hrQhat : r ∈ Qhat := by
      have hr_eq : r = q * (r⁻¹ * q)⁻¹ := by group
      rw [hr_eq]
      exact Qhat.mul_mem hq (hK_le_Qhat (K.inv_mem hrK))
    have hrYH : r ∈ YH := ⟨hrQhat, hr⟩
    have hq_eq : q = r * (r⁻¹ * q) := by group
    rw [hq_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hrYH) (Subgroup.mem_sup_left hrK)
  have hZYH : Z.subgroupOf H ≤ YH := by
    intro z hz
    exact ⟨hK_le_Qhat (hK_eq ▸ Subgroup.mem_sup_right hz), hst.ctx.xShape.zLe hz⟩
  have hQhat_eq : Qhat = (CFSG.pPrimeCore 3 ↥H) ⊔ YH := by
    have h1 : Qhat = K ⊔ YH := hQhat_K_sup
    have h2 : K ⊔ YH = (CFSG.pPrimeCore 3 ↥H) ⊔ (Z.subgroupOf H) ⊔ YH := by rw [hK_eq]
    have h3 : (CFSG.pPrimeCore 3 ↥H) ⊔ (Z.subgroupOf H) ⊔ YH =
        (CFSG.pPrimeCore 3 ↥H) ⊔ ((Z.subgroupOf H) ⊔ YH) := by rw [sup_assoc]
    have h4 : (CFSG.pPrimeCore 3 ↥H) ⊔ ((Z.subgroupOf H) ⊔ YH) =
        (CFSG.pPrimeCore 3 ↥H) ⊔ YH := by rw [sup_eq_right.mpr hZYH]
    exact h1.trans (h2.trans (h3.trans h4))
  have hRH3 : IsPGroup 3 ↥RH := by
    have hRcard : Nat.card ↥R = 3 ^ 3 := by
      have hExtra := hst.ctx.xShape.rExtra
      unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hExtra
      exact hExtra.1
    exact (IsPGroup.of_card hRcard).comap_subtype
  have hYH3 : IsPGroup 3 ↥YH := hRH3.to_le inf_le_right
  have hYH_sylow : CFSG.ABGLocalTools.IsSylowOf 3 YH Qhat := by
    have h := CFSG.RankThree.PartOne.Sec15Frattini.isSylowOf_sup_of_coprime
      (V := CFSG.pPrimeCore 3 ↥H) (R := YH) hYH3
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card)
    rwa [← hQhat_eq] at h
  have hZY : Z ≤ Y := by
    intro z hz
    have hzH : z ∈ H := (hst.ctx.xShape.zLe.trans hRH) hz
    exact Subgroup.mem_map_of_mem H.subtype
      (hZYH (show (⟨z, hzH⟩ : ↥H) ∈ Z.subgroupOf H from hz))
  have hY_gt_Z : R891Z L S < Y := by
    obtain ⟨E, hEQ, _hEel, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt Q
    have hEcard_ge : 3 ≤ Nat.card E := by
      have hp : 1 ≤ CFSG.Open.pRank 3 Q := _hRank
      rw [hEcard]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ CFSG.Open.pRank 3 Q := Nat.pow_le_pow_right (by norm_num) hp
    have hE_ne_bot : E ≠ ⊥ := by
      intro hbot
      rw [hbot] at hEcard_ge
      simp at hEcard_ge
    obtain ⟨q, hq_ne_one⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE_ne_bot
    have hqQ : q.1 ∈ Q := hEQ q.2
    obtain ⟨r, hr, hrq⟩ := hQ hqQ
    have hrQhat : r ∈ Qhat := by
      rw [Subgroup.mem_comap]
      rw [hrq]
      exact hqQ
    have hrmemY : (r : G) ∈ Y :=
      Subgroup.mem_map_of_mem H.subtype (show r ∈ YH from ⟨hrQhat, hr⟩)
    refine lt_of_le_of_ne hZY (Ne.symm ?_)
    intro hZY_eq
    have hrZm : (r : G) ∈ Z := by
      rw [hZY_eq] at hrmemY
      exact hrmemY
    have hrZ_sub : r ∈ Z.subgroupOf H := hrZm
    have hπr : π r = 1 :=
      MonoidHom.mem_ker.mp (hker ▸ (hK_eq ▸ Subgroup.mem_sup_right hrZ_sub : r ∈ K))
    rw [hrq] at hπr
    exact hq_ne_one (Subtype.ext hπr)
  have hYR : Y ≤ R := by
    intro y hy
    obtain ⟨yh, hyh, rfl⟩ := Subgroup.mem_map.mp hy
    exact hyh.2
  have hY_uniq : Y ∈ uniqueSet D.M :=
    k891hgammao3_mem_uniqueSet_of_gt_Z D L S R A n hst hY_gt_Z.le hYR
      (ne_of_gt hY_gt_Z)
  have hNYM : normalizer (Y : Set G) ≤ D.M :=
    normalizer_le_of_mem_uniqueSet D.maxLocal hY_uniq
  intro n_hat hn_hat
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective K n_hat
  have hn_Qhat : n ∈ Subgroup.normalizer (Qhat : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_comap] at hy ⊢
      have hy' : π y ∈ Q := hy
      have hn' : (QuotientGroup.mk' K) n ∈ Subgroup.normalizer (Q : Set (R891Star H Z)) := hn_hat
      have hmem := (Subgroup.mem_normalizer_iff.mp hn') (π y)
      exact hmem.mp hy'
    · intro hy
      rw [Subgroup.mem_comap] at hy
      have hmem := (Subgroup.mem_normalizer_iff.mp hn_hat) (π y)
      exact hmem.mpr (by simpa only [map_mul, map_inv, π] using hy)
  obtain ⟨k, hk, hkN⟩ :=
    CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hYH_sylow hn_Qhat
  have hkM : π k ∈ R891Img H Z D.M := by
    have hkQhat : k ∈ K ⊔ YH := hQhat_K_sup ▸ hk
    obtain ⟨v, hv, y, hy, hk_eq⟩ := Subgroup.mem_sup_of_normal_left.1 hkQhat
    rw [hk_eq.symm, map_mul]
    have hπv : π v = 1 := MonoidHom.mem_ker.mp (hker ▸ hv)
    rw [hπv, one_mul]
    exact Subgroup.mem_map_of_mem π (show y ∈ D.M.subgroupOf H from hRM hy.2)
  have hkNM : π (k⁻¹ * n) ∈ R891Img H Z D.M := by
    have hkN' : (k⁻¹ * n).1 ∈ normalizer (Y : Set G) := by
      have hkNH : k⁻¹ * n ∈ Subgroup.normalizer (YH : Set ↥H) := hkN
      exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ hkNH)
    exact Subgroup.mem_map_of_mem π (show (k⁻¹ * n : ↥H) ∈ D.M.subgroupOf H from hNYM hkN')
  have hπn : π n = π k * π (k⁻¹ * n) := by
    rw [show π n = π (k * (k⁻¹ * n)) from by rw [mul_inv_cancel_left], map_mul]
  rw [hπn]
  exact Subgroup.mul_mem _ hkM hkNM

theorem s891_h_gamma_o3 {G : Type} [Group G] [Finite G] (D : Data G) (L S R A : Subgroup G) (n : ℕ)
    (hst : R891State D L S R A n) :
    R891Gamma895 D L S R := by
  refine ⟨?_, ?_, ?_⟩
  · exact k891hgammao3_rank_le D L S R A n hst
  · exact k891hgammao3_pCoreOf_three_le D L S R A n hst
  · exact k891hgammao3_pPrimeCore_map_le D L S R A n hst

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
