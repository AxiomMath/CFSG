module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Rank
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Alt5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_sig_prime_dvd_of_listTwo_of_s15_le_three
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L))
    (hs : s15 D.M V₀ V hV L ≤ 3) :
    ∀ p ∈ D.sig, p ∣ Nat.card ↥(lBar V₀ V hV L) := by
  classical
  let W := Vtil V₀ V hV
  let V₁ := v1Sub D.M V₀ V hV L
  let S := vStar D.M V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let B : Subgroup (MulAut W) := lBar V₀ V hV L
  let A' : Subgroup (MulAut S) := Mbar D.M V₁ V hV
  let B' : Subgroup (MulAut S) := lStar D.M V₀ V hV L
  let U : Subgroup S := wStar D.M V₀ V hV L
  let κ := s15T7Kappa V₀ V₁ V hV (s15_Infra_le_v1Sub D.M V₀ V hV L)
  have hthree : 3 ∣ Nat.card ↥B := by
    rcases hL2 with hL3 | hA5
    · rw [CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two hL3]
      norm_num
    · rw [CFSG.RankThree.PartTwo.KFacts.KS166.card_of_alt5 hA5.some]
      norm_num
  have hAut : Nat.card (MulAut ↥B) = 2 * Nat.card ↥B := by
    rcases hL2 with hL3 | hA5
    · rw [CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two hL3,
        CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two hL3]
    · rw [CFSG.RankThree.PartTwo.KFacts.KS166.card_mulAut_of_alt5 hA5.some,
        CFSG.RankThree.PartTwo.KFacts.KS166.card_of_alt5 hA5.some]
  intro p hpSig
  by_contra hpB
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpSig
  have hp3 : p ≠ 3 := by
    intro h3
    exact hpB (h3 ▸ hthree)
  have hp2lt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have h3le : 3 ≤ p := Nat.succ_le_of_lt hp2lt
  have hp3lt : 3 < p := lt_of_le_of_ne h3le (Ne.symm hp3)
  have hsp : s15 D.M V₀ V hV L < p := by omega
  have hpAut : ¬ p ∣ Nat.card (MulAut ↥B) := by
    rw [hAut]
    intro h
    rcases hp.dvd_mul.mp h with h2 | hB
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact hpB hB
  obtain ⟨ρ, hρB, hκ⟩ :=
    s16e_two_kappa_equiv D c.std.h1217 c.setting.hyp151 hV
  have hm₁ : ∀ (m : G), m ∈ D.M → m ∈ stabTil V₁ V := fun m hm =>
    le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub c.setting.hyp151.hyp125 hV) hm
  let am : (m : G) → m ∈ D.M → ↥A := fun m hm =>
    ⟨actTil V₀ V hV ⟨m, c.m_le_stabTil hm⟩,
      actTil_mem_barSub V₀ V hV hm (c.m_le_stabTil hm)⟩
  let αm : (m : G) → m ∈ D.M → MulAut S := fun m hm =>
    actTil V₁ V hV ⟨m, hm₁ m hm⟩
  have hρα : ∀ (m : G) (hm : m ∈ D.M),
      (ρ (am m hm) : MulAut S) = αm m hm := by
    intro m hm
    ext z
    obtain ⟨w, rfl⟩ := s15_T7_kappa_surjective V₀ V₁ V hV
      (s15_Infra_le_v1Sub D.M V₀ V hV L) z
    have h1 := hκ (am m hm) w
    have h2 := s15_T7_kappa_act V₀ V₁ V hV
      (s15_Infra_le_v1Sub D.M V₀ V hV L) (c.m_le_stabTil hm) (hm₁ m hm) w
    exact (h2.symm.trans h1).symm
  have hραinv : ∀ (m : G) (hm : m ∈ D.M),
      (ρ ((am m hm)⁻¹) : MulAut S) = (αm m hm)⁻¹ := by
    intro m hm
    rw [map_inv, Subgroup.coe_inv, hρα m hm]
  have hker : ∀ k ∈ A,
      (∀ g ∈ A, k ∈ normalizer
        ((B.map (MulAut.conj g).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W))) →
      (∃ n : ℕ, k ^ (p ^ n) = 1) → k = 1 := by
    intro k hk hkN hkpow
    obtain ⟨n, hkn⟩ := hkpow
    let kA : A := ⟨k, hk⟩
    have hbA_mem : ∀ g : A, (g : MulAut W)⁻¹ * k * (g : MulAut W) ∈ A := by
      intro g
      exact A.mul_mem (A.mul_mem (A.inv_mem g.2) hk) g.2
    let bA : A → A := fun g =>
      ⟨(g : MulAut W)⁻¹ * k * (g : MulAut W), hbA_mem g⟩
    have hfixUFor : ∀ g : A, ∀ u ∈ U, (ρ (bA g) : MulAut S) u = u := by
      intro g u hu
      have hbN : ((bA g : A) : MulAut W) ∈
          Subgroup.normalizer (B : Set (MulAut W)) := by
        have hgk := hkN (g : A) g.2
        rw [CFSG.GroupTheory.normalizer_map_conj (g : MulAut W) B] at hgk
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hgk
        have hxeq' : (g : MulAut W) * x * (g : MulAut W)⁻¹ = k := by
          simpa [MulAut.conj_apply] using hxeq
        have hbx : ((bA g : A) : MulAut W) = x := by
          calc ((bA g : A) : MulAut W)
              = (g : MulAut W)⁻¹ * k * (g : MulAut W) := rfl
            _ = (g : MulAut W)⁻¹ *
                  ((g : MulAut W) * x * (g : MulAut W)⁻¹) * (g : MulAut W) := by
                rw [hxeq']
            _ = x := by group
        rw [hbx]
        exact hx
      let bN : Subgroup.normalizer (B : Set (MulAut W)) :=
        ⟨((bA g : A) : MulAut W), hbN⟩
      let β : MulAut ↥B := B.normalizerMonoidHom bN
      have hbpow : ((bA g : A) : MulAut W) ^ (p ^ n) = 1 := by
        have hb_eq : ((bA g : A) : MulAut W) =
            MulAut.conj ((g : A) : MulAut W)⁻¹ k := by
          simp [bA]
        rw [hb_eq, ← map_pow, hkn, map_one]
      have hbNpow : bN ^ (p ^ n) = 1 := Subtype.ext (by simpa [bN] using hbpow)
      have hβpow : β ^ (p ^ n) = 1 := by
        simpa [β] using congrArg (B.normalizerMonoidHom) hbNpow
      have hβcard : β ^ Nat.card (MulAut ↥B) = 1 := pow_card_eq_one'
      have hcopP : Nat.Coprime p (Nat.card (MulAut ↥B)) :=
        hp.coprime_iff_not_dvd.mpr hpAut
      have hcop : Nat.Coprime (p ^ n) (Nat.card (MulAut ↥B)) := hcopP.pow_left n
      have hβ1 : β = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hβpow, hβcard⟩
      have hcommB : ∀ y ∈ B, ((bA g : A) : MulAut W) * y = y * ((bA g : A) : MulAut W) := by
        intro y hy
        have hβy : B.normalizerMonoidHom bN ⟨y, hy⟩ = ⟨y, hy⟩ := by
          change β ⟨y, hy⟩ = ⟨y, hy⟩
          rw [hβ1]
          rfl
        have h2 : (B.normalizerMonoidHom bN ⟨y, hy⟩ : MulAut W) = y := by
          simpa using congrArg (fun z : ↥B => (z : MulAut W)) hβy
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
        calc ((bA g : A) : MulAut W) * y
            = (((bA g : A) : MulAut W) * y * ((bA g : A) : MulAut W)⁻¹) *
                ((bA g : A) : MulAut W) := by group
          _ = y * ((bA g : A) : MulAut W) := by rw [h2]
      have hB'leA' : B' ≤ A' := s16e_two_lStar_le D c.setting.hyp151 hV
      have hcommStar : ∀ y ∈ B',
          (ρ (bA g) : MulAut S) * y = y * (ρ (bA g) : MulAut S) := by
        intro y hy
        have hyA' : y ∈ A' := hB'leA' hy
        have hySub : (⟨y, hyA'⟩ : A') ∈ B'.subgroupOf A' := hy
        rw [← hρB] at hySub
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hySub
        have hxB : (x : MulAut W) ∈ B := by
          simpa only [B] using (Subgroup.mem_subgroupOf.mp hx)
        let xB : ↥B := ⟨(x : MulAut W), hxB⟩
        have hxA : (⟨(xB : MulAut W), hcomp.1 xB.2⟩ : A) = x := Subtype.ext rfl
        have hρx : (ρ x : MulAut S) = y := by
          simpa using congrArg (fun z : A' => (z : MulAut S)) hxeq
        have hcommA : (bA g) * x = x * (bA g) := by
          rw [← hxA]
          exact Subtype.ext (hcommB (xB : MulAut W) xB.2)
        have hmap : (ρ ((bA g) * x) : MulAut S) = (ρ (x * (bA g)) : MulAut S) := by
          rw [hcommA]
        have hmap' : (ρ (bA g) : MulAut S) * (ρ x : MulAut S) =
            (ρ x : MulAut S) * (ρ (bA g) : MulAut S) := by
          simpa only [map_mul, Subgroup.coe_mul] using hmap
        simpa only [hρx] using hmap'
      have hcent : (ρ (bA g) : MulAut S) ∈
          Subgroup.centralizer (B' : Set (MulAut S)) := by
        rw [Subgroup.mem_centralizer_iff]
        exact fun y hy => (hcommStar y hy).symm
      have hnorm : (ρ (bA g) : MulAut S) ∈
          Subgroup.normalizer (B' : Set (MulAut S)) :=
        (Subgroup.centralizer_le_normalizer (B' : Set (MulAut S))) hcent
      have hstabTop : (ρ (bA g) : MulAut S) ∈ stabSub (⊤ : Subgroup S) := fun _ => Iff.rfl
      have hstabComm : (ρ (bA g) : MulAut S) ∈
          stabSub (commSub (⊤ : Subgroup S) B') :=
        CFSG.Quasithin.StabLat.mem_stabSub_commSub hstabTop hnorm
      have hstabU : (ρ (bA g) : MulAut S) ∈ stabSub U := by
        rw [s15_Three_commSub_top_lStar c.setting.hyp151 hV] at hstabComm
        simpa [U] using hstabComm
      exact rAbsIrr153_holds S (s15_Infra_vtil_sq_eq_one V₁ V hV) ↥B B' U hperf
        (ρ (bA g) : MulAut S) hstabU hcommStar u hu
    have hfixMoved : ∀ g : A, ∀ z ∈ U.map (ρ g : MulAut S).toMonoidHom,
        (ρ kA : MulAut S) z = z := by
      intro g z hz
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
      have hb_eq : (ρ (bA g) : MulAut S) =
          (ρ g : MulAut S)⁻¹ * (ρ kA : MulAut S) * (ρ g : MulAut S) := by
        have hbA_eq : bA g = g⁻¹ * kA * g := by
          apply Subtype.ext
          rfl
        calc (ρ (bA g) : MulAut S) = (ρ (g⁻¹ * kA * g) : MulAut S) := by rw [hbA_eq]
          _ = (ρ g : MulAut S)⁻¹ * (ρ kA : MulAut S) * (ρ g : MulAut S) := by
            simp [map_mul]
      have h3 := hfixUFor g u hu
      rw [hb_eq, MulAut.mul_apply, MulAut.mul_apply] at h3
      calc (ρ kA : MulAut S) ((ρ g : MulAut S) u)
          = (ρ g : MulAut S)
              ((ρ g : MulAut S)⁻¹ ((ρ kA : MulAut S) ((ρ g : MulAut S) u))) := by
            rw [MulAut.apply_inv_self]
        _ = (ρ g : MulAut S) u := by rw [h3]
    have hZle : ∀ Z ∈ wStarConj D.M V₀ V hV L,
        Z ≤ fixV (Subgroup.zpowers (ρ kA : MulAut S)) := by
      intro Z hZ
      obtain ⟨m, hm, rfl⟩ := hZ
      have hmap_eq : imgTil V₁ V hV (conjSubgroup (wSub V₀ V hV L) m) =
          U.map ((ρ ((am m hm)⁻¹) : MulAut S)).toMonoidHom := by
        rw [s15_Infra_imgTil_conjSubgroup V₁ V (wSub V₀ V hV L) hV (hm₁ m hm)]
        change U.map ((αm m hm)⁻¹).toMonoidHom =
          U.map ((ρ ((am m hm)⁻¹) : MulAut S)).toMonoidHom
        rw [← hραinv m hm]
      intro z hz
      rw [hmap_eq] at hz
      exact mem_fixV_zpowers_iff_apply.mpr (hfixMoved (am m hm)⁻¹ z hz)
    obtain ⟨-, hspan⟩ := fifteen_two_directSum D c.std.h1217 c.setting.hyp151 hV c.ne
    have hsup : sSup (wStarConj D.M V₀ V hV L) ≤
        fixV (Subgroup.zpowers (ρ kA : MulAut S)) := sSup_le hZle
    rw [hspan] at hsup
    have htop : fixV (Subgroup.zpowers (ρ kA : MulAut S)) = ⊤ := top_le_iff.mp hsup
    have hone : (ρ kA : MulAut S) = 1 := by
      ext v
      have hv : v ∈ fixV (Subgroup.zpowers (ρ kA : MulAut S)) := by
        rw [htop]
        trivial
      simpa using mem_fixV_zpowers_iff_apply.mp hv
    have hρk : ρ kA = 1 := Subtype.ext (by simpa using hone)
    have hkA : kA = 1 := ρ.injective (by rw [hρk, map_one])
    simpa [kA] using congrArg Subtype.val hkA
  have hrank := s16h_pRank_le_ncard_div (A := MulAut W) (Mb := A) (Lb := B) hp hker
  have hncard : Set.ncard {X : Subgroup (MulAut W) |
      ∃ g ∈ A, X = B.map (MulAut.conj g).toMonoidHom} = s15 D.M V₀ V hV L := rfl
  have hzero : s15 D.M V₀ V hV L / p = 0 := Nat.div_eq_of_lt hsp
  have hrank0 : CFSG.Open.pRank p A ≤ 0 := by
    calc CFSG.Open.pRank p A
        ≤ Set.ncard {X : Subgroup (MulAut W) |
            ∃ g ∈ A, X = B.map (MulAut.conj g).toMonoidHom} / p := hrank
      _ = s15 D.M V₀ V hV L / p := by rw [hncard]
      _ = 0 := hzero
  have h2 : 2 ≤ CFSG.Open.pRank p A := c.two_le_pRank_mbar hpSig
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
