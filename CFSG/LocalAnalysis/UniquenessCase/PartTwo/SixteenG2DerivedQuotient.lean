module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenG2DerivedModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKG2Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixedQuotientCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s168e3_g2_quotient_data
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hN : G2NaturalDerived (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 1)
    (hs : s15 D.M V₀ V hV L = 1) :
    ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q)
      (q : Vtil V₀ V hV →* Q) (ρ : ↥(lBar V₀ V hV L) →* MulAut Q),
      Function.Surjective q ∧
      (∀ x : Vtil V₀ V hV, q x = 1 ↔ x ∈ fixV (lBar V₀ V hV L)) ∧
      Function.Injective ρ ∧
      (∀ (l : ↥(lBar V₀ V hV L)) (x : Vtil V₀ V hV),
        q ((l : MulAut (Vtil V₀ V hV)) x) = ρ l (q x)) ∧
      G2NaturalDerived ρ.range ⊤ ⊥ 1 ∧
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) = ⊥ ∧
      CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 2 ∧
      D.sig = {3} ∧
      CFSG.Open.pRank 3 D.M = 3 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) = 3 := by
  classical
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hcompH : CFSG.Open.IsComponentOf H (Mbar D.M V₀ V hV) := hcomp
  have hqH : CFSG.Open.IsQuasisimple ↥H := hcompH.2.2
  have hperf : Group.IsPerfect ↥H := ⟨hqH.1⟩
  have hPSU : IsPSU 3 3 1 ↥H := s168e3_g2_isPSU hN
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) H = ⊤ := by
    simpa only [H, wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  obtain ⟨Q, hQc, hQf, q, ρ, hqsurj, hqker, hρinj, heq, -, -, -⟩ :=
    s16k_qm_quotMap (W := Vtil V₀ V hV) (H := H) hqH hcomm
      (s15_Infra_vtil_sq_eq_one V₀ V hV)
  have hqker_eq : q.ker = fixV H := by
    ext x
    rw [MonoidHom.mem_ker, hqker x]
  have hZeq : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) H ⊓ fixV H) = fixV H := by
    rw [hcomm, top_inf_eq]
  have hNvia : G2NaturalDerived H
      (commSub ⊤ H) (commSub ⊤ H ⊓ fixV H) 1 := hN
  obtain ⟨K, hKfield, hKfin, hKcard, π, hπ⟩ := hNvia
  have hker : q.ker ≤ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) H ⊓ fixV H) := by
    rw [hZeq]
    exact hqker_eq.le
  have hequiv : ∀ (h : ↥H) (w : Vtil V₀ V hV),
      q ((h : MulAut (Vtil V₀ V hV)) w) =
        ((ρ.rangeRestrict h : ρ.range) : MulAut Q) (q w) := by
    intro h w
    exact heq h w
  have hreal : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes ρ.range
      ((commSub (⊤ : Subgroup (Vtil V₀ V hV)) H).map q)
      ((commSub (⊤ : Subgroup (Vtil V₀ V hV)) H ⊓ fixV H).map q) :=
    s16k_realizes_map ⟨π, hπ⟩ q hker ρ.rangeRestrict ρ.rangeRestrict_surjective hequiv
  have hmapTop : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) H).map q = ⊤ := by
    rw [hcomm, Subgroup.map_top_of_surjective _ hqsurj]
  have hmapBot : ((commSub (⊤ : Subgroup (Vtil V₀ V hV)) H ⊓ fixV H).map q) = ⊥ := by
    rw [hZeq]
    exact (Subgroup.map_eq_bot_iff _).mpr (le_of_eq hqker_eq.symm)
  have hNq : G2NaturalDerived ρ.range ⊤ ⊥ 1 := by
    refine ⟨K, hKfield, hKfin, hKcard, ?_⟩
    rwa [hmapTop, hmapBot] at hreal
  have hcentrange : Subgroup.centralizer (ρ.range : Set (MulAut Q)) = ⊥ :=
    s16k_centralizer_g2_trivial hNq
  have hn : ∀ a ∈ Subgroup.centralizer (ρ.range : Set (MulAut Q)), a ^ 1 = 1 := by
    intro a ha
    rw [hcentrange] at ha
    simpa using Subgroup.mem_bot.mp ha
  have hcentHpow : ∀ a ∈ Subgroup.centralizer (H : Set (MulAut (Vtil V₀ V hV))),
      a ^ 1 = 1 :=
    centralizer_pow_eq_one_of_fixed_quotient (H := H) q ρ hqsurj hqker heq hcomm
      (n := 1) hn
  have hcentH : Subgroup.centralizer (H : Set (MulAut (Vtil V₀ V hV))) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    simpa using hcentHpow a ha
  have hAnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  have hnorm : ∀ n ∈ Mbar D.M V₀ V hV, ∀ l ∈ H, n * l * n⁻¹ ∈ H :=
    fun n hn l hl => (Subgroup.mem_normalizer_iff.mp (hAnorm hn) l).mp hl
  have hB42 : CFSG.Quasithin.B42TypeU33 ↥H := s168e3_g2_b42Type hPSU hperf
  have hrank3le : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 2 := by
    have h := s16k_pRank_le_of_normalizer (Q := Vtil V₀ V hV) (L' := H)
      (N := Mbar D.M V₀ V hV) hnorm Nat.prime_three
    rw [hcentH, inf_bot_eq, s13_Rank13_pRank_bot Nat.prime_three, Nat.zero_add] at h
    have haut := s16k_pRank_aut_u33 hB42 Nat.prime_three (by norm_num)
    rw [if_pos rfl] at haut
    exact h.trans haut
  have hsig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 ?_
    intro q hq hq2 hq3
    have h := s16k_pRank_le_of_normalizer (Q := Vtil V₀ V hV) (L' := H)
      (N := Mbar D.M V₀ V hV) hnorm hq
    rw [hcentH, inf_bot_eq, s13_Rank13_pRank_bot hq, Nat.zero_add] at h
    have haut := s16k_pRank_aut_u33 hB42 hq hq2
    rw [if_neg hq3] at haut
    omega
  have hM3 : CFSG.Open.pRank 3 D.M = 3 :=
    c.std.pRank_eq_three (p := 3) (by rw [hsig]; exact Set.mem_singleton 3)
  have hbar3 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) = 3 := by
    rw [← CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M]
    exact hM3
  exact ⟨Q, hQc, hQf, q, ρ, hqsurj,
    (fun x => by simpa only [H] using hqker x), hρinj, heq, hNq, hcentH, hrank3le, hsig, hM3,
    hbar3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
