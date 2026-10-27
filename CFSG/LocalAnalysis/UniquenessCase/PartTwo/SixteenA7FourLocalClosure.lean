module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourLocalWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_fifteen_eleven_local
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    {i : ℕ} (hi : i ≤ 2) :
    centralizer (E3.cClos V i D.T : Set G) ≤ D.M := by
  classical
  by_contra hC
  have h154 : Hyp154 D V₀ V L := s168e3_hyp154_of_a7Four_of_s15_eq_two c hrow hs
  have hdata := s168e3_a7Four_spaceData c hrow
  have hV1 : v1Sub D.M V₀ V hV L = ⊥ := s15_Eleven_v1_eq_bot D h154 hV hC
  have hev : Even (s15 D.M V₀ V hV L) := by
    rw [hs]
    exact even_two
  have hn2 : ¬ (s15 D.M V₀ V hV L = 2 ∧ gamma15 D.M V₀ V hV L ≤ 3) := by
    rintro ⟨-, hle⟩
    have hγ := hdata.gamma15_eq
    omega
  have h4 := s15_Eleven_h4 D h154 hV c.ne hev hn2
  have hγ4 : 4 ≤ gamma15 D.M V₀ V hV L := by
    rw [hdata.gamma15_eq]
  obtain ⟨g, A, hAg, hAM, hmA, hAN⟩ := s15_Eleven_exists_A D h154 hV c.ne hV1 hC
  have hW := s168e3_fifteen_nine_local c hrow hs hInv
  obtain ⟨_, v, X₀, _, _, _, _, hv2, hvM, _, hX₀, hvN, hmK1⟩ :=
    s15_Eleven_exists_normalized_transvection_of_wClos D c.std.h1217 h154 hV c.ne hW hV1 hs hγ4
      hi h4 hAg hAM hmA hAN
  let E : Subgroup G := conjSubgroup (X₀ ⊔ v1Sub D.M V₀ V hV L) g
  let U : Subgroup G := conjSubgroup (v1Sub D.M V₀ V hV L) g
  let K : Subgroup G := E ⊓ centralizer ({v} : Set G)
  have hUbot : U = ⊥ := by
    dsimp [U]
    rw [hV1, E3.conjSubgroup_bot]
  have hmK : E3.mQuot E K = 1 := by
    dsimp [E, K]
    simpa [hV1] using hmK1
  have hUK : U ≤ K := by
    rw [hUbot]
    exact bot_le
  have hKD : K ≤ E := inf_le_left
  have hvN' : v ∈ normalizer
      (conjSubgroup (X₀ ⊔ v1Sub D.M V₀ V hV L) g : Set G) := by
    simpa [hV1] using hvN
  have hfix : ∀ k ∈ K, v * k * v⁻¹ * k⁻¹ ∈ U := by
    intro k hk
    have hkv0 : v * k = k * v :=
      Subgroup.mem_centralizer_iff.mp hk.2 v (by simp)
    have hkv : v * k * v⁻¹ = k := by
      calc v * k * v⁻¹ = k * v * v⁻¹ := by rw [hkv0]
        _ = k := by group
    rw [hkv, mul_inv_cancel]
    rw [hUbot]
    exact Subgroup.one_mem _
  have hcomm := s168e3_block_comm_mem_v1Sub_of_hyperplane c hrow hInv hX₀
    (g := g) (X := X₀) (K := K) hvM hv2 hvN' hUK hKD hmK hfix
  have hEcent : E ≤ centralizer ({v} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyv : y = v := by simpa using hy
    subst y
    have hmem : v * d * v⁻¹ * d⁻¹ ∈ U := hcomm d hd
    rw [hUbot] at hmem
    have h1 : v * d * v⁻¹ * d⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hKE : K = E := by
    dsimp [K]
    exact inf_eq_left.mpr hEcent
  rw [hKE, E3.mQuot_self] at hmK
  omega

theorem s168e3_not_s15T7Config
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    {g : G} {X F C K : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) :
    ¬ s15T7Config (conjSubgroup D.M g)
      (conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g)
      (conjSubgroup (v1Sub D.M V₀ V hV L) g) F C K := by
  rintro ⟨hFab, hFM, hCF, hFN, hC, hUK, hKE, hmK, hFK, hmFC⟩
  have hFC : F ≤ C := by
    intro f hf
    refine (hC f hf).2 ?_
    exact s168e3_block_comm_mem_v1Sub_of_hyperplane c hrow hInv hX
      (v := f) (K := K) (hFM hf) (hFab.mul_self_eq_one hf) (hFN hf) hUK hKE hmK
      (hFK f hf)
  have hEq : C = F := le_antisymm hCF hFC
  rw [hEq, E3.mQuot_self] at hmFC
  omega

theorem s168e3_fifteen_twelve_local
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    {n : ℕ} (hn : n ≤ 2) :
    calO n D.M V₀ V = ∅ := by
  classical
  by_contra hempty
  have hO : (calO n D.M V₀ V).Nonempty := Set.nonempty_iff_ne_empty.2 hempty
  obtain ⟨k, hk⟩ := exists_cond1512 hO
  have h154 : Hyp154 D V₀ V L := s168e3_hyp154_of_a7Four_of_s15_eq_two c hrow hs
  have hdata := s168e3_a7Four_spaceData c hrow
  have hnγ : n + 2 ≤ gamma15 D.M V₀ V hV L := by
    rw [hdata.gamma15_eq]
    omega
  have hs1 : 1 < s15 D.M V₀ V hV L := by omega
  obtain ⟨Z, F, C, K, hZ, hcfg⟩ :=
    s15_Twelve_exists_config_caseI D c.std.h1217 h154 hV c.ne hk hn hnγ hs1
  exact s168e3_not_s15T7Config (g := (1 : G)) (X := Z) (F := F) (C := C) (K := K)
    c hrow hInv hZ (by simpa [conjSubgroup_one] using hcfg)

theorem s168e3_false_of_a7Four_of_s15_eq_two_of_blockInvolutionBound
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV) : False := by
  classical
  have h154 : Hyp154 D V₀ V L := s168e3_hyp154_of_a7Four_of_s15_eq_two c hrow hs
  have h125 : Hyp125 D V₀ V := h154.hyp151.hyp125
  have hdata := s168e3_a7Four_spaceData c hrow
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
    (E3.wClos_mono D.sylowM.le).trans (s168e3_fifteen_nine_local c hrow hs hInv)
  have hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p D.M := by
    intro p hp
    simpa only [UC6.groupPRank_eq_pRank, c.std.pRank_eq_three hp] using
      (show (3 : ℕ) ≤ 3 from le_rfl)
  have hN := fifteen_thirteen_a D (r129_1_of_r127 D c.std.h127) c.std.h61 c.std.hSg.nonempty
    hrk h125 hW
  have hkc := s15_Thirteen_k_cases D
  have hk2 : D.k ≤ 2 := by rcases hkc with h | h <;> omega
  have hC : centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M :=
    s168e3_fifteen_eleven_local c hrow hs hInv hk2
  have hfour : max (gamma15 D.M V₀ V hV L)
      ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) = 4 := by
    rw [hdata.gamma15_eq, hs]
    norm_num
  have hkm : D.k < max (gamma15 D.M V₀ V hV L)
      ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) := by
    rw [hfour]
    omega
  have hr := s15_Thirteen_lt_rParam D h154 hV c.ne hkm
  have hbeta4 : ((4 : ℕ) : ℕ∞) ≤ betaN 0 D.M V := by
    simpa [hfour] using s15_Thirteen_beta D c.std.h1217 h154 hV c.ne
  have hbeta : (D.k : ℕ∞) < betaN 0 D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (show D.k < 4 by omega)) hbeta4
  obtain ⟨H, A, K, hS, hA, hK, hne⟩ := s15_Thirteen_exists_A_K D c.std.h126 h125 hN hC
  obtain ⟨X, g, hX, hg⟩ := s15_Thirteen_six_nine D h125 hS hA hK hr hbeta hne
  have hO : (calO D.k D.M V₀ V).Nonempty := ⟨X, g, hX, hg.1⟩
  have hempty := s168e3_fifteen_twelve_local c hrow hs hInv hk2
  rw [hempty] at hO
  obtain ⟨x, hx⟩ := hO
  exact hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
