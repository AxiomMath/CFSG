module

public import CFSG.Quasithin.MS93.MResSq
public import CFSG.Quasithin.MS93.S45Incl
public import CFSG.Quasithin.H13.A5W1622F4L45D

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S45
open scoped Pointwise commutatorElement Matrix

theorem incl_of_sq {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h43 : S43) (h44 : S44) (h14 : MS14AS) (hSQ : SQTKQuot) (hQ2a : S45Q2a)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hfull : IsSL3Full M T L) (hL : NotSL3Big L)
    (hsq : Nat.card ↥(omegaOneCenterOf T ⊓ Subgroup.centralizer (L : Set G)) ^ 2 ≤
      Nat.card ↥(omegaOneCenterOf T)) :
    ∀ y ∈ Vq M L, (∀ x ∈ Vq M L, y * x * y⁻¹ * x⁻¹ ∈ Vq M L ⊓ Subgroup.centralizer (L : Set G)) →
      y ∈ frattiniIn (Vq M L) := by
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have hq := card_eq_two_of_via h hL hφ
  have c : Ctx M T L φ := Ctx.ofItems h43 h44 h hmin hb hφ
  have hZV : c.HZV := hQ2a G M T L F φ c hq
  have hZq : Nat.card ↥(Zq M L) ≤ Fintype.card F ^ 2 := card_zq_le_of_sq c hsq
  have hQ2b := hQ2b_of_card_zq h14 hSQ c hZV hZq
  obtain ⟨p₀, hp₀⟩ := c.exists_isGoodPath_of_ctx 28
  have hα := c.isMVtx_of_isGoodPath hp₀ (k := 34) (by omega) (by decide)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα (isMVtx_baseA _)
  have hp := hp₀.smul g
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp (a := 34) (by decide) (by omega)
    (by omega)
  have key := @Ctx.mem_frattiniIn_of_commutator_mem G _ _ F _ _ M T L φ c _ p' 64 h14 hSQ hZV
    (S45Q4.hQ4 c) hQ2b hp hp' 34 (by decide) le_rfl (by omega) hpp' hU1 hU3
  have hg' : (fun i => g • p₀ i) 34 = baseA (puAmalgam c.hyp.le) := hg
  simp only [hg'] at key
  have hOM : pCoreOf 2 M ≤ M := pCoreOf_le' M
  have hVM : Vq M L ≤ M := Vq_le h.L_le
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hLt : Ltil h.le L (baseA _) = imM h.le L :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)
  have hV : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ = imM h.le (Vq M L) := by
    rw [hQ, hLt, imM_commutator h.le hOM h.L_le]
  have eCL : imM h.le (Vq M L ⊓ Subgroup.centralizer (L : Set G)) =
      ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
        Subgroup.centralizer (Ltil h.le L (baseA _) : Set _) := by
    rw [imM_inf_centralizer h.le _ h.L_le, ← hV, ← hLt]
  have eΦ : imM h.le (frattiniIn (Vq M L)) =
      frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ := by
    rw [imM_frattiniIn h.le hVM, hV]
  intro y hy hyc
  have hyM : y ∈ M := hVM hy
  set ι := (puAmalgam h.le).ofA with hι
  have hmem : ∀ {K : Subgroup G} {m : G} (hm : m ∈ M), ι ⟨m, hm⟩ ∈ imM h.le K ↔ m ∈ K :=
    fun {K} {m} hm => S46.ofA_mem_imM h.le (K := K) ⟨m, hm⟩
  have hyV : ι ⟨y, hyM⟩ ∈ ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ := by
    rw [hV]; exact (hmem hyM).mpr hy
  have h1 := key hyV (fun x' hx' => by
    rw [hV] at hx'
    obtain ⟨⟨x, hxM⟩, hxV, rfl⟩ := Subgroup.mem_map.mp hx'
    rw [Subgroup.mem_subgroupOf] at hxV
    have hcomm : ⁅ι ⟨y, hyM⟩, ι ⟨x, hxM⟩⁆ = ι ⟨y * x * y⁻¹ * x⁻¹, M.mul_mem (M.mul_mem
        (M.mul_mem hyM hxM) (M.inv_mem hyM)) (M.inv_mem hxM)⟩ := by
      rw [← map_commutatorElement]
      rfl
    rw [hcomm, ← eCL]
    exact (hmem _).mpr (hyc x hxV))
  rw [← eΦ] at h1
  exact (hmem hyM).mp h1

open CFSG.Quasithin.H13.A5.C45 in
theorem incl_of_case4Corr_of_sq {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18) (h38 : S38) (h43 : S43) (h44 : S44)
    (h14 : MS14AS) (hSQ : SQTKQuot) (hQ2a : S45Q2a) (h46 : S46Two) (h512 : S512) (h7 : S7Two)
    (h : PUHyp M T L) (hL : NotSL3Big L) (hS : NoSp4Quot L) (hsq : C134SqCond T L)
    (hc : C134CorrLocal.IsC134Case4Corr M T L) :
    ∀ y ∈ Vq M L, (∀ x ∈ Vq M L, y * x * y⁻¹ * x⁻¹ ∈ Vq M L ⊓ Subgroup.centralizer (L : Set G)) →
      y ∈ frattiniIn (Vq M L) := by
  obtain ⟨⟨n, F, _, _, α, hF, hα, hE, hZeq, -, -, hΦ, -, -⟩, -⟩ := hc
  have hFc : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero] at hF; omega
    · exact hpos
  have hC4 : 4 ≤ Nat.card ↥(c134CQ M L) := by
    rw [card_of_isE2 hE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hΦZ : ¬ frattiniIn (c134Q M L) ≤ centerOf (c134Q M L) := not_le_of_isSum one_pos hΦ
  have habel : ¬ ∀ x ∈ Vq M L, ∀ y ∈ Vq M L, x * y = y * x := by
    intro hab
    apply hΦZ
    intro y hy
    have hyQ : y ∈ c134Q M L := Subgroup.map_subtype_le _ hy
    exact ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun x hx => (hab x hx y hyQ)⟩
  have hnot5 : ¬ MS93Case5 (Vq M L) L := by
    rintro ⟨n', F', _, _, α', -, -, hnat⟩
    exact habel fun x hx y hy => comm_of_isSum_bot hnat hx hy
  have hnot11 : ¬ MS93Case11 (Vq M L) T L := by
    have hΓ : ∀ {F' : Type} [Field F'] (g : Matrix.GeneralLinearGroup (Fin 3) F'),
        (g : Matrix (Fin 3) (Fin 3) F').det = 1 → g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 F' :=
      fun g hg => Subgroup.subset_closure hg
    rintro ⟨n', F', _, _, α', -, hα', hZnat, -⟩
    have hbot : c134CQ M L = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzZ : z ∈ centerOf (c134Q M L) := by
        rw [hZeq]
        exact Subgroup.mem_sup_left hz
      rw [Subgroup.mem_bot]
      exact eq_one_of_mem_centralizer hΓ hα' hZnat hzZ (Subgroup.mem_inf.mp hz).2
    rw [hbot, Subgroup.card_bot] at hC4
    omega
  by_cases hb : critDist (puAmalgam h.le) = 2
  · obtain ⟨h36a, -⟩ := h36 G M T L h hb
    by_cases hVU : Vq M L = Uq M T L
    · exact (habel fun x hx y hy => by
        rw [hVU] at hx hy
        exact isMulCommutative_subgroup_iff.mp h.isElemAbelian_Uq.1 x hx y hy).elim
    · exact (hnot5 (h18 G M T L h hb hVU (h36a.resolve_left hVU))).elim
  have hpos := h.critDist_pos
  obtain ⟨m, hm⟩ := h.critDist_even
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨T₁, hT₁, hchar, -, h₁, hmin₁, hV₁⟩ := burnsideMS93R_exists_charMin h
  have hpos₁ := h₁.critDist_pos
  obtain ⟨m₁, hm₁⟩ := h₁.critDist_even
  by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
  · exact (hnot5 (h7 G M T L (L ⊔ T₁) T₁ h h₁ hT₁ hmin₁ hV₁ hb' hb₁)).elim
  have hb₁' : 2 < critDist (puAmalgam h₁.le) := by omega
  rcases h38 G (L ⊔ T₁) T₁ L h₁ hb₁' with hSL₁ | hSp₁
  swap
  · exact (h512 G (L ⊔ T₁) T₁ L h₁ hmin₁ hb₁' (isSp4Full_of_isSp4U_of_noSp4 h₁ hS hSp₁)).elim
  have hFull := isSL3Full_of_isSL3U h₁ hL hSL₁
  rcases (show critDist (puAmalgam h₁.le) = 4 ∨ 4 < critDist (puAmalgam h₁.le) by omega)
    with h4 | h4
  · have h11 := h46 G (L ⊔ T₁) T₁ L h₁ hmin₁ h4 hFull hL
    rw [hV₁] at h11
    exact (hnot11 (h11.mono hT₁)).elim
  · have hI := incl_of_sq h43 h44 h14 hSQ hQ2a h₁ hmin₁ h4 hFull hL (hsq T₁ hT₁ hchar)
    rw [hV₁] at hI
    exact hI

@[expose] def C134Case4Lemma45CorrSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α) →
    C134SqCond R L → C134CorrLocal.IsC134Case4Corr G₀ R L →
    ∀ y ∈ c134Q G₀ L, (∀ x ∈ c134Q G₀ L, y * x * y⁻¹ * x⁻¹ ∈ c134CQ G₀ L) →
      y ∈ frattiniIn (c134Q G₀ L)

section Holds


theorem c134Case4Lemma45CorrSq_holds
    : C134Case4Lemma45CorrSq := by
  intro G _ _ G₀ R L hMS hL hG hsl3 hsq hc
  obtain ⟨F, _, _, α, hF2, hα⟩ := hsl3
  have h := puHyp_of_msPair_of_simple rankTwoLieSimple_holds hMS hL hG
  have h441 := s441_holds
  have h44 :=
    s44_frontier h441 (S4A.s442_of_s441 ms14AS_holds sqtkQuot_holds s32_holds s43_holds h441)
  exact incl_of_case4Corr_of_sq s32_holds (s36_of_g2 s38G2_holds) s37_holds s18_holds
    (s38_of_g2 s38G2_holds) s43_holds h44 ms14AS_holds sqtkQuot_holds S45J.s45Q2a_holds
    (s46Two_of s32_holds (s39_of s32_holds) (s42_of s32_holds) s43_holds ms14AS_holds
      sqtkQuot_holds)
    s512_holds (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds) h
    (notSL3Big_of_isModO2Surj_two hF2 hα) (noSp4Quot_of_isModO2Surj_two hF2 hα) hsq hc

end Holds

end CFSG.Quasithin.MS93.MRes
