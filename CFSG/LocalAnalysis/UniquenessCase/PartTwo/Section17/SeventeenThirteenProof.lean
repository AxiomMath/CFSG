module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenBounds
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.WeakClosure81.InFSqQuasisimple
public import CFSG.Quasithin.H13.NQTermSymplecticFour
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 (InFSq not_inFSq_zero not_inFSq_zero_of_isQuasisimple_bar2)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem R17_13At_of_index_bounds (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (hne : (Delta17_12 D (fundPred q) r q L).Nonempty)
    (h0 : ∀ H ∈ Delta17_12 D (fundPred q) r q L, ¬ InFSq 0 H)
    (h1 : 9 < q → ∀ H ∈ Delta17_12 D (fundPred q) r q L, InFSq 1 H)
    (h2 : q ≤ 9 → q ≠ 9 → ∀ H ∈ Delta17_12 D (fundPred q) r q L, InFSq 2 H)
    (h3 : q = 9 → ∀ H ∈ Delta17_12 D (fundPred q) r q L, InFSq 3 H) :
    R17_13At D (fundPred q) V₀ V L r q hC := by
  classical
  set Δ := Delta17_12 D (fundPred q) r q L with hΔ
  have hge : (1 : ℕ∞) ≤ iL17_12 D (fundPred q) r q L := by
    obtain ⟨H, hH⟩ := hne
    have hH1 : (1 : ℕ∞) ≤ fIndex H := by
      by_cases htop : fIndex H = ⊤
      · rw [htop]
        exact le_top
      · rw [← ENat.coe_toNat htop]
        refine ENat.coe_le_coe.mpr ?_
        by_contra hlt
        have h0n : (fIndex H).toNat = 0 := by omega
        have hz : fIndex H ≤ (0 : ℕ∞) := by
          rw [← ENat.coe_toNat htop, h0n]
          rfl
        exact h0 H hH (fIndex_le_iff.mp hz)
    exact hH1.trans (le_fIndexMax hH)
  rcases lt_or_ge (9 : ℕ) q with hq | hq
  · have hle : iL17_12 D (fundPred q) r q L ≤ 1 :=
      fIndexMax_le_iff.mpr (h1 hq)
    have hone : iL17_12 D (fundPred q) r q L = 1 := le_antisymm hle hge
    exact Or.inl hone
  · rcases eq_or_ne q 9 with hq9 | hq9
    · have hle : iL17_12 D (fundPred q) r q L ≤ 3 :=
        fIndexMax_le_iff.mpr (h3 hq9)
      have hne_top : iL17_12 D (fundPred q) r q L ≠ ⊤ :=
        ne_top_of_le_ne_top (by norm_num) hle
      have hcoe : ((iL17_12 D (fundPred q) r q L).toNat : ℕ∞) =
          iL17_12 D (fundPred q) r q L := ENat.coe_toNat hne_top
      have hnat_le : (iL17_12 D (fundPred q) r q L).toNat ≤ 3 := by
        have := hle
        rw [← hcoe] at this
        exact ENat.coe_le_coe.mp this
      have hnat_ge : 1 ≤ (iL17_12 D (fundPred q) r q L).toNat := by
        have := hge
        rw [← hcoe] at this
        exact ENat.coe_le_coe.mp this
      have hcases : (iL17_12 D (fundPred q) r q L).toNat = 1 ∨
          (iL17_12 D (fundPred q) r q L).toNat = 2 ∨
          (iL17_12 D (fundPred q) r q L).toNat = 3 := by omega
      rcases hcases with h1' | h2' | h3'
      · exact Or.inl (by rw [← hcoe, h1']; rfl)
      · exact Or.inr (Or.inl ⟨hq, by rw [← hcoe, h2']; rfl⟩)
      · exact Or.inr (Or.inr ⟨hq9, by rw [← hcoe, h3']; rfl⟩)
    · have hle : iL17_12 D (fundPred q) r q L ≤ 2 :=
        fIndexMax_le_iff.mpr (h2 hq hq9)
      have hne_top : iL17_12 D (fundPred q) r q L ≠ ⊤ :=
        ne_top_of_le_ne_top (by norm_num) hle
      have hcoe : ((iL17_12 D (fundPred q) r q L).toNat : ℕ∞) =
          iL17_12 D (fundPred q) r q L := ENat.coe_toNat hne_top
      have hnat_le : (iL17_12 D (fundPred q) r q L).toNat ≤ 2 := by
        have := hle
        rw [← hcoe] at this
        exact ENat.coe_le_coe.mp this
      have hnat_ge : 1 ≤ (iL17_12 D (fundPred q) r q L).toNat := by
        have := hge
        rw [← hcoe] at this
        exact ENat.coe_le_coe.mp this
      have hcases : (iL17_12 D (fundPred q) r q L).toNat = 1 ∨
          (iL17_12 D (fundPred q) r q L).toNat = 2 := by omega
      rcases hcases with h1' | h2'
      · exact Or.inl (by rw [← hcoe, h1']; rfl)
      · exact Or.inr (Or.inl ⟨hq, by rw [← hcoe, h2']; rfl⟩)

theorem delta17_12_nonempty_case_one (D : Data G) (r q : ℕ) (L : Subgroup G)
    (h1 : P17_12_1 r q L) : (Delta17_12 D (fundPred q) r q L).Nonempty := by
  refine ⟨D.T ⊔ L, ?_⟩
  rw [Delta17_12, dif_pos h1]
  refine ⟨1, D.M.one_mem, ?_⟩
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem delta17_12_nonempty_case_two
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    (hRee : K_ReeSylowGeneration)
    (h1 : ¬ P17_12_1 r q L) (h2 : P17_12_2 q L) :
    (Delta17_12 D (fundPred q) r q L).Nonempty := by
  classical
  obtain ⟨n, hq_eq, hLie⟩ := h2
  have hq3 : 3 < q := h9
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hq_eq
    norm_num at hq_eq
    omega
  let S : Subgroup G := NTL17 D L
  have hS_le_N : S ≤ Subgroup.normalizer (L : Set G) := by
    intro s hs
    exact (Subgroup.mem_inf.mp hs).2
  have hS_le_T : S ≤ D.T := fun s hs => (Subgroup.mem_inf.mp hs).1
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le hS_le_T
  obtain ⟨P, hPcoe⟩ := exists_sylow_syl2Bar D L hC.memL.1
  obtain ⟨hZX, hOutOdd, hReePart⟩ := hRee (Bar2 L) q n ⟨n, hq_eq, hLie⟩ hq_eq hn1
  obtain ⟨hEel, hEcard8, x, y, hxP, hyP, hxy, hx2, hy2,
    hKxL2, hKyL2, hKxO2, hKyO2, hKyZ, hCxdec, hCydec, hCxcoat, hCycoat, hxKy⟩ :=
    hReePart P
  let Kx : Subgroup (Bar2 L) :=
    ⁅Subgroup.centralizer ({x} : Set (Bar2 L)), Subgroup.centralizer ({x} : Set (Bar2 L))⁆
  let ρ : S →* MulAut (Bar2 L) :=
    (UC6S846.rhoL L).comp (Subgroup.inclusion hS_le_N)
  let κ : S →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp ρ
  have hκbot : κ.range = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    refine MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ext fun s => ?_)
    exact CFSG.Semidihedral.KleinFourOddKernel.hom_eq_one_of_coprime_card κ
      (by rw [hk]; exact (Nat.coprime_two_left.mpr hOutOdd).pow_left k) s
  have hinner : ∀ s : S,
      ρ s ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
    intro s
    have hκs : κ s = 1 := by
      have : κ s ∈ κ.range := ⟨s, rfl⟩
      rw [hκbot] at this
      simpa using this
    exact (QuotientGroup.eq_one_iff (ρ s)).mp hκs
  choose b hb using hinner
  have hconj_inj : Function.Injective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.conj_injective_of_center_eq_bot hZX
  have hb_mul : ∀ s t : S, b (s * t) = b s * b t := by
    intro s t
    apply hconj_inj
    rw [hb (s * t), map_mul, map_mul, hb s, hb t]
  let B : S →* Bar2 L := MonoidHom.mk' b hb_mul
  have hB2 : IsPGroup 2 B.range := by
    have hS2' : IsPGroup 2 (⊤ : Subgroup S) := hS2.of_equiv Subgroup.topEquiv.symm
    rw [MonoidHom.range_eq_map]
    exact hS2'.map B
  have hE_le_B : Syl2Bar D L ≤ B.range := by
    rw [Syl2Bar]
    rintro z ⟨l, hl, rfl⟩
    have hlS : (l : G) ∈ S := (Subgroup.mem_subgroupOf.mp hl).1
    have hlL : (l : G) ∈ L := (Subgroup.mem_subgroupOf.mp hl).2
    refine ⟨⟨l, hlS⟩, ?_⟩
    apply hconj_inj
    change MulAut.conj (b ⟨l, hlS⟩) = MulAut.conj ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l)
    rw [hb]
    simpa [ρ, Subgroup.inclusion] using (UC6S846.rhoL_inner L (l : G) hlL)
  have hB_range : B.range = Syl2Bar D L := by
    have heq : B.range = (P : Subgroup (Bar2 L)) := P.3 hB2 (by rw [hPcoe]; exact hE_le_B)
    rwa [hPcoe] at heq
  have hfixx : ∀ s : S, ρ s x = x := by
    intro s
    have hBs : b s ∈ Syl2Bar D L := by rw [← hB_range]; exact ⟨s, rfl⟩
    have hxE : x ∈ Syl2Bar D L := by rw [← hPcoe]; exact hxP
    have hEelE : IsMulCommutative ↥(Syl2Bar D L) := hPcoe ▸ hEel.1
    have hcomm : (b s : Bar2 L) * x = x * b s := by
      have h := hEelE.is_comm.comm (⟨b s, hBs⟩ : ↥(Syl2Bar D L))
        (⟨x, hxE⟩ : ↥(Syl2Bar D L))
      exact congrArg Subtype.val h
    rw [← hb s, MulAut.conj_apply, hcomm]
    group
  have hKx_inv : ∀ s : S, Kx.map (ρ s).toMonoidHom = Kx := by
    intro s
    have hC : (Subgroup.centralizer ({x} : Set (Bar2 L))).map (ρ s).toMonoidHom =
        Subgroup.centralizer ({x} : Set (Bar2 L)) := by
      rw [CFSG.Walter.map_centralizer_singleton_mulEquiv, hfixx s]
    dsimp only [Kx]
    rw [Subgroup.map_commutator, hC]
  let Xx : Subgroup G := barPreimage L Kx
  have hXxL : Xx ≤ L := uc22p21c_barPreimage_le L Kx
  have hXx_norm : S ≤ Subgroup.normalizer (Xx : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      dsimp only [Xx] at hz
      unfold barPreimage at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨l, hlK, rfl⟩ := hz
      refine Subgroup.mem_map.mpr ⟨Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hmem : (UC6S846.rhoL L ⟨s, hS_le_N hs⟩) (QuotientGroup.mk l) ∈ Kx :=
          hKx_inv ⟨s, hs⟩ ▸ (Subgroup.mem_map.mpr ⟨QuotientGroup.mk l, hlK, rfl⟩)
        have h1 : (UC6S846.rhoL L ⟨s, hS_le_N hs⟩) (QuotientGroup.mk l) =
            QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l) := rfl
        rwa [h1] at hmem
      · change ((Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l : ↥L) : G) =
            s * (l : G) * s⁻¹
        exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hS_le_N hs⟩ l
    · intro hz
      dsimp only [Xx] at hz
      unfold barPreimage at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨l, hlK, hzl⟩ := hz
      refine Subgroup.mem_map.mpr
        ⟨Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hmem : (UC6S846.rhoL L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩)
            (QuotientGroup.mk l) ∈ Kx :=
          hKx_inv ⟨s⁻¹, S.inv_mem hs⟩ ▸ (Subgroup.mem_map.mpr ⟨QuotientGroup.mk l, hlK, rfl⟩)
        have h1 : (UC6S846.rhoL L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩) (QuotientGroup.mk l) =
            QuotientGroup.mk
              (Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l) := rfl
        rwa [h1] at hmem
      · change ((Subgroup.normalizerMonoidHom L
          ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l : ↥L) : G) = z
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simp only [Subgroup.coe_inv, Subgroup.coe_mk, Subgroup.coe_subtype]
        have hzl' : (l : G) = s * z * s⁻¹ := hzl
        rw [hzl']
        group
  have hXx_perm : Permutes Xx S :=
    (Subgroup.set_mul_normalizer_comm (S : Set G) Xx fun _ hx => hXx_norm hx).symm
  have hXx_L2 : IsL2Over17 (Bar2 Xx) q := by
    obtain ⟨e⟩ := bar2_barPreimage_mulEquiv L Kx hKxO2
    exact isL2Over17_of_mulEquiv (q := q) e hKxL2
  refine ⟨D.T ⊔ Xx, ?_⟩
  rw [Delta17_12, dif_neg h1, dif_pos (show P17_12_2 q L from ⟨n, hq_eq, hLie⟩)]
  exact ⟨Xx, hXxL, hXx_perm, hXx_L2, rfl⟩

theorem delta17_12_nonempty_case_three
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    (hFunNe : K_FunNonempty)
    (h1 : ¬ P17_12_1 r q L) (h2 : ¬ P17_12_2 q L) :
    (Delta17_12 D (fundPred q) r q L).Nonempty := by
  classical
  obtain ⟨hr, hr2, t, n, f, hadm, hq, hmodel⟩ := hC.lie
  have hXq : CFSG.Open.IsQuasisimple (Bar2 L) := hC.memL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hC.memL
  have hmodel' : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t n r f :=
    LieModel.of_mulEquiv e1 hmodel
  have hnotL2 : ¬ IsL2Over17 (Bar2 L ⧸ Subgroup.center (Bar2 L)) q := by
    intro h
    exact h1 (Or.inl (isL2Over17_of_mulEquiv e1 h))
  have hnotL3 : ¬ IsL3EpsOdd17 (Bar2 L ⧸ Subgroup.center (Bar2 L)) r := by
    intro h
    rcases h with h | h
    · exact h1 (Or.inr (Or.inl (LieModel.of_mulEquiv e1.symm h)))
    · exact h1 (Or.inr (Or.inr (LieModel.of_mulEquiv e1.symm h)))
  obtain ⟨P, hPcoe⟩ := exists_sylow_syl2Bar D L hC.memL.1
  obtain ⟨Kb, hKb⟩ := hFunNe (Bar2 L) r q hr hr2 ⟨t, n, f, hadm, hq, hmodel'⟩ hXq hodd
    hnotL2 hnotL3 h2 h9 P
  refine ⟨D.T ⊔ barPreimage L Kb, ?_⟩
  refine mem_delta_third D V₀ V L r q hC h1 h2 (barPreimage L Kb) (uc22p21c_barPreimage_le L Kb)
    (pCoreOf_le_barPreimage L Kb) ?_
  change barImage L (barPreimage L Kb) ∈ _
  rw [barImage_barPreimage]
  exact hPcoe ▸ hKb

theorem delta17_12_nonempty
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    (hRee : K_ReeSylowGeneration) (hFunNe : K_FunNonempty) :
    (Delta17_12 D (fundPred q) r q L).Nonempty := by
  by_cases h1 : P17_12_1 r q L
  · exact delta17_12_nonempty_case_one D r q L h1
  · by_cases h2 : P17_12_2 q L
    · exact delta17_12_nonempty_case_two D V₀ V L r q hC h9 hRee h1 h2
    · exact delta17_12_nonempty_case_three D V₀ V L r q hC h9 hFunNe h1 h2

theorem isQuasisimple_of_isFundamentalOver {X : Type} [Group X] {q : ℕ} {Kb : Subgroup X}
    (h : IsFundamentalOver q Kb) (hq : 3 < q) : CFSG.Open.IsQuasisimple ↥Kb := by
  have hne : Kb ≠ ⊥ := h.ne_bot
  obtain ⟨t, n, p, e, hp, hp2, hq_eq, hfund, hadm, ψ, hsurj, hker, R, hR, hKb⟩ := h
  rw [hKb] at hne ⊢
  have h4 : 4 ≤ p ^ e := by rw [← hq_eq]; omega
  have : Fact p.Prime := ⟨hp⟩
  have hRq : CFSG.Open.IsQuasisimple ↥R :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.fundQuasisimple_core hp2 hfund hadm h4 R hR
  have hRn : CFSG.IsQuasisimple ↥R :=
    CFSG.ClassicalInvolution.ModelFacts.native_isQuasisimple hRq
  have hnot : ¬ R ≤ ψ.ker := by
    intro hle
    exact hne ((Subgroup.map_eq_bot_iff R).mpr hle)
  have himg : CFSG.IsQuasisimple (R.map ψ) := CFSG.LocalCores.isQuasisimple_map hRn ψ hnot
  exact ⟨Group.isPerfect_def.mp himg.1, himg.2.1⟩

theorem isQuasisimple_bar2_of_isL2Over17
    {H : Subgroup G} {q : ℕ} (h : IsL2Over17 (Bar2 H) q) :
    CFSG.Open.IsQuasisimple (Bar2 H) := by
  obtain ⟨r, f, -, -, -, -, hm⟩ := h
  have hs : IsSimpleGroup (Bar2 H) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hm
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := Bar2 H)
    (CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hm)).1
  exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

theorem not_inFSq_zero_of_delta
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    {H : Subgroup G} (hH : H ∈ Delta17_12 D (fundPred q) r q L) :
    ¬ InFSq 0 H := by
  classical
  by_cases h1 : P17_12_1 r q L
  · rw [Delta17_12, dif_pos h1] at hH
    obtain ⟨x, hxM, rfl⟩ := hH
    refine not_inFSq_zero_of_isQuasisimple_bar2 le_sup_right ?_
    have e : Bar2 L ≃* Bar2 (L.map (MulAut.conj x).toMonoidHom) :=
      UC6S846.bar2Equiv (Subgroup.equivMapOfInjective L (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hC.memL.2.2
  · by_cases h2 : P17_12_2 q L
    · rw [Delta17_12, dif_neg h1, dif_pos h2] at hH
      obtain ⟨X, hXL, hperm, hL2, rfl⟩ := hH
      exact not_inFSq_zero_of_isQuasisimple_bar2 le_sup_right
        (isQuasisimple_bar2_of_isL2Over17 hL2)
    · rw [Delta17_12, dif_neg h1, dif_neg h2] at hH
      obtain ⟨x, hxM, X, hXLx, hpcle, rfl, hKb⟩ := hH
      set Lx : Subgroup G := L.map (MulAut.conj x).toMonoidHom with hLx
      set mk : ↥Lx →* Bar2 Lx := QuotientGroup.mk' (CFSG.pCore 2 ↥Lx) with hmk
      set Kb : Subgroup (Bar2 Lx) := (X.subgroupOf Lx).map mk with hKbdef
      have hfund : IsFundamentalOver q Kb := hKb.1
      have hq : 3 < q := h9
      have hKbq : CFSG.Open.IsQuasisimple (Bar2 Kb) := by
        have hq' := CFSG.Quasithin.H13.NQTerm.isQuasisimple_quotient_pCore_two
          (CFSG.ClassicalInvolution.ModelFacts.native_isQuasisimple
            (isQuasisimple_of_isFundamentalOver hfund hq))
        exact ⟨Group.isPerfect_def.mp hq'.1, hq'.2.1⟩
      have hXeq : X.subgroupOf Lx = Kb.comap mk := by
        refine le_antisymm ?_ ?_
        · intro y hy
          rw [Subgroup.mem_comap]
          exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
        · intro y hy
          rw [Subgroup.mem_comap] at hy
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
          have hker : y * z⁻¹ ∈ CFSG.pCore 2 ↥Lx := by
            have h1 : mk (y * z⁻¹) = 1 := by
              rw [map_mul, map_inv, hzy, mul_inv_cancel]
            have h2 : y * z⁻¹ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)).ker :=
              MonoidHom.mem_ker.mpr h1
            rwa [QuotientGroup.ker_mk'] at h2
          have hmemG : (((y * z⁻¹ : ↥Lx) : G)) ∈ X :=
            hpcle (Subgroup.mem_map.mpr ⟨y * z⁻¹, hker, rfl⟩)
          have hmem : y * z⁻¹ ∈ X.subgroupOf Lx := hmemG
          have hy' : y = (y * z⁻¹) * z := by group
          rw [hy']
          exact (X.subgroupOf Lx).mul_mem hmem hz
      have e1 : Bar2 X ≃* Bar2 (X.subgroupOf Lx) :=
        UC6S846.bar2Equiv (Subgroup.subgroupOfEquivOfLe hXLx).symm
      have e2 : Nonempty (Bar2 (X.subgroupOf Lx) ≃* Bar2 Kb) := by
        rw [hXeq]
        let g : ↥(Kb.comap mk) →* ↥Kb :=
          { toFun := fun y => ⟨mk y, y.2⟩
            map_one' := by ext; simp
            map_mul' := by intro a b; ext; simp }
        have hgs : Function.Surjective g := by
          intro y
          obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
          exact ⟨⟨x, Subgroup.mem_comap.mpr (hxy.symm ▸ y.2)⟩, Subtype.ext hxy⟩
        have hgk : IsPGroup 2 g.ker := by
          let κ : ↥g.ker →* ↥(CFSG.pCore 2 ↥Lx) :=
            { toFun := fun y =>
                ⟨((y : ↥(Kb.comap mk)) : ↥Lx), by
                  have hy : mk ((y : ↥(Kb.comap mk)) : ↥Lx) = 1 :=
                    congrArg Subtype.val y.2
                  exact (QuotientGroup.eq_one_iff _).mp hy⟩
              map_one' := by ext; simp
              map_mul' := by intro a b; ext; simp }
          have hκ : Function.Injective κ := by
            intro a b hab
            refine Subtype.ext (Subtype.ext ?_)
            exact congrArg (fun z : ↥(CFSG.pCore 2 ↥Lx) => (z : ↥Lx)) hab
          exact IsPGroup.of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥Lx)) κ hκ
        exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker g hgs hgk
      obtain ⟨e2'⟩ := e2
      exact not_inFSq_zero_of_isQuasisimple_bar2 le_sup_right
        (CFSG.Open.IsQuasisimple.of_mulEquiv (e1.trans e2') hKbq)

theorem seventeen_thirteen (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    (hRee : K_ReeSylowGeneration) (hFunNe : K_FunNonempty)
    (h43c : W3Lem45_2Chief)
    (hdiag : Gap17_13_diagonal D V₀ V L r q hC) :
    R17_13At D (fundPred q) V₀ V L r q hC := by
  have hgap : Gap17_13_upperBounds D V₀ V L r q hC :=
    Gap17_13_upperBounds_of_diagonal h43c D V₀ V L r q hC hdiag
  exact R17_13At_of_index_bounds D V₀ V L r q hC
    (delta17_12_nonempty D V₀ V L r q hC h9 hRee hFunNe)
    (fun H hH => not_inFSq_zero_of_delta D V₀ V L r q hC h9 hH)
    hgap.1 hgap.2.1 hgap.2.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
