module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem9
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem omega_le_ZS (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    quasithinOmegaOneCenter T ≤ ch6ZS T L V := by
  have hZV := h.omega_le_V h331 h432 h512 h614 h615
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  exact fun z hz => ⟨hZV hz, Subgroup.centralizer_le inf_le_left (hZC hz)⟩

theorem almostSpecialHyp_Gz (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    AlmostSpecialHyp (ch6ZS T L V) (quasithinOmegaOneCenter T) ⊥ T
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZ
  set H := Subgroup.centralizer (Z : Set G) with hH
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hV := h.toHyp611.isElemAbelian
  have hZSel : IsElemAbelian 2 (ch6ZS T L V) := B2F.isElemAbelian_mono inf_le_left hV
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  have hTH : T ≤ H := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
  have hTN : T ≤ Subgroup.normalizer (Z : Set G) :=
    hTH.trans (Subgroup.centralizer_le_normalizer _)
  have hZ1 : Z ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hZ2
    omega
  have hlOne : lOne (⊥ : Subgroup G) Z = ⊥ := by
    apply eq_bot_iff.mpr
    exact (oTwoUpper_le _).trans inf_le_left
  have hTsyl : IsSylowIn 2 T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hchar : CharTwo H := by
    obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
    refine CFSG.Quasithin.charTwo_of_inH h.qtke.2.1 P ⟨hP ▸ hTH, ?_⟩
    have hZO : Z ≤ pCoreOf 2 H := by
      refine le_pCoreOf_of_le_normalizer 2 (fun z hz => ?_) (fun x hx => ?_) ?_
      · exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
          B2F.isElemAbelian_comm hZSel (hZZS hy) (hZZS hz)
      · exact Subgroup.centralizer_le_normalizer _ hx
      · exact B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hZZS hZSel)
    exact fun h0 => hZ1 (eq_bot_iff.mpr (h0 ▸ hZO))
  have hlt : Z < ch6ZS T L V := by
    refine lt_of_le_of_ne hZZS fun he => ?_
    rw [he, hZS4] at hZ2
    omega
  refine
    { elemAbelian := hZSel
      ne_bot := hZ1
      le_V := hZZS
      oTwo_eq := ?_
      V_le_T := inf_le_left.trans h.toHyp611.le_T
      T_le_normV₁ := hTN
      T_le_normV := fun x hx => h.toHyp611Nat.T_le_normalizer_ZS hx
      T_le_normL := fun x _ => by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl; group
        · intro hy
          have := congrArg (fun w => x⁻¹ * w * x) hy
          simpa [mul_assoc] using this
      sylow_LT := by
        rw [bot_sup_eq]
        exact E6.isSylowIn_of_le hTsyl le_rfl le_top
      H_le := Subgroup.centralizer_le_normalizer _
      lOne_sup_le := by rw [hlOne, bot_sup_eq]; exact hTH
      sylow_H := E6.isSylowIn_of_le hTsyl hTH le_top
      charTwo := hchar
      irred := ?_ }
  · apply le_antisymm bot_le
    exact eq_bot_iff.mp (by
      apply eq_bot_iff.mpr
      exact (Subgroup.closure_le _).mpr fun x hx => hx.1)
  · rw [hlOne, bot_sup_eq]
    refine ⟨hlt, fun x hx => h.toHyp611Nat.T_le_normalizer_ZS hx, hTN, fun W hZW hWZS _ => ?_⟩
    by_cases hW : W = Z
    · exact Or.inl hW
    · right
      apply le_antisymm hWZS
      have hZW' : Z < W := lt_of_le_of_ne hZW (Ne.symm hW)
      have h1 : Nat.card Z < Nat.card W := Subgroup.card_lt_of_lt hZW'
      have h2 : Nat.card W ∣ Nat.card (ch6ZS T L V) := Subgroup.card_dvd_of_le hWZS
      rw [hZS4] at h2
      rw [hZ2] at h1
      have h3 : Nat.card W = 4 := by
        have : Nat.card W ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨h2, by norm_num⟩
        have hd : Nat.divisors 4 = {1, 2, 4} := by decide
        rw [hd] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        omega
      exact (Subgroup.eq_of_le_of_card_ge hWZS (by rw [h3, hZS4])).ge

theorem lemma_6_2_10_one_three_five (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    let Z := quasithinOmegaOneCenter T
    let H := Subgroup.centralizer (Z : Set G)
    let U := conjClosure (ch6ZS T L V) H
    (QuasithinUnique.CharTwo H ∧ U ≤ pCoreOf 2 H ∧ ⁅U, pCoreOf 2 H⁆ ≤ Z) ∧
    (centralizerMod Z H U ≤ Subgroup.normalizer (V : Set G) ∧
      Subgroup.normalizer (V : Set G) ≤ M ∧ V ⊓ centralizerMod Z H U ≤ pCoreOf 2 H) ∧
    IsO2Trivial H (centralizerMod Z H U) ∧
    ⁅V, U⁆ ≤ V ⊓ U := by
  intro Z H U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := h.almostSpecialHyp_Gz h331 h432 h512 h614 h615
  have hcc : U ≤ Subgroup.normalizer (Z : Set G) := hA.conjClosure_le_N
  have hV := h.toHyp611.isElemAbelian
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hUQ : U ≤ pCoreOf 2 H := by
    intro x hx
    have hQ := omegaOneCenterOf_le _ ((secImg_le_iff.1 hA.G22_one.2) ⟨x, hcc hx⟩ hx)
    exact (secMk_mem_secImg_iff hA.V₁_le_pCoreOf).1 hQ
  have hcommQ : ∀ x ∈ U, ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ * q⁻¹ ∈ Z := by
    intro x hx q hq
    have hqN : q ∈ Subgroup.normalizer (Z : Set G) := hA.H_le (pCoreOf_le 2 H hq)
    have hmemY := (secImg_le_iff.1 hA.G22_one.2) ⟨x, hcc hx⟩ hx
    have hqQ : tmk Z ⟨q, hqN⟩ ∈ tildeOf Z (pCoreOf 2 H) := secMk_mem_secImg hq
    have hxy : tmk Z ⟨x, hcc hx⟩ * tmk Z ⟨q, hqN⟩ = tmk Z ⟨q, hqN⟩ * tmk Z ⟨x, hcc hx⟩ :=
      (mem_centralizer_of_mem_omegaOneCenterOf hmemY hqQ).symm
    exact commutator_mem_of_secMk_commute hxy
  have hcomm : ⁅U, pCoreOf 2 H⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    rw [commutatorElement_def]
    exact hcommQ x hx q hq
  have hO2 : IsO2Trivial H (centralizerMod Z H U) :=
    isO2Trivial_of_isTwoReducedIn_tildeOf hA.H_le hcc hA.G22_four
  set C := centralizerMod Z H U with hC
  have hZSU : ch6ZS T L V ≤ U := le_conjClosure _ _
  have hconj : ∀ c ∈ C, ∀ y ∈ ch6ZS T L V, c * y * c⁻¹ ∈ ch6ZS T L V := by
    intro c hc y hy
    have h1 := (mem_centralizerMod.mp hc).2.2 y (hZSU hy)
    have h2 := (ch6ZS T L V).mul_mem (hZZS h1) hy
    simpa [mul_assoc] using h2
  have hCZS : C ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj c hc y, fun hy => ?_⟩
    have := hconj c⁻¹ (C.inv_mem hc) _ hy
    simpa [mul_assoc] using this
  have h9 := (stmt6_2_9 h331 h432 h512 h614 h615 G T M L V h).2.1
  have hCN : C ≤ Subgroup.normalizer (V : Set G) := by
    intro c hc
    have hcH : c ∈ H := centralizerMod_le_left _ _ _ hc
    have : c ∈ H ⊓ Subgroup.normalizer (V : Set G) := by rw [h9]; exact ⟨hcH, hCZS hc⟩
    exact this.2
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    mem_normalizer_centralizerMod_ch62 (hA.H_le hx) (Subgroup.le_normalizer hx)
      (le_normalizer_conjClosure _ H hx)
  have hVC : V ⊓ C ≤ pCoreOf 2 H := by
    have h1 : V ⊓ C ≤ pCoreOf 2 C := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx => ?_) ?_
      · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hCN hx, Subgroup.le_normalizer hx⟩
      · exact (B2F.isPGroup_of_isElemAbelian hV).to_le inf_le_left
    have h2 : pCoreOf 2 C ≤ pCoreOf 2 H :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans (centralizerMod_le_left _ _ _))
        (hHC.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
    exact h1.trans h2
  have hUH : U ≤ H := conjClosure_le fun x hx z hz => by
    have hzH : z ∈ H := Subgroup.mem_centralizer_iff.mpr fun y hy =>
      B2F.isElemAbelian_comm hV (hZZS hy).1 hz.1
    exact H.mul_mem (H.mul_mem hx hzH) (H.inv_mem hx)
  have hUC : U ≤ C := by
    intro u hu
    refine mem_centralizerMod.mpr ⟨hUH hu, hcc hu, fun y hy => ?_⟩
    exact hcommQ u hu y (hUQ hy)
  have hVH : V ≤ H := fun v hv => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    B2F.isElemAbelian_comm hV (hZZS hy).1 hv
  have h5 : ⁅V, U⁆ ≤ V ⊓ U := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp (hUC.trans hCN)) ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hVH.trans (le_normalizer_conjClosure _ H))
  exact ⟨⟨hA.charTwo, hUQ, hcomm⟩, ⟨hCN, h.normalizer_V_le h432, hVC⟩, hO2, h5⟩

end Hyp6Sec2

theorem stmt6_2_10_of (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h628 : Stmt6_2_8) : Stmt6_2_10 := by
  intro G _ _ T M L V h
  obtain ⟨h1, h2, h3, h5⟩ := h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615
  exact ⟨h1, h2, h3, fun hle => h628 G T M L V h ((le_inf le_rfl hle).trans h2.2.2), h5⟩


end CFSG.Quasithin.H13
