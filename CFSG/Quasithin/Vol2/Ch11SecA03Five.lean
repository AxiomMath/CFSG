module

public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11SecBBasic
public import CFSG.Quasithin.Vol2.Ch11SecCB51

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem stmt11_0_3_five (h51 : AsB51) (h56 : AsB56) (hKF : SecC.KindModuleFacts)
    (h322 : Ch10.TmpL6_3_2_2_two) (h3228 : Ch10.TmpL6_3_2_2_eight) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (hFC : SecB.FactCentralizerTwo) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n →
      ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
        H ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  intro hk H hH
  by_contra hle
  obtain ⟨b, hbHM, hbN⟩ : ∃ b ∈ H ⊓ Subgroup.normalizer (L : Set G),
      b ∉ Subgroup.normalizer (fsuV T I : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hle fun x hx => hcon x hx
  have hTI := (isTISetIn_fsuV h325 h).2 b hbHM.2 hbN
  have hCH : fsuV T I ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hTI]
    rintro v ⟨hvV, hvC⟩
    refine ⟨hvV, mem_conjSubgroup_iff.mpr ?_⟩
    rw [Subgroup.mem_centralizer_iff.mp hvC b hbHM.1, mul_inv_cancel_right]
    exact hvV
  have hJ : ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    obtain ⟨hVLT, hVred, hcent⟩ := h3228 G T L I h.fsu
    rw [fsuL0_eq h] at hVLT hVred hcent
    have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L (fsuV T I) :=
      { inM := ⟨isMaxTwoLocal_M h331 h, h.normal⟩
        nonempty := ⟨H, hH⟩
        perfect := (C2Nine.oTwoUpper_eq_of_perfect h.fsu.faithful.1.2.1.2.1).symm
        le_M := Subgroup.le_normalizer
        normal := le_rfl
        unique := isUniqueM_LT h331 h
        reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hVred⟩
        centralizer := hcent }
    rcases theorem318_three hC58 h317 h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow h318
      with h' | ⟨-, hZ, -⟩
    · exact h'.1
    exfalso
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (SecB.inf_centralizer_ne_bot h.fsu.sylow.1 (fsuV_le_T h) (T_le_normalizer_fsuV T I)
        (fsuV_ne_bot h))
    have hvZ : v ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨fsuV_le_T h hv.1, hv.2⟩, (isElemAbelian_fsuV h).2 v hv.1⟩
    have hvC : v ∈ fsuV T I ⊓ Subgroup.centralizer (H : Set G) := ⟨hv.1, (hZ H hH hvZ).2⟩
    rw [hCH, Subgroup.mem_bot] at hvC
    exact hv1 (Subtype.ext hvC)
  have hLJ := SecB.eq_commutator_thompsonJ hFC h1102 h hJ
  rcases SecC.fsuV_eq_VM_or h51 h56 h1102 hKF h322 h hLJ with hV | ⟨hk3, -, -⟩
  · apply hbN
    rw [hV]
    exact le_normalizer_conjClosure _ _ hbHM.2
  · rcases hk with hk | hk
    · exact kind_not_SL3_Sp4 (by have := h.one_lt; omega) hk3 hk
    · exact kind_not_SL3_G2 hKF.2.2.2 h.one_lt hk3 hk

end CFSG.Quasithin.Vol2.Ch11.SecA
