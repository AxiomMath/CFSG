module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Par

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem card_iSup_commSub {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {𝓗 I : Finset (Subgroup (MulAut W))}
    (hb : IsTransvectionBlocks J 𝓗) (hI : I ⊆ 𝓗) (hc : I.card = 1 ∨ I.card = 2) :
    Nat.card ↥(⨆ L ∈ I, commSub (⊤ : Subgroup W) L) = 4 ^ I.card := by
  classical
  rcases hc with h1 | h2
  · obtain ⟨L₁, hI1⟩ := Finset.card_eq_one.mp h1
    rw [hI1, Finset.iSup_singleton, hb.card_comm L₁ (hI (by rw [hI1]; simp)), Finset.card_singleton,
      pow_one]
  · obtain ⟨L₁, L₂, h12, hI2⟩ := Finset.card_eq_two.mp h2
    have s₁ : L₁ ∈ 𝓗 := hI (by rw [hI2]; simp)
    have s₂ : L₂ ∈ 𝓗 := hI (by rw [hI2]; simp)
    rw [hI2, Finset.iSup_insert, Finset.iSup_singleton, Finset.card_pair h12]
    have h1 := card_sup_mul_card_inf_of_commute (A := commSub (⊤ : Subgroup W) L₁)
      (B := commSub (⊤ : Subgroup W) L₂) fun a _ b _ => mul_comm a b
    rw [commSub_inf_eq_bot_of_ne hW hb s₁ s₂ h12, Subgroup.card_bot, mul_one,
      hb.card_comm L₁ s₁, hb.card_comm L₂ s₂] at h1
    rw [h1]
    norm_num

theorem card_eq_mul_of_compl {W : Type*} [CommGroup W] [Finite W] {X C : Subgroup W}
    (hsup : X ⊔ C = ⊤) (hinf : X ⊓ C = ⊥) : Nat.card W = Nat.card X * Nat.card C := by
  have h1 := card_sup_mul_card_inf_of_commute (A := X) (B := C) fun a _ b _ => mul_comm a b
  rw [hsup, hinf, Subgroup.card_bot, mul_one, Subgroup.card_top] at h1
  exact h1

theorem card_commutator_eq_pow {G : Type*} [Group G] [Finite G] {H T M Y W : Subgroup G}
    (hW : IsElemAbelian 2 W) (hmin : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (h3 : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H W)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G)) (hK : twoResidual H = Y)
    {𝓗 I : Finset (Subgroup (MulAut (IntMod W hW)))} (B : E2.Blocks hW H 𝓗 I) :
    (I.card = 1 ∨ I.card = 2) ∧ Odd (Nat.card (autI hW Y)) ∧
      Nat.card (⁅W, Y⁆ : Subgroup G) = 4 ^ I.card := by
  have hW' : ∀ w : IntMod W hW, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hYN : Y ≤ Subgroup.normalizer (W : Set G) := hK ▸ (twoResidual_le H).trans hred.2.1
  have hc := B.card_eq_one_or_two hmin hsolv h3 hred hJ
  have hp3 := B.isPGroup_autI_twoResidual hmin hsolv hred hJ
  rw [hK] at hp3
  have hodd : Odd (Nat.card (autI hW Y)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hp3.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have hfix := B.fixV_twoResidual hmin hsolv h3 hred hJ
  rw [hK] at hfix
  have hdec := B.hb.decomp hW' I B.sub
  rw [← B.eq, ← hfix] at hdec
  have e1 := card_eq_mul_of_compl hdec.1 hdec.2
  have e2 := card_eq_mul_of_compl (fixV_sup_commSub_eq_top hW' hodd)
    (fixV_inf_commSub_eq_bot hW' hodd)
  have hpos : 0 < Nat.card (fixV (autI hW Y)) := Nat.card_pos
  have e3 : Nat.card (commSub (⊤ : Subgroup (IntMod W hW)) (autI hW Y)) = 4 ^ I.card := by
    rw [← card_iSup_commSub hW' B.hb B.sub hc]
    exact Nat.eq_of_mul_eq_mul_left hpos (e2.symm.trans e1)
  refine ⟨hc, hodd, ?_⟩
  rw [commutator_eq_map_commSub hW hYN, card_map_valHom, e3]

namespace Setup

variable (h : Setup T M) {Y : Subgroup G}
include h

theorem omegaOneCenter_le_omega (hYM : Y ≤ M) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) := by
  have hF := h.charTwo_sup hYM
  have hOT : pCoreOf 2 (Y ⊔ T) ≤ T := pCoreOf_le_of_isSylowTwoOf h.isSylowTwoOf_sup
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  have hzC' : z ∈ Subgroup.centralizer (pCoreOf 2 (Y ⊔ T) : Set G) :=
    Subgroup.centralizer_le hOT hzC
  exact Subgroup.subset_closure ⟨⟨hF ⟨Subgroup.mem_sup_right hzT, hzC'⟩, hzC'⟩, hz2⟩

omit [Finite G] h in
theorem le_normalizer_omega :
    Y ⊔ T ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) : Set G) :=
  (le_normalizer_pCoreOf 2 (Y ⊔ T)).trans
    (normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf X)
      (fun φ X => omegaOneCenterOf_map_mulEquiv φ X) _)

theorem isTwoReducedIn_omega (hYM : Y ≤ M) :
    IsTwoReducedIn (Y ⊔ T) (omegaOneCenterOf (pCoreOf 2 (Y ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) with hW
  have hWO : W ≤ centerOf (pCoreOf 2 (Y ⊔ T)) := omegaOneCenterOf_le_centerOf _
  refine ⟨hWO.trans (inf_le_left.trans (pCoreOf_le 2 _)), le_normalizer_omega,
    isElemAbelian_omegaOneCenterOf _, fun D hDH hHD hD => ?_⟩
  have hD2 : IsPGroup 2 D := by
    intro d
    obtain ⟨k, hk⟩ := hD d d.2
    have hkT : (d : G) ^ 2 ^ k ∈ T := by
      rw [← h.cz]
      exact Subgroup.centralizer_le (h.omegaOneCenter_le_omega hYM) hk
    obtain ⟨j, hj⟩ := h.isPGroup ⟨_, hkT⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((d : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    exact hj'
  have hDO : D ≤ pCoreOf 2 (Y ⊔ T) := le_pCoreOf_of_le_normalizer 2 hDH hHD hD2
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hWO hw).2 d (hDO hd)).symm

theorem twoReducedJoin_eq (hYM : Y ≤ M) :
    twoReducedJoin (Y ⊔ T) = omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) :=
  le_antisymm (iSup₂_le fun _ hV' => le_omegaOneCenterOf_of_isTwoReducedIn hV')
    (le_iSup₂_of_le (f := fun (V' : Subgroup G) (_ : IsTwoReducedIn (Y ⊔ T) V') => V') _
      (h.isTwoReducedIn_omega hYM) le_rfl)

theorem commutator_le_omega (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ⁅VZ T M, Y⁆ ≤ omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) :=
  le_omegaOneCenterOf_of_isTwoReducedIn (h.isTwoReducedIn_commutator hY hYM)

theorem not_thompsonJ_le_omega (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) : Set G) :=
  fun hle => h.not_thompsonJ_le hY hYM
    (hle.trans (Subgroup.centralizer_le (h.commutator_le_omega hY hYM)))

theorem commutator_commutator_eq (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ⁅(⁅VZ T M, Y⁆ : Subgroup G), Y⁆ = ⁅VZ T M, Y⁆ := by
  have hW : ∀ w : IntMod (VZ T M) h.elem, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans h.le_normalizer
  have e := commutator_map_valHom h.elem hYN (commSub ⊤ (autI h.elem Y))
  rw [commSub_commSub_eq hW (h.odd_card_autI hY hYM), ← h.commutator_eq hYM] at e
  rw [h.commutator_eq hYM] at e ⊢
  exact e

theorem commutator_omega_eq (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ⁅omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)), Y⁆ = ⁅VZ T M, Y⁆ := by
  classical
  set Wz := omegaOneCenterOf (pCoreOf 2 (Y ⊔ T)) with hWz
  have hZel : IsElemAbelian 2 Wz := isElemAbelian_omegaOneCenterOf _
  have hred := h.isTwoReducedIn_omega hYM
  have hJ := h.not_thompsonJ_le_omega hY hYM
  have hmin := h.minParabolic hY hYM
  have hsolv := h.solv_sup hYM
  have h3 : CFSG.Open.pRank 3 (Y ⊔ T) ≤ 2 := h.rank_sup hYM 3 Nat.prime_three (by norm_num)
  have hK : twoResidual (Y ⊔ T) = Y := h.twoResidual_eq hY
  have hW' : ∀ w : IntMod Wz hZel, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hYN : Y ≤ Subgroup.normalizer (Wz : Set G) := le_sup_left.trans hred.2.1
  obtain ⟨𝓗', I', B'⟩ := E2.exists_blocks hZel hred hsolv hmin.isSylow hJ
  obtain ⟨hc, -, hcardWY⟩ := card_commutator_eq_pow hZel hmin hsolv h3 hred hJ hK B'
  obtain ⟨s, hs, hidx, -, hU, -⟩ := h.three hY hYM
  have hO2 : pCoreOf 2 Y ≤ Y ⊓ Subgroup.centralizer (Wz : Set G) := by
    refine le_inf (pCoreOf_le 2 Y) ?_
    refine le_trans ?_ (MinParabolic.pCoreOf_le_centralizer hred)
    rw [h.pCoreOf_eq hY hYM]
    exact (inf_le_inf_right _ hYM).trans
      (h.cent ▸ h.pCoreOf_le_pCoreOf le_sup_right (h.sup_le_M hYM))
  have hcardY : Nat.card (autI hZel Y) ≤ 3 ^ s := by
    rw [card_autI_eq hZel hYN, ← hidx]
    refine Subgroup.relIndex_le_of_le_left hO2 fun h0 => ?_
    exact (Nat.card_pos (α := Y)).ne'
      (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_card (pCoreOf 2 Y) Y))
  have hIs : I'.card ≤ s := by
    rcases hc with h1 | h2
    · rw [h1]
      rcases hs with rfl | rfl <;> norm_num
    · rcases hs with rfl | rfl
      · exfalso
        obtain ⟨L₁, L₂, h12, hI2⟩ := Finset.card_eq_two.mp h2
        have hL₁ : L₁ ∈ I' := by rw [hI2]; simp
        have hL₂ : L₂ ∈ I' := by rw [hI2]; simp
        obtain ⟨f₁, hf₁, hf₁K, h3₁⟩ := B'.exists_orderOf_eq_three hL₁
        obtain ⟨f₂, hf₂, hf₂K, h3₂⟩ := B'.exists_orderOf_eq_three hL₂
        rw [hK] at hf₁K hf₂K
        have hle : Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ≤ autI hZel Y :=
          sup_le (Subgroup.zpowers_le.mpr hf₁K) (Subgroup.zpowers_le.mpr hf₂K)
        have h9 := card_sup_zpowers B'.hb (B'.sub hL₁) (B'.sub hL₂) h12 hf₁ hf₂ h3₁ h3₂
        have := Subgroup.card_le_of_le hle
        omega
      · rw [h2]
  have hle : ⁅VZ T M, Y⁆ ≤ ⁅Wz, Y⁆ := by
    rw [← h.commutator_commutator_eq hY hYM]
    exact Subgroup.commutator_mono (h.commutator_le_omega hY hYM) le_rfl
  have hcard_le := Subgroup.card_le_of_le hle
  rw [hU, hcardWY] at hcard_le
  have hsI : s ≤ I'.card := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard_le
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hU, hcardWY, le_antisymm hIs hsI]

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
