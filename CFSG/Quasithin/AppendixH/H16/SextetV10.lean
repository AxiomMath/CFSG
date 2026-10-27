module

public import CFSG.Quasithin.AppendixH.H16.SextetAction

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Open CFSG.Quasithin.H.Coc

@[expose] def V10 : Subgroup W11 := maskSub 11 v10Basis

theorem toW_mem_V10_iff {m : ℕ} (hm : m < 2 ^ 11) :
    toW 11 m ∈ V10 ↔ popPar 11 (m &&& 1192) = false := by
  rw [V10, mem_maskSub]
  constructor
  · rintro ⟨m', hm', he⟩
    have hmm : m' = m := toW_inj (combos_lt v10Basis_lt m' hm') hm he
    subst m'
    exact v10_par_of_mem m hm'
  · intro h
    exact ⟨m, mem_combos_of_reduceBy_echelon v10Basis m (v10_red_of_par m hm h), rfl⟩

theorem mem_V10_iff (v : W11) :
    v ∈ V10 ↔ ∃ m < 2 ^ 11, popPar 11 (m &&& 1192) = false ∧ toW 11 m = v := by
  constructor
  · intro hv
    obtain ⟨m, hm, hmv⟩ := toW_surj 11 v
    exact ⟨m, hm, (toW_mem_V10_iff hm).1 (hmv.symm ▸ hv), hmv⟩
  · rintro ⟨m, hm, h, rfl⟩
    exact (toW_mem_V10_iff hm).2 h

theorem US_le_V10 : US ≤ V10 := by
  rintro u ⟨m, hm, rfl⟩
  rw [toW_mem_V10_iff (combos_lt uSBasis_lt m hm)]
  exact us_le_v10 m ((uSMasks_combos m (combos_lt uSBasis_lt m hm)).1 hm)

theorem card_V10 : Nat.card ↥V10 = 1024 := by
  rw [V10, card_maskSub v10Basis_lt v10_nodup]
  decide

theorem US_lt_V10 : US < V10 := by
  refine lt_of_le_of_ne US_le_V10 ?_
  intro h
  have := card_US
  rw [h, card_V10] at this
  omega

theorem V10_lt_top : V10 < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have h8 : toW 11 8 ∈ V10 := by rw [h]; exact Subgroup.mem_top _
  have hpar := (toW_mem_V10_iff (by norm_num)).1 h8
  rw [par_eight] at hpar
  exact Bool.false_ne_true hpar.symm

theorem rkIdx_V10 : rkIdx V10 = 1 := by
  have hW : Nat.card W11 = 2048 := by
    rw [Nat.card_eq_fintype_card, card_Wn]
    decide
  have hmul := V10.card_mul_index
  rw [card_V10, hW] at hmul
  have hidx : V10.index = 2 := by omega
  rw [rkIdx, hidx]
  exact padicValNat.self (by norm_num)

theorem rk_US : rk ↥US = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rk, card_US, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]

theorem fixV_imgCd_sxKS : fixV (imgCd sxKS) = US := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
    refine (toW_mem_US_iff hm).2 (fix_ks6 m hm fun i hi => ?_)
    have hmem : rhoCd (ks6_autPerm i) ∈ imgCd sxKS :=
      rhoCd_mem_imgCd (ks6_autPerm i) (ks6_mem_KS ⟨i, hi⟩)
    have hfix : rhoCd (ks6_autPerm i) (toW 11 m) = toW 11 m := (mem_fixV.1 hv) _ hmem
    have hba : rhoCd (ks6_autPerm i) (toW 11 m) = toW 11 (actM (ksC6 i) m) := actsBy_ks6 hi m
    exact toW_inj (actM_lt (ksC6_lt i hi) m) hm (hba.symm.trans hfix)
  · intro u hu
    exact mem_fixV.2 fun φ hφ => (mem_centSub.1 (imgCd_KS_le hφ).2) u hu

theorem popPar_xor (k a b : ℕ) : popPar k (a ^^^ b) = (popPar k a != popPar k b) := by
  induction k generalizing a b with
  | zero => simp [popPar]
  | succ k ih =>
    rw [popPar, popPar, popPar, Nat.xor_div_two, ih (a / 2) (b / 2)]
    have hpar : ((a ^^^ b) % 2 == 1) = ((a % 2 == 1) != (b % 2 == 1)) := by
      rw [Nat.xor_mod_two_eq, Nat.add_mod]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        rw [ha, hb] <;> decide
    rw [hpar, Bool.bne_eq_xor]
    generalize h1 : (a % 2 == 1) = p
    generalize h2 : (b % 2 == 1) = q
    generalize h3 : popPar k (a / 2) = r
    generalize h4 : popPar k (b / 2) = s
    cases p <;> cases q <;> cases r <;> cases s <;> rfl

private def commInV10 : Subgroup (MulAut W11) where
  carrier := {φ | ∀ v : W11, φ v * v⁻¹ ∈ V10}
  one_mem' := by
    intro v
    have hv : (1 : MulAut W11) v = v := rfl
    have h1 : v * v⁻¹ = 1 := mul_inv_cancel v
    rw [hv, h1]
    exact V10.one_mem
  mul_mem' := by
    intro a b ha hb v
    have h1 : a (b v) * (b v)⁻¹ ∈ V10 := ha (b v)
    have h2 : b v * v⁻¹ ∈ V10 := hb v
    have hab : (a * b) v = a (b v) := rfl
    have hkey : a (b v) * v⁻¹ = a (b v) * (b v)⁻¹ * (b v * v⁻¹) := by
      have hc : (b v)⁻¹ * (b v * v⁻¹) = v⁻¹ := inv_mul_cancel_left (b v) v⁻¹
      rw [mul_assoc, hc]
    rw [hab, hkey]
    exact V10.mul_mem h1 h2
  inv_mem' := by
    intro a ha v
    have h1 : a (a⁻¹ v) * (a⁻¹ v)⁻¹ ∈ V10 := ha (a⁻¹ v)
    have hval : a (a⁻¹ v) = v := by simp
    have hrev : (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ = ((a⁻¹ v)⁻¹)⁻¹ * (a (a⁻¹ v))⁻¹ :=
      mul_inv_rev _ _
    have hinv : ((a⁻¹ v)⁻¹)⁻¹ = a⁻¹ v := inv_inv _
    have hainv : (a (a⁻¹ v))⁻¹ = v⁻¹ := by rw [hval]
    have hkey : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
      rw [hrev, hinv, hainv]
    rw [hkey]
    exact V10.inv_mem h1

theorem imgCd_sxGen_comm_mem_V10 : ∀ φ ∈ imgCd sxGen, ∀ v : W11, φ v * v⁻¹ ∈ V10 := by
  have hle : imgCd sxGen ≤ commInV10 := by
    refine imgCd_closure_le (S := ({sxG1, sxG2, sxT} : Set (Equiv.Perm (Fin 24)))) (by
      rintro _ (rfl | rfl | rfl)
      · exact sxG1_mem
      · exact sxG2_mem
      · exact sxT_mem) ?_
    rintro _ (rfl | rfl | rfl)
    · intro v
      obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
      change rhoCd sxG1_mem (toW 11 m) * (toW 11 m)⁻¹ ∈ V10
      have hgoal : rhoCd sxG1_mem (toW 11 m) * (toW 11 m)⁻¹ =
          toW 11 (actM sxG1C m ^^^ m) := by
        have hact : rhoCd sxG1_mem (toW 11 m) = toW 11 (actM sxG1C m) := actsBy_sxG1 m
        have hinv : (toW 11 m)⁻¹ = toW 11 m := toW_inv_self 11 m
        have hxor : toW 11 (actM sxG1C m) * toW 11 m = toW 11 (actM sxG1C m ^^^ m) :=
          (toW_xor 11 (actM sxG1C m) m).symm
        rw [hact, hinv, hxor]
      rw [hgoal, toW_mem_V10_iff (Nat.xor_lt_two_pow (actM_lt (fun c hc =>
        sxCols_lt c (List.mem_append_left _ hc)) m) hm)]
      simp only [Nat.and_xor_distrib_right, popPar_xor, (v10_pres m hm).1, Bool.bne_eq_xor,
        Bool.xor_self]
    · intro v
      obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
      change rhoCd sxG2_mem (toW 11 m) * (toW 11 m)⁻¹ ∈ V10
      have hgoal : rhoCd sxG2_mem (toW 11 m) * (toW 11 m)⁻¹ =
          toW 11 (actM sxG2C m ^^^ m) := by
        have hact : rhoCd sxG2_mem (toW 11 m) = toW 11 (actM sxG2C m) := actsBy_sxG2 m
        have hinv : (toW 11 m)⁻¹ = toW 11 m := toW_inv_self 11 m
        have hxor : toW 11 (actM sxG2C m) * toW 11 m = toW 11 (actM sxG2C m ^^^ m) :=
          (toW_xor 11 (actM sxG2C m) m).symm
        rw [hact, hinv, hxor]
      rw [hgoal, toW_mem_V10_iff (Nat.xor_lt_two_pow (actM_lt (fun c hc =>
        sxCols_lt c (List.mem_append_right _ hc)) m) hm)]
      simp only [Nat.and_xor_distrib_right, popPar_xor, (v10_pres m hm).2.1, Bool.bne_eq_xor,
        Bool.xor_self]
    · intro v
      obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
      change rhoCd sxT_mem (toW 11 m) * (toW 11 m)⁻¹ ∈ V10
      have hgoal : rhoCd sxT_mem (toW 11 m) * (toW 11 m)⁻¹ = toW 11 (actM sxTC m ^^^ m) := by
        have hact : rhoCd sxT_mem (toW 11 m) = toW 11 (actM sxTC m) := actsBy_sxT m
        have hinv : (toW 11 m)⁻¹ = toW 11 m := toW_inv_self 11 m
        have hxor : toW 11 (actM sxTC m) * toW 11 m = toW 11 (actM sxTC m ^^^ m) :=
          (toW_xor 11 (actM sxTC m) m).symm
        rw [hact, hinv, hxor]
      rw [hgoal, toW_mem_V10_iff (Nat.xor_lt_two_pow (actM_lt sxTC_lt m) hm)]
      simp only [Nat.and_xor_distrib_right, popPar_xor, (v10_pres m hm).2.2, Bool.bne_eq_xor,
        Bool.xor_self]
  intro φ hφ v
  exact hle hφ v

theorem isActsInv_V10 : IsActsInv (actsOnModule (imgCd sxGen)) V10 := by
  rintro f ⟨y, hy, rfl⟩ v hv
  change y v ∈ V10
  have h1 : y v * v⁻¹ ∈ V10 := imgCd_sxGen_comm_mem_V10 y hy v
  have e : (y v * v⁻¹) * v = y v := by
    have hc : v⁻¹ * v = 1 := inv_mul_cancel v
    rw [mul_assoc, hc, mul_one]
  rw [← e]
  exact V10.mul_mem h1 hv

theorem isActsInv_US : IsActsInv (actsOnModule (imgCd sxGen)) US := by
  rintro f ⟨y, hy, rfl⟩ u hu
  exact (mem_stabSub.1 (imgCd_sxGen_le_stabSub hy) u).2 hu

private theorem toW_comm_mem_commV (c : List ℕ) (m : ℕ)
    (h : ∃ g ∈ imgCd sxP0, ActsBy g c) :
    toW 11 (actM c m ^^^ m) ∈ CFSG.Quasithin.commV (imgCd sxP0) := by
  obtain ⟨g, hg, hgact⟩ := h
  have hgoal : toW 11 (actM c m ^^^ m) = g (toW 11 m) * (toW 11 m)⁻¹ := by
    have h1 : g (toW 11 m) = toW 11 (actM c m) := hgact m
    have h2 : (toW 11 m)⁻¹ = toW 11 m := toW_inv_self 11 m
    have h3 : toW 11 (actM c m) * toW 11 m = toW 11 (actM c m ^^^ m) :=
      (toW_xor 11 (actM c m) m).symm
    rw [h1, h2, h3]
  rw [hgoal]
  exact Subgroup.subset_closure ⟨g, hg, toW 11 m, rfl⟩

theorem commV_imgCd_sxP0 : CFSG.Quasithin.commV (imgCd sxP0) = V10 := by
  have hmono : imgCd sxP0 ≤ imgCd sxGen :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono AutPerm sxP0_le_gen)
  have hgen1 : ∀ m, toW 11 (actM sxG1C m ^^^ m) ∈ CFSG.Quasithin.commV (imgCd sxP0) :=
    fun m => toW_comm_mem_commV sxG1C m
      ⟨rhoCd sxG1_mem, rhoCd_mem_imgCd sxG1_mem sxG1_mem_P0, actsBy_sxG1⟩
  have hgen2 : ∀ m, toW 11 (actM sxG2C m ^^^ m) ∈ CFSG.Quasithin.commV (imgCd sxP0) :=
    fun m => toW_comm_mem_commV sxG2C m
      ⟨rhoCd sxG2_mem, rhoCd_mem_imgCd sxG2_mem sxG2_mem_P0, actsBy_sxG2⟩
  refine le_antisymm ?_ ?_
  · change Subgroup.closure {w : W11 | ∃ x ∈ imgCd sxP0, ∃ v : W11, x v * v⁻¹ = w} ≤ V10
    rw [Subgroup.closure_le]
    rintro w ⟨φ, hφ, v, rfl⟩
    exact imgCd_sxGen_comm_mem_V10 φ (hmono hφ) v
  · intro v hv
    obtain ⟨m, hm, rfl⟩ := hv
    have hmem : ∀ a ∈ v10Basis, toW 11 a ∈ CFSG.Quasithin.commV (imgCd sxP0) := by
      intro a ha
      rw [v10Basis_comm] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hgen1 1
      · exact hgen1 2
      · exact hgen1 4
      · exact hgen1 8
      · exact hgen1 16
      · exact hgen1 32
      · exact hgen1 128
      · exact hgen1 256
      · exact hgen2 1
      · exact hgen2 16
    exact mem_of_combos (fun x => toW 11 x ∈ CFSG.Quasithin.commV (imgCd sxP0))
      (by rw [toW_zero]; exact (CFSG.Quasithin.commV (imgCd sxP0)).one_mem)
      (fun a b ha hb => by rw [toW_xor]; exact (CFSG.Quasithin.commV (imgCd sxP0)).mul_mem ha hb)
      v10Basis hmem m hm

theorem isChiefFactorUnder_bot_US :
    IsChiefFactorUnder (actsOnModule (imgCd sxGen)) ⊥ US := by
  have hbot : maskSub 11 ([] : List ℕ) = (⊥ : Subgroup W11) := by
    ext v
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm0 : m = 0 := by simpa only [combos, List.mem_singleton] using hm
      rw [hm0, toW_zero]
      exact Subgroup.mem_bot.2 rfl
    · intro hv
      rw [Subgroup.mem_bot] at hv
      exact ⟨0, zero_mem_combos [], by rw [hv, toW_zero]⟩
  rw [← hbot]
  refine isChiefFactorUnder_maskSub (n := 11) (G := imgCd sxGen)
    [rhoCd sxG1_mem, rhoCd sxG2_mem] [sxG1C, sxG2C] ?_ ?_ [] uSBasis words2 ?_ chief_US ?_
    ?_ ?_
  · intro i hi
    rcases i with _ | _ | i
    · exact rhoCd_mem_imgCd sxG1_mem (Subgroup.subset_closure (by simp))
    · exact rhoCd_mem_imgCd sxG2_mem (Subgroup.subset_closure (by simp))
    · simp at hi
  · intro i hi
    rcases i with _ | _ | i
    · exact actsBy_sxG1
    · exact actsBy_sxG2
    · simp at hi
  · decide
  · rw [hbot]
    exact bot_lt_iff_ne_bot.2 (by
      intro h
      have hc : Nat.card ↥(maskSub 11 uSBasis) = 16 := card_US
      have hc1 : Nat.card ↥(maskSub 11 uSBasis) = Nat.card ↥(⊥ : Subgroup W11) :=
        congrArg (fun K : Subgroup W11 => Nat.card ↥K) h
      rw [Subgroup.card_bot] at hc1
      omega)
  · rw [hbot]
    rintro f ⟨y, hy, rfl⟩ v hv
    change y v ∈ (⊥ : Subgroup W11)
    rw [Subgroup.mem_bot] at hv
    rw [hv]
    exact Subgroup.mem_bot.2 (MulEquiv.map_one y)
  · exact isActsInv_US

theorem isChiefFactorUnder_US_V10 :
    IsChiefFactorUnder (actsOnModule (imgCd sxGen)) US V10 := by
  refine isChiefFactorUnder_maskSub (n := 11) (G := imgCd sxGen)
    [rhoCd sxG1_mem, rhoCd sxG2_mem] [sxG1C, sxG2C] ?_ ?_ uSBasis v10Basis words3 ?_
    chief_V10_US US_lt_V10 isActsInv_US isActsInv_V10
  · intro i hi
    rcases i with _ | _ | i
    · exact rhoCd_mem_imgCd sxG1_mem (Subgroup.subset_closure (by simp))
    · exact rhoCd_mem_imgCd sxG2_mem (Subgroup.subset_closure (by simp))
    · simp at hi
  · intro i hi
    rcases i with _ | _ | i
    · exact actsBy_sxG1
    · exact actsBy_sxG2
    · simp at hi
  · decide

theorem isChiefFactorUnder_V10_top :
    IsChiefFactorUnder (actsOnModule (imgCd sxGen)) V10 ⊤ := by
  have hW : Nat.card W11 = 2 ^ 11 := by
    rw [Nat.card_eq_fintype_card, card_Wn]
  refine ⟨V10_lt_top, isActsInv_V10, ?_, ?_⟩
  · intro f hf v hv
    exact Subgroup.mem_top _
  · intro W hVW hWtop hWi
    have h1 : 2 ^ 10 ∣ Nat.card ↥W := by
      have h := Subgroup.card_dvd_of_le hVW
      rwa [card_V10, show (1024 : ℕ) = 2 ^ 10 by norm_num] at h
    have h2 : Nat.card ↥W ∣ 2 ^ 11 := by
      have h := Subgroup.card_subgroup_dvd_card W
      rwa [hW] at h
    obtain ⟨k, hk11, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hk10 : 10 ≤ k := by
      rw [hk] at h1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
    rcases (show k = 10 ∨ k = 11 by omega) with rfl | rfl
    · left
      have hn : Nat.card ↥W = 1024 := by rw [hk]; norm_num
      exact (Subgroup.eq_of_le_of_card_ge hVW (by rw [hn, card_V10])).symm
    · right
      have hn : Nat.card ↥W = 2048 := by rw [hk]; norm_num
      exact Subgroup.eq_of_le_of_card_ge le_top
        (by rw [hn, Subgroup.card_top, hW]; norm_num)

end CFSG.ASVolI.H16
