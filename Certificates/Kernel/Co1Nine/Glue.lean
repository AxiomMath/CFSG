
module

public import CFSG.Sporadic.Co1Patterson.IndexNineBase
public import Certificates.Kernel.Co1Nine.Chk
public import CFSG.Certificates.Kernel.Co1Nine.Sound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import Certificates.Kernel.Co1P.C21158
import CFSG.Certificates.Kernel.Misc.PermClosOrbit
import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import Certificates.Data.ExceptionalSL3

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo1Nine

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Misc.Clos CFSG.KC.Co1Nine
open CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.IndexNine
  CFSG.Sporadic.Co1Patterson.TwistNative CFSG.Sporadic.Co1Patterson.Native
  CFSG.Sporadic.Co1Schreier.Native
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem bray_conj {l : Nat} (hl : l < 8) {m : List Nat} (h : brayK m l = true) :
    conjOK (brayArr[l]!) m = true := by
  unfold brayK at h
  beta_reduce at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  have hc := (P.allN_iff _ _).1 h2
  unfold conjOK
  rw [CertificateChecks.KernelCo1P.brayArr_get hl, CertificateChecks.KernelCo1P.inv_BK hl,
    CFSG.KC.F2W.mul_unpackW, CFSG.KC.Co1B.one_eq, CFSG.KC.Co1B.beq_unpack]
  refine Bool.and_eq_true_iff.2 ⟨h1, List.all_eq_true.2 fun k hk => ?_⟩
  have h3 := P.orB_iff.1 (hc k (List.mem_range.1 hk))
  rw [CertificateChecks.KernelCo1P.yRow_W, CertificateChecks.KernelCo1P.yprodRow_W,
    CertificateChecks.KernelCo1P.iotaA_K]
  simp only [CFSG.KC.F2W.mul_unpackW, CFSG.KC.Co1B.beq_unpack, Bool.or_eq_true]
  exact h3

theorem mcols_len : MCols.length = 8 := rfl

theorem hasCols_M (i : Nat) (hi : i < 8) :
    HasCols ((typeSystemC.φ (brayC i (by rw [brayArr_size]; exact hi)) : L₀) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (MCols.getD i idCols) := by
  have h := (P.allN_iff _ _).1 bray_chk i hi
  have hlt : i < MCols.length := by rw [mcols_len]; exact hi
  rw [List.getD_eq_getElem _ _ hlt] at h ⊢
  exact hasCols_brayC i _ (bray_conj hi h)

theorem mcols_ok : ∀ m ∈ MCols ++ UCols, m.length = 8 ∧ ∀ x ∈ m, x < 256 := by
  have h := keys_chk.2.2.1
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

theorem getD_lt {m : List Nat} (h : ∀ x ∈ m, x < 256) (k : Nat) : m.getD k 0 < 256 := by
  by_cases hk : k < m.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem nthL_eq : ∀ (l : List Nat) (i : Nat), CFSG.KC.Misc.M22.nthL l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nthL_eq l i

theorem cols_bray (i : Fin 8) : co1Cols (co1BrayGens i) = MCols.getD i idCols := by
  have hlt : (i : Nat) < MCols.length := by rw [mcols_len]; exact i.isLt
  have hmem : MCols.getD i idCols ∈ MCols ++ UCols := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.mem_append_left UCols (List.getElem_mem hlt)
  have hm := mcols_ok _ hmem
  exact co1Cols_eq_of_hasCols hm.1 (getD_lt hm.2) (hasCols_M i i.isLt)

theorem cols_U (j : Fin 4) : co1Cols (co1UGens j) = co1WordC MCols (co1UWords.get j) :=
  co1Cols_eq_of_hasCols (co1WordC_length _ _) (co1WordC_getD_lt _ _)
    (hasCols_wordC MCols hasCols_M _ (co1UWords_idx_lt _ (List.get_mem _ _)))

theorem MG_eq {i : Nat} (hi : i < 8) :
    MG i = co1RowsKeyC (co1Cols (co1BrayGens ⟨i, hi⟩)) := by
  have hlt : i < MCols.length := by rw [mcols_len]; exact hi
  rw [cols_bray, MG, nthL_eq, keys_chk.1, List.getD_eq_getElem _ _ (by simpa using hlt),
    List.getElem_map, List.getD_eq_getElem _ _ hlt]

theorem UG_eq {j : Nat} (hj : j < 4) :
    UG j = co1RowsKeyC (co1Cols (co1UGens ⟨j, hj⟩)) := by
  rw [cols_U, UG, nthL_eq, keys_chk.2.1, keys_chk.2.2.2, List.map_map,
    List.getD_eq_getElem _ _ (by simpa [co1UWords_length] using hj), List.getElem_map]
  rfl

theorem unkey_cols (g : L₀) : unkey (co1RowsKeyC (co1Cols g)) = co1Cols g :=
  unkey_key (co1Cols_length g) (fun _ hx => co1Cols_mem_lt g hx)

theorem encU : ClosEnc (fun g : L₀ => co1RowsKeyC (co1Cols g)) mulC idK where
  enc_one := by
    rw [co1Cols_one]
    decide +kernel
  enc_mul a b := by
    change co1RowsKeyC (co1Cols (a * b)) = mulC _ _
    rw [mulC_eq, unkey_cols, unkey_cols, co1Cols_mul]
  inj := co1Key_injective

theorem finite_L₀ : Finite ↥L₀ := Nat.finite_of_card_ne_zero (by rw [card_L₀]; norm_num)

theorem ugens_closure : Subgroup.closure {g | g ∈ List.ofFn co1UGens} = co1Ubar := by
  rw [co1Ubar_eq_closure]
  congr 1
  ext g
  exact List.mem_ofFn' _ _

theorem card_Ubar : Nat.card co1Ubar = 4096 := by
  have := finite_L₀
  have hG : ∀ j < (List.ofFn co1UGens).length,
      UG j = co1RowsKeyC (co1Cols ((List.ofFn co1UGens).getD j 1)) := by
    intro j hj
    rw [List.length_ofFn] at hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    exact UG_eq hj
  have clos := clos_card_proved encU (List.ofFn co1UGens) hG (by norm_num)
    (by rw [List.length_ofFn]; exact (P.allN_iff _ _).1 u_tree) ((P.allN_iff _ _).1 u_sort)
  rw [← ugens_closure]
  exact (clos.2.2 (by rw [List.length_ofFn]; exact (P.allN_iff _ _).1 u_closed)).1

theorem sylow_Ubar : CFSG.QuasithinUnique.IsSylowTwoOf co1Ubar ⊤ := by
  have := finite_L₀
  refine ⟨le_top, IsPGroup.of_card (p := 2) (n := 12) ?_, ?_⟩
  · rw [card_Ubar]
    norm_num
  · rw [show (co1Ubar.subgroupOf ⊤).index = co1Ubar.index from Subgroup.relIndex_top_right _,
      Subgroup.index_eq_card_div, card_L₀, card_Ubar]
    norm_num

theorem stepF_smul (g : L₀) (f : Co1Flag) :
    stepF (co1RowsKeyC (co1Cols g)) (co1PairKey (co1FlagCode f)) =
      co1PairKey (co1FlagCode (g • f)) := by
  rw [co1FlagCode_smul, co1PairKey, co1PairKey, stepF_eq _ (co1FlagCode_lt f).2, unkey_cols]

theorem base_key : co1PairKey (co1FlagCode co1BaseFlagL) = baseF := by
  rw [co1FlagCode_base]
  rfl

theorem FE_zero : FE 0 = co1PairKey (co1FlagCode co1BaseFlagL) := by
  rw [base_key]
  exact Nat.eq_of_beq_eq_true ((P.allN_iff _ _).1 f_tree 0 (by norm_num))

theorem bgens_closure : Subgroup.closure {g | g ∈ List.ofFn co1BrayGens} = ⊤ := by
  rw [← closure_co1Gens]
  congr 1
  ext g
  exact List.mem_ofFn' _ _

theorem orbit_facts :
    (∀ g ∈ Subgroup.closure {g | g ∈ List.ofFn co1BrayGens},
      ∃ k < 4725, co1PairKey (co1FlagCode (g • co1BaseFlagL)) = FE k) ∧
    Nat.card {y : Co1Flag // ∃ g ∈ Subgroup.closure {g | g ∈ List.ofFn co1BrayGens},
      g • co1BaseFlagL = y} = 4725 := by
  have := finite_L₀
  have hM : ∀ j < (List.ofFn co1BrayGens).length, ∀ x : Co1Flag,
      co1PairKey (co1FlagCode ((List.ofFn co1BrayGens).getD j 1 • x)) =
        actF (co1PairKey (co1FlagCode x)) (MG j) := by
    intro j hj x
    rw [List.length_ofFn] at hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn, actF, MG_eq hj,
      stepF_smul]
  have h := orbit_card_proved co1FlagKey_injective (List.ofFn co1BrayGens) hM co1BaseFlagL
    (N := 4725) (by norm_num)
    (by rw [base_key, List.length_ofFn]; exact (P.allN_iff _ _).1 f_tree)
    ((P.allN_iff _ _).1 f_sort)
    (by rw [List.length_ofFn]; exact (P.allN_iff _ _).1 f_closed)
  exact ⟨h.2.1, h.2.2⟩

theorem card_orbit : Nat.card (MulAction.orbit L₀ co1BaseFlagL) = 4725 := by
  rw [← orbit_facts.2]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [MulAction.mem_orbit_iff, bgens_closure]
    simp)

theorem card_stab :
    Nat.card (MulAction.stabilizer L₀ co1BaseFlagL) = 9 * Nat.card co1Ubar := by
  classical
  have := finite_L₀
  have : Fintype ↥L₀ := Fintype.ofFinite L₀
  have : Fintype Co1Flag := Fintype.ofInjective (fun f : Co1Flag => (f.p, f.L))
    (fun f g h => Co1Flag.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have : Fintype (MulAction.orbit L₀ co1BaseFlagL) := Fintype.ofFinite _
  have : Fintype (MulAction.stabilizer L₀ co1BaseFlagL) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := L₀) co1BaseFlagL
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [card_orbit, card_L₀] at h
  rw [card_Ubar]
  omega

theorem Ubar_fixes : ∀ u ∈ co1Ubar, u • co1BaseFlagL = co1BaseFlagL := by
  have h0' : P.allN 4 (fun j => Nat.beq (stepF (UG j) (FE 0)) (FE 0)) = true :=
    (P.allN_iff _ _).1 f_fix 0 (by norm_num)
  have h0 := (P.allN_iff _ _).1 h0'
  have hle : co1Ubar ≤ MulAction.stabilizer L₀ co1BaseFlagL := by
    rw [co1Ubar_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨j, rfl⟩
    have h := Nat.eq_of_beq_eq_true (h0 j j.isLt)
    rw [UG_eq j.isLt, FE_zero, stepF_smul] at h
    exact co1FlagKey_injective h
  exact fun u hu => MulAction.mem_stabilizer_iff.mp (hle hu)

theorem uniq (d : L₀) (hd : ∀ u ∈ co1Ubar, u • (d • co1BaseFlagL) = d • co1BaseFlagL) :
    d • co1BaseFlagL = co1BaseFlagL := by
  obtain ⟨k, hk, hke⟩ := orbit_facts.1 d (by rw [bgens_closure]; exact Subgroup.mem_top d)
  cases k with
  | zero => exact co1FlagKey_injective (hke.trans FE_zero)
  | succ k =>
    have hfix : P.anyN 4 (fun j => notB (Nat.beq (stepF (UG j) (FE (k + 1))) (FE (k + 1)))) =
        true := (P.allN_iff _ _).1 f_fix (k + 1) hk
    obtain ⟨j, hj, hne⟩ := (P.anyN_iff _ _).1 hfix
    refine absurd ?_ (P.notB_iff.1 hne)
    rw [← hke, UG_eq hj, stepF_smul, hd _ (by
      rw [co1Ubar_eq_closure]
      exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩)]
    exact Nat.beq_refl _

theorem cols_X : co1Cols co1XEl = co1WordC MCols co1XWord :=
  co1Cols_eq_of_hasCols (co1WordC_length _ _) (co1WordC_getD_lt _ _)
    (hasCols_wordC MCols hasCols_M _ co1XWord_idx_lt)

theorem cols_Y : co1Cols co1YEl = co1WordC MCols co1YWord :=
  co1Cols_eq_of_hasCols (co1WordC_length _ _) (co1WordC_getD_lt _ _)
    (hasCols_wordC MCols hasCols_M _ co1YWord_idx_lt)

theorem x_pow : co1XEl ^ 3 = 1 := by
  apply co1Cols_injective
  rw [co1Cols_pow, cols_X, co1PowCols_three (co1WordC_length _ _) (co1WordC_getD_lt _ _)
    (co1XYCheckC_spec xy_chk).1, co1Cols_one]

theorem y_pow : co1YEl ^ 3 = 1 := by
  apply co1Cols_injective
  rw [co1Cols_pow, cols_Y, co1PowCols_three (co1WordC_length _ _) (co1WordC_getD_lt _ _)
    (co1XYCheckC_spec xy_chk).2.1, co1Cols_one]

theorem xy_comm : co1XEl * co1YEl = co1YEl * co1XEl := by
  apply co1Cols_injective
  rw [co1Cols_mul, co1Cols_mul, cols_X, cols_Y, (co1XYCheckC_spec xy_chk).2.2.1]

theorem x_ne : co1XEl ≠ 1 := by
  intro h
  apply (co1XYCheckC_spec xy_chk).2.2.2.1
  rw [← cols_X, h, co1Cols_one]

theorem y_ne : co1YEl ≠ 1 := by
  intro h
  apply (co1XYCheckC_spec xy_chk).2.2.2.2.1
  rw [← cols_Y, h, co1Cols_one]

theorem x_fix : co1XEl • co1BaseFlagL = co1BaseFlagL := by
  apply co1FlagCode_injective
  rw [co1FlagCode_smul, cols_X, co1FlagCode_base]
  exact (co1XYCheckC_spec xy_chk).2.2.2.2.2.2.2.1

theorem y_fix : co1YEl • co1BaseFlagL = co1BaseFlagL := by
  apply co1FlagCode_injective
  rw [co1FlagCode_smul, cols_Y, co1FlagCode_base]
  exact (co1XYCheckC_spec xy_chk).2.2.2.2.2.2.2.2

theorem y_not_mem : co1YEl ∉ Subgroup.zpowers co1XEl := by
  intro hmem
  have hord : orderOf co1XEl = 3 := orderOf_eq_prime x_pow x_ne
  have hfin : IsOfFinOrder co1XEl := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, x_pow⟩
  rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin, hord] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hky⟩ := hmem
  interval_cases k
  · exact y_ne (by rw [← hky, pow_zero])
  · apply (co1XYCheckC_spec xy_chk).2.2.2.2.2.1
    rw [← cols_Y, ← cols_X, ← hky, pow_one]
  · apply (co1XYCheckC_spec xy_chk).2.2.2.2.2.2.1
    rw [← cols_Y, ← hky, co1Cols_pow, cols_X,
      co1PowCols_two (co1WordC_length _ _) (co1WordC_getD_lt _ _)]

theorem package744110 : InnerIndexNinePackage L₀ :=
  innerIndexNinePackage_of_unique_fixed (U := co1Ubar) (x₀ := co1BaseFlagL) sylow_Ubar Ubar_fixes
    uniq card_stab x_fix y_fix x_pow y_pow xy_comm x_ne y_not_mem

end CertificateChecks.KernelCo1Nine

end
