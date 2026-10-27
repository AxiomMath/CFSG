module

public import CFSG.Quasithin.Recognition.St84.AutJ2VertexA
public import CFSG.Quasithin.Recognition.St84.J2ModelY3
public import Certificates.Certificate733002
public import CFSG.Quasithin.Recognition.St84.HeisF4Rigid

public section

namespace CFSG.Quasithin.F112R.St84.AutJ2Model

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.A312J2 CFSG.Quasithin.J2Cz CFSG.Quasithin.F112R
open CFSG.ComponentClassification.J2Cover
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Quasithin.F112R.St84.Heis
open CFSG.Fischer
open scoped commutatorElement

local instance (priority := high) f4DecEq : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

private theorem tp_map_ofNat {n : ℕ} (a : Array ℕ) (ha : ∀ x ∈ a, x < 2 ^ 32) :
    tp n (a.map UInt32.ofNat) = permOfArr n a := by
  have h : natArr (a.map UInt32.ofNat) = a := by
    unfold natArr
    rw [Array.map_map]
    refine Array.ext (by simp) fun i h1 h2 => ?_
    simp only [Array.getElem_map, Function.comp_apply]
    exact Nat.mod_eq_of_lt (ha _ (Array.getElem_mem h2))
  show permOfArr n (natArr (a.map UInt32.ofNat)) = permOfArr n a
  rw [h]

private theorem sylT_eq : sylT =
    [(sylowStrong[0]!).map UInt32.ofNat, (sylowStrong[1]!).map UInt32.ofNat,
      (sylowStrong[2]!).map UInt32.ofNat] := by
  decide +kernel

private theorem tp_sylT_0 :
    tp 315 ((sylowStrong[0]!).map UInt32.ofNat) = permOfArr 315 sylowStrong[0]! :=
  tp_map_ofNat (n := 315) (a := sylowStrong[0]!) (by decide +kernel)

private theorem tp_sylT_1 :
    tp 315 ((sylowStrong[1]!).map UInt32.ofNat) = permOfArr 315 sylowStrong[1]! :=
  tp_map_ofNat (n := 315) (a := sylowStrong[1]!) (by decide +kernel)

private theorem tp_sylT_2 :
    tp 315 ((sylowStrong[2]!).map UInt32.ofNat) = permOfArr 315 sylowStrong[2]! :=
  tp_map_ofNat (n := 315) (a := sylowStrong[2]!) (by decide +kernel)

private theorem tp_abuT_0 : tp 315 ((autStrong[0]!).map UInt32.ofNat) = permA :=
  tp_map_ofNat (n := 315) (a := autStrong[0]!) (by decide +kernel)

private theorem tp_abuT_1 : tp 315 ((autStrong[1]!).map UInt32.ofNat) = permB :=
  tp_map_ofNat (n := 315) (a := autStrong[1]!) (by decide +kernel)

private theorem tp_abuT_2 : tp 315 (outerArr.map UInt32.ofNat) = permU :=
  tp_map_ofNat (n := 315) (a := outerArr) (by decide +kernel)

noncomputable def WR : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 (sylT ++ [gWT])

noncomputable def X1R : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 (sylT ++ [g1T])

noncomputable def Q2R : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 q2T

private theorem mem_autJ2Tbls_of_inner {g : Table}
    (hg : g ∈ sylT ++ abuT ++ [gWT, g1T] ++ q2T) : g ∈ autJ2Tbls := by
  unfold autJ2Tbls
  exact List.mem_append_left _ hg

private theorem mem_inner_of_sylT {g : Table} (hg : g ∈ sylT) :
    g ∈ sylT ++ abuT ++ [gWT, g1T] ++ q2T := by
  show g ∈ ((sylT ++ abuT ++ [gWT, g1T]) ++ q2T)
  rw [List.mem_append]
  refine Or.inl ?_
  show g ∈ (sylT ++ abuT) ++ [gWT, g1T]
  rw [List.mem_append]
  refine Or.inl ?_
  show g ∈ sylT ++ abuT
  rw [List.mem_append]
  exact Or.inl hg

private theorem mem_inner_of_abuT {g : Table} (hg : g ∈ abuT) :
    g ∈ sylT ++ abuT ++ [gWT, g1T] ++ q2T := by
  show g ∈ ((sylT ++ abuT ++ [gWT, g1T]) ++ q2T)
  rw [List.mem_append]
  refine Or.inl ?_
  show g ∈ (sylT ++ abuT) ++ [gWT, g1T]
  rw [List.mem_append]
  refine Or.inl ?_
  show g ∈ sylT ++ abuT
  rw [List.mem_append]
  exact Or.inr hg

private theorem mem_inner_of_gWT : gWT ∈ sylT ++ abuT ++ [gWT, g1T] ++ q2T := by
  show gWT ∈ ((sylT ++ abuT ++ [gWT, g1T]) ++ q2T)
  rw [List.mem_append]
  refine Or.inl ?_
  show gWT ∈ (sylT ++ abuT) ++ [gWT, g1T]
  rw [List.mem_append]
  refine Or.inr ?_
  exact List.Mem.head _

private theorem mem_inner_of_g1T : g1T ∈ sylT ++ abuT ++ [gWT, g1T] ++ q2T := by
  show g1T ∈ ((sylT ++ abuT ++ [gWT, g1T]) ++ q2T)
  rw [List.mem_append]
  refine Or.inl ?_
  show g1T ∈ (sylT ++ abuT) ++ [gWT, g1T]
  rw [List.mem_append]
  refine Or.inr ?_
  exact List.Mem.tail _ (List.Mem.head _)

private theorem mem_inner_of_q2T {g : Table} (hg : g ∈ q2T) :
    g ∈ sylT ++ abuT ++ [gWT, g1T] ++ q2T := by
  show g ∈ ((sylT ++ abuT ++ [gWT, g1T]) ++ q2T)
  rw [List.mem_append]
  exact Or.inr hg

private theorem mem_autJ2Tbls_tail {g : Table}
    (hg : g ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT]) :
    g ∈ autJ2Tbls := by
  unfold autJ2Tbls
  exact List.mem_append_right _ hg

private theorem mem_autJ2Tbls_sylT {g : Table} (hg : g ∈ sylT) : g ∈ autJ2Tbls :=
  mem_autJ2Tbls_of_inner (mem_inner_of_sylT hg)

private theorem mem_autJ2Tbls_abuT {g : Table} (hg : g ∈ abuT) : g ∈ autJ2Tbls :=
  mem_autJ2Tbls_of_inner (mem_inner_of_abuT hg)

private theorem mem_autJ2Tbls_gWT : gWT ∈ autJ2Tbls :=
  mem_autJ2Tbls_of_inner mem_inner_of_gWT

private theorem mem_autJ2Tbls_g1T : g1T ∈ autJ2Tbls :=
  mem_autJ2Tbls_of_inner mem_inner_of_g1T

private theorem mem_autJ2Tbls_q2T {g : Table} (hg : g ∈ q2T) : g ∈ autJ2Tbls :=
  mem_autJ2Tbls_of_inner (mem_inner_of_q2T hg)

private theorem mem_tail_umT : umT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  List.Mem.head _

private theorem mem_tail_vmT : vmT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  List.Mem.tail _ (List.Mem.head _)

private theorem mem_tail_e1RT : e1RT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem mem_tail_e2RT : e2RT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem mem_tail_f1RT : f1RT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem mem_tail_f2RT :
    f2RT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _

private theorem mem_tail_tmRT :
    tmRT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _

private theorem mem_tail_gmRT :
    gmRT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _

private theorem mem_tail_bmRT :
    bmRT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _

private theorem mem_tail_rmRT :
    rmRT ∈ [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT] :=
  .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <|
    .tail _ <| .head _

private theorem permOK_sylT {h0 : autJ2VtxC0 () = true} :
    ∀ g ∈ sylT, permOK 315 g = true := fun g hg => autJ2VtxC0_perm h0 (mem_autJ2Tbls_sylT hg)

private theorem permOK_abuT {h0 : autJ2VtxC0 () = true} :
    ∀ g ∈ abuT, permOK 315 g = true := fun g hg => autJ2VtxC0_perm h0 (mem_autJ2Tbls_abuT hg)

private theorem permOK_X1R_list {h0 : autJ2VtxC0 () = true} :
    ∀ g ∈ sylT ++ [g1T], permOK 315 g = true := by
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · exact autJ2VtxC0_perm h0 (mem_autJ2Tbls_sylT hg)
  · rw [List.mem_singleton] at hg
    subst hg
    exact autJ2VtxC0_perm h0 mem_autJ2Tbls_g1T

private theorem permOK_q2T_list {h0 : autJ2VtxC0 () = true} :
    ∀ g ∈ q2T, permOK 315 g = true := fun g hg => autJ2VtxC0_perm h0 (mem_autJ2Tbls_q2T hg)

private theorem genOf_mono {n : ℕ} {gs hs : List Table} (h : ∀ g ∈ gs, g ∈ hs) :
    genOf n gs ≤ genOf n hs := by
  rw [genOf, genOf, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact tp_mem_genOf (h g (by simpa using hg))

private theorem sylowS_eq :
    sylowS = Subgroup.closure {g | ∃ i < 3, permOfArr 315 sylowStrong[i]! = g} := by
  rw [sylowS, sylowChain, ofArrays_originalSubgroup]

private theorem sylowS_le_genOf_sylT : sylowS ≤ genOf 315 sylT := by
  rw [sylowS_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  interval_cases i
  · rw [← tp_sylT_0]
    exact tp_mem_genOf (by simp [sylT_eq])
  · rw [← tp_sylT_1]
    exact tp_mem_genOf (by simp [sylT_eq])
  · rw [← tp_sylT_2]
    exact tp_mem_genOf (by simp [sylT_eq])

private theorem genOf_sylT_le_sylowS : genOf 315 sylT ≤ sylowS := by
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  rw [sylowS_eq]
  rw [sylT_eq] at hT
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨0, by norm_num, tp_sylT_0.symm⟩
  · exact Subgroup.subset_closure ⟨1, by norm_num, tp_sylT_1.symm⟩
  · exact Subgroup.subset_closure ⟨2, by norm_num, tp_sylT_2.symm⟩

private theorem genOf_abuT_eq_R : genOf 315 abuT = R := by
  apply le_antisymm
  · rw [genOf, Subgroup.closure_le]
    rintro _ ⟨T, hT, rfl⟩
    simp only [abuT, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl
    · rw [tp_abuT_0]; exact P_le_R permA_mem
    · rw [tp_abuT_1]; exact P_le_R permB_mem
    · rw [tp_abuT_2]; exact permU_mem_R
  · rw [R, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · rw [← tp_abuT_0]; exact tp_mem_genOf (by simp [abuT])
    · rw [← tp_abuT_1]; exact tp_mem_genOf (by simp [abuT])
    · rw [← tp_abuT_2]; exact tp_mem_genOf (by simp [abuT])

private theorem genOf_sylT_le_R : genOf 315 sylT ≤ R :=
  genOf_sylT_le_sylowS.trans sylowS_le_R

private theorem WR_le_R :
    WR ≤ R := by
  unfold WR
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  change T ∈ (sylT ++ [gWT]).toArray at hT
  rw [List.mem_toArray, List.mem_append] at hT
  rcases hT with hT | hT
  · exact genOf_sylT_le_R (tp_mem_genOf hT)
  · rw [List.mem_singleton] at hT
    subst hT
    rw [← genOf_abuT_eq_R]
    exact tp_wordTbl_mem (n := 315) (by norm_num)
      (permOK_abuT (h0 := Certificates.certificate733002.1))
      (by decide) (autJ2VtxC0_perm Certificates.certificate733002.1 mem_autJ2Tbls_gWT)

private theorem X1R_le_R :
    X1R ≤ R := by
  unfold X1R
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  change T ∈ (sylT ++ [g1T]).toArray at hT
  rw [List.mem_toArray, List.mem_append] at hT
  rcases hT with hT | hT
  · exact genOf_sylT_le_R (tp_mem_genOf hT)
  · rw [List.mem_singleton] at hT
    subst hT
    rw [← genOf_abuT_eq_R]
    exact tp_wordTbl_mem (n := 315) (by norm_num)
      (permOK_abuT (h0 := Certificates.certificate733002.1))
      (by decide) (autJ2VtxC0_perm Certificates.certificate733002.1 mem_autJ2Tbls_g1T)

private theorem Q2R_le_sylT : Q2R ≤ genOf 315 sylT := by
  unfold Q2R
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨T, hT, rfl⟩
  change T ∈ q2T.toArray at hT
  simp only [q2T, List.mem_toArray, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hT
  obtain ⟨w, hw, rfl⟩ := hT
  rcases hw with rfl | rfl | rfl | rfl <;>
    exact tp_wordTbl_mem (n := 315) (by norm_num)
      (permOK_sylT (h0 := Certificates.certificate733002.1)) (by decide)
      (autJ2VtxC0_perm Certificates.certificate733002.1
        (mem_autJ2Tbls_q2T (by simp [q2T])))

private theorem Q2R_le_WR : Q2R ≤ WR :=
  Q2R_le_sylT.trans (genOf_mono (by intro g hg; exact List.mem_append_left _ hg))

private theorem card_WR : Nat.card WR = 3840 :=
  Certificates.certificate733002.2.1.2.1

private theorem card_X1R : Nat.card X1R = 2304 :=
  Certificates.certificate733002.2.1.2.2

private theorem card_Q2R : Nat.card Q2R = 32 :=
  Certificates.certificate733002.2.2.1.1

private theorem WR_le_normalizer_Q2R :
    WR ≤ Subgroup.normalizer (Q2R : Set (Equiv.Perm (Fin 315))) :=
  Certificates.certificate733002.2.2.1.2

theorem WR_subgroupOf :
    WR.subgroupOf R = AJ2L.rCtx.Y 2 := by
  refine AJ2Y.eq_of_card (Or.inr rfl) ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [AJ2L.rCtx_S, Subgroup.mem_subgroupOf] at hx
    exact genOf_mono (by intro g hg; exact List.mem_append_left _ hg)
      (sylowS_le_genOf_sylT hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (WR_le_R)).toEquiv, card_WR, AJ2L.card_Y2]

theorem X1R_subgroupOf :
    X1R.subgroupOf R = AJ2L.rCtx.Y 1 := by
  refine AJ2Y.eq_of_card (Or.inl rfl) ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [AJ2L.rCtx_S, Subgroup.mem_subgroupOf] at hx
    exact genOf_mono (by intro g hg; exact List.mem_append_left _ hg)
      (sylowS_le_genOf_sylT hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (X1R_le_R)).toEquiv, card_X1R, AJ2L.card_Y1]

private theorem pCoreOf_Y2_le_J0 :
    pCoreOf 2 (AJ2L.rCtx.Y 2) ≤ J0 := by
  calc pCoreOf 2 (AJ2L.rCtx.Y 2)
      = (pCore 2 ↥(AJ2L.rCtx.Y 2)).map (AJ2L.rCtx.Y 2).subtype := rfl
    _ = (pCoreOf 2 (J0.subgroupOf (AJ2L.rCtx.Y 2))).map (AJ2L.rCtx.Y 2).subtype := by
          rw [pCoreOf_y2Inf_eq]
    _ ≤ (J0.subgroupOf (AJ2L.rCtx.Y 2)).map (AJ2L.rCtx.Y 2).subtype :=
          Subgroup.map_mono (pCoreOf_le (r := 2) _)
    _ = J0 ⊓ AJ2L.rCtx.Y 2 := Subgroup.subgroupOf_map_subtype _ _
    _ ≤ J0 := inf_le_left

private theorem pCoreOf_Y2_le_inf :
    pCoreOf 2 (AJ2L.rCtx.Y 2) ≤ J0 ⊓ AJ2L.rCtx.Y 2 :=
  le_inf (pCoreOf_Y2_le_J0) (pCoreOf_le 2 _)

private theorem pCoreOf_Y2_le_pCoreOf_inf :
    pCoreOf 2 (AJ2L.rCtx.Y 2) ≤ pCoreOf 2 (J0 ⊓ AJ2L.rCtx.Y 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := pCoreOf_Y2_le_inf
  refine le_pCoreOf (r := 2) hle ?_ (pCoreOf_isPGroup 2 _)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (inf_le_right.trans (Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_pCoreOf 2 (AJ2L.rCtx.Y 2))))

theorem Q2R_subgroupOf :
    Q2R.subgroupOf R = pCoreOf 2 (AJ2L.rCtx.Y 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQR : Q2R ≤ R := Q2R_le_WR.trans WR_le_R
  have hcardQ : Nat.card (Q2R.subgroupOf R) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv, card_Q2R]
  have hle : Q2R.subgroupOf R ≤ AJ2L.rCtx.Y 2 := by
    rw [← WR_subgroupOf]
    exact Subgroup.subgroupOf_mono R Q2R_le_WR
  have hnorm : AJ2L.rCtx.Y 2 ≤ Subgroup.normalizer (Q2R.subgroupOf R : Set ↥R) := by
    rw [← WR_subgroupOf, ← Subgroup.subgroupOf_normalizer_eq (H := Q2R) (N := R) hQR]
    exact Subgroup.subgroupOf_mono R (WR_le_normalizer_Q2R)
  have hp : IsPGroup 2 (Q2R.subgroupOf R) :=
    IsPGroup.of_card (p := 2) (n := 5) (by rw [hcardQ]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge (le_pCoreOf_of_le_normalizer (r := 2) hle hnorm hp) ?_
  rw [AJ2L.card_pCoreOf_Y2, hcardQ]
  norm_num

theorem autJ2Vertex_Y2 :
    AutJ2Vertex (AJ2L.rCtx.Y 2) (J0 ⊓ AJ2L.rCtx.Y 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrel : (J0 ⊓ AJ2L.rCtx.Y 2).relIndex (AJ2L.rCtx.Y 2) = 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact relIndex_J0 (AJ2L.rCtx.S_le_Y 2)
  refine ⟨inf_le_right, hrel, ?_, pCoreOf_Y2_le_inf, ?_⟩
  · obtain ⟨e1⟩ := nonempty_y2InfEquiv
    obtain ⟨e2⟩ := J2Model.nonempty_mulEquiv_Y3
    exact ⟨((Subgroup.subgroupOfEquivOfLe
        (inf_le_right : J0 ⊓ AJ2L.rCtx.Y 2 ≤ AJ2L.rCtx.Y 2)).symm.trans
      (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right J0 (AJ2L.rCtx.Y 2)))).trans
        (e1.trans e2)⟩
  · have h0 : autJ2VtxC0 () = true := Certificates.certificate733002.1
    have h3 : autJ2VtxC3 () = true := Certificates.certificate733002.2.2.2.1
    obtain ⟨hum_invo, hum_notP, hvm_invo, hvm_notcomm, huv_comm⟩ := autJ2VtxC3_spec h3
    have hum_perm : permOK 315 umT = true :=
      autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_umT)
    have hvm_perm : permOK 315 vmT = true :=
      autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_vmT)
    have hum_sylT : tp 315 umT ∈ genOf 315 sylT :=
      tp_wordTbl_mem (n := 315) (by norm_num) (permOK_sylT (h0 := h0)) (by decide) hum_perm
    have hvm_q2T : tp 315 vmT ∈ Q2R :=
      tp_wordTbl_mem (n := 315) (by norm_num) (permOK_q2T_list (h0 := h0)) (by decide) hvm_perm
    have hum_W : tp 315 umT ∈ WR :=
      genOf_mono (by intro g hg; exact List.mem_append_left _ hg) hum_sylT
    have hvm_W : tp 315 vmT ∈ WR := Q2R_le_WR hvm_q2T
    have hum_R : tp 315 umT ∈ R := WR_le_R hum_W
    have hvm_R : tp 315 vmT ∈ R := WR_le_R hvm_W
    have hum_sq : (tp 315 umT) ^ 2 = 1 := sq_eq_one_of_invoOK (rep_tp hum_perm) hum_invo
    have hvm_sq : (tp 315 vmT) ^ 2 = 1 := sq_eq_one_of_invoOK (rep_tp hvm_perm) hvm_invo
    have hq2_mem : q2T[0]! ∈ q2T := by
      rw [getElem!_pos q2T 0 (by simp [q2T])]
      exact List.getElem_mem (by simp [q2T])
    have hq2_perm : permOK 315 q2T[0]! = true :=
      permOK_q2T_list (h0 := h0) (g := q2T[0]!) hq2_mem
    have hq2_R : tp 315 q2T[0]! ∈ R :=
      Q2R_le_WR.trans WR_le_R (tp_mem_genOf hq2_mem)
    refine ⟨⟨tp 315 umT, hum_R⟩, ?_, ?_, ?_, ⟨tp 315 vmT, hvm_R⟩, ?_, ?_, ?_, ?_⟩
    · rw [← WR_subgroupOf, Subgroup.mem_subgroupOf]
      exact hum_W
    · intro hu
      have huJ : (⟨tp 315 umT, hum_R⟩ : ↥R) ∈ J0 := (Subgroup.mem_inf.mp hu).1
      rw [J0_eq, Subgroup.mem_subgroupOf] at huJ
      have htrue : inP (natArr umT) = true :=
        (mem_P_iff (t := natArr umT) (co2Rep_natArr_iff.2 (rep_tp hum_perm))).2 huJ
      rw [hum_notP] at htrue
      exact Bool.false_ne_true htrue
    · apply Subtype.ext
      change (tp 315 umT) ^ 2 = (1 : Equiv.Perm (Fin 315))
      exact hum_sq
    · have hvQ2 : (⟨tp 315 vmT, hvm_R⟩ : ↥R) ∈ pCoreOf 2 (AJ2L.rCtx.Y 2) := by
        rw [← Q2R_subgroupOf]
        exact hvm_q2T
      exact pCoreOf_Y2_le_pCoreOf_inf hvQ2
    · apply Subtype.ext
      change (tp 315 vmT) ^ 2 = (1 : Equiv.Perm (Fin 315))
      exact hvm_sq
    · intro hv
      have hw_core : (⟨tp 315 q2T[0]!, hq2_R⟩ : ↥R) ∈ pCoreOf 2 (J0 ⊓ AJ2L.rCtx.Y 2) := by
        refine pCoreOf_Y2_le_pCoreOf_inf ?_
        rw [← Q2R_subgroupOf]
        exact tp_mem_genOf (by simp [q2T])
      have hcomm := (Subgroup.mem_centralizer_iff.mp hv) _ hw_core
      have hnc : ¬ (tp 315 vmT * tp 315 q2T[0]! =
          tp 315 q2T[0]! * tp 315 vmT) := by
        intro h
        have h' : commTT 315 vmT q2T[0]! = true :=
          (commTT_iff (rep_tp hvm_perm) (rep_tp hq2_perm)).2 h
        rw [hvm_notcomm] at h'
        exact Bool.false_ne_true h'
      exact hnc (Subtype.ext_iff.mp hcomm.symm)
    · apply Subtype.ext
      exact (commTT_iff (rep_tp hum_perm) (rep_tp hvm_perm)).1 huv_comm

private theorem permOK_e1RT {h0 : autJ2VtxC0 () = true} : permOK 315 e1RT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_e1RT)

private theorem permOK_e2RT {h0 : autJ2VtxC0 () = true} : permOK 315 e2RT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_e2RT)

private theorem permOK_f1RT {h0 : autJ2VtxC0 () = true} : permOK 315 f1RT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_f1RT)

private theorem permOK_f2RT {h0 : autJ2VtxC0 () = true} : permOK 315 f2RT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_f2RT)

private theorem invOK_e1RT {h0 : autJ2VtxC0 () = true} :
    invOK 315 e1RT (invT 315 e1RT) = true :=
  autJ2VtxC0_inv h0 (mem_autJ2Tbls_tail mem_tail_e1RT)

private theorem invOK_f1RT {h0 : autJ2VtxC0 () = true} :
    invOK 315 f1RT (invT 315 f1RT) = true :=
  autJ2VtxC0_inv h0 (mem_autJ2Tbls_tail mem_tail_f1RT)

private theorem invOK_f2RT {h0 : autJ2VtxC0 () = true} :
    invOK 315 f2RT (invT 315 f2RT) = true :=
  autJ2VtxC0_inv h0 (mem_autJ2Tbls_tail mem_tail_f2RT)

private theorem rep_EmT_val {h0 : autJ2VtxC0 () = true} (a : F4) :
    Rep 315 (EmT a) (E1R ^ (a.code.val % 2) * E2R ^ (a.code.val / 2)) := by
  unfold EmT
  exact Rep.compT
    (Rep.powT (n := 315) (by norm_num) (rep_tp (permOK_e1RT (h0 := h0))) _)
    (Rep.powT (n := 315) (by norm_num) (rep_tp (permOK_e2RT (h0 := h0))) _)

private theorem rep_FmT_val {h0 : autJ2VtxC0 () = true} (b : F4) :
    Rep 315 (FmT b) (F1R ^ (b.code.val % 2) * F2R ^ (b.code.val / 2)) := by
  unfold FmT
  exact Rep.compT
    (Rep.powT (n := 315) (by norm_num) (rep_tp (permOK_f1RT (h0 := h0))) _)
    (Rep.powT (n := 315) (by norm_num) (rep_tp (permOK_f2RT (h0 := h0))) _)

private theorem rep_FmInvT_zero {h0 : autJ2VtxC0 () = true} :
    Rep 315 (FmInvT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := by
  unfold FmInvT
  rw [show (0 : F4).code.val = 0 from rfl]
  norm_num
  simpa using (Rep.compT (G := Equiv.Perm (Fin 315))
    (Rep.powT (n := 315) (by norm_num)
      (rep_invT (rep_tp (permOK_f2RT (h0 := h0))) (invOK_f2RT (h0 := h0))) 0)
    (Rep.powT (n := 315) (by norm_num)
      (rep_invT (rep_tp (permOK_f1RT (h0 := h0))) (invOK_f1RT (h0 := h0))) 0))

private theorem rep_κRT_e1 {h0 : autJ2VtxC0 () = true} : Rep 315 (κRT e1) E1R := by
  unfold κRT
  dsimp only
  have ha : (e1 : Q1M).a = 1 := rfl
  have hb : (e1 : Q1M).b = 0 := rfl
  rw [ha, hb]
  have hw : (e1 : Q1M).c + (1 : F4) * 0 = 0 := by decide
  rw [hw]
  have hE : Rep 315 (EmT (1 : F4)) E1R := by
    have h := rep_EmT_val (h0 := h0) (1 : F4)
    rw [show (1 : F4).code.val = 1 from rfl] at h
    norm_num at h
    simpa using h
  have hF0 : Rep 315 (FmT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := by
    have h := rep_FmT_val (h0 := h0) (0 : F4)
    rw [show (0 : F4).code.val = 0 from rfl] at h
    norm_num at h
    simpa using h
  have hFi0 : Rep 315 (FmInvT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := rep_FmInvT_zero (h0 := h0)
  have hiE : Rep 315 (invT 315 e1RT) E1R⁻¹ :=
    rep_invT (rep_tp (permOK_e1RT (h0 := h0))) (invOK_e1RT (h0 := h0))
  have h := Rep.compT (Rep.compT hE hF0)
    (Rep.compT (Rep.compT (Rep.compT (rep_tp (permOK_e1RT (h0 := h0))) hF0) hiE) hFi0)
  simpa [mul_one, inv_one] using h

private theorem rep_κRT_e2 {h0 : autJ2VtxC0 () = true} : Rep 315 (κRT e2) E2R := by
  unfold κRT
  dsimp only
  have ha : (e2 : Q1M).a = F4.ω := rfl
  have hb : (e2 : Q1M).b = 0 := rfl
  rw [ha, hb]
  have hw : (e2 : Q1M).c + F4.ω * 0 = 0 := by decide
  rw [hw]
  have hE : Rep 315 (EmT F4.ω) E2R := by
    have h := rep_EmT_val (h0 := h0) F4.ω
    rw [show F4.ω.code.val = 2 from rfl] at h
    norm_num at h
    simpa using h
  have hF0 : Rep 315 (FmT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := by
    have h := rep_FmT_val (h0 := h0) (0 : F4)
    rw [show (0 : F4).code.val = 0 from rfl] at h
    norm_num at h
    simpa using h
  have hFi0 : Rep 315 (FmInvT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := rep_FmInvT_zero (h0 := h0)
  have hiE : Rep 315 (invT 315 e1RT) E1R⁻¹ :=
    rep_invT (rep_tp (permOK_e1RT (h0 := h0))) (invOK_e1RT (h0 := h0))
  have h := Rep.compT (Rep.compT hE hF0)
    (Rep.compT (Rep.compT (Rep.compT (rep_tp (permOK_e1RT (h0 := h0))) hF0) hiE) hFi0)
  simpa [mul_one, inv_one] using h

private theorem rep_κRT_f1 {h0 : autJ2VtxC0 () = true} : Rep 315 (κRT f1) F1R := by
  unfold κRT
  dsimp only
  have ha : (f1 : Q1M).a = 0 := rfl
  have hb : (f1 : Q1M).b = 1 := rfl
  rw [ha, hb]
  have hw : (f1 : Q1M).c + (0 : F4) * 1 = 0 := by decide
  rw [hw]
  have hE : Rep 315 (EmT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := by
    have h := rep_EmT_val (h0 := h0) (0 : F4)
    rw [show (0 : F4).code.val = 0 from rfl] at h
    norm_num at h
    simpa using h
  have hF1 : Rep 315 (FmT (1 : F4)) F1R := by
    have h := rep_FmT_val (h0 := h0) (1 : F4)
    rw [show (1 : F4).code.val = 1 from rfl] at h
    norm_num at h
    simpa using h
  have hF0 : Rep 315 (FmT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := by
    have h := rep_FmT_val (h0 := h0) (0 : F4)
    rw [show (0 : F4).code.val = 0 from rfl] at h
    norm_num at h
    simpa using h
  have hFi0 : Rep 315 (FmInvT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := rep_FmInvT_zero (h0 := h0)
  have hiE : Rep 315 (invT 315 e1RT) E1R⁻¹ :=
    rep_invT (rep_tp (permOK_e1RT (h0 := h0))) (invOK_e1RT (h0 := h0))
  have h := Rep.compT (Rep.compT hE hF1)
    (Rep.compT (Rep.compT (Rep.compT (rep_tp (permOK_e1RT (h0 := h0))) hF0) hiE) hFi0)
  simpa [mul_one, one_mul, inv_one] using h

private theorem rep_κRT_f2 {h0 : autJ2VtxC0 () = true} : Rep 315 (κRT f2) F2R := by
  unfold κRT
  dsimp only
  have ha : (f2 : Q1M).a = 0 := rfl
  have hb : (f2 : Q1M).b = F4.ω := rfl
  rw [ha, hb]
  have hw : (f2 : Q1M).c + (0 : F4) * F4.ω = 0 := by decide
  rw [hw]
  have hE : Rep 315 (EmT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := by
    have h := rep_EmT_val (h0 := h0) (0 : F4)
    rw [show (0 : F4).code.val = 0 from rfl] at h
    norm_num at h
    simpa using h
  have hF2 : Rep 315 (FmT F4.ω) F2R := by
    have h := rep_FmT_val (h0 := h0) F4.ω
    rw [show F4.ω.code.val = 2 from rfl] at h
    norm_num at h
    simpa using h
  have hF0 : Rep 315 (FmT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := by
    have h := rep_FmT_val (h0 := h0) (0 : F4)
    rw [show (0 : F4).code.val = 0 from rfl] at h
    norm_num at h
    simpa using h
  have hFi0 : Rep 315 (FmInvT (0 : F4)) (1 : Equiv.Perm (Fin 315)) := rep_FmInvT_zero (h0 := h0)
  have hiE : Rep 315 (invT 315 e1RT) E1R⁻¹ :=
    rep_invT (rep_tp (permOK_e1RT (h0 := h0))) (invOK_e1RT (h0 := h0))
  have h := Rep.compT (Rep.compT hE hF2)
    (Rep.compT (Rep.compT (Rep.compT (rep_tp (permOK_e1RT (h0 := h0))) hF0) hiE) hFi0)
  simpa [mul_one, one_mul, inv_one] using h

private theorem κR_e1 : κR e1 = E1R :=
  rep_unique (rep_κRT Certificates.certificate733002.1 e1)
    (rep_κRT_e1 (h0 := Certificates.certificate733002.1))

private theorem κR_e2 : κR e2 = E2R :=
  rep_unique (rep_κRT Certificates.certificate733002.1 e2)
    (rep_κRT_e2 (h0 := Certificates.certificate733002.1))

private theorem κR_f1 : κR f1 = F1R :=
  rep_unique (rep_κRT Certificates.certificate733002.1 f1)
    (rep_κRT_f1 (h0 := Certificates.certificate733002.1))

private theorem κR_f2 : κR f2 = F2R :=
  rep_unique (rep_κRT Certificates.certificate733002.1 f2)
    (rep_κRT_f2 (h0 := Certificates.certificate733002.1))

private abbrev Q1Gens : List Table := q1Gens

private theorem Q1Gens_eq : Q1Gens = [e1RT, e2RT, f1RT, f2RT] := rfl

private theorem q1Gens_eq : q1Gens = [e1RT, e2RT, f1RT, f2RT] := rfl

private def A'Gens : List Table := [rmRT, bmRT, tmRT, gmRT]

private theorem A'Gens_eq : A'Gens = [rmRT, bmRT, tmRT, gmRT] := rfl

private noncomputable def Q1R : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 Q1Gens

private noncomputable def A'R : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 A'Gens

private theorem E1R_mem_Q1R : E1R ∈ Q1R :=
  tp_mem_genOf (show e1RT ∈ Q1Gens by rw [Q1Gens_eq]; exact List.Mem.head _)

private theorem E2R_mem_Q1R : E2R ∈ Q1R :=
  tp_mem_genOf (show e2RT ∈ Q1Gens by rw [Q1Gens_eq]; exact List.Mem.tail _ (List.Mem.head _))

private theorem F1R_mem_Q1R : F1R ∈ Q1R :=
  tp_mem_genOf (show f1RT ∈ Q1Gens by
    rw [Q1Gens_eq]; exact .tail _ <| .tail _ <| .head _)

private theorem F2R_mem_Q1R : F2R ∈ Q1R :=
  tp_mem_genOf (show f2RT ∈ Q1Gens by
    rw [Q1Gens_eq]; exact .tail _ <| .tail _ <| .tail _ <| .head _)

private noncomputable def κRHom :
    Q1M →* Equiv.Perm (Fin 315) where
  toFun := κR
  map_one' := κR_one
  map_mul' := fun x y =>
    κR_mul Certificates.certificate733002.1
      Certificates.certificate733002.2.2.2.2.1 x y

private theorem κRHom_injective :
    Function.Injective κRHom :=
  κR_injective Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1

private theorem κR_range_eq_Q1R : κRHom.range = Q1R := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    have hq : q ∈ Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) := by
      rw [closure_gens]
      exact Subgroup.mem_top q
    have hpre : Subgroup.closure ({e1, e2, f1, f2} : Set Q1M) ≤ Q1R.comap κRHom := by
      rw [Subgroup.closure_le]
      rintro q (rfl | rfl | rfl | rfl)
      · change κR e1 ∈ Q1R; rw [κR_e1]; exact E1R_mem_Q1R
      · change κR e2 ∈ Q1R; rw [κR_e2]; exact E2R_mem_Q1R
      · change κR f1 ∈ Q1R; rw [κR_f1]; exact F1R_mem_Q1R
      · change κR f2 ∈ Q1R; rw [κR_f2]; exact F2R_mem_Q1R
    exact hpre hq
  · rw [Q1R, genOf, Subgroup.closure_le]
    rintro _ ⟨T, hT, rfl⟩
    change T ∈ q1Gens.toArray at hT
    rw [q1Gens_eq, List.mem_toArray] at hT
    rw [List.mem_cons] at hT
    rcases hT with rfl | hT
    · exact ⟨e1, κR_e1⟩
    rw [List.mem_cons] at hT
    rcases hT with rfl | hT
    · exact ⟨e2, κR_e2⟩
    rw [List.mem_cons] at hT
    rcases hT with rfl | hT
    · exact ⟨f1, κR_f1⟩
    rw [List.mem_cons] at hT
    rcases hT with rfl | hT
    · exact ⟨f2, κR_f2⟩
    rw [List.mem_nil_iff] at hT
    exact absurd hT (by simp)

private noncomputable def χR : ↥Q1R ≃* Q1M :=
  (MulEquiv.subgroupCongr (κR_range_eq_Q1R).symm).trans
    (MonoidHom.ofInjective (κRHom_injective)).symm

private theorem χR_apply (x : ↥Q1R) :
    κR (χR x) = (x : Equiv.Perm (Fin 315)) := by
  change κRHom ((MonoidHom.ofInjective (κRHom_injective)).symm
    (MulEquiv.subgroupCongr (κR_range_eq_Q1R).symm x)) = _
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

private theorem genOf_le_of_mem {n : ℕ} {gs hs : List Table}
    (h : ∀ g ∈ gs, tp n g ∈ genOf n hs) : genOf n gs ≤ genOf n hs := by
  rw [genOf, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact h g (by simpa using hg)

private theorem e1RT_mem_sylT {h0 : autJ2VtxC0 () = true} : tp 315 e1RT ∈ genOf 315 sylT :=
  tp_wordTbl_mem (n := 315) (by norm_num) (permOK_sylT (h0 := h0)) (by decide)
    (permOK_e1RT (h0 := h0))

private theorem e2RT_mem_sylT {h0 : autJ2VtxC0 () = true} : tp 315 e2RT ∈ genOf 315 sylT :=
  tp_wordTbl_mem (n := 315) (by norm_num) (permOK_sylT (h0 := h0)) (by decide)
    (permOK_e2RT (h0 := h0))

private theorem f1RT_mem_sylT {h0 : autJ2VtxC0 () = true} : tp 315 f1RT ∈ genOf 315 sylT :=
  tp_wordTbl_mem (n := 315) (by norm_num) (permOK_sylT (h0 := h0)) (by decide)
    (permOK_f1RT (h0 := h0))

private theorem f2RT_mem_sylT {h0 : autJ2VtxC0 () = true} : tp 315 f2RT ∈ genOf 315 sylT :=
  tp_wordTbl_mem (n := 315) (by norm_num) (permOK_sylT (h0 := h0)) (by decide)
    (permOK_f2RT (h0 := h0))

private theorem Q1R_le_X1R : Q1R ≤ X1R := by
  rw [Q1R]
  refine genOf_le_of_mem ?_
  intro g hg
  rw [Q1Gens_eq] at hg
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact genOf_mono (by intro x hx; exact List.mem_append_left _ hx)
      (e1RT_mem_sylT (h0 := Certificates.certificate733002.1))
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact genOf_mono (by intro x hx; exact List.mem_append_left _ hx)
      (e2RT_mem_sylT (h0 := Certificates.certificate733002.1))
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact genOf_mono (by intro x hx; exact List.mem_append_left _ hx)
      (f1RT_mem_sylT (h0 := Certificates.certificate733002.1))
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact genOf_mono (by intro x hx; exact List.mem_append_left _ hx)
      (f2RT_mem_sylT (h0 := Certificates.certificate733002.1))
  rw [List.mem_nil_iff] at hg
  exact absurd hg (by simp)

private theorem rmRT_mem_A'R : rmR ∈ A'R :=
  tp_mem_genOf (show rmRT ∈ A'Gens by rw [A'Gens_eq]; exact List.Mem.head _)

private theorem bmRT_mem_A'R : bmR ∈ A'R :=
  tp_mem_genOf (show bmRT ∈ A'Gens by rw [A'Gens_eq]; exact List.Mem.tail _ (List.Mem.head _))

private theorem tmRT_mem_A'R : tmR ∈ A'R :=
  tp_mem_genOf (show tmRT ∈ A'Gens by
    rw [A'Gens_eq]; exact .tail _ <| .tail _ <| .head _)

private theorem gmRT_mem_A'R : gmR ∈ A'R :=
  tp_mem_genOf (show gmRT ∈ A'Gens by
    rw [A'Gens_eq]; exact .tail _ <| .tail _ <| .tail _ <| .head _)

private theorem permOK_rmRT {h0 : autJ2VtxC0 () = true} : permOK 315 rmRT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_rmRT)

private theorem permOK_bmRT {h0 : autJ2VtxC0 () = true} : permOK 315 bmRT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_bmRT)

private theorem permOK_tmRT {h0 : autJ2VtxC0 () = true} : permOK 315 tmRT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_tmRT)

private theorem permOK_gmRT {h0 : autJ2VtxC0 () = true} : permOK 315 gmRT = true :=
  autJ2VtxC0_perm h0 (mem_autJ2Tbls_tail mem_tail_gmRT)

private theorem rmRT_mem_X1R {h0 : autJ2VtxC0 () = true} : tp 315 rmRT ∈ X1R :=
  tp_wordTbl_mem (n := 315) (by norm_num) (permOK_X1R_list (h0 := h0)) (by decide)
    (permOK_rmRT (h0 := h0))

private theorem bmRT_mem_X1R {h0 : autJ2VtxC0 () = true} : tp 315 bmRT ∈ X1R :=
  tp_wordTbl_mem (n := 315) (by norm_num) (permOK_X1R_list (h0 := h0)) (by decide)
    (permOK_bmRT (h0 := h0))

private theorem tmRT_mem_X1R {h0 : autJ2VtxC0 () = true} : tp 315 tmRT ∈ X1R :=
  genOf_mono (by intro x hx; exact List.mem_append_left _ hx)
    (tp_wordTbl_mem (n := 315) (by norm_num) (permOK_sylT (h0 := h0)) (by decide)
      (permOK_tmRT (h0 := h0)))

private theorem gmRT_mem_X1R {h0 : autJ2VtxC0 () = true} : tp 315 gmRT ∈ X1R :=
  genOf_mono (by intro x hx; exact List.mem_append_left _ hx)
    (tp_wordTbl_mem (n := 315) (by norm_num) (permOK_sylT (h0 := h0)) (by decide)
      (permOK_gmRT (h0 := h0)))

private theorem A'R_le_X1R : A'R ≤ X1R := by
  rw [A'R]
  refine genOf_le_of_mem ?_
  intro g hg
  rw [A'Gens_eq] at hg
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact rmRT_mem_X1R (h0 := Certificates.certificate733002.1)
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact bmRT_mem_X1R (h0 := Certificates.certificate733002.1)
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact tmRT_mem_X1R (h0 := Certificates.certificate733002.1)
  rw [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact gmRT_mem_X1R (h0 := Certificates.certificate733002.1)
  rw [List.mem_nil_iff] at hg
  exact absurd hg (by simp)

private theorem X1R_le_normalizer_Q1R :
    X1R ≤ Subgroup.normalizer (Q1R : Set (Equiv.Perm (Fin 315))) :=
  Certificates.certificate733002.2.2.2.2.2.2.1.2

private theorem card_Q1R : Nat.card Q1R = 64 := by
  rw [← κR_range_eq_Q1R]
  rw [← Nat.card_congr (MonoidHom.ofInjective (κRHom_injective)).toEquiv]
  exact card_Q1M

private theorem card_A'R : Nat.card A'R = 36 := by
  unfold A'R
  rw [A'Gens_eq]
  exact Certificates.certificate733002.2.2.2.2.2.2.1.1

private noncomputable def actA' : ↥A'R →* MulAut Q1M :=
  (parAct X1R_le_normalizer_Q1R χR).comp (Subgroup.inclusion (A'R_le_X1R))

private theorem actsAs_rm : ActsAs χR rmR ρM := by
  intro x y hy
  apply κR_injective Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
  rw [χR_apply, hy, ← χR_apply]
  exact κR_rm_conj Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
    Certificates.certificate733002.2.2.2.2.2.1 (χR x)

private theorem actsAs_bm : ActsAs χR bmR βM := by
  intro x y hy
  apply κR_injective Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
  rw [χR_apply, hy, ← χR_apply]
  exact κR_bm_conj Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
    Certificates.certificate733002.2.2.2.2.2.1 (χR x)

private theorem actsAs_tm : ActsAs χR tmR τM := by
  intro x y hy
  apply κR_injective Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
  rw [χR_apply, hy, ← χR_apply]
  exact κR_tm_conj Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
    Certificates.certificate733002.2.2.2.2.2.1 (χR x)

private theorem actsAs_gm : ActsAs χR gmR γM := by
  intro x y hy
  apply κR_injective Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
  rw [χR_apply, hy, ← χR_apply]
  exact κR_gm_conj Certificates.certificate733002.1
    Certificates.certificate733002.2.2.2.2.1
    Certificates.certificate733002.2.2.2.2.2.1 (χR x)

private theorem actA'_rm :
    actA' ⟨rmR, rmRT_mem_A'R⟩ = ρM := by
  show parAct X1R_le_normalizer_Q1R χR ⟨rmR, A'R_le_X1R rmRT_mem_A'R⟩ = ρM
  exact parAct_eq_of_actsAs (A'R_le_X1R rmRT_mem_A'R) actsAs_rm

private theorem actA'_bm :
    actA' ⟨bmR, bmRT_mem_A'R⟩ = βM := by
  show parAct X1R_le_normalizer_Q1R χR ⟨bmR, A'R_le_X1R bmRT_mem_A'R⟩ = βM
  exact parAct_eq_of_actsAs (A'R_le_X1R bmRT_mem_A'R) actsAs_bm

private theorem actA'_tm :
    actA' ⟨tmR, tmRT_mem_A'R⟩ = τM := by
  show parAct X1R_le_normalizer_Q1R χR ⟨tmR, A'R_le_X1R tmRT_mem_A'R⟩ = τM
  exact parAct_eq_of_actsAs (A'R_le_X1R tmRT_mem_A'R) actsAs_tm

private theorem actA'_gm :
    actA' ⟨gmR, gmRT_mem_A'R⟩ = γM := by
  show parAct X1R_le_normalizer_Q1R χR ⟨gmR, A'R_le_X1R gmRT_mem_A'R⟩ = γM
  exact parAct_eq_of_actsAs (A'R_le_X1R gmRT_mem_A'R) actsAs_gm

theorem nonempty_Y1_equiv :
    Nonempty (↥(AJ2L.rCtx.Y 1) ≃* Q1M ⋊[AJ'.subtype] ↥AJ') := by
  have hQP : Q1R ≤ X1R := Q1R_le_X1R
  have hPQ : X1R ≤ Subgroup.normalizer (Q1R : Set (Equiv.Perm (Fin 315))) :=
    X1R_le_normalizer_Q1R
  have hAP : A'R ≤ X1R := A'R_le_X1R
  have hρ : ρM ∈ actA'.range := by
    rw [← actA'_rm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hβ : βM ∈ actA'.range := by
    rw [← actA'_bm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hτ : τM ∈ actA'.range := by
    rw [← actA'_tm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hγ : γM ∈ actA'.range := by
    rw [← actA'_gm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hAJle : AJ' ≤ actA'.range := by
    intro x hx
    rw [mem_AJ'_iff, mem_aj'List] at hx
    obtain ⟨i, j, k, l, rfl⟩ := hx
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hρ _) (Subgroup.pow_mem _ hβ _))
        (Subgroup.pow_mem _ hτ _)) (Subgroup.pow_mem _ hγ _)
  have hcardrange : Nat.card actA'.range = 36 := by
    have h1 : Nat.card actA'.range ≤ Nat.card ↥A'R :=
      Nat.card_le_card_of_surjective
        (fun a : ↥A'R => (⟨actA' a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ : ↥actA'.range))
        (fun b => by
          obtain ⟨a, ha⟩ := b.2
          exact ⟨a, Subtype.ext ha⟩)
    rw [card_A'R] at h1
    have h2 : 36 ≤ Nat.card actA'.range := by
      rw [← card_AJ']
      exact Nat.card_le_card_of_injective (Subgroup.inclusion hAJle)
        (Subgroup.inclusion_injective hAJle)
    omega
  have hrange : actA'.range = AJ' := by
    rw [eq_comm]
    exact Subgroup.eq_of_le_of_card_ge hAJle (by rw [card_AJ', hcardrange])
  have hinj : Function.Injective actA' := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥A'R) actA'.ker
    have hq : Nat.card (↥A'R ⧸ actA'.ker) = Nat.card actA'.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange actA').toEquiv
    rw [hq, hrange, card_AJ', card_A'R] at hcard
    have hker : Nat.card actA'.ker = 1 := by omega
    refine (MonoidHom.ker_eq_bot_iff actA').mp ?_
    rw [Subgroup.eq_bot_iff_card]
    exact hker
  have hAQ : A'R ⊓ Q1R = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haA, haQ⟩ := Subgroup.mem_inf.mp ha
    have h1 : actA' ⟨a, haA⟩ = MulAut.conj (χR ⟨a, haQ⟩) := by
      show parAct (X1R_le_normalizer_Q1R) χR ⟨a, A'R_le_X1R haA⟩ =
        MulAut.conj (χR ⟨a, haQ⟩)
      exact parAct_of_mem haQ (A'R_le_X1R haA)
    have h2 : actA' ⟨a, haA⟩ ∈ AJ' := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h3 : MulAut.conj (χR ⟨a, haQ⟩) ∈ AJ' := h1 ▸ h2
    have h4 : MulAut.conj (χR ⟨a, haQ⟩) = 1 := conj_eq_one_of_mem_AJ' h3
    have h5 : actA' ⟨a, haA⟩ = 1 := by rw [h1, h4]
    have h5' : actA' ⟨a, haA⟩ = actA' 1 := by rw [h5, map_one]
    have h6 : (⟨a, haA⟩ : ↥A'R) = 1 := hinj h5'
    simpa using congrArg Subtype.val h6
  have hcard : Nat.card Q1R * Nat.card A'R = Nat.card X1R := by
    rw [card_Q1R, card_A'R, card_X1R]
  let e : ↥A'R ≃* ↥AJ' := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ a : ↥A'R, (e a : MulAut Q1M) =
      parAct (X1R_le_normalizer_Q1R) χR (Subgroup.inclusion hAP a) := fun a => rfl
  obtain ⟨eX⟩ := nonempty_mulEquiv_semidirect hQP hPQ hAP hAQ hcard χR e he
  have hX1R_R : X1R ≤ R := X1R_le_R
  exact ⟨((MulEquiv.subgroupCongr (X1R_subgroupOf)).symm.trans
    (Subgroup.subgroupOfEquivOfLe hX1R_R)).trans eX⟩

end CFSG.Quasithin.F112R.St84.AutJ2Model
