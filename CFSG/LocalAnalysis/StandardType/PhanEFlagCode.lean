module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagCodeData

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

variable {K f}

theorem PhanCode.connected_sys (code : PhanCode) : (code.sys K).Connected := by
  induction code with
  | exchA1A1 =>
      exact q2cFCo_prod_connected (flagSys_connected K 1) (flagSys_connected K 1)
  | exchA2A1 =>
      exact q2cFCo_prod_connected (flagSys_connected K 2) (flagSys_connected K 1)
  | prod c c' ihc ihc' => exact q2cFCo_prod_connected ihc ihc'
  | _ => exact flagSys_connected K _

theorem PhanCode.cdist_le_diam (code : PhanCode) (x y : code.Ω K) :
    cdist (code.sys K) x y ≤ code.diam := by
  revert x y
  induction code with
  | exchA1A1 =>
      intro x y
      have h := cdist_prod (flagSys_connected K 1) (flagSys_connected K 1) x y
      have h1 : cdist (flagSys K 1) x.1 y.1 ≤ 1 := by
        simpa using cdist_flagSys_le K 1 x.1 y.1
      have h2 : cdist (flagSys K 1) x.2 y.2 ≤ 1 := by
        simpa using cdist_flagSys_le K 1 x.2 y.2
      have hb : cdist (flagSys K 1) x.1 y.1 + cdist (flagSys K 1) x.2 y.2 ≤ 2 := by omega
      exact le_trans (le_of_eq h) hb
  | exchA2A1 =>
      intro x y
      have h := cdist_prod (flagSys_connected K 2) (flagSys_connected K 1) x y
      have h1 : cdist (flagSys K 2) x.1 y.1 ≤ 3 := by
        simpa using cdist_flagSys_le K 2 x.1 y.1
      have h2 : cdist (flagSys K 1) x.2 y.2 ≤ 1 := by
        simpa using cdist_flagSys_le K 1 x.2 y.2
      have hb : cdist (flagSys K 2) x.1 y.1 + cdist (flagSys K 1) x.2 y.2 ≤ 4 := by omega
      exact le_trans (le_of_eq h) hb
  | prod c c' ihc ihc' =>
      intro x y
      have h := cdist_prod (PhanCode.connected_sys c) (PhanCode.connected_sys c') x y
      have h1 : cdist (c.sys K) x.1 y.1 ≤ c.diam := ihc x.1 y.1
      have h2 : cdist (c'.sys K) x.2 y.2 ≤ c'.diam := ihc' x.2 y.2
      have hb : cdist (c.sys K) x.1 y.1 + cdist (c'.sys K) x.2 y.2 ≤ c.diam + c'.diam := by
        omega
      exact le_trans (le_of_eq h) hb
  | _ =>
      intro x y
      exact le_trans (cdist_flagSys_le K _ x y) (by decide)

theorem PhanCode.exists_cdist_eq_diam (code : PhanCode) :
    ∃ x y : code.Ω K, cdist (code.sys K) x y = code.diam := by
  induction code with
  | exchA1A1 => exact q2cFCo_exists_cdist_eq_diam_exchA1A1 (K := K)
  | exchA2A1 => exact q2cFCo_exists_cdist_eq_diam_exchA2A1 (K := K)
  | prod c c' ihc ihc' =>
      obtain ⟨x₁, y₁, h₁⟩ := ihc
      obtain ⟨x₂, y₂, h₂⟩ := ihc'
      refine ⟨(x₁, x₂), (y₁, y₂), ?_⟩
      have h := cdist_prod (PhanCode.connected_sys c) (PhanCode.connected_sys c') (x₁, x₂)
        (y₁, y₂)
      exact h.trans (by rw [h₁, h₂]; rfl)
  | _ =>
      obtain ⟨x, y, h⟩ := q2cFCo_exists_cdist_eq_diam_flag (K := K) _
      exact ⟨x, y, h.trans (by decide)⟩

theorem PhanCode.R0_nonempty (code : PhanCode) : (code.R0 K).Nonempty := by
  induction code with
  | a1far => exact ⟨stdFlag K 2, stdFlag_mem_refSet q2cFCo_isCut_012⟩
  | a1moved => exact ⟨stdFlag K 2, stdFlag_mem_refSet q2cFCo_isCut_02⟩
  | a2chamber => exact ⟨stdFlag K 3, stdFlag_mem_refSet q2cFCo_isCut_0123⟩
  | a2panel => exact ⟨stdFlag K 3, stdFlag_mem_refSet q2cFCo_isCut_013⟩
  | a2coll => exact ⟨stdFlag K 3, stdFlag_mem_refSet q2cFCo_isCut_03⟩
  | a2pol => exact ⟨stdFlag K 3, stdFlag_mem_refSet q2cFCo_isCut_03⟩
  | a3_1111 => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_01234⟩
  | a3_211 => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_0234⟩
  | a3_121 => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_0134⟩
  | a3_22p => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_024⟩
  | a3_22x => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_024⟩
  | a3_13c => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_014⟩
  | a3_13p => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_014⟩
  | a3_4c => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_04⟩
  | a3_4p => exact ⟨stdFlag K 4, stdFlag_mem_refSet q2cFCo_isCut_04⟩
  | exchA1A1 => exact ⟨(stdFlag K 2, stdFlag K 2), Set.mem_univ _⟩
  | exchA2A1 => exact ⟨(stdFlag K 3, stdFlag K 2), stdFlag_mem_refSet q2cFCo_isCut_013⟩
  | prod c c' ihc ihc' =>
      obtain ⟨x, hx⟩ := ihc
      obtain ⟨y, hy⟩ := ihc'
      exact ⟨(x, y), Set.mem_prod.mpr ⟨hx, hy⟩⟩

theorem PhanCode.exists_diam_psi (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (code : PhanCode) :
    ∃ x ∈ code.R0 K, ∀ y ∈ code.R0 K, ∀ z ∈ code.R0 K,
      cdist (code.sys K) y z ≤ cdist (code.sys K) x (code.psi K f hK x) := by
  induction code with
  | a1far =>
      exact q2cFCo_exists_diam_psi_block hK hq 1 (by norm_num) [0, 1, 2] q2cFCo_isCut_012 []
  | a1moved =>
      exact q2cFCo_exists_diam_psi_block hK hq 1 (by norm_num) [0, 2] q2cFCo_isCut_02 [false]
  | a2chamber =>
      exact q2cFCo_exists_diam_psi_block hK hq 2 (by norm_num) [0, 1, 2, 3] q2cFCo_isCut_0123 []
  | a2panel =>
      exact q2cFCo_exists_diam_psi_block hK hq 2 (by norm_num) [0, 1, 3] q2cFCo_isCut_013 []
  | a2coll =>
      exact q2cFCo_exists_diam_psi_block hK hq 2 (by norm_num) [0, 3] q2cFCo_isCut_03 [false]
  | a2pol =>
      exact q2cFCo_exists_diam_psi_block hK hq 2 (by norm_num) [0, 3] q2cFCo_isCut_03 [true]
  | a3_1111 =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 1, 2, 3, 4]
        q2cFCo_isCut_01234 []
  | a3_211 =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 2, 3, 4] q2cFCo_isCut_0234 []
  | a3_121 =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 1, 3, 4] q2cFCo_isCut_0134 []
  | a3_22p =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 2, 4] q2cFCo_isCut_024 []
  | a3_22x =>
      obtain ⟨x, hx, hxlong⟩ := exists_opp_flagPsiX (K := K) (f := f) hK
      refine ⟨x, hx, fun y hy z hz => ?_⟩
      calc cdist (flagSys K 3) y z
          = (symCox 3).length (flagδ 3 y z) := (length_flagδ_eq_cdist 3 y z).symm
        _ ≤ (symCox 3).length (longest (symCox 3) (cutTypes 3 [0, 2, 4])) :=
            (isLongest_longest (cutTypes 3 [0, 2, 4])).2 _
              (flagδ_mem_parabolic_of_mem_refSet q2cFCo_isCut_024 hy hz)
        _ = cdist (flagSys K 3) x (flagPsiX hK x) := by
            rw [← hxlong, length_flagδ_eq_cdist]
  | a3_13c =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 1, 4] q2cFCo_isCut_014 []
  | a3_13p =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 1, 4] q2cFCo_isCut_014
        [false, true]
  | a3_4c =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 4] q2cFCo_isCut_04 [false]
  | a3_4p =>
      exact q2cFCo_exists_diam_psi_block hK hq 3 (by norm_num) [0, 4] q2cFCo_isCut_04 [true]
  | exchA1A1 =>
      obtain ⟨F, hF⟩ := exists_opp (stdFlag K 2)
      have hFne : F ≠ stdFlag K 2 := by
        intro h
        have h1 : Vsub (K := K) 2 1 ⊓ F.E 1 = ⊥ := hF 1 (by norm_num)
        rw [h] at h1
        have h1' : Vsub (K := K) 2 1 = ⊥ := by
          have hh : Vsub (K := K) 2 1 ⊓ Vsub (K := K) 2 1 = ⊥ := h1
          rwa [inf_idem] at hh
        have h2 := finrank_Vsub (K := K) (n := 2) (c := 1) (by norm_num)
        rw [h1', finrank_bot] at h2
        omega
      refine ⟨(stdFlag K 2, F), Set.mem_univ _, fun y _ z _ => ?_⟩
      have hbound : cdist ((flagSys K 1).prod (flagSys K 1)) y z ≤ 2 :=
        PhanCode.cdist_le_diam (K := K) PhanCode.exchA1A1 y z
      have hxval : cdist ((flagSys K 1).prod (flagSys K 1)) (stdFlag K 2, F)
          (psiA1A1 hK (stdFlag K 2, F)) = 2 := by
        rw [cdist_prod (flagSys_connected K 1) (flagSys_connected K 1)]
        have h1 : cdist (flagSys K 1) (stdFlag K 2, F).1
            (psiA1A1 hK (stdFlag K 2, F)).1 = 1 := by
          show cdist (flagSys K 1) (stdFlag K 2) (flagSg hK F) = 1
          refine q2cFCo_cdist_eq_one_of_adj ?_ (q2cFCo_adj_flagSys_one _ _ 0)
          intro h
          have h' := congrArg (flagSg hK) h
          rw [q2cFCo_flagSg_stdFlag hK 2, flagSg_flagSg hK F] at h'
          exact hFne h'.symm
        have h2 : cdist (flagSys K 1) (stdFlag K 2, F).2
            (psiA1A1 hK (stdFlag K 2, F)).2 = 1 := by
          show cdist (flagSys K 1) F (flagSg hK (stdFlag K 2)) = 1
          refine q2cFCo_cdist_eq_one_of_adj ?_ (q2cFCo_adj_flagSys_one _ _ 0)
          rw [q2cFCo_flagSg_stdFlag hK 2]
          exact hFne
        rw [h1, h2]
      exact le_trans hbound (le_of_eq hxval.symm)
  | exchA2A1 =>
      obtain ⟨F, hF⟩ := exists_opp (stdFlag K 2)
      have hFne : F.E 1 ≠ Vsub (K := K) 2 1 := by
        intro h
        have h1 : Vsub (K := K) 2 1 ⊓ F.E 1 = ⊥ := hF 1 (by norm_num)
        rw [h] at h1
        have h1' : Vsub (K := K) 2 1 = ⊥ := by
          have hh : Vsub (K := K) 2 1 ⊓ Vsub (K := K) 2 1 = ⊥ := h1
          rwa [inf_idem] at hh
        have h2 := finrank_Vsub (K := K) (n := 2) (c := 1) (by norm_num)
        rw [h1', finrank_bot] at h2
        omega
      have hxmem : (stdFlag K 3) ∈ refSet K 3 [0, 1, 3] :=
        stdFlag_mem_refSet q2cFCo_isCut_013
      refine ⟨(stdFlag K 3, F), hxmem, fun y hy z hz => ?_⟩
      have hbound : cdist ((flagSys K 2).prod (flagSys K 1)) y z ≤ 2 := by
        have h := cdist_prod (flagSys_connected K 2) (flagSys_connected K 1) y z
        have h1 : cdist (flagSys K 2) y.1 z.1 ≤ 1 :=
          q2cFCo_cdist_le_one_of_adj (q2cFCo_adj_refSet_013 y.1 z.1 hy hz)
        have h2 : cdist (flagSys K 1) y.2 z.2 ≤ 1 :=
          q2cFCo_cdist_le_one_of_adj (q2cFCo_adj_flagSys_one y.2 z.2 0)
        have hb : cdist (flagSys K 2) y.1 z.1 + cdist (flagSys K 1) y.2 z.2 ≤ 2 := by omega
        exact le_trans (le_of_eq h) hb
      have hxval : cdist ((flagSys K 2).prod (flagSys K 1)) (stdFlag K 3, F)
          (psiA2A1 hK (stdFlag K 3, F)) = 2 := by
        have hpsi : psiA2A1 hK (stdFlag K 3, F) =
            Classical.choose (exists_psiA2A1 (K := K) (f := f) (c := (stdFlag K 3, F))
              hK hxmem) := by
          unfold psiA2A1
          rw [dif_pos hxmem]
        have hspec := Classical.choose_spec (exists_psiA2A1 (K := K) (f := f)
          (c := (stdFlag K 3, F)) hK hxmem)
        rw [cdist_prod (flagSys_connected K 2) (flagSys_connected K 1)]
        have hne1 : (stdFlag K 3) ≠ (psiA2A1 hK (stdFlag K 3, F)).1 := by
          intro heq
          have h2 : (psiA2A1 hK (stdFlag K 3, F)).1.E 2 = Vsub (K := K) 3 2 := by
            rw [← heq]
            rfl
          rw [hpsi, hspec.2.1] at h2
          exact q2cFCo_Vsub3_ne_sup (F.E 1) (F.dim 1 (by norm_num)) hFne h2.symm
        have h1 : cdist (flagSys K 2) (stdFlag K 3, F).1
            (psiA2A1 hK (stdFlag K 3, F)).1 = 1 := by
          show cdist (flagSys K 2) (stdFlag K 3) (psiA2A1 hK (stdFlag K 3, F)).1 = 1
          exact q2cFCo_cdist_eq_one_of_adj hne1
            (q2cFCo_adj_refSet_013 (stdFlag K 3) (psiA2A1 hK (stdFlag K 3, F)).1 hxmem
              (by rw [hpsi]; exact hspec.1))
        have hz2 : (psiA2A1 hK (stdFlag K 3, F)).2.E 1 = Vsub (K := K) 2 1 := by
          have hle : (psiA2A1 hK (stdFlag K 3, F)).2.E 1 ≤ Vsub (K := K) 2 1 := by
            rw [hpsi, hspec.2.2]
            exact q2cFCo_span_jShift21Inv_le
          refine Submodule.eq_of_le_of_finrank_eq hle ?_
          rw [(psiA2A1 hK (stdFlag K 3, F)).2.dim 1 (by norm_num),
            finrank_Vsub (K := K) (n := 2) (c := 1) (by norm_num)]
        have h2 : cdist (flagSys K 1) (stdFlag K 3, F).2
            (psiA2A1 hK (stdFlag K 3, F)).2 = 1 := by
          show cdist (flagSys K 1) F (psiA2A1 hK (stdFlag K 3, F)).2 = 1
          refine q2cFCo_cdist_eq_one_of_adj ?_ (q2cFCo_adj_flagSys_one _ _ 0)
          intro heq
          apply hFne
          rw [heq, hz2]
        rw [h1, h2]
      exact le_trans hbound (le_of_eq hxval.symm)
  | prod c c' ihc ihc' =>
      obtain ⟨x₁, hx₁, hx₁max⟩ := ihc
      obtain ⟨x₂, hx₂, hx₂max⟩ := ihc'
      refine ⟨(x₁, x₂), Set.mem_prod.mpr ⟨hx₁, hx₂⟩, fun y hy z hz => ?_⟩
      have h := cdist_prod (PhanCode.connected_sys c) (PhanCode.connected_sys c') y z
      have hx := cdist_prod (PhanCode.connected_sys c) (PhanCode.connected_sys c') (x₁, x₂)
        (Prod.map (c.psi K f hK) (c'.psi K f hK) (x₁, x₂))
      have h1 := hx₁max y.1 (Set.mem_prod.mp hy).1 z.1 (Set.mem_prod.mp hz).1
      have h2 := hx₂max y.2 (Set.mem_prod.mp hy).2 z.2 (Set.mem_prod.mp hz).2
      exact le_trans (le_of_eq h) (le_trans (add_le_add h1 h2) (le_of_eq hx.symm))

theorem PhanCode.intrSet_eq (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (code : PhanCode) :
    IntrSet (code.sys K) (code.R0 K) (code.psi K f hK) code.diam = code.set K f := by
  induction code with
  | a1far =>
      exact q2cFCo_intrSet_block hK hq 1 (by norm_num) [0, 1, 2] q2cFCo_isCut_012 [] 1
        (by norm_num)
  | a1moved =>
      exact q2cFCo_intrSet_block hK hq 1 (by norm_num) [0, 2] q2cFCo_isCut_02 [false] 1
        (by norm_num)
  | a2chamber =>
      exact q2cFCo_intrSet_block hK hq 2 (by norm_num) [0, 1, 2, 3] q2cFCo_isCut_0123 [] 3
        (by norm_num)
  | a2panel =>
      exact q2cFCo_intrSet_block hK hq 2 (by norm_num) [0, 1, 3] q2cFCo_isCut_013 [] 3
        (by norm_num)
  | a2coll =>
      exact q2cFCo_intrSet_block hK hq 2 (by norm_num) [0, 3] q2cFCo_isCut_03 [false] 3
        (by norm_num)
  | a2pol =>
      exact q2cFCo_intrSet_block hK hq 2 (by norm_num) [0, 3] q2cFCo_isCut_03 [true] 3
        (by norm_num)
  | a3_1111 =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 1, 2, 3, 4] q2cFCo_isCut_01234 [] 6
        (by norm_num)
  | a3_211 =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 2, 3, 4] q2cFCo_isCut_0234 [] 6
        (by norm_num)
  | a3_121 =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 1, 3, 4] q2cFCo_isCut_0134 [] 6
        (by norm_num)
  | a3_22p =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 2, 4] q2cFCo_isCut_024 [] 6
        (by norm_num)
  | a3_22x => exact intrSet_flagSys_eq_set22x (K := K) (f := f) hK
  | a3_13c =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 1, 4] q2cFCo_isCut_014 [] 6
        (by norm_num)
  | a3_13p =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 1, 4] q2cFCo_isCut_014 [false, true] 6
        (by norm_num)
  | a3_4c =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 4] q2cFCo_isCut_04 [false] 6
        (by norm_num)
  | a3_4p =>
      exact q2cFCo_intrSet_block hK hq 3 (by norm_num) [0, 4] q2cFCo_isCut_04 [true] 6
        (by norm_num)
  | exchA1A1 => exact intrSet_exchA1A1 (K := K) (f := f) hK
  | exchA2A1 => exact intrSet_exchA2A1 (K := K) (f := f) hK
  | prod c c' ihc ihc' =>
      have h := intrSet_prod (X := c.sys K) (Y := c'.sys K) (R₁ := c.R0 K) (R₂ := c'.R0 K)
        (ψ₁ := c.psi K f hK) (ψ₂ := c'.psi K f hK) (D₁ := c.diam) (D₂ := c'.diam)
        (PhanCode.connected_sys (K := K) c) (PhanCode.connected_sys (K := K) c')
        (PhanCode.R0_nonempty (K := K) c) (PhanCode.R0_nonempty (K := K) c')
        (fun x y => PhanCode.cdist_le_diam (K := K) c x y)
        (fun x y => PhanCode.cdist_le_diam (K := K) c' x y)
      have hgoal : IntrSet (PhanCode.sys K (PhanCode.prod c c'))
          (PhanCode.R0 K (PhanCode.prod c c')) (PhanCode.psi K f hK (PhanCode.prod c c'))
          (PhanCode.diam (PhanCode.prod c c')) =
          IntrSet (c.sys K) (c.R0 K) (c.psi K f hK) c.diam ×ˢ
            IntrSet (c'.sys K) (c'.R0 K) (c'.psi K f hK) c'.diam := h
      exact hgoal.trans (by
        show IntrSet (c.sys K) (c.R0 K) (c.psi K f hK) c.diam ×ˢ
            IntrSet (c'.sys K) (c'.R0 K) (c'.psi K f hK) c'.diam =
            c.set K f ×ˢ c'.set K f
        rw [ihc, ihc'])

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
