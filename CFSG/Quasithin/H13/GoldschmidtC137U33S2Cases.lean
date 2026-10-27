module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Ppt

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

theorem bgen_sq (j : ℕ) : bgen j * bgen j = 1 := by
  refine eq_of_code ?_
  rw [matCode_mulG]
  by_cases h3 : j < 4
  · rw [matCode_bgen h3]
    interval_cases j
    all_goals first
      | exact (by decide +kernel : mmul (bcode _) (bcode _) = idMat).trans matCode_one.symm
  · have : bgen j = zTauG := by
      simp only [bgen]
      split_ifs <;> first | rfl | omega
    rw [this]
    show mmul (matCode zTau) (matCode zTau) = _
    rw [matCode_zTau]
    exact code_facts.2.1.trans matCode_one.symm

theorem bgen_inv (j : ℕ) : (bgen j)⁻¹ = bgen j := inv_eq_of_mul_eq_one_right (bgen_sq j)

theorem wd_single (j : ℕ) : wd [j] = bgen j := by
  simp [wd]

theorem wd_cons (j : ℕ) (w : List ℕ) : wd (j :: w) = bgen j * wd w := by
  have : (j :: w) = [j] ++ w := rfl
  rw [this, wd_append, wd_single]

theorem wd_reverse (w : List ℕ) : wd w.reverse = (wd w)⁻¹ := by
  induction w with
  | nil => simp [wd]
  | cons j w ih =>
    rw [List.reverse_cons, wd_append, ih, wd_single, wd_cons, mul_inv_rev, bgen_inv]

theorem wd0_eq : wd [0] = sEltG 1 := by
  refine eq_of_code ?_
  rw [matCode_wd (by decide), matCode_sEltG (by norm_num)]
  decide +kernel

theorem wd2_eq : wd [2] = sEltG 16 := by
  refine eq_of_code ?_
  rw [matCode_wd (by decide), matCode_sEltG (by norm_num)]
  decide +kernel

theorem wdW_eq : wd [1, 0, 2, 0, 1] = sEltG 32 := by
  refine eq_of_code ?_
  rw [matCode_wd (by decide), matCode_sEltG (by norm_num)]
  decide +kernel

theorem wdb_eq : wd [1, 3, 1, 3] = b₀ := by
  refine eq_of_code ?_
  rw [matCode_wd (by decide), matCode_b₀]
  decide +kernel

theorem eq_top_of_cert (H : Subgroup Gam) (hS : sSubG ≤ H) (hb : b₀ ∈ H)
    (hch : ∀ c ∈ omegaL, ∃ h ∈ H, act h 8 = c) : H = ⊤ := by
  refine top_unique fun x _ => ?_
  have h8 : isPt 8 = true := by decide
  have hlt : (8 : ℕ) ∈ o0Codes := by decide
  obtain ⟨h, hh, hhx⟩ := hch (act x 8)
    (isPt_iff_mem _ (mact_mem_o0Codes x.2 hlt) (isPt_act x (by norm_num) h8))
  have hp : h⁻¹ * x ∈ Ppt := by
    rw [mem_Ppt, act_mul _ _ (by norm_num), ← hhx, act_inv_act _ (by norm_num)]
  have hT : Tset (h⁻¹ * x) := mem_Ppt_iff.1 hp
  have hle : h⁻¹ * x ∈ H := by
    rcases hT with hT | ⟨s₁, hs₁, s₂, hs₂, hq⟩
    · exact hS hT
    · rw [hq]
      exact mul_mem (mul_mem (hS hs₁) hb) (hS hs₂)
  have : x = h * (h⁻¹ * x) := by group
  rw [this]
  exact mul_mem hh hle

@[expose] def certOk (gw : List ℕ) (cert : List ℕ × List (ℕ × ℕ × ℕ)) : Bool :=
  cert.1.all (fun j => decide (j < 5)) &&
    gcode [matT01, matX, matW, wcode gw, wcode gw.reverse] cert.1 == bCode &&
    chainCovers [matT01, matX, matW, wcode gw, wcode gw.reverse] cert.2 omegaL

@[expose] def caseOk (gw : List ℕ) (cert : List ℕ × List (ℕ × ℕ × ℕ)) : Bool :=
  (mact (wcode gw) 8 == 8) || (ell0.all fun c => ell0.contains (mact (wcode gw) c)) ||
    certOk gw cert

theorem codes_gens (gw : List ℕ) (hgw : ∀ j ∈ gw, j < 4) :
    ([wd [0], wd [2], wd [1, 0, 2, 0, 1], wd gw, wd gw.reverse].map fun x => matCode x.1) =
      [matT01, matX, matW, wcode gw, wcode gw.reverse] := by
  have hr : ∀ j ∈ gw.reverse, j < 4 := fun j hj => hgw j (List.mem_reverse.1 hj)
  simp only [List.map_cons, List.map_nil, matCode_wd hgw, matCode_wd hr,
    matCode_wd (by decide : ∀ j ∈ [0], j < 4), matCode_wd (by decide : ∀ j ∈ [2], j < 4),
    matCode_wd (by decide : ∀ j ∈ [1, 0, 2, 0, 1], j < 4)]
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ (congrArg₂ _ ?_ rfl))
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem case_sound (gw : List ℕ) (hgw : ∀ j ∈ gw, j < 4) (cert : List ℕ × List (ℕ × ℕ × ℕ))
    (h : caseOk gw cert = true) :
    wd gw ∈ Ppt ∨ wd gw ∈ Pline ∨ ∀ H : Subgroup Gam, sSubG ≤ H → wd gw ∈ H → H = ⊤ := by
  unfold caseOk at h
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at h
  rcases h with (h | h) | h
  · refine Or.inl (mem_Ppt.2 ?_)
    unfold act
    rw [matCode_wd hgw]
    exact h
  · refine Or.inr (Or.inl fun c hc => ?_)
    unfold act
    rw [matCode_wd hgw]
    exact h c hc
  · refine Or.inr (Or.inr fun H hS hg => ?_)
    unfold certOk at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlt, hb⟩, hch⟩ := h
    have hr : ∀ j ∈ gw.reverse, j < 4 := fun j hj => hgw j (List.mem_reverse.1 hj)
    have hgl : ∀ x ∈ [wd [0], wd [2], wd [1, 0, 2, 0, 1], wd gw, wd gw.reverse], x ∈ H := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · rw [wd0_eq]; exact hS (mem_sSubG.2 ⟨1, by norm_num, rfl⟩)
      · rw [wd2_eq]; exact hS (mem_sSubG.2 ⟨16, by norm_num, rfl⟩)
      · rw [wdW_eq]; exact hS (mem_sSubG.2 ⟨32, by norm_num, rfl⟩)
      · exact hg
      · rw [wd_reverse]; exact inv_mem hg
    refine eq_top_of_cert H hS ?_ ?_
    · have hbw : ∀ j ∈ cert.1,
          j < ([wd [0], wd [2], wd [1, 0, 2, 0, 1], wd gw, wd gw.reverse] : List Gam).length :=
        fun j hj => by simpa using hlt j hj
      have : gprod [wd [0], wd [2], wd [1, 0, 2, 0, 1], wd gw, wd gw.reverse] cert.1 = b₀ :=
        eq_of_code (by rw [matCode_gprod _ _ hbw, codes_gens gw hgw, matCode_b₀]; exact hb)
      rw [← this]
      exact gprod_mem hgl cert.1
    · exact chainCovers_sound H _ hgl cert.2 omegaL (by rw [codes_gens gw hgw]; exact hch)

end CFSG.Quasithin.H13.U3.GC137.S2
