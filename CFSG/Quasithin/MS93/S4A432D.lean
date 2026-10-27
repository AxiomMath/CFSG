module

public import CFSG.Quasithin.MS93.S4A432S
public import CFSG.Quasithin.MS93.S4A432T
public import CFSG.Quasithin.MS93.S4A433

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Row

variable {F : Type} [Field F]

@[expose] noncomputable def rowLevi : Subgroup (SL3 F) :=
  (ptLevi : Subgroup (SL3 F)).comap transposeInv

theorem mem_rowLevi_iff {g : SL3 F} :
    g ∈ (rowLevi : Subgroup (SL3 F)) ↔ dualMat g *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  rw [rowLevi, Subgroup.mem_comap, mem_ptLevi_iff, coe_transposeInv]

theorem rowLevi_apply {g : SL3 F} (hg : g ∈ (rowLevi : Subgroup (SL3 F))) (j : Fin 3) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 j = (![1, 0, 0] : Fin 3 → F) j := by
  rw [mem_rowLevi_iff] at hg
  have h1 := congrArg (fun v => (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ v) hg
  simp only [dualMat, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← coe_mul_SL3,
    inv_mul_cancel, coe_one_SL3, Matrix.transpose_one, Matrix.one_mulVec] at h1
  have h2 := congrFun h1 j
  rw [h2]
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]

theorem rowLevi_mulVec_zero {g : SL3 F} (hg : g ∈ (rowLevi : Subgroup (SL3 F)))
    (u : Fin 3 → F) : (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) 0 = u 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, rowLevi_apply hg]
  simp

theorem rootElt_mem_rowLevi {i j : Fin 3} (hi : i ≠ 0) (hij : i ≠ j) (c : F) :
    rootElt i j c ∈ (rowLevi : Subgroup (SL3 F)) := by
  rw [mem_rowLevi_iff, dualMat_rootElt_mulVec hij]
  have : (![1, 0, 0] : Fin 3 → F) i = 0 := by
    fin_cases i <;> simp_all
  rw [this, mul_zero, Pi.single_zero, add_zero]

theorem exists_rowLevi_mulVec_eq_e1 {w : Fin 3 → F} (hw0 : w 0 = 0) (hw : w ≠ 0) :
    ∃ g ∈ (rowLevi : Subgroup (SL3 F)),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = ![0, 1, 0] := by
  have key : ∀ w : Fin 3 → F, w 0 = 0 → w 2 ≠ 0 → ∃ g ∈ (rowLevi : Subgroup (SL3 F)),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = ![0, 1, 0] := by
    intro w hw0 hw2
    refine ⟨rootElt 2 1 (-w 2) * rootElt 1 2 ((1 - w 1) / w 2),
      Subgroup.mul_mem _ (rootElt_mem_rowLevi (by decide) (by decide) _)
        (rootElt_mem_rowLevi (by decide) (by decide) _), ?_⟩
    rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, rootElt_mulVec (by decide),
      rootElt_mulVec (by decide)]
    funext k
    fin_cases k
    · simp [hw0]
    · simp
      field_simp
      ring
    · simp
      field_simp
      ring
  by_cases hw2 : w 2 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro hw1
      apply hw
      funext k
      fin_cases k <;> simp [hw0, hw1, hw2]
    set w' := ((rootElt 2 1 (w 1)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w with hw'
    have hw'0 : w' 0 = 0 := by
      rw [hw', rootElt_mulVec (by decide)]
      simp [hw0]
    have hw'2 : w' 2 ≠ 0 := by
      rw [hw', rootElt_mulVec (by decide)]
      simp [hw2, hw1]
    obtain ⟨g, hg, hgw⟩ := key w' hw'0 hw'2
    refine ⟨g * rootElt 2 1 (w 1)⁻¹,
      Subgroup.mul_mem _ hg (rootElt_mem_rowLevi (by decide) (by decide) _), ?_⟩
    rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, ← hw', hgw]
  · exact key w hw0 hw2

theorem rowLevi_invariant_cases (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ g ∈ (rowLevi : Subgroup (SL3 F)), ∀ v ∈ S,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ S)
    (hS0 : ∀ v ∈ S, v 0 = 0) : S = ⊥ ∨ ∀ v : Fin 3 → F, v 0 = 0 → v ∈ S := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwS, hw⟩ : ∃ w ∈ S, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hbot (eq_bot_iff.mpr fun v hv => (AddSubgroup.mem_bot).mpr (hcon v hv))
    obtain ⟨g, hg, hgw⟩ := exists_rowLevi_mulVec_eq_e1 (hS0 w hwS) hw
    have he1 : (![0, 1, 0] : Fin 3 → F) ∈ S := hgw ▸ hS g hg w hwS
    intro v hv0
    by_cases hv : v = 0
    · rw [hv]
      exact S.zero_mem
    · obtain ⟨g', hg', hg'v⟩ := exists_rowLevi_mulVec_eq_e1 hv0 hv
      have := hS g'⁻¹ (Subgroup.inv_mem _ hg') _ he1
      rwa [← hg'v, Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3,
        Matrix.one_mulVec] at this

theorem eq_zero_of_rowLevi_fix {w : Fin 3 → F} (hw0 : w 0 = 0)
    (hfix : ∀ g ∈ (rowLevi : Subgroup (SL3 F)),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w) : w = 0 := by
  have h1 := hfix _ (rootElt_mem_rowLevi (i := 1) (j := 2) (by decide) (by decide) 1)
  have h2 := hfix _ (rootElt_mem_rowLevi (i := 2) (j := 1) (by decide) (by decide) 1)
  rw [rootElt_mulVec (by decide)] at h1 h2
  have e1 := congrFun h1 1
  have e2 := congrFun h2 2
  simp at e1 e2
  funext k
  fin_cases k
  · exact hw0
  · simpa using e2
  · simpa using e1

end Row

section Move

variable {G : Type} [Group G] {K V C : Subgroup G} {F : Type} [Field F]

theorem exists_conjSL_dual {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hV : IsSumOfNaturalModulesVia K V C ψ true 1) {x : G} (hxV : x ∈ V) (hxC : x ∉ C) :
    ∃ s : SL3 F, ∀ k : ↥K, (toSL3 (conjSL s ψ) k ∈ (rowLevi : Subgroup (SL3 F)) ↔
      x⁻¹ * ((k : G) * x * (k : G)⁻¹) ∈ C) := by
  set N := NatSec.ofIsSum hV with hN
  set v₀ := N.coord x with hv₀
  have hv0 : v₀ ≠ 0 := by
    rw [hv₀, Ne, N.coord_eq_zero_iff hxV]
    exact hxC
  obtain ⟨g, hg⟩ := exists_mulVec_e0_eq hv0
  refine ⟨transposeInv g⁻¹, fun k => ?_⟩
  have hs : dualMat (transposeInv g⁻¹) = ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_transposeInv, transposeInv_transposeInv]
  have hs' : dualMat (transposeInv g⁻¹)⁻¹ = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← map_inv, inv_inv, ← coe_transposeInv, transposeInv_transposeInv]
  have hkx : (k : G) * x * (k : G)⁻¹ ∈ V := N.conj_mem k hxV
  rw [mem_rowLevi_iff, toSL3_conjSL, dualMat_mul, dualMat_mul, hs, hs', ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hg]
  have hc : N.coord ((k : G) * x * (k : G)⁻¹) = dualMat (toSL3 ψ k) *ᵥ v₀ := by
    rw [N.coord_conj k hxV, natAct_true]
  constructor
  · intro h
    have h1 : dualMat (toSL3 ψ k) *ᵥ v₀ = v₀ := by
      have e : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
          ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
        rw [← coe_mul_SL3, mul_inv_cancel, coe_one_SL3]
      have := congrArg (fun w => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) h
      simp only [Matrix.mulVec_mulVec] at this
      rw [← Matrix.mul_assoc, e, Matrix.one_mul] at this
      rw [this, hg]
    exact N.inv_mul_mem_of_coord_eq hxV hkx (by rw [hc, h1])
  · intro h
    have h1 : N.coord ((k : G) * x * (k : G)⁻¹) = v₀ := by
      have h0 := (N.coord_eq_zero_iff (V.mul_mem (V.inv_mem hxV) hkx)).mpr h
      rw [N.coord_mul (V.inv_mem hxV) hkx, N.coord_inv hxV, neg_add_eq_zero] at h0
      exact h0.symm
    rw [← hc, h1, ← hg, Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3,
      Matrix.one_mulVec]

end Move

section Plane

variable {F : Type} [Field F]

theorem eq_top_of_coordZero_lt {S : Submodule F (Fin 3 → F)} (hS : coordZero 0 ≤ S)
    {v : Fin 3 → F} (hvS : v ∈ S) (hv : v 0 ≠ 0) : S = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hw : w = (w 0 / v 0) • v + (w - (w 0 / v 0) • v) := by abel
  rw [hw]
  refine S.add_mem (S.smul_mem _ hvS) (hS ?_)
  show (w - (w 0 / v 0) • v) 0 = 0
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem card_coordZero_zero [Finite F] :
    Nat.card (coordZero 0 : Submodule F (Fin 3 → F)) = Nat.card F ^ 2 := by
  have e : (coordZero 0 : Submodule F (Fin 3 → F)) ≃ F × F :=
    { toFun := fun v => ((v : Fin 3 → F) 1, (v : Fin 3 → F) 2)
      invFun := fun p => ⟨![0, p.1, p.2], by simp [coordZero]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext k
        fin_cases k
        · exact v.2.symm
        · rfl
        · rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, sq]

end Plane

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem commutator_le_zloc_or_eq_usup {F : Type} [Field F] [Fintype F]
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hc : IsC1 h.le L (Fintype.card F) μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ))
    (hVQ : ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) μ)
    (hk : KindAt h.le L F true μ) {ν δ : Vtx (puAmalgam h.le)}
    (hμν : (puAmalgam h.le).treeGraph.Adj μ ν) (hνδ : (puAmalgam h.le).treeGraph.Adj ν δ)
    (hUμ : Usup (puAmalgam h.le) μ ν ≤ ZH (puAmalgam h.le) ν)
    (hUμq : Nat.card ↥(Usup (puAmalgam h.le) μ ν) = Fintype.card F ^ 2)
    (hUδ : Usup (puAmalgam h.le) δ ν ≤ ZH (puAmalgam h.le) ν)
    (hUδq : Nat.card ↥(Usup (puAmalgam h.le) δ ν) = Fintype.card F ^ 2)
    {x : (puAmalgam h.le).Universal} (hx : x ∈ ZM (puAmalgam h.le) δ)
    (hxB : x ∉ Bloc h.le L μ) :
    Subgroup.closure {r | ∃ y ∈ Qv (puAmalgam h.le) μ, ⁅x, y⁆ = r} ≤ Zloc h.le L μ ∨
      (Subgroup.closure {r | ∃ y ∈ Qv (puAmalgam h.le) μ, ⁅x, y⁆ = r} =
          Usup (puAmalgam h.le) μ ν ∧
        Usup (puAmalgam h.le) δ ν = Usup (puAmalgam h.le) μ ν) := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hνH : ¬ IsMVtx (puAmalgam h.le) ν := by
    rw [← isMVtx_iff_of_adj _ hμν]
    exact hμ
  have hδ : IsMVtx (puAmalgam h.le) δ := by
    by_contra hδ
    exact hνH ((isMVtx_iff_of_adj _ hνδ).mpr hδ)
  have hQs : Qv (puAmalgam h.le) μ ≤ stab _ μ := qv_le_stab _ μ
  have hVs : Vv (puAmalgam h.le) μ ≤ stab _ μ := (vv_le_qv h hb hμ).trans hQs
  have hTs : Qv (puAmalgam h.le) ν ≤ stab _ μ := qv_le_stab_of_adj _ hμν.symm
  have hVn := stab_le_normalizer_vv h μ
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) μ
  have hZs : ZM (puAmalgam h.le) μ ≤ stab _ μ := (zm_le_qv_self _ hμ hb0).trans hQs
  have hUn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hBn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Bloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) μ
  have hBV : Bloc h.le L μ ≤ Vv _ μ := bloc_le_vv h μ
  have hZB : ZM (puAmalgam h.le) μ ≤ Bloc h.le L μ := zm_le_bloc h hb hμ
  have hWc := zloc_le_centralizer_stab h hfull hμ
  have hWn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Zloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp hWc)
  have hZcQ : ZM (puAmalgam h.le) μ ≤ Subgroup.centralizer (Qv (puAmalgam h.le) μ : Set _) :=
    zm_le_centralizer_qv _ h20 hμ
  have hZνZ : ZH (puAmalgam h.le) ν ≤ ZM (puAmalgam h.le) μ := zh_le_zm _ hμν
  have hdμδ : (puAmalgam h.le).treeGraph.dist μ δ ≤ 2 := by
    have := dist_triangle (puAmalgam h.le) μ ν δ
    rw [dist_eq_one_of_adj _ hμν, dist_eq_one_of_adj _ hνδ] at this
    exact this
  have hxV : x ∈ Vv (puAmalgam h.le) μ := by
    have : Zv (puAmalgam h.le) δ ≤ Vv _ μ := zv_le_vv h hdμδ
    rw [zv_of_isMVtx _ hδ] at this
    exact this hx
  obtain ⟨ψ, hψs, hψ, hP⟩ := hk
  obtain ⟨-, -, -, -, -, -, -, hPiB, hPB, -, -⟩ := isC1_normal h hfull hb hμ hc
  have hK : ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ =
      ZM (puAmalgam h.le) μ := sup_eq_right.mpr hVQ
  have hPV : ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ ≤
      Vv _ μ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hμ)
  have hPBn : ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Bloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    (hPV.trans hVs).trans hBn
  have hVB := isSumOfNaturalModulesVia_transfer hP hPB hPiB le_rfl (sup_eq_left.mpr hBV) hVn hBn
    hPBn
  obtain ⟨s₀, hs₀⟩ := exists_conjSL_dual hVB hxV (fun h' => hxB h'.2)
  set ψ' := conjSL s₀ ψ with hψ'def
  have hψ's : Function.Surjective ψ' := conjSL_surjective hψs
  have hψ' := isSumOfNaturalModulesVia_conjSL hψ s₀
  have hF1 : ∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) →
      x⁻¹ * ((k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹) ∈
        ZM (puAmalgam h.le) μ := by
    intro k hk
    have h1 := ((hs₀ k).mp hk).2
    have h2 : x⁻¹ * ((k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹) ∈
        ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ := by
      refine Subgroup.mem_sup_left ?_
      have e : x⁻¹ * ((k : (puAmalgam h.le).Universal) * x *
          (k : (puAmalgam h.le).Universal)⁻¹) = ⁅x⁻¹, (k : (puAmalgam h.le).Universal)⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxV) k.2
    rw [← hK, ← hPiB]
    exact ⟨h2, h1⟩
  have hTrow : natImage ψ' (Qv (puAmalgam h.le) ν) ≤ (rowLevi : Subgroup (SL3 F)) := by
    intro g hg
    obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
    refine (hs₀ t).mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxV)
        ((Subgroup.mem_normalizer_iff.mp (hVn t.2) x).mp hxV)
    · have e : x⁻¹ * ((t : (puAmalgam h.le).Universal) * x *
          (t : (puAmalgam h.le).Universal)⁻¹) = ⁅x⁻¹, (t : (puAmalgam h.le).Universal)⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      have : ⁅x⁻¹, (t : (puAmalgam h.le).Universal)⁆ ∈ Usup (puAmalgam h.le) δ ν := by
        rw [Usup, zv_of_isMVtx _ hδ]
        exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hx) htT
      exact hZB (hZνZ (hUδ this))
  have hcommW : commN (natImage ψ' (Qv (puAmalgam h.le) ν)) ≤ coordZero 0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, v, rfl⟩
    show (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) 0 = 0
    rw [Pi.sub_apply, rowLevi_mulVec_zero (hTrow hg), sub_self]
  have hcardC : Nat.card ↥(commN (natImage ψ' (Qv (puAmalgam h.le) ν))) = Nat.card F ^ 2 := by
    rw [← card_commutator_eq hψ' hTs, ← usup_eq_commutator_uloc h hfull hμ hμν, hUμq,
      Nat.card_eq_fintype_card]
  have hfinZ : Finite ↥(coordZero 0 : Submodule F (Fin 3 → F)) := inferInstance
  have hcommEq : commN (natImage ψ' (Qv (puAmalgam h.le) ν)) = coordZero 0 := by
    apply le_antisymm hcommW
    have hle : ((commN (natImage ψ' (Qv (puAmalgam h.le) ν))).toAddSubgroup) ≤
        (coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup := hcommW
    have := AddSubgroup.eq_of_le_of_card_ge hle (by
      rw [show Nat.card ↥(coordZero 0 : Submodule F (Fin 3 → F)).toAddSubgroup =
        Nat.card ↥(coordZero 0 : Submodule F (Fin 3 → F)) from rfl, card_coordZero_zero,
        show Nat.card ↥(commN (natImage ψ' (Qv (puAmalgam h.le) ν))).toAddSubgroup =
          Nat.card ↥(commN (natImage ψ' (Qv (puAmalgam h.le) ν))) from rfl, hcardC])
    intro v hv
    have : v ∈ (commN (natImage ψ' (Qv (puAmalgam h.le) ν))).toAddSubgroup := by
      rw [this]
      exact hv
    exact this
  have hfixW : fixN (natImage ψ' (Qv (puAmalgam h.le) ν)) = coordZero 0 := by
    have hW : commN (natImage ψ' (Qv (puAmalgam h.le) ν)) ≤ fixN (natImage ψ' (Qv _ ν)) := by
      intro y hy
      obtain ⟨u, rfl⟩ := natVec_surjective hψ' y
      have hu : (u : (puAmalgam h.le).Universal) ∈ ⁅Uloc h.le L μ, Qv (puAmalgam h.le) ν⁆ :=
        (mem_commutator_iff_natVec hψ' hTs u).mpr hy
      rw [← usup_eq_commutator_uloc h hfull hμ hμν] at hu
      have huC : (u : (puAmalgam h.le).Universal) ∈
          Subgroup.centralizer (Qv (puAmalgam h.le) ν : Set _) :=
        ((zh_inf_uloc h hfull hμ hμν).le ⟨hUμ hu, u.2⟩).2
      exact (mem_centralizer_iff_natVec hψ' hTs u).mp huC
    rw [hcommEq] at hW
    refine le_antisymm (fun v hv => ?_) hW
    by_contra hv0
    have htop := eq_top_of_coordZero_lt hW hv hv0
    have hbot : commN (natImage ψ' (Qv (puAmalgam h.le) ν)) = ⊥ := by
      rw [eq_bot_iff]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, hg, y, rfl⟩
      have : y ∈ fixN (natImage ψ' (Qv (puAmalgam h.le) ν)) := htop ▸ Submodule.mem_top
      rw [mem_fixN] at this
      rw [this g hg, sub_self]
      exact Submodule.zero_mem _
    rw [hbot] at hcardC
    have h1 : Nat.card ↥(⊥ : Submodule F (Fin 3 → F)) = 1 := by simp
    rw [h1] at hcardC
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  set R₀ : Set (puAmalgam h.le).Universal := {r | ∃ y ∈ Qv (puAmalgam h.le) μ, ⁅x, y⁆ = r}
    with hR₀
  set N := Subgroup.closure R₀ with hNdef
  have hNU : N ≤ Usup (puAmalgam h.le) δ ν := by
    rw [hNdef, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Usup, zv_of_isMVtx _ hδ]
    exact Subgroup.commutator_mem_commutator hx (qv_le_qv _ h20 hμ hμν hy)
  have hNZ : N ≤ ZH (puAmalgam h.le) ν := hNU.trans hUδ
  have hkN : ∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ r ∈ N, (k : (puAmalgam h.le).Universal) * r * (k : (puAmalgam h.le).Universal)⁻¹ ∈ N := by
    intro k hk r hr
    induction hr using Subgroup.closure_induction with
    | mem r hr =>
      obtain ⟨y, hy, rfl⟩ := hr
      set k₀ : (puAmalgam h.le).Universal := (k : (puAmalgam h.le).Universal)
      have hz := hF1 k hk
      have hy' : k₀ * y * k₀⁻¹ ∈ Qv (puAmalgam h.le) μ :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ μ k.2) y).mp hy
      have hzy : ⁅x⁻¹ * (k₀ * x * k₀⁻¹), k₀ * y * k₀⁻¹⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp (hZcQ hz) _ hy').symm
      have e : k₀ * ⁅x, y⁆ * k₀⁻¹ = ⁅x, k₀ * y * k₀⁻¹⁆ := by
        have e1 : k₀ * ⁅x, y⁆ * k₀⁻¹ = ⁅k₀ * x * k₀⁻¹, k₀ * y * k₀⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        have e2 : k₀ * x * k₀⁻¹ = x * (x⁻¹ * (k₀ * x * k₀⁻¹)) := by group
        rw [e1, e2]
        have e3 : ⁅x * (x⁻¹ * (k₀ * x * k₀⁻¹)), k₀ * y * k₀⁻¹⁆ =
            x * ⁅x⁻¹ * (k₀ * x * k₀⁻¹), k₀ * y * k₀⁻¹⁆ * x⁻¹ * ⁅x, k₀ * y * k₀⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e3, hzy, mul_one, mul_inv_cancel, one_mul]
      rw [e]
      exact Subgroup.subset_closure ⟨_, hy', rfl⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have : (k : (puAmalgam h.le).Universal) * (a * b) * (k : (puAmalgam h.le).Universal)⁻¹ =
          ((k : (puAmalgam h.le).Universal) * a * (k : (puAmalgam h.le).Universal)⁻¹) *
          ((k : (puAmalgam h.le).Universal) * b * (k : (puAmalgam h.le).Universal)⁻¹) := by group
      rw [this]
      exact N.mul_mem ha hb
    | inv a _ ha =>
      have : (k : (puAmalgam h.le).Universal) * a⁻¹ * (k : (puAmalgam h.le).Universal)⁻¹ =
          ((k : (puAmalgam h.le).Universal) * a * (k : (puAmalgam h.le).Universal)⁻¹)⁻¹ := by
        group
      rw [this]
      exact N.inv_mem ha
  have hcoordZ : ∀ u : ↥(Uloc h.le L μ), (u : (puAmalgam h.le).Universal) ∈ ZH (puAmalgam h.le) ν →
      natVec hψ' u ∈ coordZero 0 := by
    intro u hu
    rw [← hfixW]
    exact (mem_centralizer_iff_natVec hψ' hTs u).mp
      ((zh_inf_uloc h hfull hμ hμν).le ⟨hu, u.2⟩).2
  let Sc : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∃ u : ↥(Uloc h.le L μ), (u : (puAmalgam h.le).Universal) ∈ N ∧
        natVec hψ' u = v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', N.mul_mem hu hu', natVec_mul hψ' u u'⟩
      zero_mem' := ⟨1, N.one_mem, natVec_one hψ'⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, N.inv_mem hu, natVec_inv hψ' u⟩ }
  have hScinv : ∀ g ∈ (rowLevi : Subgroup (SL3 F)), ∀ v ∈ Sc,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Sc := by
    rintro g hg _ ⟨u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := toSL3_surjective hψ's g
    have hku : (k : (puAmalgam h.le).Universal) * u * (k : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L μ := (Subgroup.mem_normalizer_iff.mp (hUn k.2) _).mp u.2
    exact ⟨⟨_, hku⟩, hkN k hg _ hu, natVec_conj hψ' k u ⟨_, hku⟩ rfl⟩
  have hSc0 : ∀ v ∈ Sc, v 0 = 0 := by
    rintro _ ⟨u, hu, rfl⟩
    exact hcoordZ u (hNZ hu)
  rcases rowLevi_invariant_cases Sc hScinv hSc0 with hbot | hall
  ·
    left
    intro n hn
    have hnZ : n ∈ ((Uloc h.le L μ ⊔ Zloc h.le L μ : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
      rw [← zm_eq_uloc_sup_zloc h hfull hμ]
      exact hZνZ (hNZ hn)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (((uloc_le_zm h hfull hμ).trans hZs).trans hWn)] at hnZ
    obtain ⟨u, hu, w, hw, rfl⟩ := hnZ
    have hwZ : w ∈ ZH (puAmalgam h.le) ν := zloc_le_zh h hfull hμ hμν hw
    have huZ : u ∈ ZH (puAmalgam h.le) ν := by
      have := Subgroup.mul_mem _ (hNZ hn) (Subgroup.inv_mem _ hwZ)
      simpa using this
    have hfix : ∀ g ∈ (rowLevi : Subgroup (SL3 F)),
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ' ⟨u, hu⟩ = natVec hψ' ⟨u, hu⟩ := by
      intro g hg
      obtain ⟨k, rfl⟩ := toSL3_surjective hψ's g
      set k₀ : (puAmalgam h.le).Universal := (k : (puAmalgam h.le).Universal)
      have hku : k₀ * u * k₀⁻¹ ∈ Uloc h.le L μ := (Subgroup.mem_normalizer_iff.mp (hUn k.2) _).mp hu
      have hkw : k₀ * w * k₀⁻¹ = w := by
        rw [show k₀ * w = w * k₀ from Subgroup.mem_centralizer_iff.mp (hWc hw) k₀ k.2]
        group
      have hwu : w * u = u * w := (Subgroup.mem_centralizer_iff.mp
        (hWc.trans (Subgroup.centralizer_le ((uloc_le_zm h hfull hμ).trans hZs)) hw) u hu).symm
      have hmem : k₀ * u * k₀⁻¹ * u⁻¹ ∈ N := by
        have e : k₀ * u * k₀⁻¹ * u⁻¹ = (k₀ * (u * w) * k₀⁻¹) * (u * w)⁻¹ := by
          have e1 : k₀ * (u * w) * k₀⁻¹ = (k₀ * u * k₀⁻¹) * (k₀ * w * k₀⁻¹) := by group
          rw [e1, hkw, mul_inv_rev, show (k₀ * u * k₀⁻¹) * w * (w⁻¹ * u⁻¹) =
            k₀ * u * k₀⁻¹ * u⁻¹ by group]
        rw [e]
        exact N.mul_mem (hkN k hg _ hn) (N.inv_mem hn)
      have hmemU : k₀ * u * k₀⁻¹ * u⁻¹ ∈ Uloc h.le L μ :=
        Subgroup.mul_mem _ hku (Subgroup.inv_mem _ hu)
      have h0 : natVec hψ' ⟨_, hmemU⟩ ∈ Sc := ⟨⟨_, hmemU⟩, hmem, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at h0
      have e : (⟨_, hmemU⟩ : ↥(Uloc h.le L μ)) = ⟨_, hku⟩ * (⟨u, hu⟩ : ↥(Uloc h.le L μ))⁻¹ := rfl
      rw [e, natVec_mul, natVec_inv, natVec_conj hψ' k ⟨u, hu⟩ ⟨_, hku⟩ rfl,
        add_neg_eq_zero] at h0
      exact h0
    have h0 := eq_zero_of_rowLevi_fix (hcoordZ ⟨u, hu⟩ huZ) hfix
    have hu1 : (⟨u, hu⟩ : ↥(Uloc h.le L μ)) = 1 :=
      natVec_injective hψ' (h0.trans (natVec_one hψ').symm)
    have : u = 1 := congrArg Subtype.val hu1
    subst this
    simpa using hw
  ·
    right
    have hUN : Usup (puAmalgam h.le) μ ν ≤ N := by
      intro u hu
      have hU : Usup (puAmalgam h.le) μ ν ≤ Uloc h.le L μ := by
        rw [usup_eq_commutator_uloc h hfull hμ hμν]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hTs.trans hUn)
      obtain ⟨u', hu'N, hu'v⟩ := hall (natVec hψ' ⟨u, hU hu⟩) (hcoordZ ⟨u, hU hu⟩ (hUμ hu))
      have : u' = ⟨u, hU hu⟩ := natVec_injective hψ' hu'v
      rw [this] at hu'N
      exact hu'N
    have hfinδ : Finite ↥(Usup (puAmalgam h.le) δ ν) := by
      have := finite_qv _ h20 hνH
      exact Finite.of_injective _ (Subgroup.inclusion_injective ((hUδ.trans
        (zh_le_zm _ hνδ.symm)).trans ((zm_le_qv_self _ hδ hb0).trans
          (qv_le_qv _ h20 hδ hνδ.symm))))
    have hfinN : Finite ↥N := Finite.of_injective _ (Subgroup.inclusion_injective hNU)
    have h1 : N = Usup (puAmalgam h.le) δ ν :=
      Subgroup.eq_of_le_of_card_ge hNU (by
        rw [hUδq, ← hUμq]
        exact Subgroup.card_le_of_le hUN)
    have h2 : Usup (puAmalgam h.le) μ ν = N :=
      Subgroup.eq_of_le_of_card_ge hUN (by
        rw [h1, hUδq, hUμq])
    exact ⟨h2.symm, h1.symm.trans h2.symm⟩

end Vertex

end CFSG.Quasithin.MS93.S4A
