module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveOverlap
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveTree
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveRigidOverlap
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveRigidGram

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

theorem exists_isometry_of_markedIso {k : ℕ} {ε π : Bool}
    {W W' : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hW : IsFiveNondeg k ε W)
    (hdim : Module.finrank (ZMod 5) W = Module.finrank (ZMod 5) W')
    (h4 : 4 ≤ Module.finrank (ZMod 5) W)
    (θ : fiveReflectionGroupIn k ε π W ≃* fiveReflectionGroupIn k ε π W')
    (hθ : ∀ g : fiveReflectionGroupIn k ε π W,
      (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsIn k ε π W ↔
        (θ g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsIn k ε π W') :
    ∃ M : GL (Fin (k + 1)) (ZMod 5),
      (∀ x y, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
        ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y) ∧
      W.map (Matrix.toLin' (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) = W' ∧
      ∀ g : fiveReflectionGroupIn k ε π W,
        (θ g : GL (Fin (k + 1)) (ZMod 5)) = M * (g : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹ := by
  obtain ⟨b, p, hbmem, hbind, hppar, hptree, hbclos⟩ := exists_fiveTreeBasis hW h4
  let g : Fin (Module.finrank (ZMod 5) W) → fiveReflectionGroupIn k ε π W :=
    fun i => ⟨fiveReflOf k ε (b i), by rw [← hbclos]; exact Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hg_coe : ∀ i, (g i : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε (b i) := fun i => rfl
  have hmem : ∀ i, (θ (g i) : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsIn k ε π W' := by
    intro i
    have h1 : (g i : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsIn k ε π W := by
      refine ⟨b i, (hbmem i).1, (hbmem i).2.1, (hbmem i).2.2, fun x => ?_⟩
      exact fiveReflOf_mulVec k ε (b i) x
    exact (hθ (g i)).mp h1
  have hci : ∀ i, ∃ c, c ∈ W' ∧ fiveForm k ε c c ≠ 0 ∧
      (IsSquare (fiveForm k ε c c) ↔ π = true) ∧
      (θ (g i) : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε c := by
    intro i
    exact exists_fiveReflOf_of_mem_fiveReflectionsIn (hmem i)
  choose c hcU hcQ hcπ hcr using hci
  have hci' : ∀ i, ∃ c', c' ∈ W' ∧ fiveForm k ε c' c' = fiveForm k ε (b i) (b i) ∧
      (IsSquare (fiveForm k ε c' c') ↔ π = true) ∧
      fiveReflOf k ε c' = fiveReflOf k ε (c i) := by
    intro i
    obtain ⟨c', hc'U, hc'Q, hc'refl⟩ := exists_smul_mem_sq_eq (k := k) (ε := ε) (π := π)
      (hcU i) (hcQ i) (hcπ i) (hbmem i).2.1 (hbmem i).2.2
    exact ⟨c', hc'U, hc'Q,
      (show IsSquare (fiveForm k ε c' c') ↔ π = true by rw [hc'Q]; exact (hbmem i).2.2),
      hc'refl⟩
  choose c' hc'U hc'Q hc'π hc'refl using hci'
  have hc'Qne : ∀ i, fiveForm k ε (c' i) (c' i) ≠ 0 := by
    intro i h
    rw [hc'Q i] at h
    exact (hbmem i).2.1 h
  have hθc : ∀ i, (θ (g i) : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε (c' i) := by
    intro i; rw [hc'refl i, hcr i]
  have horder : ∀ i j, i ≠ j →
      orderOf (fiveReflOf k ε (c' i) * fiveReflOf k ε (c' j)) =
      orderOf (fiveReflOf k ε (b i) * fiveReflOf k ε (b j)) := by
    intro i j hij
    have h1 : (θ (g i * g j) : GL (Fin (k + 1)) (ZMod 5)) =
        fiveReflOf k ε (c' i) * fiveReflOf k ε (c' j) := by
      rw [map_mul, Subgroup.coe_mul, hθc i, hθc j]
    calc orderOf (fiveReflOf k ε (c' i) * fiveReflOf k ε (c' j))
        = orderOf ((θ (g i * g j) : fiveReflectionGroupIn k ε π W') :
            GL (Fin (k + 1)) (ZMod 5)) := by rw [h1]
      _ = orderOf (θ (g i * g j)) := (Subgroup.orderOf_coe _)
      _ = orderOf (g i * g j) := θ.orderOf_eq _
      _ = orderOf ((g i * g j : fiveReflectionGroupIn k ε π W) : GL (Fin (k + 1)) (ZMod 5)) :=
            (Subgroup.orderOf_coe _).symm
      _ = orderOf (fiveReflOf k ε (b i) * fiveReflOf k ε (b j)) := by
            rw [Subgroup.coe_mul, hg_coe i, hg_coe j]
  have hne_b : ∀ i j, i ≠ j → ∀ μ : ZMod 5, b j ≠ μ • b i := by
    intro i j hij μ h
    apply hbind.notMem_span j
    rw [h]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, by simpa [Set.mem_compl_iff] using hij, rfl⟩)
  have hne_c : ∀ i j, i ≠ j → ∀ μ : ZMod 5, c' j ≠ μ • c' i := by
    intro i j hij μ h
    by_cases hμ : μ = 0
    · subst hμ; rw [zero_smul] at h
      have h0 : fiveForm k ε (c' j) (c' j) = 0 := by
        rw [h]
        simp
      rw [hc'Q j] at h0
      exact (hbmem j).2.1 h0
    · have hr : fiveReflOf k ε (c' j) = fiveReflOf k ε (c' i) := by
        rw [h, fiveReflOf_smul k ε (c' i) hμ]
      have hg_eq : g j = g i := by
        apply θ.injective
        apply Subtype.ext
        rw [hθc j, hθc i, hr]
      have hrb : fiveReflOf k ε (b j) = fiveReflOf k ε (b i) := by
        have := congrArg (fun z : fiveReflectionGroupIn k ε π W =>
          (z : GL (Fin (k + 1)) (ZMod 5))) hg_eq
        simpa [hg_coe] using this
      obtain ⟨ν, hν⟩ := exists_smul_eq_of_fiveReflOf_eq (n := k) (ε := ε)
        (x := b i) (y := b j) (hbmem i).2.1 hrb.symm
      exact hne_b i j hij ν hν
  have hzero : ∀ i j, fiveForm k ε (c' i) (c' j) = 0 ↔ fiveForm k ε (b i) (b j) = 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hc'Q i]
    · exact (gram_data_of_orderOf_eq (k := k) (ε := ε) (π := π)
        (v := b i) (w := b j) (v' := c' i) (w' := c' j)
        (hbmem i).2.1 (hbmem i).2.2 (hbmem j).2.1 (hbmem j).2.2
        (hc'Qne i) (hc'π i) (hc'Qne j) (hc'π j)
        (hne_b i j hij) (hne_c i j hij) (hc'Q i).symm (hc'Q j).symm (horder i j hij)).1
  have hsq : ∀ i j, fiveForm k ε (c' i) (c' j) ^ 2 = fiveForm k ε (b i) (b j) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hc'Q i]
    · exact (gram_data_of_orderOf_eq (k := k) (ε := ε) (π := π)
        (v := b i) (w := b j) (v' := c' i) (w' := c' j)
        (hbmem i).2.1 (hbmem i).2.2 (hbmem j).2.1 (hbmem j).2.2
        (hc'Qne i) (hc'π i) (hc'Qne j) (hc'π j)
        (hne_b i j hij) (hne_c i j hij) (hc'Q i).symm (hc'Q j).symm (horder i j hij)).2
  obtain ⟨s, hs, hgram⟩ := exists_smul_c_of_gram (k := k) (ε := ε)
    (b := b) (c := c') (p := p) hc'Q hzero hsq hppar hptree
  let b' : Fin (Module.finrank (ZMod 5) W) → Fin (k + 1) → ZMod 5 := fun i => s i • c' i
  have hb'mem : ∀ i, b' i ∈ W' := fun i => Submodule.smul_mem _ _ (hc'U i)
  have hb'G : ∀ i j, fiveForm k ε (b' i) (b' j) = fiveForm k ε (b i) (b j) := hgram
  have hθb' : ∀ i, (θ (g i) : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε (b' i) := by
    intro i
    rw [hθc i]
    show fiveReflOf k ε (c' i) = fiveReflOf k ε (s i • c' i)
    rw [fiveReflOf_smul k ε (c' i) (by rcases hs i with h | h <;> rw [h] <;> decide)]
  obtain ⟨M, hMform, hMb, hMW⟩ := exists_isometry_of_gram (k := k) (ε := ε)
    (W := W) (W' := W') (d := Module.finrank (ZMod 5) W)
    hW b (fun i => (hbmem i).1) hbind rfl b' hb'mem hdim hb'G
  refine ⟨M, hMform, hMW, ?_⟩
  intro x
  have hx : (x : GL (Fin (k + 1)) (ZMod 5)) ∈
      Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)) := by
    rw [hbclos]; exact x.2
  have hmain : ∀ y (hy : y ∈ Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i))),
      (θ (⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W) :
          GL (Fin (k + 1)) (ZMod 5)) =
        M * ((⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W) :
          GL (Fin (k + 1)) (ZMod 5)) * M⁻¹ := by
    intro y hy
    refine Subgroup.closure_induction (p := fun z hz =>
      (θ (⟨z, hbclos ▸ hz⟩ : fiveReflectionGroupIn k ε π W) :
          GL (Fin (k + 1)) (ZMod 5)) =
        M * ((⟨z, hbclos ▸ hz⟩ : fiveReflectionGroupIn k ε π W) :
          GL (Fin (k + 1)) (ZMod 5)) * M⁻¹) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      have hsub : (⟨fiveReflOf k ε (b i),
          hbclos ▸ Subgroup.subset_closure (Set.mem_range_self i)⟩ :
            fiveReflectionGroupIn k ε π W) = g i := Subtype.ext rfl
      rw [hsub, hθb' i, hg_coe i, conj_fiveReflOf hMform (b i), hMb i]
    · show (θ (1 : fiveReflectionGroupIn k ε π W) : GL (Fin (k + 1)) (ZMod 5)) =
        M * (1 : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹
      simp
    · intro y z hy hz ihy ihz
      have hsub : (⟨y * z, hbclos ▸ mul_mem hy hz⟩ :
            fiveReflectionGroupIn k ε π W) =
          (⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W) *
            (⟨z, hbclos ▸ hz⟩ : fiveReflectionGroupIn k ε π W) := Subtype.ext rfl
      rw [hsub]
      show (θ ((⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W) *
            (⟨z, hbclos ▸ hz⟩ : fiveReflectionGroupIn k ε π W)) :
          GL (Fin (k + 1)) (ZMod 5)) =
        M * (((⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W) *
            (⟨z, hbclos ▸ hz⟩ : fiveReflectionGroupIn k ε π W)) :
          GL (Fin (k + 1)) (ZMod 5)) * M⁻¹
      rw [map_mul, Subgroup.coe_mul, ihy, ihz]
      group
    · intro y hy ihy
      have hsub : (⟨y⁻¹, hbclos ▸ inv_mem hy⟩ :
            fiveReflectionGroupIn k ε π W) =
          (⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W)⁻¹ := Subtype.ext rfl
      rw [hsub]
      show (θ ((⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W)⁻¹) :
            GL (Fin (k + 1)) (ZMod 5)) =
        M * (((⟨y, hbclos ▸ hy⟩ : fiveReflectionGroupIn k ε π W)⁻¹) :
          GL (Fin (k + 1)) (ZMod 5)) * M⁻¹
      rw [map_inv, Subgroup.coe_inv, ihy]
      group
  have hfin := hmain (x : GL (Fin (k + 1)) (ZMod 5)) hx
  simpa using hfin

variable {G G' : Type} [Group G] [Group G']

theorem exists_localIso_extension_five {D : Set G} {D' : Set G'} {k : ℕ} (hk : 4 ≤ k)
    {ε π : Bool} {u v : G} {u' v' : G'} (hu : u ∈ D) (hv : v ∈ commSet D u) (hu' : u' ∈ D')
    (hv' : v' ∈ commSet D' u') (cv : FiveLocalModel D v k ε π) (cv' : FiveLocalModel D' v' k ε π)
    (θ : LocalIso D u D' u') (hθv : θ.app v = v') :
    ∃ ψ : LocalIso D v D' v', ψ.app u = u' ∧
      ∀ y ∈ Subgroup.closure (commSet D u ∩ commSet D v), ψ.app y = θ.app y := by
  classical
  obtain ⟨a, ha0, _haπ, ha_eq⟩ := exists_axis_of_fiveLocalModel cv (mem_commSet_symm hu hv)
  obtain ⟨a', ha'0, _ha'π, ha'_eq⟩ :=
    exists_axis_of_fiveLocalModel cv' (mem_commSet_symm hu' hv')
  obtain ⟨e1, he1val, he1mem⟩ :=
    exists_iso_closure_inter_fiveOrth cv (mem_commSet_symm hu hv) ha0 ha_eq
  obtain ⟨e2, he2val, he2mem⟩ :=
    exists_iso_closure_inter_fiveOrth cv' (mem_commSet_symm hu' hv') ha'0 ha'_eq
  obtain ⟨eθ, heθval, heθmem⟩ := exists_iso_closure_inter_commSet θ hv hθv
  let W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    fiveOrth k ε (Submodule.span (ZMod 5) {a})
  let W' : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    fiveOrth k ε (Submodule.span (ZMod 5) {a'})
  let Θ : fiveReflectionGroupIn k ε π W ≃* fiveReflectionGroupIn k ε π W' :=
    e1.symm.trans (eθ.trans e2)
  have hΘmarked : ∀ g : fiveReflectionGroupIn k ε π W,
      (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsIn k ε π W ↔
        (Θ g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsIn k ε π W' := by
    intro g
    have h1 := (he1mem (e1.symm g)).symm
    have h3 := heθmem (e1.symm g)
    have h2 := he2mem (eθ (e1.symm g))
    simp only [MulEquiv.apply_symm_apply] at h1
    have hΘ : Θ g = e2 (eθ (e1.symm g)) := by
      simp only [Θ, MulEquiv.trans_apply]
    rw [hΘ]
    exact h1.trans (h3.trans h2)
  obtain ⟨M, hMform, hMW, hMconj⟩ := exists_isometry_of_markedIso
    (W := W) (W' := W') (isFiveNondeg_fiveOrth_span_singleton ha0)
    ((finrank_fiveOrth_span_singleton ha0).trans (finrank_fiveOrth_span_singleton ha'0).symm)
    (le_of_le_of_eq hk (finrank_fiveOrth_span_singleton ha0).symm) Θ hΘmarked
  have ha_ne : a ≠ 0 := fun h => ha0 (by rw [h]; simp [fiveForm])
  have hMa_orth : (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a ∈
      fiveOrth k ε W' := by
    rw [mem_fiveOrth]
    intro x hx
    have hx' : x ∈ W.map (Matrix.toLin' (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) := by
      rw [hMW]; exact hx
    rw [Submodule.mem_map] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    rw [Matrix.toLin'_apply, hMform a y]
    have h := (mem_fiveOrth (k := k) (ε := ε) (U := Submodule.span (ZMod 5) {a})).1 hy a
      (Submodule.mem_span_singleton_self a)
    exact (fiveForm_comm k ε a y).trans h
  have hMa_span : (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a ∈
      Submodule.span (ZMod 5) {a'} := by
    rw [← fiveOrth_fiveOrth_span_singleton ha'0]
    exact hMa_orth
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hMa_span
  have hc0 : c ≠ 0 := by
    intro hc0
    have hzero : (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = 0 := by
      rw [← hc, hc0, zero_smul]
    have haz : a = 0 := by
      have h := congrArg (fun z => ((M⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z) hzero
      simpa [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] using h
    exact ha_ne haz
  let AdM : fiveReflectionGroup k ε π ≃* fiveReflectionGroup k ε π :=
    conjMulEquiv_fiveReflectionGroup M hMform
  let ψ : LocalIso D v D' v' :=
    { toMulEquiv := cv.toMulEquiv.trans (AdM.trans cv'.toMulEquiv.symm)
      mem_iff := by
        intro y
        have h1 : (y : G) ∈ commSet D v ↔
            (cv.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π :=
          cv.mem_iff y
        have h2 : ((cv'.toMulEquiv.symm (AdM (cv.toMulEquiv y)) :
            Subgroup.closure (commSet D' v')) : G') ∈ commSet D' v' ↔
            (AdM (cv.toMulEquiv y) : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
          simpa only [MulEquiv.apply_symm_apply] using
            cv'.mem_iff (cv'.toMulEquiv.symm (AdM (cv.toMulEquiv y)))
        have h3 := conjMulEquiv_fiveReflectionGroup_mem_fiveReflections hMform
          (cv.toMulEquiv y)
        exact h1.trans (h3.symm.trans h2.symm) }
  refine ⟨ψ, ?_, ?_⟩
  · have hu_v : u ∈ commSet D v := mem_commSet_symm hu hv
    have huA : u ∈ Subgroup.closure (commSet D v) := Subgroup.subset_closure hu_v
    have hu'A : u' ∈ Subgroup.closure (commSet D' v') :=
      Subgroup.subset_closure (mem_commSet_symm hu' hv')
    rw [LocalIso.app_of_mem ψ huA]
    change ((cv'.toMulEquiv.symm (AdM (cv.toMulEquiv ⟨u, huA⟩)) :
      Subgroup.closure (commSet D' v')) : G') = u'
    have hcu : (cv.toMulEquiv ⟨u, huA⟩ : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε a :=
      ha_eq
    have hAdM : (AdM (cv.toMulEquiv ⟨u, huA⟩) : GL (Fin (k + 1)) (ZMod 5)) =
        fiveReflOf k ε a' := by
      rw [conjMulEquiv_fiveReflectionGroup_apply, hcu, conj_fiveReflOf hMform a, ← hc,
        fiveReflOf_smul k ε a' hc0]
    have hsymm : (cv'.toMulEquiv.symm (AdM (cv.toMulEquiv ⟨u, huA⟩)) :
        Subgroup.closure (commSet D' v')) = ⟨u', hu'A⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hAdM]
      exact ha'_eq.symm
    rw [show (cv'.toMulEquiv.symm (AdM (cv.toMulEquiv ⟨u, huA⟩)) :
      Subgroup.closure (commSet D' v')) = ⟨u', hu'A⟩ from hsymm]
  · intro y hy
    have hyA : y ∈ Subgroup.closure (commSet D v) :=
      Subgroup.closure_mono Set.inter_subset_right hy
    have hyB : y ∈ Subgroup.closure (commSet D u) :=
      Subgroup.closure_mono Set.inter_subset_left hy
    have hy'A : (θ.toMulEquiv ⟨y, hyB⟩ : G') ∈ Subgroup.closure (commSet D' v') := by
      have h := Subgroup.closure_mono Set.inter_subset_right (eθ ⟨y, hy⟩).2
      rw [heθval ⟨y, hy⟩] at h
      exact h
    have hy''A : (eθ ⟨y, hy⟩ : G') ∈ Subgroup.closure (commSet D' v') :=
      Subgroup.closure_mono Set.inter_subset_right (eθ ⟨y, hy⟩).2
    rw [LocalIso.app_of_mem ψ hyA, LocalIso.app_of_mem θ hyB]
    change ((cv'.toMulEquiv.symm (AdM (cv.toMulEquiv ⟨y, hyA⟩)) :
      Subgroup.closure (commSet D' v')) : G') = (θ.toMulEquiv ⟨y, hyB⟩ : G')
    have hkey : (M : GL (Fin (k + 1)) (ZMod 5)) *
        (cv.toMulEquiv ⟨y, hyA⟩ : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹ =
        (cv'.toMulEquiv ⟨(eθ ⟨y, hy⟩ : G'), hy''A⟩ : GL (Fin (k + 1)) (ZMod 5)) := by
      rw [← he1val ⟨y, hy⟩, ← hMconj (e1 ⟨y, hy⟩)]
      have hΘ : Θ (e1 ⟨y, hy⟩) = e2 (eθ ⟨y, hy⟩) := by
        simp only [Θ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hΘ, he2val]
    let Xg : fiveReflectionGroup k ε π :=
      ⟨(M : GL (Fin (k + 1)) (ZMod 5)) *
        (cv.toMulEquiv ⟨y, hyA⟩ : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹,
        conj_mem_fiveReflectionGroup hMform (cv.toMulEquiv ⟨y, hyA⟩).2⟩
    have hAdM_eq : AdM (cv.toMulEquiv ⟨y, hyA⟩) = Xg := rfl
    have hsymm : (cv'.toMulEquiv.symm Xg : Subgroup.closure (commSet D' v')) =
        ⟨(eθ ⟨y, hy⟩ : G'), hy''A⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      exact hkey
    rw [hAdM_eq]
    rw [show (cv'.toMulEquiv.symm Xg : Subgroup.closure (commSet D' v')) =
        ⟨(eθ ⟨y, hy⟩ : G'), hy''A⟩ from hsymm]
    exact heθval ⟨y, hy⟩

end CFSG.OddTranspositions.PartThree

end
