module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantor

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith invariant_of_generators)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {p : ℕ} [Fact p.Prime]

theorem det_eq_det_ofSubmodules {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {W B : Submodule (ZMod p) V} (hWB : IsCompl W B)
    (g : V ≃ₗ[ZMod p] V) (hB : ∀ u ∈ B, g u = u) (hmap : W.map (g : V →ₗ[ZMod p] V) = W) :
    LinearMap.det (g : V →ₗ[ZMod p] V) =
      LinearMap.det ((g.ofSubmodules W W hmap : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W) := by
  have key : (g : V →ₗ[ZMod p] V) = ((Submodule.prodEquivOfIsCompl W B hWB :
      (W × B) ≃ₗ[ZMod p] V) : (W × B) →ₗ[ZMod p] V) ∘ₗ
        (((g.ofSubmodules W W hmap : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W).prodMap LinearMap.id) ∘ₗ
          ((Submodule.prodEquivOfIsCompl W B hWB).symm : V →ₗ[ZMod p] (W × B)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨⟨w, b⟩, rfl⟩ : ∃ y, Submodule.prodEquivOfIsCompl W B hWB y = x :=
      ⟨_, LinearEquiv.apply_symm_apply _ x⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [LinearEquiv.symm_apply_apply]
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, Submodule.coe_prodEquivOfIsCompl',
      map_add, hB b b.2]
    rfl
  rw [key, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

variable {V : Type u} [AddCommGroup V] [Module (ZMod p) V]

theorem map_eq_of_mapsTo [Module.Finite (ZMod p) V] {W : Submodule (ZMod p) V}
    (g : V ≃ₗ[ZMod p] V) (hg : ∀ w ∈ W, g w ∈ W) : W.map (g : V →ₗ[ZMod p] V) = W :=
  Submodule.eq_of_le_of_finrank_eq (fun _ ⟨w, hw, h⟩ => by rw [← h]; exact hg w hw)
    (LinearEquiv.finrank_map_eq g W)

theorem kantor_blocks (hp : p ≠ 2) [Module.Finite (ZMod p) V] (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ N : Subgroup (V ≃ₗ[ZMod p] V), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥) :
    ∃ (ι : Type u) (_ : Finite ι) (C : Submodule (ZMod p) V) (W : ι → Submodule (ZMod p) V),
      C ⊔ (⨆ i, W i) = ⊤ ∧ (∀ i, IsCompl (W i) (C ⊔ ⨆ (j : ι) (_ : j ≠ i), W j)) ∧
      (∀ t ∈ trGroup A, (∀ c ∈ C, t c = c) ∧ ∀ i, ∀ w ∈ W i, t w ∈ W i) ∧
      ∀ i, 2 ≤ Module.finrank (ZMod p) (W i) ∧
        ((∀ g : V ≃ₗ[ZMod p] V, (∀ u ∈ C ⊔ ⨆ (j : ι) (_ : j ≠ i), W j, g u = u) →
            (∀ w ∈ W i, g w ∈ W i) → LinearEquiv.det g = 1 → g ∈ trGroup A) ∨
          ∃ β : LinearMap.BilinForm (ZMod p) V, β.IsAlt ∧
            (∀ u ∈ C ⊔ ⨆ (j : ι) (_ : j ≠ i), W j, ∀ v, β u v = 0) ∧
            (∀ w ∈ W i, w ≠ 0 → ∃ w' ∈ W i, β w w' ≠ 0) ∧
            ∀ g : V ≃ₗ[ZMod p] V, (∀ u ∈ C ⊔ ⨆ (j : ι) (_ : j ≠ i), W j, g u = u) →
              (∀ w ∈ W i, g w ∈ W i) → (∀ v w, β (g v) (g w) = β v w) → g ∈ trGroup A) := by
  classical
  have hS : ∀ t ∈ trSet A, ∃ v f, IsTransvectionWith t v f := fun t ht => ht.2
  have hSsub : trSet A ⊆ A := fun t ht => ht.1
  have hSA : ∀ a ∈ A, ∀ t ∈ trSet A, a * t * a⁻¹ ∈ trSet A := fun a ha t ht => trSet_conj ha ht
  have hK := kantor_reduction_of_normalizes hp hA hSsub hS hSA
  have hT : NoNormalExpP (Subgroup.closure (trSet A)) :=
    noNormalExpP_of_normal ((Subgroup.closure_le A).mpr hSsub)
      (fun _ ha _ ht => conj_mem_closure_of_normalizes hSA ha ht) hA
  have htop : fixSub (Subgroup.closure (trSet A)) ⊔
      (⨆ D : trComps (trSet A), cenSpan (D : Set (V ≃ₗ[ZMod p] V))) = ⊤ := by
    rw [hK.iSup_eq, sup_comm]
    exact hK.isCompl.sup_eq_top
  have hBle : ∀ D : trComps (trSet A), fixSub (Subgroup.closure (trSet A)) ⊔
      (⨆ (j : trComps (trSet A)) (_ : j ≠ D), cenSpan (j : Set (V ≃ₗ[ZMod p] V))) ≤
        fixSub (Subgroup.closure (D : Set (V ≃ₗ[ZMod p] V))) := fun D =>
    sup_le (hK.fixSub_le D D.2) (iSup₂_le fun j hj =>
      hK.cenSpan_le D D.2 j j.2 fun h => hj (Subtype.ext h.symm))
  have hcompl : ∀ D : trComps (trSet A), IsCompl (cenSpan (D : Set (V ≃ₗ[ZMod p] V)))
      (fixSub (Subgroup.closure (trSet A)) ⊔
        ⨆ (j : trComps (trSet A)) (_ : j ≠ D), cenSpan (j : Set (V ≃ₗ[ZMod p] V))) := by
    intro D
    refine ⟨(hK.isCompl_comp D D.2).disjoint.mono_right (hBle D), codisjoint_iff.mpr ?_⟩
    rw [eq_top_iff, ← htop]
    refine sup_le (le_sup_of_le_right le_sup_left) (iSup_le fun j => ?_)
    by_cases hj : j = D
    · rw [hj]
      exact le_sup_left
    · exact le_sup_of_le_right (le_sup_of_le_right (le_iSup₂_of_le (f := fun (j : trComps
        (trSet A)) (_ : j ≠ D) => cenSpan (j : Set (V ≃ₗ[ZMod p] V))) j hj le_rfl))
  have hG : ∀ (D : trComps (trSet A)) (g : V ≃ₗ[ZMod p] V),
      (∀ u ∈ fixSub (Subgroup.closure (trSet A)) ⊔
        ⨆ (j : trComps (trSet A)) (_ : j ≠ D), cenSpan (j : Set (V ≃ₗ[ZMod p] V)), g u = u) →
      (∃ h ∈ Subgroup.closure (D : Set (V ≃ₗ[ZMod p] V)),
        ∀ x : cenSpan (D : Set (V ≃ₗ[ZMod p] V)), h x = g x) → g ∈ trGroup A := by
    rintro D g hgB ⟨h, hh, hx⟩
    have hhg : h = g := by
      refine LinearEquiv.ext fun x => ?_
      have hxm : x ∈ cenSpan (D : Set (V ≃ₗ[ZMod p] V)) ⊔
          (fixSub (Subgroup.closure (trSet A)) ⊔
            ⨆ (j : trComps (trSet A)) (_ : j ≠ D), cenSpan (j : Set (V ≃ₗ[ZMod p] V))) := by
        rw [(hcompl D).sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hxm
      rw [map_add, map_add, hx ⟨w, hw⟩, hgB u hu, hBle D hu h hh]
    rw [← hhg]
    exact Subgroup.closure_mono (subset_of_mem_trComps D.2) hh
  refine ⟨trComps (trSet A), (trComps_finite _).to_subtype, fixSub (Subgroup.closure (trSet A)),
    fun D => cenSpan (D : Set (V ≃ₗ[ZMod p] V)), htop, hcompl, fun t ht => ⟨fun c hc => hc t ht,
      fun D w hw => ?_⟩, fun D => ⟨?_, ?_⟩⟩
  ·
    refine invariant_of_generators rfl (fun s hs x hx => ?_) t ht w hw
    obtain ⟨D', hD', hsD'⟩ := hK.cover s hs
    by_cases hDD' : (D : Set (V ≃ₗ[ZMod p] V)) = D'
    · have hsD : s ∈ Subgroup.closure (D : Set (V ≃ₗ[ZMod p] V)) :=
        Subgroup.subset_closure (hDD' ▸ hsD')
      exact ⟨cenSpan_invariant (tr_of_mem_trComps hS D.2) hsD hx,
        cenSpan_invariant (tr_of_mem_trComps hS D.2) (Subgroup.inv_mem _ hsD) hx⟩
    · have hfix := hK.cenSpan_le D' hD' D D.2 (fun h => hDD' h.symm) hx
      rw [hfix s (Subgroup.subset_closure hsD'),
        hfix s⁻¹ (Subgroup.inv_mem _ (Subgroup.subset_closure hsD'))]
      exact ⟨hx, hx⟩
  ·
    obtain ⟨t, ht⟩ := hK.nonempty D D.2
    obtain ⟨v, f, h⟩ := tr_of_mem_trComps hS D.2 t ht
    exact two_le_finrank_of_isTransvectionWith (isTransvectionWith_resCen
      (tr_of_mem_trComps hS D.2) (noNormalExpP_of_mem_trComps hT D.2) ht h)
  · rcases hK.slsp D D.2 with hSL | ⟨BW, hBa, hBn, hSp⟩
    · left
      intro g hgB hgW hdet
      have hmap := map_eq_of_mapsTo g hgW
      refine hG D g hgB ((hSL (g.ofSubmodules _ _ hmap)).mpr ?_)
      rw [← det_eq_det_ofSubmodules (hcompl D) g hgB hmap, ← LinearEquiv.coe_det, hdet]
      rfl
    · right
      set π := (cenSpan (D : Set (V ≃ₗ[ZMod p] V))).projectionOnto _ (hcompl D) with hπ
      refine ⟨BW.compl₁₂ π π, fun x => hBa (π x), fun u hu v => ?_, fun w hw hw0 => ?_,
        fun g hgB hgW hβ => ?_⟩
      · have : π u = 0 := Submodule.projectionOnto_apply_right (hcompl D) ⟨u, hu⟩
        rw [LinearMap.compl₁₂_apply, this, map_zero, LinearMap.zero_apply]
      · obtain ⟨hsepL, -⟩ := hBn
        by_contra hno
        push Not at hno
        apply hw0
        have h0 := hsepL ⟨w, hw⟩ fun n => by
          have := hno n n.2
          rwa [LinearMap.compl₁₂_apply, Submodule.projectionOnto_apply_left (hcompl D) ⟨w, hw⟩,
            Submodule.projectionOnto_apply_left (hcompl D) n] at this
        exact congrArg Subtype.val h0
      · have hmap := map_eq_of_mapsTo g hgW
        refine hG D g hgB ((hSp (g.ofSubmodules _ _ hmap)).mpr fun x y => ?_)
        have hx : π (g x) = g.ofSubmodules _ _ hmap x := by
          have := Submodule.projectionOnto_apply_left (hcompl D) (g.ofSubmodules _ _ hmap x)
          exact this
        have hy : π (g y) = g.ofSubmodules _ _ hmap y := by
          have := Submodule.projectionOnto_apply_left (hcompl D) (g.ofSubmodules _ _ hmap y)
          exact this
        have hx' : π x = x := Submodule.projectionOnto_apply_left (hcompl D) x
        have hy' : π y = y := Submodule.projectionOnto_apply_left (hcompl D) y
        have := hβ x y
        rw [LinearMap.compl₁₂_apply, LinearMap.compl₁₂_apply, hx, hy, hx', hy'] at this
        exact this

end CFSG.StandardType.McLaughlinOdd
