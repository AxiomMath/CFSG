module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
import CFSG.LocalAnalysis.StandardType.GGTBFix
import CFSG.LocalAnalysis.StandardType.GGDepAConfig

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l04fLC_automizer_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hxBs : x ∈ Bs) :
    ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hcent : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hle : ggAutomizer L Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro ψ hψ
    obtain ⟨g, hgL, -, hg⟩ := hψ
    have hmem : g ∈ Subgroup.centralizer ({x} : Set G) := hcent hgL
    have hcomm : g * x = x * g :=
      ((Subgroup.mem_centralizer_iff.mp hmem) x (by simp)).symm
    change ψ • (⟨x, hxBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs)
    rw [MulAut.smul_def]
    apply Subtype.ext
    have h : ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = g * x * g⁻¹ := by
      have h1 := hg (⟨x, hxBs⟩ : ↥Bs)
      simpa using h1
    rw [h, hcomm]
    group
  intro ψ hψ
  simpa only [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hle hψ

theorem ggResXDatum_lframe (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hdat : GGResXDatum p Bs L) (V : Type)
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (T : Type) (_ : Finite T) (s : T → (V ≃ₗ[ZMod p] V)),
      (∀ k, GGLinRefl (s k)) ∧
      (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected ∧
      Subgroup.closure (Set.range s) = (ggAutomizer L Bs).map (ggLin (p := p) ι) ∧
      ggLinFix (Set.range s) = Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)} ∧
      ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 := by
  classical
  rcases hdat with
    ⟨Λ, hFin, hDec, M, C, V₀, hAC, hMod, ι₀, φ, v₀, α, hM, hC, hφ, hrefl, hpair, hf, hgen⟩
  have : Fintype Λ := hFin
  have : DecidableEq Λ := hDec
  obtain ⟨f, hf⟩ := hf
  have hne : Nonempty Λ := by
    have hM' := hM
    rcases hM' with ⟨n, e, hn, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · exact ⟨e ⟨0, by omega⟩⟩
    · exact ⟨e 0⟩
    · exact ⟨e 0⟩
    · exact ⟨e 0⟩
    · exact ⟨e 0⟩
    · exact ⟨e 0⟩
  let s : Λ → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ i)
  refine ⟨Λ, inferInstance, s, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (ggRC_isReflection_iff_linRefl (p := p) ι (φ k)).mp (hrefl k)
  · have hnc : ∀ u v : Λ, u ≠ v → M.M u v ≠ 2 → s u * s v ≠ s v * s u := by
      intro u v huv hMuv hcomm
      have hφcomm : φ u * φ v = φ v * φ u := by
        apply ggLin_injective (p := p) ι
        rw [map_mul, map_mul]
        exact hcomm
      have hsub : f (M.simple u) * f (M.simple v) = f (M.simple v) * f (M.simple u) := by
        apply Subtype.ext
        show (f (M.simple u) : MulAut ↥Bs) * (f (M.simple v) : MulAut ↥Bs) =
          (f (M.simple v) : MulAut ↥Bs) * (f (M.simple u) : MulAut ↥Bs)
        rw [hf u, hf v]
        exact hφcomm
      have hsimple : M.simple u * M.simple v = M.simple v * M.simple u := by
        apply f.injective
        rw [map_mul, map_mul]
        exact hsub
      have hsi : M.simple u * M.simple u = 1 := by
        rw [← pow_two]
        exact M.toCoxeterSystem.simple_sq u
      have hsj : M.simple v * M.simple v = 1 := by
        rw [← pow_two]
        exact M.toCoxeterSystem.simple_sq v
      have h2 : (M.simple u * M.simple v) ^ 2 = 1 := by
        rw [pow_two]
        calc (M.simple u * M.simple v) * (M.simple u * M.simple v)
            = M.simple u * (M.simple v * M.simple u) * M.simple v := by group
          _ = M.simple u * (M.simple u * M.simple v) * M.simple v := by rw [← hsimple]
          _ = (M.simple u * M.simple u) * (M.simple v * M.simple v) := by group
          _ = 1 := by rw [hsi, hsj, mul_one]
      have ho : orderOf (M.simple u * M.simple v) = M.M u v := by
        have h := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem u v
        rw [CoxeterMatrix.toCoxeterSystem_simple] at h
        exact h
      have hdvd : M.M u v ∣ 2 := ho ▸ orderOf_dvd_iff_pow_eq_one.mpr h2
      have hle : M.M u v ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < M.M u v := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
      have hoff : M.M u v ≠ 1 := M.off_diagonal u v huv
      omega
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨Classical.choice hne, ?_⟩
    intro j
    induction ggRC_weyl_connected hM (Classical.choice hne) j with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hbc ih =>
        have hadj : (SimpleGraph.fromRel fun i j : Λ => s i * s j ≠ s j * s i).Adj _ _ :=
          (SimpleGraph.fromRel_adj _ _ _).mpr
            ⟨hbc.1, Or.inl (hnc _ _ hbc.1 hbc.2)⟩
        exact ih.trans (SimpleGraph.Adj.reachable hadj)
  · rw [hgen, MonoidHom.map_closure]
    congr 1
    exact Set.range_comp (ggLin (p := p) ι) φ
  · apply le_antisymm
    · intro v hv
      let bb : ↥Bs := Additive.toMul (ι.symm v)
      have hbbw : ι (Additive.ofMul bb) = v := by
        dsimp only [bb]
        rw [ofMul_toMul, AddEquiv.apply_symm_apply]
      have hbb : ∀ i, φ i bb = bb := by
        intro i
        refine (ggLin_fix_iff (p := p) ι (φ i) bb).mpr ?_
        rw [hbbw]
        exact hv (s i) ⟨i, rfl⟩
      have hfixL : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
        rw [hgen]
        exact ggFixed_of_mem_closure φ bb hbb
      have hxmem : (bb : G) ∈ Subgroup.zpowers x :=
        hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
          hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hfixL
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
      have hbk : bb = (⟨x, hx⟩ : ↥Bs) ^ k := Subtype.ext (by simpa using hk.symm)
      have hof : Additive.ofMul bb = k • Additive.ofMul (⟨x, hx⟩ : ↥Bs) := by
        rw [hbk, ofMul_zpow]
      have hvk : v = k • ι (Additive.ofMul ⟨x, hx⟩) := by
        have h := congrArg ι hof
        simpa [hbbw, map_zsmul] using h
      rw [hvk]
      have hmem : ι (Additive.ofMul ⟨x, hx⟩) ∈
          Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) :=
        Submodule.subset_span rfl
      have hsm := Submodule.smul_mem
        (Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V))
        (k : ZMod p) hmem
      rwa [Int.cast_smul_eq_zsmul] at hsm
    · rw [Submodule.span_le]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rintro a ⟨i, rfl⟩
      show ggLin (p := p) ι (φ i) (ι (Additive.ofMul ⟨x, hx⟩)) =
        ι (Additive.ofMul ⟨x, hx⟩)
      refine (ggLin_fix_iff (p := p) ι (φ i) ⟨x, hx⟩).mp ?_
      have hmem : φ i ∈ ggAutomizer L Bs := by
        rw [hgen]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      exact l04fLC_automizer_fixes_x hH.1 hx (φ i) hmem
  · intro h0
    have hzero : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := by
      apply ι.injective
      rw [map_zero]
      exact h0
    have h1 : (⟨x, hx⟩ : ↥Bs) = 1 := by
      have h := Additive.ofMul.injective hzero
      simpa using h
    exact l05nDD1_x_ne_one hH (by simpa using congrArg Subtype.val h1)

end CFSG.StandardType

end
