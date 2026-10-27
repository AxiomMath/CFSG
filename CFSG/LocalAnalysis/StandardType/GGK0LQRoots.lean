module

public import CFSG.LocalAnalysis.StandardType.GGK0LQNodes
import CFSG.LocalAnalysis.StandardType.GGK0NormalTypes
import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private theorem lk0xlqroots_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private def lk0xlqroots_cast (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun v := fun i => (v i : ℚ)
  map_add' v w := by ext i; simp
  map_smul' m v := by
    ext i
    simp only [Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    rfl

private theorem lk0xlqroots_p_pos (A : K0LangMark Omega lab p R I phi) : 0 < p := by
  obtain ⟨N⟩ := k0Normal_nonempty A
  exact N.zero_lt

private theorem lk0xlqroots_nodes_proper
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    ∃ i < (k0DiagOf A.row.T).marks.length, i ∉ lqNodes A P j := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hnb := lq_nodes_basic A P j
  have hsum := ggKacShVecs_sum (k0DiagOf A.row.T).marks p A.row.s A.row.s_mem
  have hzero : (∑ i : Fin (k0DiagOf A.row.T).marks.length,
      (k0DiagOf A.row.T).marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hs : A.row.s.getD i.val 0 = 0 := (hnb.2.2 i.val (h i.val i.isLt)).2
    rw [hs, mul_zero]
  rw [hzero] at hsum
  have hp := lk0xlqroots_p_pos A
  omega

theorem lq_compRank (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    compRank (componentRoots (rootCharHom A.a) (P.repr j)) = (lqNodes A P j).length := by
  have hbs := lq_nodes_basic A P j
  have hnd : (lqNodes A P j).Nodup := hbs.2.1
  have hc : ∀ x ∈ lqNodes A P j, x < (k0DiagOf A.row.T).marks.length := by
    intro x hx
    have h := hbs.2.2 x hx
    rw [lk0xlqroots_marks_length A.row.T, A.tau_eq]
    exact h.1
  have hproper := lk0xlqroots_nodes_proper A P j
  have hind : LinearIndependent ℚ
      (fun x : {x // x ∈ lqNodes A P j} =>
        fun i : Fin A.tau.rank => ((lqExtRoot A.tau A.row.T x.1 i : ℤ) : ℚ)) :=
    lq_extRoot_independent A.tau A.row.T A.tau_eq (lqNodes A P j) hnd hc hproper
  let S : Set (Fin A.tau.rank → ℤ) :=
    {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ lqNodes A P j ∧
      w = A.nodeMap (Pi.single i 1)}
  have hrepr := P.repr_roots j
  have hspan : Submodule.span ℚ
        (lk0xlqroots_cast A.tau.rank '' componentRoots (rootCharHom A.a) (P.repr j))
      = Submodule.span ℚ (Set.range (fun x : {x // x ∈ lqNodes A P j} =>
          fun i : Fin A.tau.rank => ((lqExtRoot A.tau A.row.T x.1 i : ℤ) : ℚ))) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨γ, hγ, rfl⟩
      have hγS : γ ∈ Submodule.span ℤ S := (hrepr ▸ hγ).2
      have hmap : Submodule.span ℤ S ≤
          ((Submodule.span ℚ (Set.range (fun x : {x // x ∈ lqNodes A P j} =>
            fun i : Fin A.tau.rank =>
              ((lqExtRoot A.tau A.row.T x.1 i : ℤ) : ℚ)))).restrictScalars ℤ).comap
            (lk0xlqroots_cast A.tau.rank) := by
        rw [Submodule.span_le]
        intro s hs
        rcases hs with ⟨i, hic, rfl⟩
        change lk0xlqroots_cast A.tau.rank (A.nodeMap (Pi.single i 1)) ∈
          Submodule.span ℚ (Set.range (fun x : {x // x ∈ lqNodes A P j} =>
            fun i : Fin A.tau.rank =>
              ((lqExtRoot A.tau A.row.T x.1 i : ℤ) : ℚ)))
        refine Submodule.subset_span ⟨⟨i.val, hic⟩, ?_⟩
        rw [lq_nodeMap_eq A i]
        rfl
      exact Submodule.mem_comap.mp (hmap hγS)
    · rw [Submodule.span_le]
      rintro z ⟨x, rfl⟩
      refine Submodule.subset_span
        ⟨A.nodeMap (Pi.single (⟨x.1, hc x.1 x.2⟩ : Fin A.row.diagram.marks.length) 1), ?_, ?_⟩
      · rw [hrepr]
        refine ⟨A.node_isRoot ⟨x.1, hc x.1 x.2⟩, Submodule.subset_span ?_⟩
        exact ⟨⟨x.1, hc x.1 x.2⟩, x.2, rfl⟩
      · change lk0xlqroots_cast A.tau.rank
            (A.nodeMap (Pi.single (⟨x.1, hc x.1 x.2⟩ : Fin A.row.diagram.marks.length) 1)) = _
        rw [lq_nodeMap_eq A ⟨x.1, hc x.1 x.2⟩]
        rfl
  have hcard : Fintype.card {x // x ∈ lqNodes A P j} = (lqNodes A P j).length := by
    rw [← List.toFinset_card_of_nodup hnd, ← Fintype.card_coe (lqNodes A P j).toFinset]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => List.mem_toFinset.symm))
  change Module.finrank ℚ (Submodule.span ℚ
      (lk0xlqroots_cast A.tau.rank '' componentRoots (rootCharHom A.a) (P.repr j)))
      = (lqNodes A P j).length
  rw [hspan, finrank_span_eq_card hind, hcard]

theorem lq_rankOne_iff (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    (∀ α ∈ componentRoots (rootCharHom A.a) (P.repr j),
        ∀ δ ∈ componentRoots (rootCharHom A.a) (P.repr j), δ = α ∨ δ = -α) ↔
      (lqNodes A P j).length = 1 := by
  constructor
  · intro h
    have hbs := lq_nodes_basic A P j
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hbs.1
    have hx_lt : x < (k0DiagOf A.row.T).marks.length := by
      have h := hbs.2.2 x hx
      rw [lk0xlqroots_marks_length A.row.T, A.tau_eq]
      exact h.1
    let i0 : Fin A.row.diagram.marks.length := ⟨x, hx_lt⟩
    let α0 : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single i0 1)
    have hα0 : α0 ∈ componentRoots (rootCharHom A.a) (P.repr j) := by
      rw [P.repr_roots j]
      exact ⟨A.node_isRoot i0, Submodule.subset_span ⟨i0, by simpa [lqNodes] using hx, rfl⟩⟩
    have hα0_ne : lk0xlqroots_cast A.tau.rank α0 ≠ 0 := by
      intro hzero
      have hz : α0 = 0 := by
        ext i
        have := congrFun hzero i
        simpa [lk0xlqroots_cast] using this
      exact (A.node_isRoot i0).ne_zero hz
    have hle : Submodule.span ℚ
          (lk0xlqroots_cast A.tau.rank '' componentRoots (rootCharHom A.a) (P.repr j))
        ≤ Submodule.span ℚ {lk0xlqroots_cast A.tau.rank α0} := by
      rw [Submodule.span_le]
      rintro z ⟨δ, hδ, rfl⟩
      rcases h α0 hα0 δ hδ with hEq | hEq
      · rw [hEq]; exact Submodule.subset_span rfl
      · rw [hEq]
        simpa using Submodule.neg_mem (Submodule.span ℚ {lk0xlqroots_cast A.tau.rank α0})
          (Submodule.subset_span rfl)
    have hfin : Module.finrank ℚ (Submodule.span ℚ
        (lk0xlqroots_cast A.tau.rank '' componentRoots (rootCharHom A.a) (P.repr j))) = 1 := by
      apply le_antisymm
      · calc Module.finrank ℚ (Submodule.span ℚ
              (lk0xlqroots_cast A.tau.rank '' componentRoots (rootCharHom A.a) (P.repr j)))
            ≤ Module.finrank ℚ (Submodule.span ℚ {lk0xlqroots_cast A.tau.rank α0}) :=
              Submodule.finrank_mono hle
          _ = 1 := finrank_span_singleton hα0_ne
      · have hmem : lk0xlqroots_cast A.tau.rank α0 ∈ Submodule.span ℚ
            (lk0xlqroots_cast A.tau.rank '' componentRoots (rootCharHom A.a) (P.repr j)) :=
          Submodule.subset_span ⟨α0, hα0, rfl⟩
        have hge : Submodule.span ℚ {lk0xlqroots_cast A.tau.rank α0} ≤ Submodule.span ℚ
            (lk0xlqroots_cast A.tau.rank '' componentRoots (rootCharHom A.a) (P.repr j)) := by
          rw [Submodule.span_le]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact Submodule.subset_span ⟨α0, hα0, rfl⟩
        calc 1 = Module.finrank ℚ (Submodule.span ℚ {lk0xlqroots_cast A.tau.rank α0}) :=
              (finrank_span_singleton hα0_ne).symm
          _ ≤ _ := Submodule.finrank_mono hge
    rw [← lq_compRank A P j]
    exact hfin
  · intro hlen
    have hbs := lq_nodes_basic A P j
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    have hx' : (P.orbitNodes j).headD [] = [x] := by simpa only [lqNodes] using hx
    have hx_lt : x < (k0DiagOf A.row.T).marks.length := by
      have h := hbs.2.2 x (by rw [hx]; simp)
      rw [lk0xlqroots_marks_length A.row.T, A.tau_eq]
      exact h.1
    let i0 : Fin A.row.diagram.marks.length := ⟨x, hx_lt⟩
    let α0 : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single i0 1)
    have hS : {w : Fin A.tau.rank → ℤ | ∃ i : Fin A.row.diagram.marks.length,
        i.val ∈ (P.orbitNodes j).headD [] ∧ w = A.nodeMap (Pi.single i 1)} = {α0} := by
      ext w
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi' : i.val = x := by
          rw [hx'] at hi
          simpa using hi
        rw [show i = i0 from Fin.ext hi', Set.mem_singleton_iff]
      · rintro rfl
        exact ⟨i0, by rw [hx']; simp [i0], rfl⟩
    have hmem_pm : ∀ v ∈ componentRoots (rootCharHom A.a) (P.repr j), v = α0 ∨ v = -α0 := by
      intro v hv
      obtain ⟨hvroot, hvspan⟩ := (P.repr_roots j) ▸ hv
      rw [hS] at hvspan
      obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hvspan
      rcases hvroot.eq_one_or_neg_one_of_eq_smul hn.symm with h1 | h1
      · left; rw [h1, one_smul] at hn; exact hn.symm
      · right; rw [h1, neg_one_smul] at hn; exact hn.symm
    intro α hα δ hδ
    rcases hmem_pm α hα with rfl | rfl <;> rcases hmem_pm δ hδ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr (neg_neg α0).symm
    · exact Or.inl rfl

end CFSG.StandardType.GGK0LQ

end
