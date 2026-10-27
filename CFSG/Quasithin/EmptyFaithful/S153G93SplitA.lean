module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin

namespace S153G93

open CFSG.Open

theorem exists_component_conjClosure_eq {Q : Type*} [Group Q] [Finite Q] {K : Subgroup Q}
    (hKn : K.Normal) (hK1 : K ≠ ⊥)
    (hmin : ∀ M : Subgroup Q, M.Normal → M ≤ K → M = ⊥ ∨ M = K)
    (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) :
    ∃ N : Subgroup Q, CFSG.IsComponent N ∧ N ≤ K ∧ conjClosure N ⊤ = K := by
  obtain ⟨r, S, -, hSK, hSs, -, hSn, e, -⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hKn hK1 hmin
  have hnab : ∃ i, ∃ a b : ↥(S i), a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    obtain ⟨u, hu⟩ := e.surjective ⟨x, hx⟩
    obtain ⟨v, hv⟩ := e.surjective ⟨y, hy⟩
    have huv : u * v = v * u := funext fun i => hall i (u i) (v i)
    have h2 : e (u * v) = e (v * u) := by rw [huv]
    rw [map_mul, map_mul, hu, hv] at h2
    exact hxy (congrArg Subtype.val h2)
  obtain ⟨i, a, b, hab⟩ := hnab
  have := hSs i
  have hq : CFSG.IsQuasisimple ↥(S i) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨a, b, hab⟩).1
  have hSne : S i ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hq)
  have hsub : (S i).IsSubnormal :=
    Subgroup.IsSubnormal.step _ K (hSK i) hKn.isSubnormal (hSn i)
  have hnorm : (conjClosure (S i) ⊤).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_conjClosure _ _))
  have hle : conjClosure (S i) ⊤ ≤ K :=
    conjClosure_le fun h _ z hz => hKn.conj_mem z (hSK i hz) h
  refine ⟨S i, ⟨hq, hsub⟩, hSK i, ?_⟩
  rcases hmin _ hnorm hle with h | h
  · exact absurd (le_bot_iff.mp ((le_conjClosure (S i) ⊤).trans h.le)) hSne
  · exact h

end S153G93

end CFSG.Quasithin
