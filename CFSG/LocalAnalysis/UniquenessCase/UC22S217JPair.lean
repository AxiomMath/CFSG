module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217j_barImage_inf_eq_bot {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : L ≠ K) (hZ : center (Bar2 L) = ⊥) :
    barImage M L ⊓ barImage M K = ⊥ := by
  obtain ⟨e, he⟩ := uc22p22l_barImage_equiv hL
  refine (Subgroup.eq_bot_iff_forall _).2 fun q hq => ?_
  obtain ⟨m, hmL, rfl⟩ := uc22p21c_mem_barImage.1 (mem_inf.1 hq).1
  have hc := uc22ine229_mk_mem_center hL hK hne ⟨m, hmL⟩ (mem_inf.1 hq).2
  rw [hZ, mem_bot] at hc
  have h := he ⟨m, hmL⟩
  rw [hc, map_one, OneMemClass.coe_one] at h
  exact h.symm

theorem uc22s217j_exists_elemAbelian_of_pair {M L A₀ : Subgroup G} (hL : L ∈ calC M)
    (hc2 : (conjSetOf M L).ncard = 2) (hZ : center (Bar2 L) = ⊥) {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r)
    (hW : ∀ W : Subgroup (Bar2 M), (Bar2 L ≃* ↥W) →
      CFSG.Open.pRank r W ≤ 1 ∧ r ∣ Nat.card W ∧ ¬ p ∣ Nat.card (Sylow r ↥W))
    (hA₀M : A₀ ≤ M) (hA₀ : IsPGroup p A₀) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      A₀ ≤ normalizer (E : Set G) ∧
      ∀ R : Subgroup G, R ≤ M → IsPGroup r R → E ≤ R → E ≤ centralizer (R : Set G) := by
  obtain ⟨K, hKmem, hKL⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (conjSetOf M L).ncard) L
  have hKC : K ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL hKmem
  have hcK : (conjSetOf M K).ncard = 2 := by rwa [uc22p2214_conjSetOf_eq hKmem]
  obtain ⟨eL, -⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨eK, -⟩ := uc22p22l_barImage_equiv hKC
  obtain ⟨g, -, hg⟩ := hKmem
  obtain ⟨f⟩ : Nonempty (Bar2 L ≃* Bar2 K) := hg ▸ uc22p20d_bar2_conj g L
  have hN : ∀ x : ↥M, Odd (orderOf x) → uc22p21cPi M x ∈
      normalizer (barImage M L : Set (Bar2 M)) ⊓ normalizer (barImage M K : Set (Bar2 M)) := by
    intro x hx
    rw [← Subgroup.orderOf_coe] at hx
    exact ⟨uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hc2 x.2 hx),
      uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcK x.2 hx)⟩
  exact uc22ine229_exists_elemAbelian_pair hp hr hp2 hr2 hpr
    (uc22p22l_barImage_commute hL hKC hKL.symm) (uc22s217j_barImage_inf_eq_bot hL hKC hKL.symm hZ)
    (hW _ eL) (hW _ (f.trans eK)) hN hA₀M hA₀

end CFSG.LocalAnalysis.UniquenessCase.UC22
