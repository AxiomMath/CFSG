module

public import CFSG.RankThree.GF2n.Tim79Local

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

theorem Hyp79.comm_mem_V (H : Hyp79 M V Q) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ ∈ V := by
  obtain ⟨hQ', -, -⟩ := H.special
  exact hQ' ▸ Subgroup.commutator_mem_commutator hx hy

theorem Hyp79.sq_mem_V (H : Hyp79 M V Q) {x : G} (hx : x ∈ Q) : x ^ 2 ∈ V := by
  obtain ⟨g, hgV, hgQ⟩ := H.exists_opposite
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  exact h.sq_mem (hPQ.symm.le hx)

theorem Hyp79.V_central (H : Hyp79 M V Q) {v y : G} (hv : v ∈ V) (hy : y ∈ Q) :
    v * y = y * v := by
  obtain ⟨-, hZ, -⟩ := H.special
  have : v ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ hv
  exact (Subgroup.mem_centralizer_iff.mp this.2 y hy).symm

theorem Hyp79.comm_mem_conj (H : Hyp79 M V Q) (g : G) {x y : G} (hx : x ∈ conjSubgroup g Q)
    (hy : y ∈ conjSubgroup g Q) : ⁅x, y⁆ ∈ conjSubgroup g V := by
  obtain ⟨hQ', -, -⟩ := H.special
  have : ⁅conjSubgroup g Q, conjSubgroup g Q⁆ = conjSubgroup g V := by
    rw [← hQ']
    exact (Subgroup.map_commutator _ _ _).symm
  exact this ▸ Subgroup.commutator_mem_commutator hx hy

theorem Hyp79.sq_mem_conj (H : Hyp79 M V Q) (g : G) {x : G} (hx : x ∈ conjSubgroup g Q) :
    x ^ 2 ∈ conjSubgroup g V := by
  rw [mem_conjSubgroup] at hx ⊢
  rw [show g⁻¹ * x ^ 2 * g = (g⁻¹ * x * g) ^ 2 by rw [pow_two, pow_two]; group]
  exact H.sq_mem_V hx

theorem Hyp79.conj_central (H : Hyp79 M V Q) (g : G) {u y : G} (hu : u ∈ conjSubgroup g V)
    (hy : y ∈ conjSubgroup g Q) : u * y = y * u := by
  rw [mem_conjSubgroup] at hu hy
  have h1 := H.V_central hu hy
  have e1 : u * y = g * ((g⁻¹ * u * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
  have e2 : y * u = g * ((g⁻¹ * y * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
  rw [e1, e2, h1]

theorem Hyp79.sup_le_normalizer_W (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) :
    Q ⊔ conjSubgroup g Q ≤ Subgroup.normalizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G) := by
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  exact sup_le (hPQ.symm.le.trans h.P_le_normalizer_W)
    ((Subgroup.map_mono hPQ.symm.le).trans (h.Pg_le_normalizer_W hxW hxV))

theorem Hyp79.centralizer_W_eq_sup (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) :
    (Q ⊔ conjSubgroup g Q) ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G) =
      (Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)) ⊔
        (conjSubgroup g Q ⊓
          Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)) := by
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  have := h.inf_centralizer_W_eq_sup hxW hxV hy H.q4 (H := Q ⊔ conjSubgroup g Q) (by rw [hPQ])
  rwa [hPQ] at this

private theorem mem_normalizer_of_comm_mem {L : Subgroup G} {z : G}
    (h : ∀ l ∈ L, ⁅z, l⁆ ∈ L) : z ∈ Subgroup.normalizer (L : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun l hl => ?_
  rw [show z * l * z⁻¹ = ⁅z, l⁆ * l by rw [commutatorElement_def]; group]
  exact mul_mem (h l hl) hl

theorem Hyp79.L_normal (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) :
    ∀ z ∈ Q ⊔ conjSubgroup g Q, ∀ l ∈ Q ⊓ conjSubgroup g Q,
      z * l * z⁻¹ ∈ Q ⊓ conjSubgroup g Q := by
  obtain ⟨hVL, -⟩ := H.L_facts hgV hgQ
  have hle : Q ⊔ conjSubgroup g Q ≤
      Subgroup.normalizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G) :=
    sup_le (fun z hz => mem_normalizer_of_comm_mem fun l hl =>
      (le_sup_left.trans hVL) (H.comm_mem_V hz hl.1))
      (fun z hz => mem_normalizer_of_comm_mem fun l hl =>
        (le_sup_right.trans hVL) (H.comm_mem_conj g hz hl.2))
  intro z hz l hl
  exact (Subgroup.mem_normalizer_iff.mp (hle hz) l).mp hl

end CFSG.RankThree.GF2n.Tim79
