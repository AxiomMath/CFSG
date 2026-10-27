module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux4
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm37

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G Q Y : Subgroup Γ}

theorem sol_eq_bot_of_pair (h : NearAsolvAction p A G) (hP : (Q, ⊥) ∈ iPairsY A G Y)
    (hns : ¬ Group.IsSolvable ↥Q) (hG : G = Q ⊔ cenIn G (A : Set Γ)) : sol G = ⊥ := by
  have hD : cenIn G (A : Set Γ) ≤ G := inf_le_left
  have hQG : Q ≤ G := Thm33a.pair_le hP
  have hSn : Admits G (sol G) := Nonsolv.SolQuot.le_nrm_sol G
  have hSA : Admits A (sol G) := h.admits.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol G)
  have hSH : Admits (Q ⊔ cenIn G (A : Set Γ) ⊔ A) (sol G) :=
    sup_le (sup_le (hQG.trans hSn) (hD.trans hSn)) hSA
  have hSQ : Admits (Q ⊔ cenIn G (A : Set Γ) ⊔ A) (sol G ⊓ Q) :=
    Admits.inf hSH (Thm33a.pair_admits_H hP)
  rcases Thm33a.chief_dichotomy (Thm33a.pair_chief hP) hSQ inf_le_right with h1 | h1
  · refine eq_bot_iff.mpr fun s hs => ?_
    have hsG : s ∈ Q ⊔ cenIn G (A : Set Γ) := hG ▸ sol_le G hs
    have hGQ : G ≤ Subgroup.normalizer (Q : Set Γ) :=
      hG ▸ sup_le Subgroup.le_normalizer (le_sup_left.trans (Thm33a.pair_admits_left hP))
    have hsec : s ∈ secCenIn (Q ⊔ cenIn G (A : Set Γ)) Q ⊥ := by
      refine Subgroup.mem_inf.mpr ⟨hsG, ?_⟩
      rw [mem_sectionCentralizer_iff]
      refine ⟨?_, hGQ (sol_le G hs), fun y hy => ?_⟩
      · exact (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup Γ).Normal)) ▸
          Subgroup.mem_top s
      · have hyG : y ∈ G := hQG hy
        have h2 : ⁅s, y⁆ ∈ sol G ⊓ Q := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have e : ⁅s, y⁆ = s * (y * s⁻¹ * y⁻¹) := by
              simp only [commutatorElement_def]
              group
            rw [e]
            exact mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hSn hyG) s⁻¹).mp (inv_mem hs))
          · have e : ⁅s, y⁆ = (s * y * s⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
            rw [e]
            exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hGQ (sol_le G hs)) y).mp hy)
              (inv_mem hy)
        have h3 := h1 h2
        simpa using h3
    rw [Thm33a.pair_secCenIn hP] at hsec
    exact hsec
  · exfalso
    rw [sup_bot_eq] at h1
    exact hns (Thm211.isSolvable_of_le (h1 ▸ inf_le_left) (isSolvable_sol G))

theorem le_kOf_of_pair (h : NearAsolvAction p A G) (hsol : sol G = ⊥)
    (hP : (Q, ⊥) ∈ iPairsY A G Y) (hG : G = Q ⊔ cenIn G (A : Set Γ)) : Q ≤ kOf G := by
  have hQG : Q ≤ G := Thm33a.pair_le hP
  have hKG : Admits G (kOf G) := Nonsolv.le_normalizer_kOf G
  have hKA : Admits A (kOf G) := h.admits.trans (Thm211.normalizer_le_normalizer_kOf G)
  have hKH : Admits (Q ⊔ cenIn G (A : Set Γ) ⊔ A) (kOf G) :=
    sup_le (sup_le (hQG.trans hKG) (inf_le_left.trans hKG)) hKA
  have hB : Admits (Q ⊔ cenIn G (A : Set Γ) ⊔ A) (kOf G ⊓ Q) :=
    Admits.inf hKH (Thm33a.pair_admits_H hP)
  have hGQ : Admits G Q :=
    hG ▸ sup_le Subgroup.le_normalizer (le_sup_left.trans (Thm33a.pair_admits_left hP))
  rcases Thm33a.chief_dichotomy (Thm33a.pair_chief hP) hB inf_le_right with h1 | h1
  · exfalso
    have hQC : Q ≤ Subgroup.centralizer (kOf G : Set Γ) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Thm33a.commute_of_inf_eq_bot hKG hGQ (kOf_le G) hQG (le_bot_iff.mp h1) hk hq).eq
    have : Q ≤ G ⊓ Subgroup.centralizer (kOf G : Set Γ) := le_inf hQG hQC
    rw [centralizer_kOf_eq_bot hsol] at this
    exact (Thm33a.pair_lt hP).not_ge this
  · rw [sup_bot_eq] at h1
    exact h1 ▸ inf_le_left

theorem decomp_of_pair
    (h : NearAsolvAction p A G) (hP : (Q, ⊥) ∈ iPairsY A G Y)
    (hns : ¬ Group.IsSolvable ↥Q) (hG : G = Q ⊔ cenIn G (A : Set Γ)) {T : Subgroup Γ}
    (hTQ : T ≤ Q) (hTadm : Admits (cenIn G (A : Set Γ) ⊔ A) T) (hTperf : Group.IsPerfect ↥T)
    {x : Γ} (hxQ : x ∈ Q) (hxA : x ∈ Subgroup.centralizer (A : Set Γ)) :
    ∃ t ∈ T, ∃ c ∈ Subgroup.centralizer (T : Set Γ), x = t * c := by
  have hsol := sol_eq_bot_of_pair h hP hns hG
  have hG1 : G ≠ ⊥ := fun h0 => (Thm33a.pair_lt hP).not_ge ((Thm33a.pair_le hP).trans h0.le)
  have hQK := le_kOf_of_pair h hsol hP hG
  obtain ⟨hdp, hk2⟩ := lemma213b h hsol hG1 (hTQ.trans hQK) hTadm hTperf
  have hx : x ∈ cenIn (kOf G) (A : Set Γ) := Subgroup.mem_inf.mpr ⟨hQK hxQ, hxA⟩
  rw [← hdp.sup_eq] at hx
  obtain ⟨j, hj, l, hl, rfl⟩ := (mem_sup_iff_of_commute hdp.commute).mp hx
  rw [hk2] at hl
  refine ⟨l, (Subgroup.mem_inf.mp hl).1, j, ?_, (hdp.commute j hj l (hk2 ▸ hl)).eq⟩
  exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hj).1).2

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm37
