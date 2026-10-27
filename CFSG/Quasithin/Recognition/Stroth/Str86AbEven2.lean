module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbEven

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.Stroth.Str86AbOdd
import CFSG.Quasithin.Recognition.F112Crit.Lemma65
import CFSG.Quasithin.Background.D15Chief
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_displacement_far_even {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb : Even (str86CritB L1 L2 S)) (hb4 : 4 ≤ str86CritB L1 L2 S) {μ ν : Str86Γ L1 L2 S}
    (hμ : μ ∈ nbrs (lam (str86CritB L1 L2 S))) (hν : ν ∈ nbrs μ) {t : G}
    (ht : t ∈ Vv (Z2 L1 L2 S) ν) :
    (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Vv (Z2 L1 L2 S) (lam 1)) ≤ 2 ^ m * 2 ^ k * 2 ^ m := by
  obtain ⟨-, hGL2, -⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨-, hAB2, -⟩ := str86_Vv_abelian hI
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  have hb1 : 1 ≤ str86CritB L1 L2 S := by omega
  have hvb : vtype (lam (str86CritB L1 L2 S)) = false := hP.vtype_of_even hI le_rfl hb
  have hv1 : vtype (lam 1) = true := hP.vtype_of_odd hI (by omega) odd_one
  have hvb1 : vtype (lam (str86CritB L1 L2 S - 1)) = true := by
    obtain ⟨j, hj⟩ := hb
    exact hP.vtype_of_odd hI (by omega) ⟨j - 1, by omega⟩
  have hadjb : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 1) (by omega)
    rwa [Nat.sub_add_cancel hb1] at h
  have hvμ : vtype μ = true := F112Crit.vtype_eq_true_of_mem_nbrs hvb hμ
  have hvν : vtype ν = false := str86_vtype_of_mem_nbrs hvμ hν
  have hμb : lam (str86CritB L1 L2 S) ∈ nbrs μ :=
    (show (graph _ _ _).Adj (lam (str86CritB L1 L2 S)) μ from hμ).symm
  have hVα : Vv (Z2 L1 L2 S) (lam 1) ≤
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)) ⊓ stab (lam (str86CritB L1 L2 S))) := by
    refine (hGL2 _ _ hv1 ?_).trans (str86_pCoreOf_le_pCoreOf_inf hI hadjb)
    rw [hP.isGeo 1 _ (by omega) (by omega)]
    omega
  set A1 : Subgroup G := Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))
    with hA1
  set A2 : Subgroup G := A1 ⊓ pCoreOf 2 (stab μ) with hA2
  set A3 : Subgroup G := A2 ⊓ pCoreOf 2 (stab ν) with hA3
  have h1 : A1.relIndex (Vv (Z2 L1 L2 S) (lam 1)) ≤ 2 ^ m := by
    rw [hA1, Subgroup.inf_relIndex_left, ← (str86_edge_facts hI hvb1 hadjb).2.2.2.1]
    exact Subgroup.relIndex_le_of_le_right hVα (D15Proof.relIndex_ne_zero _ _)
  have hA1e : IsElemAbelian 2 A1 := (hAB2 (by omega) _ hv1).mono inf_le_left
  have hA1S : A1 ≤ pCoreOf 2 (stab μ ⊓ stab (lam (str86CritB L1 L2 S))) := by
    rw [inf_comm]
    exact inf_le_right.trans (str86_pCoreOf_le_pCoreOf_inf hI hμ)
  have h2 : A2.relIndex A1 ≤ 2 ^ k := by
    rw [hA2]
    exact (str86_edge_facts hI hvμ hμb).2.2.2.2.2.2 A1 hA1e hA1S
  have h3 : A3.relIndex A2 ≤ 2 ^ m := by
    rw [hA3, Subgroup.inf_relIndex_left, ← (str86_edge_facts hI hvμ hν).2.2.2.1]
    exact Subgroup.relIndex_le_of_le_right
      (inf_le_right.trans (str86_pCoreOf_le_pCoreOf_inf hI hν)) (D15Proof.relIndex_ne_zero _ _)
  have ht' : t ∈ omegaOneCenterOf (pCoreOf 2 (stab ν)) := by
    rw [← hD41 ν hvν]
    exact ht
  have hC : A3 ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    inf_le_right.trans ((SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (stab ν)).trans
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr ht')))
  have hmul1 := Subgroup.relIndex_mul_relIndex A3 A2 A1 inf_le_left inf_le_left
  have hmul2 := Subgroup.relIndex_mul_relIndex A3 A1 (Vv (Z2 L1 L2 S) (lam 1))
    (inf_le_left.trans inf_le_left) inf_le_left
  calc (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (Vv (Z2 L1 L2 S) (lam 1)) ≤ A3.relIndex (Vv (Z2 L1 L2 S) (lam 1)) :=
        Subgroup.relIndex_le_of_le_left hC (D15Proof.relIndex_ne_zero _ _)
    _ = A3.relIndex A2 * A2.relIndex A1 * A1.relIndex (Vv (Z2 L1 L2 S) (lam 1)) := by
        rw [← hmul2, ← hmul1]
    _ ≤ 2 ^ m * 2 ^ k * 2 ^ m := Nat.mul_le_mul (Nat.mul_le_mul h3 h2) h1

theorem str86_V2_le_pCoreOf_even {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb : Even (str86CritB L1 L2 S)) (hb6 : 6 ≤ str86CritB L1 L2 S) :
    str86V2 L1 L2 S (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2))) := by
  obtain ⟨hGL1, -, -⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨-, hZ1b, hcomm, -, -, -, hc2, hc1⟩ := str86_critPath_e1 hE1 hI hP hb (by omega)
  have hd : ∀ i j, i ≤ j → j ≤ str86CritB L1 L2 S →
      CosetGeom.dist (lam i) (lam j) = j - i := hP.isGeo
  have hadj : ∀ i, i < str86CritB L1 L2 S →
      (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj (lam i) (lam (i + 1)) :=
    fun i hi => hP.isGeo.adj hi
  have hv1 : vtype (lam 1) = true := hP.vtype_of_odd hI (by omega) odd_one
  unfold str86V2
  refine iSup₂_le fun γ hγ => ?_
  have hγt : vtype γ = true := F112Crit.vtype_eq_true_of_mem_nbrs hP.linear hγ
  refine F112Crit.Vv_le_of_forall_mem_nbrs hγt fun ν hν => ?_
  have hνt : vtype ν = false := str86_vtype_of_mem_nbrs hγt hν
  by_contra hνQ
  have hγν : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj ν γ :=
    (show (graph _ _ _).Adj γ ν from hν).symm
  have hγ0 : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj γ (lam 0) :=
    (show (graph _ _ _).Adj (lam 0) γ from hγ).symm
  have hγ1 : γ ≠ lam 1 := by
    rintro rfl
    apply hνQ
    refine hGL1 ν _ hνt ?_
    have h := CosetGeom.dist_triangle_of_adj hγν (lam (str86CritB L1 L2 S - 2))
    rw [CosetGeom.dist_eq_one_iff_adj.mpr hγν, hd 1 _ (by omega) (by omega)] at h
    omega
  set lam' : ℕ → Str86Γ L1 L2 S :=
    fun i => if i = 0 then ν else if i = 1 then γ else lam (i - 2) with hlam'
  have hl0 : lam' 0 = ν := by simp [hlam']
  have hl1 : lam' 1 = γ := by simp [hlam']
  have hl : ∀ i, 2 ≤ i → lam' i = lam (i - 2) := fun i hi => by
    simp only [hlam']
    rw [if_neg (by omega), if_neg (by omega)]
  have hP' : Str86CritPath L1 L2 S lam' := by
    refine str86_critPath_of_walk hI (by rw [hl0]; exact hνt) (fun i hi => ?_) ?_
    · rcases Nat.lt_or_ge i 2 with h2 | h2
      · interval_cases i
        · rw [hl0, hl1]
          exact hγν
        · rw [hl1, hl 2 le_rfl]
          exact hγ0
      · rw [hl i h2, hl (i + 1) (by omega), show i + 1 - 2 = i - 2 + 1 by omega]
        exact hadj (i - 2) (by omega)
    · rw [hl0, hl _ (by omega)]
      exact hνQ
  obtain ⟨-, hZ', -⟩ := str86_critPath_e1 hE1 hI hP' hb (by omega)
  rw [hl1, hl _ (by omega), show str86CritB L1 L2 S - 1 - 2 = str86CritB L1 L2 S - 3 by omega]
    at hZ'
  have hV0 := str86_Vv_eq_sup_of_ne hI hc2 hc1 hP.linear hγ (hadj 0 (by omega)) hγ1
  have hvb2 : vtype (lam (str86CritB L1 L2 S - 2)) = false := by
    obtain ⟨j, hj⟩ := hb
    exact hP.vtype_of_even hI (by omega) ⟨j - 1, by omega⟩
  have hn3 : lam (str86CritB L1 L2 S - 3) ∈ nbrs (lam (str86CritB L1 L2 S - 2)) := by
    have h := (hadj (str86CritB L1 L2 S - 3) (by omega)).symm
    rwa [show str86CritB L1 L2 S - 3 + 1 = str86CritB L1 L2 S - 2 by omega] at h
  have hn1 : lam (str86CritB L1 L2 S - 1) ∈ nbrs (lam (str86CritB L1 L2 S - 2)) := by
    have h := hadj (str86CritB L1 L2 S - 2) (by omega)
    rwa [show str86CritB L1 L2 S - 2 + 1 = str86CritB L1 L2 S - 1 by omega] at h
  have hVb2 := str86_Vv_eq_sup_of_ne hI hc2 hc1 hvb2 hn3 hn1
    (hP.isGeo.ne (by omega) (by omega))
  have heq : Vv (Z2 L1 L2 S) (lam 0) = Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S - 2)) := by
    rw [hV0, hVb2, hZ', hZ1b]
  have hle : Vv (Z2 L1 L2 S) (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) := by
    rw [heq]
    refine hGL1 _ _ hvb2 ?_
    rw [hd _ _ (by omega) le_rfl]
    omega
  have hbot : ⁅Vv (Z2 L1 L2 S) (lam 0), Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans ?_)
    rw [hD41 _ (hP.vtype_of_even hI le_rfl hb)]
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf _
  rw [hcomm] at hbot
  exact (str86_edge_facts hI hv1 (hadj 0 (by omega)).symm).2.2.2.2.2.1 hbot

end CFSG.Quasithin.Stroth

end
