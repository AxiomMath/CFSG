module

public import CFSG.Quasithin.Recognition.Kleidman.F204.T3S
public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Geo

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Main

variable (F : Frame L1 L2 S D X)
include F

theorem T3_false (hT3 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ¬ ZCentral δ) : False := by
  have hA := Amal.of_frame F
  have hdich : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ∨ ZFaithful δ :=
    fun δ => dichotomy F δ
  have hfaith : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZFaithful δ := fun δ =>
    (hdich δ).resolve_left (hT3 δ)
  set b := bMin (P1 L1 L2 S) (P2 L1 L2 S) with hbdef
  have hb2 : 2 ≤ b := two_le_bMin F
  obtain ⟨α, hαb⟩ := hA.exists_bAt_eq_bMin
  obtain ⟨β, hβ⟩ : ∃ β, β ∈ nbrs α := by
    by_contra hcon
    push Not at hcon
    have hcard := hA.card_nbrs α
    have : nbrs α = ∅ := Set.eq_empty_iff_forall_notMem.mpr hcon
    rw [this] at hcard
    simp at hcard
  have hadj : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj α β := hβ
  obtain ⟨α', hc⟩ := hA.exists_critData hαb hadj
  obtain ⟨hnot, hvα, hvα', -, -, hrel1, hrel2⟩ := T3_H4 F hT3 hc
  obtain ⟨hb', -, -⟩ := hA.caseI hdich hc hnot
  have hsx : Zv α' ≤ stab α := by
    apply hA.Zv_le_stab_of_dist_le
    rw [hb', CosetGeom.dist_comm, hc.dist_eq]
  have hsy : Zv α ≤ stab α' := by
    apply hA.Zv_le_stab_of_dist_le
    rw [hc.dist_eq, hc.bAt_eq]
  obtain ⟨ε, hαε, hβε⟩ := exists_adj_dist_eq hA.amalgam.gen (α := β) (δ := α') (d := b - 2)
    (by have := hc.dist_eq'; omega)
  have hε : ε ∈ nbrs α' := hαε
  have hdαε : dist α ε ≤ b - 1 := by
    have h1 := dist_triangle_of_adj hadj ε
    have h2 : dist α β = 1 := dist_eq_one_iff_adj.mpr hadj
    omega
  have hε1 : ∀ δ ∈ nbrs α, Zv δ ≤ Qv ε := by
    intro δ hδ
    refine no_D_end F hT3 (vtype_nbr_false hvα hδ) ?_
    have h1 := dist_triangle_of_adj (show (graph _ _ _).Adj δ α from (mem_nbrs_symm hδ)) ε
    have h2 : dist δ α = 1 := dist_eq_one_iff_adj.mpr (mem_nbrs_symm hδ)
    omega
  have hZαε : Zv α ≤ Qv ε := Zv_le_Qv_of_dist_lt (by rw [hc.bAt_eq]; omega)
  have hV2α : ∀ a ∈ Zv α, a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv α).2 a ha
  have hV2α' : ∀ a ∈ Zv α', a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv α').2 a ha
  have hε2 : ∀ q ∈ Qv ε, ∃ a ∈ Zv α, ∃ u ∈ Qv α', q = a * u :=
    Qv_le_mul_of_index4 F hvα' hε hsy (hZαε.trans (pCoreOf_le 2 (stab ε)))
      (isPGroup_two_of_sq_gen hV2α) hrel1
  have hNN : Zv α' ≤ NN hA α := Zv_le_NN hA α α' ε hε1 hε2 hsx
  have hNs : NN hA α ≤ stab α := fun n hn => (mem_NN hA).mp hn |>.1
  have hNn : ∀ n ∈ NN hA α, ∀ g ∈ stab α, g * n * g⁻¹ ∈ NN hA α :=
    fun n hn g hg => NN_normal hA α hn hg
  have hNQ : ¬ NN hA α ≤ Qv α := fun h => hnot (hNN.trans h)
  have hEx := inf_centralizer_eq_inf_Qv F (hfaith α') hsy
  have hHyp : T3Hyp α (NN hA α) (Zv α') :=
    { vt := hvα
      Ns := hNs
      Nn := hNn
      big := exists_mul_Q_of_normal F hvα hNs hNn hNQ
      comm := fun δ hδ z hz n hn =>
        ((mem_NN hA).mp hn).2 δ hδ z hz
      Ax := hsx
      A2 := isPGroup_two_of_sq_gen fun u hu => Subtype.ext (by
        simpa using hV2α' _ (Subgroup.mem_subgroupOf.mp hu))
      Ant := exists_noncomm_of_not_le F hEx hc.not_le
      idx := by rw [hEx, hrel1, hrel2] }
  exact false_of_Zv_le F hvα hβ (hfaith β) (hHyp.Zv_le F hβ)

end Main

end CFSG.Quasithin.Kleidman.F204
