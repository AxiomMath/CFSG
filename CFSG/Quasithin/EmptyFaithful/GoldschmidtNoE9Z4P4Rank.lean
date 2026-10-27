module

public import CFSG.Quasithin.EmptyFaithful.S14612GB1
public import CFSG.Quasithin.EmptyFaithful.S14612GB0a
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Pl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Cen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Rank

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9z4_rank (h35 : Lemma1435) (h5 : Stage1461Five) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) :
    4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
  classical
  have hcls : ClassAutShapeStmt := classAutShapeStmt
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hHZ : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hHG.trans S.normalizer_Z.ge
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hYU : uK T M H ⊔ quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
    uK_sup_Z_le_conjClosure T M H
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact S146T.comm_Z (hHG (pCoreOf_le 2 H hq)) hz
  have hNY : H ≤ Subgroup.normalizer
      ((uK T M H ⊔ quasithinOmegaOneCenter T : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨mem_normalizer_commutator_P14 (hHU hg) (Subgroup.le_normalizer hg), hHZ hg⟩
  have hNE : H ≤ Subgroup.normalizer (((uK T M H ⊔ quasithinOmegaOneCenter T) ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
    intro g hg
    refine mem_normalizer_of_conjSub_eq' ?_
    rw [conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hg),
      conjSub_eq_of_mem_normalizer (hNY hg)]
  have hE : (uK T M H ⊔ quasithinOmegaOneCenter T) ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) = quasithinOmegaOneCenter T := by
    rcases shape_irreducible hcls h35 S hred hshape _ (le_inf le_sup_right hZC) inf_le_left hNE
      with h | h
    · exact h
    · exfalso
      have hle : (uK T M H ⊔ quasithinOmegaOneCenter T) ⊓
          Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
        inf_le_right
      rw [h] at hle
      exact S.not_uK_le_centralizer_pCoreOf h5 hred (le_sup_left.trans hle)
  have hcard : Nat.card ↥(uK T M H ⊔ quasithinOmegaOneCenter T) = 2 ^ 5 :=
    shape_card_uK_Z hcls h35 S hred hshape
  have hrelY : (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex
      (uK T M H ⊔ quasithinOmegaOneCenter T) = 16 := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hE]
    have h2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T)
      (uK T M H ⊔ quasithinOmegaOneCenter T)
    rw [inf_eq_left.mpr le_sup_right, S.card_Z, hcard] at h2
    omega
  have hUp : IsPGroup 2 ↥(conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hne : (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) ≠ 0 :=
    (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card _ _) Nat.card_pos).ne'
  have hle := Subgroup.relIndex_le_of_le_right hYU hne
  rw [hrelY, HypF98.relIndex_eq_two_pow_mIdx hUp] at hle
  by_contra hlt
  push Not at hlt
  have h3 : 2 ^ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) ≤
      2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Rank

end CFSG.Quasithin
