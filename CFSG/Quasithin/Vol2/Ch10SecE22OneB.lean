module

public import CFSG.Quasithin.Vol2.Ch10SecE22One
public import CFSG.Quasithin.Vol2.Ch10SecBInner3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem commutator_conjugate_thompsonJ {t : G} (ht : t ∈ T) :
    ⁅CFSG.conjugate L t, thompsonJ T⁆ = CFSG.conjugate ⁅L, thompsonJ T⁆ t := by
  have hJ : CFSG.conjugate (thompsonJ T) t = thompsonJ T :=
    SecA.conjugate_eq_self_iff.mpr
      (normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer ht))
  rw [SecA.conjugate_eq_map, SecA.conjugate_eq_map, Subgroup.map_commutator,
    ← SecA.conjugate_eq_map, ← SecA.conjugate_eq_map, hJ]

theorem fsuL0_eq_commutator_thompsonJ
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1012 : Ch10.Stmt10_1_2) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hyp : Hyp10 G T L I) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuV T I : Set G)) :
    fsuL0 T L = ⁅fsuL0 T L, thompsonJ T⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hloc := hyp.fsu.maximal.1
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJL : thompsonJ T ≤ Subgroup.normalizer (L : Set G) :=
    (h1012 G T L I hyp).2.1.trans inf_le_right
  have hJL0 : thompsonJ T ≤ Subgroup.normalizer (fsuL0 T L : Set G) :=
    hJT.trans (SecA.le_fsuM T L)
  have hLJ : ⁅L, thompsonJ T⁆ ≤ L := commutator_le_of_le_normalizer hJL
  have hLt := commutator_conjugate_thompsonJ (L := L) ht
  have hL0 := SecA.fsuL0_eq_sup h37 h38 hyp ht htn
  by_cases heq : ⁅L, thompsonJ T⁆ = L
  · refine le_antisymm ?_ (commutator_le_of_le_normalizer hJL0)
    calc fsuL0 T L = ⁅L, thompsonJ T⁆ ⊔ ⁅CFSG.conjugate L t, thompsonJ T⁆ := by
          rw [hL0, hLt, heq]
      _ ≤ ⁅fsuL0 T L, thompsonJ T⁆ := sup_le
          (Subgroup.commutator_mono (SecA.le_fsuL0 T L) le_rfl)
          (Subgroup.commutator_mono (SecA.conjugate_le_fsuL0 ht) le_rfl)
  · exfalso
    have hO := SecB.le_pCoreOf_of_normal_of_ne hLJ (le_normalizer_commutator_left L _)
      (SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
        hyp.fsu.faithful hyp.not_normal) (SecA.perfect_L hloc) heq
    set N := pCoreOf 2 (fsuL0 T L ⊔ T)
    have hL0N : pCoreOf 2 (fsuL0 T L) ≤ N := by
      rw [← SecA.inf_pCoreOf_eq_of_normal le_sup_left
        (sup_le Subgroup.le_normalizer (SecA.le_fsuM T L))]
      exact inf_le_right
    have hLN : pCoreOf 2 L ≤ N :=
      (SecA.inf_pCoreOf_fsuL0 hloc).symm.le.trans (inf_le_right.trans hL0N)
    have hLtN : pCoreOf 2 (CFSG.conjugate L t) ≤ N :=
      (SecA.conjugate_inf_pCoreOf_fsuL0 hloc ht).symm.le.trans (inf_le_right.trans hL0N)
    have hOt : ⁅CFSG.conjugate L t, thompsonJ T⁆ ≤ pCoreOf 2 (CFSG.conjugate L t) := by
      rw [hLt, SecA.pCoreOf_conjugate]
      exact SecA.conjugate_mono hO t
    have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (N : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hJN : thompsonJ T ≤ Subgroup.normalizer (N : Set G) :=
      (hJT.trans le_sup_right).trans hHN
    have hX : ∀ X : Subgroup G, X ≤ fsuL0 T L → ⁅X, thompsonJ T⁆ ≤ N →
        X ≤ Subgroup.normalizer ((thompsonJ T ⊔ N : Subgroup G) : Set G) := by
      intro X hXL0 hXN x hx
      refine mem_normalizer_sup_of_commutator_mem hJN (hHN (Subgroup.mem_sup_left (hXL0 hx)))
        (fun j hj => ?_) (fun j hj => ?_)
      · have := hXN (Subgroup.commutator_mem_commutator hx hj)
        rwa [commutatorElement_def] at this
      · have := hXN (Subgroup.commutator_mem_commutator (X.inv_mem hx) hj)
        rwa [commutatorElement_def, inv_inv] at this
    have hTY : T ≤ Subgroup.normalizer ((thompsonJ T ⊔ N : Subgroup G) : Set G) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp
          (normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer hs)),
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hHN (Subgroup.mem_sup_right hs))]
    have hHY : fsuL0 T L ⊔ T ≤ Subgroup.normalizer ((thompsonJ T ⊔ N : Subgroup G) : Set G) := by
      refine sup_le ?_ hTY
      rw [hL0]
      exact sup_le (hX L (SecA.le_fsuL0 T L) (hO.trans hLN))
        (hX _ (SecA.conjugate_le_fsuL0 ht) (hOt.trans hLtN))
    have hYT : thompsonJ T ⊔ N ≤ T :=
      sup_le hJT (SecA.pCoreOf_le_of_sylow hyp.fsu.sylow le_sup_right)
    have hYN : thompsonJ T ⊔ N ≤ N :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYT.trans le_sup_right) hHY
        (hyp.fsu.sylow.1.to_le hYT)
    obtain ⟨-, -, h3⟩ := h3228 G T L I hyp.fsu
    apply hJ
    have hN : N ≤ Subgroup.centralizer (fsuV T I : Set G) := by
      rw [show N = T ⊓ Subgroup.centralizer (fsuV T I : Set G) from h3]
      exact inf_le_right
    exact (le_sup_left.trans hYN).trans hN

theorem stmt10_2_2_one
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h1012 : Ch10.Stmt10_1_2) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) :
    (fsuL0 T L = ⁅fsuL0 T L, thompsonJ T⁆ ∧ ((∃ n, Ch10.Case10_1_1One T L I n) ∨
      Ch10.Case10_1_1Two T L I ∨ Ch10.Case10_1_1Three T L I)) ∧
      ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have hJ := not_thompsonJ_le_of_commutator_ne_bot hC58 h317 h37 h38 h331 h3228 hyp hH hZH
  have hJV : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := fun h =>
    hJ (h.trans (Subgroup.centralizer_le (SecA.fsuV_le_fsuVM T L I)))
  refine ⟨⟨fsuL0_eq_commutator_thompsonJ h37 h38 h1012 h3228 hyp hJ, ?_⟩, hJV⟩
  by_contra h
  exact hJV ((h1012 G T L I hyp).1 h).2

end CFSG.Quasithin.Vol2.Ch10.SecE
