module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs
public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

theorem Sec5Hyp.m0Of_le_M (hS : Sec5Hyp M V) : m0Of M V ≤ M := by
  unfold m0Of
  exact iSup₂_le fun U hU => (hS.le_M_of_mem_sigmaSet hU).1

theorem le_m0Of_of_mem_sigmaSet {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    U ≤ m0Of M V :=
  le_iSup₂ (f := fun U (_ : U ∈ sigmaSet M V) => U) U hU

theorem Hyp.le_normalizer_m0Of (h : Hyp M V) :
    M ≤ Subgroup.normalizer (m0Of M V : Set G) := by
  intro m hm
  rw [mem_normalizer_iff_conjSubgroup_eq, ← m0Of_conjSubgroup m,
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hm),
    conjSubgroup_eq_self_iff.mpr (h.le_normalizer hm)]

theorem Sec5Hyp.imgQ_m0Of_normal (hS : Sec5Hyp M V) :
    (imgQ M (m0Of M V)).Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hS.m0Of_le_M).mpr
    hS.toRootHyp.toHyp.le_normalizer_m0Of).map (QuotientGroup.mk' (pCore 2 ↥M))
      (QuotientGroup.mk'_surjective _)

theorem Sec6Hyp.mk_eq_one_iff (hS : Sec6Hyp M V) (x : ↥M) :
    QuotientGroup.mk' (pCore 2 ↥M) x = 1 ↔ (x : G) ∈ Pc M V := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hS.sec5.Pc_subgroupOf hS.ne,
    Subgroup.mem_subgroupOf]

theorem mem_imgQ_iff {U : Subgroup G} {z : MBar M} :
    z ∈ imgQ M U ↔ ∃ x : ↥M, (x : G) ∈ U ∧ QuotientGroup.mk' (pCore 2 ↥M) x = z := by
  simp [imgQ, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mk_mem_imgQ {U : Subgroup G} {x : ↥M} (hx : (x : G) ∈ U) :
    QuotientGroup.mk' (pCore 2 ↥M) x ∈ imgQ M U :=
  Subgroup.mem_map.mpr ⟨x, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩

theorem imgQ_mono {U U' : Subgroup G} (h : U ≤ U') : imgQ M U ≤ imgQ M U' :=
  Subgroup.map_mono fun x hx => h (Subgroup.mem_subgroupOf.mp hx)

theorem isPGroup_conj_Pc (M V : Subgroup G) (g : G) :
    IsPGroup 2 (conjSubgroup g (Pc M V)) :=
  ((inSubgroup_pCore_two M).1.to_le inf_le_left).map (MulAut.conj g).toMonoidHom

theorem conjSubgroup_Pc_le_centralizer (M V : Subgroup G) (g : G) :
    conjSubgroup g (Pc M V) ≤ Subgroup.centralizer (conjSubgroup g V : Set G) := by
  rw [← Pc_conjSubgroup]
  exact inf_le_right

theorem Sec5Hyp.mem_normalizer_conj_Pc (hS : Sec5Hyp M V) (g : G) {u : G}
    (hu : u ∈ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    u ∈ Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) := by
  have hR := (hS.root g).toHyp
  have huM : u ∈ conjSubgroup g M :=
    hR.normalizer_eq ▸ Subgroup.centralizer_le_normalizer _ hu
  have h := hR.le_normalizer_Pc huM
  rwa [Pc_conjSubgroup] at h

theorem Sec5Hyp.conjSubgroup_le_lOf (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    conjSubgroup g V ≤ lOf M V g :=
  le_inf (conjSubgroup_mono hS.toRootHyp.toHyp.le_Pc)
    (hS.le_M_of_mem_sigmaSet hg).1

theorem Sec5Hyp.exists_conj_data (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    ∃ y ∈ hOf M V g, conjSubgroup g (Pc M V) = conjSubgroup y (Pc M V) ∧
      conjSubgroup g V = conjSubgroup y V ∧ conjSubgroup y V ≠ V ∧
      Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) =
        Pc M V ⊓ kOf V (hOf M V g) := by
  obtain ⟨y, hyH, hPy, hVy, -⟩ :=
    hS.toRootHyp.exists_mem_conj_eq_of_eq_sup (H := hOf M V g) le_sup_left rfl
  have hVy_mem : conjSubgroup y V ∈ sigmaSet M V := hVy ▸ hg
  have hyV : conjSubgroup y V ≠ V := ne_of_mem_sigmaSet hS.toRootHyp hVy_mem
  refine ⟨y, hyH, hPy, hVy, hyV, ?_⟩
  rw [hVy]
  exact (hS.shape hg).Pc_inf_centralizer_conj hS.toRootHyp hyH hyV

theorem Sec5Hyp.commutator_conj_Pc (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    ⁅conjSubgroup g (Pc M V), conjSubgroup g (Pc M V)⁆ = conjSubgroup g V := by
  rw [← Pc_conjSubgroup]
  exact (hS.conj g).commutator_Pc_eq_V ⟨V, hS.mem_sigmaSet_iff_self_mem.mp hg⟩

theorem Sec6Hyp.card_imgQ_mul_card_inf_Pc (hS : Sec6Hyp M V) {U : Subgroup G}
    (hUM : U ≤ M) :
    Nat.card (imgQ M U) * Nat.card ↥(U ⊓ Pc M V) = Nat.card U := by
  have hker : (QuotientGroup.mk' (pCore 2 ↥M)).ker ⊓ U.subgroupOf M =
      (U ⊓ Pc M V).subgroupOf M := by
    rw [QuotientGroup.ker_mk', ← hS.sec5.Pc_subgroupOf hS.ne]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact and_comm
  have hkerCard : Nat.card ↥((QuotientGroup.mk' (pCore 2 ↥M)).ker ⊓ U.subgroupOf M) =
      Nat.card ↥(U ⊓ Pc M V) := by
    rw [hker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hUM)).toEquiv
  have hU : Nat.card ↥(U.subgroupOf M) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
  have h := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf
    (f := QuotientGroup.mk' (pCore 2 ↥M)) (H := U.subgroupOf M)
  rw [hkerCard, hU] at h
  exact h.symm

theorem Sec6Hyp.card_imgQ_of_inf_Pc_eq_bot (hS : Sec6Hyp M V) {U : Subgroup G}
    (hUM : U ≤ M) (hUP : U ⊓ Pc M V = ⊥) :
    Nat.card (imgQ M U) = Nat.card U := by
  simpa [hUP] using hS.card_imgQ_mul_card_inf_Pc hUM

end CFSG.RankThree.GF2n.Tim81
