module

public import CFSG.LocalAnalysis.WeakClosure81.W183FourOddShape
public import CFSG.LocalAnalysis.WeakClosure81.W183FourDefs
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch5
import CFSG.LocalAnalysis.WeakClosure81.W183Br1Base
import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
public import CFSG.LocalAnalysis.WeakClosure81.W18ASBasic
public import CFSG.LocalAnalysis.WeakClosure81.W19ModE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem w183fourodd_hasQuotShape {L : Subgroup G} {N : Set G}
    (h : (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧
            HasQuotShape L N (fun X _ => CFSG.Quasithin.F6.IsL2 p e X)) ∨
          (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
            ((p % 4 = 3 ∧ HasQuotShape L N (fun X _ => LieModel X .PSL 3 p 1)) ∨
              (p % 4 = 1 ∧ HasQuotShape L N (fun X _ => LieModel X .PSU 3 p 1))))) :
    HasQuotShape L N (fun X _ => OddShape X) := by
  rcases h with ⟨p, e, hp, hp2, h9, X, hX, φ, hs, hk, hP⟩ |
    ⟨p, hp, h5, ⟨h4, X, hX, φ, hs, hk, hP⟩ | ⟨h4, X, hX, φ, hs, hk, hP⟩⟩
  · exact ⟨X, hX, φ, hs, hk, Or.inl ⟨p, e, hp, hp2, h9, hP⟩⟩
  · exact ⟨X, hX, φ, hs, hk, Or.inr ⟨p, hp, h5, Or.inl ⟨h4, hP⟩⟩⟩
  · exact ⟨X, hX, φ, hs, hk, Or.inr ⟨p, hp, h5, Or.inr ⟨h4, hP⟩⟩⟩

theorem w183fourodd_three_dvd_relIndex {K L : Subgroup G}
    (hX : HasQuotShape L (K : Set G) (fun X _ => OddShape X)) : 3 ∣ K.relIndex L := by
  obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
  have hker : φ.ker = K.subgroupOf L := by
    ext k
    rw [MonoidHom.mem_ker, hk k, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
    Subgroup.card_top]
  exact w183fourodd_oddShape_three_dvd hP

theorem w183fourodd_conj_cases {L T : Subgroup G}
    (h : Set.ncard {X : Subgroup G | ∃ t ∈ T, X = conjSubgroup L t} ≤ 2) :
    (∀ t ∈ T, conjSubgroup L t = L) ∨
      ∃ t ∈ T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t := by
  classical
  by_cases hall : ∀ t ∈ T, conjSubgroup L t = L
  · exact Or.inl hall
  obtain ⟨t, ht⟩ := not_forall.mp hall
  obtain ⟨htT, hne⟩ := not_imp.mp ht
  refine Or.inr ⟨t, htT, hne, fun s hs => ?_⟩
  have h1 : L ∈ {X : Subgroup G | ∃ t ∈ T, X = conjSubgroup L t} := by
    refine ⟨1, T.one_mem, ?_⟩
    ext x
    simp [mem_conjSubgroup_iff]
  have hpair : ({L, conjSubgroup L t} : Set (Subgroup G)) ⊆
      {X : Subgroup G | ∃ t ∈ T, X = conjSubgroup L t} := by
    rintro X (rfl | rfl)
    · exact h1
    · exact ⟨t, htT, rfl⟩
  have hcard : Set.ncard {X : Subgroup G | ∃ t ∈ T, X = conjSubgroup L t} ≤
      Set.ncard ({L, conjSubgroup L t} : Set (Subgroup G)) := by
    rw [Set.ncard_pair (Ne.symm hne)]
    exact h
  have heq := Set.eq_of_subset_of_ncard_le hpair hcard (Set.toFinite _)
  have hmem : conjSubgroup L s ∈ ({L, conjSubgroup L t} : Set (Subgroup G)) := by
    rw [heq]
    exact ⟨s, hs, rfl⟩
  rcases hmem with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem w183fourodd_le_normalizer {L T H : Subgroup G} (hLT : L ⊔ T = H)
    (h : ∀ t ∈ T, conjSubgroup L t = L) : H ≤ Subgroup.normalizer (L : Set G) := by
  rw [← hLT]
  refine sup_le Subgroup.le_normalizer ?_
  intro t ht
  rw [Subgroup.mem_set_normalizer_iff]
  intro l
  have h1 : l ∈ conjSubgroup L t ↔ t * l * t⁻¹ ∈ L := mem_conjSubgroup_iff
  rw [h t ht] at h1
  exact h1

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem false_of_fourOdd (h210 : Asch2_10) (h64o : Asch6_4Odd) (h65o : Asch6_5Odd)
    (h162 : W3Thm162Gt2 G) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (c : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i)
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => OddShape X)) {g : G}
    (hgK : ¬ vInH V H g ≤ kerMV V H) (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g)) : False := by
  classical
  have hbase : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    exact ⟨X, hXg, φ, hs, hk, w183fourodd_oddShape_simple_nonab hP⟩
  have hr : CFSG.Open.pRank 3 H ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 H]
    exact (not_concl182_iff.mp h2).1.1
  have h3 : 3 ∣ (kerMV V H).relIndex L := w183fourodd_three_dvd_relIndex hX
  have hle2 := h210 G H D.T (kerMV V H) L c.hyp.kgroup c.hyp.isSylowIn_T hr hL h3 hLT
  have hN : calNIn H D.T = {H ⊓ D.M} := c.calNIn_eq_AS h5_11 h5_13
  have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
    hgK ((le_inf (inf_le_right : vInH V H g ≤ H) hle).trans
      c.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
  obtain ⟨-, hA4⟩ := four_le_card_img M inf_le_right hab hA
  have hAH : M.img (vInH V H g) ≤ M.img H := M.img_mono inf_le_right
  have hA4' : 4 ≤ Nat.card ↥(M.img (vInH V H g)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv) ▸ hA4
  have hAmem : M.img (vInH V H g) ∈ Ctx188.packFamilyU D V H i M := ⟨g, hgam, rfl⟩
  have hshape' : OddShape ↥(M.img L) :=
    x.br1_shape_transport M hK hL.2.2.1
      (fun X Y _ _ e h => w183fourodd_oddShape_of_mulEquiv e h) hX
  rcases w183fourodd_conj_cases hle2 with hnorm | ⟨t, htT, hne, hall⟩
  · have hLn : H ≤ Subgroup.normalizer (L : Set G) := w183fourodd_le_normalizer hLT hnorm
    obtain ⟨hLY, hnormY, hsimple, hnonab, hcent⟩ :=
      x.br1_comp_base M hK hL.2.2.1 hLn hLT hbase
    exact br1_odd_false_one h64o h65o (x.br2Common M hN).toBr1Base.h131 hLY hnormY hcent hsimple
      hnonab hshape' hAmem hA4'
  · have htwo := x.br1_twoComp M hK hL hLT hbase htT hne hall
    exact br1_odd_false_two h64o h65o (x.br2Common M hN) htwo hshape' hAmem hA4'

end MinCex183

theorem fourOdd_of_inputs (h210 : Asch2_10) (h64o : Asch6_4Odd) (h65o : Asch6_5Odd) :
    FourOdd G := by
  intro h162 _ _ h5_11 _ h5_13 D V₀ V H i c h2 hK hshape g _ hgK hgi hA
  obtain ⟨L, hL, hLT, hsh⟩ := hshape
  exact c.false_of_fourOdd h210 h64o h65o h162 h5_11 h5_13 h2 hK hL hLT
    (w183fourodd_hasQuotShape hsh) hgK hgi hA

end CFSG.LocalAnalysis.WeakClosure81

end
