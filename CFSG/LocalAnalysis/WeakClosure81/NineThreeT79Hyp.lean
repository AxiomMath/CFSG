module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79HypA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_kSub_barV (h : Nine3T79Setup V T A K S X p g x) :
    kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g) = ⊤ := by
  refine le_antisymm le_top ?_
  have hmap : (⊤ : Subgroup (nine3G1 V K g)) ≤
      kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g) := by
    calc (⊤ : Subgroup (nine3G1 V K g))
        = ((⊤ : Subgroup ↥(nineH0 V K g)).map
            (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))) := by
          rw [Subgroup.map_top,
            MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      _ ≤ ((kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g)).comap
            (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g)))).map
            (QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g))) :=
          Subgroup.map_mono (nine3_iSup_dcal_map_le_kSub h)
      _ = kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g) :=
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact hmap

theorem nine3_hyp711 (h : Nine3T79Setup V T A K S X p g x) :
    Hyp711 (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g) where
  elemAbelian := nine3_elemAbelian_barV h
  ti := nine3_isTI_barV h
  noncyclic := by
    rw [nine3_card_barV h]
    exact h.hc.core.hyp7.2.1
  abelian := nine3_abelian_barE h
  le := le_top
  normal := (nine3_normal_barE h).comap (⊤ : Subgroup (nine3G1 V K g)).subtype
  mem := by
    have hD : V ∈ nine3Dcal V (nineH0 V K g) :=
      ⟨1, (nineH0 V K g).one_mem, (CFSG.Quasithin.conjSubgroup_one V).symm⟩
    exact nine3_dcal_map_mem_omegaSet h hD
  omega_le := fun _ _ => le_top
  iSub_le := nine3_iSub_le_pCoreOf_kSub_barV h
  pcore_le := by
    rw [nine3_kSub_barV h]
  jnormal := by
    rw [nine3_kSub_barV h, CFSG.Quasithin.B6.pCoreOf_top 2 (nine3G1 V K g)]
    exact (CFSG.pCore_normal (p := 2) (G := nine3G1 V K g)).comap
      (⊤ : Subgroup (nine3G1 V K g)).subtype
  oddCore := by
    rw [nine3_kSub_barV h, nine3_fusionOddCoreOf_top_eq (nine3G1 V K g)]
    exact nine3_fusionOddCore_quotient_eq_bot h
  transitive := by
    intro U hU
    obtain ⟨g', hg'U, -, -⟩ := mem_omegaSet.mp hU
    refine ⟨g', ?_, hg'U⟩
    rw [nine3_kSub_barV h]
    exact Subgroup.mem_top g'

end CFSG.LocalAnalysis.WeakClosure81
