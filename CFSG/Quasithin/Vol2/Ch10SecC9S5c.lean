module

public import CFSG.Quasithin.Vol2.Ch10SecC9S4e
public import CFSG.Quasithin.Vol2.Ch10SecCFacts2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

namespace Conf

variable {T L I J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem fsuUL_le_L (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) : fsuUL T L I ≤ L := by
  rw [fsuUL, Subgroup.commutator_comm]
  exact commutator_le_left_of_le_normalizer ((fsuVM_le_Q c.hyp).trans
    (Q_le_T1 h37 h38 c.hyp h1011) |>.trans inf_le_right)

theorem VI_le_J (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) :
    VI T L I J w ≤ J := by
  have hV1L := c.fsuUL_le_L h37 h38 h1011
  refine conjClosure_le fun h hh z hz => ?_
  have hJN : J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer c.Tw_le_normalizer
  exact (Subgroup.mem_normalizer_iff.mp (hJN hh) z).mp (c.le (hV1L hz.1))

theorem commutator_VI_J (hV1 : fsuUL T L I ≤ VI T L I J w) :
    ⁅VI T L I J w, J⁆ = VI T L I J w := by
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  refine le_antisymm (commutator_le_left_of_le_normalizer hJN) ?_
  have hV1c : fsuUL T L I ≤ ⁅VI T L I J w, J⁆ :=
    calc fsuUL T L I = ⁅fsuUL T L I, L⁆ := (commutator_fsuUL_eq c.hyp).symm
      _ ≤ ⁅VI T L I J w, J⁆ := Subgroup.commutator_mono hV1 c.le
  have hN : J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      Subgroup.normalizer ((⁅VI T L I J w, J⁆ : Subgroup G) : Set G) :=
    SecA.le_normalizer_commutator (le_normalizer_VI T L I J w)
      (sup_le Subgroup.le_normalizer c.Tw_le_normalizer)
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) z).mp (hV1c hz.1)

theorem autI_ne (hC : Subgroup.centralizer (VI T L I J w : Set G) ≤ fsuM T L)
    (hVe : IsElemAbelian 2 (VI T L I J w)) : autI hVe L ≠ autI hVe J := by
  intro heq
  apply c.not_le
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  intro j hj
  have hφ : convI hVe ⟨j, hJN hj⟩ ∈ autI hVe L := heq ▸ convI_mem_autI hVe hj (hJN hj)
  obtain ⟨g, hgL, hg⟩ := (mem_autI hVe).1 hφ
  have h1 : convI hVe (g⁻¹ * ⟨j, hJN hj⟩) = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
  have h2 : (g : G)⁻¹ * j ∈ Subgroup.centralizer (VI T L I J w : Set G) :=
    (convI_eq_one_iff hVe _).1 h1
  have hgM : (g : G) ∈ fsuM T L := SecA.fsuL0_le_fsuM T L (SecA.le_fsuL0 T L hgL)
  have e : j = (g : G) * ((g : G)⁻¹ * j) := by group
  rw [e]
  exact (fsuM T L).mul_mem hgM (hC h2)

theorem s5Core (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1026 : Stmt10_2_6)
    (h1027 : Stmt10_2_7) (hK8a : FactK8a) (hK8b : FactK8b) (hq : ¬ CFSG.Open.IsQuasisimple ↥J)
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hI : CFSG.Open.IsQuasisimple ↥(autI hVe J)) :
    S5Core (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) (T ⊓ Subgroup.centralizer ({w} : Set G))
      J L (VI T L I J w) hVe := by
  have hyp := c.hyp
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hSQ := InternalSec.sqtkGroup_of_localSQTK hK (pCoreOf_centralizer_ne_bot c.w_ne_one c.w_sq)
  have hC := c.centralizer_VI_le h37 h38 h1011 h1026 h1027 hK8a hK8b
  have hJT : thompsonJ T ≤ T ⊓ Subgroup.centralizer ({w} : Set G) :=
    le_inf (B6.thompsonJ_le T) c.claim.2.2.2.2.1
  have hJeq := B6.thompsonJ_eq_of_le hJT inf_le_left
  refine ⟨InternalSec.sqtkGroup_mono hSQ (sup_le c.J_le inf_le_right), hF, c.isSylowTwoOf_sup,
    cComp_mem_of_le c.mem le_sup_left (sup_le c.J_le inf_le_right),
    sup_le Subgroup.le_normalizer c.Tw_le_normalizer, rfl, hq,
    (VI_props hyp c.w_mem_V c.isSylowTwoOf_sup hF).2.2, c.VI_le_J h37 h38 h1011, hI, ?_,
    c.L_mem_lFamily, c.le, (c.Tw_le_T1 h37 h38).trans inf_le_right,
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal, c.L_not_le_centralizer hC, c.autI_ne hC hVe⟩
  rw [hJeq]
  exact c.not_thompsonJ_le_centralizer h37 h38 h1026 hC

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
