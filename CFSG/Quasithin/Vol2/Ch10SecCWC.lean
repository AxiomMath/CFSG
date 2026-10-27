module

public import CFSG.Quasithin.Vol2.Ch10SecC9S5e
public import CFSG.Quasithin.Background.C124AsmStmt

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem pCoreOf_JTw_ne_bot (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))) :
    pCoreOf 2 (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) ≠ ⊥ := by
  intro hb
  have hX : J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤ ⊥ := fun x hx => by
    rw [← hb]
    refine hF ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [hb, Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  exact c.mem.1 (le_bot_iff.mp (le_sup_left.trans hX))

theorem sqtkGroup_JTw (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))) :
    SQTKGroup ↥(J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) := by
  have := c.hyp.fsu.simple
  exact InternalSec.sqtkGroup_of_localSQTK
    (qtkeCore_of_cat c.hyp.fsu.nonabelian c.hyp.fsu.qtke).1 (c.pCoreOf_JTw_ne_bot hF)

theorem c124SQTK (h124 : C124StatementSQTK (G := G))
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1026 : Stmt10_2_6)
    (h1027 : Stmt10_2_7) (hK8a : FactK8a) (hK8b : FactK8b) (hq : ¬ CFSG.Open.IsQuasisimple ↥J)
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hA : IsAltQuotient J (oTwoZIn J) 7) :
    IsChiBlock (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) J ∨
      (QuasithinUnique.IsBlock2 (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) J ∧
        (CFSG.Quasithin.IsExcA7Block J ∨ IsAltBlockType J 6 ∨
          CFSG.Quasithin.IsHatA6Block J)) := by
  have hyp := c.hyp
  have hred := (VI_props hyp c.w_mem_V c.isSylowTwoOf_sup hF).2.2
  have hO := oddCoreIn_eq_bot h37 h38 hyp h1011 h1026 c.ht c.claim.1 c.claim.2.1 c.mem c.le
    c.normal
  have hJ2 := charTwo_of_not_isQuasisimple c.mem hq hO
  have hC := c.centralizer_VI_le h37 h38 h1011 h1026 h1027 hK8a hK8b
  have hVJ : ⁅VI T L I J w, J⁆ ≠ ⊥ := fun h => c.L_not_le_centralizer hC
    (c.le.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)))
  have hprod : ∀ x ∈ J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)),
      ∃ l ∈ J, ∃ s ∈ T ⊓ Subgroup.centralizer ({w} : Set G), x = l * s := by
    intro x hx
    have hx' : x ∈ (↑(J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ c.Tw_le_normalizer] at hx'
    obtain ⟨l, hl, s, hs, rfl⟩ := hx'
    exact ⟨l, hl, s, hs, rfl⟩
  rcases h124 _ _ (VI T L I J w) J _ 7 hF (c.sqtkGroup_JTw hF) hred c.isSylowTwoOf_sup hprod
      (cComp_mem_of_le c.mem le_sup_left (sup_le c.J_le inf_le_right)) hJ2 hVJ hA
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf c.isSylowTwoOf_sup) le_rfl
      (Or.inr (Or.inl rfl)) with ⟨C, hC1, hCS, hchar, hN⟩ | h | h
  · exact (c.false_of_char h1026 hC1 hCS hchar hN).elim
  · exact Or.inl h
  · exact Or.inr h

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
