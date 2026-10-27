module

public import CFSG.Quasithin.Vol2.Ch10SecC9S5d
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

theorem center_alt7 : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ := by
  have := alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(alternatingGroup (Fin 7)))
    with h | h
  · exact h
  · exfalso
    have ha : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have hb : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 3 ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    set a : ↥(alternatingGroup (Fin 7)) := ⟨_, ha⟩
    set b : ↥(alternatingGroup (Fin 7)) := ⟨_, hb⟩
    have hab := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b
    have h1 : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 3 * (Equiv.swap 0 1 * Equiv.swap 0 2) =
        Equiv.swap 0 1 * Equiv.swap 0 2 * (Equiv.swap 0 1 * Equiv.swap 0 3) :=
      congrArg Subtype.val hab
    revert h1
    decide

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem pCoreOf_J_le (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))) :
    pCoreOf 2 J ≤ Subgroup.centralizer (VI T L I J w : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))
  have hJX : pCoreOf 2 J ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer c.Tw_le_normalizer).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)
  have hV := (VI_props c.hyp c.w_mem_V c.isSylowTwoOf_sup hF).1
  exact hJX.trans (Subgroup.le_centralizer_iff.mp (hV.trans inf_le_right))

theorem isAltQuotient (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1026 : Stmt10_2_6)
    (h1027 : Stmt10_2_7) (hK8a : FactK8a) (hK8b : FactK8b)
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hQ : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (e : ↥(autI hVe J) ≃* ↥(alternatingGroup (Fin 7))) : IsAltQuotient J (oTwoZIn J) 7 := by
  have hC := c.centralizer_VI_le h37 h38 h1011 h1026 h1027 hK8a hK8b
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  have hJC : ¬ J ≤ Subgroup.centralizer (VI T L I J w : Set G) := fun h =>
    c.L_not_le_centralizer hC (c.le.trans h)
  obtain ⟨φ, hφ, hker⟩ := exists_quotient_oTwoZIn hVe hJN (c.pCoreOf_J_le hF) hJC hQ e center_alt7
  exact ⟨φ, hφ, hker⟩

theorem false_of_char (h1026 : Stmt10_2_6) {C : Subgroup G} (hC1 : C ≠ ⊥)
    (hCS : C ≤ baum (T ⊓ Subgroup.centralizer ({w} : Set G)))
    (hchar : (C.subgroupOf (baum (T ⊓ Subgroup.centralizer ({w} : Set G)))).Characteristic)
    (hN : J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤ Subgroup.normalizer (C : Set G)) :
    False := by
  have hyp := c.hyp
  have hwJ : w ∈ Subgroup.centralizer (thompsonJ T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.mp (c.claim.2.2.2.2.1 hj)
  have hSw : baum T ≤ T ⊓ Subgroup.centralizer ({w} : Set G) :=
    le_inf inf_le_left (baum_le_centralizer_of_mem (SecA.isElemAbelian_fsuVM hyp)
      (SecA.fsuVM_le_T hyp) c.w_mem_V hwJ)
  have hbeq : baum T = baum (T ⊓ Subgroup.centralizer ({w} : Set G)) :=
    baum_eq_of_le hSw inf_le_left
  rw [← hbeq] at hCS hchar
  have hTN : T ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Setup.Campbell.mem_normalizer_of_characteristic hchar hCS
      ((normalizer_le_normalizer_baum T) (Subgroup.le_normalizer hx))
  have hLN : L ≤ Subgroup.normalizer (C : Set G) := c.le.trans (le_sup_left.trans hN)
  have hL0 : fsuL0 T L ≤ Subgroup.normalizer (C : Set G) := conjClosure_le fun s hs l hl =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTN hs) (hLN hl)) (Subgroup.inv_mem _ (hTN hs))
  have hCp : IsPGroup 2 C := hyp.fsu.sylow.1.to_le (hCS.trans inf_le_left)
  have hO : pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := by
    intro hb
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hCp
    rw [hb] at this
    exact hC1 (le_bot_iff.mp this)
  have hNM := le_fsuM_of_le hyp h1026 (sup_le hL0 (inf_le_left.trans hTN)) hO
  exact c.not_le (le_sup_left.trans (hN.trans hNM))

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
