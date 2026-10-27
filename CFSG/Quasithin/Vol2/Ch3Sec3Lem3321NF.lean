module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GExt
public import CFSG.Quasithin.Vol2.Ch3Sec3NFSite
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321WH

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement IsMulCommutative

section Pw

open scoped Pointwise

theorem sup_inf_eq_inf_sup_of_le_normalizer {G : Type} [Group G] {L T C : Subgroup G}
    (hTC : T ≤ C) (hTL : T ≤ Subgroup.normalizer (L : Set G)) : L ⊓ C ⊔ T = (L ⊔ T) ⊓ C := by
  refine le_antisymm (sup_le (inf_le_inf_right C le_sup_left) (le_inf le_sup_right hTC))
    (fun x hx => ?_)
  obtain ⟨hxLT, hxC⟩ := hx
  have hxLT' : x ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
    exact hxLT
  obtain ⟨l, hl, t, ht, rfl⟩ := hxLT'
  have hlC : l ∈ C := by
    have := C.mul_mem hxC (C.inv_mem (hTC ht))
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hl, hlC⟩) (Subgroup.mem_sup_right ht)

end Pw

theorem inH_sup_of_le {G : Type} [Group G] [Finite G] {T M L D P : Subgroup G}
    (h : Hyp331 G T M L D) (hPL : P ≤ L) : InH T (P ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_sup_right, fun hbot => h.toSetup331.pCoreOf_ne_bot ?_⟩
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hle : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (P ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      ((sup_le_sup_right hPL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
  rw [hbot] at hle
  exact le_bot_iff.1 hle

namespace L3321

theorem step3_3_21gExt_of_on (h9 : Stmt3_3_9) (h13 : Stmt3_3_13LTOn Site3321a2) (h14 : Stmt3_3_14)
    (hGA : GriessAllModelsStatement) (hd : Step3_3_21d) : Step3_3_21gExt := by
  intro G _ _ T M L D h ⟨e⟩ hc hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hout
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨α, hαs, hαk, hαU, hCZ⟩ := exists_alpha_ext h9 h14 hGA h e hmod
  have hW := nonempty_wreath hαs hαk hTL h.sylow.1 hαU hout
  rw [← hCZ] at hW
  set H := L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T with hH
  have hInH : InH T H := by
    refine ⟨le_sup_right, fun hbot => h.toSetup331.pCoreOf_ne_bot ?_⟩
    have hOT : pCoreOf 2 (L ⊔ T) ≤ T :=
      EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
    have hle : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
        ((sup_le_sup_right (inf_le_left :
          L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ L) T).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  have hHeq : H = (L ⊔ T) ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    sup_inf_eq_inf_sup_of_le_normalizer
      (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T) hTL
  have hDH := h13 G T M L D H h ⟨hTL, ⟨e⟩, hc, hmod, hout, hHeq⟩ hInH
    (sup_le_sup_right inf_le_left T) hW
  have hDR : D ≤ Subgroup.normalizer ((pCoreOf 2 H) : Set G) := fun d hd =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (hDH hd)
  exact Hyp331.not_D_le h (hDR.trans (hd G T M L D h ⟨e⟩ ⟨hc, Or.inl hmod⟩))

end L3321

end CFSG.Quasithin.H13
