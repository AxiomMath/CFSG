module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem424N
public import CFSG.Quasithin.Vol2.Ch4Sec4W443

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem conjClosure_le_M (s : Setting443 G T M L B Tp VB) : conjClosure L T ≤ M :=
  CFSG.Quasithin.conjClosure_le fun t ht l hl => by
    have hTN : T ≤ Subgroup.normalizer (M : Set G) := fun x hx =>
      Subgroup.le_normalizer (s.hyp.T_le hx)
    exact (Subgroup.mem_normalizer_iff.mp (hTN ht) l).mp (s.hyp.L_le hl)

theorem VB_le_T (s : Setting443 G T M L B Tp VB) : VB ≤ T := fun _ hv =>
  pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le s.hyp.sylow le_sup_right)
    (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).1

theorem pCoreOf_le_R (s : Setting443 G T M L B Tp VB) :
    pCoreOf 2 M ≤ pCoreOf 2 (conjClosure L T ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 M ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le s.hyp.sylow s.hyp.T_le)
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right) ?_
    (pCoreOf_isPGroup 2 M)
  exact (sup_le (conjClosure_le_M s) s.hyp.T_le).trans (le_normalizer_pCoreOf 2 M)

theorem VB_le_centralizer_pCoreOf (s : Setting443 G T M L B Tp VB) :
    VB ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := fun _ hv =>
  Subgroup.centralizer_le (pCoreOf_le_R s)
    (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).2.1

theorem VB_le_pCoreOf (s : Setting443 G T M L B Tp VB) : VB ≤ pCoreOf 2 M := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo s.hyp.sylow
  have hchar := s.hyp.qtke.2.1 M s.hyp.maxTwoLocal.1 ⟨S, hS ▸ s.hyp.T_le⟩
  exact fun v hv => hchar ⟨s.hyp.T_le (VB_le_T s hv), VB_le_centralizer_pCoreOf s hv⟩

theorem VB_le_centralizer (s : Setting443 G T M L B Tp VB) :
    VB ≤ Subgroup.centralizer (B : Set G) := by
  have h := s.hyp.VB_centralizes
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact h

theorem VB_le_normalizer (s : Setting443 G T M L B Tp VB) :
    VB ≤ Subgroup.normalizer (B : Set G) :=
  (VB_le_centralizer s).trans (Subgroup.centralizer_le_normalizer _)

theorem commutator_VB_oddCoreIn (s : Setting443 G T M L B Tp VB)
    (h448 : oddCoreIn (Subgroup.normalizer (B : Set G)) ≤
      M ⊓ Subgroup.normalizer (B : Set G)) :
    ⁅VB, oddCoreIn (Subgroup.normalizer (B : Set G))⁆ = ⊥ := by
  set O := oddCoreIn (Subgroup.normalizer (B : Set G)) with hO
  have hON : Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_oddCoreIn _
  have h1 : ⁅VB, O⁆ ≤ O :=
    commutator_le_right_of_le_normalizer ((VB_le_normalizer s).trans hON)
  have h2 : ⁅VB, O⁆ ≤ pCoreOf 2 M :=
    (Subgroup.commutator_mono (VB_le_pCoreOf s) le_rfl).trans
      (commutator_le_left_of_le_normalizer
        ((h448.trans inf_le_left).trans (le_normalizer_pCoreOf 2 M)))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := inf_eq_bot_of_isPGroup_two_of_odd (pCoreOf_isPGroup 2 M) (odd_card_oddCoreIn
    (Subgroup.normalizer (B : Set G)))
  exact le_bot_iff.mp (h3 ▸ le_inf h2 h1)

end CFSG.Quasithin.H13.Ch4.E443
