module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Mbar
public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G]

structure Setup (T M : Subgroup G) : Prop where
  sylow : ∃ S : Sylow 2 G, (S : Subgroup G) = T
  inM : InM T M
  charTwo : CharTwo M
  solv : Group.IsSolvable M
  rank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p M ≤ 2
  elem : IsElemAbelian 2 (VZ T M)
  red : IsTwoReducedIn M (VZ T M)
  sylowM : IsSylowTwoOf T M
  cent : M ⊓ Subgroup.centralizer (VZ T M : Set G) = pCoreOf 2 M
  notJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)
  cz : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = T
  even : quasithinEvenCharacteristic G

theorem setup_of {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T)
    (h2 : Stmt1542Two G T) (h8 : Stmt1548 G T) (h11 : Stmt15411 G T) {M : Subgroup G}
    (hM : InM T M) : Setup T M := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hF : CharTwo M := hyp.qtke.2.1 M hM.1.1 ⟨S, hM.2⟩
  have hT : IsSylowTwoOf (S : Subgroup G) M := isSylowTwoOf_of_sylow S hM.2
  obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF
    (le_refl (quasithinOmegaOneCenter (S : Subgroup G)))
  obtain ⟨hO, -, -, hJ⟩ := h11 M hM
  refine ⟨⟨S, rfl⟩, hM, hF, h2 M hM, fun p hp hp2 => ?_, hel, hred, hT, hO.symm, ?_, h8,
    hyp.qtke.2.1⟩
  · exact (A1b.pRank_le_evenRank hp hp2 hM.1.1).trans hyp.qtke.2.2
  · intro hle
    apply hJ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hle

namespace Setup

variable {T M : Subgroup G} (h : Setup T M)
include h

theorem isPGroup : IsPGroup 2 T := by
  obtain ⟨S, rfl⟩ := h.sylow
  exact S.isPGroup'

theorem le_normalizer : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.red.2.1

theorem T_le : T ≤ M := h.inM.2

theorem isPGroup_inf : IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.cent]
  exact pCoreOf_isPGroup 2 M

theorem inf_le_T : M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ T := by
  rw [h.cent]
  exact pCoreOf_le_of_isSylowTwoOf h.sylowM

theorem V_le_T : VZ T M ≤ T :=
  (le_pCoreOf_of_isTwoReducedIn h.red).trans (pCoreOf_le_of_isSylowTwoOf h.sylowM)

theorem T_le_normalizer : T ≤ Subgroup.normalizer (VZ T M : Set G) :=
  h.T_le.trans h.le_normalizer

theorem rank_three : CFSG.Open.pRank 3 M ≤ 2 := h.rank 3 Nat.prime_three (by norm_num)

theorem exists_blocks : ∃ (𝓗 I : Finset (Subgroup (MulAut (IntMod (VZ T M) h.elem)))),
    E2.Blocks h.elem M 𝓗 I ∧ I.card ≤ 2 := by
  obtain ⟨𝓗, I, B⟩ := E2.exists_blocks h.elem h.red h.solv h.sylowM h.notJ
  exact ⟨𝓗, I, B, blocks_card_le_two B h.red h.isPGroup_inf h.rank_three⟩

theorem pCoreOf_ne_bot : pCoreOf 2 M ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP1, hP2, hMP⟩ := h.inM.1.1
  intro hbot
  apply hP1
  have hPM : P ≤ M := hMP ▸ Subgroup.le_normalizer
  have hle : P ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 hPM (hMP ▸ le_rfl) hP2
  rw [hbot] at hle
  exact le_bot_iff.mp hle

theorem pCoreOf_le_pCoreOf {H : Subgroup G} (hTH : T ≤ H) (hHM : H ≤ M) :
    pCoreOf 2 M ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_isSylowTwoOf h.sylowM).trans hTH)
    (hHM.trans (le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M)

variable {Y : Subgroup G}

omit h [Finite G] in
theorem basic (hY : IsYFamily T Y) :
    Y = oTwoUpper Y ∧ T ≤ Subgroup.normalizer (Y : Set G) ∧ pCoreOf 2 (Y ⊔ T) ≠ ⊥ := by
  rcases hY.1 with h' | h'
  · exact ⟨h'.1, h'.2.1, h'.2.2.1⟩
  · exact ⟨h'.1, h'.2.1, h'.2.2.1.2⟩

theorem le_thompsonJ (hY : IsYFamily T Y) (hYM : Y ≤ M) : Y ≤ thompsonJ M := by
  rw [← hY.2]
  refine (Subgroup.commutator_mono hYM (thompsonJ_le_thompsonJ_of_isSylowTwoOf h.sylowM)).trans ?_
  rw [Subgroup.commutator_le]
  intro m hm j hj
  rw [commutatorElement_def]
  have hmN : m ∈ Subgroup.normalizer (thompsonJ M : Set G) :=
    normalizer_le_normalizer_thompsonJ M (Subgroup.le_normalizer hm)
  exact (thompsonJ M).mul_mem ((Subgroup.mem_normalizer_iff.mp hmN j).mp hj)
    ((thompsonJ M).inv_mem hj)

omit h [Finite G] in
theorem not_le_of_isPGroup (hY : IsYFamily T Y) {P : Subgroup G} (hP : IsPGroup 2 P) :
    ¬ Y ≤ P := by
  intro hYP
  have h1 : (pCoreOf 2 Y).relIndex Y = 1 :=
    Subgroup.relIndex_eq_one.mpr (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
      (hP.to_le hYP))
  rcases hY.1 with h' | h'
  · obtain ⟨-, -, -, p, hp, -, -, hidx, -⟩ := h'
    have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    have hp3 : 1 < p ^ 3 := Nat.one_lt_pow three_ne_zero hp.one_lt
    rw [h1] at hidx
    omega
  · obtain ⟨-, -, -, p, hp, -, hidx⟩ := h'
    rw [h1] at hidx
    exact hp.one_lt.ne hidx

theorem autI_eq_oTwoUpper (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    autI h.elem Y = oTwoUpper (autI h.elem Y) := by
  have h1 : oTwoUpper (autI h.elem Y) = autI h.elem (oTwoUpper Y) :=
    A4.oTwoUpper_autOn (hYM.trans h.le_normalizer)
  rw [h1, ← (basic hY).1]

theorem autI_le_normalizer (hY : IsYFamily T Y) :
    autI h.elem T ≤
      Subgroup.normalizer ((autI h.elem Y : Subgroup _) :
        Set (MulAut (IntMod (VZ T M) h.elem))) := by
  intro x hx
  obtain ⟨g, hgT, rfl⟩ := (mem_autI h.elem).1 hx
  rw [mem_normalizer_iff_conjAut, conjAut_eq_map]
  have hgN : (g : G) ∈ Subgroup.normalizer (VZ T M : Set G) := g.2
  have e := autI_cjSub h.elem hgN Y
  rw [show (⟨(g : G), hgN⟩ : Subgroup.normalizer (VZ T M : Set G)) = g from rfl] at e
  rw [e, cjSub_eq_of_mem_normalizer ((basic hY).2.1 hgT)]

theorem autI_ne_bot (hY : IsYFamily T Y) (hYM : Y ≤ M) : autI h.elem Y ≠ ⊥ := by
  intro hbot
  rw [autI_eq_bot_iff h.elem (hYM.trans h.le_normalizer)] at hbot
  exact not_le_of_isPGroup hY h.isPGroup_inf (le_inf hYM hbot)

theorem autI_le_thompsonJ (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    autI h.elem Y ≤ autI h.elem (thompsonJ M) :=
  autI_mono h.elem (h.le_thompsonJ hY hYM)

theorem eq_psi (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    Y = psi h.elem h.le_normalizer (autI h.elem Y) :=
  eq_psi_autI h.elem h.le_normalizer hYM (basic hY).1
    (h.inf_le_T.trans (basic hY).2.1) h.isPGroup_inf

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
