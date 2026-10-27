module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112sa_S_inf_P1' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    S ⊓ f112saP1' L1 L2 S = S ⊓ f112saK L1 L2 S := by
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxS, hxP⟩
    refine ⟨hxS, ?_⟩
    rw [← f112sa_P1'_inf_bigB hF]
    exact ⟨hxP, hSB hxS⟩
  · refine inf_le_inf_left S ?_
    rw [f112saK, f112saP1']
    exact sup_le ((f112sa_X1_le_oTwoRes L1 L2 S).trans le_sup_left) le_sup_right

theorem f112sa_S_inf_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    S ⊓ f112saP2' L1 L2 S = S ⊓ f112saK L1 L2 S := by
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxS, hxP⟩
    refine ⟨hxS, ?_⟩
    rw [← f112sa_P2'_inf_bigB hF]
    exact ⟨hxP, hSB hxS⟩
  · refine inf_le_inf_left S ?_
    rw [f112saK, f112saP2']
    exact sup_le le_sup_right ((f112sa_X2_le_oTwoRes L1 L2 S).trans le_sup_left)

theorem f112sa_T_sylow_P1'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (f112saP1' L1 L2 S) := by
  have hSyl : IsSylowTwoOf S (f112P1 L1 L2 S) :=
    F112W.isSylowTwoOf_parabolic hR
  have hle : S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    (((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)).trans
        (f112sa_P1_le_normalizer_P1' hF))
  have h := F7.isSylowTwoOf_inf_normal hSyl (f112sa_P1'_le_P1 hF) hle
  rwa [f112sa_S_inf_P1' hF] at h

theorem f112sa_T_sylow_P1' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (f112saP1' L1 L2 S) :=
  f112sa_T_sylow_P1'_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_T_sylow_P2'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (f112saP2' L1 L2 S) := by
  have hSyl : IsSylowTwoOf S (f112P2 L1 L2 S) :=
    F112W.isSylowTwoOf_parabolic' hR
  have hle : S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    (((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)).trans
        (f112sa_P2_le_normalizer_P2' hF))
  have h := F7.isSylowTwoOf_inf_normal hSyl (f112sa_P2'_le_P2 hF) hle
  rwa [f112sa_S_inf_P2' hF] at h

theorem f112sa_T_sylow_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (f112saP2' L1 L2 S) :=
  f112sa_T_sylow_P2'_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_T_sylow_K_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (f112saK L1 L2 S) := by
  have hSyl : IsSylowTwoOf S (f112P1 L1 L2 S) := F112W.isSylowTwoOf_parabolic hR
  have hKle : f112saK L1 L2 S ≤ f112P1 L1 L2 S :=
    sup_le ((f112sa_X1_le_oTwoRes L1 L2 S |>.trans (oTwoRes_le L1)).trans le_sup_left)
      ((f112sa_X2_le_bigB L1 L2 S).trans le_sup_right)
  have hKN : S ≤ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_K hF)
  exact F7.isSylowTwoOf_inf_normal hSyl hKle hKN

theorem f112sa_T_sylow_K {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (f112saK L1 L2 S) :=
  f112sa_T_sylow_K_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_charTwo_P1'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) : CharTwo (f112saP1' L1 L2 S) :=
  A4.charTwo_of_normal (f112sa_P1'_le_P1 hF) (f112sa_P1_le_normalizer_P1' hF)
    (f112_charTwo_P1_of_hyp111R hR)

theorem f112sa_charTwo_P1' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) : CharTwo (f112saP1' L1 L2 S) :=
  f112sa_charTwo_P1'_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_charTwo_P2'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) : CharTwo (f112saP2' L1 L2 S) :=
  A4.charTwo_of_normal (f112sa_P2'_le_P2 hF) (f112sa_P2_le_normalizer_P2' hF)
    (f112_charTwo_P2_of_hyp111R hR)

theorem f112sa_charTwo_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) : CharTwo (f112saP2' L1 L2 S) :=
  f112sa_charTwo_P2'_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_core_free_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    bigB L1 L2 S ⊓ Subgroup.centralizer (f112saP1' L1 L2 S : Set H) ⊓
        Subgroup.centralizer (f112saP2' L1 L2 S : Set H) = ⊥ := by
  let C : Subgroup H :=
    bigB L1 L2 S ⊓ Subgroup.centralizer (f112saP1' L1 L2 S : Set H) ⊓
      Subgroup.centralizer (f112saP2' L1 L2 S : Set H)
  change C = ⊥
  have hCB : C ≤ bigB L1 L2 S := inf_le_left.trans inf_le_left
  have hBG0 : bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (F1.borelOf_le L1 S).trans (le_sup_left.trans le_sup_left)
    · exact (F1.borelOf_le L2 S).trans (le_sup_right.trans le_sup_left)
    · exact le_sup_right
  have hCG0 : C ≤ L1 ⊔ L2 ⊔ S := hCB.trans hBG0
  have hcent1 : C ≤ Subgroup.centralizer (f112saP1' L1 L2 S : Set H) :=
    inf_le_left.trans inf_le_right
  have hcent2 : C ≤ Subgroup.centralizer (f112saP2' L1 L2 S : Set H) := inf_le_right
  have hBEα : bigB L1 L2 S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S).trans
      (f112sa_P1_le_normalizer_P1' hF)
  have hBEβ : bigB L1 L2 S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S).trans
      (f112sa_P2_le_normalizer_P2' hF)
  have hBcent1 : bigB L1 L2 S ≤
      Subgroup.normalizer (Subgroup.centralizer (f112saP1' L1 L2 S : Set H) : Set H) :=
    hBEα.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (f112saP1' L1 L2 S))
  have hBcent2 : bigB L1 L2 S ≤
      Subgroup.normalizer (Subgroup.centralizer (f112saP2' L1 L2 S : Set H) : Set H) :=
    hBEβ.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (f112saP2' L1 L2 S))
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (C : Set H) := by
    intro b hb
    exact A4.mem_normalizer_inf
      (A4.mem_normalizer_inf (Subgroup.le_normalizer hb) (hBcent1 hb)) (hBcent2 hb)
  have hO1cent : oTwoRes L1 ≤ Subgroup.centralizer (C : Set H) := by
    rw [Subgroup.le_centralizer_iff]
    exact hcent1.trans
      (Subgroup.centralizer_le fun x hx =>
        (le_sup_left : oTwoRes L1 ≤ f112saP1' L1 L2 S) hx)
  have hO2cent : oTwoRes L2 ≤ Subgroup.centralizer (C : Set H) := by
    rw [Subgroup.le_centralizer_iff]
    exact hcent2.trans
      (Subgroup.centralizer_le fun x hx =>
        (le_sup_left : oTwoRes L2 ≤ f112saP2' L1 L2 S) hx)
  have hO1N : oTwoRes L1 ≤ Subgroup.normalizer (C : Set H) :=
    hO1cent.trans (Subgroup.centralizer_le_normalizer (C : Set H))
  have hO2N : oTwoRes L2 ≤ Subgroup.normalizer (C : Set H) :=
    hO2cent.trans (Subgroup.centralizer_le_normalizer (C : Set H))
  have hSN : S ≤ Subgroup.normalizer (C : Set H) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans hBN
  have hL1 : L1 ≤ Subgroup.normalizer (C : Set H) :=
    (le_oTwoRes_sup_of_isSylowTwoOf hF.1.h1.sylow).trans
      (sup_le hO1N (inf_le_left.trans hSN))
  have hL2 : L2 ≤ Subgroup.normalizer (C : Set H) :=
    (le_oTwoRes_sup_of_isSylowTwoOf hF.1.h2.sylow).trans
      (sup_le hO2N (inf_le_left.trans hSN))
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (C : Set H) :=
    sup_le (sup_le hL1 hL2) hSN
  have hCN : (C.subgroupOf (L1 ⊔ L2 ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCG0).mpr hG0N
  have hCP1 : C ≤ f112P1 L1 L2 S := hCB.trans le_sup_right
  have hP1G0 : f112P1 L1 L2 S ≤ L1 ⊔ L2 ⊔ S :=
    sup_le (le_sup_left.trans le_sup_left) hBG0
  have hP1N : f112P1 L1 L2 S ≤ Subgroup.normalizer (C : Set H) := hP1G0.trans hG0N
  have hCharC : CharTwo C := A4.charTwo_of_normal hCP1 hP1N (f112_charTwo_P1_of_hyp111R hR)
  have hSub : IsSubnormal C (L1 ⊔ L2 ⊔ S) := A4.subnormal_of_normal hCG0 hCN
  have hO2 : pCoreOf 2 C ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    A4.pCoreOf_le_of_subnormal 2 hSub
  have hO2bot : pCoreOf 2 C = ⊥ := by
    rw [hF.1.o2] at hO2
    exact le_bot_iff.mp hO2
  have h := hCharC
  unfold CharTwo at h
  rw [hO2bot] at h
  have hle : C ≤ ⊥ := by
    refine (le_inf le_rfl ?_).trans h
    intro c _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    simp [hy1]
  exact le_bot_iff.mp hle

theorem f112sa_core_free {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    bigB L1 L2 S ⊓ Subgroup.centralizer (f112saP1' L1 L2 S : Set H) ⊓
        Subgroup.centralizer (f112saP2' L1 L2 S : Set H) = ⊥ :=
  f112sa_core_free_of_hyp111R hF.toW (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

end CFSG.Quasithin.F112R.St84
