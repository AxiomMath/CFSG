module

public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.H13.L32NLem1434
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.H13.L32AHStr

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Lemma14_7_67_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    Subgroup.normalizer (L32A.kz T V : Set G) = L32A.hz T V ∧
      quasithinIsMaxTwoLocal (L32A.hz T V)

namespace L32A

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem isSylowTwoOf_of_le (h : Hyp147 G T L V) {X : Subgroup G} (hTX : T ≤ X) :
    QuasithinUnique.IsSylowTwoOf T X :=
  ⟨hTX, h.fsu.sylow.1, fun h2 =>
    h.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTX))⟩

theorem T_le_hz (h : Hyp147 G T L V) (h63 : Thm14_7_63) : T ≤ hz T V := by
  rw [(h63 G T L V h).2.2.1]
  exact le_sup_right

theorem isLocal_kz (h : Hyp147 G T L V) (h63 : Thm14_7_63) : quasithinIsLocal T (kz T V) := by
  obtain ⟨hHz, -, hHK, hC, -⟩ := h63 G T L V h
  rw [hHK] at hC
  refine ⟨h.fsu.sylow.1, hC, (isSylowTwoOf_of_le h le_sup_right).2.2, ?_⟩
  rw [← hHK]
  exact hHz.1.2

omit [Finite G] in
private theorem mem_normalizer_inf' {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  exact fun x => ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩,
    fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

theorem lemma14_7_67_three (h : Hyp147 G T L V) (h63 : Thm14_7_63) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One) : quasithinIsMaximalLocal T (kz T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hC, -⟩ := h63 G T L V h
  have hTH := T_le_hz h h63
  refine ⟨isLocal_kz h h63, fun I hI hKI => ?_⟩
  by_contra hne
  have hlt : kz T V < I := lt_of_le_of_ne hKI (Ne.symm hne)
  have hIc : I ∈ cComp (I ⊔ T) := cComp_of_isLocal hI
  have hIp : ⁅I, I⁆ = I := hIc.2.1
  have hIH : ¬ I ≤ hz T V := fun hle =>
    hne (le_antisymm (B1Red.perfect_le_oTwoUpper' hle (Subgroup.isPerfect_iff.mpr hIp)) hKI)
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hInH : InH (S : Subgroup G) (I ⊔ T) := ⟨hS ▸ le_sup_right, hI.2.2.2⟩
  have hTFAE := lemma_1_2_10_of_a36 h.fsu.qtke h.fsu.simple h.fsu.nonabelian h36 S hInH hIc
  have hchar : CharTwo (I ⊔ T) := charTwo_of_inH h.fsu.qtke.2.1 S hInH
  have hred := (conjClosure_isTwoReducedIn_of_charTwo (isSylowTwoOf_of_le h le_sup_right) hchar
    (inf_le_right : fsuV1 T V ≤ quasithinOmegaOneCenter T)).2.2
  have hVI : ⁅conjClosure (fsuV1 T V) (I ⊔ T), I⁆ ≠ ⊥ := by
    intro hb
    apply hIH
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : ⁅v, x⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator
        (le_conjClosure (fsuV1 T V) (I ⊔ T) hv) hx
      rwa [hb, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm).mp h1
  have h2 : ∃ W, IsTwoReducedIn (I ⊔ T) W ∧ ⁅W, I⁆ ≠ ⊥ := ⟨_, hred, hVI⟩
  have hLf : quasithinIsFaithfulLocal (S : Subgroup G) I := (hTFAE.out 1 2).mpr h2
  rw [hS] at hLf
  have hidx : Nat.card (↥I ⧸ CFSG.pCore 2 ↥I) = 60 ∨ Nat.card (↥I ⧸ CFSG.pCore 2 ↥I) = 168 := by
    rcases h1434 G T L h.hyp I hLf with he5 | h3
    · left
      obtain ⟨e5⟩ := he5
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    · right
      obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h3
      rw [Nat.card_congr e3.toEquiv, card_SL_three_two']
  have hPI : (pCoreOf 2 I).relIndex I = Nat.card (↥I ⧸ CFSG.pCore 2 ↥I) := by
    rw [Subgroup.relIndex, pCoreOf_subgroupOf]
    rfl
  rw [← hPI] at hidx
  set P := pCoreOf 2 I with hP
  set Q := pCoreOf 2 (hz T V) with hQ
  have hIN : I ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 I
  have hKN : kz T V ≤ Subgroup.normalizer (P : Set G) := hKI.trans hIN
  have hKQ : kz T V ≤ Subgroup.normalizer (Q : Set G) :=
    (oTwoUpper_le _).trans (le_normalizer_pCoreOf 2 _)
  have hO2K : pCoreOf 2 (kz T V) ≤ Q :=
    A4.pCoreOf_le_of_subnormal 2 (A4.subnormal_of_normal (oTwoUpper_le _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).mpr
        (le_normalizer_oTwoUpper _)))
  have hKP : kz T V ⊓ P ≤ kz T V ⊓ Q := by
    refine le_inf inf_le_left (le_trans ?_ hO2K)
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun k hk => ?_)
      ((pCoreOf_isPGroup 2 I).to_le inf_le_right)
    exact mem_normalizer_inf' (Subgroup.le_normalizer hk) (hKN hk)
  have h60 : Q.relIndex (kz T V) = 60 := by
    rw [← A4.relIndex_sup_eq_of_le_normalizer' hKQ]
    exact relIndex_kz_sup h h63
  have hdvd : 60 ∣ P.relIndex (kz T V ⊔ P) := by
    rw [A4.relIndex_sup_eq_of_le_normalizer' hKN, ← Subgroup.inf_relIndex_left,
      ← Subgroup.relIndex_mul_relIndex _ _ _ hKP inf_le_left, Subgroup.inf_relIndex_left, h60]
    exact Dvd.intro_left _ rfl
  have hle : kz T V ⊔ P ≤ I := sup_le hKI (pCoreOf_le 2 I)
  have hm := Subgroup.relIndex_mul_relIndex P (kz T V ⊔ P) I le_sup_right hle
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hm
  have h1 : (kz T V ⊔ P).relIndex I = 1 := by
    rcases hidx with e | e <;> rw [e] at hm
    · have : k * (kz T V ⊔ P).relIndex I = 1 := by
        have := hm
        rw [mul_assoc] at this
        omega
      exact Nat.eq_one_of_mul_eq_one_left this
    · exfalso
      rw [mul_assoc] at hm
      omega
  have hIK : I ≤ kz T V ⊔ P := Subgroup.relIndex_eq_one.mp h1
  have hPT : P ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hIc)).trans
      (hS ▸ pCoreOf_two_le_sylow (I ⊔ T) S (hS ▸ le_sup_right))
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper _)
  have hINK : I ≤ Subgroup.normalizer (kz T V : Set G) :=
    hIK.trans (sup_le Subgroup.le_normalizer (hPT.trans hTK))
  have hsn : IsSubnormal (kz T V) (I ⊔ T) :=
    A4.subnormal_trans (A4.subnormal_of_normal hKI
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKI).mpr hINK)) (subnormal_of_mem_cComp hIc)
  exact hIc.2.2.2 (kz T V) hlt hC.1 hC.2.1 hsn

end L32A

end CFSG.Quasithin.H13
