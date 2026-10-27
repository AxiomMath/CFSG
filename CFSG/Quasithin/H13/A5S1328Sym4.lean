module

public import CFSG.Quasithin.H13.A5S1328Sym3
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.Quasithin.Background.B2FactorizationR2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] noncomputable def Sp {G : Type} [Group G] (L K T : Subgroup G) : Subgroup G :=
  pCoreOf 2 (bigB L K T)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem pCoreOf_ne_bot_of_le_M {X : Subgroup G} (hTX : T ≤ X)
    (hXM : X ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have hM2 : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal S.uniqueM.1.1.1
  have hMT : pCoreOf 2 M ≤ T :=
    pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow (hTX.trans hXM))
  have hle : pCoreOf 2 M ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (hMT.trans hTX) (hXM.trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  intro h
  rw [h] at hle
  exact hM2 (le_bot_iff.mp hle)

theorem hyp111R_of_borels {H K VH : Subgroup G}
    (S' : Setting G T K VH) (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHK : H = K ⊔ T) (hB1 : borelOf L T ≤ Subgroup.normalizer (K : Set G))
    (hB2 : borelOf K T ≤ Subgroup.normalizer (L : Set G)) : Hyp111R L K T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite ↥T := inferInstance
  have h1 : Hyp111At L K T := by
    refine ⟨hfin, S.isPGroup_T, S.T_le_NL, S.sylow_inf_L, S.isRankOneListed_L, hB2, ?_⟩
    have hX : L ⊔ T ⊔ borelOf K T ≤ Subgroup.normalizer (L : Set G) :=
      sup_le (sup_le Subgroup.le_normalizer S.T_le_NL) hB2
    have hTX : T ≤ L ⊔ T ⊔ borelOf K T := le_sup_right.trans le_sup_left
    exact S.charTwo_of_inH ⟨hTX, S.pCoreOf_ne_bot_of_le_M hTX hX⟩
  have h2 : Hyp111At K L T := by
    refine ⟨hfin, S.isPGroup_T, S'.T_le_NL, S'.sylow_inf_L, S'.isRankOneListed_L, hB1, ?_⟩
    have hX : K ⊔ T ⊔ borelOf L T ≤ Subgroup.normalizer (K : Set G) :=
      sup_le (sup_le Subgroup.le_normalizer S'.T_le_NL) hB1
    have hTX : T ≤ K ⊔ T ⊔ borelOf L T := le_sup_right.trans le_sup_left
    exact S.charTwo_of_inH ⟨hTX, S'.pCoreOf_ne_bot_of_le_M hTX hX⟩
  have ho2 : pCoreOf 2 (L ⊔ K ⊔ T) = ⊥ := by
    by_contra hne
    obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hne
    have hLT : L ⊔ T ≤ M' :=
      sup_le (le_sup_left.trans (le_sup_left.trans hM'.2)) (le_sup_right.trans hM'.2)
    have hM'eq : M' = Subgroup.normalizer (L : Set G) := S.uniqueM.2 M' ⟨hM'.1, hLT⟩
    apply hH.2.1
    rw [hHK, ← hM'eq]
    exact sup_le (le_sup_right.trans (le_sup_left.trans hM'.2)) (le_sup_right.trans hM'.2)
  exact ⟨⟨h1, h2, ho2⟩, S.rankOneAt_L, S'.rankOneAt_L⟩

end Setting

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem Sp_le_T (K : Subgroup G) : Sp L K T ≤ T :=
  pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow le_sup_right)

omit S in
theorem inf_le_Sp_left {K : Subgroup G} (h : Hyp111R L K T) : T ⊓ L ≤ Sp L K T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← F1.pCoreOf_borelOf h.hyp.h1.sylow]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans ?_) ?_ (pCoreOf_isPGroup 2 _)
  · exact le_sup_left.trans le_sup_left
  · exact (F1.bigB_le_normalizer_borelOf h).1.trans (normalizer_le_normalizer_pCoreOf 2 _)

omit S in
theorem inf_le_Sp_right {K : Subgroup G} (h : Hyp111R L K T) : T ⊓ K ≤ Sp L K T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← F1.pCoreOf_borelOf h.hyp.h2.sylow]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans ?_) ?_ (pCoreOf_isPGroup 2 _)
  · exact le_sup_right.trans le_sup_left
  · exact (F1.bigB_le_normalizer_borelOf h).2.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem Sp_inf_left {K : Subgroup G} (h : Hyp111R L K T) : Sp L K T ⊓ L = T ⊓ L :=
  le_antisymm (fun _ hx => ⟨S.Sp_le_T K hx.1, hx.2⟩) (le_inf (inf_le_Sp_left h) inf_le_right)

theorem Sp_inf_right {K : Subgroup G} (h : Hyp111R L K T) : Sp L K T ⊓ K = T ⊓ K :=
  le_antisymm (fun _ hx => ⟨S.Sp_le_T K hx.1, hx.2⟩) (le_inf (inf_le_Sp_right h) inf_le_right)

theorem borelOf_Sp_right {K : Subgroup G} (h : Hyp111R L K T) :
    borelOf K (Sp L K T) = borelOf K T := by
  unfold borelOf
  rw [S.Sp_inf_right h]

theorem borelOf_Sp_left {K : Subgroup G} (h : Hyp111R L K T) :
    borelOf L (Sp L K T) = borelOf L T := by
  unfold borelOf
  rw [S.Sp_inf_left h]

omit S [Finite G] in
theorem T_le_normalizer_Sp (K : Subgroup G) : T ≤ Subgroup.normalizer (Sp L K T : Set G) :=
  (le_sup_right : T ≤ bigB L K T).trans (le_normalizer_pCoreOf 2 _)

theorem le_normalizer_Sp_sup {K : Subgroup G} (h : Hyp111R L K T) :
    L ⊔ T ⊔ borelOf K T ≤ Subgroup.normalizer ((L ⊔ Sp L K T ⊔ borelOf K T : Subgroup G) :
      Set G) := by
  have hTn : T ≤ Subgroup.normalizer ((L ⊔ Sp L K T ⊔ borelOf K T : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_sup S.T_le_NL (T_le_normalizer_Sp K))
      ((le_sup_right : T ≤ bigB L K T).trans (F1.bigB_le_normalizer_borelOf h).2)
  exact sup_le (sup_le ((le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer) hTn)
    (le_sup_right.trans Subgroup.le_normalizer)

theorem charTwo_Sp_left {K : Subgroup G} (h : Hyp111R L K T) :
    CharTwo (L ⊔ Sp L K T ⊔ borelOf K T) := by
  have hle : L ⊔ Sp L K T ⊔ borelOf K T ≤ L ⊔ T ⊔ borelOf K T :=
    sup_le_sup (sup_le_sup le_rfl (S.Sp_le_T K)) le_rfl
  exact CharTwo.of_normal h.hyp.h1.charTwo hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (S.le_normalizer_Sp_sup h))

omit S [Finite G] in
theorem Sp_comm (K : Subgroup G) : Sp K L T = Sp L K T := by
  unfold Sp
  rw [bigB_comm]

theorem hyp111_Sp {H K VH : Subgroup G} (S' : Setting G T K VH)
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hHK : H = K ⊔ T)
    (h : Hyp111R L K T) : Hyp111 L K (Sp L K T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite ↥(Sp L K T) := inferInstance
  have hp : IsPGroup 2 ↥(Sp L K T) := pCoreOf_isPGroup 2 _
  have hBL := F1.bigB_le_normalizer_left h
  have h1 : Hyp111At L K (Sp L K T) := by
    refine ⟨hfin, hp, (pCoreOf_le 2 _).trans hBL.1, ?_, S.isRankOneListed_L, ?_, ?_⟩
    · rw [S.Sp_inf_left h]; exact S.sylow_inf_L
    · rw [S.borelOf_Sp_right h]; exact h.hyp.h1.borel_le
    · rw [S.borelOf_Sp_right h]; exact S.charTwo_Sp_left h
  have h2 : Hyp111At K L (Sp L K T) := by
    refine ⟨hfin, hp, (pCoreOf_le 2 _).trans hBL.2, ?_, S'.isRankOneListed_L, ?_, ?_⟩
    · rw [S.Sp_inf_right h]; exact S'.sylow_inf_L
    · rw [S.borelOf_Sp_left h]; exact h.hyp.h2.borel_le
    · rw [S.borelOf_Sp_left h]
      have := S'.charTwo_Sp_left h.symm
      rwa [Sp_comm] at this
  have ho2 : pCoreOf 2 (L ⊔ K ⊔ Sp L K T) = ⊥ := by
    by_contra hne
    set Y := L ⊔ K ⊔ Sp L K T with hY
    have hTY : T ≤ Subgroup.normalizer (Y : Set G) :=
      F1.le_normalizer_sup (F1.le_normalizer_sup S.T_le_NL S'.T_le_NL) (T_le_normalizer_Sp K)
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
      ⟨pCoreOf 2 Y, hne, pCoreOf_isPGroup 2 Y, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hYN : Y ≤ M' := (le_normalizer_pCoreOf 2 Y).trans hle
    have hTN : T ≤ M' := (hTY.trans (normalizer_le_normalizer_pCoreOf 2 Y)).trans hle
    have hLT : L ⊔ T ≤ M' := sup_le (le_sup_left.trans (le_sup_left.trans hYN)) hTN
    have hM'eq : M' = Subgroup.normalizer (L : Set G) := S.uniqueM.2 M' ⟨hM', hLT⟩
    apply hH.2.1
    rw [hHK, ← hM'eq]
    exact sup_le (le_sup_right.trans (le_sup_left.trans hYN)) hTN
  exact ⟨h1, h2, ho2⟩

end Setting

end CFSG.Quasithin.H13.A5
