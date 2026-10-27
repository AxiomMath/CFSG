module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420B56Group

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.C27

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem pCoreOf_sup_le (hC23 : HypC23Cat H R M) (hKc : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 (K ⊔ R) ≤ R :=
  c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hC23.radical hKc hq hRK)

theorem pCoreOf_le_pCoreOf_sup (hRK : R ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hRK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem sup_inf_centralizer_pCoreOf_le (hR2 : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hch : CharTwo K) :
    (K ⊔ R) ⊓ Subgroup.centralizer (pCoreOf 2 (K ⊔ R) : Set G) ≤ pCoreOf 2 (K ⊔ R) := by
  refine L15420.le_pCoreOf_sup_of_inf_le hR2 hRK inf_le_left
    (L15420.le_normalizer_inf_centralizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R))) ?_
  rintro x ⟨hxK, -, hxC⟩
  exact hch ⟨hxK, Subgroup.centralizer_le (pCoreOf_le_pCoreOf_sup hRK) hxC⟩

omit [Finite G] in
theorem omegaOneCenterOf_le {Q : Subgroup G} (hQR : Q ≤ R)
    (hCQ : (K ⊔ R) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    omegaOneCenterOf R ≤ omegaOneCenterOf Q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨⟨hxR, hxC⟩, hx2⟩
  have hxCQ : x ∈ Subgroup.centralizer (Q : Set G) := Subgroup.centralizer_le hQR hxC
  exact Subgroup.subset_closure ⟨⟨hCQ ⟨Subgroup.mem_sup_right hxR, hxCQ⟩, hxCQ⟩, hx2⟩

omit [Finite G] in
theorem inf_normalizer_le_cgsIn {C : Subgroup G} (hCR : C ≤ R) (hC1 : C ≠ ⊥)
    (hCc : (C.subgroupOf R).Characteristic) :
    H ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn H R :=
  le_iSup₂_of_le C hCR (le_iSup₂_of_le hC1 hCc le_rfl)

omit [Finite G] in
theorem sup_le_normalizer (K R : Subgroup G) :
    K ⊔ R ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
  (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf _)

theorem inf_centralizer_le (hC23 : HypC23Cat H R M) (hKc : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hch : CharTwo K) (hKM : ¬ K ≤ M)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) :
    K ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤ pCoreOf 2 K := by
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hVdef
  have hR2 : IsPGroup 2 R := hC23.radical.isPGroup
  have hOV : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_sup hRK).trans (L15420.le_centralizer_omegaOneCenterOf _)
  rcases L15420.le_pCoreOf_or_le hq hZ inf_le_left
    (L15420.le_normalizer_inf_centralizer (le_sup_left.trans (sup_le_normalizer K R)))
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hOV) with h | h
  · exact h
  · exfalso
    have hZR : omegaOneCenterOf R ≤ V := omegaOneCenterOf_le (pCoreOf_sup_le hC23 hKc hq hRK)
      (sup_inf_centralizer_pCoreOf_le hR2 hRK hch)
    have hKN : K ≤ H ⊓ Subgroup.normalizer (omegaOneCenterOf R : Set G) := fun k hk =>
      ⟨le_of_mem_cComp hKc hk, Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le hZR (h hk).2)⟩
    exact hKM (hKN.trans ((inf_normalizer_le_cgsIn (Setup.omegaOneCenterOf_le R)
      (Setup.omegaOneCenterOf_ne_bot hR2 hC23.radical.2.1)
      (Setup.characteristic_omegaOneCenterOf R)).trans hC23.cgs))

theorem sup_inf_centralizer_le (hR2 : IsPGroup 2 R) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hCK : K ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤
      pCoreOf 2 K) :
    (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤
      pCoreOf 2 (K ⊔ R) := by
  refine L15420.le_pCoreOf_sup_of_inf_le hR2 hRK inf_le_left
    (L15420.le_normalizer_inf_centralizer (sup_le_normalizer K R)) ?_
  rintro x ⟨hxK, -, hxC⟩
  exact hCK ⟨hxK, hxC⟩

theorem exists_ffStarOffender (hC23 : HypC23Cat H R M) (hKc : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hch : CharTwo K) (hKM : ¬ K ≤ M)
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hV : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :
    ∃ A : Subgroup (MulAut (IntMod _ hV)), IsFFStarOffender (autI hV (K ⊔ R)) A := by
  set Q := pCoreOf 2 (K ⊔ R) with hQdef
  set V := omegaOneCenterOf Q with hVdef
  have hR2 : IsPGroup 2 R := hC23.radical.isPGroup
  have hQR : Q ≤ R := pCoreOf_sup_le hC23 hKc hq hRK
  have hCV := sup_inf_centralizer_le hR2 hRK (inf_centralizer_le hC23 hKc hq hZ hch hKM hRK)
  have hVR : V ≤ R := (A4.omegaOneCenterOf_le _).trans hQR
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans (sup_le_normalizer K R)
  have hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G) := by
    intro hJ
    have hJR : thompsonJ R ≤ R := CFSG.Quasithin.thompsonJ_le_self R
    have hJQ : thompsonJ R ≤ Q := fun x hx => hCV ⟨Subgroup.mem_sup_right (hJR hx), hJ hx⟩
    have heq : thompsonJ R = thompsonJ Q := CFSG.Quasithin.thompsonJ_eq_of_le hJQ hQR
    have hN : K ≤ H ⊓ Subgroup.normalizer (thompsonJ R : Set G) := fun k hk => by
      refine ⟨le_of_mem_cComp hKc hk, ?_⟩
      rw [heq]
      exact (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ Q)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R) (Subgroup.mem_sup_left hk))
    exact hKM (hN.trans ((inf_normalizer_le_cgsIn hJR
      (Setup.thompsonJ_ne_bot hR2 hC23.radical.2.1) (Setup.characteristic_thompsonJ R)).trans
      hC23.cgs))
  obtain ⟨B, hB⟩ := (offenderImages_nonempty_iff_not_le hV).2 hJ
  exact ⟨B, isFFStarOffender_mono (autI_mono hV le_sup_right)
    (offenderImages_isFFStarOffender hV hVR hRN hB)⟩

end CFSG.Quasithin.Vol2.Ch10.V1C.C27
