module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323MS
public import CFSG.Quasithin.Background.C134L32CorrM

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace MS3323

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem exists_charW
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hC34 : CFSG.Quasithin.C134L32CorrM) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα : IsModO2Surj L α)
    (hinner : ∀ t ∈ T, ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c) (hNC : HasNoncentralTwoChief L 2) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧
      C ≤ pCoreOf 2 (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) ∧
      L ⊔ T ≤ Subgroup.normalizer (C : Set G) ∧
      Subgroup.normalizer ((pCoreOf 2
        (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Subgroup G) :
          Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T with hH
  set R := pCoreOf 2 H with hR
  have hTH : T ≤ H := le_sup_right
  have hHLT : H ≤ L ⊔ T := sup_le_sup_right inf_le_left T
  have hsylT : IsSylowTwoOf T (L ⊔ T) := h.toSetup331.isSylowTwoOf
  have hsylH : IsSylowTwoOf T H := ⟨hTH, hsylT.2.1, fun h2 =>
    hsylT.2.2 (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T H (L ⊔ T) hTH hHLT)))⟩
  have hRT : R ≤ T := pCoreOf_le_of_isSylowTwoOf hsylH
  have hQR : qL L T ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le_of_isSylowTwoOf hsylT).trans hTH) (fun x hx =>
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (hHLT hx))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hset : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T hTL
  have hset' : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (R : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hset] at hx
      obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨l', hl', c, hc, rfl⟩ := hinner t ht
      exact Set.mem_mul.mpr ⟨l * l', L.mul_mem hl hl', c, hQR hc, by group⟩
    · rintro _ ⟨l, hl, r, hr, rfl⟩
      exact Subgroup.mul_mem_sup hl (hRT hr)
  have hr2 := CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2
  have hcomp := h.toSetup331.mem_cComp
  have hMST : IsMSPair (L ⊔ T) T := h.isMSPair h38 h39 hr2 hTL
  by_cases hMS3 : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      ¬ L ⊔ T ≤ Subgroup.normalizer (C : Set G)
  · exfalso
    have hMSR : IsMSPair (L ⊔ T) R :=
      ⟨⟨hMST.1.1, hMST.1.2.1, L, hcomp, hset', hr2⟩,
        Or.inl ⟨H, lt_sup h h38 h39 hTL, not_two_dvd_relIndex h, rfl⟩, hMS3⟩
    obtain ⟨i, hi⟩ := hC34 G (L ⊔ T) R L hMSR hcomp hset'
      ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
    have hRZ : R = pCoreOf 2 ((L ⊔ T) ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G)) := by
      rw [inf_centralizer_eq hTL]
    match i, hi with
    | 0, hi => exact hi.elim
    | 1, hi => exact Lem3328.not_hasNoncentralTwoChief_two_of_isShort2 hi.1.1 hNC
    | 2, hi => exact hi.2 T hsylT hRT hRZ
    | 3, hi => exact hi.2 T hsylT hRT hRZ
    | 4, hi => exact hi.2 T hsylT hRT hRZ
    | 5, hi => exact false_of_le_center h h38 h39 hTL (hi.2 T hsylT hRT).1
    | n + 6, hi => exact hi.elim
  · push Not at hMS3
    obtain ⟨C, hCR, hC1, hchar, hLTC⟩ := hMS3
    exact ⟨C, hC1, hCR, hLTC, Hyp331.normalizer_le_normalizer_of_characteristic hCR hchar⟩


end MS3323

end CFSG.Quasithin.H13
