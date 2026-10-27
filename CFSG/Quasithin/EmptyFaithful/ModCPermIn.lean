module

public import CFSG.Quasithin.EmptyFaithful.ModCGlueIn
public import CFSG.Quasithin.EmptyFaithful.ModCPerm
public import CFSG.Quasithin.EmptyFaithful.S14610Q4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem input14610PermTuInS_holds :
    ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
      Facts14610 T M H u I I₂ → IsSylowTwoOf (T ⊓ I) I →
      yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) →
      tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G) →
      ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.centralizer (VZ T M : Set G)) →
      Concl14610List T M I I₂ K → IsAlt 6 (OTwoQuot K) → Nat.card (wOf1469 K) = 2 ^ 5 →
      T ⊓ I = tU T u → Nat.card (conjClosure (VZ T M) I₂) ≠ 2 ^ 3 → u ∈ wOf1469 K → False := by
  intro G _ _ T M H u I I₂ K c hsyl hLT hN hV3 hK hA hW hTu _ _
  have hshort : IsShort2 K := ModB.isShort_of_alt hK (Or.inl hA)
  have hWU := ModB.wOf1469_eq_blockU_of_short hshort
  rw [hWU] at hW
  obtain ⟨Φ, hΦ⟩ := ModC.exists_core_equiv_six hshort hA hW
  exact ModC.in_contradiction c hK hsyl hLT hshort Φ hΦ hTu hN hV3

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.facts14610_perm_of_sylow' (i16 : Input14610PermFixed) (i7 : Input14610PermA7Fixed)
    {H : Subgroup G} {u : G} {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hcases : T ⊓ I = tU T u ∨ T ⊓ I = tZero T u)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hN : tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G))
    (hV3 : ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.centralizer (VZ T M : Set G)))
    (hK : Concl14610List T M I I₂ K)
    (hperm : (IsAlt 6 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 5) ∨
      (IsAlt 7 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 6)) :
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3 := by
  by_contra hne
  rcases hcases with hTu | hT0
  · by_cases huW : u ∈ wOf1469 K
    · rcases hperm with ⟨hA, hW⟩ | ⟨hA, hW⟩
      · exact input14610PermTuInS_holds G T M H u I I₂ K c hsyl hLT hN hV3 hK hA hW hTu hne huW
      · have hIu : I ≤ Subgroup.centralizer ({u} : Set G) := c.cent hTu
        have huC : u ∈ Subgroup.centralizer (K : Set G) := by
          refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
          have := Subgroup.mem_centralizer_iff.mp (hIu (hK.le hk)) u rfl
          exact this.symm
        have hbot := i7 G T M H u I I₂ K c hK hA hW
        have hu1 : u = 1 := by
          have : u ∈ wOf1469 K ⊓ Subgroup.centralizer (K : Set G) := ⟨huW, huC⟩
          rw [hbot] at this
          exact Subgroup.mem_bot.mp this
        apply c.hu.not_central
        rw [hu1]
        exact Subgroup.one_mem _
    · exact input14610PermTuOutS_holds G T M H u I I₂ K c hsyl hLT hK hperm hTu hne huW
  · have S : Setting146 G T M := c.setting
    have hres : oTwoUpper (yOfL22 T M) = yOfL22 T M := S.hyp1281.residual
    have hLI1 : yOfL22 T M ≤ i1Of1469 T M I := by
      calc yOfL22 T M = oTwoUpper (yOfL22 T M) := hres.symm
        _ ≤ i1Of1469 T M I := (Subgroup.closure_le _).mpr fun x hx =>
          S.odd_mem_i1_of_tI_eq_tZero c.hu hT0 hLT (Subgroup.mem_sup_left hx.1) hx.2
    have hlI : lI T M I = yOfL22 T M := by
      have hLI : yOfL22 T M ≤ I := hLI1.trans (i1Of1469_le T M I)
      unfold lI
      rw [inf_eq_left.mpr hLI]
      exact hres
    have hW := i16 G T M H u I I₂ K c hK hperm
    rw [hlI] at hW
    apply hW
    have hWT : wOf1469 K ≤ T := wOf1469_le_T hK.le hK.normal hsyl
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← S.hyp.inf_centralizer_yOfL22_eq_bot S.facts]
    exact ⟨hWT hx.1, hx.2⟩

end CFSG.Quasithin
