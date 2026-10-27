module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotSp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineC2
public import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem comap_pCore_eq_of_pCore_eq_bot_of_kSchurO6p
    {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f)
    (hperfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hker : ∀ x ∈ f.ker, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 X)
    (hSO : KSchurO6p)
    (hshape : ∃ n : ℕ, 3 ≤ n ∧ IsOmegaPlus (Y ⧸ CFSG.pCore 2 Y) 6 n)
    (hbot : CFSG.pCore 2 Y = ⊥) : f.ker = CFSG.pCore 2 X := by
  have hSchur : ∀ (Xb : Type) [Group Xb] [Finite Xb] (K : Subgroup Xb) [K.Normal],
      ⁅(⊤ : Subgroup Xb), (⊤ : Subgroup Xb)⁆ = ⊤ → K ≤ Subgroup.center Xb →
      Odd (Nat.card ↥K) →
      Nonempty (Xb ⧸ K ≃* Y ⧸ CFSG.pCore 2 Y) → K = ⊥ := by
    intro Xb _ _ K _ hcomm hcenter hodd ⟨e⟩
    obtain ⟨n, hn, hPlus⟩ := hshape
    exact hSO Xb K hcomm hcenter hodd ⟨n, hn, IsOmegaPlus.of_mulEquiv e.symm hPlus⟩
  have hmain := comap_pCore_eq_of_surjective_of_schur f hf hperfect hker hSchur
  rw [← hmain, hbot, MonoidHom.comap_bot]

theorem phiL_ker_eq_pCore_and_map_Hinf_eq {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (hK : KOrdNatural) (hSO : KSchurO6p)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    (c.phiL hV).ker = CFSG.pCore 2 ↥c.L ∧
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) =
        Hinf (MulAction.stabilizer ↥(c.H hV)
          (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
            Set (c.W hV)))) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hbotH : CFSG.pCore 2 ↥(c.H hV) = ⊥ := hK.1 hnat
  have hshapeP : ∃ m : ℕ, 3 ≤ m ∧
      IsOmegaPlus (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) 6 m := by
    have eY : (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) ≃* ↥(c.H hV) :=
      (QuotientGroup.quotientMulEquivOfEq hbotH).trans QuotientGroup.quotientBot
    exact ⟨CFSG.Open.pRank 2 D.Z, h3, IsOmegaPlus.of_mulEquiv eY.symm hline.1⟩
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  refine ⟨?_, ?_⟩
  · exact comap_pCore_eq_of_pCore_eq_bot_of_kSchurO6p (c.phiL hV) (c.phiL_surjective hV)
      (c.commutator_L_eq_top) (c.phiL_ker_commutator_mem_pCore hV hK hnat) hSO
      hshapeP hbotH
  · rw [show ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)) = ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) by rw [hℓ]]
    exact c.map_Hinf_inf_eq hV h4 h1930

theorem s23_9_NotO6p_of (D : Data G) (Ch : Choice2011 G)
    (hA : KTab23a) (h4 : S23_4 D Ch) (hK : KOrdNatural)
    (hEmb : S23_9_C2Emb D Ch) (hGO : KGenO6p) (hSO : KSchurO6p) :
    S23_9_NotO6p D Ch := by
  intro h1930 c h3 hV
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  change ¬ (IsOmegaPlus ↥(c.H hV) 6 n ∧ NatOmegaPlus (c.H hV) ⊤ ⊥ 6 n)
  intro hline
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let Pℓ : Subgroup ↥(c.H hV) :=
    MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)))
  let Kstar : Subgroup ↥(c.H hV) := Hinf Pℓ
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  have hnat : IsNaturalClassicalModule (c.H hV) n := by
    rcases hline with ⟨hPlus, hNatPlus⟩
    exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inl ⟨hPlus, hNatPlus⟩
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA (by simpa only [n] using hnat) h4 h1930
  have hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L :=
    (phiL_ker_eq_pCore_and_map_Hinf_eq c hV hA h4 hK hSO h1930 h3
      (by simpa only [n] using hnat) (by simpa only [n] using hline)).1
  have hKstar_eq : (K.subgroupOf c.L).map (c.phiL hV) = Kstar := by
    dsimp only [Kstar, Pℓ]
    exact (phiL_ker_eq_pCore_and_map_Hinf_eq c hV hA h4 hK hSO h1930 h3
      (by simpa only [n] using hnat) (by simpa only [n] using hline)).2
  have hPℓ_image : ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = Pℓ := by
    dsimp only [Pℓ]
    rw [hℓ]
    exact c.map_inf_eq_stabilizer_Ztil hV h4 h1930
  obtain ⟨p, hp, hp2, hpK, hNorm⟩ :=
    hEmb h1930 c (by simpa only [n] using h3) hV (by simpa only [Ctx23L.H] using hline)
  have hKle : K ≤ c.L := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right
  have hKcard : Nat.card ↥(K.subgroupOf c.L) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hkerP : IsPGroup 2 (c.phiL hV).ker := by
    rw [hker_eq]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hnotdvd : ¬ p ∣ Nat.card ↥(K.subgroupOf c.L ⊓ (c.phiL hV).ker) := by
    intro hdvd
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hkerP hp hp2
      (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hcard : Nat.card ↥(K.subgroupOf c.L) =
      Nat.card ↥Kstar * Nat.card ↥(K.subgroupOf c.L ⊓ (c.phiL hV).ker) := by
    have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker (c.phiL hV)
      (K.subgroupOf c.L)
    rwa [hKstar_eq] at h
  have hpKstar : p ∣ Nat.card ↥Kstar := by
    have hcop : Nat.Coprime p
        (Nat.card ↥(K.subgroupOf c.L ⊓ (c.phiL hV).ker)) :=
      hp.coprime_iff_not_dvd.mpr hnotdvd
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [← hcard, hKcard]
    exact hpK
  obtain ⟨Xstar, hXstar_le, hXcard, w, hw_notPℓ, hw_norm⟩ :=
    hGO (c.W hV) (c.H hV) n hnat (c.commutator_H_eq hV) h3 (c.sylowStar hV)
      hline p hp hp2 hpKstar
  have hN : ∀ a : ↥c.L, (a : G) ∈ Hinf (D.M ⊓ c.L) → orderOf a = p →
      c.phiL hV a ∈ Xstar →
      Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) ≤ D.M := by
    intro a haK haord _
    exact hNorm (a : G) haK ((Subgroup.orderOf_coe a).trans haord)
  obtain ⟨g, hgφ⟩ := c.phiL_surjective hV w
  exact hw_notPℓ (Ctx23L.mem_stabilizer_of_forall_normalizer_le_M c hV hp hp2 hker_eq
    h1930 hPℓ_image hKstar_eq hXstar_le hXcard hw_norm hN hgφ)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
