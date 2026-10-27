module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSmallCommCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeventeenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords

public section


namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mult

theorem k_K_Omega6Minus_smallComm_holds_of (hIso : K_Omega6Minus_natIsoMod) :
    K_Omega6Minus_smallComm := by
  classical
  intro W _ _ H p n s hn hs1 hs2 _hO hSum hp hcong t ht ht2 hcard z hz1 hz
  obtain ⟨I, -, hind, hsup, hNat⟩ := hSum
  have : NeZero s := ⟨by omega⟩
  obtain ⟨-, K, hK, hKf, b, c, hcardK, hpoly, π0, hπ0⟩ := hNat 0
  letI : Field K := hK
  have : Finite K := hKf
  have : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcardK
  let Γ := StatedOmega (StatedQuadMinus (6 / 2) K b c)
  have hiso' : ∀ i : Fin s, CFSG.Quasithin.H.Pair.IsoMod H (I 0) (I i) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact ⟨MulEquiv.refl _, fun l hl w h => rfl⟩
    · exact hIso H (I 0) (I i) n (hNat 0) (hNat i)
  have hVia : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SumOfNatVia
      (FFModel.nat Γ) H ⊤ ⊥ s π0 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.sumOfNatVia_of_isoMod
      (D := FFModel.nat Γ) (X := H) (I := I) hind hsup 0 hπ0 hiso'
  obtain ⟨-, e, -, he, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.exists_coords_of_sumOfNatVia Γ hVia
  have hXmap : H.map (congrHom e) = natImage (diagSub s Γ) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.map_congrHom_eq_natImage_diag Γ
      hπ0.1 e he
  set T := congrHom e t with hTdef
  have hT : T ∈ Subgroup.normalizer
      (natImage (diagSub s Γ) : Set (MulAut (StdMod (Fin s × _) K))) := by
    rw [← hXmap, ← Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)]
    exact Subgroup.mem_map_of_mem _ ht
  have hT2 : ∃ m : ℕ, orderOf T = 2 ^ m := by
    obtain ⟨m, hm⟩ := ht2
    exact ⟨m, by rw [hTdef, orderOf_injective _ (congrHom_injective e) t, hm]⟩
  have hfixT : ∀ w : W, T (e w) = e (t w) := fun w => by
    rw [hTdef, congrHom_apply, MulEquiv.symm_apply_apply]
  have hcardT : Nat.card (StdMod (Fin s × (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2)) K) <
      2 ^ (2 * n * s) * Nat.card (fixV (Subgroup.zpowers T)) := by
    have h1 : Nat.card (StdMod (Fin s × (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2)) K) =
        Nat.card W :=
      (Nat.card_congr e.toEquiv).symm
    have h2 : Nat.card (fixV (Subgroup.zpowers T)) = Nat.card (fixV (Subgroup.zpowers t)) := by
      refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun w => ?_)).symm
      change w ∈ fixV (Subgroup.zpowers t) ↔ e w ∈ fixV (Subgroup.zpowers T)
      rw [mem_fixV_zpowers_iff_apply, mem_fixV_zpowers_iff_apply, hfixT]
      exact ⟨fun h => by rw [h], fun h => e.injective h⟩
    rw [h1, h2]
    exact hcard
  have hzT : e z ∈ commSub ⊤ (Subgroup.zpowers T) := by
    rw [commSub_zpowers_eq_map (fun _ _ _ _ => Subgroup.mem_top _)] at hz ⊢
    obtain ⟨v₀, -, rfl⟩ := Subgroup.mem_map.mp hz
    refine ⟨e v₀, Subgroup.mem_top _, ?_⟩
    rw [commHom_apply, commHom_apply, hfixT, map_mul, map_inv]
  have hz1T : e z ≠ 1 := fun h => hz1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨E, hEΓ, hEa, hEcard, hEfix⟩ :=
    omegaMinus_smallComm_diag hpoly hn hcardK hs2 hp hcong hT hT2 hcardT hz1T hzT
  have hπinj : Function.Injective π0 :=
    CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on
      (CFSG.Quasithin.FFModel.nat_faithful _) hπ0
  let f : ↥Γ →* MulAut W := H.subtype.comp π0
  have hfinj : Function.Injective f := H.subtype_injective.comp hπinj
  let E' : Subgroup (MulAut W) := (E.subgroupOf Γ).map f
  have hE'a : IsElemAbelian p E' := (hEa.subgroupOf Γ).map f
  have hE'card : Nat.card ↥E' = p ^ 2 := by
    have h2 : Nat.card ↥(E.subgroupOf Γ) = Nat.card ↥E := by
      calc Nat.card ↥(E.subgroupOf Γ) = Nat.card ↥((E.subgroupOf Γ).map Γ.subtype) :=
            (Subgroup.card_map_of_injective Γ.subtype_injective).symm
        _ = Nat.card ↥E := by rw [Subgroup.map_subgroupOf_eq_of_le hEΓ]
    calc Nat.card ↥E' = Nat.card ↥(E.subgroupOf Γ) := Subgroup.card_map_of_injective hfinj
      _ = Nat.card ↥E := h2
      _ = p ^ 2 := hEcard
  refine ⟨E', ?_, hE'a.isPGroup, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (π0 y).2
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_not_isCyclic_of_card_sq hp hE'a hE'card
  · rintro _ ⟨y, hy, rfl⟩
    apply e.injective
    refine (he y z).trans ?_
    exact hEfix (y : GL (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2) K)
      (Subgroup.mem_subgroupOf.mp hy)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
