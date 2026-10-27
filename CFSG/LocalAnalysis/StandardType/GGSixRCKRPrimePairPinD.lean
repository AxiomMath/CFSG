module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogD

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

theorem weakCT_spinPlus_of_frame_pinned {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .POmegaPlus n p f) (hn3 : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (U : Fin n → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin n → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin n, edgeD n i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : spinGroup (Spin.quadPlus n (GaloisField p f)) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X =
        (Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField p f)))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaPlus n p f ∧
      ∀ k : Fin n,
        ((Spin.plusDatum n (GaloisField p f) hn3).rootGroup (sroot k)).map Ψ =
            Subgroup.closure (Set.range fun c : F => ρ k (tv 0 1 c)) ∧
        ((Spin.plusDatum n (GaloisField p f) hn3).rootGroup (-sroot k)).map Ψ =
            Subgroup.closure (Set.range fun c : F => ρ k (tv 1 0 c)) := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Spin.plusDatum n (GaloisField p f) hn3).isFiniteType
    (Dv := (Spin.plusDatum n (GaloisField p f) hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin n) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := GaloisField p f) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, hpin⟩ := weakCT_of_frame_of_equiv_pinned e
    (CurtisTits.curtisTitsConclusion_spinPlus hadm
      (GaloisField.card p f (by have := hadm.2.1; omega)) hn3)
    (leviConePresented_spinPlus (GaloisField p f) hn3) hD
    (⟨0, by omega⟩ : Fin n) hgen hcomm hρ hψ
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ⟨(hpin k).2.1, (hpin k).2.2⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

namespace CFSG.StandardType.RCKRP

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open scoped MatrixGroups

theorem innerRecogPinned_D
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    {n : ℕ} (hn : 4 ≤ n) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    ∃ Ψ : spinGroup (Spin.quadPlus n (GaloisField p f)) →* ModGL τ K,
      Ψ.range = rootSpan τ K (rootsOfFam β (Set.range l)) ∧
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField p f))) ∧
      ∀ k : Fin n,
        ((Spin.plusDatum n (GaloisField p f) (by omega)).rootGroup (Pi.single k 1)).map Ψ =
            rootSubgroup τ K (β (l k)) ∧
        ((Spin.plusDatum n (GaloisField p f) (by omega)).rootGroup (-Pi.single k 1)).map Ψ =
            rootSubgroup τ K (-β (l k)) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ, hρeq⟩ :=
    rckPin_weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨Fact.out, hf, hn⟩
  obtain ⟨Ψ', hsurj, hker, hqs, hcent, hmodel, hpin⟩ :=
    weakCT_spinPlus_of_frame_pinned hadm (by omega) hK U hgen hcomm hρ hψ
  refine ⟨(rootSpan τ K (rootsOfFam β (Set.range l))).subtype.comp Ψ', ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [MonoidHom.comp_apply] at hx
    have hx' : Ψ' x = 1 := (rootSpan τ K (rootsOfFam β (Set.range l))).subtype_injective (by
      rw [hx, map_one])
    exact hker (by rwa [MonoidHom.mem_ker])
  · intro k
    exact rckPin_map_rootGroup_pinned hroot l k (ρ := ρ k) (fun A => hρeq k A)
      (hpin k).1 (hpin k).2

end CFSG.StandardType.RCKRP

end
