module

public import CFSG.RankThree.GF2n.Smith81.InspKSpBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.LieType
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.A2Mod.Frame

section CertBound


open CFSG.Blueprint.Chevalley in
theorem KFact.card_rootGroup_f4 (K : Type) [Field K] (i : Fin (Tag.rank .F4)) :
    Nat.card ((Steinberg.Adjoint.f4Datum K).rootGroup (Pi.single i 1)) = Nat.card K := by
  have hγ := isRoot_single .F4 i
  refine (Nat.card_eq_of_bijective (fun c : K => (⟨Steinberg.Adjoint.xPar _ _ c,
    Steinberg.Adjoint.xPar_mem hγ c⟩ : (Steinberg.Adjoint.f4Datum K).rootGroup (Pi.single i 1)))
    ⟨fun c d h => Steinberg.Adjoint.xPar_injective hγ (congrArg Subtype.val h),
      fun x => ?_⟩).symm
  obtain ⟨c, hc⟩ := (Steinberg.Adjoint.mem_rootGroup_iff hγ x.1).mp x.2
  exact ⟨c, Subtype.ext hc⟩

theorem KFact.nslFrame_cases {Y : Type} [Group Y] [Finite Y] {R : Set (Subgroup Y)}
    (F : NSLFrameData Y R) (hZ : Subgroup.center Y = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (hmem : Nat.card ((F.D.rootGroup (Pi.single F.i₀ 1)).map F.Ψ) = 2 ^ f) :
    (∃ (n : ℕ) (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2)
        (Ψ : StatedSp n K' →* Y), 3 ≤ n ∧ Nat.card K' = 2 ^ f ∧ LieModel Y .PSp n 2 f ∧
        Function.Injective Ψ ∧ Function.Surjective Ψ ∧ ∃ i : Fin n, i.val + 1 < n ∧
          ((Symplectic.rootDatum n K').rootGroup (Pi.single i 1)).map Ψ ∈ R) ∨
    (∃ (n : ℕ) (K' : Type) (_ : Field K') (_ : Finite K') (b c : K')
        (hirr : ∀ s : K', s ^ 2 + b * s + c ≠ 0)
        (Ψ : spinGroup (Spin.quadMinus n K' b c) →* Y), 4 ≤ n ∧ Nat.card K' = 2 ^ f ∧
        LieModel Y .POmegaMinus n 2 f ∧ Function.Surjective Ψ ∧
        Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n K' b c)) ∧
        ∃ i : Fin (n - 1), i.val + 1 < n - 1 ∧
          ((Spin.Twisted.minusDatum n hirr).rootGroup (Pi.single i 1)).map Ψ ∈ R) ∨
    (∃ (t : StatedLieTag) (n f' : ℕ), t ≠ .PSp ∧ t ≠ .POmegaMinus ∧ t ≠ .POmegaPlus ∧
        LieModel Y t n 2 f') := by
  have hX : Nat.card (F.D.rootGroup (Pi.single F.i₀ 1)) = 2 ^ f :=
    (card_map_rootGroup_single F F.i₀).symm.trans hmem
  have hL : ∀ {t : StatedLieTag} {n p f' : ℕ},
      LieModel (F.K ⧸ Subgroup.center F.K) t n p f' → LieModel Y t n p f' :=
    fun h => lieModel_of_centerQuotient F hZ h
  have he := centerQuotientEquiv F hZ
  have hmemR := F.mem
  obtain ⟨K, D, nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp, comm, conc⟩ := F
  dsimp only at hX hL he hmemR ⊢
  cases conc with
  | symplectic n F' =>
    have hn : 3 ≤ n := three_le_of_nslType_cartanC type
    have hi₀ : i₀.val + 1 < n := KFact.lt_of_nslType_cartanC type
    have hF : Nat.card F' = 2 ^ f := (card_rootGroup_symplectic n F' i₀).symm.trans hX
    have hfin : Finite F' := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
    have hch : CharP F' 2 := KFact.charP_two_of_card (by omega) hF
    have hadm : StatedLieAdmissible .PSp n 2 f :=
      ⟨Nat.prime_two, by omega, by omega, fun h => by
        have h1 := congrArg Prod.fst h
        simp only at h1
        omega⟩
    have hLm : LieModel Y .PSp n 2 f := hL (Or.inl ⟨by decide,
      Symplectic.statedClassicalModel_center_quotient n F' hadm hF⟩)
    have hinj : Function.Injective Ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      have hc : Subgroup.center ↥(StatedSp n F') = ⊥ := by
        rw [Symplectic.center_eq, CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
      exact le_bot_iff.mp (hc ▸ ker)
    exact Or.inl ⟨n, F', inferInstance, hfin, hch, Ψ, hn, hF, hLm, hinj, surj, i₀, hi₀, hmemR⟩
  | @minus n K' _ b c hirr =>
    obtain ⟨hm, hi₀⟩ := of_nslType_cartanB (m := n - 1) type
    have hK : Nat.card K' = 2 ^ f := (card_rootGroup_minus n hirr hi₀).symm.trans hX
    have hfin : Finite K' := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have hadm : StatedLieAdmissible .POmegaMinus n 2 f :=
      ⟨Nat.prime_two, by omega, show 4 ≤ n by omega⟩
    exact Or.inr (Or.inl ⟨n, K', inferInstance, hfin, b, c, hirr, Ψ, show 4 ≤ n by omega, hK,
      hL (Or.inl ⟨by decide, Spin.statedClassicalModel_spin_quadMinus hadm hK hirr⟩), surj, ker,
      ⟨⟨i₀.val, by omega⟩, hi₀, mem⟩⟩)
  | g2 K' =>
    have hK : Nat.card K' = 2 ^ f := (card_rootGroup_g2 K' i₀).symm.trans hX
    have hfin : Finite K' := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have hq : 3 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
    exact Or.inr (Or.inr ⟨.G2, 0, f, by decide, by decide, by decide,
      hL (lieModel_G2_quotient Nat.prime_two (by omega) hq hK)⟩)
  | twistedD4 f' =>
    have hK : Nat.card (GaloisField 2 (3 * f')) = (2 ^ f') ^ 3 := by
      rw [GaloisField.card 2 (3 * f') (by have := Fact.out (p := 1 ≤ f'); omega), ← pow_mul,
        mul_comm]
    exact Or.inr (Or.inr ⟨.trialityD4, 0, f', by decide, by decide, by decide,
      lieModel_trialityD4_of_twistedGroup
      (Fact.out : 1 ≤ f') hK (fun c => iterateFrobenius_def _ _ _) he⟩)
  | f4 K' =>
    have hK : Nat.card K' = 2 ^ f := (KFact.card_rootGroup_f4 K' i₀).symm.trans hX
    have hfin : Finite K' := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have hadm : StatedLieAdmissible .F4 0 2 f := ⟨Nat.prime_two, by omega, rfl⟩
    exact Or.inr (Or.inr ⟨.F4, 0, f, by decide, by decide, by decide,
      hL (Or.inr (Or.inl ⟨rfl, by decide, hadm, K', inferInstance, inferInstance, hK,
        ⟨MulEquiv.refl _⟩⟩))⟩)
  | twistedE6 f' =>
    have hadm : StatedLieAdmissible .twistedE6 0 2 f' :=
      ⟨Nat.prime_two, Fact.out, rfl⟩
    exact Or.inr (Or.inr ⟨.twistedE6, 0, f', by decide, by decide, by decide,
      hL (CurtisTits.curtisTitsConclusion_twistedE6.{0} 2 f' hadm).1.2.2⟩)

end CertBound

end CFSG.RankThree.GF2n.Smith81.Insp
