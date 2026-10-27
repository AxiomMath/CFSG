module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUOpp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUGen
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary GGOppRad

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

omit [CharP F 2] in
theorem exists_lt_of_suU_ne_bot {σ : F ≃+* F} {n : ℕ} {ℓ : Fin n → ℕ} (h : suU σ ℓ ≠ ⊥) :
    ∃ c a, ℓ c < ℓ a := by
  by_contra hno
  refine h ((Subgroup.eq_bot_iff_forall _).mpr fun g hg => Subtype.ext (Units.ext ?_))
  ext c a
  rw [Subgroup.coe_one, Units.val_one]
  exact mem_suU_iff.mp hg c a fun hca => hno ⟨c, a, hca⟩

theorem exists_SU_eichler' (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {x y : Fin n → F}
    (hx : (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).β x x = 0)
    (hxy : (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).β x y = 0) :
    ∃ (c : F) (g : SU (unitaryInvolution F 2 f) n),
      ((suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).β y y = 0 → c = 0) ∧
      ∀ v, natRep (SU (unitaryInvolution F 2 f) n) g v =
        v + (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).β x v •
          (y + c • x) +
        (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).β y v • x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n
  by_cases hyy : B.β y y = 0
  · obtain ⟨g, hg⟩ := exists_SU_eichler (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      hx hxy (c := 0) (by rw [map_zero, add_zero, hyy])
    exact ⟨0, g, fun _ => rfl, hg⟩
  · have hfix : unitaryInvolution F 2 f (B.β y y) = B.β y y := by
      rw [← suForm_symm]
    obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hF hfix
    obtain ⟨g, hg⟩ := exists_SU_eichler (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      hx hxy hc
    exact ⟨c, g, fun h => absurd h hyy, hg⟩

theorem ggOppRadGood_suU (hF : Nat.card F = (2 ^ f) ^ 2) {n M : ℕ} (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {ℓ : Fin n → ℕ} (hℓ : IsSULevel M ℓ)
    (hQ : GGRadicalTwo ⊤ (suU (unitaryInvolution F 2 f) ℓ))
    (hN : (⊤ : Subgroup (SU (unitaryInvolution F 2 f) n)) ⊓
      Subgroup.normalizer (suU (unitaryInvolution F 2 f) ℓ :
        Set (SU (unitaryInvolution F 2 f) n)) = suP (unitaryInvolution F 2 f) ℓ)
    (hne : suU (unitaryInvolution F 2 f) ℓ ≠ ⊥) :
    GGOppRadGood ⊤ (suU (unitaryInvolution F 2 f) ℓ) := by
  set σ := unitaryInvolution F 2 f
  have hσ := unitaryInvolution_involutive hF
  refine ⟨suU σ (ℓ ∘ Fin.rev),
    ⟨radicalTwo_suU_comp_rev hQ, card_suU_comp_rev ℓ, ?_⟩,
    sup_suU_comp_rev hF hn hnq hℓ hne, fun V hV => ?_⟩
  · rw [hN]
    exact suU_comp_rev_inf_suP hℓ
  obtain ⟨hVrad, hVcard, hVbot⟩ := hV
  set F' := isoFlag (suForm σ hσ n) (natRep (SU σ n)) V with hF'def
  obtain ⟨hVeq, -⟩ := eq_flagKernel_isoFlag_of_radical (suForm σ hσ n) (natRep (SU σ n))
    (natRep_injective _) (isIsometric_natRep_SU σ hσ n) hVrad
  have hbot : flagKernel (natRep (SU σ n)) F' ⊓ flagStab (natRep (SU σ n)) (stdFlag ℓ) = ⊥ := by
    rw [← hVeq]
    rw [hN] at hVbot
    exact hVbot
  have hF' := isSelfDual_isoFlag (suForm σ hσ n) (natRep (SU σ n)) V
  have hA := isSelfDual_stdFlag_su σ hσ hℓ
  have hcompl : ∀ j, ∃ k, IsCompl (stdFlag ℓ k) (F' j) :=
    exists_isCompl_of_inf_eq_bot' (natRep (SU σ n))
      (fun x hx => exists_SU_transvection σ hσ hx)
      (fun _ _ hx hxy => exists_SU_eichler' hF hx hxy) hA hF' hbot
  obtain ⟨u, i, hi, hu, huF, hle⟩ :=
    exists_eq_flagMap_of_isCompl_su σ hσ hℓ hF' (by omega) hcompl
  have hVD : V = (suU σ i).map (MulAut.conj u).toMonoidHom := by
    rw [suU, ← flagKernel_flagMap, huF]
    exact hVeq
  have hcV : Nat.card V = Nat.card (suU σ i) := by
    rw [hVD]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hc1 : Nat.card (suU σ ℓ) ≤ Nat.card (suU σ (i ∘ Fin.rev)) := by
    rw [card_suU_comp_rev, ← hcV, hVcard]
  have heq : suU σ (i ∘ Fin.rev) = suU σ ℓ := Subgroup.eq_of_le_of_card_ge hle hc1
  have hii : (i ∘ Fin.rev) ∘ Fin.rev = i := by
    funext a
    simp
  have heq' : suU σ i = suU σ (ℓ ∘ Fin.rev) := by
    rw [← hii, suU_comp_rev, heq, ← suU_comp_rev]
  exact ⟨u, hu, hVD.trans (by rw [heq'])⟩

variable (F f) in
@[expose] def GGSUIsoFlagStdAt (n : ℕ) (hF : Nat.card F = (2 ^ f) ^ 2) : Prop :=
  ∀ R : Subgroup (SU (unitaryInvolution F 2 f) n), ∃ (g : SU (unitaryInvolution F 2 f) n)
    (ℓ : Fin n → ℕ), IsSULevel (2 * Module.finrank F (Fin n → F)) ℓ ∧
    isoFlag (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n)
        (natRep (SU (unitaryInvolution F 2 f) n)) R =
      GGOppRad.flagMap (natRep (SU (unitaryInvolution F 2 f) n)) g (stdFlag ℓ)

theorem ggOppRadGood_su (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (hstd : GGSUIsoFlagStdAt F f n hF)
    {Q : Subgroup (SU (unitaryInvolution F 2 f) n)} (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ⊤ Q) :
    GGOppRadGood ⊤ Q := by
  obtain ⟨hQeq, hQN⟩ := eq_flagKernel_isoFlag_of_radical
    (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n)
    (natRep (SU (unitaryInvolution F 2 f) n)) (natRep_injective _)
    (isIsometric_natRep_SU (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n) hQ
  obtain ⟨g, ℓ, hℓ, hF'⟩ := hstd Q
  have hQU : Q = (suU (unitaryInvolution F 2 f) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [suU, ← flagKernel_flagMap, ← hF']
    exact hQeq
  have hQP : Subgroup.normalizer (Q : Set (SU (unitaryInvolution F 2 f) n)) =
      (suP (unitaryInvolution F 2 f) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [suP, ← flagStab_flagMap, ← hF', ← hQN, top_inf_eq]
  have hQ0 : suU (unitaryInvolution F 2 f) ℓ = Q.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hQU, ← GGTwoSig.map_conj_mul, inv_mul_cancel, GGTwoSig.map_conj_one]
  have hrad0 : GGRadicalTwo ⊤ (suU (unitaryInvolution F 2 f) ℓ) := by
    rw [hQ0]
    exact hQ.map_conj (mem_normalizer_top _)
  have hN0 : (⊤ : Subgroup (SU (unitaryInvolution F 2 f) n)) ⊓
      Subgroup.normalizer (suU (unitaryInvolution F 2 f) ℓ : Set (SU (unitaryInvolution F 2 f) n)) =
        suP (unitaryInvolution F 2 f) ℓ := by
    rw [hQ0, top_inf_eq, ← GGTwoSig.map_conj_normalizer, hQP, ← GGTwoSig.map_conj_mul,
      inv_mul_cancel, GGTwoSig.map_conj_one]
  have hne0 : suU (unitaryInvolution F 2 f) ℓ ≠ ⊥ := fun h =>
    hQne (by rw [hQU, h, Subgroup.map_bot])
  rw [hQU]
  exact (ggOppRadGood_suU hF hn hnq hℓ hrad0 hN0 hne0).map_conj (mem_normalizer_top g)

end GGOppRadSpU

end CFSG.StandardType
