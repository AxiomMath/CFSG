module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwTorus
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Coprime

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

namespace InnerDiagTwE6

section Abstract

variable {F : Type*} [Field F] [CharP F 2] {U G : Type*} [Group U] [Group G]

theorem conj_eq_of_conj_sl2 (Φ : Matrix.SpecialLinearGroup (Fin 2) F →* U)
    (hΦ : Function.Injective Φ) (ψ : U →* G) (hker : ψ.ker ≤ Subgroup.center U)
    {P N : Subgroup U} (hP : ∀ c, Φ (sl2Upper c) ∈ P) (hN : ∀ z ∈ N, ∃ c, z = Φ (sl2Lower c))
    (hN' : ∀ c, Φ (sl2Lower c) ∈ N) {d : G} {h : U}
    (hh : h ∈ Subgroup.normalizer (N : Set U)) (hpos : ∀ z ∈ P, d⁻¹ * ψ z * d = ψ z)
    (hneg : ∀ z ∈ N, d⁻¹ * ψ z * d = ψ (h * z * h⁻¹)) :
    ∀ z ∈ N, d⁻¹ * ψ z * d = ψ z := by
  have hinj : Function.Injective (ψ.comp Φ) :=
    PsiDiag.injective_comp_of_ker_le_center Φ hΦ ψ hker
  have hconj : ∀ c, ∃ c', h * Φ (sl2Lower c) * h⁻¹ = Φ (sl2Lower c') := fun c =>
    hN _ ((Subgroup.mem_normalizer_iff.mp hh _).mp (hN' c))
  choose φ hφ using hconj
  have hid : ∀ c, φ c = c := PsiDiag.eq_of_conj_sl2 (ψ.comp Φ) hinj (d := d) (φ := φ)
    (fun c => hpos _ (hP c)) fun c => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hneg _ (hN' c), hφ c]
  intro z hz
  obtain ⟨c, rfl⟩ := hN z hz
  rw [hneg _ hz, hφ c, hid c]

end Abstract

section Twisted


variable {k : Type} [Field k] [CharP k 2] (θ : k →+* k)

theorem conj_eq_of_rankOne_fixed {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i) {G : Type*} [Group G]
    (ψ : fixedGroup k θ →* G) (hker : ψ.ker ≤ Subgroup.center (fixedGroup k θ)) {d : G}
    {h : fixedGroup k θ}
    (hh : h ∈ Subgroup.normalizer
      (twistedRootGroup k θ (-Pi.single i 1) : Set (fixedGroup k θ)))
    (hpos : ∀ z ∈ twistedRootGroup k θ (Pi.single i 1), d⁻¹ * ψ z * d = ψ z)
    (hneg : ∀ z ∈ twistedRootGroup k θ (-Pi.single i 1), d⁻¹ * ψ z * d = ψ (h * z * h⁻¹)) :
    ∀ z ∈ twistedRootGroup k θ (-Pi.single i 1), d⁻¹ * ψ z * d = ψ z := by
  subst hi
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have h2 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  refine conj_eq_of_conj_sl2 (slFixedNodeHom θ ha) (slFixedNodeHom_injective θ ha) ψ hker
    (fun c => ?_) (fun z hz => ?_) (fun c => ?_) hh hpos hneg
  · exact (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) (proj_single a) h1 _).2
      ⟨c, c.2, slFixedNodeE_upper θ a c⟩
  · obtain ⟨c, hc, hzc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) (proj_neg_single a) h2 z).1 hz
    exact ⟨⟨c, hc⟩, Subtype.ext (hzc.trans (slFixedNodeE_lower θ a ⟨c, hc⟩).symm)⟩
  · exact (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) (proj_neg_single a) h2
      _).2 ⟨c, c.2, slFixedNodeE_lower θ a c⟩

variable (hθ : ∀ c, θ (θ c) = c)

include hθ in
theorem conj_eq_of_rankOne_pair {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hi : orbitMap a = i) {G : Type*} [Group G] (ψ : fixedGroup k θ →* G)
    (hker : ψ.ker ≤ Subgroup.center (fixedGroup k θ)) {d : G} {h : fixedGroup k θ}
    (hh : h ∈ Subgroup.normalizer
      (twistedRootGroup k θ (-Pi.single i 1) : Set (fixedGroup k θ)))
    (hpos : ∀ z ∈ twistedRootGroup k θ (Pi.single i 1), d⁻¹ * ψ z * d = ψ z)
    (hneg : ∀ z ∈ twistedRootGroup k θ (-Pi.single i 1), d⁻¹ * ψ z * d = ψ (h * z * h⁻¹)) :
    ∀ z ∈ twistedRootGroup k θ (-Pi.single i 1), d⁻¹ * ψ z * d = ψ z := by
  subst hi
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne2 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hU : ∀ c : k, sl2Upper c = Minuscule.MinData.Valid.slUpper k c := fun _ => rfl
  have hL : ∀ c : k, sl2Lower c = Minuscule.MinData.Valid.slLower k c := fun _ => rfl
  refine conj_eq_of_conj_sl2 (slOrbitHom θ hθ hab) (slOrbitHom_injective θ hθ hab) ψ hker
    (fun c => ?_) (fun z hz => ?_) (fun c => ?_) hh hpos hneg
  · refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) (proj_single a) hne1 _).2
      ⟨c, ?_⟩
    rw [hU, slOrbitHom_upper, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]
  · obtain ⟨c, hc⟩ :=
      (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) (proj_neg_single a) hne2 z).1 hz
    refine ⟨c, Subtype.ext ?_⟩
    rw [hc, hL, slOrbitHom_slLower, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one,
      one_mul]
  · refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) (proj_neg_single a) hne2
      _).2 ⟨c, ?_⟩
    rw [hL, slOrbitHom_slLower, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one, one_mul]

end Twisted

section Holds


theorem twE6RankOneInput_holds (f : ℕ) (hf : 1 ≤ f) : TwE6RankOneInput f := by
  intro G _ ψ hker d j h hh hpos hneg
  have hN : h ∈ Subgroup.normalizer
      ((twistedE6Datum 2 f).rootGroup (-Pi.single j 1) : Set (twistedE6Group 2 f)) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh _ (neg_single_mem_roots (D := twistedE6Datum 2 f) j)
  fin_cases j
  · exact conj_eq_of_rankOne_fixed (frobQ 2 f) (a := nd 1) (i := nf 0) rfl rfl ψ hker hN hpos
      hneg
  · exact conj_eq_of_rankOne_fixed (frobQ 2 f) (a := nd 3) (i := nf 1) rfl rfl ψ hker hN hpos
      hneg
  · exact conj_eq_of_rankOne_pair (frobQ 2 f) (frobQ_frobQ 2 f hf) (a := nd 2) (b := nd 4)
      (Or.inl ⟨rfl, rfl⟩) (i := nf 2) rfl ψ hker hN hpos hneg
  · exact conj_eq_of_rankOne_pair (frobQ 2 f) (frobQ_frobQ 2 f hf) (a := nd 0) (b := nd 5)
      (Or.inr ⟨rfl, rfl⟩) (i := nf 3) rfl ψ hker hN hpos hneg

end Holds

end InnerDiagTwE6

section Genuine

theorem ggInnerDiagMarkingAt_twistedE6 : GGInnerDiagMarkingAt .twistedE6 :=
  ggInnerDiagMarkingAt_twistedE6_of_rankOne InnerDiagTwE6.twE6RankOneInput_holds

end Genuine

end CFSG.StandardType
