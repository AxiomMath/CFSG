module

public import CFSG.Timmesfeld.RootInvolutionQuotient
import CFSG.Quasithin.Recognition.ProductDisconnected
import CFSG.RankThree.GF2n.Tim79aTransvectionHyp
import CFSG.RankThree.GF2n.Tim81.Cited.OddTranspRootL2
import CFSG.Timmesfeld.Bridge.OddTranspMain
import CFSG.Timmesfeld.RootInvolutionCenter
import CFSG.Timmesfeld.Transvection.LieModel
import CFSG.Timmesfeld.Transvection.OddBC2Rel
public import CFSG.Timmesfeld.Closure.MinCex

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

private theorem pCore_two_eq_bot {X : Type} [Group X] [Finite X]
    (h : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥) : CFSG.pCore 2 X = ⊥ := by
  have : Group.IsNilpotent (CFSG.pCore 2 X) := CFSG.pCore_isPGroup.isNilpotent
  exact h _ CFSG.pCore_normal inferInstance

private theorem meetsSq_image_center {Y : Type} [Group Y] {D : Set Y}
    (hroot : IsRootInvolutionSet D) (hDZ : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hsq : ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) :
    ∃ u ∈ QuotientGroup.mk' (Subgroup.center Y) '' D,
      ∃ v ∈ QuotientGroup.mk' (Subgroup.center Y) '' D, u ≠ v ∧ Commute u v ∧
        u * v ∈ QuotientGroup.mk' (Subgroup.center Y) '' D := by
  obtain ⟨u, hu, v, hv, -, hc, huv⟩ := hsq
  refine ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, fun h => hDZ _ huv ?_, hc.map _,
    ⟨u * v, huv, map_mul _ _ _⟩⟩
  have hz : u⁻¹ * v ∈ Subgroup.center Y := QuotientGroup.eq.mp h
  rwa [hroot.inv_eq hu] at hz

private theorem exists_lieModel_of_isBenderGroup {X : Type} [Group X]
    (h : CFSG.BenderSuzuki.IsBenderGroup X) :
    ∃ (t : StatedLieTag) (n f : ℕ), t ≠ .twistedF4 ∧ t ≠ .Tits ∧
      StatedLieAdmissible t n 2 f ∧ LieModel X t n 2 f := by
  rcases Quasithin.Recognition.lieModel_of_isBenderGroup h with ⟨f, -, h | h⟩ | ⟨a, -, h⟩
  · exact ⟨.PSL, 2, f, by decide, by decide, h.admissible, h⟩
  · exact ⟨.PSU, 3, f, by decide, by decide, h.admissible, h⟩
  · exact ⟨.twistedB2, 0, 2 * a + 1, by decide, by decide, h.admissible, h⟩

private theorem exists_lieModel_of_transvectionHyp {X : Type} [Group X] {Δ : Set (Subgroup X)}
    (hΔ : Transvection.TransvectionHyp X Δ) (h4 : ∀ A ∈ Δ, 4 ≤ Nat.card A) :
    ∃ (t : StatedLieTag) (n f : ℕ), t ≠ .twistedF4 ∧ t ≠ .Tits ∧
      StatedLieAdmissible t n 2 f ∧ LieModel X t n 2 f := by
  obtain ⟨f, hf, hcard, hT⟩ := Transvection.transvectionStatement_of_oddUnitary
    Transvection.oddUnitaryStatement_holds X Δ hΔ
  obtain ⟨A, hA, -⟩ := hΔ.rank
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have h := h4 A hA
    rw [hcard A hA, show f = 1 by omega] at h
    norm_num at h
  rcases Transvection.lieModel_of_transvectionConclusion hf hf2 hT with ⟨n, -, h⟩ | ⟨m, -, h⟩
  · exact ⟨.PSp, n, f, by decide, by decide, h.admissible, h⟩
  · exact ⟨.PSU, m, f, by decide, by decide, h.admissible, h⟩

theorem lieModel_quotient_center_of_degenerate {Y : Type} [Group Y] [Finite Y] {D : Set Y}
    (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g}) (hroot : IsRootInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤)
    (hsq : ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D)
    (h2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hDZ : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4) :
    ∃ (t : StatedLieTag) (n f : ℕ), t ≠ .twistedF4 ∧ t ≠ .Tits ∧
      StatedLieAdmissible t n 2 f ∧ CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) t n 2 f := by
  have hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y := by
    obtain ⟨u, hu, v, hv, hne, hc, huv⟩ := hsq
    exact fun _ hN hs => Bridge.le_center_of_isSolvable hcls hroot hgen hu hv hne hc huv h2 hN hs
  have hrad : ∀ N : Subgroup (Y ⧸ Subgroup.center Y), N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hs => by
      have := hN
      exact solvable_normal_eq_bot_quotient_center hsolv N hs
  have hS : Bridge.Asc72.Setup (Y ⧸ Subgroup.center Y)
      (QuotientGroup.mk' (Subgroup.center Y) '' D) :=
    ⟨image_isClass_center hcls, image_isOddTransp_center hroot hDZ hdeg,
      image_closure_eq_top_center hgen⟩
  have hsq' := meetsSq_image_center hroot hDZ hsq
  by_cases hdisc : Connectivity.Disconnected (QuotientGroup.mk' (Subgroup.center Y) '' D)
  · exact exists_lieModel_of_isBenderGroup
      (Bridge.OddTransp.oddTranspBender _ _ hS hrad hsq' hdisc)
  · refine exists_lieModel_of_transvectionHyp
      (RankThree.GF2n.Tim79a.transvectionHyp_of_connected RankThree.GF2n.Tim81.oddTranspRootL2
        hS (pCore_two_eq_bot hrad) (hrad _ inferInstance inferInstance) hsq' hdisc) ?_
    rintro A ⟨d, hd, rfl⟩
    exact RankThree.GF2n.Tim79a.four_le_card_closure_rootSet hS hsq' d hd

theorem lieModel_quotient_center_or_exception {Y : Type} [Group Y] [Finite Y] {D : Set Y}
    (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g}) (hroot : IsRootInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤)
    (hsq : ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D)
    (h2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hDZ : ∀ d ∈ D, d ∉ Subgroup.center Y) :
    (∃ (t : StatedLieTag) (n f : ℕ), t ≠ .twistedF4 ∧ t ≠ .Tits ∧
      StatedLieAdmissible t n 2 f ∧ CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) t n 2 f) ∨
    ((∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) ∧
      (CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSU 3 3 1 ∨
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6)) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic (Y ⧸ Subgroup.center Y) .J2)) := by
  by_cases hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4
  · rcases (outcome_quotient_center_of_nondegenerate hcls hroot hgen h2 hDZ
      hnd).lieModel_or_exception with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hnd, h⟩
  · push Not at hnd
    exact Or.inl (lieModel_quotient_center_of_degenerate hcls hroot hgen hsq h2 hDZ hnd)

end CFSG.Timmesfeld
