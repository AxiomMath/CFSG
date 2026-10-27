module

public import CFSG.Timmesfeld.Transvection.QTwoSetup
public import CFSG.Timmesfeld.Transvection.Lines
public import CFSG.Fischer.Classification.Basic.Trichotomy

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open CFSG.Timmesfeld.Transvection.QTwo

variable {H : Type} [Group H]

theorem connected_commGraph_rootElts [Finite H] {Δ : Set (Subgroup H)}
    (hΔ : IsTransvectionClass Δ) (h2 : ∀ A ∈ Δ, Nat.card A = 2)
    (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ Commuting A B) (hlines : MeetsLines Δ) :
    (commGraph (rootElts Δ)).Connected := by
  obtain ⟨A₀, hA₀, B₀, hB₀, hAB₀, hc₀⟩ := hrank
  obtain ⟨a₀, ha₀, rfl⟩ := (mem_iff_exists_zpowers hΔ h2 A₀).1 hA₀
  obtain ⟨b₀, hb₀, rfl⟩ := (mem_iff_exists_zpowers hΔ h2 _).1 hB₀
  have hab₀ : a₀ * b₀ = b₀ * a₀ := commuting_zpowers_iff.1 hc₀
  have hne₀ : a₀ ≠ b₀ := fun h => hAB₀ (by rw [h])
  have hreach : ∀ {x y : rootElts Δ}, (x : H) * y = y * x →
      (commGraph (rootElts Δ)).Reachable x y :=
    fun {x y} hxy => by
      by_cases h : x = y
      · rw [h]
      · exact SimpleGraph.Adj.reachable ⟨h, hxy⟩
  have : Nonempty (rootElts Δ) := ⟨⟨a₀, ha₀⟩⟩
  refine ⟨fun a c => ?_⟩
  have ha : IsConj a₀ (a : H) := (Set.ext_iff.1 (rootElts_eq_isConj hΔ h2 ha₀) a).1 a.2
  obtain ⟨g, hg⟩ := isConj_iff.1 ha
  have hbD : g * b₀ * g⁻¹ ∈ rootElts Δ := by
    rw [rootElts_eq_isConj hΔ h2 hb₀]
    exact isConj_iff.2 ⟨g, rfl⟩
  have hab : (a : H) * (g * b₀ * g⁻¹) = g * b₀ * g⁻¹ * a := by
    rw [← hg]
    calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
      _ = g * (b₀ * a₀) * g⁻¹ := by rw [hab₀]
      _ = g * b₀ * g⁻¹ * (g * a₀ * g⁻¹) := by group
  have hneab : (a : H) ≠ g * b₀ * g⁻¹ := by
    rw [← hg]
    intro h
    apply hne₀
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  have hzne : Subgroup.zpowers (a : H) ≠ Subgroup.zpowers (g * b₀ * g⁻¹) :=
    fun h => hneab (eq_of_zpowers_eq hΔ a.2 hbD h)
  obtain ⟨L, ⟨hL, hLline⟩, hcL⟩ := hlines _ (zpowers_mem hΔ h2 a.2) _ (zpowers_mem hΔ h2 hbD)
    hzne (commuting_zpowers_iff.2 hab) _ (zpowers_mem hΔ h2 c.2)
  obtain ⟨l, hl, rfl⟩ := (mem_iff_exists_zpowers hΔ h2 L).1 hL
  have hal : (a : H) * l = l * a := commuting_zpowers_iff.1
    (hLline _ (zpowers_mem hΔ h2 a.2) (hΔ.root.commuting_self (zpowers_mem hΔ h2 a.2))
      (commuting_zpowers_iff.2 hab))
  have hcl : (c : H) * l = l * c := commuting_zpowers_iff.1 hcL
  exact (hreach (x := a) (y := ⟨l, hl⟩) hal).trans (hreach (x := ⟨l, hl⟩) (y := c) hcl.symm)

theorem isSimpleGroup_commutator_of_card_two {H : Type} [Group H] [Finite H]
    {Δ : Set (Subgroup H)} (hΔ : IsTransvectionClass Δ) (hcen : Subgroup.center H = ⊥)
    (_hpts : PointsDetermined Δ) (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ Commuting A B)
    (hlines : MeetsLines Δ) (_hthick : ThickLines Δ)
    (hO2 : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N = ⊥)
    (hO3 : ∀ N : Subgroup H, N.Normal → IsPGroup 3 N → N = ⊥)
    (h2 : ∀ A ∈ Δ, Nat.card A = 2) : IsSimpleGroup (commutator H) := by
  obtain ⟨A₀, hA₀, -⟩ := id hrank
  obtain ⟨a₀, ha₀, -⟩ := (mem_iff_exists_zpowers hΔ h2 A₀).1 hA₀
  exact Pair.isSimpleGroup_commutator_of_connected (pair_rootElts hΔ h2 ha₀) hcen hO2 hO3
    (connected_commGraph_rootElts hΔ h2 hrank hlines)

end CFSG.Timmesfeld.Transvection
