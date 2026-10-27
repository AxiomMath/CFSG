module

public import CFSG.RankThree.GF2n.Tim79aIdentConnected
public import CFSG.Timmesfeld.Transvection.OneOrAll
public import CFSG.Timmesfeld.Transvection.Small

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

theorem le_of_commuting_conjSub (hΔ : IsRootClass Δ) {A L : Subgroup H}
    (hSL : (⨆ C ∈ Δ, ⨆ (_ : C ≤ Subgroup.centralizer (A : Set H)), C) ≤ L) {g : H}
    (hg : g ∈ L) {C : Subgroup H} (hC : C ∈ Δ) (hc : Commuting (conjSub A g) C) : C ≤ L := by
  have h1 : Commuting A (conjSub C g⁻¹) := by
    have := hc.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  have h2 : conjSub C g⁻¹ ≤ L := by
    refine le_trans ?_ hSL
    refine le_iSup₂_of_le (conjSub C g⁻¹) (hΔ.conjSub_mem hC g⁻¹) ?_
    exact le_iSup_of_le (commuting_iff_le_centralizer.1 h1) le_rfl
  have h3 : conjSub (conjSub C g⁻¹) g ≤ L := conjSub_le h2 hg
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h3

theorem iSup_sup_zpowers_eq_top_of_meetsLines (hΔ : TransvectionHyp H Δ) (hlines : MeetsLines Δ)
    {A B : Subgroup H} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : Opposite A B) {b : H} (hb : b ∈ B)
    (hb1 : b ≠ 1) :
    (⨆ C ∈ Δ, ⨆ (_ : C ≤ Subgroup.centralizer (A : Set H)), C) ⊔ Subgroup.zpowers b = ⊤ := by
  haveI := hΔ.finite
  have hR := hΔ.cls.root
  set L := (⨆ C ∈ Δ, ⨆ (_ : C ≤ Subgroup.centralizer (A : Set H)), C) ⊔ Subgroup.zpowers b
  have hkey : ∀ g ∈ L, ∀ C ∈ Δ, Commuting (conjSub A g) C → C ≤ L :=
    fun g hg C hC hc => le_of_commuting_conjSub hR le_sup_left hg hC hc
  have hAL : A ≤ L :=
    hkey 1 L.one_mem A hA (by rw [conjSub_one]; exact hR.commuting_self hA)
  have hbL : b ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
  have hg₀ : conjSub A (a⁻¹ * b) = B := by
    rw [conjSub_mul, ← hab, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hg₀L : a⁻¹ * b ∈ L := L.mul_mem (L.inv_mem (hAL ha)) hbL
  have hBL : B ≤ L := by
    rw [← hg₀]
    exact conjSub_le hAL hg₀L
  obtain ⟨Y, hY, hYA, hcAY⟩ : ∃ Y ∈ Δ, Y ≠ A ∧ Commuting A Y := by
    obtain ⟨A₁, hA₁, B₁, hB₁, hne, hc⟩ := hΔ.rank
    obtain ⟨x, rfl⟩ := hR.exists_conjSub_eq hA₁ hA
    exact ⟨conjSub B₁ x, hR.conjSub_mem hB₁ x, fun h => hne (conjSub_injective x h).symm,
      hc.conjSub x⟩
  obtain ⟨Z, hZ, hBZ⟩ := hlines A hA Y hY hYA.symm hcAY B hB
  have hBA : ¬ Commuting B A := fun h => hAB.not_commuting (hR.ne_bot A hA) h.symm
  have hout : ∀ W ∈ Δ, W ≤ L ∨ W ≤ Subgroup.centralizer (Z : Set H) := by
    intro W hW
    by_cases hWL : W ≤ L
    · exact Or.inl hWL
    right
    obtain ⟨Z', hZ', hWZ'⟩ := hlines A hA Y hY hYA.symm hcAY W hW
    by_cases hZZ' : Z' = Z
    · rw [hZZ'] at hWZ'
      exact commuting_iff_le_centralizer.1 hWZ'.symm
    exfalso
    have hnBZ' : ¬ Commuting B Z' := fun h =>
      hZZ' (eq_of_commuting_of_not_commuting hΔ.cls hΔ.points hA hY hYA.symm hcAY hZ hZ' hB
        hBA hBZ h).symm
    have hBZ'ne : B ≠ Z' := fun h => hnBZ' (h ▸ hR.commuting_self hB)
    have hopp : Opposite B Z' :=
      (hΔ.cls.commuting_or_opposite hB hZ'.1 hBZ'ne).resolve_left hnBZ'
    obtain ⟨c, hc, d, hd, hcd⟩ := Opposite.exists_conjSub_eq_mul hΔ.cls hB hopp
    have hZ'L : Z' ≤ L := hkey 1 L.one_mem Z' hZ'.1
      (by rw [conjSub_one]; exact (commuting_of_mem_lineOf' hΔ.cls hA hY hcAY hZ').1)
    have hxL : c⁻¹ * d * (a⁻¹ * b) ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem (hBL hc)) (hZ'L hd)) hg₀L
    have hZ'eq : conjSub A (c⁻¹ * d * (a⁻¹ * b)) = Z' := by
      rw [conjSub_mul, hg₀, hcd]
    exact hWL (hkey _ hxL W hW (by rw [hZ'eq]; exact hWZ'.symm))
  rcases eq_top_or_eq_top_of_forall_le hR hout with h | h
  · exact h
  · exfalso
    apply hR.ne_bot Z hZ.1
    rw [eq_bot_iff]
    intro z hz
    have hzc : z ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun g =>
      (Subgroup.mem_centralizer_iff.1 (h ▸ Subgroup.mem_top g) z hz).symm
    rw [hΔ.center] at hzc
    exact hzc

theorem iSup_sup_zpowers_eq_top (hΔ : TransvectionHyp H Δ) (h4 : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {A B : Subgroup H} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : Opposite A B) {b : H} (hb : b ∈ B)
    (hb1 : b ≠ 1) :
    (⨆ C ∈ Δ, ⨆ (_ : C ≤ Subgroup.centralizer (A : Set H)), C) ⊔ Subgroup.zpowers b = ⊤ :=
  iSup_sup_zpowers_eq_top_of_meetsLines hΔ (hΔ.meetsLines h4) hA hB hAB hb hb1

theorem transvectionGenerationStatement_holds : TransvectionGenerationStatement :=
  fun _ _ _ hΔ h4 _ hA _ hB hAB _ hb hb1 => iSup_sup_zpowers_eq_top hΔ h4 hA hB hAB hb hb1

end CFSG.RankThree.GF2n.Tim79a
