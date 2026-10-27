module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin
open scoped commutatorElement

theorem card_perm_le_card_realized {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) {n : ℕ} (hn : 5 ≤ n) (hL : L = ⁅G, G⁆) (e : ↥G ≃* Equiv.Perm (Fin n)) :
    Subgroup.center ↥L = ⊥ ∧ Nat.card (Equiv.Perm (Fin n)) ≤ Nat.card (realized L) ∧
      Nonempty (↥L ≃* ↥(alternatingGroup (Fin n))) := by
  obtain ⟨-, hLn, hself, -⟩ := FFC.b4hyp_data hHyp
  obtain ⟨hs, hnab⟩ := FFC.commutator_simple_of_perm hn e
  obtain ⟨f⟩ := FFC.commutator_equiv_alternating hn e
  subst hL
  have hZ : Subgroup.center ↥⁅G, G⁆ = ⊥ := FFC.center_eq_bot_of_simple hnab
  have hGn : G ≤ Subgroup.normalizer ((⁅G, G⁆ : Subgroup (MulAut V)) : Set (MulAut V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hLn g hg x hx, fun hx => ?_⟩
    have h := hLn g⁻¹ (G.inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h
  have hGc : ∀ g ∈ G, (∀ l ∈ ⁅G, G⁆, g * l = l * g) → g = 1 := by
    intro g hg hcomm
    have hgL : g ∈ ⁅G, G⁆ := hself g hg hcomm
    have hcen : (⟨g, hgL⟩ : ↥⁅G, G⁆) ∈ Subgroup.center ↥⁅G, G⁆ := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Finite (MulAut ↥⁅G, G⁆) := MulEquiv.finite_left
  refine ⟨hZ, ?_, ⟨f⟩⟩
  rw [← Nat.card_congr e.toEquiv]
  exact card_le_card_realized hGn hGc

theorem case5Twist_holds : Case5Twist := by
  intro V _ _ _ G L A hHyp h5
  obtain ⟨-, -, -, hq⟩ := FFC.b4hyp_data hHyp
  have hJL : ffJ G ≠ L := FFC.ffJ_ne_of_case5 hq h5
  obtain ⟨⟨n, hn, π, hπ, -⟩, -⟩ := h5
  have hn5 : 5 ≤ n := by omega
  have hinj := FFC.injective_of_symDn_realizes hn5 hπ
  let e : Equiv.Perm (Fin n) ≃* ↥(ffJ G) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨hL, hGH⟩ := FFC.ident_perm hHyp hJL hn e.symm
  let eG : ↥G ≃* Equiv.Perm (Fin n) := (MulEquiv.subgroupCongr hGH).trans e.symm
  have hL' : L = ⁅G, G⁆ := by
    calc L = ⁅ffJ G, ffJ G⁆ := hL
      _ = ⁅G, G⁆ := by rw [← hGH]
  obtain ⟨hZ, hcard, ⟨f⟩⟩ := card_perm_le_card_realized hHyp hn5 hL' eG
  refine ⟨?_, Or.inl hZ⟩
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Finite (MulAut ↥L) := MulEquiv.finite_left
  apply stableMod_of_card
  have hA : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥(alternatingGroup (Fin n)) := by
    rw [Nat.card_congr (MulAut.congr f).toEquiv]
    exact FFC.card_mulAut_alternating_le (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
  omega

theorem case3TwistOne_holds : Case3TwistOne := by
  intro V _ _ _ G L hHyp h
  obtain ⟨⟨e6⟩, hL, hGH⟩ := FFC.ident_sp4 hHyp h
  let eG : ↥G ≃* Equiv.Perm (Fin 6) := (MulEquiv.subgroupCongr hGH).trans e6
  have hL' : L = ⁅G, G⁆ := by
    calc L = ⁅ffJ G, ffJ G⁆ := hL
      _ = ⁅G, G⁆ := by rw [← hGH]
  obtain ⟨hZ, hcard, ⟨f⟩⟩ := card_perm_le_card_realized hHyp (by norm_num) hL' eG
  refine ⟨?_, Or.inl hZ⟩
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Finite (MulAut ↥L) := MulEquiv.finite_left
  apply twoClassMod_of_card
  have h1 : Nat.card (MulAut ↥L) = 1440 := by
    rw [Nat.card_congr (MulAut.congr f).toEquiv]
    exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
  have h2 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  omega

end CFSG.Quasithin.F918X
