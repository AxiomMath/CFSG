module

public import CFSG.Quasithin.Background.SmithB42LnL4Case10
public import CFSG.Quasithin.Background.SmithB42Alt7Ctx
public import CFSG.Quasithin.Background.B5FinS8
public import CFSG.Quasithin.Background.B3Two
public import CFSG.Quasithin.Background.F918V7
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.EmptyFaithful.LRed4Orth
public import CFSG.Quasithin.EmptyFaithful.A38c5Model
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Quasithin.Background.B3Facts
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall Matrix CFSG.Assembly.LowTwoRank

theorem swap01_mem_Am : Equiv.swap (0 : Fin 8) 1 ∈ B3.Am 8 1 := by
  refine Subgroup.subset_closure ?_
  show Equiv.swap (0 : Fin 8) 1 ∈ B3.gensAm 8 1
  unfold B3.gensAm B3.ti B3.swapN
  simp only [List.range_one, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  rfl

theorem ffJ_model :
    ffJ ((⊤ : Subgroup (B3.Gp 8)).map (B3.Mod.act 8 B3.Mod.ut0)) =
      (⊤ : Subgroup (B3.Gp 8)).map (B3.Mod.act 8 B3.Mod.ut0) := by
  set X := (⊤ : Subgroup (B3.Gp 8)).map (B3.Mod.act 8 B3.Mod.ut0) with hX
  refine le_antisymm (B6.ffJ_le _) ?_
  have key : Subgroup.closure {σ : B3.Gp 8 | σ.IsSwap} ≤
      (ffJ X).comap (B3.Mod.act 8 B3.Mod.ut0) := by
    rw [Subgroup.closure_le]
    rintro σ ⟨a, b, hab, rfl⟩
    obtain ⟨g, hg⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap (by decide : (0 : Fin 8) ≠ 1) hab)
    have hoff : B3.IsOffG 8 B3.Mod.ut0 (B3.cj g (B3.Am 8 1)) :=
      ((B3.B3_2_6).1 _).2 (Or.inr (Or.inr (Or.inl ⟨1, le_rfl, by norm_num, g, rfl⟩)))
    have hmem : Equiv.swap a b ∈ B3.cj g (B3.Am 8 1) := by
      rw [B3.mem_cj, ← hg]
      have : g⁻¹ * (g * Equiv.swap (0 : Fin 8) 1 * g⁻¹) * g = Equiv.swap 0 1 := by group
      rw [this]
      exact swap01_mem_Am
    exact B6.le_ffJ hoff ⟨_, hmem, rfl⟩
  rw [Equiv.Perm.closure_isSwap] at key
  rw [hX, Subgroup.map_le_iff_le_comap]
  exact key

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem commutator_eq_L_core (hHyp : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) : ⁅G, G⁆ = L := by
  have hLG : L ≤ G := le_G_core hHyp
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    by_cases hgL : g ∈ L <;> by_cases hhL : h ∈ L
    · exact L.mul_mem (L.mul_mem (L.mul_mem hgL hhL) (L.inv_mem hgL)) (L.inv_mem hhL)
    · have h1 : h * g⁻¹ * h⁻¹ ∈ L := conj_mem_core hHyp hh (L.inv_mem hgL)
      have e1 : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by group
      rw [e1]
      exact L.mul_mem hgL h1
    · exact L.mul_mem (conj_mem_core hHyp hg hhL) (L.inv_mem hhL)
    · have h1 := mul_mem_of_not_mem4_core hHyp hZ e hg hh hgL hhL
      have h2 := mul_mem_of_not_mem4_core hHyp hZ e (G.inv_mem hg) (G.inv_mem hh)
        (fun h0 => hgL (by simpa using L.inv_mem h0)) (fun h0 => hhL (by simpa using L.inv_mem h0))
      have e1 : g * h * g⁻¹ * h⁻¹ = (g * h) * (g⁻¹ * h⁻¹) := by group
      rw [e1]
      exact L.mul_mem h1 h2
  · have hperf : commutator ↥L = ⊤ := hHyp.2.1.1.commutator_eq_top
    have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc L = (⊤ : Subgroup ↥L).map L.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = ⁅L, L⁆ := by rw [← hperf, h1]
      _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono hLG hLG

theorem nonempty_equiv_perm8_core (hHyp : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥)
    (ι : ↥L ≃* alternatingGroup (Fin 8)) (hGL : G ≠ L) :
    Nonempty (↥G ≃* Equiv.Perm (Fin 8)) := by
  obtain ⟨θ, hinj, hθL⟩ := B42Alt7.exists_embedding_of (m := 8) (by norm_num) (by norm_num)
    hHyp.1 hZ ι
  have hLG : L ≤ G := le_G_core hHyp
  obtain ⟨a, haG, haL⟩ : ∃ a ∈ G, a ∉ L := by
    by_contra hall
    push Not at hall
    exact hGL (le_antisymm hall hLG)
  have hA8 : alternatingGroup (Fin 8) ≤ θ.range := by
    intro σ hσ
    obtain ⟨l, hl⟩ := ι.surjective ⟨σ, hσ⟩
    refine ⟨⟨l, hLG l.2⟩, ?_⟩
    rw [hθL l (hLG l.2), hl]
  have hne : θ ⟨a, haG⟩ ∉ alternatingGroup (Fin 8) := by
    intro h
    obtain ⟨l, hl⟩ := ι.surjective ⟨θ ⟨a, haG⟩, h⟩
    have h1 : θ ⟨l, hLG l.2⟩ = θ ⟨a, haG⟩ := by
      rw [hθL l (hLG l.2), hl]
    have h2 : (l : MulAut V) = a := congrArg Subtype.val (hinj h1)
    exact haL (h2 ▸ l.2)
  have hrange : θ.range = ⊤ := by
    have hidx := Subgroup.relIndex_mul_index hA8
    rw [alternatingGroup.index_eq_two] at hidx
    have hidx2 : θ.range.index ∣ 2 := ⟨_, by rw [mul_comm] at hidx; exact hidx.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx2 with h1 | h2
    · exact Subgroup.index_eq_one.1 h1
    · exfalso
      rw [h2] at hidx
      have h1 : (alternatingGroup (Fin 8)).relIndex θ.range = 1 := by omega
      rw [Subgroup.relIndex_eq_one] at h1
      exact hne (h1 ⟨⟨a, haG⟩, rfl⟩)
  exact ⟨MulEquiv.ofBijective θ ⟨hinj, MonoidHom.range_eq_top.1 hrange⟩⟩

section Coords

variable [Module (ZMod 2) (Additive V)] {e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))}
  {β : Additive V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}

theorem case10_ne_core (hV : ∀ v : V, v ^ 2 = 1)
    (hHyp : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥) (ι : ↥L ≃* alternatingGroup (Fin 8))
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w)) (hGL : G ≠ L) :
    B42Case10 G L A := by
  have hθ := nonempty_equiv_perm8_core hHyp hZ ι hGL
  have hext : SLExteriorTwo ⁅G, G⁆ ⊤ ⊥ 4 := by
    rw [commutator_eq_L_core hHyp hZ e]
    exact slExteriorTwo_of_wedge4 e hβ
  have hsym : SymmetricNatural G ⊤ ⊥ 8 := symmetricNatural_eight_top G hθ hext
  obtain ⟨q, hq, hnd, ⟨E, hE, hEq⟩, hcard, hGq⟩ := LRed4.exists_quad_of_symmetricNatural_eight hsym
  obtain ⟨ε, hε⟩ := A38c5.exists_model_mulEquiv hV q hq hnd E hE hEq hcard
  have hGmap : G.map (MulAut.congr ε).toMonoidHom =
      (⊤ : Subgroup (B3.Gp 8)).map (B3.Mod.act 8 B3.Mod.ut0) := by
    rw [← MonoidHom.range_eq_map, ← hε, hGq]
  refine ⟨slExteriorTwo_of_wedge4 e hβ, Or.inr ⟨?_, hθ, ?_⟩⟩
  ·
    have h1 := ffJ_map_mulAutCongr ε G
    rw [hGmap, ffJ_model] at h1
    exact (Subgroup.map_injective (MulAut.congr ε).injective (h1.symm.trans hGmap.symm)).symm
  ·
    have h1 := H13.kq_map_congr ε G 2
    have h2 := (B3.B3_2_6).2.2
    unfold qOf at h2 ⊢
    rw [← h1]
    exact (congrArg (fun X => kq X 2) hGmap).trans h2

end Coords

end CFSG.Quasithin.B42Ln
