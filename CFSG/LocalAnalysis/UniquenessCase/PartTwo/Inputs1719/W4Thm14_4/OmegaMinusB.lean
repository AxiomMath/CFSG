module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.OrbitTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.EquivCopy
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

open CFSG.QuasithinUnique.A5.Delta5 (pact isEven vact)

private lemma irrSet_nonempty_of_isAlt_five {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (hL : IsAlt ↥L 5)
    (hsup : (⨆ I ∈ irrSet L, I) = ⊤) : (irrSet L).Nonempty := by
  classical
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hbot : (⊥ : Subgroup W) = ⊤ := by
    simpa [hempty] using hsup
  haveI hsubW : Subsingleton W := ⟨fun x y => by
    have hx : x ∈ (⊥ : Subgroup W) := by rw [hbot]; exact Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup W) := by rw [hbot]; exact Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]⟩
  haveI hsubA : Subsingleton (MulAut W) :=
    ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim (a x) (b x)⟩
  obtain ⟨e⟩ := hL
  have hnt : Nontrivial ↥L := e.isSimpleGroup.toNontrivial
  have hne : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp hnt
  have hbotL : L = ⊥ := by
    ext l
    simp only [Subgroup.mem_bot]
    exact ⟨fun _ => Subsingleton.elim l 1, fun h => h ▸ L.one_mem⟩
  exact hne hbotL

theorem commutator_eq_bot_of_alternatingNatural_of_mem_aSet_two {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L A : Subgroup (MulAut W)} {I : Subgroup W}
    (hI : AlternatingNatural L I ⊥ 5) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : A ∈ E3.aSet 2 Y) : ⁅L, A⁆ = ⊥ := by
  classical
  have hP : IsPGroup 2 ↥A := CFSG.Quasithin.E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  obtain ⟨s, φ, hφinj, hφeq, hcent⟩ :=
    exists_equivariant_copy_of_alternatingNatural hW hI hAN hP
  have hs2 : ∀ g : ↥A, s g * s g = 1 := by
    intro g
    have hg : g * g = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hA.2.2.1.2 (g : MulAut W) g.2
    calc s g * s g = s (g * g) := (map_mul s g g).symm
      _ = s 1 := by rw [hg]
      _ = 1 := map_one s
  have hsc : ∀ g h : ↥A, s g * s h = s h * s g := by
    intro g h
    have hgh : g * h = h * g :=
      Subtype.ext (hA.2.2.1.1 (g : MulAut W) g.2 (h : MulAut W) h.2)
    calc s g * s h = s (g * h) := (map_mul s g h).symm
      _ = s (h * g) := by rw [hgh]
      _ = s h * s g := map_mul s h g
  by_contra hne
  have hsne : ∃ g : ↥A, s g ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcent ⟨a, ha⟩ (hall ⟨a, ha⟩) l hl
  obtain ⟨x, hxeven, g₀, hmvx, horbx⟩ := exists_orbit_two_of_perm s hs2 hsc hsne
  let y₀ : ↥(CFSG.QuasithinUnique.evenWeight 5) := ⟨x, hxeven⟩
  let w : W := φ (s15T7OfEven y₀)
  have hact : ∀ a : ↥A, (a : MulAut W) w =
      φ (s15T7OfEven (vact (s a) y₀)) := by
    intro a
    dsimp only [w]
    rw [hφeq a (s15T7OfEven y₀), s15_T7_ofEven_vact]
  have hmv : (g₀ : MulAut W) w ≠ w := by
    intro h
    have h1 : φ (s15T7OfEven (vact (s g₀) y₀)) = φ (s15T7OfEven y₀) := by
      rw [← hact g₀]
      simpa only [w] using h
    have h2 := hφinj h1
    exact hmvx (congrArg Subtype.val
      (Function.LeftInverse.injective s15_T7_toEven_ofEven h2))
  have horb : ∀ a ∈ A, a w = w ∨ a w = (g₀ : MulAut W) w := by
    intro a ha
    have h := horbx (⟨a, ha⟩ : ↥A)
    rw [hact ⟨a, ha⟩, hact g₀]
    rcases h with hx1 | hx2
    · left
      rw [show vact (s ⟨a, ha⟩) y₀ = y₀ from Subtype.ext hx1]
    · right
      rw [show vact (s ⟨a, ha⟩) y₀ = vact (s g₀) y₀ from Subtype.ext hx2]
  exact not_orbit_two_of_mem_aSet_two hA g₀.2 hmv horb

theorem kA5OmegaMinusB_holds : KA5OmegaMinusB := by
  intro W _ _ hW Y L hLY hLn hL _ hsup hO
  have hlt : bParam L Y < 2 := by
    rw [bParam_lt_iff (by norm_num : 0 < 2) L Y]
    intro A hA
    have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      hA.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn)
    obtain ⟨I, hI⟩ := irrSet_nonempty_of_isAlt_five hL hsup
    exact commutator_eq_bot_of_alternatingNatural_of_mem_aSet_two hW (hO I hI) hAN hA
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
