module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5ActualCountInputs
public import CFSG.LocalAnalysis.StandardType.GGK2E6OriginalAxes
public import CFSG.LocalAnalysis.StandardType.GGK2E6D5ActualStabilizer
public import CFSG.LocalAnalysis.StandardType.GGK2E6D5E6OrbitCount
public import CFSG.LocalAnalysis.StandardType.GGK2E6E6OriginalOutsideAxisTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem GGResHyp.false_of_D5_E6_original_data
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φL : Fin 5 → MulAut ↥Bs) (hL : Fin 5 → V)
    (αL : Fin 5 → Dual (ZMod 3) V)
    (hpairL : ∀ i j, αL i (hL j) = (CartanMatrix.D 5 i j : ZMod 3))
    (hlinL : ∀ i w, ggLin (p := 3) ι (φL i) w = w - αL i w • hL i)
    (fL : (ggCoxeterMatrixD 5).Group ≃* ↥(ggAutomizer L Bs))
    (hfL : ∀ i, (fL ((ggCoxeterMatrixD 5).simple i) : MulAut ↥Bs) = φL i)
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hreflL : ∀ i, GGIsReflection 3 (φL i))
    (φK : Fin 6 → MulAut ↥Bs) (hK : Fin 6 → V)
    (αK : Fin 6 → Dual (ZMod 3) V)
    (hpairK : ∀ i j, αK i (hK j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hlinK : ∀ i w, ggLin (p := 3) ι (φK i) w = w - αK i w • hK i)
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (fK : (CoxeterMatrix.E₆).Group ≃* ↥(ggAutomizer K Bs))
    (hdepK : ¬ LinearIndependent (ZMod 3) hK)
    (hcardBs : Nat.card Bs = 3 ^ 6) : False := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hSstar : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
  have hSHat : LargeEvenSHat 3 B y K := hH.2.2.2.2.1.1
  have hx : x ∈ Bs := hH.1.2.1.1 hSstar.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  let Q := (ggAutomizer K Bs).map (ggLin (p := 3) ι)
  let H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)
  let xv := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let yv := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hx0 : xv ≠ 0 := by
    intro hzero
    have hxB1 : (⟨x, hx⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      apply ι.injective
      simpa [xv] using hzero
    exact hx1 (congrArg Subtype.val hxB1)
  have hselfL : ∀ i, αL i (hL i) = 2 := by
    intro i
    rw [hpairL]
    fin_cases i <;> decide
  have hαx : ∀ i, αL i xv = 0 := by
    intro i
    have hmem : φL i ∈ ggAutomizer L Bs := by
      rw [hgenL]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hfix : φL i (⟨x, hx⟩ : ↥Bs) = (⟨x, hx⟩ : ↥Bs) :=
      ggAutomizer_apply_eq_of_le_centralizer hSstar.2.2.2.1.1 hmem
    have hfixV := (ggLin_fix_iff (p := 3) ι (φL i) (⟨x, hx⟩ : ↥Bs)).mp hfix
    rw [hlinL i] at hfixV
    have hz : αL i xv • hL i = 0 := sub_eq_self.mp hfixV
    have hne : hL i ≠ 0 := by
      intro hzero
      have hc := hselfL i
      rw [hzero, map_zero] at hc
      exact (by decide : (0 : ZMod 3) ≠ 2) hc
    exact (smul_eq_zero.mp hz).resolve_right hne
  obtain ⟨_, _, ⟨a, ha, hmove⟩, hst⟩ :=
    d5_actual_count_inputs hH ι hL αL φL fL hfL hx hy hselfL hpairL hx0 hαx
      hcardBs hlinL hreflL hgenL
  let t := ggLin (p := 3) ι a
  have ht : t ∈ H := ⟨a, (show ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs from le_sup_left) ha, rfl⟩
  have hty : t yv ≠ yv := by
    intro heq
    apply hmove
    rw [show ggLin (p := 3) ι a yv = yv from heq]
    exact Submodule.mem_span_singleton_self yv
  have hQy : ∀ g ∈ Q, g yv = yv := by
    intro g hg
    obtain ⟨a', ha', rfl⟩ := hg
    have hKy : K ≤ Subgroup.centralizer ({y} : Set G) :=
      (hH.2.2.2.2.1.1 : LargeEvenSHat 3 B y K).2.2.2.1
    exact (ggLin_fix_iff (p := 3) ι a' (⟨y, hy⟩ : ↥Bs)).mp
      (ggAutomizer_apply_eq_of_le_centralizer hKy ha')
  have hQcard : Nat.card Q = 51840 := by
    calc Nat.card Q = Nat.card (ggAutomizer K Bs) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer K Bs)
          (ggLin (p := 3) ι) (ggLin_injective (p := 3) ι)).toEquiv).symm
      _ = Nat.card (CoxeterMatrix.E₆).Group := (Nat.card_congr fK.toEquiv).symm
      _ = 51840 := card_coxeterE6_group
  have hV : Nat.card V = 3 ^ 6 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ 6 := hcardBs
  have ho : 72 ≤ Nat.card (MulAction.orbit Q (t yv)) :=
    hH.K_E6_actual_orbit_ge_72 ι hy φK hK αK hpairK hlinK hgenK hcardBs hdepK hmove
  exact d5_e6_join_false_of_actual_counts (Subgroup.map_mono le_sup_right)
    hQcard hV hx0 hQy hst ht hty ho

end CFSG.StandardType

end
