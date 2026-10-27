module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenCoreB
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUClassLarge

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTen_core {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (hKG : GGReflClassLargeInput') [Finite V] {ι : Type} [Fintype ι] (h : ι → V)
    (α : ι → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2) (r : ι → (V ≃ₗ[ZMod 3] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hA : A = Subgroup.closure (Set.range r))
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j)
    (hker : ∀ v, (∀ i, α i v = 0) → v = 0)
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hd : 9 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)))
    (hV : Module.finrank (ZMod 3) V ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) + 1)
    (hcard : 8 * Nat.card A < 3 ^ (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) *
      (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) - 1) / 2)) :
    ZS.LinWeyl 3 A := by
  classical
  have hsub := ggTen_sub_mem_span h α r hr A hA
  have hinv : ∀ g ∈ A, ∀ w ∈ Submodule.span (ZMod 3) (Set.range h),
      g w ∈ Submodule.span (ZMod 3) (Set.range h) := by
    intro g hg w hw
    have h1 := Submodule.add_mem _ (hsub g hg w) hw
    rwa [sub_add_cancel] at h1
  have hfaith := ggTen_faithful h α r hr A hA hnt hV
  have hinj : Function.Injective
      (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine hfaith (g : V ≃ₗ[ZMod 3] V) g.2 (fun u hu => ?_)
    have h1 := congrArg
      (fun φ => ((φ ⟨u, hu⟩ : Submodule.span (ZMod 3) (Set.range h)) : V)) hg
    simpa using h1
  have hcardQ : Nat.card (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range =
      Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hQ := HdRo7SU.su_linWeyl_of_card_lt hKG (p := 3) rfl hd rfl
    (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range
    (ggTen_absIrred h α hα r hr A hA hconn hker hinv)
    (ggTen_Q_reflGen h α hα r hr A hA hinv) (by rw [hcardQ]; exact hcard)
  exact ggTen_linWeyl_lift h α hα r hr A hA hinv hfaith hQ

theorem ggTen_core_of_card_lt {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hKG : GGReflClassLargeInput') (hKS : GGReflClassOmegaSmall) [Finite V] {ι : Type}
    [Fintype ι] (h : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
    (r : ι → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r))
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j)
    (hker : ∀ v ∈ Submodule.span (ZMod 3) (Set.range h), (∀ i, α i v = 0) → v = 0)
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hd : 5 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)))
    (hV : Module.finrank (ZMod 3) V ≤
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) + 1)
    (hcard : 8 * Nat.card A < 3 ^
      (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) *
        (Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) - 1) / 2)) :
    ZS.LinWeyl 3 A := by
  classical
  have hsub := ggTen_sub_mem_span h α r hr A hA
  have hinv : ∀ g ∈ A, ∀ w ∈ Submodule.span (ZMod 3) (Set.range h),
      g w ∈ Submodule.span (ZMod 3) (Set.range h) := by
    intro g hg w hw
    have h1 := Submodule.add_mem _ (hsub g hg w) hw
    rwa [sub_add_cancel] at h1
  have hfaith := ggTen_faithful h α r hr A hA hnt hV
  have hinj : Function.Injective
      (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine hfaith (g : V ≃ₗ[ZMod 3] V) g.2 (fun u hu => ?_)
    have h1 := congrArg
      (fun φ => ((φ ⟨u, hu⟩ : Submodule.span (ZMod 3) (Set.range h)) : V)) hg
    simpa using h1
  have hcardQ : Nat.card
      (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range =
      Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hirr : ZS.AbsIrred 3
      (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range :=
    ggTen_absIrred_on_span h α hα r hr A hA hconn hker hinv
  have hrefl : (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range =
      Subgroup.closure {s | s ∈
        (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range ∧ GGLinRefl s} :=
    ggTen_Q_reflGen h α hα r hr A hA hinv
  have hQ : ZS.LinWeyl 3
      (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range := by
    haveI : Module.Finite (ZMod 3) ↥(Submodule.span (ZMod 3) (Set.range h)) :=
      Module.Finite.of_finite
    let d : ℕ := Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h))
    have hd5 : 5 ≤ d := by simpa [d] using hd
    have hfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = d := rfl
    have hcard' : 8 * Nat.card
        (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range <
        3 ^ (d * (d - 1) / 2) := by
      rw [hcardQ]
      simpa [d] using hcard
    by_cases h9 : 9 ≤ d
    · exact HdRo7SU.su_linWeyl_of_card_lt hKG (p := 3) rfl (d := d) h9 hfin
        (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range hirr hrefl hcard'
    · have h8 : d ≤ 8 := by omega
      exact HdRo7SU.su_linWeyl_of_card_lt_small hKS (d := d) hd5 h8 hfin
        (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range hirr hrefl hcard'
  exact ggTen_linWeyl_lift h α hα r hr A hA hinv hfaith hQ

theorem ggTen_core_of_negated_complement {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Finite V] {ι : Type} [Fintype ι]
    (hKG : GGReflClassLargeInput') (hKS : GGReflClassOmegaSmall)
    (h : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
    (r : ι → V ≃ₗ[ZMod 3] V) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r))
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j)
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧
      ∀ w, g (g w - w) = g w - w)) (hTF : QTwoLin.TransvectionFree A)
    (S : Submodule (ZMod 3) V) (x : V)
    (hcomp : IsCompl S (Submodule.span (ZMod 3) ({x} : Set V)))
    (hST : S ≤ Submodule.span (ZMod 3) (Set.range h))
    (h5 : 5 ≤ Module.finrank (ZMod 3) S)
    (hdim : Module.finrank (ZMod 3) V = Module.finrank (ZMod 3) S + 1)
    (z : V ≃ₗ[ZMod 3] V) (hz : z ∈ A) (hzS : ∀ s ∈ S, z s = -s) (hzx : z x = x)
    (hker : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) ({x} : Set V))
    (hfull : 8 * Nat.card A < 3 ^
      ((Module.finrank (ZMod 3) S + 1) * Module.finrank (ZMod 3) S / 2))
    (hfix : (∀ g ∈ A, g x = x) → 8 * Nat.card A < 3 ^
      (Module.finrank (ZMod 3) S * (Module.finrank (ZMod 3) S - 1) / 2)) :
    ZS.LinWeyl 3 A := by
  classical
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let T : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hrefl : ∀ i, Module.reflection (hα i) = r i := by
    intro i
    ext v
    rw [Module.reflection_apply, hr]
  have hrA : ∀ i, Module.reflection (hα i) ∈ A := by
    intro i
    rw [hrefl i, hA]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hkerT := QTwoLin.reflection_kernel_on_span_of_negated_complement
    hTF hcomp hz hzS hzx h α hα hrA hker
  have hle : Module.finrank (ZMod 3) S ≤ Module.finrank (ZMod 3) T :=
    Submodule.finrank_mono hST
  have htop : Module.finrank (ZMod 3) T ≤ Module.finrank (ZMod 3) V :=
    Submodule.finrank_le T
  apply ggTen_core_of_card_lt hKG hKS h α hα r hr A hA hconn hkerT hnt
    (by change 5 ≤ Module.finrank (ZMod 3) T; omega)
    (by change Module.finrank (ZMod 3) V ≤ Module.finrank (ZMod 3) T + 1; omega)
  by_cases hd : Module.finrank (ZMod 3) T = Module.finrank (ZMod 3) S
  · have hTS : T = S := (Submodule.eq_of_le_of_finrank_eq hST hd.symm).symm
    have hfixA : ∀ g ∈ A, g x = x := by
      have hgen : A ≤ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x := by
        rw [hA, Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        apply MulAction.mem_stabilizer_iff.mpr
        rw [← hrefl i]
        apply QTwoLin.reflection_fixes_of_negated_root hTF (hα i) (hrA i) hz
          (hzS (h i) ?_) hzx
        rw [← hTS]
        exact Submodule.subset_span (Set.mem_range_self i)
      intro g hg
      exact MulAction.mem_stabilizer_iff.mp (hgen hg)
    simpa only [T, hd] using hfix hfixA
  · have hd' : Module.finrank (ZMod 3) T = Module.finrank (ZMod 3) S + 1 := by omega
    change 8 * Nat.card A < 3 ^
      (Module.finrank (ZMod 3) T * (Module.finrank (ZMod 3) T - 1) / 2)
    simpa only [hd', Nat.add_sub_cancel] using hfull

end CFSG.StandardType

end
