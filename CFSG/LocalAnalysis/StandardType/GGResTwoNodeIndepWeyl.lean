module

public import CFSG.LocalAnalysis.StandardType.GGRCClassify
public import CFSG.LocalAnalysis.StandardType.GGRCWeylOfPerm
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGIndepPm1 (p n : ℕ) [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs)) : Prop :=
  ZS.AbsIrred p (A.map (ggLin (p := p) ι)) → ∀ f : Module.Basis (Fin n) (ZMod p) V,
    (∀ a ∈ A.map (ggLin (p := p) ι), ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) →
    ∃ b' : Module.Basis (Fin n) (ZMod p) V, ∀ a ∈ A.map (ggLin (p := p) ι),
      ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
        (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i)

theorem ggIndep_map_reflGen {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (A' : Subgroup (MulAut ↥Bs)) (hgen' : GGReflGenerated p A') :
    A'.map (ggLin (p := p) ι) = Subgroup.closure
      {r | r ∈ A'.map (ggLin (p := p) ι) ∧ GGLinRefl r} := by
  let A : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  change A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r}
  apply le_antisymm
  · calc A = (Subgroup.closure {φ | φ ∈ A' ∧ GGIsReflection p φ}).map (ggLin (p := p) ι) := by
          change A'.map (ggLin (p := p) ι) = _
          rw [← hgen']
      _ = Subgroup.closure ((ggLin (p := p) ι) '' {φ | φ ∈ A' ∧ GGIsReflection p φ}) :=
          MonoidHom.map_closure _ _
      _ ≤ Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} := by
          apply Subgroup.closure_mono
          rintro _ ⟨φ, ⟨hφA, hφr⟩, rfl⟩
          exact ⟨Subgroup.mem_map.mpr ⟨φ, hφA, rfl⟩,
            (ggRC_isReflection_iff_linRefl (p := p) ι φ).mp hφr⟩
  · rw [Subgroup.closure_le]
    intro z hz
    exact hz.1

theorem ggIndep_weyl_of_classify (hKG : GGReflClassLargeInput') {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) {n : ℕ} (hn : Module.finrank (ZMod p) V = n)
    (h9 : 9 ≤ n) (A' : Subgroup (MulAut ↥Bs)) (hgen' : GGReflGenerated p A')
    (hirr : ZS.AbsIrred p (A'.map (ggLin (p := p) ι)))
    (hsmall : 8 * Nat.card ↥A' < p ^ (n * (n - 1) / 2))
    (hpm1 : 5 ≤ p → GGIndepPm1 p n ι A') :
    GGWeylReflectionGroup p A' := by
  let A : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} := ggIndep_map_reflGen ι A' hgen'
  have hcardA : Nat.card ↥A = Nat.card ↥A' :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv).symm
  have hsmallA : 8 * Nat.card ↥A < p ^ (n * (n - 1) / 2) := by
    rw [hcardA]
    exact hsmall
  obtain hclass | ⟨N, hN, e, he⟩ :=
    ggRC_classify hKG hp2 hn h9 A hirr hgen hsmallA (fun h5 f hmon => hpm1 h5 hirr f hmon)
  · exact ggRC_weylReflGroup_of_linWeyl ι A' hclass
  · let e' : A' ≃* Equiv.Perm (Fin N) :=
      (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)).trans e
    have hrefl' : ∀ r : A', GGIsReflection p (r : MulAut ↥Bs) →
        ∃ i j, i ≠ j ∧ e' r = Equiv.swap i j := by
      intro r hr
      have hrlin : GGLinRefl (ggLin (p := p) ι (r : MulAut ↥Bs)) :=
        (ggRC_isReflection_iff_linRefl (p := p) ι (r : MulAut ↥Bs)).mp hr
      obtain ⟨i, j, hij, heij⟩ :=
        he (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι) r) hrlin
      exact ⟨i, j, hij, heij⟩
    exact ggRC_weyl_of_perm A' hN e' hrefl' hgen'

end CFSG.StandardType

end
