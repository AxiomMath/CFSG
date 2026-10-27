module

public import CFSG.Quasithin.Background.G10FifteenSplit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem irrPlus_conj {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I) {x : GLV V}
    (hx : x ∈ X) : IrrPlus (normalClosure Γ L) (conjSub x I) :=
  ((hI.isIrr hyp.fixedSpace_H).conj_of_normal (normalClosure_normal Γ L)
    (hyp.X_le hx)).irrPlus hyp.fixedSpace_H

theorem isDualOf_conj_of_isotropic (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hiso : Isotropic B I) :
    IsDualOf (normalClosure Γ L) I (conjSub x I) := by
  have hcompl := hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne
  have hrefl := hyp.toG101Hyp.isRefl
  have hiso' : Isotropic B (conjSub x I) := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rw [LinearEquiv.coe_coe]
    show B (x u) (x u') = 0
    rw [hyp.isometry x (hyp.X_le hx)]
    exact hiso u hu u' hu'
  have htop : ∀ v : V, ∃ a ∈ I, ∃ b ∈ conjSub x I, v = a + b := by
    intro v
    have hv : v ∈ I ⊔ conjSub x I := by
      rw [codisjoint_iff.1 hcompl.codisjoint]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    exact ⟨a, ha, b, hb, hab.symm⟩
  refine ⟨LinearMap.domRestrict₁₂ B (conjSub x I) I, fun j hj => ?_, fun i hi => ?_, ?_⟩
  · apply Subtype.ext
    apply hyp.nondegenerate
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := htop v
    rw [map_add]
    have h1 : B (j : V) a = 0 := hj ⟨a, ha⟩
    have h2 : B (j : V) b = 0 := hiso' j j.2 b hb
    rw [h1, h2, add_zero]
  · apply Subtype.ext
    apply hyp.nondegenerate
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := htop v
    rw [map_add]
    have h1 : B (i : V) a = 0 := hiso i i.2 a ha
    have h2 : B (i : V) b = 0 := hrefl _ _ (hi ⟨b, hb⟩)
    rw [h1, h2, add_zero]
  · intro k hk j j' i i' hj hi
    have : B (j' : V) (i' : V) = B (j : V) (i : V) := by
      rw [← hj, ← hi]
      exact hyp.isometry k (hyp.H_le hk) _ _
    exact this

theorem faithfulOn_of_isotropic (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hiso : Isotropic B I) :
    FaithfulOn (normalClosure Γ L) I := by
  have hdual := hyp.isDualOf_conj_of_isotropic h10 h11 h12 hI hfix hx hne hiso
  have hI' := hyp.irrPlus_conj hI hx
  have hce := centralizerOn_eq_of_isDualOf hI.1 hI'.1 hdual
  have hcompl := hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne
  rw [faithfulOn_iff]
  intro k hk hkI
  have hkI' : ∀ u ∈ conjSub x I, k u = u := by
    have hmem : k ∈ centralizerOn (normalClosure Γ L) I := ⟨hk, hkI⟩
    rw [hce] at hmem
    exact hmem.2
  have hkΓ : k ∈ Γ := hyp.H_le hk
  have : (⟨k, hkΓ⟩ : Γ) = 1 := by
    apply Subtype.ext
    ext v
    have hv : v ∈ I ⊔ conjSub x I := by
      rw [codisjoint_iff.1 hcompl.codisjoint]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    show k (a + b) = a + b
    rw [map_add, hkI a ha, hkI' b hb]
  exact congrArg Subtype.val this

theorem caseII (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hiso : Isotropic B I) :
    ¬ Homogeneous (normalClosure Γ L) ∧ ¬ SelfDual (normalClosure Γ L) I ∧
      FaithfulOn (normalClosure Γ L) I ∧ Isotropic B I ∧
      ∀ x' ∈ X, conjSub x' I ≠ I → IsDualOf (normalClosure Γ L) I (conjSub x' I) := by
  have hdual := hyp.isDualOf_conj_of_isotropic h10 h11 h12 hI hfix hx hne hiso
  have hI' := hyp.irrPlus_conj hI hx
  have hn : ¬ HIso (normalClosure Γ L) I (conjSub x I) := fun h => hne (hfix x hx h)
  have hperm := hyp.permutes hI hfix hx hne
  refine ⟨fun h => hn (h I (conjSub x I) hI hI'), fun hsd => hn ?_,
    hyp.faithfulOn_of_isotropic h10 h11 h12 hI hfix hx hne hiso, hiso, fun x' hx' hx'ne => ?_⟩
  · exact hiso_of_selfDual_isDual hI.1 hI'.1 hsd hdual
  · rw [(hperm x' hx').resolve_left hx'ne]
    exact hdual

end G108Hyp

end G11

end CFSG.Quasithin
