module

public import CFSG.Quasithin.Background.G10FifteenRing
public import CFSG.Quasithin.Background.G10Local

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem conjSub_comm {x y : GLV V} (h : x * y = y * x) (U : Submodule (ZMod 2) V) :
    conjSub x (conjSub y U) = conjSub y (conjSub x U) := by
  rw [← conjSub_mul, ← conjSub_mul, h]

theorem conjSub_conjSub_of_sq {x : GLV V} (h : x * x = 1) (U : Submodule (ZMod 2) V) :
    conjSub x (conjSub x U) = U := by
  rw [← conjSub_mul, h, conjSub_one]

section Swap

variable [Finite V] {Γ H X : Subgroup (GLV V)}

theorem swap_lemma (hXΓ : X ≤ Γ) (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hX2 : ∀ a ∈ X, a * a = 1)
    {I : Submodule (ZMod 2) V} (hI : IsIrr H I)
    (hfix : ∀ z ∈ X, HIso H I (conjSub z I) → conjSub z I = I) {x : GLV V} (hx : x ∈ X)
    (hne : conjSub x I ≠ I) {y : GLV V} (hy : y ∈ X) {a b : V} (ha : a ∈ I)
    (hb : b ∈ conjSub x I) (ha0 : a ≠ 0) (hyab : y (a + b) = a + b) :
    conjSub y I = I ∨ conjSub y I = conjSub x I := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  let S : Set (Submodule (ZMod 2) V) := {J | IsIrr H J ∧ ¬ HIso H J I}
  have hS : ∀ z ∈ X, conjSub z I ≠ I → conjSub z I ∈ S := by
    intro z hz hz1
    have hzirr : IsIrr H (conjSub z I) := hI.conj_of_normal hN (hXΓ hz)
    refine ⟨hzirr, fun hiso => hz1 ?_⟩
    exact hfix z hz (hiso_symm hzirr.1 hI.1 hiso)
  have hSirr : ∀ J ∈ S, IsIrr H J := fun J hJ => hJ.1
  have hSI : ∀ J ∈ S, ¬ HIso H J I := fun J hJ => hJ.2
  have hxy : x * y = y * x := hXc x hx y hy
  have hI'S : conjSub x I ∈ S := hS x hx hne
  have hyx : conjSub (y * x) I ≠ I := by
    intro h
    apply h2
    have h3 : conjSub x (conjSub (y * x) I) = conjSub x I := by rw [h]
    rw [← conjSub_mul] at h3
    have e : x * (y * x) = y := by
      rw [← mul_assoc, hxy, mul_assoc, hX2 x hx, mul_one]
    rw [e] at h3
    exact h3
  have hI'yS : conjSub (y * x) I ∈ S := hS (y * x) (X.mul_mem hy hx) hyx
  have hIyS : conjSub y I ∈ S := hS y hy h1
  have hya : y a ∈ sSup S := le_sSup hIyS (apply_mem_conjSub ha)
  have hyb : y b ∈ sSup S := by
    refine le_sSup hI'yS ?_
    rw [conjSub_mul]
    exact apply_mem_conjSub hb
  have hb' : b ∈ sSup S := le_sSup hI'S hb
  have hab : a = (y a + y b) - b := by
    rw [← map_add, hyab]
    abel
  have hamem : a ∈ sSup S := by
    rw [hab]
    exact (sSup S).sub_mem ((sSup S).add_mem hya hyb) hb'
  have hbot := homComp_inf_eq_bot hI S hSirr hSI
  have : a ∈ homComp H I ⊓ sSup S := ⟨le_homComp hI ha, hamem⟩
  rw [hbot, Submodule.mem_bot] at this
  exact ha0 this

@[expose] def permSub (X : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (x : GLV V)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hx : x ∈ X) (hX2 : ∀ a ∈ X, a * a = 1) :
    Subgroup (GLV V) where
  carrier := {y | y ∈ X ∧ (conjSub y I = I ∨ conjSub y I = conjSub x I)}
  one_mem' := ⟨X.one_mem, Or.inl (conjSub_one I)⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨X.mul_mem ha hb, ?_⟩
    have hax : a * x = x * a := hXc a ha x hx
    rw [conjSub_mul]
    rcases hb' with hb' | hb'
    · rw [hb']
      exact ha'
    · rw [hb', ← conjSub_mul, hax, conjSub_mul]
      rcases ha' with ha' | ha'
      · rw [ha']
        right
        rfl
      · rw [ha', conjSub_conjSub_of_sq (hX2 x hx)]
        left
        rfl
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨X.inv_mem ha, ?_⟩
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hX2 a ha)
    rw [this]
    exact ha'

end Swap


theorem finrank_le_finrank_inf_perp_add_one [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (hnd : B.Nondegenerate) {v : V} (hv : v ≠ 0) (I : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) ↥(I ⊓ perp B v) + 1 := by
  have hperp : perp B v = B.orthogonal (Submodule.span (ZMod 2) {v}) := by
    ext w
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hw n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
      show B (c • v) w = 0
      rw [LinearMap.map_smul, LinearMap.smul_apply]
      have : B v w = 0 := hw
      rw [this, smul_zero]
    · intro hw
      exact hw v (Submodule.mem_span_singleton_self v)
  have h0 := LinearMap.BilinForm.finrank_orthogonal hnd (Submodule.span (ZMod 2) {v})
  rw [← hperp, finrank_span_singleton hv] at h0
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq I (perp B v)
  have h4 : Module.finrank (ZMod 2) ↥(I ⊔ perp B v) ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_le _
  have h5 : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨v, hv⟩
  omega

theorem exists_two_ne [Finite V] {U : Submodule (ZMod 2) V} (h : 2 ≤ Module.finrank (ZMod 2) U) :
    ∃ u ∈ U, ∃ u' ∈ U, u ≠ 0 ∧ u' ≠ 0 ∧ u ≠ u' := by
  have hnt : Nontrivial ↥U := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨⟨u, hu⟩, hu0⟩ := exists_ne (0 : ↥U)
  have hu0' : u ≠ 0 := fun h0 => hu0 (Subtype.ext h0)
  have hex : ∃ u' ∈ U, u' ∉ Submodule.span (ZMod 2) {u} := by
    by_contra hcon
    push Not at hcon
    have : Module.finrank (ZMod 2) ↥U ≤ 1 := by
      rw [finrank_le_one_iff]
      refine ⟨⟨u, hu⟩, fun y => ?_⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hcon y y.2)
      exact ⟨c, Subtype.ext hc⟩
    omega
  obtain ⟨u', hu', hn⟩ := hex
  refine ⟨u, hu, u', hu', hu0', ?_, ?_⟩
  · intro h0
    apply hn
    rw [h0]
    exact Submodule.zero_mem _
  · intro h0
    apply hn
    rw [← h0]
    exact Submodule.mem_span_singleton_self _

theorem eq_zero_of_conj_add {I : Submodule (ZMod 2) V} {x : GLV V}
    (hTI : conjSub x I ⊓ I = ⊥) {z : V} (hz : z ∈ I) (h : x z + z = 0) : z = 0 := by
  have h1 : x z = z := by
    have := eq_neg_of_add_eq_zero_left h
    rw [this]
    exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 z)
  have h2 : z ∈ conjSub x I := by
    rw [← h1]
    exact apply_mem_conjSub hz
  have : z ∈ conjSub x I ⊓ I := ⟨h2, hz⟩
  rw [hTI, Submodule.mem_bot] at this
  exact this

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem permutes {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) :
    ∀ y ∈ X, conjSub y I = I ∨ conjSub y I = conjSub x I := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := hyp.X_comm
  have hX2 : ∀ a ∈ X, a * a = 1 := hyp.X_sq
  have hsw := fun {y} (hy : y ∈ X) {a b : V} (ha : a ∈ I) (hb : b ∈ conjSub x I) (ha0 : a ≠ 0)
      (hyab : y (a + b) = a + b) => swap_lemma hyp.X_le (normalClosure_normal Γ L) hXc hX2 hirr
        hfix hx hne hy ha hb ha0 hyab
  have hTI : conjSub x I ⊓ I = ⊥ := by
    rcases hirr.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) (hyp.X_le hx) with h | h
    · exact absurd h hne
    · exact h
  have hW : ∀ u ∈ I ⊓ perp B v₁, x u + u ∈ W := by
    intro u hu
    have := hyp.commutator_le x hx u hu.2
    have h2 : x u + u = x u - u := by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_zmod2 u)]
    rw [h2]
    exact this
  have hmem : ∀ u ∈ I, x u ∈ conjSub x I := fun u hu => apply_mem_conjSub hu
  by_cases hA : ∃ u ∈ I ⊓ perp B v₁, x u + u = v₁
  · obtain ⟨u, hu, hv⟩ := hA
    have hu0 : u ≠ 0 := by
      rintro rfl
      apply hyp.point
      rw [← hv, map_zero, add_zero]
    intro y hy
    refine hsw hy hu.1 (hmem u hu.1) hu0 ?_
    rw [add_comm u (x u), hv]
    exact hyp.X_fixes y hy
  · push Not at hA
    have hdim : 2 ≤ Module.finrank (ZMod 2) ↥(I ⊓ perp B v₁) := by
      have h1 := finrank_le_finrank_inf_perp_add_one hyp.toG101Hyp.nondegenerate' hyp.point I
      have h2 := hyp.two_lt_finrank hirr
      omega
    obtain ⟨u, hu, u', hu', hu0, hu'0, huu'⟩ := exists_two_ne hdim
    have hφ0 : ∀ z ∈ I, x z + z = 0 → z = 0 := fun z hz h => eq_zero_of_conj_add hTI hz h
    have hwne : ∀ z ∈ I ⊓ perp B v₁, z ≠ 0 → x z + z ≠ 0 := fun z hz hz0 h => hz0 (hφ0 z hz.1 h)
    have hwW : x u + u ∈ W := hW u hu
    have hw'W : x u' + u' ∈ W := hW u' hu'
    have hwv : x u + u ∉ Submodule.span (ZMod 2) {v₁} := by
      intro hmemw
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmemw
      rcases hc2 c with rfl | rfl
      · rw [zero_smul] at hc
        exact hwne u hu hu0 hc.symm
      · rw [one_smul] at hc
        exact hA u hu hc.symm
    have hw'v : x u' + u' ∉ Submodule.span (ZMod 2) {v₁, x u + u} := by
      intro hmemw
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hmemw
      have hz : u' + u ∈ I ⊓ perp B v₁ := (I ⊓ perp B v₁).add_mem hu' hu
      have hzsum : x (u' + u) + (u' + u) = (x u' + u') + (x u + u) := by
        rw [map_add]
        abel
      rcases hc2 a with rfl | rfl <;> rcases hc2 b with rfl | rfl
      · rw [zero_smul, zero_smul, add_zero] at hab
        exact hwne u' hu' hu'0 hab.symm
      · rw [zero_smul, one_smul, zero_add] at hab
        have h0 : x (u' + u) + (u' + u) = 0 := by
          rw [hzsum, ← hab]
          exact add_self_eq_zero_of_zmod2 _
        have hz0 : u' + u = 0 := hφ0 _ hz.1 h0
        apply huu'
        have : u' = -u := eq_neg_of_add_eq_zero_left hz0
        rw [this]
        exact (neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 u)).symm
      · rw [one_smul, zero_smul, add_zero] at hab
        exact hA u' hu' hab.symm
      · rw [one_smul, one_smul] at hab
        apply hA _ hz
        rw [hzsum, ← hab, add_assoc, add_self_eq_zero_of_zmod2, add_zero]
    have hh1 := hyp.toG101Hyp.relIndex_fixIn hwW hwv
    have hh2 := hyp.toG101Hyp.relIndex_fixIn hw'W
      (fun hs => hw'v (Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hs))
    have hne12 := hyp.toG101Hyp.fixIn_ne hwW hw'W hwv hw'v
    have hle1 : fixIn X (x u + u) ≤ X := fun y hy => hy.1
    have hle2 : fixIn X (x u' + u') ≤ X := fun y hy => hy.1
    have hsup := sup_eq_of_relIndex_two hle1 hle2 hh1 hh2 hne12
    let P := permSub X I x hXc hx hX2
    have hP : ∀ (z : V) (hz : z ∈ I), z ≠ 0 → ∀ y ∈ fixIn X (x z + z), y ∈ P := by
      intro z hz hz0 y hy
      refine ⟨hy.1, hsw hy.1 hz (hmem z hz) hz0 ?_⟩
      rw [add_comm z (x z)]
      exact hy.2
    have hXP : X ≤ P := by
      rw [← hsup]
      exact sup_le (fun y hy => hP u hu.1 hu0 y hy) (fun y hy => hP u' hu'.1 hu'0 y hy)
    intro y hy
    exact (hXP hy).2

end G108Hyp

end G11

end CFSG.Quasithin
