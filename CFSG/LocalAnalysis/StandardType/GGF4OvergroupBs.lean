module

public import CFSG.LocalAnalysis.StandardType.GGF4Overgroup
public import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGF4WeylData
public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGF4CrossPair
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGF4FrameData
import CFSG.LocalAnalysis.StandardType.GGF4ReflGroup

public section

namespace CFSG.StandardType

namespace F4Model

theorem reflPair_pow : ∀ x, x < 24 → ∀ y, y < 24 →
    pw3 ((Rm x).mul (Rm y)) = M4.one ∨ pw4 ((Rm x).mul (Rm y)) = M4.one := by decide +kernel

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem refl_mul_pow {w w' : W} (hw : R.IsRefl w) (hw' : R.IsRefl w') :
    (w * w') ^ 3 = 1 ∨ (w * w') ^ 4 = 1 := by
  obtain ⟨x, hx, hxρ⟩ := R.refl_rep hw
  obtain ⟨y, hy, hyρ⟩ := R.refl_rep hw'
  have hρ : R.ρ (w * w') = ((Rm x).mul (Rm y)).toMat := R.rho_mul hxρ hyρ
  rcases reflPair_pow x hx y hy with h | h
  · left
    apply R.inj
    rw [map_pow, hρ, map_one, pow_three, ← M4.toMat_mul, ← M4.toMat_mul]
    change (pw3 ((Rm x).mul (Rm y))).toMat = 1
    rw [h, M4.toMat_one]
  · right
    apply R.inj
    rw [map_pow, hρ, map_one, pow_four_eq, ← M4.toMat_mul, ← M4.toMat_mul]
    change (pw4 ((Rm x).mul (Rm y))).toMat = 1
    rw [h, M4.toMat_one]

theorem card_le_of_isRefl {s : Finset W} (hs : ∀ w ∈ s, R.IsRefl w) : s.card ≤ 24 := by
  classical
  have key : ∀ w ∈ s, ∃ x, x < 24 ∧ R.ρ w = (Rm x).toMat := fun w hw => R.refl_rep (hs w hw)
  choose! f hf using key
  calc s.card ≤ (Finset.range 24).card := by
        refine Finset.card_le_card_of_injOn f ?_ ?_
        · intro w hw
          exact Finset.mem_range.2 (hf w hw).1
        · intro w hw w' hw' h
          exact R.inj ((hf w hw).2.trans (by rw [h]; exact (hf w' hw').2.symm))
    _ = 24 := Finset.card_range 24

end F4Rep

end F4Model

namespace F4Over

open Multiplicative SpCoord CFSG.Open


theorem ggF4_eq_stdF4_of_signedB4_le {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hEl : IsElemAbelian 5 Bs) (hNT : GGNoTransvection 5 Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    (hA : GGWeylOfType 5 CoxeterMatrix.F₄ A) (κ : V5 ≃* ↥Bs)
    (hH : signedB4.map (MulAut.congr κ).toMonoidHom ≤ A) :
    A = stdF4.map (MulAut.congr κ).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set c : MulAut V5 ≃* MulAut ↥Bs := MulAut.congr κ with hc
  set A' : Subgroup (MulAut V5) := A.comap c.toMonoidHom with hA'
  have hmem : ∀ r, r ∈ A' ↔ c r ∈ A := fun _ => Iff.rfl
  have hrefl_iff : ∀ r : MulAut V5, IsReflF r ↔ GGIsReflection 5 (c r) := by
    intro r
    have hcr : ∀ b : ↥Bs, c r b = κ (r (κ.symm b)) := fun _ => rfl
    have hfix : Nat.card {b : ↥Bs // c r b = b} = Nat.card {f : V5 // r f = f} := by
      refine Nat.card_congr ⟨fun b => ⟨κ.symm b.1, ?_⟩, fun f => ⟨κ f.1, ?_⟩, fun b => ?_, fun f => ?_⟩
      · have h := b.2
        rw [hcr] at h
        rw [← κ.symm_apply_apply (r (κ.symm b.1)), h]
      · rw [hcr, κ.symm_apply_apply, f.2]
      · exact Subtype.ext (κ.apply_symm_apply b.1)
      · exact Subtype.ext (κ.symm_apply_apply f.1)
    have hcard : Nat.card ↥Bs = Nat.card V5 := Nat.card_congr κ.symm.toEquiv
    constructor
    · rintro ⟨h2, hc5⟩
      exact ⟨by rw [← map_pow, h2, map_one], by rw [hfix, hcard]; exact hc5⟩
    · rintro ⟨h2, hc5⟩
      refine ⟨c.injective (by rw [map_pow, h2, map_one]), ?_⟩
      rw [← hfix, ← hcard]
      exact hc5
  obtain ⟨e, he⟩ := hA
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hnotG2 : ¬ ∃ e' : Fin 2 ≃ Fin 4, CoxeterMatrix.F₄ = CoxeterMatrix.G₂.reindex e' := by
    rintro ⟨e', -⟩
    simpa using Fintype.card_congr e'
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hWrefl : ∀ (r : MulAut ↥Bs) (hr : r ∈ A), GGIsReflection 5 r →
      R.IsRefl (e.symm ⟨r, hr⟩) := by
    intro r hr hrr
    obtain ⟨i, g, hg⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G 5 Bs (by norm_num)
      (by norm_num) hEl hNT A hAind (Fin 4) CoxeterMatrix.F₄ hF4W hnotG2 e he ⟨r, hr⟩ hrr
    rw [hg, MulEquiv.symm_apply_apply]
    exact (F4Model.F4Rep.isRefl_iff hRs).2 ⟨g, i, rfl⟩
  let ι : CoxeterMatrix.F₄.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιe : ∀ (r : MulAut ↥Bs) (hr : r ∈ A), ι (e.symm ⟨r, hr⟩) = r := fun r hr => by
    simp [ι]
  have hgen : A' ≤ Subgroup.closure {r | r ∈ A' ∧ IsReflF r} := by
    intro r hr
    have htop : Subgroup.closure (Set.range CoxeterMatrix.F₄.simple) = ⊤ :=
      CoxeterMatrix.F₄.toCoxeterSystem.subgroup_closure_range_simple
    let ψ : CoxeterMatrix.F₄.Group →* MulAut V5 := c.symm.toMonoidHom.comp ι
    have hψ : ψ (e.symm ⟨c r, (hmem r).1 hr⟩) = r := by
      change c.symm (ι (e.symm ⟨c r, (hmem r).1 hr⟩)) = r
      rw [hιe, MulEquiv.symm_apply_apply]
    have hle : (Subgroup.closure (Set.range CoxeterMatrix.F₄.simple)).map ψ ≤
        Subgroup.closure {r | r ∈ A' ∧ IsReflF r} := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have hci : c (ψ (CoxeterMatrix.F₄.simple i)) = ι (CoxeterMatrix.F₄.simple i) := by
        change c (c.symm (ι (CoxeterMatrix.F₄.simple i))) = _
        rw [MulEquiv.apply_symm_apply]
      refine ⟨?_, ?_⟩
      · rw [hmem, hci]
        exact (e (CoxeterMatrix.F₄.simple i)).2
      · rw [hrefl_iff, hci]
        exact he i
    rw [← hψ]
    exact hle (Subgroup.mem_map_of_mem ψ (htop ▸ Subgroup.mem_top _))
  have hA'eq : A' = stdF4 := by
    refine eq_stdF4 (fun g hg => hH ⟨g, hg, rfl⟩) hgen ?_ ?_ ?_
    · intro s hs
      let F : MulAut V5 → CoxeterMatrix.F₄.Group := fun r =>
        if h : c r ∈ A then e.symm ⟨c r, h⟩ else 1
      have hFinj : Set.InjOn F s := by
        intro r hr r' hr' h
        have h1 := (hs r hr).1
        have h2 := (hs r' hr').1
        simp only [F, dif_pos ((hmem r).1 h1), dif_pos ((hmem r').1 h2)] at h
        exact c.injective (congrArg Subtype.val (e.symm.injective h))
      calc s.card = (s.image F).card := (Finset.card_image_of_injOn hFinj).symm
        _ ≤ 24 := by
          refine R.card_le_of_isRefl fun w hw => ?_
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hw
          have h1 := (hmem r).1 (hs r hr).1
          simp only [F, dif_pos h1]
          exact hWrefl (c r) h1 ((hrefl_iff r).1 (hs r hr).2)
    · intro x hx y hy hxr hyr
      have hx' : c x ∈ A := (hmem x).1 hx
      have hy' : c y ∈ A := (hmem y).1 hy
      have hw := hWrefl (c x) hx' ((hrefl_iff x).1 hxr)
      have hw' := hWrefl (c y) hy' ((hrefl_iff y).1 hyr)
      have key : ∀ n : ℕ, (x * y) ^ n = 1 ↔
          (e.symm ⟨c x, hx'⟩ * e.symm ⟨c y, hy'⟩) ^ n = 1 := by
        intro n
        have h : c ((x * y) ^ n) = ι ((e.symm ⟨c x, hx'⟩ * e.symm ⟨c y, hy'⟩) ^ n) := by
          rw [map_pow, map_pow, map_mul, map_mul, hιe (c x) hx', hιe (c y) hy']
        constructor
        · intro h1
          apply hι
          rw [← h, h1, map_one, map_one]
        · intro h1
          apply c.injective
          rw [h, h1, map_one, map_one]
      rcases R.refl_mul_pow hw hw' with h | h
      · exact Or.inl ((key 3).2 h)
      · exact Or.inr ((key 4).2 h)
    · by_contra hcon
      push Not at hcon
      have hle : A' ≤ signedB4 := by
        refine hgen.trans ((Subgroup.closure_le _).2 ?_)
        rintro r' ⟨hr'A, hr'r⟩
        exact hcon r' hr'A hr'r
      have hcardA : Nat.card ↥A = 1152 := ggF4Orig_card_weylOfType_F4 ⟨e, he⟩
      have hcardA' : Nat.card ↥A' = 1152 := by
        rw [← hcardA]
        exact Nat.card_congr
          { toFun := fun r => ⟨c r.1, (hmem r.1).1 r.2⟩
            invFun := fun r => ⟨c.symm r.1,
              (hmem (c.symm r.1)).2 (by rw [MulEquiv.apply_symm_apply]; exact r.2)⟩
            left_inv := fun r => Subtype.ext (c.symm_apply_apply r.1)
            right_inv := fun r => Subtype.ext (c.apply_symm_apply r.1) }
      have hcardB : Nat.card ↥signedB4 = 384 := by
        rw [SignedPermCount.card_signedPermSubgroup (by norm_num) (by norm_num)]
        rfl
      have := Subgroup.card_le_of_le hle
      omega
  have hmap : A = A'.map c.toMonoidHom := by
    rw [hA', Subgroup.map_comap_eq_self_of_surjective c.surjective]
  rw [hmap, hA'eq]

end F4Over

end CFSG.StandardType

end
