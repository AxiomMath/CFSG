module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneTwelve

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L128A

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem twelve_two_of_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {U : Subgroup G}
    (hU : uA V V₁ = U) :
    Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V : Set G) ≤
        Subgroup.normalizer ((rconj (U ⊓ Subgroup.centralizer (V : Set G)) g ⊔
          centralizerMod (centerOf U) (Subgroup.normalizer (V₁ : Set G)) U : Subgroup G) :
            Set G) ∧
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V : Set G) ≤
        Subgroup.normalizer ((rconj (centerOf U) g ⊔
          centralizerMod (centerOf U) (Subgroup.normalizer (V₁ : Set G)) U : Subgroup G) :
            Set G) := by
  subst hU
  exact ⟨(S.twelve_two hg).1, (S.twelve_two hg).2.1⟩

theorem eleven_of_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {U : Subgroup G}
    (hU : uA V V₁ = U) :
    ⁅U ⊓ Subgroup.centralizer (V : Set G), rconj (U ⊓ Subgroup.centralizer (V : Set G)) g⁆ ≤
        (U ⊓ Subgroup.centralizer (V : Set G)) ⊓ rconj (U ⊓ Subgroup.centralizer (V : Set G)) g ∧
      IsElemAbelian 2
        ((U ⊓ Subgroup.centralizer (V : Set G)) ⊓ rconj (U ⊓ Subgroup.centralizer (V : Set G)) g) ∧
      centralizerMod (centerOf U)
          ((U ⊓ Subgroup.centralizer (V : Set G)) ⊓ rconj (U ⊓ Subgroup.centralizer (V : Set G)) g)
          (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g) ⊔ centerOf U = V ⊔ centerOf U := by
  subst hU
  exact ⟨S.eleven_one hg, (S.eleven_two hg).1, S.eleven_four hg⟩

theorem g111_of_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {U : Subgroup G}
    (hU : uA V V₁ = U) (D : HatModelU U) (hU4 : 4 < (centerOf U).relIndex U) {a : G} (haV : a ∈ V)
    (haZ : a ∉ V₁) :
    G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
      (D.hat (U ⊓ Subgroup.centralizer (V : Set G) ⊓
        rconj (U ⊓ Subgroup.centralizer (V : Set G)) g))
      (D.img (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g)) (D.img (rconj (centerOf U) g)) := by
  subst hU
  exact S.twelve_three hg D hU4 haV haZ

theorem hat_of_g111 {V' : Type} [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    {B : LinearMap.BilinForm (ZMod 2) V'} {Γ X X₀ : Subgroup (V' ≃ₗ[ZMod 2] V')} {v₁ : V'}
    {W : Submodule (ZMod 2) V'} (h : G111Hyp B Γ v₁ W X X₀) :
    ((∀ x ∈ X, ∃ f : V' →ₗ[ZMod 2] ZMod 2, f v₁ = 0 ∧ ∀ w ∈ W, x w = w + f w • v₁) ∧
        ∀ f : V' →ₗ[ZMod 2] ZMod 2, f v₁ = 0 →
          ∃ x ∈ X, ∀ w ∈ W, x w = w + f w • v₁) ∧
      Module.finrank (ZMod 2) ↥W + Nat.log 2 (X₀.relIndex X) = Module.finrank (ZMod 2) V' - 1 ∧
      ((∃ v : V', (∀ x ∈ X, x v = v) ∧ v ≠ 0 ∧ v ≠ v₁) →
        ∃ x ∈ X, x ≠ 1 ∧
          Module.finrank (ZMod 2) ↥(LinearMap.range (x.toLinearMap - LinearMap.id)) ≤ 2 ∧
          v₁ ∈ LinearMap.range (x.toLinearMap - LinearMap.id)) := by
  refine ⟨⟨fun x hx => ?_, fun f hf => ?_⟩, h.rank, fun ⟨v, hv, hv0, hv1⟩ => ?_⟩
  · obtain ⟨f, hf0, hf⟩ := h.toG101Hyp.transvection x hx
    refine ⟨Subspace.dualLift W f, ?_, fun w hw => ?_⟩
    · rw [Subspace.dualLift_of_mem h.toG101Hyp.mem_W]
      exact hf0
    · rw [Subspace.dualLift_of_mem hw]
      exact hf ⟨w, hw⟩
  · obtain ⟨x, hx, hxf⟩ := h.toG101Hyp.transvection_full (f.comp W.subtype) (by simpa using hf)
    exact ⟨x, hx, fun w hw => by simpa using hxf ⟨w, hw⟩⟩
  · rcases h.three with h1 | ⟨x, hx, hr, hxv⟩
    · rcases h1 v hv with h2 | h2
      · exact absurd h2 hv0
      · exact absurd h2 hv1
    · refine ⟨x, hx, ?_, hr, hxv⟩
      rintro rfl
      have : v₁ ∈ LinearMap.range ((1 : V' ≃ₗ[ZMod 2] V').toLinearMap - LinearMap.id) := hxv
      simp at this
      exact h.toG101Hyp.point this

end L128A

open L128P

theorem lemma12_8_12_two_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) : Lemma12_8_12_two := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  have S := setting128A h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, hTZ⟩ := T_le_normalizer_w128 h1222 h12213 hs
  rw [hkY _ hTW, hkY _ hTZ]
  exact L128A.twelve_two_of_eq S ⟨hk, hkN⟩ (uA_eq h1222 hs)

theorem lemma12_8_11_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) : Lemma12_8_11 := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  have S := setting128A h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, -⟩ := T_le_normalizer_w128 h1222 h12213 hs
  rw [hkY _ hTW]
  exact L128A.eleven_of_eq S ⟨hk, hkN⟩ (uA_eq h1222 hs)

theorem lemma12_8_11_hat_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) : Lemma12_8_11_hat := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN a ha haV₁ D
  have S := setting128A h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, hTZ⟩ := T_le_normalizer_w128 h1222 h12213 hs
  rw [hkY _ hTW, hkY _ hTZ]
  exact L128A.hat_of_g111 (L128A.g111_of_eq S ⟨hk, hkN⟩ (uA_eq h1222 hs) D
    (four_lt_relIndex h1222 h12213 hs) ha haV₁)

end CFSG.Quasithin.H13
