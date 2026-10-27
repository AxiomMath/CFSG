module

public import CFSG.Quasithin.H13.L32NLem1442a
public import CFSG.Quasithin.H13.L32NLem14312
public import CFSG.Quasithin.Vol2.GoldschmidtL128Quad

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

theorem card_orthSub_six {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    {f : LinearMap.BilinForm (ZMod 2) U} (hf : G11.IsSymplectic f) {q : U → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 6) :
    Nat.card ↥(G11.orthSub q) = 40320 ∨ Nat.card ↥(G11.orthSub q) = 51840 := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hnd := G11.P4InspOrth.p4insporth_nondegenerate_quad hf hq
  have h2 : (∏ i ∈ Finset.Icc 1 2, (((2 : ℤ) ^ 2) ^ i - 1)) = 45 := by decide
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (G11.P4InspOrth.p4insporth_quad hq)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2) hnd
      (m := 2) (by rw [hdim]) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
    rw [G11.P4InspOrth.p4insporth_orthogonalGroup_quad hq, Nat.card_zmod] at h
    simp only [Nat.cast_ofNat] at h
    rw [h2] at h
    norm_num at h
    left
    exact_mod_cast h
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2) hnd
      (m := 2) (by rw [hdim]) (ε := -1) (Or.inr ⟨rfl, hplus⟩)
    rw [G11.P4InspOrth.p4insporth_orthogonalGroup_quad hq, Nat.card_zmod] at h
    simp only [Nat.cast_ofNat] at h
    rw [h2] at h
    norm_num at h
    right
    exact_mod_cast h

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem exists_quad (h12213 : Stmt12_2_13) :
    ∃ q : D.V → ZMod 2, (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
      (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
      ∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v := by
  have hfr : frattiniOf (centerOf (fsuU T V)) = ⊥ := by
    rw [C.base.zU]
    exact L14312.frattiniOf_eq_bot_of_card_two C.card_V1
  exact (lemma12_8_8_two_of C.base.h1222 h12213 G T L V 3 (fsuV1 T V) V₂ C.base.s1282
    D).2.2.2 hfr

theorem false_of_concl6 (h12213 : Stmt12_2_13) (h6 : G112Concl6 (D.img (l32nH T V))) : False := by
  obtain ⟨q, -, hq, hΓ⟩ := C.exists_quad h12213
  have hle : D.img (l32nH T V) ≤ G11.orthSub q := fun γ hγ v => hΓ γ hγ v
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h6.2] at hdvd
  rcases card_orthSub_six ⟨C.g111.alt, C.g111.nondegenerate⟩ hq h6.1 with h | h
  · rw [h] at hdvd
    exact absurd hdvd (by decide)
  · rw [h] at hdvd
    exact absurd hdvd (by decide)

end Ctx

end L1442

end CFSG.Quasithin.H13
