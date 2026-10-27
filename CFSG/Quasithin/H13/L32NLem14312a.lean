module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneTwelve

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L14312

variable {G : Type} [Group G] [Finite G]

theorem twelve_three_of_eq {V V₁ L T : Subgroup G} (S : L128A.Setting V V₁ L T) {g : G}
    (hg : L128A.Good V₁ L g) {U : Subgroup G} (hU : L128A.uA V V₁ = U) (D : HatModelU U)
    (hU4 : 4 < (centerOf U).relIndex U) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁) :
    G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
      (D.hat (U ⊓ Subgroup.centralizer (V : Set G) ⊓
        rconj (U ⊓ Subgroup.centralizer (V : Set G)) g))
      (D.img (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g)) (D.img (rconj (centerOf U) g)) := by
  subst hU
  exact S.twelve_three hg D hU4 haV haZ

theorem g101Hyp (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) {g : G} (hg : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) {a : G} (ha : a ∈ V₂) (haV₁ : a ∉ V₁)
    (D : HatModelU (u128 V V₁)) :
    G101Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
      (D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g))
      (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) (D.img (CFSG.conjugate (zU128 V V₁) g)) := by
  have S := L128P.setting128A h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := L128P.exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, hTZ⟩ := L128P.T_le_normalizer_w128 h1222 h12213 hs
  rw [hkY _ hTW, hkY _ hTZ]
  exact (twelve_three_of_eq S ⟨hk, hkN⟩ (L128P.uA_eq h1222 hs) D
    (L128P.four_lt_relIndex h1222 h12213 hs) ha haV₁).toG101Hyp

end L14312

end CFSG.Quasithin.H13
