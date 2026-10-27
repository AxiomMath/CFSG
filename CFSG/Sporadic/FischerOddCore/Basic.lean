module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

variable {G H : Type*} [Group G] [Group H]

@[expose] def centralizerMulEquiv (e : G ≃* H) (x : G) :
    ↥(Subgroup.centralizer ({x} : Set G)) ≃* ↥(Subgroup.centralizer ({e x} : Set H)) where
  toFun g := ⟨e g, Subgroup.mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp g.2])⟩
  invFun g := ⟨e.symm g, Subgroup.mem_centralizer_singleton_iff.mpr (by
    have hg := Subgroup.mem_centralizer_singleton_iff.mp g.2
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hg])⟩
  left_inv g := Subtype.ext (e.symm_apply_apply (g : G))
  right_inv g := Subtype.ext (e.apply_symm_apply (g : H))
  map_mul' g h := Subtype.ext (map_mul e (g : G) h)

theorem coe_centralizerMulEquiv (e : G ≃* H) (x : G) (g : Subgroup.centralizer ({x} : Set G)) :
    ((centralizerMulEquiv e x g : Subgroup.centralizer ({e x} : Set H)) : H) = e g :=
  rfl

theorem oddCore_centralizer_eq_bot_of_mulEquiv (e : G ≃* H) {x : G}
    (h : CFSG.oddCore (Subgroup.centralizer ({x} : Set G)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({e x} : Set H)) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv (centralizerMulEquiv e x) h

theorem card_centralizer_mulEquiv (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) :=
  (Nat.card_congr (centralizerMulEquiv e x).toEquiv).symm

theorem oddCore_centralizer_eq_bot_of_isConj {x y : G} (hxy : IsConj x y)
    (h : CFSG.oddCore (Subgroup.centralizer ({x} : Set G)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({y} : Set G)) = ⊥ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
  have e := oddCore_centralizer_eq_bot_of_mulEquiv (MulAut.conj c) h
  rwa [MulAut.conj_apply] at e

theorem card_centralizer_of_isConj {x y : G} (hxy : IsConj x y) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
  have e := card_centralizer_mulEquiv (MulAut.conj c) x
  rwa [MulAut.conj_apply] at e

theorem oddCore_eq_bot_of_quotient_isSimpleGroup [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Nat.card Z ∣ 2) {Q : Type*} [Group Q] [IsSimpleGroup Q] (hQ : Even (Nat.card Q))
    (e : G ⧸ Z ≃* Q) : CFSG.oddCore G = ⊥ := by
  have hodd := odd_card_oddCore (G := G)
  let f : G →* Q := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hnorm : ((CFSG.oddCore G).map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.oddCore G).map f) with h | h
  · have hle : CFSG.oddCore G ≤ Z := by
      intro x hx
      have hfx : f x = 1 := by
        have : f x ∈ (CFSG.oddCore G).map f := ⟨x, hx, rfl⟩
        rwa [h, Subgroup.mem_bot] at this
      have hmk : (QuotientGroup.mk' Z) x = 1 := e.injective (by
        rw [map_one]
        exact hfx)
      exact (QuotientGroup.eq_one_iff x).mp hmk
    have hdvd : Nat.card (CFSG.oddCore G) ∣ 2 := (Subgroup.card_dvd_of_le hle).trans hZ
    have h1 : Nat.card (CFSG.oddCore G) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · exfalso
        rw [h2] at hodd
        exact Nat.not_even_iff_odd.mpr hodd even_two
    exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hdvd : Nat.card ((CFSG.oddCore G).map f) ∣ Nat.card (CFSG.oddCore G) :=
      Subgroup.card_map_dvd _ f
    rw [h, Subgroup.card_top] at hdvd
    exact Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hodd hdvd) hQ

end CFSG.Sporadic.FischerOddCore
