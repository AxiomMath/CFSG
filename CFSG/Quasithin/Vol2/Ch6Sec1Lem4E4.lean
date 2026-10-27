module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4EIn
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_fusion_ch614 (hFus : KG614Fusion) {K T X : Subgroup G}
    (hKq : CFSG.IsQuasisimple (ModO2 K))
    (hKt : (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e (ModO2 K)) ∨
      ∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧
        IsPSLEps3 δ p 1 (ModO2 K ⧸ Subgroup.center (ModO2 K)))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hsyl : IsSylowTwoOf T (K ⊔ T))
    (hXK : X ≤ K) (hX2 : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXTK : ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hJX : X ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G))
    (hJK : ¬ K ≤ Subgroup.normalizer (thompsonJ T : Set G)) : False := by
  have hRT : pCoreOf 2 (K ⊔ T) ≤ T := F7.isSylowTwoOf_pCoreOf_le hsyl
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hJR : ¬ thompsonJ T ≤ pCoreOf 2 (K ⊔ T) := by
    intro hJ
    apply hJK
    have heq : thompsonJ (pCoreOf 2 (K ⊔ T)) = thompsonJ T := B6.thompsonJ_eq_of_le hJ hRT
    have h1 : K ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ T) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)
    have h2 := normalizer_le_normalizer_thompsonJ (pCoreOf 2 (K ⊔ T))
    rw [heq] at h2
    exact le_sup_left.trans (h1.trans h2)
  obtain ⟨A, hA, hAR⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ¬ A ≤ pCoreOf 2 (K ⊔ T) := by
    by_contra hcon
    push Not at hcon
    exact hJR (iSup₂_le fun A hA => hcon A hA)
  have hJO : thompsonJ T ≤ pCoreOf 2 (X ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hJT.trans le_sup_right) hJX
      (hsyl.2.1.to_le hJT)
  have hAO : A ≤ pCoreOf 2 (X ⊔ T) := (B6.le_thompsonJ hA).trans hJO
  obtain ⟨k, -, hkT, hkO⟩ :=
    hFus G K T X hKq hKt hTK hsyl hXK hX2 hX5 hXn hTX hXTK A hAO hA.2.1 hAR
  have hAk : IsMaxElemAbelian T (A.map (MulAut.conj k).toMonoidHom) := by
    have he : IsElemAbelian 2 (B6.conjSub k A) := B6.isElemAbelian_conjSub hA.2.1 k
    have hc : Nat.card (B6.conjSub k A) = Nat.card A := B6.card_conjSub A k
    refine ⟨hkT, he, fun B hBT hB => ?_⟩
    have := hA.2.2 B hBT hB
    exact this.trans hc.symm.le
  exact hkO ((B6.le_thompsonJ hAk).trans hJO)

end CFSG.Quasithin.H13
