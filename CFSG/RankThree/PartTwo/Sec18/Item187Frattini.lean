module

public import CFSG.RankThree.PartTwo.Sec18.Item187Min
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

omit [Finite G] in
private theorem le_normalizer_inf_of_le {K U V : Subgroup G} (hU : K ≤ Subgroup.normalizer (U : Set G))
    (hV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp (hU hg) h)
    (Subgroup.mem_normalizer_iff.mp (hV hg) h)

omit [Finite G] in
private theorem le_normalizer_normalizer_of_le {K T : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (T : Set G)) :
    K ≤ Subgroup.normalizer ((Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
  intro g hg
  have hgT : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK hg)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have key := Subgroup.map_normalizer_eq_of_bijective T
    (f := (MulAut.conj g).toMonoidHom) (MulEquiv.bijective (MulAut.conj g))
  rw [hgT] at key
  exact key

theorem sup_inf_normalizer_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {X V T : Subgroup G}
    (hVX : V ≤ X) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf p T V) :
    V ⊔ (X ⊓ Subgroup.normalizer (T : Set G)) = X := by
  refine le_antisymm (sup_le hVX inf_le_left) ?_
  intro x hx
  have hxT : T.map (MulAut.conj x).toMonoidHom ≤ V := by
    rintro _ ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXV hx) t).mp (hT.le ht)
  have hxTsyl : CFSG.ABGLocalTools.IsSylowOf p (T.map (MulAut.conj x).toMonoidHom) V := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hxT ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hT.card_eq
  obtain ⟨k, hkV, hk⟩ := hT.exists_mem_conj hxTsyl
  have hconj : ∀ y : G, y ∈ T.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ T := by
    intro y
    constructor
    · rintro ⟨t, ht, rfl⟩
      show x⁻¹ * (x * t * x⁻¹) * x ∈ T
      have e : x⁻¹ * (x * t * x⁻¹) * x = t := by group
      rw [e]
      exact ht
    · intro hy
      refine Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, hy, ?_⟩
      show x * (x⁻¹ * y * x) * x⁻¹ = y
      group
  have hkey : ∀ y : G, x⁻¹ * y * x ∈ T ↔ k⁻¹ * y * k ∈ T :=
    fun y => (hconj y).symm.trans (hk y)
  have hmemN : k⁻¹ * x ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    have e2 : k⁻¹ * (x * h * x⁻¹) * k = k⁻¹ * x * h * (k⁻¹ * x)⁻¹ := by group
    have := hkey (x * h * x⁻¹)
    rw [e1, e2] at this
    exact this
  have hn : k⁻¹ * x ∈ X ⊓ Subgroup.normalizer (T : Set G) :=
    ⟨X.mul_mem (X.inv_mem (hVX hkV)) hx, hmemN⟩
  have hmul := Subgroup.mul_mem_sup hkV hn
  rwa [mul_inv_cancel_left] at hmul

namespace MinCex

theorem sup_eq_or_inf_le {X : Subgroup G} (hX : MinCex A M H c X)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X) {V : Subgroup G}
    (hVX : V ≤ X) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    V ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) = X ∨
      V ⊓ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ CFSG.Open.pCoreOf 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  have hSX : S ≤ X := hX.pCoreOf_le
  have hSV : S ≤ Subgroup.normalizer (V : Set G) := hSX.trans hXV
  have hAS : A ⊔ S ≤ Subgroup.normalizer (V : Set G) := sup_le hAV hSV
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ V) V := hS.inf_of_le_normalizer hVX hXV
  have hASN : A ⊔ S ≤ Subgroup.normalizer ((S ⊓ V : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le (le_normalizer_pCoreOf hX.sec18H) hAS
  have hASNN : A ⊔ S ≤ Subgroup.normalizer
      ((Subgroup.normalizer ((S ⊓ V : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    le_normalizer_normalizer_of_le hASN
  have hV' : A ⊔ S ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.normalizer ((S ⊓ V : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le hX.le_normalizer hASNN
  have hUV : V ⊔ (X ⊓ Subgroup.normalizer ((S ⊓ V : Subgroup G) : Set G)) = X :=
    sup_inf_normalizer_eq_of_isSylowOf hVX hXV hT
  rcases hX.sup_eq_or_sup_eq hVX inf_le_left hAS hV' hUV with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hSN : S ≤ Subgroup.normalizer ((S ⊓ V : Subgroup G) : Set G) :=
      le_normalizer_inf_of_le Subgroup.le_normalizer hSV
    have hSle : S ≤ X ⊓ Subgroup.normalizer ((S ⊓ V : Subgroup G) : Set G) :=
      le_inf hSX hSN
    have hXN : X ≤ Subgroup.normalizer ((S ⊓ V : Subgroup G) : Set G) :=
      inf_eq_left.mp ((sup_eq_left.mpr hSle).symm.trans h)
    have hNX : S ⊓ V ≤ X := inf_le_right.trans hVX
    have hpc := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNX hXN hT.isPGroup
    exact (inf_comm V S).le.trans hpc

end MinCex

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
