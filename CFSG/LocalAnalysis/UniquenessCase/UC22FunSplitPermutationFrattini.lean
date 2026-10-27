module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
import CFSG.GroupTheory.SubgroupTransport
import CFSG.GroupTheory.SteinbergBWFrattini
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F14

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

theorem mem_funSet_map_conj_of_mem_normalizer {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X},
      𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    {S K : Subgroup X} {g : X} (hg : g ∈ normalizer (S : Set X))
    (hK : K ∈ FunSet 𝔉 X S) :
    K.map (MulAut.conj g).toMonoidHom ∈ FunSet 𝔉 X S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : S.map (MulAut.conj g).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hs := (CFSG.GroupTheory.isSylowOf_map_mulEquiv (MulAut.conj g)).mpr hK.2
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hS] at hs
  exact ⟨hconj g hK.1, hs⟩

theorem funSet_inf_eq_of_intersections_le {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    {P N : Subgroup X} (hP : IsPGroup 2 P)
    (hN : ∀ J ∈ FunSet 𝔉 X P, P ⊓ J ≤ N) :
    FunSet 𝔉 X (P ⊓ N) = FunSet 𝔉 X P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext J
  constructor
  · intro hJ
    have heq := hJ.2.eq_of_le
      (inf_le_inf_right J (show P ⊓ N ≤ P from inf_le_left)) inf_le_right hP.to_inf_left
    exact ⟨hJ.1, heq.symm ▸ hJ.2⟩
  · intro hJ
    have heq : (P ⊓ N) ⊓ J = P ⊓ J := le_antisymm
      (inf_le_inf_right J inf_le_left)
      (le_inf (le_inf inf_le_left (hN J hJ)) inf_le_right)
    exact ⟨hJ.1, heq.symm ▸ hJ.2⟩

theorem mapsTo_funSet_conj_of_normal_two_quotient {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X},
      𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    (P : Sylow 2 X) (H : Subgroup X) (hPH : (P : Subgroup X) ≤ H)
    (O N : Subgroup H) [O.Normal] [N.Normal] (hON : O ≤ N)
    (hN2 : IsPGroup 2 (N ⧸ O.subgroupOf N))
    (hO : ∀ J ∈ FunSet 𝔉 X (P : Subgroup X),
      O.map H.subtype ≤ normalizer (J : Set X))
    (hPN : ∀ J ∈ FunSet 𝔉 X (P : Subgroup X),
      (P : Subgroup X) ⊓ J ≤ N.map H.subtype) :
    ∀ g ∈ H, Set.MapsTo (Subgroup.map (MulAut.conj g).toMonoidHom)
      (FunSet 𝔉 X (P : Subgroup X)) (FunSet 𝔉 X (P : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal (P.subtype hPH) N
  let S₀ : Subgroup H := (P₀ : Subgroup N).map N.subtype
  have hS₀ : S₀.map H.subtype = (P : Subgroup X) ⊓ N.map H.subtype := by
    rw [show S₀ = ((P.subtype hPH : Sylow 2 H) : Subgroup H) ⊓ N from hP₀,
      Subgroup.map_inf_eq _ _ _ H.subtype_injective, Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hPH]
  have hFun : FunSet 𝔉 X (S₀.map H.subtype) = FunSet 𝔉 X (P : Subgroup X) := by
    rw [hS₀]
    exact funSet_inf_eq_of_intersections_le P.isPGroup' hPN
  obtain ⟨_, hfratt⟩ := CFSG.GroupTheory.ZJ.normal_p_quotient_frattini hON hN2 P₀
  intro g hg J hJ
  have hgf : (⟨g, hg⟩ : H) ∈ (O : Set H) * (normalizer (S₀ : Set H) : Set H) := by
    rw [hfratt]
    exact Set.mem_univ _
  obtain ⟨o, ho, n, hn, hon⟩ := hgf
  have hnX : (n : X) ∈ normalizer (S₀.map H.subtype : Set X) :=
    Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  have hJn : J.map (MulAut.conj (n : X)).toMonoidHom ∈ FunSet 𝔉 X (P : Subgroup X) := by
    rw [← hFun] at hJ ⊢
    exact mem_funSet_map_conj_of_mem_normalizer hconj hnX hJ
  have hoX : (o : X) ∈ normalizer
      (J.map (MulAut.conj (n : X)).toMonoidHom : Set X) :=
    hO _ hJn (Subgroup.mem_map.mpr ⟨o, ho, rfl⟩)
  have hfix : (J.map (MulAut.conj (n : X)).toMonoidHom).map
      (MulAut.conj (o : X)).toMonoidHom = J.map (MulAut.conj (n : X)).toMonoidHom :=
    mem_normalizer_iff_map_conj_eq.mp hoX
  have hgX : g = (o : X) * (n : X) := (congrArg (fun x : H => (x : X)) hon).symm
  have hmap : J.map (MulAut.conj g).toMonoidHom =
      (J.map (MulAut.conj (n : X)).toMonoidHom).map (MulAut.conj (o : X)).toMonoidHom := by
    rw [hgX, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group
  rw [hmap, hfix]
  exact hJn

end CFSG.LocalAnalysis.UniquenessCase.UC22.F14
