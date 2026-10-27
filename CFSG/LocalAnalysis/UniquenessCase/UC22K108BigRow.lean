module

public import CFSG.Open.SplitBNPair
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigStar
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BN
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem CFSG.ASVolI.ChIJK

theorem k108big_split_ne_bot {G : Type} [Group G] {p : ℕ} {B N U : Subgroup G}
    (hBN : IsSplitBNPair p B N) (hB : B ≠ ⊤) (hUH : U ⊔ (B ⊓ N) = B) : U ≠ ⊥ := by
  intro hU
  rw [hU, bot_sup_eq] at hUH
  obtain ⟨S₀, hS₁, hS₂, -, hS₄⟩ := hBN.coxeter
  by_cases hS₀ : S₀.Nonempty
  · obtain ⟨s, hs⟩ := hS₀
    obtain ⟨hsN, -, hs2⟩ := hS₁ s hs
    obtain ⟨b, hb, hsbs⟩ := hS₄ s hs
    apply hsbs
    have hbH : b ∈ B ⊓ N := by
      rw [hUH]
      exact hb
    have h1 : s * b * s⁻¹ ∈ B := by
      have := hBN.normal_inter.conj_mem ⟨b, hbH.2⟩ (Subgroup.mem_subgroupOf.2 hbH) ⟨s, hsN⟩
      exact (Subgroup.mem_subgroupOf.1 this).1
    have e : s * b * s = s * b * s⁻¹ * s ^ 2 := by group
    rw [e]
    exact B.mul_mem h1 hs2
  · rw [Set.not_nonempty_iff_eq_empty.1 hS₀, Subgroup.closure_empty, bot_sup_eq, hUH] at hS₂
    apply hB
    rw [← hBN.gen, ← hS₂, sup_idem]

theorem k108big_rowX_strong {Gh : Type} [Group Gh] [Finite Gh] (S : Subgroup Gh) [S.Normal]
    [IsSimpleGroup ↥S] {B N : Subgroup ↥S} (hBN : IsSplitBNPair 2 B N) (hB : B ≠ ⊤)
    {T X M : Subgroup Gh} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hX : (Nat.card X).Prime)
    (hXodd : Odd (Nat.card X)) (hXT : X ≤ Subgroup.normalizer (T : Set Gh))
    (hTM : T ≤ M) (hXM : X ≤ M) (hstar : ∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) :
    S ≤ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ S) S :=
    hT.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top (H := S)).ge
  obtain ⟨-, hUp0, hUi0⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hTS
  set U : Subgroup ↥S := (T ⊓ S).subgroupOf S with hUdef
  have hUp : IsPGroup 2 U := hUp0.comap_subtype
  have hUi : ¬ 2 ∣ U.index := hUi0
  have hUmap : U.map S.subtype = T ⊓ S := by
    rw [hUdef, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  obtain ⟨U₀, hU₀B, hU₀n, hU₀p, hU₀i, -, hU₀H, -⟩ := hBN.split
  have hU₀ne : U₀ ≠ ⊥ := k108big_split_ne_bot hBN hB hU₀H
  have hsyl₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤ := ⟨le_top, hU₀p, by
    change ¬ 2 ∣ U₀.relIndex ⊤
    rwa [Subgroup.relIndex_top_right]⟩
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := ⟨le_top, hUp, by
    change ¬ 2 ∣ U.relIndex ⊤
    rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨c, -, hc⟩ := hsyl₀.exists_conj hsyl
  have hfinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hBN' : IsSplitBNPair 2 (B.map (MulAut.conj c).toMonoidHom)
      (N.map (MulAut.conj c).toMonoidHom) :=
    burnsideI2BN_map hBN _ (MulAut.conj c).surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 hfinj]; exact bot_le)
  haveI : (cartan (B.map (MulAut.conj c).toMonoidHom)
      (N.map (MulAut.conj c).toMonoidHom)).Normal := hBN'.normal_inter
  obtain ⟨W, hW⟩ := burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN')
  have hUB' : U ≤ B.map (MulAut.conj c).toMonoidHom := hc ▸ Subgroup.map_mono hU₀B
  have hBU₀ : B ≤ Subgroup.normalizer (U₀ : Set ↥S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU₀B).1 hU₀n
  have hB'U : B.map (MulAut.conj c).toMonoidHom ≤ Subgroup.normalizer (U : Set ↥S) := by
    rw [hc, ← Subgroup.map_equiv_normalizer_eq U₀ (MulAut.conj c)]
    exact Subgroup.map_mono hBU₀
  have hUn' : (U.subgroupOf (B.map (MulAut.conj c).toMonoidHom)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB').2 hB'U
  have hNU : Subgroup.normalizer (U : Set ↥S) = B.map (MulAut.conj c).toMonoidHom :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22k108bn_normalizer_eq Nat.prime_two hBN' hUB'
      hUn' hUp hUi
  have hBUH : B.map (MulAut.conj c).toMonoidHom ≤
      U ⊔ (B.map (MulAut.conj c).toMonoidHom ⊓ N.map (MulAut.conj c).toMonoidHom) := by
    rw [hc, ← Subgroup.map_inf_eq _ _ _ hfinj, ← Subgroup.map_sup, hU₀H]
  have hU : U ≠ ⊥ := by
    rw [hc]
    exact fun h => hU₀ne ((Subgroup.map_eq_bot_iff_of_injective _ hfinj).1 h)
  have hXU : X ≤ Subgroup.normalizer ((U.map S.subtype : Subgroup Gh) : Set Gh) := by
    rw [hUmap]
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hXT hx, by rw [Subgroup.normalizer_eq_top]; trivial⟩
  have hUM : U.map S.subtype ≤ M := by
    rw [hUmap]
    exact inf_le_left.trans hTM
  have hpX : 2 ≠ Nat.card X := fun h => by
    rw [← h] at hXodd
    exact absurd hXodd (by decide)
  exact k108big_le S hW hUp hU hUB' hNU hBUH hX hpX hXU hUM hXM hstar

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
