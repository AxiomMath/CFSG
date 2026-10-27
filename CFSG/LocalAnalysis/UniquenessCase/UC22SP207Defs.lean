module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.Open.SplitBNPair
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ASVolI.ChIJK (IsSplitBNPair)

@[expose] def HasCentralLongest (X : Type) [Group X] : Prop :=
  ∃ B N : Subgroup X, IsSplitBNPair 2 B N ∧ ∃ n₀ ∈ N,
    B ⊔ B.map (MulAut.conj n₀).toMonoidHom = ⊤ ∧ ∀ x ∈ N, n₀ * x * n₀⁻¹ * x⁻¹ ∈ B

@[expose] def NoStrongParabolic (X : Type) [Group X] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Y : Subgroup X, IsParabolicTwo X Y → ¬ IsStronglyPEmbedded p Y

theorem NoStrongParabolic.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : NoStrongParabolic X) : NoStrongParabolic X' := by
  intro p hp hp2 Y' ⟨S', hS'⟩ ⟨hne, hdvd, hint⟩
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hS'e : (S' : Subgroup X') ≤ e.toMonoidHom.range := fun x _ =>
    MonoidHom.mem_range.2 ⟨e.symm x, by simp⟩
  refine h p hp hp2 (Y'.comap e.toMonoidHom)
    ⟨S'.comapOfInjective e.toMonoidHom hinj hS'e, ?_⟩ ⟨fun htop => hne ?_, ?_, ?_⟩
  · have hsurj : Function.Surjective e.toMonoidHom := e.surjective
    change normalizer (((S'.comapOfInjective e.toMonoidHom hinj hS'e : Sylow 2 X) :
      Subgroup X) : Set X) ≤ Y'.comap e.toMonoidHom
    rw [Sylow.coe_comapOfInjective, ← comap_normalizer_eq_of_surjective _ hsurj]
    exact comap_mono hS'
  · refine eq_top_iff.2 fun y _ => ?_
    have hy : e.symm y ∈ Y'.comap e.toMonoidHom := htop ▸ mem_top _
    simpa using hy
  · rwa [comap_equiv_eq_map_symm', card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
  · intro g hg
    have hconj : (Y'.comap e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (Y'.map (MulAut.conj (e g)).toMonoidHom).comap e.toMonoidHom := by
      ext x
      simp only [mem_map, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e y, hy, by simp⟩
      · rintro ⟨y', hy', hxy⟩
        refine ⟨e.symm y', by simpa using hy', e.injective ?_⟩
        simp [hxy]
    rw [hconj, ← comap_inf, comap_equiv_eq_map_symm',
      card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
    exact hint (e g) hg

theorem uc22sp207_not_isStronglyPEmbedded_of_subset_mul {G : Type} [Group G] [Finite G]
    {Y U : Subgroup G} (hU : IsPGroup 2 U) (hUY : U ≤ Y) {g : G} (hg : g ∉ Y)
    (hY : ∀ x ∈ Y, ∃ u ∈ U, u⁻¹ * x ∈ Y.map (MulAut.conj g).toMonoidHom) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsStronglyPEmbedded p Y := by
  rintro ⟨-, hdvd, hint⟩
  set H := Y.map (MulAut.conj g).toMonoidHom
  have hsurj : Function.Surjective (quotientSubgroupOfEmbeddingOfLE H hUY) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, huy⟩ := hY y y.2
    refine ⟨QuotientGroup.mk ⟨u, hu⟩, ?_⟩
    rw [quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq]
    exact huy
  have hidx : H.relIndex U = H.relIndex Y :=
    Nat.card_congr (Equiv.ofBijective _ ⟨(quotientSubgroupOfEmbeddingOfLE H hUY).injective, hsurj⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have hcop : p.Coprime (H.relIndex Y) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hpY => hp2 ?_
    rw [← hidx] at hpY
    have hpk : p ∣ 2 ^ k := hk ▸ hpY.trans (relIndex_dvd_card H U)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpk)
  refine hint g hg ?_
  rw [inf_comm]
  rw [← relIndex_mul_card H Y] at hdvd
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem uc22sp207_not_isStronglyPEmbedded_of_witness {G X : Type} [Group G] [Group X] [Finite X]
    (α : G →* X) (hαc : α.ker ≤ center G) {p : ℕ} (hp : p.Prime) {Y : Subgroup X} {g x : G}
    (hg : g ∉ Y.comap α) (hx : x ∈ Y.comap α ⊓ (Y.comap α).map (MulAut.conj g).toMonoidHom)
    (hxp : x ^ p = 1) (hxz : x ∉ center G) : ¬ IsStronglyPEmbedded p Y := by
  rintro ⟨-, -, hint⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hxY, y, hy, rfl⟩ := mem_inf.1 hx
  have hmem : α ((MulAut.conj g).toMonoidHom y) ∈ Y ⊓ Y.map (MulAut.conj (α g)).toMonoidHom :=
    mem_inf.2 ⟨hxY, α y, hy, by simp [MulAut.conj_apply]⟩
  set z : ↥(Y ⊓ Y.map (MulAut.conj (α g)).toMonoidHom) := ⟨_, hmem⟩
  have hz : z ^ p = 1 := by
    ext
    change α ((MulAut.conj g).toMonoidHom y) ^ p = 1
    rw [← map_pow, hxp, map_one]
  have hz1 : z ≠ 1 := fun h1 => hxz (hαc (MonoidHom.mem_ker.2 (congrArg Subtype.val h1)))
  have hpz := orderOf_dvd_natCard z
  rw [orderOf_eq_prime hz hz1] at hpz
  exact hint (α g) hg hpz

end CFSG.LocalAnalysis.UniquenessCase.UC22
