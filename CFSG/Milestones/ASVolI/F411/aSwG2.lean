module

public import CFSG.Milestones.ASVolI.F411.aSwCore
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem burnsideF411a_mem_normalizer_subgroupOf {G : Type*} [Group G] {H X : Subgroup G}
    (hX : X ≤ H) (g : ↥H) :
    g ∈ Subgroup.normalizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (g : G) ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ H
    · have := h ⟨x, hx⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hxX
        exact absurd (hX hxX) hx
      · intro hgx
        exfalso
        apply hx
        have h1 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem g.2) (hX hgx)) g.2
        simpa [mul_assoc] using h1
  · intro h x
    have := h (x : G)
    simpa [Subgroup.mem_subgroupOf] using this

theorem burnsideF411a_map_map_congr {G H : Type*} [Group G] [Group H] (χ : G ≃* H)
    (φ : MulAut G) (L : Subgroup G) :
    (L.map χ.toMonoidHom).map (MulAut.congr χ φ).toMonoidHom =
      (L.map φ.toMonoidHom).map χ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun x => by simp [MulAut.congr_apply]

section G2

set_option linter.unusedSectionVars false


section Field

variable {K : Type} [Field K]

theorem burnsideF411a_g2_positiveBorel_eq :
    G2Native.positiveBorel K = Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup (G2Native.Parent K)) : Set (G2Native.Parent K)) := by
  ext x
  have h1 : x ∈ G2Native.positiveBorel K ↔ (x : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
    rw [← burnsideF4h_g2_map_positiveBorel]
    exact (Subgroup.mem_map_iff_mem (adjointGroup Tag.G2 K).subtype_injective).symm
  rw [h1, ← (borel_self_normalizers Tag.G2 K).1, Subgroup.mem_inf,
    burnsideF411a_mem_normalizer_subgroupOf posUnipotent_le_adjointGroup]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem burnsideF411a_g2_rootSubgroup_neg (i : Fin Tag.G2.rank) :
    G2Native.rootSubgroup K (-G2Native.simpleVector i) = simpleNegSubgroup Tag.G2 K i := by
  refine (burnsideF4h_g2_rootSubgroup_eq (K := K) (isRoot_neg_single Tag.G2 i)).trans ?_
  ext x
  rw [Subgroup.mem_subgroupOf, mem_rootSubgroup, mem_simpleNegSubgroup]
  simp only [pinnedX_neg_single]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end Field

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

variable (K) in
@[expose] noncomputable def burnsideF411a_g2Phi : MulAut (G2Native.Parent K) :=
  ReeTag.G2.finiteExceptionalAut K

theorem burnsideF411a_g2_map_positiveBorel :
    (G2Native.positiveBorel K).map (burnsideF411a_g2Phi K).toMonoidHom =
      G2Native.positiveBorel K := by
  have hU : ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      (burnsideF411a_g2Phi K).toMonoidHom =
        (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :=
    (finiteExceptionalAut_mem_unipotentPairAut ReeTag.G2 (K := K)).1
  rw [burnsideF411a_g2_positiveBorel_eq, Subgroup.map_equiv_normalizer_eq, hU]

theorem burnsideF411a_g2_map_rootSubgroup_neg (i : Fin Tag.G2.rank) :
    (G2Native.rootSubgroup K (-G2Native.simpleVector i)).map (burnsideF411a_g2Phi K).toMonoidHom =
      simpleNegSubgroup Tag.G2 K (ReeTag.G2.perm i) := by
  rw [burnsideF411a_g2_rootSubgroup_neg]
  exact map_simpleNegSubgroup_finiteExceptionalAut ReeTag.G2 i

theorem burnsideF411a_g2_map_parabolic :
    (G2Native.pointParabolic K).map (burnsideF411a_g2Phi K).toMonoidHom =
        G2Native.lineParabolic K ∧
      (G2Native.lineParabolic K).map (burnsideF411a_g2Phi K).toMonoidHom =
        G2Native.pointParabolic K := by
  have hB := burnsideF411a_g2_map_positiveBorel (K := K)
  have h1 : (G2Native.rootSubgroup K (-G2Native.simpleVector 1)).map
      (burnsideF411a_g2Phi K).toMonoidHom = G2Native.rootSubgroup K (-G2Native.simpleVector 0) :=
    (burnsideF411a_g2_map_rootSubgroup_neg ⟨1, by decide⟩).trans
      (burnsideF411a_g2_rootSubgroup_neg ⟨0, by decide⟩).symm
  have h0 : (G2Native.rootSubgroup K (-G2Native.simpleVector 0)).map
      (burnsideF411a_g2Phi K).toMonoidHom = G2Native.rootSubgroup K (-G2Native.simpleVector 1) :=
    (burnsideF411a_g2_map_rootSubgroup_neg ⟨0, by decide⟩).trans
      (burnsideF411a_g2_rootSubgroup_neg ⟨1, by decide⟩).symm
  refine ⟨?_, ?_⟩
  · show (G2Native.positiveBorel K ⊔ G2Native.rootSubgroup K (-G2Native.simpleVector 1)).map
        (burnsideF411a_g2Phi K).toMonoidHom =
      G2Native.positiveBorel K ⊔ G2Native.rootSubgroup K (-G2Native.simpleVector 0)
    rw [Subgroup.map_sup, hB, h1]
  · show (G2Native.positiveBorel K ⊔ G2Native.rootSubgroup K (-G2Native.simpleVector 0)).map
        (burnsideF411a_g2Phi K).toMonoidHom =
      G2Native.positiveBorel K ⊔ G2Native.rootSubgroup K (-G2Native.simpleVector 1)
    rw [Subgroup.map_sup, hB, h0]

theorem burnsideF411a_swap_G2_three {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 3 f Gp M₁ M₂) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨chart, hB, hP1, hP2⟩ := hyp.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, -⟩ | ⟨-, hp, hd, K, fK, finK, card, marking, h1, h2, h3, -, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c <;> decide)
  rotate_left
  iterate 4 exact absurd hk (by decide)
  letI := fK
  haveI := finK
  haveI : CharP K ReeTag.G2.prime := (burnsideF4h_cl_charP card : CharP K 3)
  obtain ⟨hl, -, -⟩ := burnsideF4h_g2_full K 3 f hp hd card
  have hmap := burnsideF4h_isLieParabolics_marking Gp marking hl
  have e1 : ∀ L, G2Native.fullImage K marking L =
      (G2Native.fullLocal K L).map marking.toMonoidHom := fun L => rfl
  rw [e1] at h1 h2 h3
  rw [← h1, ← h2, ← h3, ← hB, ← hP1, ← hP2] at hmap
  set Z := Subgroup.center (G2Native.Parent K) with hZdef
  have hZ : Z = ⊥ := center_adjointGroup_eq_bot
  let χ₀ : G2Native.Parent K →* ↥Gp := marking.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hχ : Function.Bijective χ₀ := by
    refine ⟨fun a b hab => ?_, marking.surjective.comp (QuotientGroup.mk'_surjective Z)⟩
    have h : (QuotientGroup.mk' Z a : G2Native.FullModel K) = QuotientGroup.mk' Z b :=
      marking.injective hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hZ,
      Subgroup.mem_bot] at h
    exact inv_mul_eq_one.mp h
  let χ : G2Native.Parent K ≃* ↥Gp := MulEquiv.ofBijective χ₀ hχ
  have hQ : ∀ L, (G2Native.fullLocal K L).map marking.toMonoidHom = L.map χ.toMonoidHom :=
    fun L => by
      rw [G2Native.fullLocal, Subgroup.map_map]
      rfl
  have hQ1 : (Gp ⊓ M₁).subgroupOf Gp = (G2Native.pointParabolic K).map χ.toMonoidHom := by
    rw [hP1, h2, ← hQ]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hQ2 : (Gp ⊓ M₂).subgroupOf Gp = (G2Native.lineParabolic K).map χ.toMonoidHom := by
    rw [hP2, h3, ← hQ]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hNF := (G2_three_exact_automorphism_normal_form hd K card).2.1
  have hNF' : ∀ α : MulAut (G2Native.Parent K), ∃ (g : G2Native.Parent K) (k : ℕ),
      α = MulAut.conj g * burnsideF411a_g2Phi K ^ k := fun α => by
    obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF α
    exact ⟨g, (k : ℕ), hgk⟩
  have hgen : ∀ α : MulAut ↥Gp, ∃ (x : ↥Gp) (m : ℕ),
      α = MulAut.conj x * MulAut.congr χ (burnsideF411a_g2Phi K) ^ m := by
    intro α
    obtain ⟨g, k, hgk⟩ := hNF' ((MulAut.congr χ).symm α)
    refine ⟨χ g, k, ?_⟩
    rw [← (MulAut.congr χ).apply_symm_apply α, hgk, map_mul, map_pow]
    congr 1
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hpar := burnsideF411a_g2_map_parabolic (K := K)
  refine burnsideF411a_swap_of_graph hyp.normal hyp.centralizer_trivial hyp.split hmap
    (MulAut.congr χ (burnsideF411a_g2Phi K)) hgen (MulAut.congr χ (burnsideF411a_g2Phi K)) ?_ ?_
  · rw [hQ1, hQ2, burnsideF411a_map_map_congr, hpar.1]
  · rw [hQ1, hQ2, burnsideF411a_map_map_congr, hpar.2]

end G2

end CFSG.ASVolI
