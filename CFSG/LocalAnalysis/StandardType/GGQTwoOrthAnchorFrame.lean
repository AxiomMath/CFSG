module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType.OrthAnchor

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

private lemma oaG_exists_pow_fin_three :
    ∀ c d : Multiplicative (ZMod 3), c ≠ 1 → ∃ j : Fin 3, c ^ (j : ℕ) = d := by
  decide

theorem omKFrame_of_calibrated {G : Type} [Group G] {L Bs : Subgroup G} {x : G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hBsL : ∀ b : Bs, (b : G) ∈ L ↔ eta b i0 = 1) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (E : QuadExt F K (unitaryInvolution K 2 1)) {ζ : K} (χ₀ : Multiplicative (ZMod 3) →* Kˣ)
    (hχ₀ : Function.Injective χ₀) (hχ₀ζ : ∀ a, (χ₀ a : K) = ζ ^ (Multiplicative.toAdd a).val)
    (π : Fin (n - 1) ≃ {i : Fin n // i ≠ i0}) (χ : normOmega E (n - 1) ≃* L)
    (hχ : ∀ (b : Bs) (hb : (b : G) ∈ L) (v : (F × F) × (Fin (n - 1) → K)),
      (((χ.symm ⟨b, hb⟩ : ↥(normOmega E (n - 1))) :
        ((F × F) × (Fin (n - 1) → K)) ≃ₗ[F] ((F × F) × (Fin (n - 1) → K)))) v =
        (v.1, fun i => ζ ^ (Multiplicative.toAdd (eta b (π i))).val * v.2 i)) :
    ∃ π' : Fin (n - 1 + 1) ≃ Fin n, π' (Fin.last (n - 1)) = i0 ∧
      GGSecFiveBPermOmKFrame E Bs L eta π' (L.subtype.comp χ.toMonoidHom) χ₀ := by
  have hsupp : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock Nat.prime_three (by norm_num) hx hLx eta i0 hA
  let π' : Fin (n - 1 + 1) ≃ Fin n :=
    finSuccEquivLast.trans ((Equiv.optionCongr π).trans (Equiv.optionSubtypeNe i0))
  have hπ'last : π' (Fin.last (n - 1)) = i0 := by
    simp [π', finSuccEquivLast_last]
  have hπ'cast : ∀ i : Fin (n - 1), π' i.castSucc = (π i : Fin n) := by
    intro i
    simp [π', finSuccEquivLast_castSucc]
  let κ : normOmega E (n - 1) →* G := L.subtype.comp χ.toMonoidHom
  have hframe : GGSecFiveBPermOmKFrame E Bs L eta π' κ χ₀ := by
    unfold GGSecFiveBPermOmKFrame
    refine ⟨?_, ?_, hχ₀, fun b => ?_⟩
    · intro a b hab
      exact χ.injective (Subtype.ext hab)
    · ext g
      constructor
      · rintro ⟨s, rfl⟩
        exact (χ s).2
      · intro hg
        refine ⟨χ.symm ⟨g, hg⟩, ?_⟩
        show ((χ (χ.symm ⟨g, hg⟩) : L) : G) = g
        rw [MulEquiv.apply_symm_apply]
    · have hc : eta ⟨x, hx⟩ i0 ≠ 1 := by
        intro h1
        exact hxL ((hBsL ⟨x, hx⟩).mpr h1)
      obtain ⟨j, hj⟩ : ∃ j : Fin 3, (eta ⟨x, hx⟩ i0) ^ (j : ℕ) = eta b i0 :=
        oaG_exists_pow_fin_three (eta ⟨x, hx⟩ i0) (eta b i0) hc
      let b' : ↥Bs := b * (⟨x, hx⟩ ^ (j : ℕ))⁻¹
      have h1 : eta b' = eta b * (eta ⟨x, hx⟩ ^ (j : ℕ))⁻¹ := by
        simp only [b', map_mul, map_inv, map_pow]
      have hcoord : eta b' i0 = 1 := by
        rw [h1, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, hj, mul_inv_cancel]
      have hb' : (b' : G) ∈ L := (hBsL b').mpr hcoord
      have hb'k : ∀ k, k ≠ i0 → eta b' k = eta b k := by
        intro k hk
        simp only [h1, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, hsupp k hk,
          one_pow, inv_one, mul_one]
      refine ⟨χ.symm ⟨b', hb'⟩, ?_, ?_⟩
      · intro v
        rw [hχ b' hb' v]
        congr 1
        funext i
        rw [hχ₀ζ (eta b (π' i.castSucc)), hπ'cast i, ← hb'k (π i) (π i).2]
      · intro s
        have hχT : χ (χ.symm ⟨b', hb'⟩) = ⟨b', hb'⟩ := MulEquiv.apply_symm_apply χ _
        have hκT : κ (χ.symm ⟨b', hb'⟩) = (b' : G) := by
          show ((χ (χ.symm ⟨b', hb'⟩) : L) : G) = (b' : G)
          rw [hχT]
        have hbG : (b' : G) * x ^ (j : ℕ) = (b : G) := by
          simp only [b', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
          group
        have hcomm : Commute (κ s) (x ^ (j : ℕ)) := by
          have hmem : κ s ∈ L := (χ s).2
          have hcent := hLx hmem
          rw [Subgroup.mem_centralizer_singleton_iff] at hcent
          exact (show Commute (κ s) x from hcent).pow_right (j : ℕ)
        have hconj : κ (χ.symm ⟨b', hb'⟩ * s * (χ.symm ⟨b', hb'⟩)⁻¹) =
            (b' : G) * κ s * (b' : G)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hκT]
        rw [hconj]
        calc (b : G) * κ s * (b : G)⁻¹
            = ((b' : G) * x ^ (j : ℕ)) * κ s * ((b' : G) * x ^ (j : ℕ))⁻¹ := by
                rw [← hbG]
          _ = (b' : G) * (x ^ (j : ℕ) * κ s) * (x ^ (j : ℕ))⁻¹ * (b' : G)⁻¹ := by
                rw [mul_inv_rev]; group
          _ = (b' : G) * (κ s * x ^ (j : ℕ)) * (x ^ (j : ℕ))⁻¹ * (b' : G)⁻¹ := by
                rw [← hcomm.eq]
          _ = (b' : G) * κ s * (b' : G)⁻¹ := by group
  exact ⟨π', hπ'last, hframe⟩

end CFSG.StandardType.OrthAnchor

end
