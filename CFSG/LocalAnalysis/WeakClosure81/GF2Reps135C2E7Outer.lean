module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterNormalForm
import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
import CFSG.LocalAnalysis.SeitzReduction.Fusion

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem e7_exists_inv_mul_eq_root {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .E7 K)) (h2 : α * α = 1)
    (hout : ∀ c : adjointGroup .E7 K, α ≠ MulAut.conj c) :
    ∃ (ψ : MulAut (adjointGroup .E7 K)) (x : adjointGroup .E7 K) (d : Kˣ),
      ψ ((α x)⁻¹ * x) = ⟨pinnedX .E7 K (highRoot .E7) (d : K), pinnedX_mem_adjointGroup _ _⟩ := by
  classical
  obtain ⟨e, σ, g, hf, hσ, hαeq⟩ :=
    CFSG.StandardType.ggFieldOuterNormalForm_E78 hf hK (Or.inl rfl) α h2 hout
  have he : 1 ≤ e := by omega
  have hK2 : Nat.card K = 2 ^ (2 * e) := by rw [hK, hf]
  have hK' : Nat.card K = (2 ^ e) ^ 2 := by
    rw [hK2, mul_comm 2 e, pow_mul]
  have hexpr : ∀ u : adjointGroup .E7 K,
      (α u : ModGL .E7 K) =
        (g : ModGL .E7 K) * rootDiagUnit .E7 (1 : Fin Tag.E7.rank → Kˣ) *
          Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E7 K) *
            (rootDiagUnit .E7 (1 : Fin Tag.E7.rank → Kˣ))⁻¹ * (g : ModGL .E7 K)⁻¹ := by
    intro u
    rw [hαeq]
    simp only [MulAut.mul_apply, MulAut.conj_apply, coe_entrywiseAdjointAut,
      rootDiagUnit_one, Subgroup.coe_mul, Subgroup.coe_inv, mul_one, inv_one]
  obtain ⟨β, -, hcos⟩ :=
    (exceptional_Lang_quadratic_field_coset_conjugacy Nat.prime_two he K hK' σ.toRingHom hσ).1
      Tag.E7
  obtain ⟨ψ, hψ, -⟩ := (hcos g (1 : Fin Tag.E7.rank → Kˣ)).2 α hexpr h2
  obtain ⟨c, hc⟩ : ∃ c : K, c ^ 2 ^ e ≠ c := by
    by_contra! h
    have hle := CFSG.SeitzReduction.natCard_le_of_forall_pow_eq_self
      (Nat.one_lt_two_pow (by omega : e ≠ 0)) (Set.univ : Set K) fun a _ => h a
    rw [Nat.card_univ, hK2] at hle
    have hlt : 2 ^ e < 2 ^ (2 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hd : c - σ c ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hc (by rw [← hσ c]; exact h.symm)
  let u : adjointGroup .E7 K :=
    ⟨pinnedX .E7 K (highRoot .E7) c, pinnedX_mem_adjointGroup _ _⟩
  let x : adjointGroup .E7 K := ψ⁻¹ u
  let d : Kˣ := Units.mk0 (c - σ c) hd
  refine ⟨ψ, x, d, ?_⟩
  have hψx : ψ x = u := by simp [x]
  have hψαx : ψ (α x) = (ψ * α * ψ⁻¹) u := by simp [x]
  have h1 : (ψ (α x) : ModGL .E7 K) =
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E7 K) := by
    rw [hψαx]
    exact hψ u
  have h2 : (ψ x : ModGL .E7 K) = (u : ModGL .E7 K) := by rw [hψx]
  apply Subtype.ext
  have hstep : (ψ ((α x)⁻¹ * x) : ModGL .E7 K) =
      (ψ (α x) : ModGL .E7 K)⁻¹ * (ψ x : ModGL .E7 K) := by
    rw [map_mul, map_inv]
    rfl
  rw [hstep, h1, h2]
  dsimp only [u]
  have hmap : Units.map (entrywiseHom σ.toRingHom)
      (pinnedX .E7 K (highRoot .E7) c) =
        pinnedX .E7 K (highRoot .E7) (σ c) := by
    apply Units.ext
    rw [Units.coe_map]
    change entrywise σ.toRingHom
      (pinnedX .E7 K (highRoot .E7) c : Module.End K (RootModule .E7 K)) =
        pinnedX .E7 K (highRoot .E7) (σ c)
    rw [entrywise_pinnedX]
    rfl
  rw [hmap, pinnedX_neg, ← pinnedX_add]
  have harg : -σ c + c = (d : K) := by
    dsimp only [d]
    rw [Units.val_mk0]
    ring
  rw [harg]

end CFSG.LocalAnalysis.WeakClosure81
