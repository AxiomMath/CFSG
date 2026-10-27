module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorusConj
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorusNormalizer
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.LocalAnalysis.StandardType.GGSpinInnerAction
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKToral

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial

private theorem ggSecFiveBPermOmK_normBar_signs {p m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (E : QuadExt F K (unitaryInvolution K 2 f)) (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) {ε : Fin m → ZMod p} (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (t : Fin m → Multiplicative (ZMod p)) :
    normOmegaConj E (normBar_mem_orthogonalGroup E (Finset.univ.filter fun k => ε k = -1))
        (normPlaneTorus E hm hpq χ t) =
      normPlaneTorus E hm hpq χ
        (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (t k))) := by
  have hp : p.Prime := Fact.out
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  rw [normOmegaConj_normBar_normPlaneTorus]
  congr 1
  funext k
  rcases hε k with h | h
  · have hk : k ∉ Finset.univ.filter fun k => ε k = -1 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
      exact ZMod.neg_one_ne_one.symm
    rw [if_neg hk, h, one_mul, ofAdd_toAdd]
  · have hk : k ∈ Finset.univ.filter fun k => ε k = -1 := by simp [h]
    rw [if_pos hk, h, neg_one_mul, ofAdd_neg, ofAdd_toAdd]

private theorem ggSecFiveBPermOmK_frame_of_signFree {G : Type} [Group G] {p n m f : ℕ}
    [Fact p.Prime] {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (E : QuadExt F K (unitaryInvolution K 2 f)) (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    {Bs X : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π' : Fin (m + 1) ≃ Fin n} {c : ZMod p} (hc : c ≠ 0) {ε : Fin m → ZMod p}
    (hε : ∀ k, ε k = 1 ∨ ε k = -1) {χ₀ : Multiplicative (ZMod p) →* Kˣ}
    (hχ₀ : Function.Injective χ₀) {T : ↥Bs →* (Fin m → Multiplicative (ZMod p))}
    (halign : ∀ (b : ↥Bs) k, Multiplicative.toAdd (T b k) =
      ε k * c * Multiplicative.toAdd (eta b (π' k.succ)))
    {κ : normOmega E m →* G} (hκ : Function.Injective κ) (hκX : κ.range = X)
    (hframe : ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ =
      κ (normPlaneTorus E hm hpq χ₀
          (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))) * s *
        (normPlaneTorus E hm hpq χ₀
          (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))))⁻¹)) :
    ∃ χ : Multiplicative (ZMod p) →* Kˣ,
      GGSecFiveBPermOmKFrame E Bs X eta ((finRotate (m + 1)).trans π') κ χ := by
  let χ : Multiplicative (ZMod p) →* Kˣ :=
    χ₀.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c))
  have hχapp : ∀ a, χ a = χ₀ (Multiplicative.ofAdd (c * Multiplicative.toAdd a)) := fun _ => rfl
  have hχinj : Function.Injective χ := by
    intro a b hab
    rw [hχapp, hχapp] at hab
    exact Multiplicative.toAdd.injective
      (mul_left_cancel₀ hc (Multiplicative.ofAdd.injective (hχ₀ hab)))
  refine ⟨χ, hκ, hκX, hχinj, fun b => ⟨normPlaneTorus E hm hpq χ₀
    (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))), fun v => ?_, hframe b⟩⟩
  rw [normPlaneTorus_apply]
  congr 1
  funext i
  have hπ : ((finRotate (m + 1)).trans π') i.castSucc = π' i.succ := by
    rw [Equiv.trans_apply, finRotate_succ_apply, Fin.coeSucc_eq_succ]
  have hee : ε i * ε i = 1 := by rcases hε i with h | h <;> simp [h]
  have hsign : ε i * Multiplicative.toAdd (T b i) =
      c * Multiplicative.toAdd (eta b (π' i.succ)) := by
    rw [halign b i, ← mul_assoc, ← mul_assoc, hee, one_mul]
  rw [hπ, hχapp, hsign]

private theorem range_subtype_comp {G S : Type} [Group G] [Group S] (X : Subgroup G) (ψ : S ≃* X) :
    (X.subtype.comp ψ.toMonoidHom).range = X := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (ψ y).2
  · intro hx
    exact ⟨ψ.symm ⟨x, hx⟩, by simp⟩

theorem ggSecFiveBPermOmK_exists_frame_of_inner {G : Type} [Group G] [Finite G] {p n m f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K]
    [CharP K 2] (E : QuadExt F K (unitaryInvolution K 2 f)) (hK : UnitaryFieldData 2 f K)
    (hpq : p ∣ 2 ^ f + 1) (hm : 3 ≤ m) (hn : n = m + 1) {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hinner : ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹)
    (e : ↥X ≃* normOmega E m) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∃ π : Fin (m + 1) ≃ Fin n, π (Fin.last m) = i0 ∧
      ∃ (κ : normOmega E m →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
        GGSecFiveBPermOmKFrame E Bs X eta π κ χ := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  obtain rfl : n = r + 2 := by omega
  have hm2 : 2 ≤ r + 1 := by omega
  have hr : 2 ≤ r := by omega
  obtain ⟨χ₀, hχ₀⟩ := exists_injective_unitChar (p := p) hK hpq
  have hZS : Subgroup.center (normOmega E (r + 1)) = ⊥ := center_normOmega_eq_bot E hm2
  have hZX : Subgroup.center ↥X = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, hZS, Subgroup.map_bot]
  have hF : Nat.card F = 2 ^ f := card_base_eq_two_pow E hK
  obtain ⟨hDinj, κ₀, hκ₀, hκ₀X, htor⟩ := ggSecFiveBPermSpK_exists_toral_of_inner hBs
    (φ := X.subtype.comp e.symm.toMonoidHom) (X.subtype_injective.comp e.symm.injective)
    (range_subtype_comp X e.symm) hZX hinner
    (ggSecFiveBPermSpK_pow_mul_card_inf_centralizer_le hp2 hA)
    (D := normPlaneTorus E hm2 hpq χ₀) fun A hA hcardA => by
      obtain ⟨g, hg, hmap⟩ :=
        exists_normOmegaConj_map_eq_normPlaneTorus_range E hp2 hF hm2 hpq hχ₀ A hA hcardA
      exact ⟨normOmegaConj E hg, hmap⟩
  obtain ⟨T, hT, π', hπ'0, c, hc, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_align_of_toral hp2 hr eta hA hκ₀ hκ₀X hDinj hZS htor
      fun u hu => normPlaneTorus_exists_signedPerm_of_normalizes E hm2 hpq hχ₀ u hu
  obtain ⟨κ, hκ, hκX, hframe⟩ := ggSecFiveBPermSpK_exists_signFree_of_conj hκ₀ hκ₀X hT
    (α := normOmegaConj E (normBar_mem_orthogonalGroup E (Finset.univ.filter fun k => ε k = -1)))
    (ggSecFiveBPermOmK_normBar_signs hp2 E hm2 hpq χ₀ hε)
    (τ := fun b => normPlaneTorus E hm2 hpq χ₀
      (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k)))) fun _ => rfl
  obtain ⟨χ, hχ⟩ := ggSecFiveBPermOmK_frame_of_signFree E hm2 hpq hc hε hχ₀
    (fun b k => by
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
        using halign (eta b) k) hκ hκX hframe
  refine ⟨(finRotate (r + 1 + 1)).trans π', ?_, κ, χ, hχ⟩
  rw [Equiv.trans_apply, finRotate_last]
  exact hπ'0

section Marked

theorem ggSecFiveBPermOmK_exists_frame (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p n m f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Algebra (GaloisField 2 f) K]
    [Finite K] [CharP K 2] (E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f))
    (hK : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (hm : 3 ≤ m) (hn : n = m + 1)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* normOmega E m) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∃ π : Fin (m + 1) ≃ Fin n, π (Fin.last m) = i0 ∧
      ∃ (κ : normOmega E m →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
        GGSecFiveBPermOmKFrame E Bs X eta π κ χ := by
  refine ggSecFiveBPermOmK_exists_frame_of_inner hp2 E hK hpq hm hn hBs ?_ e eta hA
  rcases Nat.even_or_odd m with hev | hodd
  · obtain ⟨ψ⟩ := nonempty_spinPlus_mulEquiv_normOmega E hev (by omega)
    exact ggSpinPlusInnerAction_of_mp hMp (by omega) hK.one_le hmark
      (X.subtype.comp (ψ.trans e.symm).toMonoidHom)
      (X.subtype_injective.comp (ψ.trans e.symm).injective) (range_subtype_comp X (ψ.trans e.symm))
  · obtain ⟨ψ⟩ := nonempty_spinMinus_mulEquiv_normOmega E hodd hm
      (CFSG.LieType.Universal.minusCoeffs_irr 2 f)
    exact ggSpinMinusInnerAction_of_mp hMp (by omega) hK.one_le hmark
      (X.subtype.comp (ψ.trans e.symm).toMonoidHom)
      (X.subtype_injective.comp (ψ.trans e.symm).injective) (range_subtype_comp X (ψ.trans e.symm))

end Marked

end CFSG.StandardType

end
