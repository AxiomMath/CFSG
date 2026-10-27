module

public import CFSG.Quasithin.Vol2.Ch11SecAKA11
public import CFSG.Quasithin.Vol2.Ch11SecAKA7
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4J

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Open (pCoreOf)

namespace KA

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem delta_fix [Finite K] [Finite W] (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (g : StatedSp 2 K)
    (hfix : Ch11.SecA.RadicalFixes H Z (hf.pre (gmapSp g (spLine K)).toAddSubgroup))
    (U₃ : Subgroup W) :
    ∀ u ∈ U₃, (∀ s ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmapSp g (spLine K)).toAddSubgroup))), s u = u) ↔
        u ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  intro u _
  constructor
  · intro h
    refine hfix u fun x hx => ?_
    rw [h x ((mem_pCoreOf_iff' _ x).mpr hx), mul_inv_cancel]
    exact one_mem Z
  · intro hu s hs
    exact Ch11.SecS.C11P9A.fix_gammaW_one hf hZ g s (Subgroup.map_subtype_le _ hs) u hu

theorem delta_line [Finite K] [Finite W] (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {g : StatedSp 2 K} {P : Subgroup (MulAut W)}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W))
    (hP2 : IsPGroup 2 P) (hPΓ : P ≤ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmapSp g (spLine K)).toAddSubgroup))) :
    ∀ R : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf R (perfectCore (H ⊓
      Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))) → R ≤ P →
      ∀ U : Subgroup W, hf.pre (gmapSp g (spLine K)).toAddSubgroup ≤ U →
        U ≤ hf.pre (gmapSp g (spHyp K)).toAddSubgroup →
        (hf.pre (gmapSp g (spLine K)).toAddSubgroup).relIndex U = Nat.card K →
        R ≤ Ch11.SecA.stabW U → U = hf.pre (gmapSp g (spPlane K)).toAddSubgroup := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  intro R hR hRP U h1U hU3 hidx hRU
  rw [eq_of_isSylowTwoOf_le hR hRP hPΓ hP2] at hRU
  have hZU : Z ≤ U := (hf.le_pre _).trans h1U
  have hZU₁ : Z.relIndex (hf.pre (gmapSp g (spLine K)).toAddSubgroup) = Nat.card K := by
    rw [← hf.card_img, hf.img_pre, ← card_spLine (K := K), ← card_gmapSp g (spLine K)]
    rfl
  have hcardS : Nat.card (hf.img U) = Nat.card K ^ 2 := by
    rw [hf.card_img, ← Subgroup.relIndex_mul_relIndex Z _ U (hf.le_pre _) h1U, hidx, hZU₁, sq]
  let S' : AddSubgroup (Fin 2 ⊕ Fin 2 → K) :=
    (hf.img U).comap (Matrix.mulVecLin (mat 2 K g)).toAddMonoidHom
  have hmemS' : ∀ x, x ∈ S' ↔ mat 2 K g *ᵥ x ∈ hf.img U := fun x => Iff.rfl
  have hcardS' : Nat.card S' = Nat.card (hf.img U) := Nat.card_congr
    { toFun := fun x => ⟨mat 2 K g *ᵥ x, (hmemS' x).mp x.2⟩
      invFun := fun y => ⟨mat 2 K g⁻¹ *ᵥ y, (hmemS' _).mpr (by rw [mat_mulVec_inv]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (mat_inv_mulVec g x)
      right_inv := fun y => Subtype.ext (mat_mulVec_inv g y) }
  have h1 : ∀ x ∈ spLine K, x ∈ S' := by
    intro x hx
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ x)
    have hw1 : w ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup := by
      show f w ∈ gmapSp g (spLine K)
      rw [hw, mem_gmapSp, mat_inv_mulVec]
      exact hx
    exact ⟨w, h1U hw1, hw⟩
  have h3 : ∀ x ∈ S', x ∈ spHyp K := by
    intro x hx
    obtain ⟨w, hwU, hw⟩ := (hmemS' x).mp hx
    have hw3 : f w ∈ gmapSp g (spHyp K) := hU3 hwU
    rw [hw, mem_gmapSp, mat_inv_mulVec] at hw3
    exact hw3
  have hq : ∀ t : K, ∀ x ∈ S', mat 2 K (qSp 0 0 t) *ᵥ x ∈ S' := by
    intro t x hx
    obtain ⟨w, hwU, hw⟩ := (hmemS' x).mp hx
    have hp : ((π (g * qSp 0 0 t * g⁻¹) : ↥H) : MulAut W) ∈ P :=
      (hg _).mpr ⟨_, qSp_mem_Usp 0 0 t, rfl⟩
    have hpU := (Ch11.SecA.mem_stabW.mp (hRU hp) w).mp hwU
    refine (hmemS' _).mpr ⟨_, hpU, ?_⟩
    rw [hf.act4, hw, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      mat_inv_mulVec]
  have hS := eq_spPlane_of_stable h1 h3 hq (hcardS'.trans hcardS)
  have himg : hf.img U = (gmapSp g (spPlane K)).toAddSubgroup := by
    ext y
    change y ∈ hf.img U ↔ y ∈ gmapSp g (spPlane K)
    rw [mem_gmapSp, ← hS, hmemS', mat_mulVec_inv]
  rw [← hf.pre_img hZU, himg]

end KA

end CFSG.Quasithin.Vol2.KGNat
