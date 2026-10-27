module

public import CFSG.Monster.Existence.TwoB
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseExtraspecial
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergNativeCo1Centralizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated Subgroup
  CFSG.LocalAnalysis.ComponentInitial.NativeCo1Centralizer
open scoped IsMulCommutative

theorem center_rhoQvis_eq_zRho : center rhoQvis = zRho := by
  have hzz : rhoQvisEquivQ.symm zQ = rhoN zQ :=
    Subtype.ext (Subtype.ext (rhoQvisEquivQ_symm_zQ.trans (xmat_eq_xB.trans
      coe_coe_rhoN_zQ.symm)))
  rw [center_rhoQvis, hzz]
  rfl

theorem centralizer_rhoQvis_eq :
    centralizer (rhoQvis : Set Gvis) = (center rhoQvis).map rhoQvis.subtype := by
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, centralizer_rhoQvis_le hg⟩, mem_center_iff.2 fun r => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.1 hg r r.2
  · rintro ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.1 hc ⟨r, hr⟩)

theorem mem_rhoQvis_of_forall_conj_mem (h : Gvis)
    (hh : ∀ q ∈ rhoQvis, h * q * h⁻¹ * q⁻¹ ∈ (center rhoQvis).map rhoQvis.subtype) :
    h ∈ rhoQvis := by
  rw [← ker_conjVis, MonoidHom.mem_ker, conjVis_eq_one_iff]
  intro x
  rw [QuotientGroup.eq, ← center_rhoQvis_eq_zRho]
  obtain ⟨c, hc, hce⟩ := hh x x.2
  have h1 : MulAut.conjNormal h x = c * x := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, Subgroup.coe_mul]
    change h * (x : Gvis) * h⁻¹ = rhoQvis.subtype c * x
    rw [hce]
    group
  rw [h1, mul_inv_rev, mul_assoc, ← mem_center_iff.1 (inv_mem hc) x, inv_mul_cancel_left]
  exact inv_mem hc

theorem exists_mul_ne_mul_visQuot :
    ∃ a b : Gvis ⧸ rhoQvis, a * b ≠ b * a := by
  by_contra hab
  have : IsMulCommutative (Gvis ⧸ rhoQvis) :=
    ⟨⟨fun a b => not_not.1 fun h => hab ⟨a, b, h⟩⟩⟩
  have hp := Group.is_simple_iff_prime_card.1 VisQuot.isSimpleGroup_visQuot
  rw [VisQuot.natCard_visQuot] at hp
  norm_num at hp

theorem visQuot_inner_of_Co1_inner
    (hCo1 : ∀ α : MulAut Blueprint.NativeSporadic.Co1,
      ∃ g : Blueprint.NativeSporadic.Co1, α = MulAut.conj g) :
    ∀ φ : MulAut (Gvis ⧸ rhoQvis), ∃ g : Gvis ⧸ rhoQvis, φ = MulAut.conj g := by
  intro φ
  let e : Gvis ⧸ rhoQvis ≃* Blueprint.NativeSporadic.Co1 := Co1Bridge.visQuotEquivCo1
  obtain ⟨s, hs⟩ := hCo1 ((e.symm.trans φ).trans e)
  refine ⟨e.symm s, MulEquiv.ext fun t => ?_⟩
  have h1 := congrArg (fun β : MulAut Blueprint.NativeSporadic.Co1 => e.symm (β (e t))) hs
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

@[expose] def visModProj : rhoQvis →* Multiplicative (Additive VisMod) where
  toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk x))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem visModProj_surjective : Function.Surjective visModProj := fun w => by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd w))
  exact ⟨x, by
    change Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk x)) = w
    rw [hx]
    rfl⟩

theorem ker_visModProj : visModProj.ker = center rhoQvis := by
  rw [center_rhoQvis_eq_zRho]
  ext x
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk x : VisMod) = 1 ↔ x ∈ zRho
  exact QuotientGroup.eq_one_iff x

theorem visModProj_conj (k) (hk : k ∈ visImage) : ∃ h : Gvis, ∀ q : rhoQvis,
    visModProj (MulAut.conjNormal h q) =
      Multiplicative.ofAdd ((k : Additive VisMod →ₗ[ZMod 2] Additive VisMod)
        (Multiplicative.toAdd (visModProj q))) := by
  obtain ⟨c, rfl⟩ := hk
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨h, fun q => by rw [repQuot_mk]; rfl⟩

theorem Hmat_perfect_and_inner_of_Co1_inner
    (hCo1 : ∀ α : MulAut Blueprint.NativeSporadic.Co1,
      ∃ g : Blueprint.NativeSporadic.Co1, α = MulAut.conj g) :
    Group.IsPerfect Hmat ∧ ∀ α : MulAut Hmat, ∃ g : Hmat, α = MulAut.conj g := by
  change Group.IsPerfect Gvis ∧ ∀ α : MulAut Gvis, ∃ g : Gvis, α = MulAut.conj g
  have : Finite Gvis := Nat.finite_of_card_ne_zero (by
    rw [natCard_Gvis, twoBCentralizerOrder]
    positivity)
  have h23 : 23 ∣ Nat.card (Gvis ⧸ rhoQvis) := by
    rw [VisQuot.natCard_visQuot]
    norm_num
  exact CFSG.ComponentClassification.BMCase.perfect_and_inner_of_model
    isExtraspecialPGroup_rhoQvis (Or.inr natCard_rhoQvis) centralizer_rhoQvis_eq
    mem_rhoQvis_of_forall_conj_mem VisQuot.isSimpleGroup_visQuot exists_mul_ne_mul_visQuot
    (visQuot_inner_of_Co1_inner hCo1) h23 visModProj visModProj_surjective ker_visModProj
    visImage visModProj_conj visImage_irreducible pow_three_eq_one

end CFSG.Monster.Existence
