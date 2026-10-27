module

public import CFSG.Quasithin.Background.G117Inputs
import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.M22

public section

namespace CFSG.Quasithin

namespace G11

namespace G117

theorem mulAut_eq_of_mem_center {N : Type*} [Group N] (hperf : commutator N = ⊤)
    {φ ψ : MulAut N} (h : ∀ x : N, (ψ x)⁻¹ * φ x ∈ Subgroup.center N) : φ = ψ := by
  let f : N →* Subgroup.center N :=
    { toFun := fun x => ⟨(ψ x)⁻¹ * φ x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (ψ (x * y))⁻¹ * φ (x * y) = ((ψ x)⁻¹ * φ x) * ((ψ y)⁻¹ * φ y)
        have hc := Subgroup.mem_center_iff.1 (h x) (ψ y)⁻¹
        rw [map_mul, map_mul, mul_inv_rev]
        calc (ψ y)⁻¹ * (ψ x)⁻¹ * (φ x * φ y)
            = (ψ y)⁻¹ * ((ψ x)⁻¹ * φ x) * φ y := by simp only [mul_assoc]
          _ = ((ψ x)⁻¹ * φ x) * (ψ y)⁻¹ * φ y := by rw [hc]
          _ = ((ψ x)⁻¹ * φ x) * ((ψ y)⁻¹ * φ y) := by simp only [mul_assoc] }
  have hker : commutator N ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (f b).2 (f a : N)))
  rw [hperf] at hker
  ext x
  have h1 : f x = 1 := hker (Subgroup.mem_top x)
  have h2 : (ψ x)⁻¹ * φ x = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.1 h2).symm

theorem autHatM22Bound
    : AutHatM22Bound := by
  intro N _ _ hN
  obtain ⟨hq, -, ⟨e⟩⟩ := hN
  have hperf : commutator N = ⊤ := hq.1.commutator_eq_top
  have hchar : ∀ φ : MulAut N,
      (Subgroup.center N).map (φ : N ≃* N).toMonoidHom = Subgroup.center N := fun φ =>
    (Subgroup.map_equiv_eq_comap_symm φ (Subgroup.center N)).trans
      ((inferInstance : (Subgroup.center N).Characteristic).fixed φ.symm)
  let Φ : MulAut N → MulAut (N ⧸ Subgroup.center N) := fun φ =>
    QuotientGroup.congr (Subgroup.center N) (Subgroup.center N) φ (hchar φ)
  have hΦ : Function.Injective Φ := by
    intro φ ψ hφψ
    apply mulAut_eq_of_mem_center hperf
    intro x
    have h1 := congrArg (fun α : MulAut (N ⧸ Subgroup.center N) => α (x : N ⧸ Subgroup.center N))
      hφψ
    simp only [Φ] at h1
    exact QuotientGroup.eq.1 h1.symm
  have : Finite (N ⧸ Subgroup.center N) := inferInstance
  have : Finite (MulAut (N ⧸ Subgroup.center N)) :=
    Finite.of_injective (fun α : MulAut (N ⧸ Subgroup.center N) => (α : _ → _))
      DFunLike.coe_injective
  calc Nat.card (MulAut N) ≤ Nat.card (MulAut (N ⧸ Subgroup.center N)) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M22) :=
        Nat.card_congr (MulAut.congr e).toEquiv
    _ ≤ 2 * Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 := CFSG.Sporadic.Schreier.m22_mulAut_card
    _ = 887040 := by rw [CFSG.Sporadic.Schreier.m22_card]

end G117

end G11

end CFSG.Quasithin
