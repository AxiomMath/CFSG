module

public import CFSG.Quasithin.Background.A1cModuleUnits
public import CFSG.Quasithin.Background.Module
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin

namespace XMod

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

variable (A Q) in
private noncomputable def quotRestr : eqvAut A Q →* eqvAut A (Q ⧸ fixed A (⊤ : Subgroup Q)) where
  toFun φ := ⟨quotAut φ, fun a q => by
    refine QuotientGroup.induction_on q fun x => ?_
    rw [smul_quotMk, quotAut_mk, quotAut_mk, smul_quotMk, φ.2 a x]⟩
  map_one' := by
    refine Subtype.ext (MulEquiv.ext fun q => ?_)
    refine QuotientGroup.induction_on q fun x => ?_
    exact quotAut_mk 1 x
  map_mul' φ ψ := by
    refine Subtype.ext (MulEquiv.ext fun q => ?_)
    refine QuotientGroup.induction_on q fun x => ?_
    change quotAut (φ * ψ) (QuotientGroup.mk x) = quotAut φ (quotAut ψ (QuotientGroup.mk x))
    rw [quotAut_mk, quotAut_mk, quotAut_mk]
    rfl

private theorem quotRestr_mk (φ : eqvAut A Q) (x : Q) :
    (quotRestr A Q φ : MulAut (Q ⧸ fixed A (⊤ : Subgroup Q))) (QuotientGroup.mk x) =
      QuotientGroup.mk ((φ : MulAut Q) x) :=
  quotAut_mk φ x

theorem eq_bot_of_isPerfect_of_le_eqvAut [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hcomm : commOf A (⊤ : Subgroup Q) = ⊤) (hirr : IsIrrSec A (fixed A (⊤ : Subgroup Q)) ⊤)
    {H : Subgroup (MulAut Q)} (hH : H ≤ eqvAut A Q) (hperf : Group.IsPerfect ↥H) : H = ⊥ := by
  have hP : ∀ q : Q ⧸ fixed A (⊤ : Subgroup Q), q ^ 2 = 1 := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    rw [← QuotientGroup.mk_pow, hQ x, QuotientGroup.mk_one]
  obtain ⟨-, hfield, -⟩ := eqvEnd_isField_charTwo hP (isIrrSec_quotient hirr)
  have hab : ∀ x y : eqvAut A (Q ⧸ fixed A (⊤ : Subgroup Q)), x * y = y * x := fun x y =>
    toEqvEnd_injective (by rw [map_mul, map_mul]; exact hfield.mul_comm _ _)
  let ρ : ↥H →* eqvAut A (Q ⧸ fixed A (⊤ : Subgroup Q)) :=
    (quotRestr A Q).comp (Subgroup.inclusion hH)
  have hker : ρ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.1 hperf, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab _ _
  have htriv : ∀ h ∈ H, ∀ x : Q, x⁻¹ * h x ∈ fixed A (⊤ : Subgroup Q) := by
    intro h hh x
    have h1 : ρ ⟨h, hh⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      trivial
    have h2 := congrArg (fun z : eqvAut A (Q ⧸ fixed A (⊤ : Subgroup Q)) =>
      (z : MulAut (Q ⧸ fixed A (⊤ : Subgroup Q))) (QuotientGroup.mk x)) h1
    change (quotRestr A Q ⟨h, hH hh⟩ : MulAut (Q ⧸ fixed A (⊤ : Subgroup Q)))
      (QuotientGroup.mk x) = QuotientGroup.mk x at h2
    rw [quotRestr_mk] at h2
    exact QuotientGroup.eq.1 h2.symm
  have hfix : commOf A (⊤ : Subgroup Q) ≤ fixed ↥H ⊤ := by
    rw [commOf_le_iff]
    intro a l _
    refine ⟨trivial, fun h => ?_⟩
    have he : (h : MulAut Q) (a • l) = a • (h : MulAut Q) l := hH h.2 a l
    set c := l⁻¹ * (h : MulAut Q) l with hcdef
    have hc : a • c = c := (htriv h h.2 l).2 a
    have hl : (h : MulAut Q) l = l * c := by rw [hcdef, mul_inv_cancel_left]
    change (h : MulAut Q) (a • l * l⁻¹) = a • l * l⁻¹
    rw [map_mul, map_inv, he, hl, smul_mul', hc, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  have htop : fixed ↥H (⊤ : Subgroup Q) = ⊤ := eq_top_iff.2 (hcomm.symm.le.trans hfix)
  rw [Subgroup.eq_bot_iff_forall]
  intro h hh
  ext x
  exact fixed_top_eq_top_iff.1 htop ⟨h, hh⟩ x

end XMod

theorem d35Two_caseI {Y : Type} [CommGroup Y] [Finite Y] (hY : ∀ y : Y, y ^ 2 = 1)
    {K K' : Subgroup (MulAut Y)} (hirr : commV K ∈ IrrPlus K ⊤) (hcK : commV K = ⊤)
    (hq : CFSG.IsQuasisimple ↥K') (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) : False := by
  rw [hcK] at hirr
  obtain ⟨-, -, hcomm1, hirr1⟩ := hirr
  have hle : K' ≤ XMod.eqvAut ↥K Y := fun b hb => XMod.mem_eqvAut_iff.2 fun a p =>
    congrArg (fun φ : MulAut Y => φ p) (hcomm a a.2 b hb).symm
  obtain ⟨hperf, -, a, b, hab⟩ := hq
  have hbot := XMod.eq_bot_of_isPerfect_of_le_eqvAut hY hcomm1 hirr1 hle hperf
  have hsub : ∀ x : ↥K', x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.1 (hbot.le x.2))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [hsub x, hsub y])

end CFSG.Quasithin
