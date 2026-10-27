module

public import CFSG.Quasithin.Background.HTransport
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.Quasithin

namespace B69

variable {V : Type} [CommGroup V]

@[expose] def secInfEquiv (W U : Subgroup V) : Sec W (W ⊓ U) ≃* Sec W U :=
  QuotientGroup.quotientMulEquivOfEq (Subgroup.inf_subgroupOf_left U W)

theorem centSec_inf (W U : Subgroup V) : centSec W (W ⊓ U) = centSec W U := by
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw => (h2 w hw).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw => ⟨W.mul_mem ((h1 w).2 hw) (W.inv_mem hw), h2 w hw⟩⟩

theorem autQuot_map_congr {V₀ : Type} [CommGroup V₀] (Y : Subgroup (MulAut V₀))
    {N N' : Subgroup V₀} (h : N' = N) :
    (autQuot Y N').map (H.congrHom (QuotientGroup.quotientMulEquivOfEq h)) = autQuot Y N := by
  subst h
  have he : QuotientGroup.quotientMulEquivOfEq (rfl : N' = N') = MulEquiv.refl (V₀ ⧸ N') :=
    MulEquiv.ext fun q => by
      induction q using QuotientGroup.induction_on with
      | H v => rfl
  have hid : ∀ x : MulAut (V₀ ⧸ N'),
      H.congrHom (QuotientGroup.quotientMulEquivOfEq (rfl : N' = N')) x = x := by
    intro x
    rw [he]
    rfl
  ext φ
  simp only [Subgroup.mem_map, hid]
  exact ⟨fun ⟨x, hx, hxφ⟩ => hxφ ▸ hx, fun hφ => ⟨φ, hφ, rfl⟩⟩

theorem map_autSec_inf (X : Subgroup (MulAut V)) (W U : Subgroup V) :
    (autSec X W (W ⊓ U)).map (H.congrHom (secInfEquiv W U)) = autSec X W U :=
  autQuot_map_congr (autSub X W) (Subgroup.inf_subgroupOf_left U W)

theorem rAV_autSec_inf (X : Subgroup (MulAut V)) (W U : Subgroup V) :
    rAV (autSec X W U) = rAV (autSec X W (W ⊓ U)) := by
  unfold rAV
  rw [← map_autSec_inf X W U, H.rk_map_congrHom, H.rkIdx_fixV_map_congrHom]

theorem isElemAbelian2_autSec {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hA : IsElemAbelian2 A) (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U) :
    IsElemAbelian2 (autSec A W U) := by
  rw [← B5.range_secHom A hAW hAU]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 a a.2 b b.2)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2 a a.2)
    rw [this, map_one]

theorem autSec_ne_bot {A : Subgroup (MulAut V)} {W U : Subgroup V} (hAW : A ≤ stabSub W)
    (hAU : A ≤ stabSub U) (hnt : ¬ A ≤ centSec W U) : autSec A W U ≠ ⊥ := by
  intro hbot
  apply hnt
  intro a ha
  have hmem : B5.secHom A hAW hAU ⟨a, ha⟩ ∈ autSec A W U := by
    rw [← B5.range_secHom A hAW hAU]
    exact ⟨⟨a, ha⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (B5.mem_ker_secHom A hAW hAU ⟨a, ha⟩).1 (MonoidHom.mem_ker.2 hmem)

theorem isQuadratic_autSec {A : Subgroup (MulAut V)} {W U : Subgroup V} (hAW : A ≤ stabSub W)
    (hAU : A ≤ stabSub U) (hq : IsQuadratic A) : IsQuadratic (autSec A W U) := by
  rw [IsQuadratic, commV, Subgroup.closure_le]
  rintro _ ⟨φ, hφ, s, rfl⟩
  rw [← B5.range_secHom A hAW hAU] at hφ
  obtain ⟨⟨a, ha⟩, rfl⟩ := hφ
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  intro ψ hψ
  rw [← B5.range_secHom A hAW hAU] at hψ
  obtain ⟨⟨b, hb⟩, rfl⟩ := hψ
  have hfix : b ((a : MulAut V) (w : V) * (w : V)⁻¹) = (a : MulAut V) (w : V) * (w : V)⁻¹ :=
    hq (Subgroup.subset_closure ⟨a, ha, w, rfl⟩) b hb
  have hW' : ∀ g : ↥A, ∀ w : ↥W, (g : MulAut V) (w : V) ∈ W := fun g w => (hAW g.2 w).2 w.2
  set x : ↥W := ⟨(a : MulAut V) (w : V), hW' ⟨a, ha⟩ w⟩ * w⁻¹ with hx
  have hxV : ((x : ↥W) : V) = (a : MulAut V) (w : V) * (w : V)⁻¹ := rfl
  have hLHS : (B5.secHom A hAW hAU ⟨a, ha⟩) (QuotientGroup.mk w) * (QuotientGroup.mk w)⁻¹ =
      (QuotientGroup.mk x : Sec W U) := by
    rw [B5.secHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  show (B5.secHom A hAW hAU ⟨b, hb⟩)
      ((B5.secHom A hAW hAU ⟨a, ha⟩) (QuotientGroup.mk w) * (QuotientGroup.mk w)⁻¹) =
    (B5.secHom A hAW hAU ⟨a, ha⟩) (QuotientGroup.mk w) * (QuotientGroup.mk w)⁻¹
  rw [hLHS, B5.secHom_mk]
  congr 1
  apply Subtype.ext
  show (b : MulAut V) ((x : ↥W) : V) = ((x : ↥W) : V)
  rw [hxV]
  exact hfix

end B69

end CFSG.Quasithin
