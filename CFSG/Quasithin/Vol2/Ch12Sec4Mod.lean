module

public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Vol2.Ch10SecD31D
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem sq_eq_one_sec (hW : ∀ w : W, w ^ 2 = 1) (C : Subgroup W)
    (x : Sec (⊤ : Subgroup W) C) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H w =>
    rw [← QuotientGroup.mk_pow, show w ^ 2 = 1 from Subtype.ext (by simpa using hW w),
      QuotientGroup.mk_one]

omit [Finite W] in
theorem commV_le_of_le {A B : Subgroup (MulAut W)} (h : A ≤ B) : commV A ≤ commV B :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ => ⟨x, h hx, v, hv⟩

theorem binaryNaturalSL_of_card_sixteen (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {X : Subgroup (MulAut W)} (hs : IsSimpleGroup X) (hX : Nat.card X = 168)
    (hcomm : commV X = ⊤) (hfix : Nat.card (fixV X) = 2) :
    BinaryNaturalSL X ⊤ (fixV X) 3 1 := by
  set C := fixV X with hC
  have hK : X ≤ stabSub C := by
    intro g hg u
    constructor
    · intro hu
      have h1 : g⁻¹ (g u) = g u := hu g⁻¹ (X.inv_mem hg)
      have h2 : g⁻¹ (g u) = u := by simp
      rw [h2.symm.trans h1]
      exact hu
    · intro hu
      rw [show g u = u from hu g hg]
      exact hu
  have hf : X ⊓ centSec ⊤ C = ⊥ := by
    have := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (B5.secHom X (InternalSec.le_stabSub_top X) hK).ker with h | h
    · refine eq_bot_iff.2 fun g hg => ?_
      have hk : (⟨g, hg.1⟩ : ↥X) ∈ (B5.secHom X (InternalSec.le_stabSub_top X) hK).ker :=
        (B5.mem_ker_secHom X _ hK _).2 hg.2
      rw [h, Subgroup.mem_bot] at hk
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hk)
    · exfalso
      have hle : commV X ≤ C := by
        rw [commV, Subgroup.closure_le]
        rintro _ ⟨x, hx, v, rfl⟩
        have hk : (⟨x, hx⟩ : ↥X) ∈ (B5.secHom X (InternalSec.le_stabSub_top X) hK).ker :=
          h ▸ Subgroup.mem_top _
        exact ((B5.mem_ker_secHom X _ hK _).1 hk).2 v trivial
      rw [hcomm] at hle
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_top, hcard, hfix] at h1
      norm_num at h1
  have hC8 : Nat.card (Sec (⊤ : Subgroup W) C) = 2 ^ 3 := by
    have h1 := card_sec_mul (V := W) (le_top : C ≤ ⊤)
    rw [Subgroup.card_top, hcard, hfix] at h1
    omega
  obtain ⟨π, hπ⟩ := G64.realizesVia_top_of_card (sq_eq_one_sec hW C) hC8
  have : Finite (MulAut (Sec (⊤ : Subgroup W) C)) :=
    Finite.of_injective _ DFunLike.coe_injective
  have hcardTop : Nat.card (MulAut (Sec (⊤ : Subgroup W) C)) ≤ 168 := by
    have h1 := Nat.card_le_card_of_surjective π hπ.1
    have h2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 := by
      rw [← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv]
      exact card_sl_three_zmod_two
    rw [Subgroup.card_top] at h1
    omega
  have hAut : Nat.card (autSec X ⊤ C) = 168 := by
    have h1 := card_autSec_mul (InternalSec.le_stabSub_top X) hK
    rw [hf, Subgroup.card_bot, mul_one, hX] at h1
    exact h1
  have htop : autSec X ⊤ C = ⊤ := Subgroup.eq_top_of_le_card _ (by rw [hAut]; exact hcardTop)
  refine InternalSec.binaryNaturalSL_of_autSec hK hf
    ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ?_⟩
  rw [htop]
  exact ⟨π, hπ⟩

theorem fixV_le_commV_zpowers_of_normalizes (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 4) {X : Subgroup (MulAut W)}
    (hnat : BinaryNaturalSL X ⊤ (fixV X) 3 1) (hcomm : commV X = ⊤) {x : MulAut W}
    (hx : ∀ g, g ∈ X ↔ x * g * x⁻¹ ∈ X) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) :
    fixV X ≤ commV (Subgroup.zpowers x) := by
  obtain ⟨D⟩ := hnat.toL3Coord
  have hxX : x ∈ X := Vol2.Ch10.SecD.mem_of_normalizes D hcomm hx
  have h16 : Nat.card W = 16 := by rw [hcard]; norm_num
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcomm h16
  obtain ⟨-, -, -, h4⟩ := B4_8_2 hW h16 hnat hind
  rw [(h4 x hxX hx1 hx2).1]
  intro v hv y hy
  exact hv y ((Subgroup.zpowers_le.2 hxX) hy)

@[expose] def B46OffenderCommEqFix : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X L₀ : Subgroup (MulAut W), L₀ ≤ X → X ≤ Subgroup.normalizer (L₀ : Set (MulAut W)) →
      X ⊓ Subgroup.centralizer (L₀ : Set (MulAut W)) = ⊥ → commV L₀ = ⊤ →
      G2NaturalDerived L₀ ⊤ (fixV L₀) 1 →
        ∀ A : Subgroup (MulAut W), IsFFStarOffender X A → commV A = fixV A

theorem fixV_le_commV_of_g2 (hB46 : B46OffenderCommEqFix) (hW : ∀ w : W, w ^ 2 = 1)
    {X L₀ A : Subgroup (MulAut W)} (hLX : L₀ ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L₀ : Set (MulAut W)))
    (hXC : X ⊓ Subgroup.centralizer (L₀ : Set (MulAut W)) = ⊥) (hcomm : commV L₀ = ⊤)
    (hnat : G2NaturalDerived L₀ ⊤ (fixV L₀) 1) (hA : IsA2 X A)
    (hr : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) : fixV X ≤ commV A := by
  obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le hW hA ((rAV_le_one_iff hW hA).2 hr)
  have h1 := hB46 W hW X L₀ hLX hXN hXC hcomm hnat B hB
  intro w hw
  have hwB : w ∈ fixV B := fun b hb => hw b (hB.1 hb)
  rw [← h1] at hwB
  exact commV_le_of_le hBA hwB

end CFSG.Quasithin.H13
