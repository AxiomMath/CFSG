module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3WInnerB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3WInnerC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_isPSL_of_isSLn {X : Type} [Group X] (h : IsSLn X 3 1) :
    IsPSL 3 2 1 X := by
  classical
  obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := h
  letI : Field K := hF
  letI : Finite K := hfin
  have hcardK : Nat.card K = 2 := by simpa using hcard
  have hsubsing : Subsingleton Kˣ := by
    have hlt : Nat.card Kˣ < Nat.card K := natCard_units_lt K
    rw [hcardK] at hlt
    have hle : Nat.card Kˣ ≤ 1 := by omega
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card] at hle
    exact Fintype.card_le_one_iff_subsingleton.mp hle
  have hscal : StatedScalars (Fin 3) K = ⊥ := by
    rw [eq_bot_iff]
    rintro A ⟨c, -, rfl⟩
    rw [Subgroup.mem_bot]
    rw [Subsingleton.elim c 1, map_one]
  have hsub : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
    rw [hscal]; simp
  refine ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, K, hF, hfin, hcard,
    ⟨?_⟩⟩
  refine e.trans ?_
  exact ((QuotientGroup.quotientMulEquivOfEq hsub).trans
    (QuotientGroup.quotientBot (G := ↥(StatedSL 3 K)))).symm

private theorem s16h_e3_l3_secHom_inj_on_L {U Z : Subgroup W} {L X : Subgroup (MulAut W)}
    (hLX : L ≤ X) (hXU : X ≤ stabSub U) (hXZ : X ≤ stabSub Z)
    (hfaith : L ⊓ centSec U Z = ⊥) {a b : ↥X}
    (ha : (a : MulAut W) ∈ L) (hb : (b : MulAut W) ∈ L)
    (h : B5.secHom X hXU hXZ a = B5.secHom X hXU hXZ b) :
    (a : MulAut W) = (b : MulAut W) := by
  let s := B5.secHom X hXU hXZ
  have h1 : s (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : ((a * b⁻¹ : ↥X) : MulAut W) ∈ centSec U Z :=
    (B5.mem_ker_secHom X hXU hXZ (a * b⁻¹)).mp (by
      rw [MonoidHom.mem_ker]; exact h1)
  have h2L : ((a * b⁻¹ : ↥X) : MulAut W) ∈ L := L.mul_mem ha (L.inv_mem hb)
  have h3 : ((a * b⁻¹ : ↥X) : MulAut W) = 1 :=
    Subgroup.mem_bot.mp (by rw [← hfaith]; exact ⟨h2L, h2⟩)
  have h4 : a * b⁻¹ = 1 := Subtype.ext h3
  have h5 : a = b := by
    have := congrArg (fun x : ↥X => x * b) h4
    simpa using this
  exact congrArg Subtype.val h5

private theorem s16h_e3_l3_conj_secHom_mem {U Z : Subgroup W} {L X : Subgroup (MulAut W)}
    (hLX : L ≤ X) (hXU : X ≤ stabSub U) (hXZ : X ≤ stabSub Z)
    (hXN : X ≤ normalizer (L : Set (MulAut W)))
    (hmap : (L.subgroupOf X).map (B5.secHom X hXU hXZ) = autSec L U Z)
    {x : ↥X} (l' : MulAut (Sec U Z)) (hl' : l' ∈ autSec L U Z) :
    B5.secHom X hXU hXZ x * l' * (B5.secHom X hXU hXZ x)⁻¹ ∈ autSec L U Z := by
  rw [← hmap] at hl' ⊢
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hl'
  refine Subgroup.mem_map.mpr ⟨x * a * x⁻¹, ?_, ?_⟩
  · change (x : MulAut W) * (a : MulAut W) * (x : MulAut W)⁻¹ ∈ L
    exact conj_mem_of_mem_normalizer (hXN x.2) (Subgroup.mem_subgroupOf.mp ha)
  · rw [map_mul, map_inv, map_mul]

theorem s16h_e3_l3_normalizer_inner (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {τ : MulAut W} (hτ : τ ∈ normalizer (L : Set (MulAut W))) :
    ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹ := by
  classical
  obtain ⟨hfaith, hsum'⟩ := s16h_e3_l3_quotient_natSum3 hW hL3
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hfaith' : L ⊓ centSec U Z = ⊥ := by rw [hU, hZ]; exact hfaith
  have hsum'' : SumOfNat (fun H A B => BinaryNaturalSL H A B 3 1) (autSec L U Z) ⊤ ⊥ 3 := by
    rw [hU, hZ]; exact hsum'
  have hLU : L ≤ stabSub U := by
    rw [hU]
    intro l hl
    exact StabLat.mem_stabSub_commSub (X := L) (Y := ⊤)
      (mem_stabSub.mpr (fun _ => by simp)) (Subgroup.le_normalizer hl)
  have hLfix : L ≤ stabSub (fixV L) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer (X := L) (K := L) Subgroup.le_normalizer
  have hLZ : L ≤ stabSub Z := by
    rw [hZ]
    intro l hl u
    exact ⟨fun h => ⟨(hLU hl u).mp h.1, (hLfix hl u).mp h.2⟩,
      fun h => ⟨(hLU hl u).mpr h.1, (hLfix hl u).mpr h.2⟩⟩
  have hτU : τ ∈ stabSub U := by
    rw [hU]
    exact StabLat.mem_stabSub_commSub (X := L) (Y := ⊤)
      (mem_stabSub.mpr (fun _ => by simp)) hτ
  have hτfix : τ ∈ stabSub (fixV L) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer (X := Subgroup.zpowers τ) (K := L)
      (Subgroup.zpowers_le.mpr hτ) (Subgroup.mem_zpowers τ)
  have hτZ : τ ∈ stabSub Z := by
    rw [hZ]
    intro u
    exact ⟨fun h => ⟨(hτU u).mp h.1, (hτfix u).mp h.2⟩,
      fun h => ⟨(hτU u).mpr h.1, (hτfix u).mpr h.2⟩⟩
  let X : Subgroup (MulAut W) := L ⊔ Subgroup.zpowers τ
  have hLX : L ≤ X := le_sup_left
  have hτX : τ ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
  have hXU : X ≤ stabSub U := sup_le hLU (Subgroup.zpowers_le.mpr hτU)
  have hXZ : X ≤ stabSub Z := sup_le hLZ (Subgroup.zpowers_le.mpr hτZ)
  have hXN : X ≤ normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hτ)
  let s := B5.secHom X hXU hXZ
  let xτ : ↥X := ⟨τ, hτX⟩
  let τ' : MulAut (Sec U Z) := s xτ
  have hmap : (L.subgroupOf X).map s = autSec L U Z :=
    B5.map_secHom_eq_autSec X hXU hXZ hLX
  have hτ' : τ' ∈ normalizer (autSec L U Z : Set (MulAut (Sec U Z))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l'
    constructor
    · intro hl'
      exact s16h_e3_l3_conj_secHom_mem (x := xτ) hLX hXU hXZ hXN hmap l' hl'
    · intro hl'
      have hback := s16h_e3_l3_conj_secHom_mem (x := xτ⁻¹) hLX hXU hXZ hXN hmap
        (τ' * l' * τ'⁻¹) hl'
      have hback' : (τ')⁻¹ * (τ' * l' * τ'⁻¹) * τ' ∈ autSec L U Z := by
        simpa using hback
      have h2 : (τ')⁻¹ * (τ' * l' * τ'⁻¹) * τ' = l' := by group
      rwa [h2] at hback'
  have hQ : ∀ q : Sec U Z, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H u =>
        change (QuotientGroup.mk' (Z.subgroupOf U) u) ^ 2 = 1
        rw [← map_pow (QuotientGroup.mk' (Z.subgroupOf U)) u 2]
        have h1 : u ^ 2 = 1 := Subtype.ext (by simpa using hW (u : W))
        rw [h1, map_one]
  have hPSL : IsPSL 3 2 1 ↥(autSec L U Z) :=
    IsPSL.of_mulEquiv (B5.secEquiv L hLU hLZ hfaith') (s16h_e3_l3_isPSL_of_isSLn hL3.1)
  obtain ⟨γ', hγ', hconj'⟩ :=
    s16h_e3_normalizer_inner_of_sumOfNat hQ hPSL hsum'' hτ'
  have hγ'map : γ' ∈ (L.subgroupOf X).map s := by rw [hmap]; exact hγ'
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hγ'map
  have hγL : (a : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp ha
  refine ⟨(a : MulAut W), hγL, fun l hl => ?_⟩
  let xl : ↥X := ⟨l, hLX hl⟩
  have hsl : s xl ∈ autSec L U Z := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨xl, hl, rfl⟩
  have hc := hconj' (s xl) hsl
  have hleft : s (xτ * xl * xτ⁻¹) = s (a * xl * a⁻¹) := by
    have e1 : s (xτ * xl * xτ⁻¹) = τ' * s xl * τ'⁻¹ := by
      change s (xτ * xl * xτ⁻¹) = s xτ * s xl * (s xτ)⁻¹
      simp only [map_mul, map_inv]
    have e2 : s (a * xl * a⁻¹) = γ' * s xl * γ'⁻¹ := by
      rw [← haeq]
      change s (a * xl * a⁻¹) = s a * s xl * (s a)⁻¹
      simp only [map_mul, map_inv]
    rw [e1, e2]; exact hc
  have haL : ((xτ * xl * xτ⁻¹ : ↥X) : MulAut W) ∈ L := by
    change τ * l * τ⁻¹ ∈ L
    exact conj_mem_of_mem_normalizer hτ hl
  have hbL : ((a * xl * a⁻¹ : ↥X) : MulAut W) ∈ L := by
    change (a : MulAut W) * l * (a : MulAut W)⁻¹ ∈ L
    exact L.mul_mem (L.mul_mem hγL hl) (L.inv_mem hγL)
  have heq := s16h_e3_l3_secHom_inj_on_L hLX hXU hXZ hfaith' haL hbL hleft
  simpa using heq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
