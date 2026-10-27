module

public import CFSG.Quasithin.Background.B45L32Pair
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4B
import CFSG.Quasithin.Background.F918J3
import CFSG.Quasithin.Background.F918Z6Aux
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4FAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.QuasithinUnique.Setup.Family CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem isIrrOn_autSub_sup {X X' : Subgroup (MulAut W)} {U : Subgroup W}
    (hirr : IsIrrOn (X ⊔ X') U ⊥) :
    ∀ J : Subgroup ↥U,
      (∀ g ∈ autSub X U ⊔ autSub X' U, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤ := by
  intro J hJ
  have hXU : X ≤ stabSub U :=
    f4f_le_stabSub fun x hx => hirr.2.1 x (Subgroup.mem_sup_left hx)
  have hX'U : X' ≤ stabSub U :=
    f4f_le_stabSub fun x hx => hirr.2.1 x (Subgroup.mem_sup_right hx)
  have hJ'X : StableUnder X (J.map U.subtype) := by
    intro x hx u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_map.mpr
      ⟨resHom U ⟨x, hXU hx⟩ v,
        hJ (resHom U ⟨x, hXU hx⟩)
          (Subgroup.mem_sup_left (mem_autSub.mpr ⟨⟨x, hXU hx⟩, hx, rfl⟩)) v hv,
        resHom_apply U ⟨x, hXU hx⟩ v⟩
  have hJ'X' : StableUnder X' (J.map U.subtype) := by
    intro x hx u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_map.mpr
      ⟨resHom U ⟨x, hX'U hx⟩ v,
        hJ (resHom U ⟨x, hX'U hx⟩)
          (Subgroup.mem_sup_right (mem_autSub.mpr ⟨⟨x, hX'U hx⟩, hx, rfl⟩)) v hv,
        resHom_apply U ⟨x, hX'U hx⟩ v⟩
  have hJ' : StableUnder (X ⊔ X') (J.map U.subtype) := f4f_stableUnder_sup hJ'X hJ'X'
  rcases hirr.2.2.2 (J.map U.subtype) hJ' bot_le (Subgroup.map_subtype_le J) with h | h
  · left
    refine Subgroup.map_injective U.subtype_injective ?_
    rw [h, Subgroup.map_bot]
  · right
    refine Subgroup.map_injective U.subtype_injective ?_
    rw [h, Subgroup.map_top, Subgroup.range_subtype]

omit [Finite W] in
theorem exists_pair_restrict_of_isIrrOn {X X' : Subgroup (MulAut W)}
    (hXX' : ∀ a ∈ X, ∀ b ∈ X', a * b = b * a) (hL3 : IsL3 ↥X 1) (hL3' : IsL3 ↥X' 1)
    {U : Subgroup W} (hirr : IsIrrOn (X ⊔ X') U ⊥)
    (hXnt : ¬ ∀ x ∈ X, ∀ u ∈ U, (x : MulAut W) u = u)
    (hX'nt : ¬ ∀ x ∈ X', ∀ u ∈ U, (x : MulAut W) u = u) :
    ∃ L₁ L₂ : Subgroup (MulAut ↥U), Nonempty (↥L₁ ≃* GL32) ∧ Nonempty (↥L₂ ≃* GL32) ∧
      (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∧
      ∀ J : Subgroup ↥U, (∀ g ∈ L₁ ⊔ L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤ := by
  have hXU : X ≤ stabSub U :=
    f4f_le_stabSub fun x hx => hirr.2.1 x (Subgroup.mem_sup_left hx)
  have hX'U : X' ≤ stabSub U :=
    f4f_le_stabSub fun x hx => hirr.2.1 x (Subgroup.mem_sup_right hx)
  have hXfaith : X ⊓ centSub U = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup (s134b_isSimpleGroup_of_isL3 hL3) hXU fun hle =>
      hXnt fun x hx u hu => (mem_centSub.mp (hle hx)) u hu
  have hX'faith : X' ⊓ centSub U = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup (s134b_isSimpleGroup_of_isL3 hL3') hX'U fun hle =>
      hX'nt fun x hx u hu => (mem_centSub.mp (hle hx)) u hu
  refine ⟨autSub X U, autSub X' U, ?_, ?_, autSub_commute hXX', isIrrOn_autSub_sup hirr⟩
  · obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL3
    exact ⟨(autSubEquivOfFaithful hXU hXfaith).symm.trans e⟩
  · obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL3'
    exact ⟨(autSubEquivOfFaithful hX'U hX'faith).symm.trans e⟩

theorem nine_le_rk_and_card_of_isIrrOn (hW : ∀ w : W, w ^ 2 = 1) {X X' : Subgroup (MulAut W)}
    (hXX' : ∀ a ∈ X, ∀ b ∈ X', a * b = b * a) (hL3 : IsL3 ↥X 1) (hL3' : IsL3 ↥X' 1)
    {U : Subgroup W} (hirr : IsIrrOn (X ⊔ X') U ⊥)
    (hXnt : ¬ ∀ x ∈ X, ∀ u ∈ U, (x : MulAut W) u = u)
    (hX'nt : ¬ ∀ x ∈ X', ∀ u ∈ U, (x : MulAut W) u = u) :
    9 ≤ rk ↥U ∧ (rk ↥U ≤ 16 → Nat.card ↥U = 2 ^ 9) := by
  obtain ⟨L₁, L₂, ⟨e₁⟩, ⟨e₂⟩, hcomm, hirrU⟩ :=
    exists_pair_restrict_of_isIrrOn hXX' hL3 hL3' hirr hXnt hX'nt
  have : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).2 hirr.1.ne'
  obtain ⟨n, hn, h9, h16⟩ := B45L32.exists_card_eq_two_pow_of_pair
    (fun u => Subtype.ext (by simpa using hW u)) e₁ e₂ hcomm hirrU
  have hrk : rk ↥U = n := by rw [rk, hn, padicValNat.prime_pow]
  refine ⟨hrk ▸ h9, fun h => ?_⟩
  rw [hn, h16 (hrk ▸ h)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
