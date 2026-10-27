module

public import CFSG.Quasithin.EmptyFaithful.LRed5Pair
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecE9U
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple

variable {V : Type} [CommGroup V] [Finite V]

theorem faithful_of_natural {L : Subgroup (MulAut V)} {W C : Subgroup V} (hsimp : IsSimpleGroup ↥L)
    (hinvW : ∀ l ∈ L, ∀ w ∈ W, l w ∈ W) (hfixC : ∀ l ∈ L, ∀ c ∈ C, l c = c)
    (hnat : BinaryNaturalSL L (modComm L W ⊔ C) C 3 1) :
    ∀ g ∈ L, (∀ w ∈ W, g w * w⁻¹ ∈ C) → g = 1 := by
  let N : Subgroup ↥L :=
    { carrier := {g | ∀ w ∈ W, (g : MulAut V) w * w⁻¹ ∈ C}
      one_mem' := fun w _ => by simp
      mul_mem' := by
        intro g h hg hh w hw
        have hhw : (h : MulAut V) w ∈ W := hinvW _ h.2 w hw
        have e : ((g * h : ↥L) : MulAut V) w * w⁻¹ =
            ((g : MulAut V) ((h : MulAut V) w) * ((h : MulAut V) w)⁻¹) *
              ((h : MulAut V) w * w⁻¹) := by
          simp only [Subgroup.coe_mul, MulAut.mul_apply]
          group
        rw [e]
        exact C.mul_mem (hg _ hhw) (hh w hw)
      inv_mem' := by
        intro g hg w hw
        have hgw : (g⁻¹ : ↥L) • w ∈ W := hinvW _ (g⁻¹).2 w hw
        have h1 := hg _ hgw
        have e : (g : MulAut V) (((g⁻¹ : ↥L) : MulAut V) w) = w := by
          simp
        have e2 : ((g⁻¹ : ↥L) : MulAut V) w * w⁻¹ =
            ((g : MulAut V) (((g⁻¹ : ↥L) : MulAut V) w) * (((g⁻¹ : ↥L) : MulAut V) w)⁻¹)⁻¹ := by
          rw [e, mul_inv_rev, inv_inv]
        rw [e2]
        exact C.inv_mem h1 }
  have hNn : N.Normal := by
    constructor
    intro g hg k w hw
    have hkw : ((k⁻¹ : ↥L) : MulAut V) w ∈ W := hinvW _ (k⁻¹).2 w hw
    have h1 := hg _ hkw
    have h2 := hfixC _ k.2 _ h1
    have e : ((k * g * k⁻¹ : ↥L) : MulAut V) w * w⁻¹ =
        (k : MulAut V) ((g : MulAut V) (((k⁻¹ : ↥L) : MulAut V) w) *
          (((k⁻¹ : ↥L) : MulAut V) w)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, map_mul, map_inv,
        MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rw [e, h2]
    exact h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  · intro g hg hgW
    have : (⟨g, hg⟩ : ↥L) ∈ N := hgW
    rw [hN, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    have hle : modComm L W ≤ C := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, w, hw, rfl⟩
      have : g ∈ N := hN ▸ Subgroup.mem_top g
      exact this w hw
    obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
    have h := G64.RealizesVia.card_eq hπ
    rw [sup_eq_right.mpr hle, G64.card_natMod, hK] at h
    have hpos : 0 < Nat.card ↥C := Nat.card_pos
    simp at h
    omega

theorem mem_commV_sup_of_piece (hB48 : AsB4_8Three) (hV2 : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} {W W' C : Subgroup V} (hsimp : IsSimpleGroup ↥L)
    (hP : B56Piece L W C) (hCW : C ≤ W) (hWW' : W ⊔ W' = ⊤) (hinf : W ⊓ W' = C)
    (hinvW : ∀ l ∈ L, ∀ w ∈ W, l w ∈ W) (hinvW' : ∀ l ∈ L, ∀ w ∈ W', l w ∈ W')
    (hfixC : ∀ l ∈ L, ∀ c ∈ C, l c = c) {a : MulAut V} (ha : a ∈ L) (ha2 : orderOf a = 2)
    {w : V} (hw : w ∈ W) (haw : a w * w⁻¹ ∈ C) : w ∈ commV L ⊔ C := by
  rcases hP with ⟨hWeq, -⟩ | ⟨hWeq, -⟩ | ⟨⟨e⟩, hcW, hcard, hind, hnat⟩
  · exact hWeq ▸ hw
  · exact hWeq ▸ hw
  · have h := hB48 V hV2 L W C ⟨e⟩ hCW (fun l x hx => hinvW l l.2 x hx)
      (fun l c hc => by
        show (l : MulAut V) c ∈ C
        rw [hfixC l l.2 c hc]
        exact hc)
      (faithful_of_natural hsimp hinvW hfixC hnat) hcard hind hnat a ha ha2 w hw haw
    rwa [LRed5.modComm_sup_eq hcW hWW' hinf hinvW'] at h

omit [Finite V] in
theorem card_commV_sup_of_piece {L : Subgroup (MulAut V)} {W W' C : Subgroup V}
    (hc : Nat.card ↥L = 168) (hP : B56Piece L W C) (hWW' : W ⊔ W' = ⊤) (hinf : W ⊓ W' = C)
    (hinvW' : ∀ l ∈ L, ∀ w ∈ W', l w ∈ W') :
    Nat.card ↥(commV L ⊔ C) = 8 * Nat.card ↥C ∨
      (W = commV L ⊔ C ∧
        DirectSumOfCopies L W C
          (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) 2) := by
  rcases hP with ⟨hWeq, h2 | h5 | ⟨m, K, _, _, hK, π, hπ⟩⟩ | ⟨hWeq, m, K, _, _, hK, hDS⟩ |
    ⟨-, hcW, -, -, hnat⟩
  · exfalso
    obtain ⟨n, K, _, _, hK, π, hπ⟩ := h2
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hK] at h1
    exact LRed5.sl2_ne (FFL.one_le_of_card hK) (Or.inl hc) h1.symm
  · exfalso
    obtain ⟨π, hπ⟩ := h5
    have h1 := FFL.card_eq_of_realizesVia (G64.symDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card (Equiv.Perm (Fin 5)) at h1
    rw [LRed4.card_perm_fin] at h1
    norm_num [Nat.factorial] at h1
    omega
  · left
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hK] at h1
    rcases LRed5.sl3_cases (FFL.one_le_of_card hK) with hm | hm
    · subst hm
      rw [← hWeq]
      have h := G64.RealizesVia.card_eq hπ
      rw [G64.card_natMod, hK] at h
      simpa using h
    · omega
  · right
    obtain ⟨Ic, π, hZI, hind, hsup, hreal⟩ := hDS
    have h1 := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hK] at h1
    rcases LRed5.sl3_cases (FFL.one_le_of_card hK) with hm | hm
    · subst hm
      exact ⟨hWeq, FFC.DirectSumOfCopies.zmod (K := K) (by rw [hK]; norm_num)
        ⟨Ic, π, hZI, hind, hsup, hreal⟩⟩
    · omega
  · left
    rw [← LRed5.modComm_sup_eq hcW hWW' hinf hinvW']
    obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
    have h := G64.RealizesVia.card_eq hπ
    rw [G64.card_natMod, hK] at h
    simpa using h

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
