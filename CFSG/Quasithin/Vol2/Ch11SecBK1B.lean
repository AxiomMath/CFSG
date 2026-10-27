module

public import CFSG.Quasithin.Vol2.Ch11SecAKA2
public import CFSG.Quasithin.Vol2.Ch11SecAKA8

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem factParSp4_holds : FactParSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hfixV hcommV P hP U hU S hS2 hSH hSU _
  subst hfixV
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four
    (KGNat.four_le_card hn hK)
  have hpt := KGNat.factPointSp4_holds K n hn hK W hW H (fixV H) π hπ P hP U hU
  have ha : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u = u :=
    KGNat.fix_of_perfect (perfectCore_perfect _)
      (fun h hh z hz => mem_fixV.mp hz h (perfectCore_le _ hh).1) hpt
  refine ⟨ha, fun s hs hcomm u hu => ?_⟩
  have hs' : ∀ h ∈ H, s⁻¹ * h * s ∈ H := fun h hh => by
    have := hSH s⁻¹ (S.inv_mem hs) h hh
    rwa [inv_inv] at this
  have hs'' : ∀ h ∈ H, s⁻¹⁻¹ * h * s⁻¹ ∈ H := fun h hh => by
    rw [inv_inv]
    exact hSH s hs h hh
  have hτZ : s ∈ Ch11.SecA.stabW (fixV H) := by
    refine Ch11.SecA.mem_stabW.mpr fun z => ⟨fun hz => KGNat.maps_fixV hs' z hz, fun hz => ?_⟩
    have := KGNat.maps_fixV hs'' _ hz
    rwa [MulAut.inv_apply_self] at this
  have hτ2 : ∃ k : ℕ, s ^ 2 ^ k = 1 := by
    obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hτc : ∀ x : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
      ∃ y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
        y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) ∧
          s * (x : MulAut W) * s⁻¹ = (y : MulAut W) * x := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hcomm x x.2)
    refine ⟨y, by exact hy, ?_⟩
    have hyx' : (y : MulAut W) = s * x * s⁻¹ * (x : MulAut W)⁻¹ := hyx
    rw [hyx', inv_mul_cancel_right]
  have hfix := KGNat.factRadicalFixedSp4_holds K n hn hK W hW H (fixV H) π hπ P hP U hU
  obtain ⟨f, hf, g, -, hUeq⟩ := KGNat.KA.exists_point_coords hn hK hW hπ hP hU
  obtain ⟨N, hN, hact⟩ := KGNat.KA.exists_core hK4 hf g hUeq hfix hpt hτ2 hτZ (hSH s hs) hτc
  subst hUeq
  obtain ⟨y, -, hyN⟩ := KGNat.KA.exists_pCore_of_mem hf g hN
  have hyH : (y : MulAut W) ∈ H := (perfectCore_le _ y.2).1
  have hact' : ∀ w, f (s w) = f ((y : MulAut W) w) := fun w => by rw [hyN]; exact hact w
  obtain ⟨c, hc⟩ : ∃ c : MulAut W, c = (y : MulAut W)⁻¹ * s := ⟨_, rfl⟩
  have hcf : ∀ w, f (c w) = f w := fun w => by
    rw [hc, MulAut.mul_apply]
    refine KGNat.KA.act_cancel hf hyH ?_
    rw [MulAut.apply_inv_self, hact']
  have hcf' : ∀ w, f (c⁻¹ w) = f w := fun w => by
    have h1 := hcf (c⁻¹ w)
    rw [MulAut.apply_inv_self] at h1
    exact h1.symm
  have hcN : ∀ h ∈ H, c * h * c⁻¹ ∈ H := fun h hh => by
    rw [show c * h * c⁻¹ = (y : MulAut W)⁻¹ * (s * h * s⁻¹) * (y : MulAut W) by
      rw [hc]; group]
    exact H.mul_mem (H.mul_mem (H.inv_mem hyH) (hSH s hs h hh)) hyH
  have hcH : ∀ h ∈ H, c * h = h * c := by
    intro h hh
    have h1 : c * h * c⁻¹ = h := KGNat.KA.eq_of_forall_f_eq hf (hcN h hh) hh fun w => by
      rw [MulAut.mul_apply, MulAut.mul_apply, hcf]
      exact KGNat.KA.act_congr hf hh (hcf' w)
    calc c * h = c * h * c⁻¹ * c := by group
      _ = h * c := by rw [h1]
  have hc1 : c = 1 := KGNat.eq_one_of_commV hcommV hcH fun w =>
    (hf.ker _).mp (by rw [hf.map_mul_inv, hcf, sub_self])
  rw [hc] at hc1
  rw [← inv_mul_eq_one.mp hc1]
  exact ha _ y.2 u hu

end CFSG.Quasithin.Vol2.Ch11.SecB
