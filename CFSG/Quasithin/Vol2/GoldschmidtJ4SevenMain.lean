module

public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenFixed
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenReal
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenFix
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenDef

public section

namespace CFSG.Quasithin.H13

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 CFSG.Quasithin.J4Seven Subgroup

theorem notReal_J
    {y : J} (hy : orderOf y = 7)
    (g : J) : g * y * g⁻¹ ≠ y⁻¹ := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have h49 : ¬ 49 ∣ Nat.card J := by rw [card_J hF]; decide
  have hx7 : orderOf sevenElt = 7 := orderOf_sevenElt hM
  have hH : ∀ y g : J, y • w₀ = w₀ → g • w₀ = w₀ → orderOf y = 7 → g * y * g⁻¹ ≠ y⁻¹ :=
    fun y g hy hg hord =>
      Hj_not_real hM h49 (mem_Hj_of_smul_root hF hy) (mem_Hj_of_smul_root hF hg) hord
  obtain ⟨k, -, hk⟩ := Seven.exists_conj_of_card_seven h49 (M := ⊤) (S := zpowers sevenElt)
    (S' := zpowers y) le_top le_top (by rw [Nat.card_zpowers, hx7])
    (by rw [Nat.card_zpowers, hy])
  obtain ⟨z, hzdef⟩ : ∃ z : J, z = k * y * k⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ zpowers sevenElt := by rw [hzdef]; exact hk y (mem_zpowers y)
  intro hg
  have hz7 : orderOf z = 7 := by
    have := MulEquiv.orderOf_eq (MulAut.conj k) y
    rw [MulAut.conj_apply, ← hzdef, hy] at this
    exact this
  have hinvz : (k * g * k⁻¹) * z * (k * g * k⁻¹)⁻¹ = z⁻¹ := by
    calc (k * g * k⁻¹) * z * (k * g * k⁻¹)⁻¹ = k * (g * y * g⁻¹) * k⁻¹ := by rw [hzdef]; group
      _ = k * y⁻¹ * k⁻¹ := by rw [hg]
      _ = z⁻¹ := by rw [hzdef]; group
  have hzz : zpowers z = zpowers sevenElt :=
    eq_of_le_of_card_ge (zpowers_le.2 hz) (by rw [Nat.card_zpowers, Nat.card_zpowers, hx7, hz7])
  have hfix : ∀ p : Row, z • p = p ↔ sevenElt • p = p := by
    intro p
    rw [← MulAction.mem_stabilizer_iff (G := J), ← MulAction.mem_stabilizer_iff (G := J),
      ← zpowers_le, ← zpowers_le (g := sevenElt), hzz]
  have hset : {p : Row | (∃ j : J, j • w₀ = p) ∧ z • p = p} =
      {p : Row | (∃ j : J, j • w₀ = p) ∧ sevenElt • p = p} := by
    ext p
    exact and_congr_right fun _ => hfix p
  have hfin : {p : Row | (∃ j : J, j • w₀ = p) ∧ z • p = p}.Finite := by
    rw [hset]
    exact finite_fixed hF
  have hodd : Odd {p : Row | (∃ j : J, j • w₀ = p) ∧ z • p = p}.ncard := by
    rw [hset, ncard_fixed hF]
    exact ⟨2, rfl⟩
  exact Seven.not_real_of_odd_fixed w₀ hH hz7 hfin hodd (k * g * k⁻¹) hinvz

theorem j4SevenNotReal_holds :
    J4SevenNotReal := by
  intro X _ _ hX x g hx hg
  obtain ⟨e⟩ := hX
  have hF : J4Facts := j4Facts
  let φ : X ≃* J := e.trans (seedEquiv hF.mat)
  refine notReal_J (y := φ x) (by rw [MulEquiv.orderOf_eq]; exact hx) (φ g) ?_
  have h := congrArg φ hg
  simpa [map_mul, map_inv] using h

end CFSG.Quasithin.H13
