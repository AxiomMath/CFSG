module

public import CFSG.Quasithin.Vol2.Ch11SecBK7I
public import CFSG.Quasithin.Vol2.Ch11SecBK7C
public import CFSG.Quasithin.Vol2.Ch11SecBK7D
public import CFSG.Quasithin.Vol2.Ch11SecBK7H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp)
open scoped IsMulCommutative

open K7 in
theorem factSp4Root_holds : FactSp4Root := by
  intro G _ _ L V X T V₁ V₂ n hfl hk W hW hmW hCW
  obtain ⟨_, K, _, _, _, hK, π, f, hf, g, -, -, hV₂⟩ := exists_coord_flag24 hfl hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWV : ∀ {w : G}, w ∈ W → w ∈ Subgroup.normalizer (V : Set G) := fun hw =>
    r2_le_normalizer hfl (hW hw)
  obtain ⟨v, ⟨hvV, hvW⟩, hvV₂⟩ := Set.not_subset.mp hCW
  set v' : ↥V := ⟨v, hvV⟩ with hv'
  set kv := mat 2 K g⁻¹ *ᵥ f v' with hkv
  have hkP : kv ∉ spPlane K := fun h => hvV₂ (by
    have : v' ∈ V₂.subgroupOf V := by
      rw [hV₂]
      exact mem_gmapSp.mpr h
    exact this)
  set y := mat 2 K g *ᵥ vec4 (kv (.inr 1)) (-kv (.inr 0)) 0 0 with hy
  have hy0 : y ≠ 0 := fun h => y₀_ne_zero hkP (by
    have := congrArg (fun x => mat 2 K g⁻¹ *ᵥ x) h
    simpa only [hy, mat_inv_mulVec, Matrix.mulVec_zero] using this)
  have hact : ∀ w (hw : w ∈ W), ∃ c : K,
      SecA.conjV V w (hWV hw) = ((π (trv y c) : ↥(autOn L V)) : MulAut ↥V) := by
    intro w hw
    obtain ⟨x₁, x₂, x₃, hq⟩ := exists_qSp_of_mem_r2 hfl hK hf hV₂ (hW hw)
    have hfix : mat 2 K (qSp x₁ x₂ x₃) *ᵥ kv = kv := by
      have h1 : SecA.conjV V w (hWV hw) v' = v' := Subtype.ext (by
        rw [SecA.conjV_apply_coe, hv', Subgroup.mem_centralizer_iff.mp hvW w hw,
          mul_inv_cancel_right])
      have h2 := congrArg f h1
      rw [hq, hf.act4, KA.gconj_mulVec_sp] at h2
      have h3 := congrArg (fun x => mat 2 K g⁻¹ *ᵥ x) h2
      simpa only [mat_inv_mulVec] using h3
    obtain ⟨c, hc⟩ := exists_trv_of_qSp_fix hkP hfix
    exact ⟨c, by rw [hq, hc, trv_conj]⟩
  choose c hc using hact
  have hWp : IsPGroup 2 W := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hW
  have hcard : Nat.card (autOn W V) = Nat.card K := by
    rw [card_autOn_eq_two_pow hWp (fun w hw => hWV hw) hmW, hK]
  have hψ : ∀ x : ↥(autOn W V), ∃ c' : K,
      ((π (trv y c') : ↥(autOn L V)) : MulAut ↥V) = x := by
    intro x
    obtain ⟨w, hwW, hwV, hx⟩ := SecA.mem_autOn_iff.mp x.2
    exact ⟨c w hwW, by rw [← hc w hwW, hx]⟩
  choose ψ hψ using hψ
  have hψinj : Function.Injective ψ := fun x x' h =>
    Subtype.ext (by rw [← hψ x, ← hψ x', h])
  have hψbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hψinj, hcard⟩
  have hall : ∀ c' : K, ∃ w, ∃ hw : w ∈ W,
      SecA.conjV V w (hWV hw) = ((π (trv y c') : ↥(autOn L V)) : MulAut ↥V) := by
    intro c'
    obtain ⟨x, hx⟩ := hψbij.2 c'
    obtain ⟨w, hwW, hwV, hxw⟩ := SecA.mem_autOn_iff.mp x.2
    exact ⟨w, hwW, by rw [← hx, hψ x]; exact hxw.symm⟩
  have hC : ∀ u : ↥V, (u : G) ∈ Subgroup.centralizer (W : Set G) ↔
      Matrix.toBilin' (spJ K) (f u) y = 0 := by
    intro u
    constructor
    · intro hu
      obtain ⟨w, hw, hw1⟩ := hall 1
      apply bil_eq_zero_of_trv_fix hf hy0 one_ne_zero
      rw [← hw1]
      exact Subtype.ext (by
        rw [SecA.conjV_apply_coe, Subgroup.mem_centralizer_iff.mp hu w hw, mul_inv_cancel_right])
    · intro hu
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := trv_fix hf fix_of_autOn hy0 (c w hw) hu
      rw [← hc w hw] at h1
      have h2 := congrArg Subtype.val h1
      rw [SecA.conjV_apply_coe] at h2
      calc w * u = w * u * w⁻¹ * w := by group
        _ = u * w := by rw [h2]
  refine ⟨mQuot_eq_of_iff hf hK hy0 hC, ?_⟩
  obtain ⟨l, hl0, hl1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hfl.two_le hK
  have hsq : ∀ u : ↥V, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hfl.elem.2 u u.2)
  refine le_commutator_of_le_acomm (le_acomm hf fix_of_autOn
    (commV_autOn_eq_top hfl.le_normalizer hfl.commutator_eq) hsq hl0 hl1 hy0) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨c', u, rfl⟩
  obtain ⟨w, hw, hw'⟩ := hall c'
  rw [← hw']
  exact conjV_comm_mem hw (hWV hw) u

end CFSG.Quasithin.Vol2.Ch11.SecB
