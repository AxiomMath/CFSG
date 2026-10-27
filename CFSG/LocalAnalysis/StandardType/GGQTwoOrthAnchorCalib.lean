module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount

public section

namespace CFSG.StandardType.OrthAnchor

open Multiplicative

theorem isSignedPerm_of_conj_generators {m : ℕ} (hm : 3 ≤ m)
    {T : MulAut (Fin m → Multiplicative (ZMod 3))}
    (hs : ∀ i, SpCoord.IsSignedPerm
      ⇑(T⁻¹ * (SpCoord.sgnAut i : MulAut (Fin m → Multiplicative (ZMod 3))) * T))
    (ht : ∀ a b : Fin m, a ≠ b → SpCoord.IsSignedPerm
      ⇑(T⁻¹ * (SpCoord.permAut (Equiv.swap a b) : MulAut (Fin m → Multiplicative (ZMod 3))) * T)) :
    SpCoord.IsSignedPerm ⇑T := by
  classical
  let W : Subgroup (MulAut (Fin m → Multiplicative (ZMod 3))) :=
    SignedPermCount.signedPermSubgroup 3 m
  have hWmem : ∀ u : MulAut (Fin m → Multiplicative (ZMod 3)),
      u ∈ W ↔ SpCoord.IsSignedPerm ⇑u := fun _ => Iff.rfl
  have hcomap : ∀ u : MulAut (Fin m → Multiplicative (ZMod 3)),
      u ∈ W.comap (MulAut.conj T⁻¹).toMonoidHom ↔
        SpCoord.IsSignedPerm ⇑(T⁻¹ * u * T) := by
    intro u
    rw [Subgroup.mem_comap, hWmem]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hsH : ∀ i, SpCoord.sgnAut i ∈ W.comap (MulAut.conj T⁻¹).toMonoidHom :=
    fun i => (hcomap _).mpr (hs i)
  have htH : ∀ a b : Fin m, a ≠ b →
      SpCoord.permAut (Equiv.swap a b) ∈ W.comap (MulAut.conj T⁻¹).toMonoidHom :=
    fun a b hab => (hcomap _).mpr (ht a b hab)
  have hstep : ∀ u : MulAut (Fin m → Multiplicative (ZMod 3)),
      SpCoord.IsSignedPerm ⇑u → SpCoord.IsSignedPerm ⇑(T⁻¹ * u * T) := by
    intro u hu
    exact (hcomap u).mp (SpCoord.mem_of_isSignedPerm hsH htH hu)
  have hmap : W.map (MulAut.conj T⁻¹).toMonoidHom ≤ W := by
    intro u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact (hWmem _).mpr (by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hstep v hv)
  have hcard : Nat.card W ≤ Nat.card (W.map (MulAut.conj T⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj T⁻¹).toMonoidHom)
      (MulAut.conj T⁻¹).injective]
  have hWeq : W.map (MulAut.conj T⁻¹).toMonoidHom = W :=
    Subgroup.eq_of_le_of_card_ge hmap hcard
  have hconjT : ∀ u : MulAut (Fin m → Multiplicative (ZMod 3)),
      SpCoord.IsSignedPerm ⇑u → SpCoord.IsSignedPerm ⇑(T * u * T⁻¹) := by
    intro u hu
    have h1 : u ∈ W.map (MulAut.conj T⁻¹).toMonoidHom := by
      rw [hWeq]
      exact hu
    have h2 : (MulAut.conj T⁻¹).symm u ∈ W :=
      (Subgroup.mem_map_equiv (f := MulAut.conj T⁻¹) (K := W) (x := u)).mp h1
    have h3 : SpCoord.IsSignedPerm ⇑((MulAut.conj T⁻¹).symm u) := (hWmem _).mp h2
    simpa only [MulAut.conj_symm_apply, inv_inv] using h3
  obtain ⟨w, hw, c, hc⟩ :=
    SpCoord.exists_isSignedPerm_pow (p := 3) (k := m) Nat.prime_three (by norm_num) hm
      hconjT hstep
  obtain ⟨π, ε, hε, hw'⟩ := hw
  have hthree : ∀ x : Fin m → Multiplicative (ZMod 3), x ^ 3 = 1 := by
    intro x
    funext j
    apply toAdd.injective
    rw [SpCoord.toAdd_pow_apply, Pi.one_apply, toAdd_one]
    rw [ZMod.natCast_self, zero_mul]
  have hc3 : ¬ 3 ∣ c := by
    intro hdiv
    obtain ⟨k, rfl⟩ := hdiv
    let i₀ : Fin m := ⟨0, by omega⟩
    have hne : (Pi.mulSingle i₀ (ofAdd (1 : ZMod 3)) : Fin m → Multiplicative (ZMod 3)) ≠ 1 := by
      intro h
      have h0 := congrArg (fun f => toAdd (f i₀)) h
      rw [SpCoord.toAdd_mulSingle, Pi.one_apply, toAdd_one] at h0
      norm_num at h0
    have hpow : ∀ f : Fin m → Multiplicative (ZMod 3), (w f) ^ (3 * k) = 1 := by
      intro f
      rw [pow_mul, hthree, one_pow]
    have hT1 : T (Pi.mulSingle i₀ (ofAdd (1 : ZMod 3))) = 1 := by
      rw [hc, hpow]
    have hTone : T (1 : Fin m → Multiplicative (ZMod 3)) = 1 := by
      rw [hc, hpow]
    exact hne (T.injective (hT1.trans hTone.symm))
  have hcsign : (c : ZMod 3) = 1 ∨ (c : ZMod 3) = -1 := by
    have hmod : c % 3 ≠ 0 := fun h => hc3 (Nat.dvd_of_mod_eq_zero h)
    have hlt : c % 3 < 3 := Nat.mod_lt c (by norm_num)
    have hcases : c % 3 = 1 ∨ c % 3 = 2 := by omega
    have hcv : ((c : ZMod 3).val) = c % 3 := ZMod.val_natCast 3 c
    have h1 : ((c % 3 : ℕ) : ZMod 3) = (c : ZMod 3) := by
      rw [← hcv]
      exact ZMod.natCast_zmod_val _
    rcases hcases with h | h
    · left
      rw [← h1, h]
      decide
    · right
      rw [← h1, h]
      decide
  refine ⟨π, fun i => (c : ZMod 3) * ε i, ?_, ?_⟩
  · intro i
    change (c : ZMod 3) * ε i = 1 ∨ (c : ZMod 3) * ε i = -1
    rcases hcsign with hc1 | hc1 <;> rcases hε i with he | he
    · left; rw [hc1, he]; decide
    · right; rw [hc1, he]; decide
    · right; rw [hc1, he]; decide
    · left; rw [hc1, he]; decide
  · intro f i
    rw [hc f]
    rw [SpCoord.toAdd_pow_apply, hw' f i, mul_assoc]

end CFSG.StandardType.OrthAnchor

end
