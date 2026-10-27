module

public import CFSG.Quasithin.AppendixH.H9.ConjTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem mQuot_conjAut {W : Type*} [CommGroup W] (g : MulAut W)
    (P X : Subgroup (MulAut W)) :
    E3.mQuot (conjAut g P) (conjAut g X) = E3.mQuot P X := by
  unfold E3.mQuot conjAut
  rw [Subgroup.relIndex_map_map_of_injective X P (MulAut.conj g).injective]

private theorem mem_centSub_zpowers_iff_apply {W : Type*} [CommGroup W] {x : MulAut W} {w : W} :
    x ∈ centSub (Subgroup.zpowers w) ↔ x w = w := by
  rw [mem_centSub]
  constructor
  · intro h
    exact h w (Subgroup.mem_zpowers w)
  · intro h u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, h]

theorem gammaCheck_conjAut {W : Type*} [CommGroup W] (k : ℕ) (g : MulAut W)
    (P : Subgroup (MulAut W)) :
    E3.gammaCheck k (conjAut g P) = (E3.gammaCheck k P).map (g : MulAut W).toMonoidHom := by
  unfold E3.gammaCheck
  apply le_antisymm
  · refine iSup_le fun X => iSup₂_le fun hX hk => ?_
    have hXX' : conjAut g (conjAut g⁻¹ X) = X := by
      rw [← conjAut_mul, mul_inv_cancel, conjAut_one]
    have hX'P : conjAut g⁻¹ X ≤ P := by
      have h := conjAut_mono g⁻¹ hX
      rwa [← conjAut_mul, inv_mul_cancel, conjAut_one] at h
    have hk' : E3.mQuot P (conjAut g⁻¹ X) ≤ k := by
      rw [← mQuot_conjAut g P (conjAut g⁻¹ X), hXX']
      exact hk
    have h1 : fixV (conjAut g⁻¹ X) ≤
        ⨆ (X : Subgroup (MulAut W)) (_ : X ≤ P) (_ : E3.mQuot P X ≤ k), fixV X :=
      le_iSup_of_le (conjAut g⁻¹ X) (le_iSup₂_of_le hX'P hk' le_rfl)
    calc fixV X = fixV (conjAut g (conjAut g⁻¹ X)) := by rw [hXX']
      _ = (fixV (conjAut g⁻¹ X)).map (g : MulAut W).toMonoidHom := fixV_map_conj_eq (conjAut g⁻¹ X) g
      _ ≤ _ := Subgroup.map_mono h1
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun X => iSup₂_le fun hX hk => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← fixV_map_conj_eq]
    exact le_iSup_of_le (conjAut g X) (le_iSup₂_of_le (conjAut_mono g hX)
      (by rw [mQuot_conjAut]; exact hk) le_rfl)

theorem gammaCheck_eq_closure_stab {W : Type*} [CommGroup W] [Finite W] (k : ℕ)
    (P : Subgroup (MulAut W)) :
    E3.gammaCheck k P =
      Subgroup.closure {w : W | E3.mQuot P (P ⊓ centSub (Subgroup.zpowers w)) ≤ k} := by
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  unfold E3.gammaCheck
  apply le_antisymm
  · refine iSup_le fun X => iSup₂_le fun hX hk w hw => ?_
    refine Subgroup.subset_closure ?_
    have hXle : X ≤ P ⊓ centSub (Subgroup.zpowers w) :=
      le_inf hX fun x hx => mem_centSub_zpowers_iff_apply.2 (hw x hx)
    exact (E3.mQuot_mono hXle).trans hk
  · rw [Subgroup.closure_le]
    intro w hw
    have h1 : w ∈ fixV (P ⊓ centSub (Subgroup.zpowers w)) := fun x hx =>
      mem_centSub_zpowers_iff_apply.1 (Subgroup.mem_inf.1 hx).2
    have h2 : fixV (P ⊓ centSub (Subgroup.zpowers w)) ≤
        ⨆ (X : Subgroup (MulAut W)) (_ : X ≤ P) (_ : E3.mQuot P X ≤ k), fixV X :=
      le_iSup_of_le (P ⊓ centSub (Subgroup.zpowers w)) (le_iSup₂_of_le inf_le_left hw le_rfl)
    exact h2 h1

theorem mem_fixV_zpowers {W : Type*} [CommGroup W] (g : MulAut W) (w : W) :
    w ∈ fixV (Subgroup.zpowers g) ↔ g w = w := by
  constructor
  · intro h
    exact h g (Subgroup.mem_zpowers g)
  · intro h x hx
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut W) w := by
      rw [Subgroup.zpowers_le]
      exact h
    exact hle hx

theorem mem_fixV_range {W : Type*} [CommGroup W] {d : ℕ}
    (ρ : Multiplicative (Fin d → ZMod 2) →* MulAut W) (w : W) :
    w ∈ fixV ρ.range ↔ ∀ ε : Fin d → ZMod 2, ρ (Multiplicative.ofAdd ε) w = w := by
  rw [mem_fixV]
  constructor
  · intro h ε
    exact h _ ⟨Multiplicative.ofAdd ε, rfl⟩
  · rintro h x ⟨e, rfl⟩
    exact h (Multiplicative.toAdd e)

theorem gammaCheck_two_range {W : Type*} [CommGroup W] [Finite W]
    (ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut W) (hρ : Function.Injective ρ) :
    E3.gammaCheck 2 ρ.range =
      Subgroup.closure
        {w : W | 4 ≤ Nat.card {ε : Fin 4 → ZMod 2 // ρ (Multiplicative.ofAdd ε) w = w}} := by
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  rw [gammaCheck_eq_closure_stab]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq]
  have hcardP : Nat.card ρ.range = 2 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
    show Nat.card (Fin 4 → ZMod 2) = 2 ^ 4
    simp [Nat.card_fun]
  have hP : IsPGroup 2 ρ.range := IsPGroup.of_card hcardP
  have hcardS : Nat.card ↥(ρ.range ⊓ centSub (Subgroup.zpowers w)) =
      Nat.card {ε : Fin 4 → ZMod 2 // ρ (Multiplicative.ofAdd ε) w = w} := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun ε => ⟨ρ (Multiplicative.ofAdd ε.1),
        Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, mem_centSub_zpowers_iff_apply.2 ε.2⟩⟩) ⟨?_, ?_⟩)
    · intro ε₁ ε₂ h
      apply Subtype.ext
      exact hρ (congrArg Subtype.val h)
    · rintro ⟨x, hxP, hxc⟩
      obtain ⟨e, rfl⟩ := hxP
      exact ⟨⟨Multiplicative.toAdd e, mem_centSub_zpowers_iff_apply.1 hxc⟩, rfl⟩
  have h := E3.card_eq_two_pow_mul hP
    (inf_le_left : ρ.range ⊓ centSub (Subgroup.zpowers w) ≤ ρ.range)
  rw [hcardP, hcardS] at h
  generalize E3.mQuot ρ.range (ρ.range ⊓ centSub (Subgroup.zpowers w)) = m at h ⊢
  generalize Nat.card {ε : Fin 4 → ZMod 2 // ρ (Multiplicative.ofAdd ε) w = w} = s at h ⊢
  constructor
  · intro hm
    have h2 : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm
    by_contra hs
    have : 2 ^ m * s ≤ 2 ^ 2 * 3 := Nat.mul_le_mul h2 (by omega)
    omega
  · intro hs
    by_contra hm
    have h2 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 3 * 4 ≤ 2 ^ m * s := Nat.mul_le_mul h2 hs
    omega

end CFSG.ASVolI.ChH
