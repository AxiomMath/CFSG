module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Conj
public import CFSG.Quasithin.Vol2.GoldschmidtH11Emb
public import CFSG.Quasithin.Vol2.GoldschmidtH11TauL
public import CFSG.Quasithin.Vol2.GoldschmidtH11Vec

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

theorem exists_conj_UK (h : Nat.card F = 2 ^ (2 * a)) {A : Subgroup (MulAut (HV F a))}
    (hel : IsElemAbelian2 A) (hτ : tauAut a h ∈ A) :
    ∃ κ ∈ Lh a h, tauAut a h * κ = κ * tauAut a h ∧
      UType a h (conjSub κ⁻¹ A ⊓ Lh a h) ∧
      Tset a h (conjSub κ⁻¹ A ⊓ Lh a h) ⊆ ((Kf a : Subfield F) : Set F) := by
  classical
  let π' : SL(2, (Kf a : Subfield F)) →* MulAut (HV F a) := (actHom a h).comp (embK a)
  have hπ'inj : Function.Injective π' := (actHom_injective a h).comp embK_injective
  have hx_emb : ∀ x ∈ A ⊓ Lh a h, ∃ γ' : SL(2, (Kf a : Subfield F)), π' γ' = x := by
    intro x hx
    obtain ⟨γ, rfl⟩ := hx.2
    have hcomm : tauAut a h * actHom a h γ = actHom a h γ * tauAut a h := hel.1 _ hτ _ hx.1
    have hσγ : sgMap h γ = γ := by
      apply actHom_injective a h
      rw [← tau_conj_actHom h γ, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨γ', hγ'⟩ := exists_embK h γ hσγ
    exact ⟨γ', by simp [π', hγ']⟩
  let P₀ : Subgroup SL(2, (Kf a : Subfield F)) := (A ⊓ Lh a h).comap π'
  have hP₀p : IsPGroup 2 P₀ := fun x => ⟨1, by
    apply Subtype.ext
    apply hπ'inj
    have := hel.2 _ x.2.1
    simpa [pow_two] using this⟩
  obtain ⟨g', hg'⟩ := exists_conj_unitriangular P₀ hP₀p
  have hκL : actHom a h (embK a g') ∈ Lh a h := actHom_mem_Lh _
  have hκτ : tauAut a h * actHom a h (embK a g') = actHom a h (embK a g') * tauAut a h := by
    have := tau_actHom h (embK a g')
    rwa [sgMap_embK] at this
  have hkey : ∀ y ∈ conjSub (actHom a h (embK a g'))⁻¹ A ⊓ Lh a h,
      ∃ d : (Kf a : Subfield F), y = actHom a h (uSL (d : F)) := by
    intro y hy
    have hyA := mem_conjSub.mp hy.1
    have hx₀ : (actHom a h (embK a g'))⁻¹⁻¹ * y * (actHom a h (embK a g'))⁻¹ ∈ A ⊓ Lh a h :=
      ⟨hyA, (Lh a h).mul_mem ((Lh a h).mul_mem (by simpa using hκL) hy.2)
        ((Lh a h).inv_mem hκL)⟩
    obtain ⟨γ', hγ'⟩ := hx_emb _ hx₀
    obtain ⟨d, hd⟩ := hg' γ' (by show π' γ' ∈ A ⊓ Lh a h; rw [hγ']; exact hx₀)
    refine ⟨d, ?_⟩
    have e1 : y = π' g'⁻¹ * π' γ' * π' g' := by
      rw [hγ']
      simp only [π', MonoidHom.comp_apply, map_inv]
      group
    rw [e1, ← map_mul, ← map_mul, hd]
    simp [π', embK_uSL]
  refine ⟨actHom a h (embK a g'), hκL, hκτ, fun y hy => ?_, fun d₀ hd₀ => ?_⟩
  · obtain ⟨d, hd⟩ := hkey y hy
    exact ⟨(d : F), hd⟩
  · obtain ⟨d, hd⟩ := hkey _ hd₀
    have := uSL_injective ((actHom_injective a h) hd)
    rw [this]
    exact d.2

end CFSG.Quasithin.H11
