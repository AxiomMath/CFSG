module

public import CFSG.Quasithin.Background.C116Two.NatLin2Defs

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

theorem charP_two_of_card {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) : CharP F 2 := by
  obtain ⟨p, hc⟩ := CharP.exists F
  obtain ⟨m, hp, hm⟩ := FiniteField.card F p
  have hdvd : p ∣ 2 ^ n := by
    rw [← hcard, hm]
    exact dvd_pow_self p (PNat.ne_zero m)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hc

theorem addMap_zero_aut {N : Type} [AddCommGroup N] (g : MulAut (Multiplicative N)) :
    addMap g 0 = 0 := by
  simp [addMap]

theorem addMap_injective_aut {N : Type} [AddCommGroup N] (g : MulAut (Multiplicative N)) :
    Function.Injective (addMap g) := by
  intro x y h
  have h' : g (Multiplicative.ofAdd x) = g (Multiplicative.ofAdd y) :=
    Multiplicative.toAdd.injective h
  exact Multiplicative.ofAdd.injective (MulEquiv.injective g h')

theorem semilinear_unique {F : Type} [Field F] {σ τ : F ≃+* F}
    {g : MulAut (Multiplicative (Fin 2 → F))} (hσ : IsSemilinear σ g) (hτ : IsSemilinear τ g) :
    σ = τ := by
  have hne : (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hy : addMap g (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
    intro h0
    apply hne
    apply addMap_injective_aut g
    rw [h0, addMap_zero_aut]
  ext c
  have h1 := hσ c (Pi.single 0 1 : Fin 2 → F)
  have h2 := hτ c (Pi.single 0 1 : Fin 2 → F)
  have h3 : (σ c - τ c) • addMap g (Pi.single 0 1 : Fin 2 → F) = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hy

theorem isSemilinear_one {F : Type} [Field F] :
    IsSemilinear (RingEquiv.refl F) (1 : MulAut (Multiplicative (Fin 2 → F))) := by
  intro c x
  simp only [addMap_one, RingEquiv.refl_apply]

theorem isSemilinear_mul {F : Type} [Field F] {σ τ : F ≃+* F}
    {g h : MulAut (Multiplicative (Fin 2 → F))} (hg : IsSemilinear σ g) (hh : IsSemilinear τ h) :
    IsSemilinear (τ.trans σ) (g * h) := by
  intro c x
  rw [addMap_mul, addMap_mul, hh c x, hg (τ c) (addMap h x), RingEquiv.trans_apply]

theorem isSemilinear_inv {F : Type} [Field F] {σ : F ≃+* F}
    {g : MulAut (Multiplicative (Fin 2 → F))} (hg : IsSemilinear σ g) :
    IsSemilinear σ.symm g⁻¹ := by
  intro c x
  have hx : ∀ y : Fin 2 → F, addMap g (addMap g⁻¹ y) = y := by
    intro y
    rw [← addMap_mul, mul_inv_cancel, addMap_one]
  have key : c • x = addMap g (σ.symm c • addMap g⁻¹ x) := by
    rw [hg (σ.symm c) (addMap g⁻¹ x), RingEquiv.apply_symm_apply, hx]
  calc addMap g⁻¹ (c • x) = addMap g⁻¹ (addMap g (σ.symm c • addMap g⁻¹ x)) := by rw [← key]
    _ = addMap (g⁻¹ * g) (σ.symm c • addMap g⁻¹ x) := by rw [addMap_mul]
    _ = σ.symm c • addMap g⁻¹ x := by rw [inv_mul_cancel, addMap_one]

theorem card_involutions_le_two (F : Type) [Field F] [Finite F] :
    Nat.card {σ : F ≃+* F // ∀ c, σ (σ c) = c} ≤ 2 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hc⟩ := CharP.exists F
  obtain ⟨m, hp, -⟩ := FiniteField.card F p
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let toAlg : (F ≃+* F) → (F ≃ₐ[ZMod p] F) := fun σ =>
    AlgEquiv.ofRingEquiv (f := σ)
      (fun x => RingHom.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) F))
        (algebraMap (ZMod p) F)) x)
  have hinv : ∀ σ : F ≃+* F, (∀ c, σ (σ c) = c) → toAlg σ ^ 2 = 1 := by
    intro σ hσ
    apply AlgEquiv.ext
    intro x
    rw [sq, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact hσ x
  have hinj : Function.Injective toAlg := by
    intro σ τ h
    apply RingEquiv.ext
    intro x
    exact congrArg (fun e : F ≃ₐ[ZMod p] F => e x) h
  have hfin : Finite (F ≃ₐ[ZMod p] F) :=
    Finite.of_injective (fun e : F ≃ₐ[ZMod p] F => (e : F → F))
      (fun a b h => AlgEquiv.ext (fun x => congrFun h x))
  letI : Fintype (F ≃ₐ[ZMod p] F) := Fintype.ofFinite _
  let φ : {σ : F ≃+* F // ∀ c, σ (σ c) = c} → {τ : F ≃ₐ[ZMod p] F // τ ^ 2 = 1} :=
    fun σ => ⟨toAlg σ.1, hinv σ.1 σ.2⟩
  have hφ : Function.Injective φ := by
    intro σ τ h
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val h
  calc Nat.card {σ : F ≃+* F // ∀ c, σ (σ c) = c}
      ≤ Nat.card {τ : F ≃ₐ[ZMod p] F // τ ^ 2 = 1} := Nat.card_le_card_of_injective φ hφ
    _ = (Finset.univ.filter fun τ : F ≃ₐ[ZMod p] F => τ ^ 2 = 1).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 2 := IsCyclic.card_pow_eq_one_le two_pos

end CFSG.Quasithin.C116Two
