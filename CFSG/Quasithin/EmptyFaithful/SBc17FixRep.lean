module

public import CFSG.Quasithin.EmptyFaithful.SBc16FDec
import CFSG.Quasithin.EmptyFaithful.SBc16FCoord
import CFSG.Quasithin.EmptyFaithful.SBc16FCore
import CFSG.Quasithin.EmptyFaithful.SBc16FSyl

public section

namespace CFSG.Quasithin

open SBc16

namespace SBc17

theorem map_eq_self_iff_mem {V : Type} [Group V] [Finite V] {Q : Subgroup V} (hQ : Nat.card Q = 5)
    {z : V} (hz : z ∈ Q) (hz1 : z ≠ 1) (α : MulAut V) :
    Q.map α.toMonoidHom = Q ↔ α z ∈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := Subgroup.mem_map_of_mem α.toMonoidHom hz
    rwa [h] at this
  · have hz' : Subgroup.zpowers z = Q := zpowers_eq_of_mem_of_card_five hQ hz hz1
    have hle : Q.map α.toMonoidHom ≤ Q := by
      conv_lhs => rw [← hz']
      rw [MonoidHom.map_zpowers]
      exact (Subgroup.zpowers_le).mpr h
    exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).ge

theorem pow_five_eq_one_of_sup {V : Type} [CommGroup V] {V₁ V₂ : Subgroup V} (h1 : Nat.card V₁ = 5)
    (h2 : Nat.card V₂ = 5) (hsup : V₁ ⊔ V₂ = ⊤) (x : V) : x ^ 5 = 1 := by
  have hx : x ∈ V₁ ⊔ V₂ := by rw [hsup]; exact Subgroup.mem_top x
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
  have hy5 : y ^ 5 = 1 := by
    have := pow_card_eq_one' (G := V₁) (x := ⟨y, hy⟩)
    rw [h1] at this
    exact congrArg Subtype.val this
  have hz5 : z ^ 5 = 1 := by
    have := pow_card_eq_one' (G := V₂) (x := ⟨z, hz⟩)
    rw [h2] at this
    exact congrArg Subtype.val this
  rw [mul_pow, hy5, hz5, one_mul]

theorem exists_matrix_rep_lines (V : Type) [CommGroup V] [Finite V] (hV : Nat.card V = 25)
    (h5 : ∀ x : V, x ^ 5 = 1) (V₁ V₂ : Subgroup V) (h1 : Nat.card V₁ = 5) (h2 : Nat.card V₂ = 5)
    (hd : V₁ ⊓ V₂ = ⊥) :
    ∃ ρ : MulAut V →* GL (Fin 2) (ZMod 5), Function.Injective ρ ∧
      (∀ α : MulAut V, (ρ α : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0 ↔
        V₂.map α.toMonoidHom = V₂) ∧
      (∀ α : MulAut V, (ρ α : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0 ↔
        V₁.map α.toMonoidHom = V₁) ∧
      (∀ σ : MulAut V, (∀ x ∈ V₂, σ x = x) → (∀ x ∈ V₁, σ x = x⁻¹) →
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = -1 ∧
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0 ∧
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0 ∧
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 1) ∧
      (∀ τ : MulAut V, V₁.map τ.toMonoidHom = V₂ → V₂.map τ.toMonoidHom = V₁ →
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = 0 ∧
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 0 ∧
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 ≠ 0 ∧
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 ≠ 0) := by
  have hval1 : (1 : ZMod 5).val = 1 := by decide
  have hvalm1 : (-1 : ZMod 5).val = 4 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨v₁, hv₁, hne₁⟩ := exists_ne_one_of_card_five h1
  obtain ⟨v₂, hv₂, hne₂⟩ := exists_ne_one_of_card_five h2
  have ho₁ : orderOf v₁ = 5 := orderOf_eq_prime (h5 v₁) hne₁
  have ho₂ : orderOf v₂ = 5 := orderOf_eq_prime (h5 v₂) hne₂
  have hbij : Function.Bijective (coordHom h5 v₁ v₂) := coordHom_bijective hV hd hv₁ ho₁ hv₂ ho₂
  let eV : Z52 ≃* V := MulEquiv.ofBijective (coordHom h5 v₁ v₂) hbij
  have heV : ∀ w, eV w = coordHom h5 v₁ v₂ w := fun w => rfl
  let ρ : MulAut V →* GL (Fin 2) (ZMod 5) :=
    (matHom.comp (MulAut.congr eV.symm).toMonoidHom).toHomUnits
  have hmatent : ∀ (β : MulAut Z52) (i j : Fin 2), matOf β i j =
      Multiplicative.toAdd (β (Multiplicative.ofAdd (Pi.single j 1))) i := by
    intro β i j
    have h := congrFun (matOf_apply β (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h
    exact h.symm
  have hent : ∀ (α : MulAut V) (i j : Fin 2), (ρ α : Matrix (Fin 2) (Fin 2) (ZMod 5)) i j =
      Multiplicative.toAdd (eV.symm (α (eV (Multiplicative.ofAdd (Pi.single j 1))))) i :=
    fun α i j => hmatent _ i j
  have hρinj : Function.Injective ρ := by
    intro α α' h
    have h1 : matOf (MulAut.congr eV.symm α) = matOf (MulAut.congr eV.symm α') :=
      congrArg Units.val h
    exact (MulAut.congr eV.symm).injective (matOf_injective h1)
  have hb0 : eV (Multiplicative.ofAdd (Pi.single 0 1)) = v₁ := by
    rw [heV, coordHom_apply]
    simp [hval1]
  have hb1 : eV (Multiplicative.ofAdd (Pi.single 1 1)) = v₂ := by
    rw [heV, coordHom_apply]
    simp [hval1]
  have hinv0 : eV (Multiplicative.ofAdd (Pi.single 0 (-1))) = v₁⁻¹ := by
    rw [heV, coordHom_apply]
    have h4 : v₁ ^ 4 = v₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h5 v₁)
    simp [hvalm1, h4]
  have hcrd : ∀ x : V, coordHom h5 v₁ v₂ (eV.symm x) = x := fun x => by
    rw [← heV, MulEquiv.apply_symm_apply]
  have hne : ∀ x : V, x ≠ 1 → Multiplicative.toAdd (eV.symm x) 0 = 0 →
      Multiplicative.toAdd (eV.symm x) 1 = 0 → False := by
    intro x hx h0 h1'
    apply hx
    have : eV.symm x = 1 := by
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i
      · exact h0
      · exact h1'
    rw [MulEquiv.symm_apply_eq] at this
    rw [this, map_one]
  refine ⟨ρ, hρinj, ?_, ?_, ?_, ?_⟩
  · intro α
    rw [map_eq_self_iff_mem h2 hv₂ hne₂ α, hent, hb1]
    constructor
    · intro h0
      have h := hcrd (α v₂)
      rw [coordHom_apply, h0] at h
      rw [← h]
      simpa using Subgroup.pow_mem V₂ hv₂ (Multiplicative.toAdd (eV.symm (α v₂)) 1).val
    · intro hm
      exact fst_eq_zero_of_mem hd hv₁ ho₁ hv₂ (by rw [hcrd]; exact hm)
  · intro α
    rw [map_eq_self_iff_mem h1 hv₁ hne₁ α, hent, hb0]
    constructor
    · intro h0
      have h := hcrd (α v₁)
      rw [coordHom_apply, h0] at h
      rw [← h]
      simpa using Subgroup.pow_mem V₁ hv₁ (Multiplicative.toAdd (eV.symm (α v₁)) 0).val
    · intro hm
      exact snd_eq_zero_of_mem hd hv₁ hv₂ ho₂ (by rw [hcrd]; exact hm)
  · intro σ hσ2 hσ1
    have hc0 : eV.symm (σ v₁) = Multiplicative.ofAdd (Pi.single 0 (-1)) := by
      rw [hσ1 v₁ hv₁, MulEquiv.symm_apply_eq, hinv0]
    have hc1 : eV.symm (σ v₂) = Multiplicative.ofAdd (Pi.single 1 1) := by
      rw [hσ2 v₂ hv₂, MulEquiv.symm_apply_eq, hb1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hent, hb0, hc0]
      simp
    · rw [hent, hb1, hc1]
      simp
    · rw [hent, hb0, hc0]
      simp
    · rw [hent, hb1, hc1]
      simp
  · intro τ hτ1 hτ2
    have hτv₁ : τ v₁ ∈ V₂ := by
      rw [← hτ1]
      exact ⟨v₁, hv₁, rfl⟩
    have hτv₂ : τ v₂ ∈ V₁ := by
      rw [← hτ2]
      exact ⟨v₂, hv₂, rfl⟩
    have hτ₁0 : Multiplicative.toAdd (eV.symm (τ v₁)) 0 = 0 :=
      fst_eq_zero_of_mem hd hv₁ ho₁ hv₂ (by rw [hcrd]; exact hτv₁)
    have hτ₂1 : Multiplicative.toAdd (eV.symm (τ v₂)) 1 = 0 :=
      snd_eq_zero_of_mem hd hv₁ hv₂ ho₂ (by rw [hcrd]; exact hτv₂)
    have hτ₁1 : Multiplicative.toAdd (eV.symm (τ v₁)) 1 ≠ 0 := fun h =>
      hne _ (fun h' => hne₁ (τ.injective (h'.trans (map_one τ).symm))) hτ₁0 h
    have hτ₂0 : Multiplicative.toAdd (eV.symm (τ v₂)) 0 ≠ 0 := fun h =>
      hne _ (fun h' => hne₂ (τ.injective (h'.trans (map_one τ).symm))) h hτ₂1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hent, hb0]
      exact hτ₁0
    · rw [hent, hb1]
      exact hτ₂1
    · rw [hent, hb1]
      exact hτ₂0
    · rw [hent, hb0]
      exact hτ₁1

theorem commutator_decide : ∀ a d : ZMod 5, a * d ≠ 0 → ∀ c : ZMod 5, c ≠ 0 →
    ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 5),
      B * (!![-1, 0; 0, 1] * !![a, 0; c, d]) = !![a, 0; c, d] * !![-1, 0; 0, 1] →
      B ^ 5 = 1 ∧ B ≠ 1 := by
  decide +kernel

theorem orderOf_eq_five_of_mul_eq {S X B : GL25}
    (hs00 : (S : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = -1)
    (hs01 : (S : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0)
    (hs10 : (S : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0)
    (hs11 : (S : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 1)
    (hx01 : (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0)
    (hx10 : (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 ≠ 0) (hB : B * (S * X) = X * S) :
    orderOf B = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hBM : (B : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
      ((S : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (X : Matrix (Fin 2) (Fin 2) (ZMod 5))) =
      (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (S : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
    have := congrArg Units.val hB
    simpa only [Units.val_mul] using this
  have hS : (S : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![-1, 0; 0, 1] := by
    have h := Matrix.eta_fin_two (S : Matrix (Fin 2) (Fin 2) (ZMod 5))
    rwa [hs00, hs01, hs10, hs11] at h
  have hXM : (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![X 0 0, 0; X 1 0, X 1 1] := by
    have h := Matrix.eta_fin_two (X : Matrix (Fin 2) (Fin 2) (ZMod 5))
    rwa [hx01] at h
  have hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod 5)).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det X).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hdet' : (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 * (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 ≠ 0 := by
    rw [Matrix.det_fin_two, hx01] at hdet
    simpa using hdet
  rw [hS, hXM] at hBM
  have hdec := commutator_decide _ _ hdet' _ hx10 _ hBM
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hdec.1
  · intro h1
    apply hdec.2
    rw [h1]
    rfl

theorem fix_of_noFive_apply {V : Type} [Group V] [Finite V]
    (hc : ∀ a b : V, a * b = b * a) (hcard : Nat.card V = 25)
    (V₁ V₂ : Subgroup V) (h1 : Nat.card V₁ = 5) (h2 : Nat.card V₂ = 5) (hd : V₁ ⊓ V₂ = ⊥)
    (hsup : V₁ ⊔ V₂ = ⊤) (A : Subgroup (MulAut V)) (σ : MulAut V) (hσA : σ ∈ A)
    (hσ₂ : ∀ x ∈ V₂, σ x = x) (hσ₁ : ∀ x ∈ V₁, σ x = x⁻¹)
    (hno : ∀ α ∈ A, orderOf α ≠ 5) :
    ∀ α ∈ A, V₂.map α.toMonoidHom = V₂ → V₁.map α.toMonoidHom = V₁ := by
  let : CommGroup V := { ‹Group V› with mul_comm := hc }
  obtain ⟨ρ, hρ, hρ₂, hρ₁, hsig, -⟩ :=
    exists_matrix_rep_lines V hcard (pow_five_eq_one_of_sup h1 h2 hsup) V₁ V₂ h1 h2 hd
  obtain ⟨s00, s01, s10, s11⟩ := hsig σ hσ₂ hσ₁
  intro α hαA hα₂
  rw [← hρ₁]
  by_contra hα₁
  have h01 : (ρ α : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0 := (hρ₂ α).mpr hα₂
  have hmem : α * σ * α⁻¹ * σ⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hαA hσA) (A.inv_mem hαA)) (A.inv_mem hσA)
  apply hno _ hmem
  rw [← orderOf_injective ρ hρ, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact orderOf_eq_five_of_mul_eq s00 s01 s10 s11 h01 hα₁ (by group)

theorem ker_det_le_of_five (K : Subgroup GL25) (σ τ u : GL25) (hσK : σ ∈ K) (hτK : τ ∈ K)
    (huK : u ∈ K) (hu : orderOf u = 5)
    (hσ00 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = -1)
    (hσ01 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0)
    (hσ10 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0)
    (hσ11 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 1)
    (hτ00 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = 0)
    (hτ11 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 0)
    (hτ01 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 ≠ 0)
    (hτ10 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 ≠ 0) :
    (Matrix.GeneralLinearGroup.det : GL25 →* (ZMod 5)ˣ).ker ≤ K := by
  have hFive : IsFive u := isFive_of_orderOf_eq_five hu
  have hmove : ¬ (Subgroup.zpowers (⟨u, huK⟩ : K)).Normal := fun hnorm =>
    not_both_normalize hσ00 hσ01 hσ10 hσ11 hτ00 hτ11 hτ01 hτ10 hFive
      ⟨exists_pow_mul_of_normal huK hu hnorm hσK, exists_pow_mul_of_normal huK hu hnorm hτK⟩
  have hall : ∀ x : GL25, IsFive x → x ∈ K := by
    intro x hx
    have := all_isFive_mem_range K.subtype (Subgroup.subtype_injective K) ⟨u, huK⟩ hFive hmove x hx
    simpa using this
  intro g hg
  refine det_one_mem hall g ?_
  have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
  simpa using this

theorem exists_moves_of_five_apply {V : Type} [Group V] [Finite V]
    (hc : ∀ a b : V, a * b = b * a) (hcard : Nat.card V = 25)
    (V₁ V₂ : Subgroup V) (h1 : Nat.card V₁ = 5) (h2 : Nat.card V₂ = 5) (hd : V₁ ⊓ V₂ = ⊥)
    (hsup : V₁ ⊔ V₂ = ⊤) (A : Subgroup (MulAut V)) (σ : MulAut V) (hσA : σ ∈ A)
    (hσ₂ : ∀ x ∈ V₂, σ x = x) (hσ₁ : ∀ x ∈ V₁, σ x = x⁻¹)
    (τ : MulAut V) (hτA : τ ∈ A) (hτ₁ : V₁.map τ.toMonoidHom = V₂)
    (hτ₂ : V₂.map τ.toMonoidHom = V₁) (u : MulAut V) (huA : u ∈ A) (hu : orderOf u = 5) :
    ∃ α ∈ A, V₂.map α.toMonoidHom = V₂ ∧ ¬ V₁.map α.toMonoidHom = V₁ := by
  let : CommGroup V := { ‹Group V› with mul_comm := hc }
  obtain ⟨ρ, hρ, hρ₂, hρ₁, hsig, htau⟩ :=
    exists_matrix_rep_lines V hcard (pow_five_eq_one_of_sup h1 h2 hsup) V₁ V₂ h1 h2 hd
  obtain ⟨s00, s01, s10, s11⟩ := hsig σ hσ₂ hσ₁
  obtain ⟨t00, t11, t01, t10⟩ := htau τ hτ₁ hτ₂
  have hker := ker_det_le_of_five (A.map ρ) (ρ σ) (ρ τ) (ρ u) (Subgroup.mem_map_of_mem ρ hσA)
    (Subgroup.mem_map_of_mem ρ hτA) (Subgroup.mem_map_of_mem ρ huA)
    (by rw [orderOf_injective ρ hρ]; exact hu) s00 s01 s10 s11 t00 t11 t01 t10
  obtain ⟨g, hg⟩ : ∃ g : GL25, (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![1, 0; 1, 1] :=
    ⟨⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by decide +kernel, by decide +kernel⟩, rfl⟩
  have hgdet : g ∈ (Matrix.GeneralLinearGroup.det : GL25 →* (ZMod 5)ˣ).ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_fin_two_of]
    norm_num
  obtain ⟨α, hαA, hαg⟩ := hker hgdet
  refine ⟨α, hαA, ?_, ?_⟩
  · rw [← hρ₂, hαg, hg]
    rfl
  · rw [← hρ₁, hαg, hg]
    show ¬ (1 : ZMod 5) = 0
    decide

end SBc17

end CFSG.Quasithin
