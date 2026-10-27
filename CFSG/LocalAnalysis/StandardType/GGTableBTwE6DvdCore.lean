module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TwE6Dvd

variable {R : Type} [Group R]

@[expose] def CentInv (p : ℕ) (τ : MulAut R) : Prop :=
  ∀ A B : Subgroup R, IsElemAbelian p A → Nat.card A = p ^ 6 → (∀ a ∈ A, τ a = a) → B ≤ A →
    Nat.card B = p ^ 5 →
    (∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ b ∈ B, ∀ v ∈ V, b * v * b⁻¹ ∈ V) →
    ∃ u : R, u ≠ 1 ∧ u ^ 2 = 1 ∧ τ u = u ∧ ∀ b ∈ B, b * u = u * b

theorem CentInv.conj {p : ℕ} {f : MulAut R} (h : CentInv p f) (g : MulAut R) :
    CentInv p (g * f * g⁻¹) := by
  intro A B hA hA6 hfix hBA hB5 ⟨V, hV1, hV2, hVB⟩
  have hginj : Function.Injective (g⁻¹ : MulAut R).toMonoidHom := (g⁻¹ : MulAut R).injective
  have hgg : ∀ x : R, g⁻¹ (g x) = x := fun x => by rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hgg' : ∀ x : R, g (g⁻¹ x) = x := fun x => by rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hfix' : ∀ a ∈ A, f (g⁻¹ a) = g⁻¹ a := fun a ha => by
    have e := hfix a ha
    rw [MulAut.mul_apply, MulAut.mul_apply] at e
    rw [← hgg (f (g⁻¹ a)), e]
  obtain ⟨u, hu1, hu2, hfu, hub⟩ := h (A.map (g⁻¹ : MulAut R).toMonoidHom)
    (B.map (g⁻¹ : MulAut R).toMonoidHom) (TableB.isElemAbelian_map hA _)
    (by rwa [Subgroup.card_map_of_injective hginj])
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact hfix' a ha)
    (Subgroup.map_mono hBA) (by rwa [Subgroup.card_map_of_injective hginj])
    ⟨V.map (g⁻¹ : MulAut R).toMonoidHom, by
      rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hginj], hV2.map _, by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨v, hv, rfl⟩
      refine ⟨b * v * b⁻¹, hVB b hb v hv, ?_⟩
      change g⁻¹ (b * v * b⁻¹) = g⁻¹ b * g⁻¹ v * (g⁻¹ b)⁻¹
      rw [map_mul, map_mul, map_inv]⟩
  refine ⟨g u, fun h1 => hu1 ?_, ?_, ?_, fun b hb => ?_⟩
  · rw [← hgg u, h1, map_one]
  · rw [← map_pow, hu2, map_one]
  · rw [MulAut.mul_apply, MulAut.mul_apply, hgg, hfu]
  · have e := hub (g⁻¹ b) ⟨b, hb, rfl⟩
    have e' := congrArg g e
    rwa [map_mul, map_mul, hgg'] at e'

theorem comap_conj_facts {p : ℕ} (hZ : Subgroup.center R = ⊥) {E : Subgroup (MulAut R)}
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap MulAut.conj) ∧ Nat.card (E.comap MulAut.conj) =
      Nat.card (E ⊓ (MulAut.conj : R →* MulAut R).range : Subgroup (MulAut R)) := by
  have hinj := mulAut_conj_injective hZ
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hE a.2 b.2
  · rw [map_pow, map_one]
    exact hE.2 _ hx
  · rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_comm]

theorem apply_eq_of_commute (hZ : Subgroup.center R = ⊥) {τ : MulAut R} {b : R}
    (hc : τ * MulAut.conj b = MulAut.conj b * τ) : τ b = b := by
  apply mulAut_conj_injective hZ
  refine MulEquiv.ext fun x => ?_
  have e := congrArg (fun φ : MulAut R => φ (τ⁻¹ x)) hc
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self] at e
  rw [MulAut.conj_apply, MulAut.conj_apply]
  exact e

theorem ggBstarBoundInnR_of_centInv [Finite R] {p : ℕ} (hp : p.Prime) {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥) (hO : GGOutdiagPrime p R I)
    (hR : ∀ A : Subgroup R, IsElemAbelian p A → Nat.card A ≤ p ^ 6)
    (hQ : ∀ E : Subgroup (MulAut R), IsElemAbelian p E →
      Nat.card E ≤ p * Nat.card (E ⊓ (MulAut.conj : R →* MulAut R).range : Subgroup (MulAut R)))
    (hC : ∀ τ : MulAut R, τ ∉ I → τ ^ p = 1 → CentInv p τ) :
    GGBstarBoundInnR p 5 R I := by
  intro Eb Eh hEbI hEb h5 _ hV hle hEh hcard
  have hEbinn : ∀ φ ∈ Eb, φ ∈ (MulAut.conj : R →* MulAut R).range := fun φ hφ =>
    hO φ (hEbI hφ) (hEb.2 φ hφ)
  obtain ⟨hA, hAc⟩ := comap_conj_facts hZ hEh
  obtain ⟨hB, hBc⟩ := comap_conj_facts hZ hEb
  rw [inf_eq_left.mpr hEbinn] at hBc
  have hA6 : Nat.card (Eh.comap MulAut.conj) = p ^ 6 := by
    refine le_antisymm (hR _ hA) (Nat.le_of_mul_le_mul_left ?_ hp.pos)
    calc p * p ^ 6 = p ^ 2 * p ^ 5 := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ h5
      _ ≤ Nat.card Eh := hcard
      _ ≤ p * Nat.card (Eh.comap MulAut.conj) := hAc ▸ hQ Eh hEh
  have hB5 : Nat.card (Eb.comap MulAut.conj) = p ^ 5 := by
    refine le_antisymm (Nat.le_of_mul_le_mul_left ?_ (pow_pos hp.pos 2)) (hBc ▸ h5)
    calc p ^ 2 * Nat.card (Eb.comap MulAut.conj) ≤ Nat.card Eh := hBc ▸ hcard
      _ ≤ p * Nat.card (Eh.comap MulAut.conj) := hAc ▸ hQ Eh hEh
      _ = p ^ 2 * p ^ 5 := by rw [hA6]; ring
  obtain ⟨τ, hτ, hτI⟩ : ∃ τ ∈ Eh, τ ∉ I := by
    by_contra hall
    push Not at hall
    have hinn : Eh ≤ (MulAut.conj : R →* MulAut R).range := fun φ hφ =>
      hO φ (hall φ hφ) (hEh.2 φ hφ)
    have h7 : p ^ 7 ≤ p ^ 6 := calc
      p ^ 7 = p ^ 2 * p ^ 5 := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ h5
      _ ≤ Nat.card Eh := hcard
      _ = p ^ 6 := by rw [← hA6, hAc, inf_eq_left.mpr hinn]
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h7
    omega
  have hτp : τ ^ p = 1 := hEh.2 τ hτ
  have hfix : ∀ a ∈ Eh.comap MulAut.conj, τ a = a := fun a ha =>
    apply_eq_of_commute hZ (TableB.IsElemAbelian.comm hEh hτ ha)
  obtain ⟨V, hV1, hV2, hVB⟩ := hV
  obtain ⟨u, hu1, hu2, hτu, hub⟩ := hC τ hτI hτp _ _ hA hA6 hfix (Subgroup.comap_mono hle) hB5
    ⟨V, hV1, hV2, fun b hb v hv => by
      have e := hVB _ hb v hv
      rwa [MulAut.conj_apply] at e⟩
  have hstab : Eb ⊔ Subgroup.zpowers τ ≤ MulAction.stabilizer (MulAut R) u := by
    refine sup_le (fun φ hφ => ?_) ((Subgroup.zpowers_le).2 hτu)
    obtain ⟨b, rfl⟩ := hEbinn φ hφ
    change MulAut.conj b u = u
    rw [MulAut.conj_apply, hub b hφ, mul_inv_cancel_right]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Eb ⊔ Subgroup.zpowers τ, lt_of_le_of_ne le_sup_left fun h => hτI (hEbI ?_),
    sup_le hle ((Subgroup.zpowers_le).2 hτ), Subgroup.zpowers u, ?_, ?_, ?_⟩
  · rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1, pow_one]
  · intro φ hφ v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have e : φ u = u := hstab hφ
    rw [map_zpow, e]
    exact Subgroup.zpow_mem_zpowers u k

end TwE6Dvd

end CFSG.StandardType
