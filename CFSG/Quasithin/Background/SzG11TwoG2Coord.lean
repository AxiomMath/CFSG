module

public import CFSG.Quasithin.Background.SzG11TwoG2Model
public import CFSG.Quasithin.Background.JonesParshallG2Cocycle

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]

@[expose] def zIHom (K : Type) [Field K] : (Ix3 → K) →+ quasithinZorn K where
  toFun := zI
  map_zero' := zI_zero
  map_add' := zI_add

@[expose] def thetaHom (π : quasithinZorn K →ₗ[ZMod 2] V) : (Ix3 → K) →+ V :=
  (π : quasithinZorn K →ₗ[ZMod 2] V).toAddMonoidHom.comp (zIHom K)

omit [CharP K 2] in
theorem thetaHom_apply (π : quasithinZorn K →ₗ[ZMod 2] V) (w : Ix3 → K) :
    thetaHom π w = π (zI w) := rfl

theorem map_smul_cayleyOne_eq_zero {H : Subgroup (GLV V)}
    {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} {φ : ↥H ≃* ↥G₀}
    {π : quasithinZorn K →ₗ[ZMod 2] V} (hM : IsG2Model H G₀ φ π) (c : K) :
    π (c • cayleyOne K) = 0 := by
  have h1 : c • cayleyOne K = ((c, 0, 0, c) : quasithinZorn K) := by
    simp [cayleyOne, Prod.smul_def]
  rw [h1]
  exact (hM.ker _ (CharTwo.add_self_eq_zero c)).2 ⟨c, rfl⟩

theorem thetaHom_bijective {H : Subgroup (GLV V)}
    {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} {φ : ↥H ≃* ↥G₀}
    {π : quasithinZorn K →ₗ[ZMod 2] V} (hM : IsG2Model H G₀ φ π) :
    Function.Bijective (thetaHom π) := by
  refine ⟨(injective_iff_map_eq_zero (thetaHom π)).2 fun w hw => ?_, fun v => ?_⟩
  · obtain ⟨c, hc⟩ := (hM.ker (zI w) (cayleyTr_zI w)).1 hw
    have h1 : ((c, 0, 0, c) : quasithinZorn K) = c • cayleyOne K := by
      simp [cayleyOne, Prod.smul_def]
    calc w = zP (zI w) := (zP_zI w).symm
      _ = zP ((c, 0, 0, c) : quasithinZorn K) := by rw [hc]
      _ = 0 := by rw [h1, zP_smul, zP_one, smul_zero]
  · obtain ⟨x, hxt, hxv⟩ := hM.surj v
    refine ⟨zP x, ?_⟩
    have hx := trace_zero_eq (x := x) hxt
    rw [thetaHom_apply, ← hxv]
    conv_rhs => rw [hx]
    rw [map_add, map_smul_cayleyOne_eq_zero hM, add_zero]

omit [CharP K 2] in
theorem thetaHom_smul {π : quasithinZorn K →ₗ[ZMod 2] V} {sc : K →+* Module.End (ZMod 2) V}
    (hsc : ∀ (κ : K) (x : quasithinZorn K), x.1 + x.2.2.2 = 0 → sc κ (π x) = π (κ • x))
    (κ : K) (w : Ix3 → K) : thetaHom π (κ • w) = sc κ (thetaHom π w) := by
  have hzI : zI (κ • w) = κ • zI w := by
    rw [q6_eta w, q6_smul, zI_q6, zI_q6, zmk_smul]
    simp
  rw [thetaHom_apply, thetaHom_apply, hzI, hsc κ _ (cayleyTr_zI w)]

theorem thetaHom_equiv {H : Subgroup (GLV V)} {φ : ↥H ≃* ↥(cayleyGroup K)}
    {π : quasithinZorn K →ₗ[ZMod 2] V} (hM : IsG2Model H (cayleyGroup K) φ π) (h : ↥H)
    (w : Ix3 → K) : (h : GLV V) (thetaHom π w) = thetaHom π (g2Act (φ h) w) := by
  have h1 := hM.equiv h (zI w) (cayleyTr_zI w)
  rw [thetaHom_apply, thetaHom_apply, ← h1]
  conv_lhs => rw [g2_zI_eq (φ h) w]
  rw [map_add, map_smul_cayleyOne_eq_zero hM, add_zero]

omit [CharP K 2] in
theorem thetaHom_q6_one {π : quasithinZorn K →ₗ[ZMod 2] V} {v₁ : V} (hπ : π (zU0 K) = v₁) :
    thetaHom π (q6 1 0 0 0 0 0) = v₁ := by
  rw [thetaHom_apply, zI_q6]
  exact hπ

theorem card_eq_pow_six [Finite K] {H : Subgroup (GLV V)}
    {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} {φ : ↥H ≃* ↥G₀}
    {π : quasithinZorn K →ₗ[ZMod 2] V} (hM : IsG2Model H G₀ φ π) :
    Nat.card V = Nat.card K ^ 6 := by
  have e := Nat.card_congr (Equiv.ofBijective (thetaHom π) (thetaHom_bijective hM))
  have hI : Nat.card Ix3 = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
  rw [← e, Nat.card_fun, hI]

omit [CharP K 2] [Algebra (ZMod 2) K] in
theorem bilQ_comm (w w' : Ix3 → K) : bilQ w w' = bilQ w' w := by
  simp only [bilQ]
  ring

omit [Algebra (ZMod 2) K] in
theorem bilQ_self (w : Ix3 → K) : bilQ w w = 0 := by
  have h2F : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [bilQ]
  linear_combination (w (.inl 0) * w (.inr 0) + w (.inl 1) * w (.inr 1) +
    w (.inl 2) * w (.inr 2)) * h2F

omit [CharP K 2] [Algebra (ZMod 2) K] in
theorem bilQ_add_right (w w' x : Ix3 → K) : bilQ x (w + w') = bilQ x w + bilQ x w' := by
  simp only [bilQ, Pi.add_apply]
  ring

omit [CharP K 2] [Algebra (ZMod 2) K] in
theorem bilQ_smul_right (c : K) (w x : Ix3 → K) : bilQ x (c • w) = c * bilQ x w := by
  simp only [bilQ, Pi.smul_apply, smul_eq_mul]
  ring

omit [CharP K 2] [Algebra (ZMod 2) K] in
theorem bilQ_left_nondeg {w : Ix3 → K} (h : ∀ w', bilQ w w' = 0) : w = 0 :=
  eq_of_bilQ fun w' => by rw [h w']; simp [bilQ]

omit [CharP K 2] [Algebra (ZMod 2) K] in
theorem bilQ_right_nondeg {w : Ix3 → K} (h : ∀ w', bilQ w' w = 0) : w = 0 :=
  bilQ_left_nondeg fun w' => by rw [bilQ_comm]; exact h w'

end CFSG.Quasithin.G11.SzG11S.Two
