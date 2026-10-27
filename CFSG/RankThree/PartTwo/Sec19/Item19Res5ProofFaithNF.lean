module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.SeitzGeneration.OutdiagPlane

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG.LieType.SeitzGeneration

variable {F : Type} [Field F]

theorem isPrimitiveRoot_of_pow_three {w : F} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) :
    IsPrimitiveRoot w 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← orderOf_eq_prime hw3 hw1]
  exact IsPrimitiveRoot.orderOf w

theorem heis_of_normalized (H : Subgroup (GL (Fin 3) F))
    (hH : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H)
    {x g : GL (Fin 3) F} (hx : x ∈ H) (hg : g ∈ H) {w α s : Fˣ}
    (hrel : g * x = Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * g)) (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) (hx3 : x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) α)
    (hg3 : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (s ^ 3)) :
    ∃ x' ∈ H, ∃ y' ∈ H, ∃ (P : GL (Fin 3) F) (ξ w' α' : F), IsPrimitiveRoot w' 3 ∧
      (y' : Matrix (Fin 3) (Fin 3) F) * P = P * diagonal ![ξ, ξ * w', ξ * w' ^ 2] ∧
      (x' : Matrix (Fin 3) (Fin 3) F) * P = P * !![0, 0, α'; 1, 0, 0; 0, 1, 0] := by
  set y' : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g with hy'
  have hrel' : y' * x = Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * y') := by
    calc (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g) * x
        = Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * (g * x) := mul_assoc _ _ _
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * g)) := by rw [hrel]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) w *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * (x * g)) := by
        rw [← mul_assoc, (commute_scalarGL s⁻¹
          (Matrix.GeneralLinearGroup.scalar (Fin 3) w)).eq, mul_assoc]
      _ = _ := by
        congr 1
        rw [← mul_assoc, ← mul_assoc, (commute_scalarGL s⁻¹ x).eq]
  have hy3 : y' ^ 3 = 1 := by
    rw [hy', Commute.mul_pow (commute_scalarGL s⁻¹ g) 3, ← map_pow, hg3, ← map_mul, ← mul_pow,
      inv_mul_cancel, one_pow, map_one]
  have hyxM : (y' : Matrix (Fin 3) (Fin 3) F) * x = (w : F) • ((x : Matrix (Fin 3) (Fin 3) F) *
      (y' : Matrix (Fin 3) (Fin 3) F)) := by
    have h := congrArg Units.val hrel'
    rw [Units.val_mul, Units.val_mul (Matrix.GeneralLinearGroup.scalar (Fin 3) w), coe_scalarGL,
      Matrix.smul_mul, Matrix.one_mul, ← Units.val_mul] at h
    exact h
  have hy3M : (y' : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  have hx3M : (x : Matrix (Fin 3) (Fin 3) F) ^ 3 = (α : F) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, coe_scalarGL]
  have hw3F : (w : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
  have hw1F : (w : F) ≠ 1 := fun h => hw1 (Units.val_eq_one.1 h)
  have hprim := isPrimitiveRoot_of_pow_three hw3F hw1F
  obtain ⟨P, ξ, -, hPy, hPx⟩ := exists_heisenberg_basis_gl hprim hyxM hy3M hx3M
  exact ⟨x, hx, y', H.mul_mem (hH _) hg, P, ξ, w, α, hprim, hPy, hPx⟩

variable [Finite F]

theorem toral_or_heis (hF3 : 3 ∣ Nat.card F - 1) (hζ : ∃ ζ : F, IsPrimitiveRoot ζ 3)
    (H : Subgroup (GL (Fin 3) F))
    (hH : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H) {x y : GL (Fin 3) F}
    (hx : x ∈ H) (hy : y ∈ H) {ω α β : Fˣ}
    (hyx : y * x = Matrix.GeneralLinearGroup.scalar (Fin 3) ω * (x * y))
    (hx3 : x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) α)
    (hy3 : y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) β)
    (hind : ∀ a b : ℕ, (∃ c : Fˣ, x ^ a * y ^ b = Matrix.GeneralLinearGroup.scalar (Fin 3) c) →
      3 ∣ a ∧ 3 ∣ b) :
    (∃ P : GL (Fin 3) F, ∀ i j : Fin 3, i ≠ j →
      ((P * x * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j = 0 ∧
      ((P * y * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j = 0) ∨
    (∃ x' ∈ H, ∃ y' ∈ H, ∃ (P : GL (Fin 3) F) (ξ w α' : F), IsPrimitiveRoot w 3 ∧
      (y' : Matrix (Fin 3) (Fin 3) F) * P = P * diagonal ![ξ, ξ * w, ξ * w ^ 2] ∧
      (x' : Matrix (Fin 3) (Fin 3) F) * P = P * !![0, 0, α'; 1, 0, 0; 0, 1, 0]) := by
  have hω3 := cube_eq_one_of_quasi_commute hyx
  have hx3M : ((x ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (α : F) • 1 := by
    rw [hx3, coe_scalarGL]
  have hy3M : ((y ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (β : F) • 1 := by
    rw [hy3, coe_scalarGL]
  by_cases hω1 : ω = 1
  ·
    left
    subst hω1
    have hxy : x * y = y * x := by rw [map_one, one_mul] at hyx; exact hyx.symm
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc : Commute x y := hxy
    obtain ⟨a, b, s, hs0, hab, hs3⟩ := exists_cube_line hF3 (x := x) (y := y) (w := 1)
      (fun g => Commute.one_left g) (one_pow 3) (by rw [one_mul]; exact hxy.symm) α.ne_zero
      β.ne_zero hx3M hy3M
    set g₀ : GL (Fin 3) F := x ^ a * y ^ b with hg₀
    set X₁ : Matrix (Fin 3) (Fin 3) F := s⁻¹ • (g₀ : Matrix (Fin 3) (Fin 3) F) with hX₁
    have hX₁3 : X₁ ^ 3 = 1 := by
      rw [hX₁, smul_pow, ← Units.val_pow_eq_pow_val, hs3, smul_smul, ← mul_pow,
        inv_mul_cancel₀ hs0, one_pow, one_smul]
    have hX₁s : ∀ c : F, X₁ ≠ c • (1 : Matrix (Fin 3) (Fin 3) F) := by
      intro c hcX
      have h1 : ((x ^ a * y ^ b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (s * c) • 1 := by
        have : (g₀ : Matrix (Fin 3) (Fin 3) F) = s • X₁ := by
          rw [hX₁, smul_smul, mul_inv_cancel₀ hs0, one_smul]
        rw [← hg₀, this, hcX, smul_smul]
      have := hind a b (exists_scalarGL_of_coe_eq (by norm_num) h1)
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    have hcomm : ∀ h : GL (Fin 3) F, Commute x h → Commute y h →
        X₁ * (h : Matrix (Fin 3) (Fin 3) F) = (h : Matrix (Fin 3) (Fin 3) F) * X₁ := by
      intro h hxh hyh
      have h1 : Commute g₀ h := ((hxh.pow_left a).mul_left (hyh.pow_left b))
      have h2 : (g₀ : Matrix (Fin 3) (Fin 3) F) * h = h * g₀ := congrArg Units.val h1.eq
      rw [hX₁, Matrix.smul_mul, Matrix.mul_smul, h2]
    have hcube : ∀ (h : GL (Fin 3) F) (lam : F), Commute x h → Commute y h →
        ((h ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = lam • 1 → ∃ μ : F, μ ^ 3 = lam := by
      intro h lam hxh hyh hh3
      refine exists_cube_of_commute hζ hX₁3 hX₁s (hcomm h hxh hyh) ?_
      rw [← Units.val_pow_eq_pow_val]
      exact hh3
    obtain ⟨μx, hμx⟩ := hcube x α (Commute.refl x) hc.symm hx3M
    obtain ⟨μy, hμy⟩ := hcube y β hc (Commute.refl y) hy3M
    have hμx0 : μx ≠ 0 := by rintro rfl; exact α.ne_zero (by rw [← hμx]; norm_num)
    have hμy0 : μy ≠ 0 := by rintro rfl; exact β.ne_zero (by rw [← hμy]; norm_num)
    obtain ⟨ux, hux⟩ : ∃ u : Fˣ, (u : F) = μx⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμx0), rfl⟩
    obtain ⟨uy, huy⟩ : ∃ u : Fˣ, (u : F) = μy⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμy0), rfl⟩
    obtain ⟨xn, hxn⟩ : ∃ g : GL (Fin 3) F, g = Matrix.GeneralLinearGroup.scalar (Fin 3) ux * x :=
      ⟨_, rfl⟩
    obtain ⟨yn, hyn⟩ : ∃ g : GL (Fin 3) F, g = Matrix.GeneralLinearGroup.scalar (Fin 3) uy * y :=
      ⟨_, rfl⟩
    have hx3' : (x : Matrix (Fin 3) (Fin 3) F) ^ 3 = (α : F) • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hx3M
    have hy3' : (y : Matrix (Fin 3) (Fin 3) F) ^ 3 = (β : F) • 1 := by
      rw [← Units.val_pow_eq_pow_val]; exact hy3M
    have hxn3 : xn ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hxn, coe_scalarGL_mul, smul_pow, hx3', smul_smul, hux, ← hμx,
        ← mul_pow, inv_mul_cancel₀ hμx0, one_pow, one_smul, Units.val_one]
    have hyn3 : yn ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hyn, coe_scalarGL_mul, smul_pow, hy3', smul_smul, huy, ← hμy,
        ← mul_pow, inv_mul_cancel₀ hμy0, one_pow, one_smul, Units.val_one]
    have hxyn : Commute xn yn := by
      rw [hxn, hyn]
      exact Commute.mul_left (Commute.mul_right (commute_scalarGL ux _) (commute_scalarGL ux _))
        (Commute.mul_right (commute_scalarGL uy x).symm hc)
    have hpair : ({xn, yn} : Set (GL (Fin 3) F)).Pairwise Commute := by
      rw [Set.pairwise_pair]; exact fun _ => ⟨hxyn, hxyn.symm⟩
    have hcomE : IsMulCommutative (Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F))) :=
      Subgroup.isMulCommutative_closure hpair
    have hcommE : ∀ u ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)),
        ∀ v ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)), u * v = v * u :=
      fun u hu v hv => congrArg Subtype.val (hcomE.is_comm.comm (⟨u, hu⟩ :
        Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F))) ⟨v, hv⟩)
    have hexpE : ∀ u ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)), u ^ 3 = 1 := by
      intro u hu
      refine Subgroup.closure_induction (p := fun u _ => u ^ 3 = 1) ?_ (by simp) ?_ ?_ hu
      · intro u hu
        rcases hu with rfl | hu
        · exact hxn3
        · rw [Set.mem_singleton_iff] at hu
          rw [hu]; exact hyn3
      · intro u v hu hv hu3 hv3
        rw [Commute.mul_pow (hcommE u hu v hv), hu3, hv3, one_mul]
      · intro u hu hu3
        rw [inv_pow, hu3, inv_one]
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
      hζ _ hcommE hexpE
    have hxnE : xn ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hynE : yn ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hxux : x = Matrix.GeneralLinearGroup.scalar (Fin 3) ux⁻¹ * xn := by
      rw [hxn, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have hyuy : y = Matrix.GeneralLinearGroup.scalar (Fin 3) uy⁻¹ * yn := by
      rw [hyn, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have hscal : ∀ (u : Fˣ) (g : GL (Fin 3) F), P * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * g)
        * P⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (P * g * P⁻¹) := by
      intro u g
      rw [← mul_assoc, ← (commute_scalarGL u P).eq, mul_assoc, mul_assoc, mul_assoc]
    refine ⟨P, fun i j hij => ⟨?_, ?_⟩⟩
    · rw [hxux, hscal, Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_apply, hP xn hxnE i j hij, smul_zero]
    · rw [hyuy, hscal, Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_apply, hP yn hynE i j hij, smul_zero]
  ·
    right
    have hw : ∀ g, Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) ω) g :=
      fun g => commute_scalarGL ω g
    have hw3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) F) ^ 3 = 1 := by
      rw [← map_pow, hω3, map_one]
    obtain ⟨a, b, s, hs0, hab, hs3⟩ := exists_cube_line hF3 hw hw3 hyx α.ne_zero β.ne_zero hx3M
      hy3M
    obtain ⟨su, hsu⟩ : ∃ u : Fˣ, (u : F) = s := ⟨Units.mk0 s hs0, rfl⟩
    have hg3 : (x ^ a * y ^ b) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (su ^ 3) := by
      apply Units.ext
      rw [hs3, coe_scalarGL, Units.val_pow_eq_pow_val, hsu]
    have hxc := fun (c : Fˣ) => (commute_scalarGL (F := F) (n := 3) c x).eq
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [pow_one, pow_zero, mul_one] at hg3
      refine heis_of_normalized H hH hy hx (w := ω⁻¹) (α := β) (s := su) ?_ ?_ ?_ hy3 hg3
      · rw [hyx, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      · rw [inv_pow, hω3, inv_one]
      · exact inv_ne_one.2 hω1
    · simp only [pow_zero, one_mul, pow_one] at hg3
      exact heis_of_normalized H hH hx hy (w := ω) (α := α) (s := su) hyx hω3 hω1 hx3 hg3
    · simp only [pow_one] at hg3
      refine heis_of_normalized H hH hx (H.mul_mem hx hy) (w := ω) (α := α) (s := su) ?_ hω3 hω1
        hx3 hg3
      calc x * y * x = x * (y * x) := mul_assoc _ _ _
        _ = x * (Matrix.GeneralLinearGroup.scalar (Fin 3) ω * (x * y)) := by rw [hyx]
        _ = _ := by rw [← mul_assoc, ← hxc ω, mul_assoc]
    · simp only [pow_one] at hg3
      have h2 : y ^ 2 * x = Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * (x * y ^ 2) := by
        rw [map_pow]; exact pow_mul_eq_of_quasi_commute hw hyx 2
      have hω2 : ω ^ 2 ≠ 1 := by
        intro h
        apply hω1
        calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
          _ = 1 := by rw [hω3, h, inv_one, one_mul]
      refine heis_of_normalized H hH hx (H.mul_mem hx (H.pow_mem hy 2)) (w := ω ^ 2) (α := α)
        (s := su) ?_ (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]) hω2 hx3 hg3
      calc x * y ^ 2 * x = x * (y ^ 2 * x) := mul_assoc _ _ _
        _ = x * (Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * (x * y ^ 2)) := by rw [h2]
        _ = _ := by rw [← mul_assoc, ← hxc (ω ^ 2), mul_assoc]

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
