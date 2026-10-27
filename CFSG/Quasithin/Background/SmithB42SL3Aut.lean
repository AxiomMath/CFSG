module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace B42SL3

open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X7Sec
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.Setup.X7
open scoped MatrixGroups

section Aut

variable {F : Type} [Field F] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)

@[expose] noncomputable def innerPart : Subgroup ↥A :=
  (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range.comap
    (normalizerHom ρ hker A hA)

theorem mem_innerPart {a : ↥A} : a ∈ innerPart ρ hker A hA ↔
    normalizerHom ρ hker A hA a ∈
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := Iff.rfl

variable [CFSG.IsElementaryAbelian 2 A]

theorem elem_mul_self (a : ↥A) : a * a = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : U ≃ₗ[ZMod 2] U) a.2

theorem normalizerHom_injective (hirr : ρ.IsIrreducible) :
    Function.Injective (normalizerHom ρ hker A hA) := by
  rw [injective_iff_map_eq_one]
  intro a ha1
  have hb := intertwines_psi ρ (normalizerHom ρ hker A hA a) 1 (by rw [map_one, ha1])
    (a : U ≃ₗ[ZMod 2] U) (exists_induced ρ hker A hA a)
  refine Subtype.ext (eq_one_of_commutes_sq_one ρ hirr (a : U ≃ₗ[ZMod 2] U) (fun x u => ?_) ?_)
  · simpa using hb x u
  · have := elem_mul_self A a
    exact congrArg Subtype.val this

variable [Fintype F]

theorem exists_lift_of_inner {f : ℕ} (hf : 1 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) (a : ↥A) (ha : a ∈ innerPart ρ hker A hA) :
    ∃ t : SL(3, F), t * t = 1 ∧ ∀ u, (a : U ≃ₗ[ZMod 2] U) u = ρ t u := by
  classical
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hNat
  obtain ⟨p, hp⟩ := ha
  have hA2' := elem_mul_self A
  have hA2 : ∀ b ∈ A, b * b = 1 := fun b hb => congrArg Subtype.val (hA2' ⟨b, hb⟩)
  have hpp : p * p = 1 := by
    have h1 : MulAut.conj (p * p) = (1 : MulAut (projectiveSL 3 F)) := by
      rw [map_mul, hp, ← map_mul, hA2' a, map_one]
    exact conj_injective_projectiveSL (h1.trans (map_one _).symm)
  obtain ⟨y, rfl⟩ := proj_surjective 3 F p
  have hy2 : y * y ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_mul]
    exact hpp
  have hkodd : Odd (Nat.card (scalars 3 F)) := by
    have hdvd := card_scalars_dvd (K := F) (n := 3) (by norm_num)
    have hodd : Odd (Nat.card F - 1) := by
      rw [hNat]
      have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      rw [Nat.odd_iff]
      omega
    exact Odd.of_dvd_nat hodd hdvd
  set k := Nat.card (scalars 3 F) with hk
  have htsq : y ^ k * y ^ k = 1 := by
    have h1 : y ^ k * y ^ k = (y * y) ^ k := by
      rw [← pow_add, ← two_mul, pow_mul, sq]
    rw [h1]
    have h2 : (⟨y * y, hy2⟩ : scalars 3 F) ^ k = 1 := pow_card_eq_one'
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hproj : proj 3 F (y ^ k) = proj 3 F y := by
    rw [map_pow]
    exact pow_eq_self_of_sq hpp hkodd
  have hdesc : descendAut 3 F (MulAut.conj (y ^ k)) = normalizerHom ρ hker A hA a := by
    rw [descendAut_conj, hproj, hp]
  have hb := intertwines_psi ρ (normalizerHom ρ hker A hA a) (MulAut.conj (y ^ k)) hdesc
    (a : U ≃ₗ[ZMod 2] U) (exists_induced ρ hker A hA a)
  set t := y ^ k with ht
  have hcomm : ∀ x' u, (repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) (ρ x' u) =
      ρ x' ((repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) u) := by
    intro x' u
    show ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) (ρ x' u)) = ρ x' (ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u))
    rw [hb x' u, MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply,
      ← map_mul]
    congr 2
    group
  have hsq : (repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) *
      (repEquiv ρ t⁻¹ * (a : U ≃ₗ[ZMod 2] U)) = 1 := by
    refine LinearEquiv.ext fun u => ?_
    show ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) (ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u))) = u
    have h1 := hb t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u)
    have haa : (a : U ≃ₗ[ZMod 2] U) ((a : U ≃ₗ[ZMod 2] U) u) = u := by
      have := LinearEquiv.congr_fun (hA2 a a.2) u
      simpa using this
    rw [h1, haa, MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul]
    have h3 : t⁻¹ * (t * t⁻¹ * t⁻¹) = 1 := by
      calc t⁻¹ * (t * t⁻¹ * t⁻¹) = (t * t)⁻¹ := by group
        _ = 1 := by rw [htsq, inv_one]
    rw [h3, map_one]
    rfl
  have hc1 := eq_one_of_commutes_sq_one ρ hirr _ hcomm hsq
  refine ⟨t, htsq, fun u => ?_⟩
  have := LinearEquiv.congr_fun hc1 u
  have h2 : ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u) = u := this
  calc (a : U ≃ₗ[ZMod 2] U) u = ρ t (ρ t⁻¹ ((a : U ≃ₗ[ZMod 2] U) u)) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    _ = ρ t u := by rw [h2]

theorem exists_transvection_of_outer [Finite U] {f : ℕ} (hf : 2 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (a : ↥A) (ha : a ∉ innerPart ρ hker A hA) :
    ∃ t : SL(3, F), CFSG.QuasithinUnique.Setup.X7a.IsTransvection t ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤
        2 * Module.finrank (ZMod 2)
          (LinearMap.range ((a : U ≃ₗ[ZMod 2] U).toLinearMap - 1)) := by
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hNat
  have hα2 : normalizerHom ρ hker A hA a * normalizerHom ρ hker A hA a = 1 := by
    rw [← map_mul, elem_mul_self A a, map_one]
  obtain ⟨ψ, g, t, -, hψ, ht, hgt⟩ :=
    outer_involution_transvection_commutator hf hNat (normalizerHom ρ hker A hA a) hα2 ha
  obtain ⟨-, -, hrk⟩ := commutator_rank_bound ρ (normalizerHom ρ hker A hA a) ψ hψ
    (a : U ≃ₗ[ZMod 2] U) (exists_induced ρ hker A hA a) g t hgt
  exact ⟨t, ht, hrk⟩

omit [CFSG.IsElementaryAbelian 2 A] in
theorem mem_semilinear_of_not_selfDual [Finite U] [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hF : Fintype.card F = 2 ^ f) (hirr : ρ.IsIrreducible) (hsd : ¬ Nonempty (ρ.Equiv ρ.dual))
    (a : ↥A) : normalizerHom ρ hker A hA a ∈ semilinearAutGroup 3 F := by
  classical
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨M, σ, ε, hε, hαeq⟩ := hgen (normalizerHom ρ hker A hA a)
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    rw [hαeq]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup M))
      (fieldAut_mem_semilinearAutGroup σ)
  · exfalso
    apply hsd
    have hψ : descendAut 3 F (stdAut M σ 1) = normalizerHom ρ hker A hA a := by
      rw [descendAut_stdAut, hαeq]
    have hint := intertwines_psi ρ _ (stdAut M σ 1) hψ (a : U ≃ₗ[ZMod 2] U)
      (exists_induced ρ hker A hA a)
    obtain ⟨j, hj⟩ := stdAut_one_apply hF hf M σ
    obtain ⟨e⟩ := (graphFieldTwistsDual f F hf hF U ρ hirr M j).2
    refine ⟨(Representation.Equiv.mk (a : U ≃ₗ[ZMod 2] U) (fun g => ?_)).trans e⟩
    refine LinearMap.ext fun u => ?_
    have h1 := hint g u
    rw [hj g] at h1
    exact h1

theorem mul_mem_innerPart [Finite U] [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hF : Fintype.card F = 2 ^ f) (hirr : ρ.IsIrreducible) (hsd : ¬ Nonempty (ρ.Equiv ρ.dual))
    {a b : ↥A} (ha : a ∉ innerPart ρ hker A hA) (hb : b ∉ innerPart ρ hker A hA) :
    a * b ∈ innerPart ρ hker A hA := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  set Φ := normalizerHom ρ hker A hA with hΦ
  have hsq : ∀ c : ↥A, Φ c * Φ c = 1 := fun c => by rw [← map_mul, elem_mul_self A c, map_one]
  have hfield : ∀ c : ↥A, c ∉ innerPart ρ hker A hA → ∃ (M : GL (Fin 3) F) (σ : F ≃+* F),
      Φ c = LinearFlag.conjAut 3 F M * LinearFlag.fieldAut 3 F σ ∧
        (Even f ∧ ∀ x, σ x = x ^ 2 ^ (f / 2)) := by
    intro c hc
    obtain ⟨M, σ, hMσ⟩ := mem_semilinearAutGroup_iff.mp
      (mem_semilinear_of_not_selfDual ρ hker A hA hf hF hirr hsd c)
    refine ⟨M, σ, hMσ, ?_⟩
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply hc
      rw [mem_innerPart, hMσ, h1, map_one, mul_one]
      refine mem_inner_of_sq_conjAut ?_
      have := hsq c
      rwa [hMσ, h1, map_one, mul_one] at this
    have hσσ : σ * σ = 1 := by
      have h1 := hsq c
      rw [hMσ, conjAut_mul_fieldAut_mul] at h1
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) (n := 3) le_rfl _ _ h1).1
    exact even_and_eq_pow_of_involution hf hNat hσ1 hσσ
  obtain ⟨M, σ, hM, hfe, hσ⟩ := hfield a ha
  obtain ⟨N, τ, hN, -, hτ⟩ := hfield b hb
  have hστ : τ = σ := RingEquiv.ext fun x => by rw [hσ, hτ]
  rw [mem_innerPart, map_mul, hM, hN, hστ, conjAut_mul_fieldAut_mul]
  have hσσ : σ * σ = 1 := RingEquiv.ext fun x => by
    show σ (σ x) = x
    rw [hσ, hσ, ← pow_mul, ← pow_add]
    obtain ⟨m, hm⟩ := hfe
    have h : f / 2 + f / 2 = f := by omega
    rw [h, ← hF, FiniteField.pow_card]
  rw [hσσ, map_one, mul_one]
  refine mem_inner_of_sq_conjAut ?_
  have := hsq (a * b)
  rwa [map_mul, hM, hN, hστ, conjAut_mul_fieldAut_mul, hσσ, map_one, mul_one] at this

theorem card_le_two_mul_innerPart [Finite U] [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hF : Fintype.card F = 2 ^ f) (hirr : ρ.IsIrreducible) (hsd : ¬ Nonempty (ρ.Equiv ρ.dual)) :
    Nat.card ↥A ≤ 2 * Nat.card ↥(innerPart ρ hker A hA) := by
  classical
  set I := innerPart ρ hker A hA with hI
  by_cases h : ∀ a : ↥A, a ∈ I
  · have : Nat.card ↥A ≤ Nat.card ↥I :=
      Nat.card_le_card_of_injective (fun a => (⟨a, h a⟩ : ↥I))
        (fun a b hab => congrArg Subtype.val hab)
    omega
  · push Not at h
    obtain ⟨a₀, ha₀⟩ := h
    let g : ↥A → Bool × ↥I := fun b =>
      if hb : b ∈ I then (false, ⟨b, hb⟩)
      else (true, ⟨a₀ * b, mul_mem_innerPart ρ hker A hA hf hF hirr hsd ha₀ hb⟩)
    have hg : Function.Injective g := by
      intro b c hbc
      by_cases hb : b ∈ I <;> by_cases hc : c ∈ I <;> simp only [g, hb, hc, dite_true,
        dite_false, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and,
        true_and] at hbc
      · exact congrArg Subtype.val hbc
      · exact mul_left_cancel (congrArg Subtype.val hbc)
    have h1 := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

omit [Fintype F] in
theorem isElementaryAbelian_range :
    CFSG.IsElementaryAbelian 2 (normalizerHom ρ hker A hA).range := by
  have hA2' := elem_mul_self A
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show normalizerHom ρ hker A hA a * normalizerHom ρ hker A hA b =
      normalizerHom ρ hker A hA b * normalizerHom ρ hker A hA a
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact CFSG.QuasithinUnique.Setup.Layer.Actor.comm_of_isElementaryAbelian_two
      inferInstance _ a.2 _ b.2
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨_, a, rfl⟩ := x
    apply Subtype.ext
    show normalizerHom ρ hker A hA a ^ 2 = 1
    rw [← map_pow, pow_two, hA2' a, map_one]

theorem card_innerPart_le [CharP F 2] {f : ℕ} (hf : 2 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) : Nat.card ↥(innerPart ρ hker A hA) ≤ 2 ^ (2 * f) := by
  have := isElementaryAbelian_range ρ hker A hA
  obtain ⟨h1, -, -, -⟩ := elementary_automorphism_rank_bound hf hNat
    (normalizerHom ρ hker A hA).range
  have hle : (innerPart ρ hker A hA).map (normalizerHom ρ hker A hA) ≤
      (normalizerHom ρ hker A hA).range ⊓
        (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, ha⟩
  rw [← Subgroup.card_map_of_injective (normalizerHom_injective ρ hker A hA hirr)]
  exact (Subgroup.card_le_of_le hle).trans h1

end Aut

section Rank

variable {F : Type} [Field F] [CharP F 2] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
  [Finite U] (ρ : Representation (ZMod 2) SL(3, F) U)

omit [CharP F 2] in
theorem finrank_range_conj (g x : SL(3, F)) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (g⁻¹ * x * g) - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have e1 : ρ (g⁻¹ * x * g) - 1 =
      (repEquiv ρ g⁻¹).toLinearMap ∘ₗ (ρ x - 1) ∘ₗ (repEquiv ρ g).toLinearMap := by
    refine LinearMap.ext fun u => ?_
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, map_mul, Module.End.mul_apply]
    show ρ g⁻¹ (ρ x (ρ g u)) - u = ρ g⁻¹ (ρ x (ρ g u) - ρ g u)
    rw [map_sub, ← Module.End.mul_apply (ρ g⁻¹) (ρ g), ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [e1, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (repEquiv ρ g))]
  exact LinearEquiv.finrank_map_eq (repEquiv ρ g⁻¹) _

theorem finrank_range_involution [Fintype F] {t : SL(3, F)} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) := by
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Setup.X7a.exists_conj_transvection t ht1 ht2
  rw [← hg, finrank_range_conj]

end Rank

section Excl

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {U : Type} [AddCommGroup U]
  [Module (ZMod 2) U] [Finite U] (ρ : Representation (ZMod 2) SL(3, F) U)
  (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

theorem card_mul_card_fix_lt {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) (hsd : ¬ Nonempty (ρ.Equiv ρ.dual)) (hA1 : A ≠ ⊥) {k : ℕ}
    (hk : Nat.card ↥(innerPart ρ hker A hA) ≤ 2 ^ k)
    (hR3 : 3 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)))
    (hRk : k + 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1))) :
    Nat.card ↥A * Nat.card {u : U // ∀ a ∈ A, a u = u} < Nat.card U := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hfinU : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  set R := Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) with hRdef
  have hcardA := card_le_two_mul_innerPart ρ hker A hA (by omega) hF hirr hsd
  have hfix : Nat.card {u : U // ∀ a ∈ A, a u = u} = 2 ^ Module.finrank (ZMod 2) (fixOf A) := by
    rw [← natCard_eq_two_pow_finrank]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => mem_fixOf.symm)
  rw [hfix, natCard_eq_two_pow_finrank U]
  set n := Module.finrank (ZMod 2) U with hn
  by_cases hI : innerPart ρ hker A hA = ⊥
  ·
    have hcard2 : Nat.card ↥A ≤ 2 := by
      rw [hI, Subgroup.card_bot] at hcardA
      omega
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have haI : a ∉ innerPart ρ hker A hA := by
      rw [hI, Subgroup.mem_bot]
      exact ha1
    obtain ⟨t, ht, hrk⟩ := exists_transvection_of_outer ρ hker A hA hf hNat a haI
    rw [finrank_range_involution ρ (ne_one_of_isTransvection ht) (isTransvection_sq ht)] at hrk
    have hfa := finrank_range_add_finrank_fixOf_le (A := A) a.2
    have h2 : 2 ≤ Module.finrank (ZMod 2)
        (LinearMap.range ((a : U ≃ₗ[ZMod 2] U).toLinearMap - 1)) := by omega
    calc Nat.card ↥A * 2 ^ Module.finrank (ZMod 2) (fixOf A)
        ≤ 2 * 2 ^ (n - 2) := Nat.mul_le_mul hcard2 (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ < 2 ^ n := by
        rw [← pow_succ']
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  ·
    obtain ⟨⟨a, haI⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hI
    have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
    obtain ⟨t, ht2, hat⟩ := exists_lift_of_inner ρ hker A hA (by omega) hNat hirr a haI
    have ht1 : t ≠ 1 := by
      rintro rfl
      apply ha1
      apply Subtype.ext
      refine LinearEquiv.ext fun u => ?_
      rw [hat u, map_one]
      rfl
    have hrk : Module.finrank (ZMod 2)
        (LinearMap.range ((a : U ≃ₗ[ZMod 2] U).toLinearMap - 1)) = R := by
      have e : (a : U ≃ₗ[ZMod 2] U).toLinearMap - 1 = ρ t - 1 := by
        refine LinearMap.ext fun u => ?_
        simp [hat u]
      rw [e, finrank_range_involution ρ ht1 ht2]
    have hfa := finrank_range_add_finrank_fixOf_le (A := A) a.2
    have hAk : Nat.card ↥A ≤ 2 ^ (k + 1) := by
      rw [pow_succ']
      exact hcardA.trans (Nat.mul_le_mul_left 2 hk)
    calc Nat.card ↥A * 2 ^ Module.finrank (ZMod 2) (fixOf A)
        ≤ 2 ^ (k + 1) * 2 ^ (n - R) :=
          Nat.mul_le_mul hAk (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ < 2 ^ n := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end Excl

end B42SL3

end CFSG.Quasithin
