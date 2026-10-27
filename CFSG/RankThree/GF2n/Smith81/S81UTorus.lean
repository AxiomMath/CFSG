module

public import CFSG.RankThree.GF2n.Smith81.S81UFam
public import CFSG.RankThree.GF2n.Smith81.S81NUG
public import CFSG.RankThree.GF2n.Smith81.S81NComm

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

theorem exists_nonzero_fixed {R A : Type*} [Semiring R] [AddCommGroup A] [Module R A] [Finite A]
    (hA2 : ∀ a : A, a + a = 0) (S : AddSubgroup A) (hS : S ≠ ⊥) (Y : Set (A ≃ₗ[R] A))
    (hY : ∀ g ∈ Subgroup.closure Y, g ^ 4 = 1) (hYS : ∀ y ∈ Y, ∀ s ∈ S, y s ∈ S) :
    ∃ s ∈ S, s ≠ 0 ∧ ∀ y ∈ Y, y s = s := by
  have hstab : ∀ g ∈ Subgroup.closure Y, ∀ s ∈ S, g s ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hYS x hx
    | one =>
      intro s hs
      exact hs
    | mul x y _ _ hx hy =>
      intro s hs
      rw [LinearEquiv.mul_apply]
      exact hx _ (hy s hs)
    | inv x hx ih =>
      intro s hs
      have e : x * (x * (x * x)) = x ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have hxinv : x⁻¹ = x * (x * x) := inv_eq_of_mul_eq_one_right (e.trans (hY x hx))
      rw [hxinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      exact ih _ (ih _ (ih _ hs))
  have hG : IsPGroup 2 (Subgroup.closure Y) := by
    refine isPGroup_iff_pow_pow_eq_one.2 fun g => ⟨2, ?_⟩
    have h := hY (g : A ≃ₗ[R] A) g.2
    apply Subtype.ext
    simpa using h
  letI act : MulAction (Subgroup.closure Y) S :=
    { smul := fun g s => ⟨(g : A ≃ₗ[R] A) s.1, hstab (g : A ≃ₗ[R] A) g.2 s.1 s.2⟩
      one_smul := fun s => Subtype.ext (by
        show (1 : A ≃ₗ[R] A) s.1 = s.1
        rfl)
      mul_smul := fun g g' s => Subtype.ext (by
        show ((g : A ≃ₗ[R] A) * (g' : A ≃ₗ[R] A)) s.1 = (g : A ≃ₗ[R] A) ((g' : A ≃ₗ[R] A) s.1)
        rfl) }
  obtain ⟨t, ht⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hS
  have hord : addOrderOf t = 2 :=
    addOrderOf_eq_prime (p := 2)
      (by rw [two_nsmul]; exact Subtype.ext (hA2 t.1)) ht
  have hdvd : 2 ∣ Nat.card S := by
    have h := addOrderOf_dvd_natCard t
    rwa [hord] at h
  have ha : (0 : S) ∈ MulAction.fixedPoints (Subgroup.closure Y) S := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    exact map_zero (g : A ≃ₗ[R] A)
  obtain ⟨b, hb, hab⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥S) hdvd ha
  refine ⟨b.1, b.2, fun h => hab (Subtype.ext h.symm), fun y hy => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.1 hb ⟨y, Subgroup.subset_closure hy⟩)

theorem diagGL_unitary_hyp (hσ : ∀ c, σ (σ c) = c) (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0)
    (hu : ∀ i, σ (d i) * d (partner i) = 1) :
    conjTr σ ((diagGL d hd : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * hypGram F *
      ((diagGL d hd : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = hypGram F := by
  have hC : conjTr σ (Matrix.diagonal d) = Matrix.diagonal (fun i => σ (d i)) := by
    ext i j
    rw [conjTr_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [diagGL_val, hC]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hypGram_apply]
  by_cases h : j = partner i
  · subst h
    simpa using hu i
  · simp [h]

@[expose] noncomputable def dtor (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, σ (d i) * d (partner i) = 1)
    (hdet : ∏ i, d i = 1) : SUid σ 6 :=
  ⟨frameGL σ ω hω * diagGL d hd * (frameGL σ ω hω)⁻¹,
    frame_conj_mem_SUid hσ.invol hω (by rw [det_diagGL, hdet]) (diagGL_unitary_hyp hσ.invol d hd hu)⟩

@[expose] noncomputable def gLongC (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (a : Fin 6)
    (c : F) (hc : σ c = c) : SUid σ 6 :=
  ⟨frameGL σ ω hω * transvGL F a (partner a) (partner_ne a).symm c * (frameGL σ ω hω)⁻¹,
    frameConj_long_mem hσ hω a hc⟩

private theorem h72_gShort_val (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (hab : a ≠ b) (hb : b ≠ partner a) (c : F) :
    ((gShort hσ hω hab hb c : SUid σ 6) : GL (Fin 6) F) =
      frameGL σ ω hω * (transvGL F a b hab c *
        transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)) * (frameGL σ ω hω)⁻¹ :=
  rfl

private theorem h72_comm_conj {G : Type*} [Group G] (S x y : G) :
    ⁅S * x * S⁻¹, S * y * S⁻¹⁆ = S * ⁅x, y⁆ * S⁻¹ := by
  simp only [commutatorElement_def]
  group

private theorem h72_coe_comm {G : Type*} [Group G] {H : Subgroup G} (x y : H) :
    ((⁅x, y⁆ : H) : G) = ⁅(x : G), (y : G)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

private theorem h72_dtor_val (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, σ (d i) * d (partner i) = 1)
    (hdet : ∏ i, d i = 1) :
    ((dtor hσ hω d hd hu hdet : SUid σ 6) : GL (Fin 6) F) =
      frameGL σ ω hω * diagGL d hd * (frameGL σ ω hω)⁻¹ :=
  rfl

private theorem h72_key (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0)
    (hu : ∀ i, σ (d i) * d (partner i) = 1) {a b : Fin 6} (hab : a ≠ b) (c : F) :
    ⁅diagGL d hd, transvGL F a b hab c *
        transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)⁆ =
      transvGL F a b hab ((d a / d b - 1) * c) *
        transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ ((d a / d b - 1) * c)) := by
  have hinv : ∀ i, σ (d i) = (d (partner i))⁻¹ := fun i => eq_inv_of_mul_eq_one_left (hu i)
  have hratio : d (partner b) / d (partner a) = σ (d a / d b) := by
    rw [map_div₀, hinv a, hinv b, inv_div_inv]
  have hpar : (d (partner b) / d (partner a) - 1) * σ c = σ ((d a / d b - 1) * c) := by
    rw [hratio, map_mul, map_sub, map_one]
  have h1 := diagGL_comm_transvGL d hd a b hab c
  have h2 := diagGL_comm_transvGL d hd (partner b) (partner a) (partner_ne_partner hab) (σ c)
  rw [hpar] at h2
  have hcomm := transvGL_commute a b (partner b) (partner a) hab (partner_ne_partner hab)
    (partner_ne b).symm (partner_ne a) c (σ ((d a / d b - 1) * c))
  have hsplit : ⁅diagGL d hd, transvGL F a b hab c *
        transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)⁆ =
      ⁅diagGL d hd, transvGL F a b hab c⁆ * (transvGL F a b hab c *
        ⁅diagGL d hd, transvGL F (partner b) (partner a) (partner_ne_partner hab) (σ c)⁆ *
        (transvGL F a b hab c)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hsplit, h1, h2, hcomm]
  group

theorem comm_dtor_gShort (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    (d : Fin 6 → F) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, σ (d i) * d (partner i) = 1)
    (hdet : ∏ i, d i = 1) {a b : Fin 6} (hab : a ≠ b) (hb : b ≠ partner a) (c : F) :
    ⁅dtor hσ hω d hd hu hdet, gShort hσ hω hab hb c⁆ =
      gShort hσ hω hab hb ((d a / d b - 1) * c) := by
  apply Subtype.ext
  rw [h72_coe_comm, h72_dtor_val, h72_gShort_val, h72_gShort_val, h72_comm_conj,
    h72_key d hd hu hab c]

theorem exists_two_group_conj (Sf : GL (Fin 6) F) (lev : Fin 6 → ℕ) (hlev : ∀ i, lev i ≤ 3) :
    ∃ H : Subgroup (GL (Fin 6) F),
      (∀ (i j : Fin 6) (hij : i ≠ j) (c : F), lev i < lev j →
        Sf * transvGL F i j hij c * Sf⁻¹ ∈ H) ∧ ∀ g ∈ H, g ^ 4 = 1 := by
  obtain ⟨H₀, hgens, h4⟩ := exists_UGrp (K := F) lev hlev
  refine ⟨H₀.map (MulAut.conj Sf).toMonoidHom, ?_, ?_⟩
  · intro i j hij c hlt
    exact Subgroup.mem_map_of_mem (MulAut.conj Sf).toMonoidHom (hgens i j hij c hlt)
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← map_pow, h4 x hx, map_one]

end CFSG.RankThree.GF2n.Smith81.U6Cube
