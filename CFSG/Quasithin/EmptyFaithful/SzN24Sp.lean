module

public import CFSG.Quasithin.EmptyFaithful.SzN24Gen
public import CFSG.Quasithin.EmptyFaithful.SzN2Sp
public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

namespace SzN24

section Sp

variable {F : Type} [Field F]

@[expose] def trSp (g : StatedSp 2 F) : F :=
  Matrix.trace (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))

theorem trSp_conj (x m : StatedSp 2 F) : trSp (x * m * x⁻¹) = trSp m := by
  unfold trSp
  have := Matrix.trace_units_conj (x : GL (Fin 2 ⊕ Fin 2) F) (((m : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
  simpa using this

theorem trSp_conjSp (H : SymplecticHigher.gsp 2 F) (m : StatedSp 2 F) :
    trSp (SymplecticHigher.conjSp 2 F H m) = trSp m := by
  unfold trSp
  rw [SymplecticHigher.coe_conjSp]
  exact Matrix.trace_units_conj (H : GL (Fin 2 ⊕ Fin 2) F) _

theorem trSp_fieldSp (σ : F ≃+* F) (m : StatedSp 2 F) :
    trSp (SymplecticHigher.fieldSp 2 F σ m) = σ (trSp m) := by
  unfold trSp
  rw [SymplecticHigher.coe_fieldSp]
  exact (AddMonoidHom.map_trace σ.toRingHom _).symm

@[expose] noncomputable def dSp (a : F) (ha : a ≠ 0) : StatedSp 2 F :=
  SymplecticTorusWeyl.torusHom (![Units.mk0 a ha, 1] : Fin 2 → Fˣ)

theorem trSp_dSp (a : F) (ha : a ≠ 0) : trSp (dSp a ha) = a + 1 + a⁻¹ + 1 := by
  unfold trSp dSp
  rw [SymplecticTorusWeyl.coe_torusHom]
  simp [Matrix.trace, Fin.sum_univ_two, Fintype.sum_sum_type, add_assoc]

theorem trSp_mul_torus {u : StatedSp 2 F} (hu : u ∈ SymplecticFlag.unipotent 2 F)
    (t : Fin 2 → Fˣ) :
    trSp (u * SymplecticTorusWeyl.torusHom t) = trSp (SymplecticTorusWeyl.torusHom t) := by
  obtain ⟨A, C, hA, hC, hg⟩ := SymplecticFlag.mem_unipotent.mp hu
  unfold trSp
  rw [Subgroup.coe_mul, Units.val_mul, SymplecticTorusWeyl.coe_torusHom, hg]
  have h1 : ∀ i, A i i = 1 := hA.2
  have h2 : ∀ i, (A⁻¹ : Matrix (Fin 2) (Fin 2) F) i i = 1 := hA.inv.2
  simp [Matrix.trace, Matrix.mul_diagonal, SymplecticFlag.blockMat, Fintype.sum_sum_type, h1, h2]

end Sp

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sp4_field_eq_one {Ŝ : Subgroup (StatedSp 2 F)} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (α : StatedSp 2 F ≃* StatedSp 2 F)
    (h2 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (StatedSp 2 F)), α b * b⁻¹ ∈ Ŝ)
    (σ : F ≃+* F) (hσ3 : ∀ a, σ (σ (σ a)) = a) (htr : ∀ g : StatedSp 2 F, trSp (α g) = σ (trSp g)) :
    σ = 1 := by
  have hU : IsSylowTwoOf (SymplecticFlag.unipotent 2 F) ⊤ := SzN2.isSylowTwoOf_unipotent
  obtain ⟨x, -, hx⟩ := B6.isSylowTwoOf_exists_conj hU hŜ
  have hmem : ∀ s, s ∈ Ŝ ↔ x⁻¹ * s * x ∈ SymplecticFlag.unipotent 2 F := by
    intro s
    rw [hx]
    constructor
    · rintro ⟨u, hu, rfl⟩
      show x⁻¹ * (x * u * x⁻¹) * x ∈ SymplecticFlag.unipotent 2 F
      rw [show x⁻¹ * (x * u * x⁻¹) * x = u by group]
      exact hu
    · intro hs
      refine ⟨x⁻¹ * s * x, hs, ?_⟩
      show x * (x⁻¹ * s * x) * x⁻¹ = s
      group
  refine eq_one_of_trace_eq hσ3 (fun a ha => ?_)
  have hd : dSp a ha ∈ Subgroup.normalizer
      ((SymplecticFlag.unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) := by
    rw [SymplecticHigher.normalizer_unipotent]
    exact SymplecticFlag.torus_le_borelSubgroup (SymplecticTorusWeyl.torusHom_mem_torus _)
  have hd' : x * dSp a ha * x⁻¹ ∈ Subgroup.normalizer (Ŝ : Set (StatedSp 2 F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [hmem, hmem]
    have h1 := Subgroup.mem_normalizer_iff.mp hd (x⁻¹ * s * x)
    have e : x⁻¹ * (x * dSp a ha * x⁻¹ * s * (x * dSp a ha * x⁻¹)⁻¹) * x =
        dSp a ha * (x⁻¹ * s * x) * (dSp a ha)⁻¹ := by group
    rw [e]
    exact h1
  have hs := (hmem _).mp (h2 _ hd')
  set u : StatedSp 2 F := x⁻¹ * (α (x * dSp a ha * x⁻¹) * (x * dSp a ha * x⁻¹)⁻¹) * x with hu
  have e2 : α (x * dSp a ha * x⁻¹) = x * (u * dSp a ha) * x⁻¹ := by
    rw [hu]
    group
  have h3 := htr (x * dSp a ha * x⁻¹)
  rw [e2, trSp_conj, dSp, trSp_mul_torus hs, ← dSp, trSp_conj, trSp_dSp] at h3
  rw [map_add, map_add, map_add, map_inv₀, map_one] at h3
  linear_combination -h3

theorem sp4_autRigid {Ŝ : Subgroup (StatedSp 2 F)} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (α : StatedSp 2 F ≃* StatedSp 2 F)
    (h2 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (StatedSp 2 F)), α b * b⁻¹ ∈ Ŝ)
    (h3 : ∀ m, α (α (α m)) = m) :
    ∃ x : StatedSp 2 F, ∀ m, α m = x * m * x⁻¹ := by
  have hbij : Function.Bijective (SymplecticFlag.proj 2 F) :=
    UnitaryHigher.proj_bijective_of_charTwo
  let e : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
    MulEquiv.ofBijective (SymplecticFlag.proj 2 F) hbij
  let α' : MulAut (StatedProj (StatedSp 2 F)) := e.symm.trans (α.trans e)
  have hα' : ∀ g, α' (SymplecticFlag.proj 2 F g) = SymplecticFlag.proj 2 F (α g) := fun g => by
    show e (α (e.symm (e g))) = e (α g)
    rw [MulEquiv.symm_apply_apply]
  have hα'3 : α' ^ 3 = 1 := by
    ext p
    obtain ⟨g, rfl⟩ := hbij.2 p
    simp [pow_succ, hα', h3]
  by_cases hD : α' ∈ (SymplecticHigher.conjAut 2 F).range
  · obtain ⟨H, hH⟩ := hD
    obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp H
    refine ⟨s, fun m => ?_⟩
    apply hbij.1
    rw [← hα', ← hH, hs, SymplecticHigher.conjAut_proj]
    congr 1
  · exfalso
    obtain ⟨σ, hσ, H, hH⟩ :=
      CFSG.RankThree.PartTwo.KFacts.sp4_even_order_three_field_descent α' hα'3 hD
    have hσ3 : ∀ a, σ (σ (σ a)) = a := by
      have h1 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
      intro a
      have := congrArg (fun τ : F ≃+* F => τ a) h1
      simpa [pow_succ] using this
    have htr : ∀ g : StatedSp 2 F, trSp (α g) = σ (trSp g) := by
      intro g
      have hg : α g = SymplecticHigher.conjSp 2 F H (SymplecticHigher.fieldSp 2 F σ
          (SymplecticHigher.conjSp 2 F H⁻¹ g)) := by
        apply hbij.1
        rw [← hα', hH]
        simp only [MulAut.mul_apply, ← map_inv, SymplecticHigher.conjAut_proj,
          SymplecticHigher.fieldAut_proj]
      rw [hg, trSp_conjSp, trSp_fieldSp, trSp_conjSp]
    have hσ1 := sp4_field_eq_one hŜ α h2 σ hσ3 htr
    rw [hσ1, orderOf_one] at hσ
    omega

end Main

section Glue

theorem krig_of_sp4 {Ω : Type} [Group Ω] {K : Subgroup Ω} {F : Type} [Field F] [Finite F] {e : ℕ}
    (hF : Nat.card F = 2 ^ e) (iso : ↥K ≃* ↥(StatedSp 2 F)) : SzN22.KRig K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ e := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hcp : CharP F 2 := charP_of_card_eq_prime_pow hcard
  exact krig_of_autRigid iso (fun Ŝ α hŜ _ h2 h3 _ => sp4_autRigid hŜ α h2 h3)

end Glue

end SzN24

end CFSG.Quasithin
