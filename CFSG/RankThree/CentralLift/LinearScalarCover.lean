module

public import CFSG.RankThree.CentralLift.LinearSplitting

public section

namespace CFSG.RankThree.CentralLift

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars mem_scalars projectiveSL proj
  proj_surjective proj_eq_one_iff)
open scoped commutatorElement

variable {k : Type} [Field k] {n : ℕ}

theorem commutatorElement_mul_center {G : Type*} [Group G] {z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) (x y : G) :
    ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have hw' := Subgroup.mem_center_iff.1 hw
  have h1 : ⁅z, w * y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hz' _).symm
  have h2 : ⁅x, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hw' x)
  rw [commutatorElement_mul_left_eq_conj_mul, h1, mul_one,
    commutatorElement_mul_right_eq_mul_conj, h2, one_mul, ← hw' ⁅x, y⁆, mul_inv_cancel_right,
    ← hz' ⁅x, y⁆, mul_inv_cancel_right]

section Scalars

variable (k n) in
@[expose] noncomputable def scalarEntry (z : Fin n) : scalars n k →* k where
  toFun A := ((A : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) z z
  map_one' := by simp
  map_mul' A B := by
    obtain ⟨c, -, hc⟩ := mem_scalars.1 A.2
    obtain ⟨d, -, hd⟩ := mem_scalars.1 B.2
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc, hd]
    simp

theorem scalarEntry_injective (z : Fin n) : Function.Injective (scalarEntry k n z) := by
  intro A B h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 A.2
  obtain ⟨d, -, hd⟩ := mem_scalars.1 B.2
  have h' : (c : k) = d := by
    have h2 : ((A : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) z z =
        ((B : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) z z := h
    rw [hc, hd] at h2
    simpa using h2
  exact Subtype.ext (Subtype.ext (by rw [hc, hd, h']))

variable [Finite k]

theorem isCyclic_scalars (z : Fin n) : IsCyclic (scalars n k) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  exact isCyclic_of_injective_ringHom (scalarEntry k n z) (scalarEntry_injective z)

theorem card_scalars_dvd (z : Fin n) : Nat.card (scalars n k) ∣ n := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have := isCyclic_scalars (k := k) z
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun A => ?_
  obtain ⟨c, hcn, hc⟩ := mem_scalars.1 A.2
  refine Subtype.ext (Subtype.ext ?_)
  rw [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow,
    ← Units.val_pow_eq_pow_val, hcn]
  simp

omit [Finite k] in
theorem card_scalars_dvd_card_sub_one (z : Fin n) : Nat.card (scalars n k) ∣ Nat.card k - 1 := by
  rw [← Nat.card_units k]
  refine Subgroup.card_dvd_of_injective (scalarEntry k n z).toHomUnits fun A B h => ?_
  exact scalarEntry_injective z (congrArg Units.val h)

end Scalars

section Cover

variable [Finite k] {L : Type*} [Group L] {η : L →* projectiveSL n k}

theorem exact_scalar_cover_map_of_comp_eq [Group.IsPerfect L] (hn : 1 ≤ n)
    (hC : η.ker ≤ Subgroup.center L)
    {φ : SpecialLinearGroup (Fin n) k →* L} (hφ : η.comp φ = proj n k) :
    Function.Surjective φ ∧ φ.ker ≤ scalars n k ∧ (scalars n k).map φ = η.ker ∧
      (∃ e : SpecialLinearGroup (Fin n) k ⧸ φ.ker ≃* L,
        ∀ h : SpecialLinearGroup (Fin n) k, e (h : SpecialLinearGroup (Fin n) k ⧸ φ.ker) = φ h ∧
          η (e (h : SpecialLinearGroup (Fin n) k ⧸ φ.ker)) = proj n k h) ∧
      Nonempty (η.ker ≃* scalars n k ⧸ φ.ker.subgroupOf (scalars n k)) ∧
      IsCyclic η.ker ∧ Nat.card η.ker ∣ Nat.gcd n (Nat.card k - 1) := by
  have hηφ : ∀ h, η (φ h) = proj n k h := fun h => DFunLike.congr_fun hφ h
  have hLC : ∀ l : L, ∃ c ∈ η.ker, ∃ h, l = c * φ h := by
    intro l
    obtain ⟨h, hh⟩ := proj_surjective n k (η l)
    refine ⟨l * (φ h)⁻¹, ?_, h, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hηφ, hh, mul_inv_cancel]
  have hsurj : Function.Surjective φ := by
    have hcomm : commutator L ≤ φ.range := by
      rw [commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨a, b, rfl⟩
      obtain ⟨c, hc, x, rfl⟩ := hLC a
      obtain ⟨d, hd, y, rfl⟩ := hLC b
      rw [commutatorElement_mul_center (hC hc) (hC hd), ← map_commutatorElement]
      exact ⟨_, rfl⟩
    have htop : commutator L = ⊤ := Group.isPerfect_def.1 inferInstance
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← htop]
    exact hcomm
  have hker : φ.ker ≤ scalars n k := by
    intro h hh
    have h1 := hηφ h
    rw [MonoidHom.mem_ker.1 hh, map_one] at h1
    exact proj_eq_one_iff.1 h1.symm
  have hmapD : (scalars n k).map φ = η.ker := by
    apply le_antisymm
    · rintro _ ⟨d, hd, rfl⟩
      rw [MonoidHom.mem_ker, hηφ, proj_eq_one_iff]
      exact hd
    · intro c hc
      obtain ⟨h, rfl⟩ := hsurj c
      refine ⟨h, proj_eq_one_iff.1 ?_, rfl⟩
      rw [← hηφ]
      exact hc
  have hDC : ∀ d : scalars n k, φ d ∈ η.ker := fun d => hmapD ▸ Subgroup.mem_map_of_mem φ d.2
  let ψ : scalars n k →* η.ker := (φ.comp (scalars n k).subtype).codRestrict η.ker hDC
  have hψ : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    rw [← hmapD] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact ⟨⟨d, hd⟩, rfl⟩
  have hψker : ψ.ker = φ.ker.subgroupOf (scalars n k) := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have z : Fin n := ⟨0, hn⟩
  have hcyc : IsCyclic (scalars n k) := isCyclic_scalars z
  refine ⟨hsurj, hker, hmapD, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hsurj,
    fun h => ⟨rfl, hηφ h⟩⟩, ⟨((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm⟩,
    isCyclic_of_surjective ψ hψ, ?_⟩
  exact (Subgroup.card_dvd_of_surjective hψ).trans
    (Nat.dvd_gcd (card_scalars_dvd z) (card_scalars_dvd_card_sub_one z))

end Cover

theorem odd_field_linear_perfect_central_large_prime_exact_scalar_cover_map {p ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = ℓ ^ f) {n : ℕ} (hn : 2 ≤ n) {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] (η : L →* projectiveSL n k) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃! φ : SpecialLinearGroup (Fin n) k →* L, η.comp φ = proj n k) ∧
    ∀ φ : SpecialLinearGroup (Fin n) k →* L, η.comp φ = proj n k →
      Function.Surjective φ ∧ φ.ker ≤ scalars n k ∧ (scalars n k).map φ = η.ker ∧
      (∃ e : SpecialLinearGroup (Fin n) k ⧸ φ.ker ≃* L,
        ∀ h : SpecialLinearGroup (Fin n) k, e (h : SpecialLinearGroup (Fin n) k ⧸ φ.ker) = φ h ∧
          η (e (h : SpecialLinearGroup (Fin n) k ⧸ φ.ker)) = proj n k h) ∧
      Nonempty (η.ker ≃* scalars n k ⧸ φ.ker.subgroupOf (scalars n k)) ∧
      IsCyclic η.ker ∧ Nat.card η.ker ∣ Nat.gcd n (ℓ ^ f - 1) := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fintype k := Fintype.ofFinite k
  set P := ((proj n k).comp (MonoidHom.fst (SpecialLinearGroup (Fin n) k) L)).eqLocus
    (η.comp (MonoidHom.snd (SpecialLinearGroup (Fin n) k) L)) with hP
  set ρ := (MonoidHom.fst (SpecialLinearGroup (Fin n) k) L).comp P.subtype with hρ
  have hmemP : ∀ y : SpecialLinearGroup (Fin n) k × L, y ∈ P ↔ proj n k y.1 = η y.2 :=
    fun _ => Iff.rfl
  have hρs : Function.Surjective ρ := by
    intro h
    obtain ⟨l, hl⟩ := hη (proj n k h)
    exact ⟨⟨(h, l), (hmemP _).2 hl.symm⟩, rfl⟩
  have hρker : ∀ y : P, y ∈ ρ.ker ↔ (y : SpecialLinearGroup (Fin n) k × L).1 = 1 :=
    fun _ => Iff.rfl
  have hkerη : ∀ y : P, y ∈ ρ.ker → (y : SpecialLinearGroup (Fin n) k × L).2 ∈ η.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, ← (hmemP _).1 y.2, (hρker y).1 hy, map_one]
  have hA : ρ.ker ≤ Subgroup.center P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hc := Subgroup.mem_center_iff.1 (hC (hkerη y hy))
      (z : SpecialLinearGroup (Fin n) k × L).2
    have h1 : (y : SpecialLinearGroup (Fin n) k × L).1 = 1 := (hρker y).1 hy
    refine Subtype.ext (Prod.ext ?_ hc)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Prod.fst_mul, Prod.fst_mul, h1, mul_one, one_mul]
  have hAp : IsPGroup p ρ.ker := by
    refine hCp.of_injective
      ((MonoidHom.snd _ L).comp (P.subtype.comp ρ.ker.subtype) |>.codRestrict η.ker
        fun y => hkerη y y.2) fun y z hyz => ?_
    have h2 : (y : P).1.2 = (z : P).1.2 := congrArg Subtype.val hyz
    exact Subtype.ext (Subtype.ext (Prod.ext (((hρker y).1 y.2).trans ((hρker z).1 z.2).symm)
      h2))
  obtain ⟨⟨s, hs, hsu⟩, -⟩ :=
    LinearRoots.odd_field_linear_central_large_prime_extension_splitting hp hp3 hℓ hℓodd hf hk
      hn ρ hρs hA hAp
  have hsec : ∀ φ : SpecialLinearGroup (Fin n) k →* L, η.comp φ = proj n k →
      ∃ σ : SpecialLinearGroup (Fin n) k →* P, ρ.comp σ = MonoidHom.id _ ∧
        (MonoidHom.snd _ L).comp (P.subtype.comp σ) = φ := by
    intro φ hφ
    refine ⟨((MonoidHom.id _).prod φ).codRestrict P fun h => ?_, ?_, ?_⟩
    · rw [hmemP]
      exact (DFunLike.congr_fun hφ h).symm
    · ext h
      rfl
    · ext h
      rfl
  refine ⟨⟨(MonoidHom.snd _ L).comp (P.subtype.comp s), ?_, fun φ hφ => ?_⟩, fun φ hφ => ?_⟩
  · ext h
    have hh := DFunLike.congr_fun hs h
    change ((s h : P) : SpecialLinearGroup (Fin n) k × L).1 = h at hh
    change η ((s h : P) : SpecialLinearGroup (Fin n) k × L).2 = proj n k h
    rw [← (hmemP _).1 (s h).2, hh]
  · obtain ⟨σ, hσ, rfl⟩ := hsec φ hφ
    rw [hsu σ hσ]
  · rw [← hk]
    exact exact_scalar_cover_map_of_comp_eq (by omega) hC hφ

end CFSG.RankThree.CentralLift
