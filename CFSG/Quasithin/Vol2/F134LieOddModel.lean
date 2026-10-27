module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.SectionRank.OddCover.ThreeRank

public section

namespace CFSG.Quasithin.F134.LieOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

abbrev scal (H : Subgroup (GL (Fin 3) K)) : Subgroup H := (StatedScalars (Fin 3) K).subgroupOf H

abbrev proj (H : Subgroup (GL (Fin 3) K)) : H →* StatedProj H := QuotientGroup.mk' (scal H)

structure OddModel (H : Subgroup (GL (Fin 3) K)) (M : Subgroup Kˣ) : Prop where
  mono : MonomialData H M
  diag : ∀ d : Fin 3 → Kˣ, diagHom 3 d ∈ H → ∀ i, d i ∈ M
  mu3 : ∀ c : Kˣ, c ^ 3 = 1 → c ∈ M
  card3 : (Nat.card H).factorization 3 = (3 * Nat.card M ^ 2).factorization 3
  sixteen : 16 ∣ Nat.card H
  two : (2 : K) ≠ 0
  three : (3 : K) ≠ 0
  prim : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1

variable {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

theorem mem_scal_iff {x : H} :
    x ∈ scal H ↔ ∃ c : Kˣ, (x : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

theorem proj_eq_one_iff {x : H} : proj H x = 1 ↔ x ∈ scal H :=
  QuotientGroup.eq_one_iff x

theorem proj_eq_proj_iff {x y : H} : proj H x = proj H y ↔ x⁻¹ * y ∈ scal H :=
  QuotientGroup.eq

theorem proj_surjective : Function.Surjective (proj H) := QuotientGroup.mk'_surjective _

theorem det_scalar (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = (c : K) ^ 3 := by
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

namespace OddModel

variable (h : OddModel H M)
include h

theorem det_eq_one (x : H) : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  h.mono.det_eq_one x x.2

theorem cube_eq_one_of_scalar {x : H} {c : Kˣ}
    (hc : (x : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c) : c ^ 3 = 1 := by
  have := h.det_eq_one x
  rw [hc, det_scalar] at this
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, this, Units.val_one])

theorem scalar_mem {c : Kˣ} (hc : c ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H := by
  rw [scalar_eq_diagHom]
  exact h.mono.diag_mem _ (fun _ => h.mu3 c hc) (by rw [← pow_three', hc])

theorem pow_three_of_mem_scal {x : H} (hx : x ∈ scal H) : x ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := mem_scal_iff.1 hx
  have h3 := h.cube_eq_one_of_scalar hc
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, h3, map_one, Subgroup.coe_one]

end OddModel

theorem mem_scal_commute {x : H} (hx : x ∈ scal H) (y : H) : x * y = y * x := by
  obtain ⟨c, hc⟩ := mem_scal_iff.1 hx
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (scalar_commute c y).eq

namespace OddModel

variable (h : OddModel H M)
include h

theorem card_rootsOfUnity_three : Nat.card (rootsOfUnity 3 K) = 3 := by
  obtain ⟨ω, hω3, hω1⟩ := h.prim
  have hprim : IsPrimitiveRoot ω 3 := by
    refine IsPrimitiveRoot.mk_of_lt ω (by norm_num) hω3 fun l hl0 hl3 => ?_
    interval_cases l
    · rwa [pow_one]
    · intro h2
      apply hω1
      rw [show ω = ω ^ 3 * (ω ^ 2)⁻¹ by group, hω3, h2, inv_one, one_mul]
  exact hprim.card_rootsOfUnity'

theorem card_scal [Finite K] : Nat.card (scal H) = 3 := by
  have hcard := h.card_rootsOfUnity_three
  let φ : rootsOfUnity 3 K → scal H := fun c =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (c : Kˣ), h.scalar_mem ((mem_rootsOfUnity _ _).1
      c.2)⟩, mem_scal_iff.2 ⟨c, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro c c' hcc'
      have h1 := congrArg (fun x : scal H => (((x : H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        0 0) hcc'
      simp only [φ, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h1
      exact Subtype.ext (Units.ext h1)
    · rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ := mem_scal_iff.1 hx
      exact ⟨⟨c, (mem_rootsOfUnity _ _).2 (h.cube_eq_one_of_scalar hc)⟩,
        Subtype.ext (Subtype.ext hc.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), hcard]

theorem card_comap [Finite K] (Q : Subgroup (StatedProj H)) :
    Nat.card (Q.comap (proj H)) = 3 * Nat.card Q := by
  have := QuotientGroup.card_preimage_mk (scal H) (Q : Set (StatedProj H))
  rw [h.card_scal] at this
  exact this

theorem exists_involution_lift {s : StatedProj H} (hs : s ^ 2 = 1) :
    ∃ x : H, proj H x = s ∧ x ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := proj_surjective s
  have hx2 : x ^ 2 ∈ scal H := proj_eq_one_iff.1 (by rw [map_pow]; exact hs)
  refine ⟨x * x ^ 2, ?_, ?_⟩
  · rw [map_mul, proj_eq_one_iff.2 hx2, mul_one]
  · have := h.pow_three_of_mem_scal hx2
    rw [← pow_mul] at this
    rw [show (x * x ^ 2) ^ 2 = x ^ (2 * 3) by group]
    exact this

theorem eq_one_of_sq_of_mem_scal {δ : H} (hδ : δ ∈ scal H) (h2 : δ ^ 2 = 1) : δ = 1 := by
  have h3 := h.pow_three_of_mem_scal hδ
  rw [show δ = δ ^ 3 * (δ ^ 2)⁻¹ by group, h3, h2, inv_one, one_mul]

theorem conj_eq_of_involution {a b : H} (hb : b ^ 2 = 1)
    (hab : proj H (a * b * a⁻¹) = proj H b) : a * b * a⁻¹ = b := by
  set δ := b⁻¹ * (a * b * a⁻¹) with hδdef
  have hδ : δ ∈ scal H := proj_eq_proj_iff.1 hab.symm
  have hδ2 : δ ^ 2 = 1 := by
    have e1 : (a * b * a⁻¹) ^ 2 = 1 := by
      rw [show (a * b * a⁻¹) ^ 2 = a * b ^ 2 * a⁻¹ by rw [sq, sq]; group, hb, mul_one,
        mul_inv_cancel]
    have e2 : a * b * a⁻¹ = b * δ := by rw [hδdef]; group
    have e3 : (b * δ) ^ 2 = δ ^ 2 := by
      calc (b * δ) ^ 2 = b * (δ * b) * δ := by rw [sq]; group
        _ = b * (b * δ) * δ := by rw [mem_scal_commute hδ b]
        _ = b ^ 2 * δ ^ 2 := by rw [sq, sq]; group
        _ = δ ^ 2 := by rw [hb, one_mul]
    rw [← e3, ← e2, e1]
  have := h.eq_one_of_sq_of_mem_scal hδ hδ2
  rw [hδdef] at this
  rw [← mul_left_cancel_iff (a := b⁻¹), this, inv_mul_cancel]

theorem conj_eq_of_involution' {a b : H} (ha : a ^ 2 = 1)
    (hab : proj H (a * b * a⁻¹) = proj H b) : a * b * a⁻¹ = b := by
  set δ := b⁻¹ * (a * b * a⁻¹) with hδdef
  have hδ : δ ∈ scal H := proj_eq_proj_iff.1 hab.symm
  have e2 : a * b * a⁻¹ = b * δ := by rw [hδdef]; group
  have hainv : a⁻¹ = a := by
    rw [← mul_left_cancel_iff (a := a), mul_inv_cancel, ← sq, ha]
  have haa : a * a = 1 := by rw [← sq, ha]
  have hδ2 : δ ^ 2 = 1 := by
    have e3 : a * (a * b * a⁻¹) * a⁻¹ = b := by
      calc a * (a * b * a⁻¹) * a⁻¹ = (a * a) * b * (a * a)⁻¹ := by group
        _ = b := by rw [haa, one_mul, inv_one, mul_one]
    have e4 : a * δ * a⁻¹ = δ := by rw [← mem_scal_commute hδ a]; group
    rw [e2, show a * (b * δ) * a⁻¹ = (a * b * a⁻¹) * (a * δ * a⁻¹) by group, e2, e4,
      mul_assoc, ← sq] at e3
    have := congrArg (b⁻¹ * ·) e3
    simpa using this
  have := h.eq_one_of_sq_of_mem_scal hδ hδ2
  rw [hδdef] at this
  rw [← mul_left_cancel_iff (a := b⁻¹), this, inv_mul_cancel]

omit h in
theorem commutator_mem_scal {a b : H} (hab : proj H a * proj H b = proj H b * proj H a) :
    a * b * a⁻¹ * b⁻¹ ∈ scal H := by
  rw [← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
  group

theorem exists_conj_le_torus3_sup_cyc [Finite K] {E : Subgroup H} (hE : IsPGroup 3 E) :
    ∃ g : H, ∀ x ∈ E,
      ((g⁻¹ * x * g : H) : GL (Fin 3) K) ∈ torus3 M ⊔ Subgroup.zpowers cycGL := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup (GL (Fin 3) K) := torus3 M ⊔ Subgroup.zpowers cycGL with hNdef
  have hNH : N ≤ H := sup_le (torus3_le M h.mono) (Subgroup.zpowers_le.2 h.mono.cyc_mem)
  set N' : Subgroup H := N.subgroupOf H with hN'def
  have hN'card : Nat.card N' = 3 * Nat.card M ^ 2 := by
    rw [hN'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, card_torus3_sup_cyc]
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 N'))
  have hS₀ := Sylow.card_eq_multiplicity S₀
  let S : Sylow 3 H := Sylow.ofCard ((S₀ : Subgroup N').map N'.subtype) (by
    rw [Subgroup.card_map_of_injective N'.subtype_injective, hS₀, hN'card, h.card3])
  have hSN : (S : Subgroup H) ≤ N' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨S', hES'⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S S'
  refine ⟨g, fun x hx => ?_⟩
  have hyS : x ∈ ((g • S : Sylow 3 H) : Subgroup H) := hg ▸ hES' hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
  have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e] at hyS
  exact Subgroup.mem_subgroupOf.1 (hSN hyS)

end OddModel

end CFSG.Quasithin.F134.LieOdd
