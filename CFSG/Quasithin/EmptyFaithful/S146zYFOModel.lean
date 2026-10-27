module

public import CFSG.Quasithin.Vol2.F134LieOddModel
public import CFSG.Quasithin.Vol2.F134LieOddMatrix

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

structure FiveModel (H : Subgroup (GL (Fin 3) K)) (M : Subgroup Kˣ) : Prop where
  mono : MonomialData H M
  diag : ∀ d : Fin 3 → Kˣ, diagHom 3 d ∈ H → ∀ i, d i ∈ M
  card5 : (Nat.card H).factorization 5 = (Nat.card M ^ 2).factorization 5
  five : 5 ∣ Nat.card M

namespace FiveModel

variable (h : FiveModel H M)
include h

theorem cube_eq_one_of_scalar {x : H} {c : Kˣ}
    (hc : (x : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c) : c ^ 3 = 1 := by
  have := h.mono.det_eq_one x x.2
  rw [hc, det_scalar] at this
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, this, Units.val_one])

theorem pow_three_of_mem_scal {x : H} (hx : x ∈ scal H) : x ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := mem_scal_iff.1 hx
  have h3 := h.cube_eq_one_of_scalar hc
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, h3, map_one, Subgroup.coe_one]

theorem eq_one_of_pow_five_of_mem_scal {x : H} (hx : x ∈ scal H) (h5 : x ^ 5 = 1) : x = 1 := by
  have h3 := h.pow_three_of_mem_scal hx
  calc x = (x ^ 3) ^ 2 * (x ^ 5)⁻¹ := by group
    _ = 1 := by rw [h3, h5]; simp

theorem commute_of_proj_commute {a b : H} (hab : proj H a * proj H b = proj H b * proj H a)
    (hb : b ^ 5 = 1) : a * b = b * a := by
  have hz : a * b * a⁻¹ * b⁻¹ ∈ scal H := OddModel.commutator_mem_scal hab
  set z := a * b * a⁻¹ * b⁻¹ with hzdef
  have hzb : a * b * a⁻¹ = z * b := by rw [hzdef]; group
  have hcomm : Commute z b := mem_scal_commute hz b
  have h1 : (a * b * a⁻¹) ^ 5 = 1 := by rw [conj_pow, hb, mul_one, mul_inv_cancel]
  have h2 : (a * b * a⁻¹) ^ 5 = z ^ 5 := by rw [hzb, hcomm.mul_pow, hb, mul_one]
  have hz5 : z ^ 5 = 1 := h2 ▸ h1
  have hz1 : z = 1 := h.eq_one_of_pow_five_of_mem_scal hz hz5
  calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
    _ = b * a := by rw [← hzdef, hz1, one_mul]

theorem mem_torus3_of_isDiag3 {g : GL (Fin 3) K} (hg : g ∈ H)
    (hd : IsDiag3 (g : Matrix (Fin 3) (Fin 3) K)) : g ∈ torus3 M := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := h.mono.det_eq_one g hg
  have hdiag := hd.eq_diagonal
  rw [hdiag, det_diagonal, Fin.prod_univ_three] at hdet
  have hne : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    have h2 := right_ne_zero_of_mul_eq_one hdet
    have h01 := left_ne_zero_of_mul_eq_one hdet
    intro i
    fin_cases i
    exacts [left_ne_zero_of_mul h01, right_ne_zero_of_mul h01, h2]
  set d : Fin 3 → Kˣ := fun i => Units.mk0 _ (hne i)
  have hgd : g = diagHom 3 d := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [coe_diagHom, hdiag]
    rfl
  have hprod : d 0 * d 1 * d 2 = 1 := Units.ext (by simpa [d] using hdet)
  rw [hgd] at hg ⊢
  exact (mem_torus3 M).2 ⟨d, h.diag d hg, hprod, rfl⟩

end FiveModel

@[expose] def omega5 (M : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) where
  carrier := {y | y ∈ torus3 M ∧ y ^ 5 = 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [Commute.mul_pow (torus3_comm M ha.1 hb.1), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow 5⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

@[expose] def pstd (H : Subgroup (GL (Fin 3) K)) (M : Subgroup Kˣ) : Subgroup (StatedProj H) :=
  ((omega5 M).comap H.subtype).map (proj H)

theorem mem_pstd {x : StatedProj H} :
    x ∈ pstd H M ↔ ∃ t : H, (t : GL (Fin 3) K) ∈ omega5 M ∧ proj H t = x := by
  simp only [pstd, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]

namespace FiveModel

variable (h : FiveModel H M)
include h

theorem exists_sylow_le_torus [Finite K] :
    ∃ S₀ : Sylow 5 H, (S₀ : Subgroup H) ≤ (torus3 M).subgroupOf H := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hNH : torus3 M ≤ H := torus3_le M h.mono
  set N' : Subgroup H := (torus3 M).subgroupOf H with hN'def
  have hN'card : Nat.card N' = Nat.card M ^ 2 := by
    rw [hN'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, card_torus3]
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 5 N'))
  have hS₀ := Sylow.card_eq_multiplicity S₀
  let S : Sylow 5 H := Sylow.ofCard ((S₀ : Subgroup N').map N'.subtype) (by
    rw [Subgroup.card_map_of_injective N'.subtype_injective, hS₀, hN'card, h.card5])
  have hSN : (S : Subgroup H) ≤ N' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  exact ⟨S, hSN⟩

theorem exists_conj_le_pstd [Finite K] {P : Subgroup (StatedProj H)} (hP : IsPGroup 5 P)
    (hexp : ∀ x ∈ P, x ^ 5 = 1) : ∃ g : StatedProj H, ∀ x ∈ P, g⁻¹ * x * g ∈ pstd H M := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S₀, hS₀⟩ := h.exists_sylow_le_torus
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedProj H)
    (Sylow.mapSurjective (proj_surjective (H := H)) S₀) R
  refine ⟨g, fun x hx => ?_⟩
  have hxR : x ∈ (((g • Sylow.mapSurjective (proj_surjective (H := H)) S₀ : Sylow 5 _) :
      Subgroup (StatedProj H))) := hg ▸ hPR hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxR
  have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e, Sylow.coe_mapSurjective] at hxR
  obtain ⟨t, ht, hty⟩ := hxR
  have htT : (t : GL (Fin 3) K) ∈ torus3 M := Subgroup.mem_subgroupOf.1 (hS₀ ht)
  have hy5 : (g⁻¹ * x * g) ^ 5 = 1 := by
    have := conj_pow (a := g⁻¹) (b := x) (i := 5)
    rw [inv_inv] at this
    rw [this, hexp x hx, mul_one, inv_mul_cancel]
  have ht5 : t ^ 5 ∈ scal H := by
    rw [← proj_eq_one_iff, map_pow]
    exact (hty ▸ hy5)
  have ht15 : (t ^ 5) ^ 3 = 1 := h.pow_three_of_mem_scal ht5
  refine mem_pstd.2 ⟨t ^ 6, ⟨?_, ?_⟩, ?_⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem htT 6
  · rw [Subgroup.coe_pow, ← pow_mul, show 6 * 5 = 5 * 3 * 2 by norm_num, pow_mul, pow_mul,
      ← Subgroup.coe_pow, ← Subgroup.coe_pow, ht15]
    simp
  · rw [map_pow, hty, show 6 = 5 + 1 by norm_num, pow_succ, hy5, one_mul]

end FiveModel

end FiveOdd

end CFSG.Quasithin.S146zY
