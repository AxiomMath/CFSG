module

public import CFSG.Quasithin.Vol2.F134LieOddModel
public import CFSG.Quasithin.Vol2.F134LieOddMatrix

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ} {p : ℕ}

structure PModel (p : ℕ) (H : Subgroup (GL (Fin 3) K)) (M : Subgroup Kˣ) : Prop where
  mono : MonomialData H M
  diag : ∀ d : Fin 3 → Kˣ, diagHom 3 d ∈ H → ∀ i, d i ∈ M
  cardp : (Nat.card H).factorization p = (Nat.card M ^ 2).factorization p
  dvd : p ∣ Nat.card M

theorem exists_exp_three_dvd (hp : p.Prime) (hp3 : p ≠ 3) : ∃ c : ℕ, 3 ∣ c ∧ c % p = 1 := by
  have hp1 := hp.one_lt
  have h3 : ¬ 3 ∣ p := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h).symm
  have : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases this with h | h
  · exact ⟨1 + p * 2, by omega, by rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hp1⟩
  · exact ⟨1 + p * 1, by omega, by rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hp1⟩

namespace PModel

variable (h : PModel p H M)
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

theorem eq_one_of_pow_of_mem_scal [hp : Fact p.Prime] (hp3 : p ≠ 3) {x : H} (hx : x ∈ scal H)
    (hxp : x ^ p = 1) : x = 1 := by
  have h3 := h.pow_three_of_mem_scal hx
  have hd : orderOf x ∣ Nat.gcd 3 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hxp)
  have hg : Nat.gcd 3 p = 1 := (Nat.coprime_primes Nat.prime_three hp.out).2 (Ne.symm hp3)
  rw [hg] at hd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)

theorem commute_of_proj_commute [Fact p.Prime] (hp3 : p ≠ 3) {a b : H}
    (hab : proj H a * proj H b = proj H b * proj H a) (hb : b ^ p = 1) : a * b = b * a := by
  have hz : a * b * a⁻¹ * b⁻¹ ∈ scal H := OddModel.commutator_mem_scal hab
  set z := a * b * a⁻¹ * b⁻¹ with hzdef
  have hzb : a * b * a⁻¹ = z * b := by rw [hzdef]; group
  have hcomm : Commute z b := mem_scal_commute hz b
  have h1 : (a * b * a⁻¹) ^ p = 1 := by rw [conj_pow, hb, mul_one, mul_inv_cancel]
  have h2 : (a * b * a⁻¹) ^ p = z ^ p := by rw [hzb, hcomm.mul_pow, hb, mul_one]
  have hzp : z ^ p = 1 := h2 ▸ h1
  have hz1 : z = 1 := h.eq_one_of_pow_of_mem_scal hp3 hz hzp
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

end PModel

@[expose] def omegaP (p : ℕ) (M : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) where
  carrier := {y | y ∈ torus3 M ∧ y ^ p = 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [Commute.mul_pow (torus3_comm M ha.1 hb.1), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

@[expose] def pstd (p : ℕ) (H : Subgroup (GL (Fin 3) K)) (M : Subgroup Kˣ) :
    Subgroup (StatedProj H) :=
  ((omegaP p M).comap H.subtype).map (proj H)

theorem mem_pstd {x : StatedProj H} :
    x ∈ pstd p H M ↔ ∃ t : H, (t : GL (Fin 3) K) ∈ omegaP p M ∧ proj H t = x := by
  simp only [pstd, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]

namespace PModel

variable (h : PModel p H M)
include h

theorem exists_sylow_le_torus [Finite K] [Fact p.Prime] :
    ∃ S₀ : Sylow p H, (S₀ : Subgroup H) ≤ (torus3 M).subgroupOf H := by
  classical
  have hNH : torus3 M ≤ H := torus3_le M h.mono
  set N' : Subgroup H := (torus3 M).subgroupOf H with hN'def
  have hN'card : Nat.card N' = Nat.card M ^ 2 := by
    rw [hN'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, card_torus3]
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p N'))
  have hS₀ := Sylow.card_eq_multiplicity S₀
  let S : Sylow p H := Sylow.ofCard ((S₀ : Subgroup N').map N'.subtype) (by
    rw [Subgroup.card_map_of_injective N'.subtype_injective, hS₀, hN'card, h.cardp])
  have hSN : (S : Subgroup H) ≤ N' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  exact ⟨S, hSN⟩

theorem exists_conj_le_pstd [Finite K] [Fact p.Prime] (hp3 : p ≠ 3) {P : Subgroup (StatedProj H)}
    (hP : IsPGroup p P) (hexp : ∀ x ∈ P, x ^ p = 1) :
    ∃ g : StatedProj H, ∀ x ∈ P, g⁻¹ * x * g ∈ pstd p H M := by
  classical
  obtain ⟨S₀, hS₀⟩ := h.exists_sylow_le_torus
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedProj H)
    (Sylow.mapSurjective (proj_surjective (H := H)) S₀) R
  obtain ⟨c, hc3, hc1⟩ := exists_exp_three_dvd (Fact.out : p.Prime) hp3
  refine ⟨g, fun x hx => ?_⟩
  have hxR : x ∈ (((g • Sylow.mapSurjective (proj_surjective (H := H)) S₀ : Sylow p _) :
      Subgroup (StatedProj H))) := hg ▸ hPR hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxR
  have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e, Sylow.coe_mapSurjective] at hxR
  obtain ⟨t, ht, hty⟩ := hxR
  have htT : (t : GL (Fin 3) K) ∈ torus3 M := Subgroup.mem_subgroupOf.1 (hS₀ ht)
  have hyp : (g⁻¹ * x * g) ^ p = 1 := by
    have := conj_pow (a := g⁻¹) (b := x) (i := p)
    rw [inv_inv] at this
    rw [this, hexp x hx, mul_one, inv_mul_cancel]
  have htp : t ^ p ∈ scal H := by
    rw [← proj_eq_one_iff, map_pow]
    exact (hty ▸ hyp)
  have ht3 : (t ^ p) ^ 3 = 1 := h.pow_three_of_mem_scal htp
  obtain ⟨c', rfl⟩ := hc3
  refine mem_pstd.2 ⟨t ^ (3 * c'), ⟨?_, ?_⟩, ?_⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem htT _
  · rw [Subgroup.coe_pow, ← pow_mul, show 3 * c' * p = p * 3 * c' by ring, pow_mul, pow_mul,
      ← Subgroup.coe_pow, ← Subgroup.coe_pow, ht3]
    simp
  · rw [map_pow, hty]
    have hc : 3 * c' = p * (3 * c' / p) + 1 := by
      have := Nat.div_add_mod (3 * c') p
      omega
    rw [hc, pow_add, pow_mul, hyp, one_pow, one_mul, pow_one]

end PModel

end CFSG.Quasithin.H13.NQCore.U3O
