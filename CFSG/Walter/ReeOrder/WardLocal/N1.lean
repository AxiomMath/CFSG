module

public import CFSG.Walter.ReeOrder.WardLocal.Borel
public import CFSG.Walter.ReeOrder.WardLocal.P1

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {k : ℕ} (hq : q = 3 ^ (2 * k + 1))
  (hK : Fintype.card K = q)

include hq hK in
theorem IV_RR {ρ b : G} (hρ : ρ ∈ RR S) (hρ1 : ρ ≠ 1)
    (hb : b * ρ * b⁻¹ ∈ Subgroup.zpowers ρ) : b * S.J = S.J * b := by
  obtain ⟨j, rfl⟩ := mem_RR.mp hρ
  have hRo : 2 * Nat.card S.W.Ro + 1 = q := by have := S.W.Ro_card; omega
  have hcR := card_RR (S := S) hK hq
  have hord : orderOf (dgen K ^ j) ∣ Nat.card S.W.Ro := by
    have h1 : Nat.card S.W.Ro = Nat.card (RR S) := by omega
    rw [h1, RR, Subgroup.card_map_of_injective S.κ_inj, Nat.card_zpowers]
    exact orderOf_pow_dvd j
  obtain ⟨g, hg⟩ := S.W.Ro_conj _ hord
  set r := g⁻¹ * dgen K ^ j * g with hr
  have hr1 : r ≠ 1 := by
    intro h
    apply hρ1
    have : dgen K ^ j = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) h
      simpa [hr, mul_assoc] using this
    rw [this, map_one]
  set b' := (S.κ g)⁻¹ * b⁻¹ * S.κ g with hb'
  have hkr : S.κ (dgen K ^ j) = S.κ g * S.κ r * (S.κ g)⁻¹ := by
    rw [hr]; simp only [map_mul, map_inv]; group
  have hb'r : b'⁻¹ * S.κ r * b' ∈ Subgroup.zpowers (S.κ r) := by
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hb
    refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
    have e : S.κ r = (S.κ g)⁻¹ * S.κ (dgen K ^ j) * S.κ g := by rw [hkr]; group
    rw [e, hb']
    calc ((S.κ g)⁻¹ * S.κ (dgen K ^ j) * S.κ g) ^ z
        = (S.κ g)⁻¹ * S.κ (dgen K ^ j) ^ z * S.κ g := by
          rw [show (S.κ g)⁻¹ * S.κ (dgen K ^ j) * S.κ g =
            (MulAut.conj (S.κ g)⁻¹) (S.κ (dgen K ^ j)) by simp,
            ← map_zpow]
          simp
      _ = (S.κ g)⁻¹ * (b * S.κ (dgen K ^ j) * b⁻¹) * S.κ g := by rw [hz]
      _ = ((S.κ g)⁻¹ * b⁻¹ * S.κ g)⁻¹ * ((S.κ g)⁻¹ * S.κ (dgen K ^ j) * S.κ g) *
          ((S.κ g)⁻¹ * b⁻¹ * S.κ g) := by group
  have hJ := S.normalizer rfl r hg hr1 b' hb'r
  have hbe : b = S.κ g * b'⁻¹ * (S.κ g)⁻¹ := by rw [hb']; group
  rw [hbe]
  have hg1 := S.κ_comm g
  have hJb' : b'⁻¹ * S.J = S.J * b'⁻¹ := by
    calc b'⁻¹ * S.J = b'⁻¹ * (S.J * b') * b'⁻¹ := by group
      _ = b'⁻¹ * (b' * S.J) * b'⁻¹ := by rw [hJ]
      _ = S.J * b'⁻¹ := by group
  have hg2 : (S.κ g)⁻¹ * S.J = S.J * (S.κ g)⁻¹ := by
    calc (S.κ g)⁻¹ * S.J = (S.κ g)⁻¹ * (S.J * S.κ g) * (S.κ g)⁻¹ := by group
      _ = (S.κ g)⁻¹ * (S.κ g * S.J) * (S.κ g)⁻¹ := by rw [hg1]
      _ = S.J * (S.κ g)⁻¹ := by group
  calc S.κ g * b'⁻¹ * (S.κ g)⁻¹ * S.J = S.κ g * b'⁻¹ * ((S.κ g)⁻¹ * S.J) := by group
    _ = S.κ g * (b'⁻¹ * S.J) * (S.κ g)⁻¹ := by rw [hg2]; group
    _ = S.κ g * S.J * b'⁻¹ * (S.κ g)⁻¹ := by rw [hJb']; group
    _ = S.J * (S.κ g * b'⁻¹ * (S.κ g)⁻¹) := by rw [hg1]; group

omit [Fintype G] in
theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {H : Subgroup X} {y : X}
    (hy : ∀ h ∈ H, y * h * y⁻¹ ∈ H) : y ∈ Subgroup.normalizer (H : Set X) := by
  have hle : H.map (MulAut.conj y).toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩; exact hy h hh
  have hcard : Nat.card (H.map (MulAut.conj y).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have heq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hy g, fun hg => ?_⟩
  rw [← heq] at hg
  obtain ⟨h, hh, hhg⟩ := hg
  have : h = g := by
    have := congrArg (fun t => y⁻¹ * t * y) hhg
    simpa [MulAut.conj_apply, mul_assoc] using this
  exact this ▸ hh

variable [CharP K 3] (hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2)

omit [CharP K 3] in
include hq hK in
theorem mem_FF_of_PP1_comm_J {x : G} (hx : x ∈ PP1 S) (hxJ : x * S.J = S.J * x) :
    x ∈ FF S := by
  have hodd : Odd (orderOf x) := by
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp isPGroup_PP1) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  obtain ⟨z, rfl⟩ := S.odd_mem_κ hxJ hodd
  have hzT : z * pslU 1 = pslU 1 * z := by
    apply S.κ_inj
    rw [map_mul, map_mul]
    exact ((Subgroup.mem_centralizer_iff.mp (PP1_le_CF hx)) _ TT_mem).symm
  have hKq : Fintype.card K = 3 ^ (2 * k + 1) := hK.trans hq
  exact mem_FF.mpr (by
    obtain ⟨c, hc⟩ := mem_pslE_iff.mp (mem_pslE_of_commute hKq one_ne_zero hzT)
    exact ⟨c, by rw [hc]⟩)

include hq hK hcT in
theorem commute_of_normalizes {n ρ : G} (hn : n ∈ Subgroup.normalizer (PP1 S : Set G))
    (hnJ : n * S.J = S.J * n) (hρ : ρ ∈ RR S) (hnρ : n * ρ * n⁻¹ ∈ Subgroup.zpowers ρ) :
    n * ρ = ρ * n := by
  have hKq : Fintype.card K = 3 ^ (2 * k + 1) := hK.trans hq
  obtain ⟨y, hy⟩ := S.centralizer n hnJ
  have hyF : ∀ c : K, y * pslU c * y⁻¹ ∈ pslE K := by
    intro c
    have hf : S.κ (pslU c) ∈ FF S := mem_FF.mpr ⟨c, rfl⟩
    have h1 : n * S.κ (pslU c) * n⁻¹ ∈ PP1 S :=
      (Subgroup.mem_normalizer_iff.mp hn _).mp (FF_le_PP1 hq hcT hf)
    have h2 : n * S.κ (pslU c) * n⁻¹ * S.J = S.J * (n * S.κ (pslU c) * n⁻¹) := by
      have hJn : n⁻¹ * S.J = S.J * n⁻¹ := by
        calc n⁻¹ * S.J = n⁻¹ * (S.J * n) * n⁻¹ := by group
          _ = n⁻¹ * (n * S.J) * n⁻¹ := by rw [hnJ]
          _ = S.J * n⁻¹ := by group
      calc n * S.κ (pslU c) * n⁻¹ * S.J = n * S.κ (pslU c) * (n⁻¹ * S.J) := by group
        _ = n * (S.κ (pslU c) * S.J) * n⁻¹ := by rw [hJn]; group
        _ = n * S.J * S.κ (pslU c) * n⁻¹ := by rw [S.κ_comm]; group
        _ = S.J * (n * S.κ (pslU c) * n⁻¹) := by rw [hnJ]; group
    have h3 := mem_FF_of_PP1_comm_J hq hK h1 h2
    have h4 : n * S.κ (pslU c) * n⁻¹ = S.κ (y * pslU c * y⁻¹) := by
      rcases hy with rfl | rfl
      · simp only [map_mul, map_inv]
      · simp only [map_mul, map_inv, mul_inv_rev]
        calc S.J * S.κ y * S.κ (pslU c) * ((S.κ y)⁻¹ * S.J⁻¹)
            = S.J * (S.κ y * S.κ (pslU c) * (S.κ y)⁻¹) * S.J⁻¹ := by group
          _ = S.κ y * S.κ (pslU c) * (S.κ y)⁻¹ := by
            rw [show (S.κ y * S.κ (pslU c) * (S.κ y)⁻¹) = S.κ (y * pslU c * y⁻¹) by
              simp [map_mul, map_inv], S.κ_comm', mul_inv_cancel_right]
    rw [h4] at h3
    obtain ⟨c', hc'⟩ := mem_FF.mp h3
    exact ⟨c', S.κ_inj hc'⟩
  have hyN : y ∈ Subgroup.normalizer ((pslE K : Subgroup PSL(2, K)) : Set PSL(2, K)) :=
    mem_normalizer_of_conj_mem (fun h hh => by
      obtain ⟨c, rfl⟩ := mem_pslE_iff.mp hh; exact hyF c)
  obtain ⟨c, j, hcj⟩ := exists_of_mem_normalizer hKq hyN
  obtain ⟨i, rfl⟩ := mem_RR.mp hρ
  obtain ⟨k', hk', -⟩ := Block.q_half hq
  have hconjn : n * S.κ (dgen K ^ i) * n⁻¹ = S.κ (y * dgen K ^ i * y⁻¹) := by
    rcases hy with rfl | rfl
    · simp only [map_mul, map_inv]
    · rw [map_mul, map_mul, map_inv]
      calc S.J * S.κ y * S.κ (dgen K ^ i) * (S.J * S.κ y)⁻¹
          = S.J * (S.κ y * S.κ (dgen K ^ i) * (S.κ y)⁻¹) * S.J⁻¹ := by group
        _ = S.κ y * S.κ (dgen K ^ i) * (S.κ y)⁻¹ := by
          rw [show (S.κ y * S.κ (dgen K ^ i) * (S.κ y)⁻¹) = S.κ (y * dgen K ^ i * y⁻¹) by
            simp [map_mul, map_inv], S.κ_comm', mul_inv_cancel_right]
  rw [hconjn] at hnρ
  have hmemL : y * dgen K ^ i * y⁻¹ ∈ Subgroup.zpowers (dgen K) := by
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hnρ
    refine Subgroup.mem_zpowers_iff.mpr ⟨i * z, ?_⟩
    apply S.κ_inj
    rw [← hz, map_zpow, map_pow, zpow_mul, zpow_natCast]
  have hyd : y * dgen K ^ i * y⁻¹ = pslU c * dgen K ^ i * (pslU c)⁻¹ := by
    rw [hcj]; group
  rw [hyd] at hmemL
  have hcomm : pslU c * dgen K ^ i * (pslU c)⁻¹ * (dgen K ^ i)⁻¹ =
      pslU (c - ((gen K : Kˣ) : K) ^ (2 * i) * c) := by
    rw [pslU_inv, show pslU c * dgen K ^ i * pslU (-c) * (dgen K ^ i)⁻¹ =
      pslU c * (dgen K ^ i * pslU (-c) * (dgen K ^ i)⁻¹) by group, dgen_pow_conj, pslU_mul]
    congr 1; ring
  have hcm : pslU (c - ((gen K : Kˣ) : K) ^ (2 * i) * c) ∈ Subgroup.zpowers (dgen K) := by
    rw [← hcomm]
    exact Subgroup.mul_mem _ hmemL (Subgroup.inv_mem _ (Subgroup.pow_mem _
      (Subgroup.mem_zpowers _) _))
  have h1 := pslU_eq_one_of_mem_zpowers hKq hcm
  have h2 : c - ((gen K : Kˣ) : K) ^ (2 * i) * c = 0 :=
    pslU_injective (h1.trans pslU_zero.symm)
  have hyc : y * dgen K ^ i * y⁻¹ = dgen K ^ i := by
    rw [hyd]
    rcases mul_eq_zero.mp (show c * (1 - ((gen K : Kˣ) : K) ^ (2 * i)) = 0 by
      linear_combination h2) with h | h
    · rw [h, pslU_zero]; group
    · have ha : gen K ^ (2 * i) = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one]; linear_combination -h)
      have hdi : dgen K ^ i = 1 := by
        rw [dgen_pow_eq_one_iff (hK.trans hk')]
        have := orderOf_dvd_of_pow_eq_one ha
        rw [orderOf_gen, hK, hk', Nat.add_sub_cancel] at this
        exact Nat.dvd_of_mul_dvd_mul_left two_pos this
      rw [hdi]; group
  have hfinal : n * S.κ (dgen K ^ i) * n⁻¹ = S.κ (dgen K ^ i) := by rw [hconjn, hyc]
  calc n * S.κ (dgen K ^ i) = n * S.κ (dgen K ^ i) * n⁻¹ * n := by group
    _ = S.κ (dgen K ^ i) * n := by rw [hfinal]

end CFSG.Walter.WardLocal
