module

public import CFSG.RankThree.GF2n.Smith81.S81R213X
public import CFSG.RankThree.GF2n.Smith81.S81RRangeOdd

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

section Odd

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem isTransvec_mul_self {g : GL (Fin 6) K} (hg : IsTransvec K g) : g * g = 1 := by
  apply Units.ext
  have h := hg.1
  set A : Matrix (Fin 6) (Fin 6) K := (g : Matrix (Fin 6) (Fin 6) K) with hA
  have e : (A - 1) * (A - 1) = A * A - (A + A) + 1 := by noncomm_ring
  have h2 : A + A = 0 := by rw [← two_smul K A, CharTwo.two_eq_zero, zero_smul]
  have h1 : (1 : Matrix (Fin 6) (Fin 6) K) + 1 = 0 := by
    rw [← two_smul K (1 : Matrix (Fin 6) (Fin 6) K), CharTwo.two_eq_zero, zero_smul]
  rw [e, h2, sub_zero] at h
  rw [Units.val_mul, Units.val_one]
  calc A * A = (A * A + 1) + 1 := by rw [add_assoc, h1, add_zero]
    _ = 1 := by rw [h, zero_add]

theorem ActsAs.pow {x : G} {g : GL (Fin 6) K} (hx : ActsAs φ x g) (n : ℕ) :
    ActsAs φ (x ^ n) (g ^ n) := by
  induction n with
  | zero => simpa using (ActsAs.one : ActsAs φ (1 : G) (1 : GL (Fin 6) K))
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx

theorem ActsAs.mem_Q_of_one {v : G} (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) (hv : ActsAs φ v 1) :
    v ∈ Q := by
  have hL := hv.mem_Lgen
  have : φ ⟨v, hL⟩ = 1 := by rw [hv.phi hL, map_one]
  exact (Dt.d.ker _).mp this

theorem ActsAs.not_mem_Q {v : G} {g : GL (Fin 6) K} (Dt : E3LDat M Q Z B K γ M₀ ψ φ z)
    (hv : ActsAs φ v g) (hg : rhoEquiv K g ≠ 1) : v ∉ Q := by
  intro hQ
  have hL := hv.mem_Lgen
  apply hg
  rw [← hv.phi hL]
  exact (Dt.d.ker _).mpr hQ

theorem ActsAs.rho_ne_one_of_not_mem_Q {v : G} {g : GL (Fin 6) K}
    (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) (hv : ActsAs φ v g) (hvQ : v ∉ Q) :
    rhoEquiv K g ≠ 1 := by
  intro h
  apply hvQ
  have hL := hv.mem_Lgen
  exact (Dt.d.ker _).mp (by rw [hv.phi hL, h])

theorem odd_orderOf_mul (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {x y : G} (hxc : IsConj z x)
    (hxM : x ∈ M) (hxQ : x ∉ Q) (hyc : IsConj z y) (hyM : y ∈ M) (hyQ : y ∉ Q)
    {gx gy : GL (Fin 6) K} (hgx : IsTransvec K gx) (hgy : IsTransvec K gy)
    (hx : ActsAs φ x gx) (hy : ActsAs φ y gy) (hodd : Odd (orderOf (gx * gy)))
    (hne : gx * gy ≠ 1) : Odd (orderOf (x * y)) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  have hxx : x * x = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hxc
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hgxx : gx * gx = 1 := isTransvec_mul_self hgx
  have hk1 : 1 < orderOf (gx * gy) := by
    rcases Nat.lt_or_ge 1 (orderOf (gx * gy)) with h | h
    · exact h
    · exfalso
      have hpos : 0 < orderOf (gx * gy) := orderOf_pos _
      exact hne (orderOf_eq_one_iff.mp (by omega))
  obtain ⟨k, hk⟩ : ∃ k, k = orderOf (gx * gy) := ⟨_, rfl⟩
  rw [← hk] at hodd hk1
  obtain ⟨u, hu⟩ : ∃ u, u = x * y := ⟨_, rfl⟩
  have hU : ActsAs φ u (gx * gy) := hu ▸ hx.mul hy
  have hgk : (gx * gy) ^ k = 1 := by rw [hk]; exact pow_orderOf_eq_one _
  have hukQ : u ^ k ∈ Q := by
    have h1 := hU.pow k
    rw [hgk] at h1
    exact h1.mem_Q_of_one Dt
  have hw4 : (u ^ k) ^ 4 = 1 := by
    have h2 := Z_sq H (sq_mem_Z H hukQ)
    calc (u ^ k) ^ 4 = (u ^ k) ^ (2 * 2) := rfl
      _ = ((u ^ k) ^ 2) ^ 2 := pow_mul (u ^ k) 2 2
      _ = 1 := h2
  have hcop : Nat.Coprime 4 k := by
    have h2 : Nat.Coprime 2 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
    simpa using Nat.Coprime.pow_left 2 h2
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hk1
  obtain ⟨u', hu'⟩ : ∃ u', u' = u ^ (4 * s) := ⟨_, rfl⟩
  have hu'k : u' ^ k = 1 := by
    calc u' ^ k = (u ^ k) ^ (4 * s) := by rw [hu', ← pow_mul, ← pow_mul, mul_comm]
      _ = ((u ^ k) ^ 4) ^ s := pow_mul (u ^ k) 4 s
      _ = 1 := by rw [hw4, one_pow]
  have hU' : ActsAs φ u' (gx * gy) := by
    have h1 := hU.pow (4 * s)
    have h2 : (gx * gy) ^ (4 * s) = gx * gy := by
      rw [← pow_mod_orderOf, ← hk, hs, pow_one]
    rw [h2, ← hu'] at h1
    exact h1
  have hxu : x * u * x⁻¹ = u⁻¹ := by
    rw [hu, hxinv, mul_inv_rev, hyinv, hxinv]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hxx, one_mul]
  have hxu' : x * u' * x⁻¹ = u'⁻¹ := by
    rw [hu', ← conj_pow, hxu, inv_pow]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = u' ^ ((k + 1) / 2) := ⟨_, rfl⟩
  have hs₀s₀ : s₀ * s₀ = u' := by
    have h1 : (k + 1) / 2 + (k + 1) / 2 = k + 1 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    rw [hs₀, ← pow_add, h1, pow_succ, hu'k, one_mul]
  have hxs₀ : x * s₀ * x⁻¹ = s₀⁻¹ := by
    rw [hs₀, ← conj_pow, hxu', inv_pow]
  have hxs₀' : x * s₀ = s₀⁻¹ * x := by
    have := hxs₀
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hx₁eq : x * u' = s₀⁻¹ * x * (s₀⁻¹)⁻¹ := by
    rw [inv_inv]
    calc x * u' = x * (s₀ * s₀) := by rw [hs₀s₀]
      _ = (x * s₀) * s₀ := by group
      _ = (s₀⁻¹ * x) * s₀ := by rw [hxs₀']
  have hx₁c : IsConj z (x * u') := hxc.trans (isConj_iff.mpr ⟨s₀⁻¹, hx₁eq.symm⟩)
  have hu'M : u' ∈ M := by
    rw [hu', hu]
    exact pow_mem (M.mul_mem hxM hyM) _
  have hx₁M : x * u' ∈ M := M.mul_mem hxM hu'M
  have hx₁A : ActsAs φ (x * u') gy := by
    have h1 := hx.mul hU'
    have h2 : gx * (gx * gy) = gy := by rw [← mul_assoc, hgxx, one_mul]
    rwa [h2] at h1
  have hx₁Q : x * u' ∉ Q := hx₁A.not_mem_Q Dt (hy.rho_ne_one_of_not_mem_Q Dt hyQ)
  obtain ⟨q, hqQ, hq⟩ := conj_of_phi_eq Dt hx₁c hx₁M hx₁Q hyc hyM hyQ hgy hx₁A hy
  obtain ⟨X, hsx, Tx, hIIx, hCsx, hRsx⟩ := Dt.xdata hxc hxM hxQ hgx hx
  obtain ⟨X₁, hs₁, T₁, hII₁, hCs₁, hRs₁⟩ := Dt.xdata hx₁c hx₁M hx₁Q hgy hx₁A
  have hRR : Rs Tx ⊓ Rs T₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨h1, h2⟩
    have h3 : ψ e ∈ LinearMap.range (rho K gx - 1) ⊓ LinearMap.range (rho K gy - 1) :=
      ⟨(hRsx e).mp h1, (hRs₁ e).mp h2⟩
    rw [range_inf_range_eq_bot_odd hgx hgy (hk ▸ hodd) hne] at h3
    have h4 : ψ e = 0 := h3
    exact (Submodule.mem_bot K).mpr (ψ.map_eq_zero_iff.mp h4)
  have hCC : Cs Tx ⊔ Cs T₁ = ⊤ := Cs_sup_Cs_eq_top hsx hs₁ Tx T₁ hRR
  have hqmem : M₀.π q ∈ Cs Tx ⊔ Cs T₁ := by rw [hCC]; trivial
  obtain ⟨e₁, he₁, e₂, he₂, he⟩ := Submodule.mem_sup.mp hqmem
  obtain ⟨q₁, hq₁Q, rfl⟩ := M₀.π_surj e₁
  obtain ⟨q₂, hq₂Q, rfl⟩ := M₀.π_surj e₂
  have hq₁x : ⁅q₁, x⁆ = 1 := hIIx q₁ hq₁Q ((comm_mem_Z_iff hsx Tx hq₁Q).mpr he₁)
  have hq₂x₁ : ⁅q₂, x * u'⁆ = 1 := hII₁ q₂ hq₂Q ((comm_mem_Z_iff hs₁ T₁ hq₂Q).mpr he₂)
  have hz'' : (q₁ * q₂)⁻¹ * q ∈ Z :=
    (Tim79.QuadModel.pi_eq_iff M₀ (Q.mul_mem hq₁Q hq₂Q) hqQ).mp (by
      rw [M₀.π_mul q₁ hq₁Q q₂ hq₂Q]; exact he)
  have hx₁H0 : x * u' ∈ H0 M Z := Lgen_le_H0 Dt.ctx hx₁A.mem_Lgen
  obtain ⟨zz, hzz⟩ : ∃ zz, zz = (q₁ * q₂)⁻¹ * q := ⟨_, rfl⟩
  rw [← hzz] at hz''
  have hqeq : q = q₁ * q₂ * zz := by rw [hzz, mul_inv_cancel_left]
  have hzzc : zz * (x * u') = (x * u') * zz := Subgroup.mem_centralizer_iff.mp hx₁H0.2 zz hz''
  have hq₂c : q₂ * (x * u') = (x * u') * q₂ := commutatorElement_eq_one_iff_mul_comm.mp hq₂x₁
  have hq₁c : q₁ * x = x * q₁ := commutatorElement_eq_one_iff_mul_comm.mp hq₁x
  have hy₁ : y = q₁ * (x * u') * q₁⁻¹ := by
    have e1 : zz * (x * u') * zz⁻¹ = x * u' := by rw [hzzc]; group
    have e2 : q₂ * (x * u') * q₂⁻¹ = x * u' := by rw [hq₂c]; group
    calc y = q * (x * u') * q⁻¹ := hq
      _ = q₁ * (q₂ * (zz * (x * u') * zz⁻¹) * q₂⁻¹) * q₁⁻¹ := by rw [hqeq]; group
      _ = q₁ * (x * u') * q₁⁻¹ := by rw [e1, e2]
  have hxy : x * y = q₁ * u' * q₁⁻¹ := by
    rw [hy₁]
    calc x * (q₁ * (x * u') * q₁⁻¹) = (x * q₁) * (x * u') * q₁⁻¹ := by group
      _ = (q₁ * x) * (x * u') * q₁⁻¹ := by rw [hq₁c]
      _ = q₁ * ((x * x) * u') * q₁⁻¹ := by group
      _ = q₁ * u' * q₁⁻¹ := by rw [hxx, one_mul]
  have hord : orderOf (x * y) = orderOf u' := by
    rw [hxy]
    exact (SemiconjBy.orderOf_eq q₁ (show q₁ * u' = q₁ * u' * q₁⁻¹ * q₁ by group)).symm
  rw [hord]
  exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hu'k)

end Odd

end CFSG.RankThree.GF2n.Smith81.E3LRoot
