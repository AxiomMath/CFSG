module

public import CFSG.Quasithin.H13.A5S1515a
public import CFSG.Quasithin.H13.A5L1
public import CFSG.Quasithin.Background.G13Wrap
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Fischer CFSG.LieType.BorelTits
open CFSG.Quasithin.A5Model
open scoped commutatorElement MatrixGroups Pointwise

section F4

abbrev M4 := F4 × F4 × F4 × F4

@[expose] def mulM (x y : M4) : M4 :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
    x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)

@[expose] def oneM : M4 := (1, 0, 0, 1)

@[expose] def detM (x : M4) : F4 := x.1 * x.2.2.2 - x.2.1 * x.2.2.1

theorem f4_sq_of_pow_four : ∀ x : M4, mulM (mulM x x) (mulM x x) = oneM → mulM x x = oneM := by
  decide +kernel

theorem f4_fix : ∀ x : M4, detM x = 1 → mulM x (mulM x x) = oneM → x ≠ oneM →
    ∀ p q : F4, x.1 * p + x.2.1 * q = p → x.2.2.1 * p + x.2.2.2 * q = q → p = 0 ∧ q = 0 := by
  decide +kernel

theorem f4_comm : ∀ x : M4, detM x = 1 → mulM x (mulM x x) = oneM → x ≠ oneM →
    ∀ y : M4, mulM y y = oneM → mulM x y = mulM y x → y = oneM := by
  decide +kernel

end F4

section GF4

noncomputable abbrev eF : GaloisField 2 2 ≃+* F4 := F4.equivGaloisField.symm

abbrev coeM (x : SL(2, GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) := x

@[expose] noncomputable def tup (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) : M4 :=
  (eF (A 0 0), eF (A 0 1), eF (A 1 0), eF (A 1 1))

theorem tup_mul (A B : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    tup (A * B) = mulM (tup A) (tup B) := by
  simp [tup, mulM, Matrix.mul_apply, Fin.sum_univ_two]

theorem tup_one : tup 1 = oneM := by
  simp [tup, oneM]

theorem tup_injective : Function.Injective tup := by
  intro A B h
  simp only [tup, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  ext i j
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem detM_tup (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) : detM (tup A) = eF A.det := by
  simp [detM, tup, Matrix.det_fin_two]

variable (g : SL(2, GaloisField 2 2)) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
include hg3 hg1

theorem tup_data : detM (tup g) = 1 ∧ mulM (tup g) (mulM (tup g) (tup g)) = oneM ∧
    tup g ≠ oneM := by
  refine ⟨by rw [detM_tup, g.2, map_one], ?_, ?_⟩
  · rw [← tup_mul, ← tup_mul, ← tup_one]
    congr 1
    have := congrArg coeM hg3
    simpa [pow_succ, mul_assoc, Matrix.SpecialLinearGroup.coe_pow] using this
  · intro h
    apply hg1
    apply Subtype.ext
    exact tup_injective (h.trans tup_one.symm)

theorem eq_zero_of_smul_eq (v : Fin 2 → GaloisField 2 2) (hv : g • v = v) : v = 0 := by
  obtain ⟨hd, h3, h1⟩ := tup_data g hg3 hg1
  have hv' : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec v = v := by
    have e : g • v = (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec v := by
      rw [Matrix.SpecialLinearGroup.smul_def]
      rfl
    rw [← e]
    exact hv
  have e0 := congrFun hv' 0
  have e1 := congrFun hv' 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  obtain ⟨hp, hq⟩ := f4_fix _ hd h3 h1 (eF (v 0)) (eF (v 1))
    (by simpa [tup] using congrArg eF e0) (by simpa [tup] using congrArg eF e1)
  funext i
  fin_cases i
  · simpa using hp
  · simpa using hq

theorem eq_one_of_comm (u : SL(2, GaloisField 2 2)) {k : ℕ} (hu : u ^ 2 ^ k = 1)
    (hgu : g * u = u * g) : u = 1 := by
  obtain ⟨hd, h3, h1⟩ := tup_data g hg3 hg1
  have hsq : ∀ k : ℕ, ∀ u : SL(2, GaloisField 2 2), u ^ 2 ^ k = 1 → u ^ 2 = 1 := by
    intro k
    induction k with
    | zero => intro u hu; rw [pow_zero, pow_one] at hu; rw [hu, one_pow]
    | succ k ih =>
      intro u hu
      have h4 : (u ^ 2) ^ 2 = 1 := ih (u ^ 2) (by rw [← pow_mul, ← pow_succ']; exact hu)
      have h4' : mulM (mulM (tup u) (tup u)) (mulM (tup u) (tup u)) = oneM := by
        rw [← tup_mul, ← tup_mul, ← tup_one]
        congr 1
        have := congrArg coeM h4
        simpa [pow_two, mul_assoc, Matrix.SpecialLinearGroup.coe_pow] using this
      have h2 := f4_sq_of_pow_four _ h4'
      rw [← tup_mul, ← tup_one] at h2
      apply Subtype.ext
      simpa [pow_two] using tup_injective h2
  have hu2 := hsq k u hu
  have hy : mulM (tup u) (tup u) = oneM := by
    rw [← tup_mul, ← tup_one]
    congr 1
    have := congrArg coeM hu2
    simpa [pow_two, Matrix.SpecialLinearGroup.coe_pow] using this
  have hc : mulM (tup g) (tup u) = mulM (tup u) (tup g) := by
    rw [← tup_mul, ← tup_mul]
    congr 1
    have := congrArg coeM hgu
    simpa using this
  have := f4_comm _ hd h3 h1 _ hy hc
  apply Subtype.ext
  exact tup_injective (this.trans tup_one.symm)

end GF4

section Sum

variable {G : Type} [Group G]

theorem mem_of_comm_of_isSum {s : ℕ} {I S S₂ : Subgroup G}
    (h : IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I S S S₂) {c x : ↥I}
    (hc3 : c ^ 3 = 1) (hcS : (c : G) ∉ S) {k : ℕ} (hx : x ^ 2 ^ k = 1) (hcx : c * x = x * c) :
    (x : G) ∈ S₂ := by
  obtain ⟨β, φ, -, hβ, -, hφ, heq⟩ := h
  have hβc1 : β c ≠ 1 := fun h' => hcS ((hβ c).mp h')
  have hβc3 : β c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hβx : β x = 1 := eq_one_of_comm (β c) hβc3 hβc1 (β x) (k := k)
    (by rw [← map_pow, hx, map_one]) (by rw [← map_mul, hcx, map_mul])
  have hxS : (x : G) ∈ S := (hβ x).mp hβx
  have hfix := heq c ⟨x, hxS⟩ ⟨x, hxS⟩ (by
    show (x : G) = c * x * (c : G)⁻¹
    rw [← Subgroup.coe_mul, hcx, Subgroup.coe_mul, mul_inv_cancel_right])
  rw [← hφ ⟨x, hxS⟩]
  apply Multiplicative.toAdd.injective
  funext j
  have hj := congrFun (congrArg Multiplicative.toAdd hfix) j
  simp only [toAdd_ofAdd] at hj
  simp only [toAdd_one, Pi.zero_apply]
  exact eq_zero_of_smul_eq (β c) hβc3 hβc1 _ hj.symm

end Sum

theorem K4_inter_conj : ∀ σ : Equiv.Perm (Fin 5), σ 4 ≠ 4 →
    ¬ InK4 (σ * pa * σ⁻¹) ∧ ¬ InK4 (σ * pb * σ⁻¹) ∧ ¬ InK4 (σ * pc * σ⁻¹) := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem sq_eq_one_of_mem_S2 (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (S.V1 : Set G)) {x : G}
    (hx : x ∈ conjClosure S.V1 L ⊔ (conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g)) :
    x ^ 2 = 1 := by
  rw [S.conjClosure_V1_L] at hx
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.T_le (S.conjClosure_V3_le_T h1323 hH hu)
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hg
  have hzg : g * S.z * g⁻¹ = S.z → False := by
    intro hgz
    apply hgN
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [hgz]
  have hg4 : S.frame.ρ ⟨g, hgV⟩ 4 ≠ 4 := by
    intro h4
    apply hzg
    rw [S.conj_eq_iff ⟨g, hgV⟩ ⟨S.z, S.z_mem_V⟩, S.psi_z]
    exact pact_W4 h4
  have hcent : ∀ w ∈ conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g,
      w ∈ Subgroup.centralizer (V : Set G) := by
    intro w hw
    obtain ⟨hwU, hwg⟩ := Subgroup.mem_inf.mp hw
    rw [mem_rconj] at hwg
    have h1 := (S.lemma_13_5_14_two h1323 hH hna).1 w hwU
    have h2 := (S.lemma_13_5_14_two h1323 hH hna).1 _ hwg
    have e : S.frame.ρ ⟨g * w * g⁻¹, hUN _ hwg⟩ =
        S.frame.ρ ⟨g, hgV⟩ * S.frame.ρ ⟨w, hUN w hwU⟩ * (S.frame.ρ ⟨g, hgV⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at h2
    have hw1 : S.frame.ρ ⟨w, hUN w hwU⟩ = 1 := by
      obtain ⟨n1, n2, n3⟩ := K4_inter_conj _ hg4
      rcases h1 with h | h | h | h
      · exact h
      · rw [h] at h2; exact absurd h2 n1
      · rw [h] at h2; exact absurd h2 n2
      · rw [h] at h2; exact absurd h2 n3
    exact S.frame.mem_centralizer_of_rho _ hw1
  have hsq : ∀ w ∈ conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨hwU, hwg⟩ := Subgroup.mem_inf.mp hw
    rw [mem_rconj] at hwg
    have hF := S.hypF91 h1323 hH
    have h1 := S.mem_V1.mp (hF.sq_mem_conjClosure w hwU)
    have h2 := S.mem_V1.mp (hF.sq_mem_conjClosure _ hwg)
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      have e : (g * w * g⁻¹) ^ 2 = g * w ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
      rw [e, h1] at h2
      rcases h2 with h2 | h2
      · apply S.z_ne_one
        have : g⁻¹ * (g * S.z * g⁻¹) * g = S.z := by group
        rw [h2] at this
        simpa using this.symm
      · exact hzg h2
  have hle : conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g ≤
      Subgroup.normalizer (V : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (hcent w hw)
  have hx' : x ∈ (V : Set G) *
      ((conjClosure S.V3 H ⊓ rconj (conjClosure S.V3 H) g : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V _ hle]
    exact hx
  obtain ⟨v, hv, w, hw, rfl⟩ := Set.mem_mul.mp hx'
  have hvw : v * w = w * v := Subgroup.mem_centralizer_iff.mp (hcent w hw) v hv
  have hv2 : v ^ 2 = 1 := S.elemAbelian_V.2 v hv
  calc (v * w) ^ 2 = v ^ 2 * w ^ 2 := by
        rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc w, ← hvw, mul_assoc, mul_assoc]
    _ = 1 := by rw [hv2, hsq w hw, mul_one]

theorem sq_eq_one_of_comm_cL1
    (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {u : G} (hu : u ∈ conjClosure S.V3 H)
    (huc : u * S.cL1 = S.cL1 * u) : u ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hgN⟩ := S.exists_L_not_normalizer_V1
  have hyp := S.almostSpecialA5Hyp h1323 hH hna
  obtain ⟨⟨s, hs⟩, -⟩ := hyp.G24_six' rfl hg hgN rfl rfl rfl
  have hI := (S.lemma_13_5_14_three h1323 hH hna hg hgN).1
  have hcI : (S.cL1 : G) ∈ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) g := by
    rw [hI]
    exact Subgroup.mem_sup_left (S.L1_le_L S.cL1_mem)
  have huI : u ∈ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) g := Subgroup.mem_sup_left hu
  have hcS : (S.cL1 : G) ∉ pCoreOf 2 (conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) g) := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 _ ⟨_, h⟩
    have hk' : (S.cL1 : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    apply S.cL1_not_mem
    have h1 : orderOf (S.cL1 : G) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one S.cL1_cube) (orderOf_dvd_of_pow_eq_one hk')
    rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨k, hk⟩ := S.isPGroup_T ⟨u, S.conjClosure_V3_le_T h1323 hH hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hS2 := mem_of_comm_of_isSum hs (c := ⟨_, hcI⟩) (x := ⟨u, huI⟩)
    (Subtype.ext S.cL1_cube) hcS (k := k) (Subtype.ext hk') (Subtype.ext huc.symm)
  exact S.sq_eq_one_of_mem_S2 h1323 hH hna hg hgN hS2

end Setting

end CFSG.Quasithin.H13.A5
