module

public import CFSG.Walter.W67.Section5.Frame5

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter
open scoped MatrixGroups

theorem psl2_sylow_transitive_cs5 {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (P : Sylow 2 PSL(2, F)) {z z' : PSL(2, F)}
    (hz : z ∈ (P : Subgroup PSL(2, F))) (hz1 : z ≠ 1) (hz' : z' ∈ (P : Subgroup PSL(2, F)))
    (hz'1 : z' ≠ 1) :
    ∃ b ∈ Subgroup.normalizer ((P : Subgroup PSL(2, F)) : Set PSL(2, F)), b * z * b⁻¹ = z' := by
  clear hn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F = 2 := by
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨p, hpC, m, hpp, hm⟩ := FiniteField.card' F
    haveI := hpC
    have hp : ringChar F = p := ringChar.eq F p
    have hcard : p ^ (m : ℕ) = 2 ^ n := by
      rw [← hm, ← hF, Nat.card_eq_fintype_card]
    have hdvd : p ∣ 2 ^ n := by
      rw [← hcard]
      exact dvd_pow_self p (PNat.ne_zero m)
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd)
    rw [hp]
    exact hp2
  let U : Sylow 2 (PSL2 F) := psl2UpperUnipotentSylow F hF
  have hU : (U : Subgroup (PSL2 F)) = psl2UpperUnipotentSubgroup F :=
    psl2UpperUnipotentSylow_coe F hF
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 F) U P
  have hmem : ∀ x : PSL2 F,
      x ∈ (P : Subgroup (PSL2 F)) ↔ g⁻¹ * x * g ∈ (U : Subgroup (PSL2 F)) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact Iff.rfl
  have hconjne : ∀ y : PSL2 F, y ≠ 1 → g⁻¹ * y * g ≠ 1 := by
    intro y hy h
    apply hy
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hcore : ∀ u v : PSL2 F, u ∈ (U : Subgroup (PSL2 F)) → v ∈ (U : Subgroup (PSL2 F)) →
      u ≠ 1 → v ≠ 1 →
      ∃ b ∈ Subgroup.normalizer ((U : Subgroup (PSL2 F)) : Set (PSL2 F)), b * u * b⁻¹ = v := by
    intro u v hu hv hu1 hv1
    rw [hU] at hu hv
    obtain ⟨a, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
    obtain ⟨a', rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff v).mp hv
    have ha : a ≠ 0 := by
      rintro rfl
      apply hu1
      rw [sl2UpperUnipotent_zero, map_one]
    have ha' : a' ≠ 0 := by
      rintro rfl
      apply hv1
      rw [sl2UpperUnipotent_zero, map_one]
    obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two hchar (a' / a)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      have h0 : a' / a = 0 := by rw [hμ, mul_zero]
      exact ha' ((div_eq_zero_iff.mp h0).resolve_right ha)
    have hμa : μ ^ 2 * a = a' := by
      rw [sq, ← hμ, div_mul_cancel₀ a' ha]
    have hμinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
    let A : SL(2, F) := ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two_of, hμinv]⟩
    have hA0 : A.val 0 0 = μ := by simp [A]
    have hA : A ∈ sl2Borel F := (sl2_mem_stabilizer_infinity_iff A).mpr (by simp [A])
    refine ⟨psl2QuotientMap F A, ?_, ?_⟩
    · rw [hU, psl2UpperUnipotent_normalizer_eq_borel, psl2Borel_eq_map]
      exact Subgroup.mem_map_of_mem _ hA
    · have hc : A * sl2UpperUnipotent a * A⁻¹ = sl2UpperUnipotent a' := by
        rw [sl2Borel_conj_upperUnipotent hA, hA0, hμa]
      calc psl2QuotientMap F A * psl2QuotientMap F (sl2UpperUnipotent a) *
            (psl2QuotientMap F A)⁻¹
          = psl2QuotientMap F (A * sl2UpperUnipotent a * A⁻¹) := by
            rw [map_mul, map_mul, map_inv]
        _ = psl2QuotientMap F (sl2UpperUnipotent a') := by rw [hc]
  obtain ⟨b₀, hb₀, hconj⟩ :=
    hcore (g⁻¹ * z * g) (g⁻¹ * z' * g) ((hmem z).mp hz) ((hmem z').mp hz')
      (hconjne z hz1) (hconjne z' hz'1)
  refine ⟨g * b₀ * g⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmem h, hmem]
    have e : g⁻¹ * (g * b₀ * g⁻¹ * h * (g * b₀ * g⁻¹)⁻¹) * g = b₀ * (g⁻¹ * h * g) * b₀⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hb₀ (g⁻¹ * h * g)
  · have e : g * b₀ * g⁻¹ * z * (g * b₀ * g⁻¹)⁻¹ =
        g * (b₀ * (g⁻¹ * z * g) * b₀⁻¹) * g⁻¹ := by
      group
    rw [e, hconj]
    group

open CFSG.Walter.W67.Borel5

theorem exists_singer_coordinates_psl216
    (T : Sylow 2 (PSL(2, GaloisField 2 4))) :
    ∃ b : PSL(2, GaloisField 2 4),
      b ∈ Subgroup.normalizer (T : Set (PSL(2, GaloisField 2 4))) ∧
      b ^ 15 = 1 ∧
      (∀ u ∈ (T : Subgroup (PSL(2, GaloisField 2 4))), u ≠ 1 →
        ∀ v ∈ (T : Subgroup (PSL(2, GaloisField 2 4))), v ≠ 1 →
        ∃ n : ℕ, b ^ n * u * (b ^ n)⁻¹ = v) ∧
      (∀ u ∈ (T : Subgroup (PSL(2, GaloisField 2 4))), u ≠ 1 →
        b * u * b⁻¹ ≠ u) ∧
      ∃ eT : Multiplicative (GaloisField 2 4) ≃* T,
      ∃ μ : (GaloisField 2 4)ˣ,
        orderOf μ = 15 ∧
        ∀ x : GaloisField 2 4,
          (eT (Multiplicative.ofAdd ((μ : GaloisField 2 4) * x)) :
            PSL(2, GaloisField 2 4)) =
          b * (eT (Multiplicative.ofAdd x) : PSL(2, GaloisField 2 4)) * b⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 4
  have hcardK : Nat.card K = 2 ^ 4 := GaloisField.card 2 4 (by norm_num)
  let U : Sylow 2 (PSL(2, K)) := psl2UpperUnipotentSylow K (p := 2) (f := 4) hcardK
  have hU : (U : Subgroup (PSL(2, K))) = psl2UpperUnipotentSubgroup K :=
    psl2UpperUnipotentSylow_coe K (p := 2) (f := 4) hcardK
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcardUnits : Nat.card Kˣ = 15 := by
    rw [Nat.card_units, hcardK]
    norm_num
  have haord : orderOf a = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, hcardUnits]
  have ha15 : a ^ 15 = 1 := by
    rw [← haord, pow_orderOf_eq_one]
  let b0 : PSL(2, K) := torusHom K a
  have hb0T : b0 ∈ torus K := ⟨a, rfl⟩
  have hb0N : b0 ∈ Subgroup.normalizer (U : Set (PSL(2, K))) := by
    change b0 ∈ Subgroup.normalizer (((U : Subgroup (PSL(2, K))) : Set (PSL(2, K))))
    rw [hU]
    exact torus_le_normalizer_unip (F := K) hb0T
  have hb0_15 : b0 ^ 15 = 1 := by
    change (torusHom K a) ^ 15 = 1
    rw [← map_pow, ha15, map_one]
  have hb0_ne_one : b0 ≠ 1 := by
    intro h1
    have ha2val : (a : K) ^ 2 = 1 := (torusHom_eq_one_iff (F := K) a).mp h1
    have ha2 : a ^ 2 = 1 := Units.ext (by simpa using ha2val)
    have hdiv : 15 ∣ 2 := by
      rw [← haord]
      exact orderOf_dvd_of_pow_eq_one ha2
    norm_num at hdiv
  have hb0_fpf : ∀ u ∈ (U : Subgroup (PSL(2, K))), u ≠ 1 →
      b0 * u * b0⁻¹ ≠ u := by
    intro u hu hu1 hfix
    have hcomm : u * b0 = b0 * u := by
      calc
        u * b0 = (b0 * u * b0⁻¹) * b0 := by rw [hfix]
        _ = b0 * u := by group
    have hmem : u ∈ unip K ⊓ Subgroup.centralizer ({b0} : Set (PSL(2, K))) := by
      refine ⟨?_, ?_⟩
      · simpa [hU] using hu
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hbot := unip_inf_centralizer_torus (F := K) hb0T hb0_ne_one
    rw [hbot] at hmem
    exact hu1 (Subgroup.mem_bot.mp hmem)
  have hb0_trans : ∀ u ∈ (U : Subgroup (PSL(2, K))), u ≠ 1 →
      ∀ v ∈ (U : Subgroup (PSL(2, K))), v ≠ 1 →
      ∃ n : ℕ, b0 ^ n * u * (b0 ^ n)⁻¹ = v := by
    intro u hu hu1 v hv hv1
    rw [hU] at hu hv
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
    obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff v).mp hv
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hu1
      rw [sl2UpperUnipotent_zero, map_one]
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hv1
      rw [sl2UpperUnipotent_zero, map_one]
    have hq0 : y / x ≠ 0 := div_ne_zero hy0 hx0
    have hchar : ringChar K = 2 := ringChar.eq K 2
    obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (F := K) hchar (y / x)
    have hμ0 : μ ≠ 0 := by
      intro h0
      have hzero : y / x = 0 := by
        rw [hμ, h0]
        norm_num
      exact hq0 hzero
    have hμa : μ * μ * x = y := by
      rw [← hμ, div_mul_cancel₀ y hx0]
    let μUnit : Kˣ := Units.mk0 μ hμ0
    have hμUnit_val : (μUnit : K) = μ := rfl
    have hμUnit_sq : (μUnit : K) ^ 2 * x = y := by
      rw [hμUnit_val, sq, hμa]
    obtain ⟨n, hn⟩ : μUnit ∈ Submonoid.powers a := by
      rw [mem_powers_iff_mem_zpowers]
      exact ha μUnit
    change a ^ n = μUnit at hn
    refine ⟨n, ?_⟩
    calc
      b0 ^ n * psl2QuotientMap K (sl2UpperUnipotent x) * (b0 ^ n)⁻¹
          = torusHom K (a ^ n) * psl2QuotientMap K (sl2UpperUnipotent x) *
              (torusHom K (a ^ n))⁻¹ := by
            rw [show b0 ^ n = torusHom K (a ^ n) by rw [map_pow]]
      _ = torusHom K μUnit * psl2QuotientMap K (sl2UpperUnipotent x) *
              (torusHom K μUnit)⁻¹ := by rw [hn]
      _ = psl2QuotientMap K (sl2UpperUnipotent ((μUnit : K) ^ 2 * x)) :=
            torusHom_conj (F := K) μUnit x
      _ = psl2QuotientMap K (sl2UpperUnipotent y) := by
            rw [hμUnit_sq]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL(2, K)) U T
  let b : PSL(2, K) := g * b0 * g⁻¹
  have hTmap : (T : Subgroup (PSL(2, K))) =
      (psl2UpperUnipotentSubgroup K).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun P : Sylow 2 (PSL(2, K)) =>
      (P : Subgroup (PSL(2, K)))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hU] at h
    convert h.symm using 2
    ext x
    rfl
  have hmem : ∀ x : PSL(2, K),
      x ∈ (T : Subgroup (PSL(2, K))) ↔
        g⁻¹ * x * g ∈ (U : Subgroup (PSL(2, K))) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact Iff.rfl
  have hbN : b ∈ Subgroup.normalizer (T : Set (PSL(2, K))) := by
    change b ∈ Subgroup.normalizer (((T : Subgroup (PSL(2, K))) : Set (PSL(2, K))))
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro x
    rw [hmem x, hmem (b * x * b⁻¹)]
    have e : g⁻¹ * (b * x * b⁻¹) * g = b0 * (g⁻¹ * x * g) * b0⁻¹ := by
      simp only [b]
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hb0N (g⁻¹ * x * g)
  have hbpow : ∀ n : ℕ, b ^ n = g * b0 ^ n * g⁻¹ := by
    intro n
    rw [show b = (MulAut.conj g) b0 by simp [b, MulAut.conj_apply]]
    rw [← map_pow]
    simp [MulAut.conj_apply]
  have hb15 : b ^ 15 = 1 := by
    rw [hbpow 15, hb0_15]
    group
  have hbtrans : ∀ u ∈ (T : Subgroup (PSL(2, K))), u ≠ 1 →
      ∀ v ∈ (T : Subgroup (PSL(2, K))), v ≠ 1 →
      ∃ n : ℕ, b ^ n * u * (b ^ n)⁻¹ = v := by
    intro u hu hu1 v hv hv1
    let u' : PSL(2, K) := g⁻¹ * u * g
    let v' : PSL(2, K) := g⁻¹ * v * g
    have hu'U : u' ∈ (U : Subgroup (PSL(2, K))) := (hmem u).mp hu
    have hv'U : v' ∈ (U : Subgroup (PSL(2, K))) := (hmem v).mp hv
    have hu'1 : u' ≠ 1 := by
      intro h1
      apply hu1
      calc
        u = g * u' * g⁻¹ := by dsimp [u']; group
        _ = 1 := by rw [h1]; group
    have hv'1 : v' ≠ 1 := by
      intro h1
      apply hv1
      calc
        v = g * v' * g⁻¹ := by dsimp [v']; group
        _ = 1 := by rw [h1]; group
    obtain ⟨n, hn⟩ := hb0_trans u' hu'U hu'1 v' hv'U hv'1
    refine ⟨n, ?_⟩
    have e : b ^ n * u * (b ^ n)⁻¹ = g * (b0 ^ n * u' * (b0 ^ n)⁻¹) * g⁻¹ := by
      rw [hbpow n]
      dsimp [u']
      group
    rw [e, hn]
    dsimp [v']
    group
  have hbfpf : ∀ u ∈ (T : Subgroup (PSL(2, K))), u ≠ 1 →
      b * u * b⁻¹ ≠ u := by
    intro u hu hu1 hfix
    let u' : PSL(2, K) := g⁻¹ * u * g
    have hu'U : u' ∈ (U : Subgroup (PSL(2, K))) := (hmem u).mp hu
    have hu'1 : u' ≠ 1 := by
      intro h1
      apply hu1
      calc
        u = g * u' * g⁻¹ := by dsimp [u']; group
        _ = 1 := by rw [h1]; group
    have hfix' : b0 * u' * b0⁻¹ = u' := by
      have h := congrArg (fun z : PSL(2, K) => g⁻¹ * z * g) hfix
      have e : g⁻¹ * (b * u * b⁻¹) * g = b0 * u' * b0⁻¹ := by
        simp only [b, u']
        group
      have e2 : g⁻¹ * u * g = u' := rfl
      rw [e, e2] at h
      exact h
    exact hb0_fpf u' hu'U hu'1 hfix'
  obtain ⟨eT, heT⟩ :=
    CFSG.Walter.W67.Borel5.exists_sylow_scalar_coordinate
      (F := K) (T := T) (g := g) a hTmap
  let μ : Kˣ := a ^ 2
  have hμord : orderOf μ = 15 := by
    dsimp [μ]
    exact (Nat.Coprime.orderOf_pow (y := a) (m := 2)
      (by rw [haord]; norm_num)).trans haord
  have hbconj : MulAut.conj g (torusHom K a) = b := by
    simp [b, b0, MulAut.conj_apply]
  have hμval : (μ : K) = (a : K) ^ 2 := by
    simp [μ]
  refine ⟨b, hbN, hb15, hbtrans, hbfpf, eT, μ, hμord, ?_⟩
  intro x
  simpa [hμval, hbconj] using heT x

end CFSG.Quasithin.H13

end
