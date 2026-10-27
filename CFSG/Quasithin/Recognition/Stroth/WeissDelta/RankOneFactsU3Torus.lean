module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalU32
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFacts

public section

open scoped Pointwise
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open Matrix

private lemma dvd_succ_of_dvd_two_mul_sub_one {q n : ℕ} (hq : 1 ≤ q)
    (hn : n ∣ 2 * q - 1) (hn' : n ∣ q ^ 2 - 1) : n ∣ q + 1 := by
  have hcop : Nat.Coprime n (q - 1) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have h1 : Nat.gcd n (q - 1) ∣ 2 * q - 1 := (Nat.gcd_dvd_left n (q - 1)).trans hn
    have h2 : Nat.gcd n (q - 1) ∣ q - 1 := Nat.gcd_dvd_right n (q - 1)
    have h3 : Nat.gcd n (q - 1) ∣ 2 * (q - 1) := dvd_mul_of_dvd_right h2 2
    have h4 : Nat.gcd n (q - 1) ∣ 2 * q - 1 - 2 * (q - 1) := Nat.dvd_sub h1 h3
    have heq : 2 * q - 1 - 2 * (q - 1) = 1 := by omega
    exact Nat.dvd_one.mp (by rwa [heq] at h4)
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa using (Nat.sq_sub_sq (a := q) (b := 1))
  rw [hfac] at hn'
  exact hcop.dvd_of_dvd_mul_right hn'

private lemma dvd_succ_of_dvd_sub_two {q n : ℕ} (hq : 2 ≤ q)
    (hn : n ∣ q - 2) (hn' : n ∣ q ^ 2 - 1) : n ∣ q + 1 := by
  have h3 : n ∣ 3 := by
    have h1 : n ∣ (q - 2) * (q + 2) := dvd_mul_of_dvd_left hn (q + 2)
    have h2 : n ∣ q ^ 2 - 1 - (q - 2) * (q + 2) := Nat.dvd_sub hn' h1
    have hq4 : (q - 2) * (q + 2) = q ^ 2 - 4 := by
      rw [mul_comm]
      simpa using (Nat.sq_sub_sq (a := q) (b := 2)).symm
    have hqsq : 4 ≤ q ^ 2 := by
      have := Nat.pow_le_pow_left (by omega : 2 ≤ q) 2
      simpa using this
    have heq : q ^ 2 - 1 - (q - 2) * (q + 2) = 3 := by
      rw [hq4]
      omega
    rwa [heq] at h2
  have heq : q + 1 = q - 2 + 3 := by omega
  rw [heq]
  exact dvd_add hn h3

private lemma not_dvd_torus_card {q : ℕ} (hq : 4 ≤ q) (hqe : Even q) :
    ¬ (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∣ (q + 1) ^ 2 := by
  intro hdiv
  have hdvd : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
    have h1 : q + 1 ∣ q ^ 2 - 1 := by
      exact ⟨q - 1, by simpa using (Nat.sq_sub_sq (a := q) (b := 1))⟩
    exact (Nat.gcd_dvd_right 3 (q + 1)).trans h1
  set d := Nat.gcd 3 (q + 1) with hddef
  set m := (q ^ 2 - 1) / d with hmdef
  have hdm : d * m = q ^ 2 - 1 := by
    rw [hddef, hmdef]
    exact Nat.mul_div_cancel' hdvd
  have hmain : q ^ 2 - 1 ∣ d * (q + 1) ^ 2 := by
    obtain ⟨c, hc⟩ := hdiv
    refine ⟨c, ?_⟩
    calc d * (q + 1) ^ 2 = d * (m * c) := by rw [hc]
      _ = (d * m) * c := by ring
      _ = (q ^ 2 - 1) * c := by rw [hdm]
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa using (Nat.sq_sub_sq (a := q) (b := 1))
  have hright : d * (q + 1) ^ 2 = (q + 1) * (d * (q + 1)) := by ring
  rw [hfac, hright] at hmain
  rw [Nat.mul_dvd_mul_iff_left (by omega : 0 < q + 1)] at hmain
  have hqodd : Odd (q - 1) :=
    Nat.Even.sub_odd (by omega : 1 ≤ q) hqe odd_one
  have hcop : (q - 1).Coprime (q + 1) := by
    have h : q + 1 = (q - 1) + 2 := by omega
    rw [h, Nat.coprime_self_add_right]
    exact hqodd.coprime_two_right
  have hdivd : q - 1 ∣ d := hcop.dvd_of_dvd_mul_right hmain
  have h3 : q - 1 ∣ 3 := hdivd.trans (Nat.gcd_dvd_left 3 (q + 1))
  have hle : q - 1 ≤ 3 := Nat.le_of_dvd (by norm_num) h3
  have hqeq : q = 4 := by omega
  have hd1 : d = 1 := by
    rw [hddef, hqeq]
    norm_num
  have h1 : q - 1 ∣ 1 := hd1 ▸ hdivd
  have hle1 : q - 1 ≤ 1 := Nat.le_of_dvd (by norm_num) h1
  omega

theorem fix_torusPSU_pow {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : ℕ) (hcard : Nat.card K = (2 ^ k) ^ 2)
    (hconj : ∀ z : K, J.conj z = z ^ (2 ^ k)) (c : Kˣ)
    (hc : c ^ (2 ^ k + 1) ≠ 1) (x : unitaryIsotropicPoints J)
    (hx : (torusPSU J hJ c) • x = x) :
    x = unitaryOuterIsotropicPoint J hJ 0 (by decide) ∨
      x = unitaryOuterIsotropicPoint J hJ 2 (by decide) := by
  classical
  obtain ⟨v, hv, hxv, hiso⟩ := x.2
  have hqpos : 0 < 2 ^ k := by positivity
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hcard1 : Nat.card K = 1 := by
      rw [hk0] at hcard
      norm_num at hcard
      exact hcard
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hq2 : 2 ≤ 2 ^ k := by
    have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk1
    simpa using h
  have hcne : (c : K) ≠ 0 := Units.ne_zero c
  have hconjne : J.conj (c : K) ≠ 0 := by
    intro h
    exact hcne (J.conj.injective (by rw [h, map_zero]))
  have hcK : (c : K) ^ (2 ^ k + 1) ≠ 1 := by
    intro h
    apply hc
    ext
    simpa using h
  have hcoe : ((torusPSU J hJ c : ProjectiveSpecialUnitaryMatrixGroup J) :
        Matrix.ProjGenLinGroup (Fin 3) K) • (x : ℙ K (Fin 3 → K)) =
      Projectivization.mk K
        (((torusGL J c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        ((smul_ne_zero_iff_ne (torusGL J c)).2 hv) := by
    rw [torusPSU_val, hxv, Projectivization.PGL.mk_smul_mk]
    rfl
  have hx' : ((torusPSU J hJ c : ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) • (x : ℙ K (Fin 3 → K)) =
        (x : ℙ K (Fin 3 → K)) := by
    have h := congrArg Subtype.val hx
    rwa [coe_smul_unitaryIsotropicPoints] at h
  have hproj : Projectivization.mk K
        (((torusGL J c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        ((smul_ne_zero_iff_ne (torusGL J c)).2 hv) = Projectivization.mk K v hv := by
    rw [← hxv, ← hx', hcoe]
  obtain ⟨mu, hmu⟩ := (Projectivization.mk_eq_mk_iff' K _ v _ hv).mp hproj
  have h0 : mu * v 0 = (c : K) * v 0 := by
    have h := congrFun hmu 0
    simpa [torusGL_val, torusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, smul_eq_mul] using h
  have h1 : mu * v 1 = (J.conj (c : K) / (c : K)) * v 1 := by
    have h := congrFun hmu 1
    simpa [torusGL_val, torusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, smul_eq_mul] using h
  have h2 : mu * v 2 = (J.conj (c : K))⁻¹ * v 2 := by
    have h := congrFun hmu 2
    simpa [torusGL_val, torusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, smul_eq_mul] using h
  have hv1 : v 1 = 0 := by
    by_contra hv1
    by_cases hv0 : v 0 = 0
    · by_cases hv2 : v 2 = 0
      · exfalso
        have hiso0 : J.conj (v 1) * v 1 = 0 := by
          have h := hiso
          rw [CFSG.UnitaryThreeRecognition.Model.selfPairing_std J hJ] at h
          simpa [hv0, hv2] using h
        rw [hconj] at hiso0
        have hq : (2 ^ k) ≠ 0 := by positivity
        rcases mul_eq_zero.mp hiso0 with h' | h'
        · exact hv1 ((pow_eq_zero_iff hq).mp h')
        · exact hv1 h'
      · have hmu1 : mu = J.conj (c : K) / (c : K) := mul_right_cancel₀ hv1 h1
        have hmu2 : mu = (J.conj (c : K))⁻¹ := mul_right_cancel₀ hv2 h2
        have heq : J.conj (c : K) / (c : K) = (J.conj (c : K))⁻¹ :=
          hmu1.symm.trans hmu2
        have hsq : (J.conj (c : K)) ^ 2 = (c : K) := by
          have h1' : J.conj (c : K) = (J.conj (c : K))⁻¹ * (c : K) := by
            have h := congrArg (fun t => t * (c : K)) heq
            rwa [div_mul_cancel₀ _ hcne] at h
          calc (J.conj (c : K)) ^ 2
              = J.conj (c : K) * J.conj (c : K) := pow_two _
            _ = ((J.conj (c : K))⁻¹ * (c : K)) * J.conj (c : K) :=
                congrArg (fun t => t * J.conj (c : K)) h1'
            _ = (J.conj (c : K))⁻¹ * ((c : K) * J.conj (c : K)) :=
                mul_assoc _ _ _
            _ = (J.conj (c : K))⁻¹ * (J.conj (c : K) * (c : K)) := by
                rw [mul_comm (c : K) (J.conj (c : K))]
            _ = ((J.conj (c : K))⁻¹ * J.conj (c : K)) * (c : K) :=
                (mul_assoc _ _ _).symm
            _ = (c : K) := by rw [inv_mul_cancel₀ hconjne, one_mul]
        have h2q : (c : K) ^ (2 * 2 ^ k) = (c : K) := by
          rw [mul_comm 2 (2 ^ k), pow_mul, ← hconj, hsq]
        have hpow : (c : K) ^ (2 * 2 ^ k - 1) = 1 := by
          have hmain : (c : K) ^ (2 * 2 ^ k - 1) * (c : K) = 1 * (c : K) := by
            rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
            exact h2q
          exact mul_right_cancel₀ hcne hmain
        have hn2 : orderOf c ∣ 2 * 2 ^ k - 1 := by
          rw [← orderOf_units]
          exact orderOf_dvd_of_pow_eq_one hpow
        have hn1 : orderOf c ∣ (2 ^ k) ^ 2 - 1 := by
          rw [← hcard, ← Nat.card_units]
          exact orderOf_dvd_natCard c
        have hdvd : orderOf c ∣ 2 ^ k + 1 :=
          dvd_succ_of_dvd_two_mul_sub_one (by omega) hn2 hn1
        have hc1 : c ^ (2 ^ k + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
        exact hcK (by simpa using congrArg (fun u : Kˣ => (u : K)) hc1)
    · have hmu1 : mu = J.conj (c : K) / (c : K) := mul_right_cancel₀ hv1 h1
      have hmu0 : mu = (c : K) := mul_right_cancel₀ hv0 h0
      have heq : (c : K) = J.conj (c : K) / (c : K) := hmu0.symm.trans hmu1
      have hsq : (c : K) ^ 2 = J.conj (c : K) := by
        have h := congrArg (fun t => t * (c : K)) heq
        rw [div_mul_cancel₀ _ hcne] at h
        rw [pow_two]
        exact h
      have h2q : (c : K) ^ (2 ^ k) = (c : K) ^ 2 := by
        rw [← hconj]
        exact hsq.symm
      have hpow : (c : K) ^ (2 ^ k - 2) = 1 := by
        have hmain : (c : K) ^ (2 ^ k - 2) * (c : K) ^ 2 = 1 * (c : K) ^ 2 := by
          rw [one_mul, ← pow_add, Nat.sub_add_cancel (by omega), h2q]
        exact mul_right_cancel₀ (pow_ne_zero 2 hcne) hmain
      have hn2 : orderOf c ∣ 2 ^ k - 2 := by
        rw [← orderOf_units]
        exact orderOf_dvd_of_pow_eq_one hpow
      have hn1 : orderOf c ∣ (2 ^ k) ^ 2 - 1 := by
        rw [← hcard, ← Nat.card_units]
        exact orderOf_dvd_natCard c
      have hdvd : orderOf c ∣ 2 ^ k + 1 :=
        dvd_succ_of_dvd_sub_two (by omega) hn2 hn1
      have hc1 : c ^ (2 ^ k + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      exact hcK (by simpa using congrArg (fun u : Kˣ => (u : K)) hc1)
  by_cases hv0 : v 0 = 0
  · right
    have hv2 : v 2 ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i <;> simp [hv0, hv1, h]
    apply Subtype.ext
    show (x : ℙ K (Fin 3 → K)) = Projectivization.mk K (Pi.single 2 1) _
    rw [hxv, Projectivization.mk_eq_mk_iff']
    refine ⟨v 2, ?_⟩
    funext i
    fin_cases i <;> simp [Pi.single_apply, hv0, hv1]
  · left
    have hv2 : v 2 = 0 := by
      by_contra hv2
      have hmu0 : mu = (c : K) := mul_right_cancel₀ hv0 h0
      have hmu2 : mu = (J.conj (c : K))⁻¹ := mul_right_cancel₀ hv2 h2
      have heq : (c : K) = (J.conj (c : K))⁻¹ := hmu0.symm.trans hmu2
      have hcq1 : (c : K) ^ (2 ^ k + 1) = 1 := by
        have hmul : (c : K) * J.conj (c : K) = 1 := by
          have h := congrArg (fun t => t * J.conj (c : K)) heq
          rw [inv_mul_cancel₀ hconjne] at h
          exact h
        rw [hconj, mul_comm] at hmul
        simpa [pow_succ] using hmul
      exact hcK hcq1
    apply Subtype.ext
    show (x : ℙ K (Fin 3 → K)) = Projectivization.mk K (Pi.single 0 1) _
    rw [hxv, Projectivization.mk_eq_mk_iff']
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [Pi.single_apply, hv1, hv2]

theorem rankOneUnitary_psu3 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (k : ℕ) (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F))
    (hΩ : Fintype.card Ω = 2 ^ (3 * k) + 1) :
    RankOneUnitary X Ω N (2 ^ k) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : N.Normal := hN
  let M := Classical.choice (exists_psu3_isotropicModel h2 k hk F hF N hN e hΩ)
  let J := M.J
  let hJ := M.hJ
  let hconj := M.hconj
  let eN := M.eN
  let φ₀ := M.φ
  let T' := M.T'
  let U' := M.U'
  let B' := M.B'
  let Ω₀ := unitaryIsotropicPoints J
  let α : Ω₀ := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  let β₀ : Ω₀ := unitaryOuterIsotropicPoint J hJ 2 (by decide)
  let ω : Ω := φ₀.symm α
  let β : Ω := φ₀.symm β₀
  have hP : UnitaryPointStructure ↥N Ω ω β U' T' B' := M.hP
  have hφ₀ := M.hequiv
  have hT'card : Nat.card T' = ((2 ^ k) ^ 2 - 1) / Nat.gcd 3 (2 ^ k + 1) := M.hT'card
  have hT'cyc : IsCyclic T' := M.hT'cyc
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqeven : Even (2 ^ k) := by
    exact (show Even 2 from ⟨1, by norm_num⟩).pow_of_ne_zero (by omega : k ≠ 0)
  have hdvd : Nat.gcd 3 (2 ^ k + 1) ∣ (2 ^ k) ^ 2 - 1 := by
    have h1 : 2 ^ k + 1 ∣ (2 ^ k) ^ 2 - 1 := by
      exact ⟨2 ^ k - 1, by simpa using (Nat.sq_sub_sq (a := 2 ^ k) (b := 1))⟩
    exact (Nat.gcd_dvd_right 3 (2 ^ k + 1)).trans h1
  have hfixModel : ∀ c : Fˣ, c ^ (2 ^ k + 1) ≠ 1 → ∀ z : Ω₀,
      (torusPSU J hJ c) • z = z →
        z = unitaryOuterIsotropicPoint J hJ 0 (by decide) ∨
          z = unitaryOuterIsotropicPoint J hJ 2 (by decide) :=
    fun c hc z hz => fix_torusPSU_pow J hJ k hF hconj c hc z hz
  have hT'model : ∀ t : ↥N, t ∈ T' → t ^ (2 ^ k + 1) ≠ 1 →
      ∀ z : Ω, t • z = z → z = ω ∨ z = β := by
    intro t ht hpow z hz
    change t ∈ M.T' at ht
    rw [M.hT'] at ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hs
    have hc : c ^ (2 ^ k + 1) ≠ 1 := by
      intro hc1
      apply hpow
      apply eN.injective
      simp only [MulEquiv.coe_toMonoidHom]
      rw [map_pow, eN.apply_symm_apply]
      rw [← map_pow, hc1, map_one]
      simp
    have hfix : (torusPSU J hJ c) • (φ₀ z) = φ₀ z := by
      have hz' : (eN.symm ((torusPSU J hJ) c)) • z = z := hz
      have h1 := hφ₀ (eN.symm (torusPSU J hJ c)) z
      rw [hz', eN.apply_symm_apply] at h1
      exact h1.symm
    rcases hfixModel c hc (φ₀ z) hfix with h | h
    · left
      calc z = φ₀.symm (φ₀ z) := (φ₀.symm_apply_apply z).symm
        _ = φ₀.symm α := by rw [h]
        _ = ω := rfl
    · right
      calc z = φ₀.symm (φ₀ z) := (φ₀.symm_apply_apply z).symm
        _ = φ₀.symm β₀ := by rw [h]
        _ = β := rfl
  have hfield : ∀ a y : Ω, N ⊓ MulAction.stabilizer X a ⊓ MulAction.stabilizer X y =
      (MulAction.stabilizer ↥N a ⊓ MulAction.stabilizer ↥N y).map N.subtype :=
    fun a y => inf_stabilizer_eq_map_subtype (N := N) (x := a) (y := y) rfl
  refine
    { fix_two := ?_
      pow_card := ?_
      exists_pow := ?_ }
  · intro a b hab t ht htpow z hz
    obtain ⟨g, hgω, hgβ, hgp⟩ := hP.exists_conj_torus hab.symm
    let tN : ↥N := ⟨t, ht.1.1⟩
    have htNmem : tN ∈ MulAction.stabilizer ↥N a ⊓ MulAction.stabilizer ↥N b := by
      constructor
      · change (tN : ↥N) • a = a
        exact MulAction.mem_stabilizer_iff.mp ht.1.2
      · change (tN : ↥N) • b = b
        exact MulAction.mem_stabilizer_iff.mp ht.2
    have htNpair : tN ∈ T'.map (MulAut.conj g).toMonoidHom := by
      rw [← hgp]
      exact htNmem
    obtain ⟨s, hs, hts⟩ := Subgroup.mem_map.mp htNpair
    have hts' : (MulAut.conj g) s = tN := hts
    have htNpow : tN ^ (2 ^ k + 1) ≠ 1 := by
      intro h1
      apply htpow
      have h2 := congrArg N.subtype h1
      simpa [tN] using h2
    have hs_pow : (s : ↥N) ^ (2 ^ k + 1) ≠ 1 := by
      intro h1
      apply htNpow
      rw [show tN = (MulAut.conj g) (s : ↥N) from hts'.symm, ← map_pow, h1, map_one]
    have hsfix : (s : ↥N) • (g⁻¹ • z) = g⁻¹ • z := by
      have hgs : g • ((s : ↥N) • (g⁻¹ • z)) = g • (g⁻¹ • z) := by
        calc g • ((s : ↥N) • (g⁻¹ • z)) = (g * (s : ↥N) * g⁻¹) • z := by
              rw [← mul_smul, ← mul_smul]
          _ = ((MulAut.conj g) (s : ↥N)) • z := rfl
          _ = tN • z := by rw [hts']
          _ = z := hz
          _ = g • (g⁻¹ • z) := (smul_inv_smul g z).symm
      have := congrArg (fun w => g⁻¹ • w) hgs
      simpa [smul_smul] using this
    rcases hT'model (s : ↥N) hs hs_pow (g⁻¹ • z) hsfix with h | h
    · left
      calc z = g • (g⁻¹ • z) := (smul_inv_smul g z).symm
        _ = g • ω := by rw [h]
        _ = a := hgω
    · right
      calc z = g • (g⁻¹ • z) := (smul_inv_smul g z).symm
        _ = g • β := by rw [h]
        _ = b := hgβ
  · intro a b hab t ht
    obtain ⟨g, -, -, hgp⟩ := hP.exists_conj_torus hab.symm
    let tN : ↥N := ⟨t, ht.1.1⟩
    have htNmem : tN ∈ MulAction.stabilizer ↥N a ⊓ MulAction.stabilizer ↥N b := by
      constructor
      · change (tN : ↥N) • a = a
        exact MulAction.mem_stabilizer_iff.mp ht.1.2
      · change (tN : ↥N) • b = b
        exact MulAction.mem_stabilizer_iff.mp ht.2
    have htNpair : tN ∈ T'.map (MulAut.conj g).toMonoidHom := by
      rw [← hgp]
      exact htNmem
    have hcardpair : Nat.card ↥(MulAction.stabilizer ↥N a ⊓
        MulAction.stabilizer ↥N b) = Nat.card T' := by
      rw [hgp, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hdivT : Nat.card T' ∣ (2 ^ k) ^ 2 - 1 := by
      rw [hT'card]
      exact Nat.div_dvd_of_dvd hdvd
    have horder : orderOf tN ∣ (2 ^ k) ^ 2 - 1 :=
      (Subgroup.orderOf_dvd_natCard _ htNmem).trans (by rw [hcardpair]; exact hdivT)
    have htNpow : tN ^ ((2 ^ k) ^ 2 - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp horder
    have h2 := congrArg N.subtype htNpow
    simpa [tN] using h2
  · intro a b hab
    obtain ⟨g, hgω, hgβ, hgp⟩ := hP.exists_conj_torus hab.symm
    haveI : IsCyclic T' := hT'cyc
    obtain ⟨s, hs⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := T')
    have hsne : (s ^ (2 ^ k + 1)) ^ (2 ^ k + 1) ≠ 1 := by
      intro h1
      apply not_dvd_torus_card (q := 2 ^ k) hq4 hqeven
      rw [← hT'card, ← hs]
      apply orderOf_dvd_iff_pow_eq_one.mpr
      rw [pow_two, pow_mul]
      exact h1
    have hsneN : ((s : ↥N) ^ (2 ^ k + 1)) ^ (2 ^ k + 1) ≠ 1 := by
      intro h1
      apply hsne
      exact Subtype.ext (by simpa using h1)
    let tN : ↥N := g * (s : ↥N) * g⁻¹
    have htNmem : tN ∈ T'.map (MulAut.conj g).toMonoidHom := by
      exact Subgroup.mem_map_of_mem _ s.2
    have htNpair : tN ∈ MulAction.stabilizer ↥N a ⊓ MulAction.stabilizer ↥N b := by
      rw [hgp]
      exact htNmem
    refine ⟨(tN : X), ?_, ?_⟩
    · rw [hfield a b]
      exact Subgroup.mem_map_of_mem _ htNpair
    · have hconjpow : tN ^ (2 ^ k + 1) =
          (MulAut.conj g) ((s : ↥N) ^ (2 ^ k + 1)) := by
        rw [show tN = (MulAut.conj g) (s : ↥N) from by
          simp [tN, MulAut.conj_apply], ← map_pow]
      have htNpow : (tN ^ (2 ^ k + 1)) ^ (2 ^ k + 1) ≠ 1 := by
        intro h1
        apply hsneN
        apply (MulAut.conj g).injective
        simpa [hconjpow, map_pow] using h1
      intro h1
      apply htNpow
      apply N.subtype_injective
      simpa using h1

end CFSG.Quasithin.Stroth.WeissDelta

end
