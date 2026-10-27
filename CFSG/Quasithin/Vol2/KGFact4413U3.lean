module

public import CFSG.Quasithin.Vol2.KGFact4413L2
public import CFSG.Quasithin.H13.KGFact22TorU3

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.QuasithinUnique CFSG.Quasithin.H13.KG22
open scoped Matrix LinearAlgebra.Projectivization Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {J : HermitianForm 3 K}

omit [Finite K] in
theorem fixU_inf_normU : fixU J ⊓ normU J = ⊥ := by
  rw [eq_bot_iff]
  rintro k ⟨hk1, hk2⟩
  have h1 : J.conj (k : K) = k := hk1
  have h2 : J.conj (k : K) * k = 1 := hk2
  rw [h1] at h2
  have h3 : ((k : K) + 1) * ((k : K) + 1) = 0 := by
    have e : ((k : K) + 1) * ((k : K) + 1) = (k : K) * k + 1 + 2 * (k : K) := by ring
    rw [e, h2, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
  have h4 : (k : K) + 1 = 0 := mul_self_eq_zero.1 h3
  have h5 : (k : K) = 1 := by
    rw [← CharTwo.neg_eq (1 : K)]
    exact eq_neg_of_add_eq_zero_left h4
  exact Subgroup.mem_bot.mpr (Units.ext h5)

theorem mul_add_one_sub_one {q : ℕ} (hq : 1 ≤ q) : (q - 1) * (q + 1) = q ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
  rw [this, Nat.add_sub_cancel]

theorem card_normU {q : ℕ} (hq : 2 ≤ q) (hKcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) : Nat.card (normU J) = q + 1 := by
  have hsup : fixU J ⊔ normU J = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := exists_fix_mul_norm (J := J) k
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk₁) (Subgroup.mem_sup_right hk₂)
  have hN : fixU J ≤ Subgroup.normalizer (normU J : Set Kˣ) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mul_comm x y, mul_inv_cancel_right]
  have h1 := E2.BorelLift.card_sup_mul_card_inf hN
  rw [hsup, fixU_inf_normU, Subgroup.card_bot, mul_one, Subgroup.card_top, Nat.card_units,
    hKcard, card_fixU, hfixed] at h1
  rw [← mul_add_one_sub_one (by omega : 1 ≤ q)] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h1).symm

theorem weylOut_psu3 {f : ℕ} (hf : 2 ≤ f) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) :
    ∃ S₀ D₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsSylowTwoOf S₀ ⊤ ∧
      D₀ ≤ Subgroup.normalizer (S₀ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
      Subgroup.normalizer (S₀ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ D₀ ⊔ S₀ ∧
      D₀ ⊓ S₀ = ⊥ ∧ WeylOut S₀ D₀ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := 2 ^ f
  have hq2 : 2 ≤ q := by
    show 2 ≤ 2 ^ f
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  rcases External.huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨hΩcard, rho, a, _hinj, _hnatural, _hUcard,
      ⟨R, D, hRle, hDle, hN, _hinf, hsup, _hcyc, hRcard,
        _hcomm, _hcommcard, _hDcard, hreg, ⟨coord, hcoord⟩,
        hDcoord, hDsurj⟩, htwo, _hGcard, _hthree⟩
  let : MulAction G Ω := MulAction.compHom Ω rho
  have hstab : (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho =
      MulAction.stabilizer G a := by
    ext g
    rfl
  have hRle' : R ≤ MulAction.stabilizer G a := hstab ▸ hRle
  have hsup' : R ⊔ D = MulAction.stabilizer G a := hsup.trans hstab
  have hDN : D ≤ Subgroup.normalizer (R : Set G) := hDle.trans hN
  have hΩ2 : ∀ b : Ω, ∃ c : Ω, c ≠ b := by
    classical
    intro b
    have := Fintype.ofFinite Ω
    have hc : 1 < Fintype.card Ω := by
      rw [← Nat.card_eq_fintype_card, hΩcard]
      have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card hc b
    exact ⟨c, hc⟩
  have h3 : ∃ b c : Ω, b ≠ a ∧ c ≠ a ∧ b ≠ c := by
    classical
    have := Fintype.ofFinite Ω
    have hc : Fintype.card Ω = q ^ 3 + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact hΩcard
    have h2 : 2 < Fintype.card Ω := by
      have h8 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
      rw [hc]
      omega
    obtain ⟨b₁, b₂, b₃, h12, h13, h23⟩ := Fintype.two_lt_card_iff.1 h2
    by_cases ha : b₁ = a
    · exact ⟨b₂, b₃, fun h => h12 (ha.trans h.symm), fun h => h13 (ha.trans h.symm), h23⟩
    · by_cases hb : b₂ = a
      · exact ⟨b₁, b₃, ha, fun h => h23 (hb.trans h.symm), h13⟩
      · exact ⟨b₁, b₂, ha, hb, h12⟩
  have hNR : Subgroup.normalizer (R : Set G) ≤ R ⊔ D := by
    rw [hsup']
    exact normalizer_le_stabilizer_of_regular hRle' hreg h3
  have hNeq : Subgroup.normalizer (R : Set G) = R ⊔ D :=
    le_antisymm hNR (sup_le Subgroup.le_normalizer hDN)
  have htrans : MulAction.IsPretransitive G Ω := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', hx'⟩ := hΩ2 x
    obtain ⟨y', hy'⟩ := hΩ2 y
    obtain ⟨g, hg, -⟩ := htwo x x' y y' (Ne.symm hx') (Ne.symm hy')
    exact ⟨g, hg⟩
  have hNidx : (Subgroup.normalizer (R : Set G)).index = q ^ 3 + 1 := by
    rw [hNeq, hsup', MulAction.index_stabilizer_of_transitive, hΩcard]
  have huD : ∀ k : Kˣ, uP hJ k ∈ D := by
    intro k
    obtain ⟨h, M, hM, hhM⟩ := hDsurj k
    have hMk : M = uT J k := Units.ext (by rw [hM, coe_uT])
    have : uP hJ k = (h : G) := Subtype.ext (by rw [coe_uP, ← hMk, hhM])
    rw [this]
    exact h.2
  have hDk : ∀ d ∈ D, ∃ k : Kˣ, d = uP hJ k := by
    intro d hd
    obtain ⟨k, M, hM, hdM⟩ := hDcoord ⟨d, hd⟩
    have hMk : M = uT J k := Units.ext (by rw [hM, coe_uT])
    exact ⟨k, Subtype.ext (by rw [coe_uP, ← hMk, ← hdM])⟩
  have hR2 : IsPGroup 2 R :=
    IsPGroup.of_card (n := f * 3) (by simpa only [q, ← pow_mul] using hRcard)
  obtain ⟨P₀, hP₀⟩ := hR2.exists_le_sylow
  have hB := CFSG.Open.bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ
  have hP₀card : Nat.card (P₀ : Subgroup G) = q ^ 3 := (hB P₀).2.2.2.2
  have hRP : R = (P₀ : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hP₀ (by rw [hP₀card, hRcard])
  have hRS : IsSylowTwoOf R ⊤ := hRP ▸ isSylowTwoOf_of_sylow P₀
  have hKu : Nat.card Kˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_units, hKcard, mul_add_one_sub_one (by omega)]
  have hkexp : ∀ k : Kˣ, k ^ ((q - 1) * (q + 1)) = 1 := fun k => by
    rw [← hKu]
    exact pow_card_eq_one'
  have hfixexp : ∀ k ∈ fixU J, k ^ (q - 1) = 1 := by
    intro k hk
    have h1 := pow_card_eq_one' (G := fixU J) (x := ⟨k, hk⟩)
    rw [card_fixU, hfixed] at h1
    exact congrArg Subtype.val h1
  have hnormexp : ∀ k ∈ normU J, k ^ (q + 1) = 1 := by
    intro k hk
    have h1 := pow_card_eq_one' (G := normU J) (x := ⟨k, hk⟩)
    rw [card_normU hq2 hKcard hfixed] at h1
    exact congrArg Subtype.val h1
  have hDexp : ∀ d ∈ D, d ^ ((q - 1) * (q + 1)) = 1 := by
    intro d hd
    obtain ⟨k, rfl⟩ := hDk d hd
    rw [← map_pow, hkexp, map_one]
  have hqodd1 : Odd (q - 1) := by
    have hqe : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd (by omega) hqe odd_one
  have hqodd2 : Odd (q + 1) := by
    have hqe : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact hqe.add_one
  have hDodd : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    (hqodd1.mul hqodd2).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hDexp d hd))
  have hDR : D ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxD, hxR⟩
    obtain ⟨m, hm⟩ := hR2 ⟨x, hxR⟩
    exact Subgroup.mem_bot.mpr
      (eq_one_of_odd_of_pow_two_pow (hDodd x hxD) (congrArg Subtype.val hm))
  have hRup : ∀ r ∈ R, (r : Matrix.ProjGenLinGroup (Fin 3) K) ∈ upImg K := by
    intro r hr
    obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
    obtain ⟨M, hM, hzM⟩ := hcoord z
    refine ⟨M, ?_, ?_⟩
    · intro i j hij
      rw [hM]
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl
    · rw [← hzM, hz]
  have hDup : ∀ d ∈ D, (d : Matrix.ProjGenLinGroup (Fin 3) K) ∈ upImg K := by
    intro d hd
    obtain ⟨k, M, hM, hdM⟩ := hDcoord ⟨d, hd⟩
    refine ⟨M, ?_, hdM⟩
    intro i j hij
    rw [hM]
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl
  have hRDup : ∀ x ∈ R ⊔ D, (x : Matrix.ProjGenLinGroup (Fin 3) K) ∈ upImg K := by
    intro x hx
    have hx' : x ∈ (R : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left R D hDN]
      exact hx
    obtain ⟨r, hr, d, hd, rfl⟩ := Set.mem_mul.1 hx'
    rw [Subgroup.coe_mul]
    exact mul_mem_upImg (hRup r hr) (hDup d hd)
  have hwN : wP hJ ∉ Subgroup.normalizer (R : Set G) := by
    intro hw
    have := hRDup _ (hNR hw)
    rw [coe_wP] at this
    exact wGL_not_mem_upImg this
  have hww : wP hJ * wP hJ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_wP, ← map_mul, Subgroup.coe_one]
    have : (wGL : GL (Fin 3) K) * wGL = 1 := by
      nth_rewrite 2 [← wGL_inv (K := K)]
      exact mul_inv_cancel _
    rw [this, map_one]
  have hwfix : ∀ k ∈ fixU J, wP hJ * uP hJ k * (wP hJ)⁻¹ = (uP hJ k)⁻¹ := by
    intro k hk
    have hσ : J.conj (k : K) = k := hk
    have hu : (Units.map J.conj.toMonoidHom k)⁻¹ = k⁻¹ := by
      have : Units.map J.conj.toMonoidHom k = k := Units.ext hσ
      rw [this]
    rw [wP_conj_uP, hu, map_inv]
  have hwnorm : ∀ k ∈ normU J, wP hJ * uP hJ k * (wP hJ)⁻¹ = uP hJ k := by
    intro k hk
    have hσ : J.conj (k : K) * k = 1 := hk
    have hu : (Units.map J.conj.toMonoidHom k)⁻¹ = k := by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val]
      exact inv_eq_of_mul_eq_one_right hσ
    rw [wP_conj_uP, hu]
  have hsq : ∀ x : G, x ^ (q - 1) = 1 → x ^ (q + 1) = 1 → x = 1 := by
    intro x h1 h2
    have h3 : x ^ 2 = 1 := by
      have e : q + 1 = (q - 1) + 2 := by omega
      rw [e, pow_add, h1, one_mul] at h2
      exact h2
    have hco : Nat.Coprime 2 (q - 1) := Nat.coprime_two_left.2 hqodd1
    have h4 : orderOf x ∣ Nat.gcd 2 (q - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h1)
    rw [hco, Nat.dvd_one] at h4
    exact orderOf_eq_one_iff.1 h4
  refine ⟨R, D, hRS, hDN, by rw [hNeq, sup_comm], hDR, ?_, hDexp, wP hJ, hwN, hww, ?_⟩
  · intro p hp hp2 hpq
    rw [hNidx]
    exact not_dvd_pow_add_one hp hp2 (by omega) hpq 3
  · intro d hd
    obtain ⟨k, rfl⟩ := hDk d hd
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := exists_fix_mul_norm (J := J) k
    have hc : Commute (uP hJ k₁) (uP hJ k₂) := by
      show uP hJ k₁ * uP hJ k₂ = uP hJ k₂ * uP hJ k₁
      rw [← map_mul, ← map_mul, mul_comm]
    have h1 : (uP hJ k₁) ^ (q - 1) = 1 := by rw [← map_pow, hfixexp k₁ hk₁, map_one]
    have h2 : (uP hJ k₂) ^ (q + 1) = 1 := by rw [← map_pow, hnormexp k₂ hk₂, map_one]
    rw [map_mul]
    refine ⟨fun hd1 => ?_, fun hd2 => ?_⟩
    ·
      have h3 : (uP hJ k₂) ^ (q - 1) = 1 := by
        rw [hc.mul_pow, h1, one_mul] at hd1
        exact hd1
      rw [hsq _ h3 h2, mul_one, hwfix k₁ hk₁]
    ·
      have h3 : (uP hJ k₁) ^ (q + 1) = 1 := by
        rw [hc.mul_pow, h2, mul_one] at hd2
        exact hd2
      rw [hsq _ h1 h3, one_mul, hwnorm k₂ hk₂]

theorem cartanWeyl_of_isPSU3 {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f) (hX : IsPSU 3 2 f X) :
    CartanWeyl X f := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := hX
  have hcard : Nat.card K₀ = 2 ^ (2 * f) := by rw [hK₀, ← pow_mul, mul_comm]
  let e₁ : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K₀ (2 ^ f)) := e
  let e₂ : X ≃* CFSG.Open.PSU3 2 f :=
    e₁.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  have : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₃ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = CFSG.Open.PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₄ : ProjectiveSpecialUnitaryMatrixGroup J ≃* CFSG.Open.PSU3 2 f :=
    e₃.trans (MulEquiv.subgroupCongr hmodel)
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
    have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    exact Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J => (x : Matrix.ProjGenLinGroup (Fin 3) K))
      Subtype.coe_injective
  obtain ⟨S₀, D₀, hS₀, h1, h2, h3, hW⟩ := weylOut_psu3 hf hJ hKcard hfixed
  exact cartanWeyl_of_mulEquiv (cartanWeyl_of_exists hS₀ h1 h2 h3 hW) (e₂.trans e₄.symm).symm

end CFSG.Quasithin.H13.KG4413
