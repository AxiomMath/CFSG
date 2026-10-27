module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofModelA
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
open scoped Matrix


@[expose] def latE : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 0, -1]

@[expose] def latF : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 2, 2]

@[expose] def latPreE : Fin TwistTag.D4.tag.rank → ℤ := ![-1, -2, -2, -1]

@[expose] def vBeta0 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 2, 1]

@[expose] def vBeta1 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 1, 1]

@[expose] def vBeta2 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 1, 1]

abbrev vTt : WeylGroup TwistTag.D4.tag := (coxeterSystem TwistTag.D4.tag).wordProd [0, 2, 1]

theorem vTt_smul_latPreE : vTt • latPreE = latE := by
  rw [KS11Lie5Proof.wordProd_smul]
  decide

theorem vTt_smul_latF : vTt • latF = latF := by
  rw [KS11Lie5Proof.wordProd_smul]
  decide

theorem vTt_smul_single_two :
    vTt • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = Pi.single 1 1 := by
  rw [KS11Lie5Proof.wordProd_smul]
  decide

theorem vTt_smul_single_zero :
    vTt • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = Pi.single 2 1 := by
  rw [KS11Lie5Proof.wordProd_smul]
  decide

theorem vT_smul (β : Fin Tag.D4.rank → ℤ) : vT • β = wordVec [0, 2, 1] β :=
  KS11Lie5Proof.wordProd_smul [0, 2, 1] β

theorem vT_smul_d4A2Weight :
    vT • d4A2Weight 0 = vBeta0 ∧ vT • d4A2Weight 1 = vBeta1 ∧ vT • d4A2Weight 2 = vBeta2 :=
  ⟨(vT_smul _).trans (by decide : wordVec [0, 2, 1] (d4A2Weight 0) = vBeta0),
    (vT_smul _).trans (by decide : wordVec [0, 2, 1] (d4A2Weight 1) = vBeta1),
    (vT_smul _).trans (by decide : wordVec [0, 2, 1] (d4A2Weight 2) = vBeta2)⟩

theorem vBeta_sum : vBeta0 + vBeta1 + vBeta2 = latE + 2 • latF := by
  decide

theorem pairing_latPreE_latF :
    (∑ j, Tag.D4.cartan 0 j * latPreE j) = 0 ∧ (∑ j, Tag.D4.cartan 2 j * latPreE j) = 0 ∧
      (∑ j, Tag.D4.cartan 0 j * latF j) = 0 ∧ (∑ j, Tag.D4.cartan 2 j * latF j) = 0 := by
  decide

theorem gT_pairing_vBeta :
    (∑ i, ((vBeta0 i : ℤ) : ZMod 3) * gT i) = 2 ∧ (∑ i, ((vBeta1 i : ℤ) : ZMod 3) * gT i) = 2 ∧
      (∑ i, ((vBeta2 i : ℤ) : ZMod 3) * gT i) = 2 := by
  decide

theorem threeSixW_latE_latF :
    threeSixW 1 *ᵥ (-(latE + latF)) = latE ∧ threeSixW 1 *ᵥ latE = latF ∧
      threeSixW (-1) *ᵥ (latE + latF) = latE ∧ threeSixW (-1) *ᵥ (-latE) = latF := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i
  · obtain ⟨h0, h1, h2, h3⟩ := threeSixW_mulVec (Or.inl rfl) (-(latE + latF))
    fin_cases i
    · exact h0.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)
  · obtain ⟨h0, h1, h2, h3⟩ := threeSixW_mulVec (Or.inl rfl) latE
    fin_cases i
    · exact h0.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)
  · obtain ⟨h0, h1, h2, h3⟩ := threeSixW_mulVec (Or.inr rfl) (latE + latF)
    fin_cases i
    · exact h0.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)
  · obtain ⟨h0, h1, h2, h3⟩ := threeSixW_mulVec (Or.inr rfl) (-latE)
    fin_cases i
    · exact h0.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)

variable {Ω : Type} [Field Ω]

theorem rootChar_inv_tuple' {τ : Tag} (b : Fin τ.rank → Ωˣ) (l : Fin τ.rank → ℤ) :
    rootChar b⁻¹ l = (rootChar b l)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem rootChar_neg' {τ : Tag} (b : Fin τ.rank → Ωˣ) (l : Fin τ.rank → ℤ) :
    rootChar b (-l) = (rootChar b l)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]

theorem rootChar_cartan_row (i : Fin Tag.D4.rank) (t : Ωˣ) (l : Fin Tag.D4.rank → ℤ) :
    rootChar (fun j => t ^ Tag.D4.cartan i j) l = t ^ (∑ j, Tag.D4.cartan i j * l j) := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm

theorem canonicalRep_inv_conj_rootDiagUnit' {τ : Tag} (w : WeylGroup τ)
    (b : Fin τ.rank → Ωˣ) :
    (canonicalRep (coxeterSystem τ) Ω w)⁻¹ * rootDiagUnit τ b *
        canonicalRep (coxeterSystem τ) Ω w =
      rootDiagUnit τ (fun j => rootChar b (w • (Pi.single j 1 : Fin τ.rank → ℤ))) := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff (K := Ω) b
    (fun j => rootChar b (w • (Pi.single j 1 : Fin τ.rank → ℤ))) w).2
    fun l => rootChar_smul_eq_rootChar b w l
  rw [h]
  group

theorem rootChar_torusPair (t u : Ωˣ) (l : Fin Tag.D4.rank → ℤ) :
    rootChar ((fun j => t ^ Tag.D4.cartan 0 j) * (fun j => u ^ Tag.D4.cartan 2 j)) l =
      t ^ (∑ j, Tag.D4.cartan 0 j * l j) * u ^ (∑ j, Tag.D4.cartan 2 j * l j) := by
  rw [rootChar_mul_tuple, rootChar_cartan_row, rootChar_cartan_row]

theorem rootChar_latE_latF_of_mem {c : Fin TwistTag.D4.tag.rank → Ωˣ}
    (hc : rootDiagUnit TwistTag.D4.tag c ∈ d4A2Tv Ω vT) :
    rootChar c latE = 1 ∧ rootChar c latF = 1 := by
  obtain ⟨s₀, hs₀, hs⟩ := Subgroup.mem_map.1 hc
  obtain ⟨t, u, rfl⟩ := mem_subsystemTorus_d4A2.1 hs₀
  set c₀ : Fin Tag.D4.rank → Ωˣ :=
    (fun j => t ^ Tag.D4.cartan 0 j) * (fun j => u ^ Tag.D4.cartan 2 j) with hc₀def
  have hc₀ : d4A2TorusElt t u = rootDiagUnit Tag.D4 c₀ := by
    rw [d4A2TorusElt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, hc₀def,
      rootDiagUnit_mul]
  rw [hc₀] at hs
  have hconj : rootDiagUnit TwistTag.D4.tag c =
      canonicalRep (coxeterSystem TwistTag.D4.tag) Ω vTt * rootDiagUnit TwistTag.D4.tag c₀ *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) Ω vTt)⁻¹ := hs.symm
  have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff c c₀ vTt).1 hconj
  have hE := hchar latPreE
  have hF := hchar latF
  rw [vTt_smul_latPreE] at hE
  rw [vTt_smul_latF] at hF
  obtain ⟨p0, p2, q0, q2⟩ := pairing_latPreE_latF
  refine ⟨hE.trans ((rootChar_torusPair t u latPreE).trans ?_),
    hF.trans ((rootChar_torusPair t u latF).trans ?_)⟩
  · rw [p0, p2, zpow_zero, zpow_zero, mul_one]
  · rw [q0, q2, zpow_zero, zpow_zero, mul_one]

theorem rootChar_threeSixFrob_rootDiagUnit (Fr : Ω →+* Ω) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (ε : ℤ) (b : Fin TwistTag.D4.tag.rank → Ωˣ) :
    ∃ b' : Fin TwistTag.D4.tag.rank → Ωˣ,
      threeSixFrob Ω Fr ε (rootDiagUnit TwistTag.D4.tag b) = rootDiagUnit TwistTag.D4.tag b' ∧
        ∀ ν, rootChar b' (threeSixW ε *ᵥ ν) = rootChar b ν ^ q :=
  ⟨trialityPsi^[threeSixExp ε] (b ^ q), threeSixFrob_rootDiagUnit Fr hFr ε b, fun ν =>
    (rootChar_trialityPsi_iterate (threeSixExp ε) (b ^ q) ν).trans
      (CFSG.RankThree.Chevalley.rootChar_pow_tuple b q ν)⟩

theorem detVec_algebra_pos {G : Type*} [CommGroup G] {X Y : G} (j : ℕ)
    (hE : X⁻¹ * ((X * Y)⁻¹) ^ (3 * j + 1) = 1) (hF : Y⁻¹ * X ^ (3 * j + 1) = 1) :
    (X * Y ^ 2) ^ (3 * j ^ 2 + 3 * j + 1) = 1 := by
  apply Additive.ofMul.injective
  have e1 := congrArg Additive.ofMul hE
  have e2 := congrArg Additive.ofMul hF
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e1 e2 ⊢
  rw [← natCast_zsmul] at e1 e2 ⊢
  rw [← natCast_zsmul]
  push_cast at e1 e2 ⊢
  linear_combination (norm := module) (-(2 * (j : ℤ) + 1)) • e1 - ((j : ℤ) + 1) • e2

theorem detVec_algebra_neg {G : Type*} [CommGroup G] {X Y : G} (j : ℕ)
    (hE : X⁻¹ * (X * Y) ^ (3 * j + 2) = 1) (hF : Y⁻¹ * X⁻¹ ^ (3 * j + 2) = 1) :
    (X * Y ^ 2) ^ (3 * j ^ 2 + 3 * j + 1) = 1 := by
  apply Additive.ofMul.injective
  have e1 := congrArg Additive.ofMul hE
  have e2 := congrArg Additive.ofMul hF
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e1 e2 ⊢
  rw [← natCast_zsmul] at e1 e2 ⊢
  rw [← natCast_zsmul]
  push_cast at e1 e2 ⊢
  linear_combination (norm := module) (2 * (j : ℤ) + 1) • e1 + (j : ℤ) • e2

theorem rootChar_detVec_pow_eq_one (Fr : Ω →+* Ω) {q j : ℕ} (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ}
    (hqj : (ε = 1 ∧ q = 3 * j + 1) ∨ (ε = -1 ∧ q = 3 * j + 2))
    (b : Fin TwistTag.D4.tag.rank → Ωˣ)
    (hs : (rootDiagUnit TwistTag.D4.tag b)⁻¹ *
      threeSixFrob Ω Fr ε (rootDiagUnit TwistTag.D4.tag b) ∈ d4A2Tv Ω vT) :
    rootChar b (latE + 2 • latF) ^ (3 * j ^ 2 + 3 * j + 1) = 1 := by
  obtain ⟨b', hb', hb'χ⟩ := rootChar_threeSixFrob_rootDiagUnit Fr hFr ε b
  have hs' : rootDiagUnit TwistTag.D4.tag (b⁻¹ * b') ∈ d4A2Tv Ω vT := by
    rw [rootDiagUnit_mul, ← rootDiagUnit_inv]
    exact hb' ▸ hs
  obtain ⟨hE, hF⟩ := rootChar_latE_latF_of_mem hs'
  rw [rootChar_mul_tuple, rootChar_inv_tuple'] at hE hF
  obtain ⟨w1, w2, w3, w4⟩ := threeSixW_latE_latF
  have hΛ : rootChar b (latE + 2 • latF) = rootChar b latE * rootChar b latF ^ 2 := by
    rw [rootChar_add, two_nsmul, rootChar_add, sq]
  rw [hΛ]
  rcases hqj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have he : rootChar b' latE = rootChar b (-(latE + latF)) ^ (3 * j + 1) :=
      (congrArg (rootChar b') w1).symm.trans (hb'χ _)
    have hf : rootChar b' latF = rootChar b latE ^ (3 * j + 1) :=
      (congrArg (rootChar b') w2).symm.trans (hb'χ _)
    rw [rootChar_neg', rootChar_add] at he
    rw [he] at hE
    rw [hf] at hF
    exact detVec_algebra_pos j hE hF
  · have he : rootChar b' latE = rootChar b (latE + latF) ^ (3 * j + 2) :=
      (congrArg (rootChar b') w3).symm.trans (hb'χ _)
    have hf : rootChar b' latF = rootChar b (-latE) ^ (3 * j + 2) :=
      (congrArg (rootChar b') w4).symm.trans (hb'χ _)
    rw [rootChar_add] at he
    rw [rootChar_neg'] at hf
    rw [he] at hE
    rw [hf] at hF
    exact detVec_algebra_neg j hE hF

theorem pow_three_eq_one_of_pow {G : Type*} [Group G] {x : G} {j k : ℕ}
    (hxk : x ^ 3 ^ k = 1) (hxm : x ^ (3 * (3 * j ^ 2 + 3 * j + 1)) = 1) : x ^ 3 = 1 := by
  obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hxk)
  have hdm := orderOf_dvd_of_pow_eq_one hxm
  rw [hix] at hdm
  have hi1 : i ≤ 1 := by
    by_contra hi2
    have h9 : 3 ^ 2 ∣ 3 * (3 * j ^ 2 + 3 * j + 1) :=
      (Nat.pow_dvd_pow 3 (by omega)).trans hdm
    obtain ⟨t, ht⟩ := h9
    have : 3 * (3 * j ^ 2 + 3 * j + 1) = 9 * (j ^ 2 + j) + 3 := by ring
    omega
  rw [← orderOf_dvd_iff_pow_eq_one, hix]
  exact Nat.pow_dvd_pow_iff_le_right'.2 hi1 |>.trans (by rw [pow_one])

theorem zpow_eps_mul_eq_self {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) {q j : ℕ} {ε : ℤ}
    (hqj : (ε = 1 ∧ q = 3 * j + 1) ∨ (ε = -1 ∧ q = 3 * j + 2)) : x ^ (ε * (q : ℤ)) = x := by
  rcases hqj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [one_mul, zpow_natCast, pow_succ, pow_mul, hx, one_pow, one_mul]
  · rw [neg_one_mul, zpow_neg, zpow_natCast, pow_add, pow_mul, hx, one_pow, one_mul,
      inv_eq_iff_mul_eq_one, ← pow_succ, hx]

theorem rootDiagUnit_mem_zpowers_of_fixed [IsAlgClosed Ω] (Fr : Ω →+* Ω) {q j : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ}
    (hqj : (ε = 1 ∧ q = 3 * j + 1) ∨ (ε = -1 ∧ q = 3 * j + 2)) {ζ : Ωˣ} (hζ : orderOf ζ = 3)
    {c : Fin TwistTag.D4.tag.rank → Ωˣ} (hc1 : c 1 = 1) (hc2 : c 2 = 1)
    (hF : threeSixFrob Ω Fr ε (rootDiagUnit TwistTag.D4.tag c) = rootDiagUnit TwistTag.D4.tag c)
    (h3 : ∃ k : ℕ, rootDiagUnit TwistTag.D4.tag c ^ 3 ^ k = 1) :
    rootDiagUnit TwistTag.D4.tag c ∈
      Subgroup.zpowers (rootDiagUnit TwistTag.D4.tag (tup ζ gT)) := by
  have hε : ε = 1 ∨ ε = -1 := by
    rcases hqj with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hmem : rootDiagUnit TwistTag.D4.tag c ∈ threeSixTorus Ω Fr ε :=
    Subgroup.mem_inf.2 ⟨rootDiagUnit_mem_torusGroup c, hF⟩
  obtain ⟨hcT, hc0d, -⟩ := (rootDiagUnit_mem_threeSixTorus_iff' Fr hFr hε c).1 hmem
  obtain ⟨-, -, -, t3⟩ := threeSixTuple_values (L := Ω) q ε (c 0) (c 1)
  have hc3 : c 3 = c 0 ^ (ε * (q : ℤ)) := by
    have h := congrFun hcT 3
    rw [h, t3, hc1, one_zpow, mul_one]
  obtain ⟨k, hk⟩ := h3
  have hck : c ^ 3 ^ k = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := Ω)
    rw [← rootDiagUnit_pow, hk, rootDiagUnit_one]
  have hc0k : c 0 ^ 3 ^ k = 1 := by
    have := congrFun hck 0
    rwa [Pi.pow_apply, Pi.one_apply] at this
  have hc0m : c 0 ^ (3 * (3 * j ^ 2 + 3 * j + 1)) = 1 := by
    rw [← hc0d]
    rw [← zpow_natCast]
    congr 1
    rcases hqj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> push_cast <;> ring
  have hc03 : c 0 ^ 3 = 1 := pow_three_eq_one_of_pow hc0k hc0m
  rw [zpow_eps_mul_eq_self hc03 hqj] at hc3
  have hprim : IsPrimitiveRoot (ζ : Ω) 3 := by
    have h := IsPrimitiveRoot.orderOf ζ
    rw [hζ] at h
    exact IsPrimitiveRoot.coe_units_iff.2 h
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (c 0 : Ω)) (by
    rw [← Units.val_pow_eq_pow_val, hc03, Units.val_one])
  have hc0 : c 0 = ζ ^ i := Units.ext (by rw [Units.val_pow_eq_pow_val, hi])
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  have hct : c = tup ζ gT ^ i := by
    refine (fin_D4_eq_iff _ _).2 ⟨?_, ?_, ?_, ?_⟩
    · simp [tup, gT, hv1, hc0]
    · simp [tup, gT, hc1]
    · simp [tup, gT, hc2]
    · simp [tup, gT, hv1, hc3, hc0]
  rw [hct, ← rootDiagUnit_pow]
  exact Subgroup.npow_mem_zpowers _ i

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
