module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofStatements
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines

public section

namespace CFSG.RankThree.PartTwo.Sec21.U4Lines

open Matrix CFSG CFSG.RankThree
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor permGL_mem_SU exists_conj_into_d8Tor_su d8Comb_four)

@[expose] def CentralizerLineType {F : Type} [Field F] (Y : Subgroup (GL (Fin 4) F))
    (ℓ : Subgroup (GL (Fin 4) F)) (b : ℕ) : Prop :=
  Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ : Set (GL (Fin 4) F))) ≃*
      projSL 2 (GaloisField 2 b)) ∨
    Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ : Set (GL (Fin 4) F))) ≃*
      projSL 2 (GaloisField 2 (2 * b)))

theorem lines_perfectResidual {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ} (hb : 0 < b)
    (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) {ℓ : Subgroup (GL (Fin 4) F)}
    (hℓ : ℓ ≤ d8Tor 3 F 4) (h3 : Nat.card ℓ = 3) :
    CentralizerLineType (SU (unitaryInvolution F 2 b) 4) ℓ b := by
  set σ : F ≃+* F := unitaryInvolution F 2 b with hσdef
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have hμ := card_rootsOfUnity_three hbe hF
  have : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 F)
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have hinv1 : (1 : F) ≠ a⁻¹ := fun h => ha1 (by rw [← inv_inv a, ← h, inv_one])
  have hw₁ : weyl₁ ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  have hw₂ : weyl₂ ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  have ht₁ : ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, 1, 1, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  have ht₃ : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  obtain ⟨eL⟩ := nonempty_longSL_mulEquiv (F := F) hb hF
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois σ hb hF
  have hperfL : ⁅longSL σ, longSL σ⁆ = longSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL hb2 eL)
  have hperfS : ⁅shortSL σ, shortSL σ⁆ = shortSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL (by omega) eS)
  have hS₁ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F))) = longSL σ :=
    perfectResidual_long σ ht₁ ha1 hainv hinv1 hperfL
  have hS₃ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) = shortSL σ :=
    perfectResidual_short σ hσσ ht₃ hainv hperfS
  have hL₂ : Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))).map (MulAut.conj weyl₁).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₁ ((ω, 1) : D8Mod 3 F)).symm
  have hL₄ : Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map (MulAut.conj weyl₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₂ ((ω, ω) : D8Mod 3 F)).symm
  rcases line_cases hμ hω hℓ h3 with rfl | rfl | rfl | rfl
  · left
    rw [hS₁]
    exact ⟨eL⟩
  · left
    rw [hL₂, perfectResidual_conj hw₁, hS₁]
    exact ⟨((longSL σ).equivMapOfInjective _ (MulAut.conj weyl₁).injective).symm.trans eL⟩
  · right
    rw [hS₃]
    exact ⟨eS⟩
  · right
    rw [hL₄, perfectResidual_conj hw₂, hS₃]
    exact ⟨((shortSL σ).equivMapOfInjective _ (MulAut.conj weyl₂).injective).symm.trans eS⟩

theorem centralizerLineType_SU {b : ℕ} (hb : 0 < b) (hbe : Even b)
    {ℓ : Subgroup (GL (Fin 4) (GaloisField 2 (2 * b)))}
    (hℓ : ℓ ≤ SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4) (h3 : Nat.card ℓ = 3) :
    CentralizerLineType (SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4) ℓ b := by
  have hF := card_galoisField_two_mul b hb
  set Y := SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4 with hY
  have hX : ∀ x ∈ ℓ.subgroupOf Y, x ^ 3 = 1 := by
    intro x hx
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := pow_card_eq_one' (G := ℓ) (x := ⟨(x : GL (Fin 4) _), hx⟩)
    rw [h3] at h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four hF
    Nat.prime_three (by norm_num) (three_dvd_two_pow_sub_one hbe) _ hX
  have hT : mapL (MulAut.conj g) ℓ ≤ d8Tor 3 (GaloisField 2 (2 * b)) 4 := by
    rw [mapL_conj g hℓ]
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hℓ hx⟩ hx
  have h3' : Nat.card (mapL (MulAut.conj g) ℓ) = 3 := by rw [card_mapL _ hℓ, h3]
  exact (lines_perfectResidual hb hbe hF hT h3').imp
    (Nonempty.map fun e => (perfectResidualEquiv (MulAut.conj g) hℓ).trans e)
    (Nonempty.map fun e => (perfectResidualEquiv (MulAut.conj g) hℓ).trans e)

end CFSG.RankThree.PartTwo.Sec21.U4Lines

namespace CFSG.RankThree.PartTwo.Sec21

open U4Lines

theorem ks222U4Even : KS222U4Even := by
  intro G _ _ L ℓ n hn he ⟨eL⟩ hℓL hℓ3
  obtain ⟨e₀⟩ := nonempty_projSU_mulEquiv_SU n hn
  have h3 : Nat.card (mapL (eL.trans e₀) ℓ) = 3 := by rw [card_mapL _ hℓL, hℓ3]
  exact (centralizerLineType_SU hn he (mapL_le (eL.trans e₀) ℓ) h3).imp
    (Nonempty.map fun e => (perfectResidualEquiv (eL.trans e₀) hℓL).trans e)
    (Nonempty.map fun e => (perfectResidualEquiv (eL.trans e₀) hℓL).trans e)

end CFSG.RankThree.PartTwo.Sec21
