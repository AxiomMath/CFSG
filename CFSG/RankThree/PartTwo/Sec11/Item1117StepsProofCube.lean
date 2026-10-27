module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements


@[expose] def KFact1117CubeG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a c d : G) (Y K : Subgroup G) (g y : G),
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 → A = Subgroup.closure {c, a, d} →
    Y ∈ thetaComponentsAt 3 a → A ≤ Subgroup.normalizer (Y : Set G) →
    Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers a : Set G) →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    ((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
          (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
      ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) →
    Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6) →
    y ∈ K → (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 → d ∈ Subgroup.zpowers y →
    g ∈ Y ⊓ Subgroup.normalizer (A : Set G) → (∃ k : ℕ, g ^ 3 ^ k = 1) →
    g * y * g⁻¹ ∈ Subgroup.zpowers y →
    g * c * g⁻¹ * c⁻¹ ∈ Subgroup.zpowers d → g * c * g⁻¹ ≠ c → False

@[expose] def KFact1117CubeL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a c d : G) (Y K : Subgroup G) (g y : G),
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 → A = Subgroup.closure {c, a, d} →
    Y ∈ thetaComponentsAt 3 a → A ≤ Subgroup.normalizer (Y : Set G) →
    Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers a : Set G) →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    (Sec8.IsZ3LThreePi (sec11YA a Y A) ∨ Sec8.IsZ3PGLThreePi (sec11YA a Y A)) →
    Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3)) →
    y ∈ K → (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 → d ∈ Subgroup.zpowers y →
    g ∈ Y ⊓ Subgroup.normalizer (A : Set G) → (∃ k : ℕ, g ^ 3 ^ k = 1) →
    g * y * g⁻¹ ∈ Subgroup.zpowers y →
    g * c * g⁻¹ * c⁻¹ ∈ Subgroup.zpowers d → g * c * g⁻¹ ≠ c → False

end Statements

section Main


theorem kFact1117Cube_of (h45 : Sec4.Item4_5) (h117 : Item117) (h118 : Item118)
    (hG2 : KFact1117CubeG2) (hL3 : KFact1117CubeL3) : KFact1117Cube := by
  intro G _ _ A c L a R Y d x s r g h _ _ hcase hx9 hgx
  have hAe := h.mem_partTwoF.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hsec := (h118 G A c L a R Y h.toSec11Std d g h.inf_eq h.closure_eq h.g_mem.2 h.g_not_mem
    h.conj_mem).2.2
  have hK := mem_thetaComponentsIn_sec11K_inf h.toSec11Std
  have hT := kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq
  have hyK := Item1117Proof.x_cube_mem_sec11K h
  obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
  have hy3k : (x ^ 3) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
  have hy3 : (x ^ 3) ^ 3 ≠ 1 := by
    intro h1
    rw [← pow_mul] at h1
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
    omega
  have hdy := Item1117Proof.d_mem_zpowers_x_cube h
  have hgc := Item1117Proof.conj_g_c_mem h117 h
  have hgc' : g * c * g⁻¹ ≠ c := by
    intro he
    apply h.g_not_mem
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [he]
    exact Subgroup.mem_zpowers c
  rcases hcase with ⟨h2, hD⟩ | ⟨h3, hS⟩
  · exact hG2 G A a c d Y (sec11K L a) g (x ^ 3) hAe h.card_eq h.closure_eq
      h.mem_thetaComponentsAt_Y hAY hsec hK hT h2 hD hyK ⟨k, hy3k⟩ hy3 hdy h.g_mem h.pow_eq_one
      hgx hgc hgc'
  · exact hL3 G A a c d Y (sec11K L a) g (x ^ 3) hAe h.card_eq h.closure_eq
      h.mem_thetaComponentsAt_Y hAY hsec hK hT h3 hS hyK ⟨k, hy3k⟩ hy3 hdy h.g_mem h.pow_eq_one
      hgx hgc hgc'

end Main

end CFSG.RankThree.PartTwo.Sec11
