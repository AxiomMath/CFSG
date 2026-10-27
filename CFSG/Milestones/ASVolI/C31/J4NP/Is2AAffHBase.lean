module

public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AAffNative
public import CFSG.Milestones.ASVolI.C31.J4NP.Aff
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open Matrix
open scoped Pointwise

@[expose] def burnsideJ4NP_HasFix (M : Matrix (Fin 12) (Fin 12) (ZMod 2)) : Prop :=
  ∃ p : Fin 12 → ZMod 2, p 0 = 1 ∧ p ᵥ* M = p

theorem burnsideJ4NP_fixesPt_spec {a : Code} {v : ℕ} (h : burnsideJ4NP_fixesPt a v = true) :
    burnsideJ4NP_HasFix (burnsideJ4NP_codeMat a) := by
  unfold burnsideJ4NP_fixesPt at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hodd, -⟩, hfix⟩ := h
  refine ⟨toVecD 12 v, ?_, ?_⟩
  · rw [toVecD_apply]
    simp [Nat.testBit_zero, hodd]
  · rw [burnsideJ4NP_codeMat, ← toVecD_vecMulN, hfix]

theorem burnsideJ4NP_toVecD_colMinus (a : Code) (z : ℕ) :
    toVecD 12 (burnsideJ4NP_colMinus a z) = (burnsideJ4NP_codeMat a - 1) *ᵥ toVecD 12 z := by
  rw [burnsideJ4NP_colMinus, toVecD_xor, burnsideJ4NP_codeMat, ← rowsMatrix_mulVec, sub_mulVec,
    one_mulVec]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply]
  generalize (rowsMatrix 12 a.rows *ᵥ toVecD 12 z) j = x
  generalize toVecD 12 z j = y
  revert x y
  decide

theorem burnsideJ4NP_toVecD_one : toVecD 12 1 = Pi.single 0 1 := by
  funext j
  revert j
  decide

theorem burnsideJ4NP_sepOK_spec {a : Code} {z : ℕ} (h : burnsideJ4NP_sepOK a z = true) :
    ¬ burnsideJ4NP_HasFix (burnsideJ4NP_codeMat a) := by
  rintro ⟨p, hp0, hp⟩
  unfold burnsideJ4NP_sepOK at h
  rw [beq_iff_eq] at h
  have h1 := burnsideJ4NP_toVecD_colMinus a z
  rw [h, burnsideJ4NP_toVecD_one] at h1
  have h2 : p ⬝ᵥ ((burnsideJ4NP_codeMat a - 1) *ᵥ toVecD 12 z) = 0 := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_sub, hp, Matrix.vecMul_one, sub_self,
      zero_dotProduct]
  rw [← h1, dotProduct_single, hp0, mul_one] at h2
  exact one_ne_zero h2

theorem burnsideJ4NP_zmod2_ite (b : ZMod 2) :
    (if decide (b = 1) = true then (1 : ZMod 2) else 0) = b := by
  revert b
  decide

theorem burnsideJ4NP_bruteFix_iff {a : Code} (ha : burnsideJ4NP_CodeWF a) :
    burnsideJ4NP_bruteFix a = true ↔ burnsideJ4NP_HasFix (burnsideJ4NP_codeMat a) := by
  constructor
  · intro h
    unfold burnsideJ4NP_bruteFix at h
    obtain ⟨w, -, hw⟩ := List.any_eq_true.1 h
    exact burnsideJ4NP_fixesPt_spec hw
  · rintro ⟨p, hp0, hp⟩
    set f : ℕ → Bool := fun j => if hj : j < 12 then decide (p ⟨j, hj⟩ = 1) else false with hf
    have hvlt : ofBits 12 f < 2 ^ 12 := ofBits_lt 12 f
    have hvp : toVecD 12 (ofBits 12 f) = p := by
      funext j
      rw [toVecD_ofBits, hf]
      simp only [j.isLt, dif_pos]
      exact burnsideJ4NP_zmod2_ite (p j)
    have hodd : ofBits 12 f % 2 = 1 := by
      have h0 := ofBits_testBit 12 f 0
      rw [Nat.testBit_zero] at h0
      have hf0 : f 0 = true := by
        rw [hf]
        simp [hp0]
      rw [hf0] at h0
      simpa using h0
    have hfix : vecMulN 12 a.rows (ofBits 12 f) = ofBits 12 f := by
      apply toVecD_injective (burnsideJ4NP_vecMulN_lt ha.2 _) hvlt
      rw [toVecD_vecMulN, hvp]
      exact hp
    unfold burnsideJ4NP_bruteFix
    refine List.any_eq_true.2 ⟨ofBits 12 f / 2, List.mem_range.2 (by omega), ?_⟩
    rw [show 2 * (ofBits 12 f / 2) + 1 = ofBits 12 f by omega]
    unfold burnsideJ4NP_fixesPt
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hodd, by omega⟩, hfix⟩

theorem burnsideJ4NP_hasFix_iff {a : Code} (ha : burnsideJ4NP_CodeWF a) :
    burnsideJ4NP_hasFix a = true ↔ burnsideJ4NP_HasFix (burnsideJ4NP_codeMat a) := by
  unfold burnsideJ4NP_hasFix
  split_ifs with h1 h2
  · exact ⟨fun _ => burnsideJ4NP_fixesPt_spec h1, fun _ => rfl⟩
  · exact ⟨fun h => by simp at h, fun h => absurd h (burnsideJ4NP_sepOK_spec h2)⟩
  · exact burnsideJ4NP_bruteFix_iff ha

theorem burnsideJ4NP_HasFix_conj
    {g x : J} (hg : g ∈ Hj) (hx : x ∈ Hj) :
    burnsideJ4NP_HasFix (burnsideJ4NP_rho (g⁻¹ * x * g)) ↔
      burnsideJ4NP_HasFix (burnsideJ4NP_rho x) := by
  have hρ : burnsideJ4NP_rho (g⁻¹ * x * g) =
      burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho x * burnsideJ4NP_rho g := by
    rw [burnsideJ4NP_rho_mul hg, burnsideJ4NP_rho_mul hx]
  have hgi : burnsideJ4NP_rho g * burnsideJ4NP_rho g⁻¹ = 1 := burnsideJ4NP_rho_mul_inv hg
  have hcol : ∀ {h : J}, h ∈ Hj → ∀ q : Fin 12 → ZMod 2, (q ᵥ* burnsideJ4NP_rho h) 0 = q 0 := by
    intro h hh q
    simp [Matrix.vecMul, dotProduct, burnsideJ4NP_rho_col0 hh]
  rw [hρ]
  constructor
  · rintro ⟨q, hq0, hq⟩
    refine ⟨q ᵥ* burnsideJ4NP_rho g⁻¹, by rw [hcol (Hj.inv_mem hg), hq0], ?_⟩
    calc q ᵥ* burnsideJ4NP_rho g⁻¹ ᵥ* burnsideJ4NP_rho x
        = q ᵥ* (burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho x) := Matrix.vecMul_vecMul _ _ _
      _ = q ᵥ* (burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho x * burnsideJ4NP_rho g *
            burnsideJ4NP_rho g⁻¹) := by
          rw [mul_assoc (burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho x), hgi, mul_one]
      _ = q ᵥ* (burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho x * burnsideJ4NP_rho g) ᵥ*
            burnsideJ4NP_rho g⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
      _ = q ᵥ* burnsideJ4NP_rho g⁻¹ := by rw [hq]
  · rintro ⟨p, hp0, hp⟩
    refine ⟨p ᵥ* burnsideJ4NP_rho g, by rw [hcol hg, hp0], ?_⟩
    calc p ᵥ* burnsideJ4NP_rho g ᵥ*
          (burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho x * burnsideJ4NP_rho g)
        = p ᵥ* (burnsideJ4NP_rho g *
            (burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho x * burnsideJ4NP_rho g)) :=
          Matrix.vecMul_vecMul _ _ _
      _ = p ᵥ* (burnsideJ4NP_rho x * burnsideJ4NP_rho g) := by
          rw [← mul_assoc, ← mul_assoc, hgi, one_mul]
      _ = p ᵥ* burnsideJ4NP_rho x ᵥ* burnsideJ4NP_rho g := (Matrix.vecMul_vecMul _ _ _).symm
      _ = p ᵥ* burnsideJ4NP_rho g := by rw [hp]

theorem burnsideJ4NP_exists_conj_mem_P0
    {x : J} (hx : x ∈ Hj)
    (hsq : x * x = 1) : ∃ g ∈ Hj, g⁻¹ * x * g ∈ P0 := by
  have hF := j4Facts
  have hM := hF.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPcard : Nat.card ↥(P0.subgroupOf Hj) = 2 ^ 21 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P0_le_Hj).toEquiv, card_P0 hM hF]
  have hfac : (Nat.card ↥Hj).factorization 2 = 21 := by
    rw [card_Hj hF]
    have h : (501397585920 : ℕ) = 2 ^ 21 * 239085 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let S : Sylow 2 ↥Hj := Sylow.ofCard (P0.subgroupOf Hj) (by rw [hPcard, hfac])
  set x' : ↥Hj := ⟨x, hx⟩ with hx'
  have hx2 : x' ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, pow_two, OneMemClass.coe_one]
    exact hsq
  have hX : IsPGroup 2 ↥(Subgroup.zpowers x') := by
    have hord : orderOf x' ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hc : Nat.card (Subgroup.zpowers x') = orderOf x' := Nat.card_zpowers x'
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hc, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [hc, h]; rfl)
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Hj S Q
  have hQ' : (Q : Subgroup ↥Hj) = MulAut.conj g • P0.subgroupOf Hj := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  have hxQ : x' ∈ MulAut.conj g • P0.subgroupOf Hj := by
    rw [← hQ']
    exact hQ (Subgroup.mem_zpowers x')
  obtain ⟨s, hs, hsx⟩ := (Subgroup.mem_smul_pointwise_iff_exists x' (MulAut.conj g) _).1 hxQ
  refine ⟨(g : J), g.2, ?_⟩
  have h1 : (g : J)⁻¹ * x * g = (s : J) := by
    have h2 : g * s * g⁻¹ = x' := by
      rw [← hsx, MulAut.smul_def, MulAut.conj_apply]
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hx'] at h3
    rw [← h3]
    group
  rw [h1]
  exact Subgroup.mem_subgroupOf.1 hs

theorem burnsideJ4NP_affine2A_iff_hasFix
    {x : J} (hx : x ∈ Hj)
    (hxE : x ∉ Eg uJ 11) :
    burnsideJ4NP_affine2A (burnsideJ4NP_enc ⟨x, hx⟩) = true ↔
      burnsideJ4NP_HasFix (burnsideJ4NP_rho x) := by
  have hin : (burnsideJ4NP_enc ⟨x, hx⟩).inE = false := by
    cases h : (burnsideJ4NP_enc ⟨x, hx⟩).inE
    · rfl
    · exact absurd ((burnsideJ4NP_mem_Eg_iff hx).2 h) hxE
  rw [burnsideJ4NP_affine2A, burnsideJ4NP_affine2AWith, hin, if_neg Bool.false_ne_true,
    burnsideJ4NP_hasFix_iff (burnsideJ4NP_codeWF_enc _), burnsideJ4NP_codeMat_enc]

end CFSG.ASVolI
