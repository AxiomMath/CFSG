module

public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.RankThree.Classical

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

@[expose] def siegelElt {H : Matrix (Fin r) (Fin r) K} (hH : Hᵀ = H) : StatedSp r K :=
  ⟨siegelGL H, siegelGL_mem_statedSp hH⟩

theorem coe_siegelElt {H : Matrix (Fin r) (Fin r) K} (hH : Hᵀ = H) :
    (((siegelElt hH : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = fromBlocks 1 H 0 1 :=
  rfl

theorem siegelElt_mem {H : Matrix (Fin r) (Fin r) K} (hH : Hᵀ = H) :
    siegelElt hH ∈ siegelRadicalSp r K :=
  ⟨Multiplicative.ofAdd ⟨H, hH⟩, rfl⟩

theorem pow_char_eq_one_of_mem_siegelRadicalSp {p : ℕ} [CharP K p] {w : StatedSp r K}
    (hw : w ∈ siegelRadicalSp r K) : w ^ p = 1 := by
  obtain ⟨v, rfl⟩ := hw
  have h : v ^ p = 1 := by
    change Multiplicative.ofAdd (p • v.toAdd) = 1
    rw [nsmul_char_eq_zero]
    rfl
  rw [← map_pow, h, map_one]

theorem siegelElt_pow_char {p : ℕ} [CharP K p] {H : Matrix (Fin r) (Fin r) K} (hH : Hᵀ = H) :
    siegelElt hH ^ p = 1 :=
  pow_char_eq_one_of_mem_siegelRadicalSp (siegelElt_mem hH)

theorem toBlocks₂₁_eq_zero_of_commute_siegelMat {D : Matrix (Fin r) (Fin r) K} (hD : IsUnit D)
    {G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h : G * fromBlocks 1 D 0 1 = fromBlocks 1 D 0 1 * G) : G.toBlocks₂₁ = 0 := by
  set P := G.toBlocks₁₁
  set Q := G.toBlocks₁₂
  set R := G.toBlocks₂₁
  set W := G.toBlocks₂₂
  have hG : G = fromBlocks P Q R W := (fromBlocks_toBlocks G).symm
  rw [hG, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    zero_add] at h
  exact hD.mul_left_cancel ((left_eq_add.mp (fromBlocks_inj.mp h).1).trans
    (Matrix.mul_zero D).symm)

theorem conj_mem_siegelRadicalSp_of_toBlocks₂₁_eq_zero {g : StatedSp r K}
    (hg : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₂₁ = 0)
    {w : StatedSp r K} (hw : w ∈ siegelRadicalSp r K) : g * w * g⁻¹ ∈ siegelRadicalSp r K := by
  obtain ⟨H, hH, hwH⟩ := mem_siegelRadicalSp.mp hw
  have hsp := SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  set G := ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hGdef
  set P := G.toBlocks₁₁
  set Q := G.toBlocks₁₂
  set E := G.toBlocks₂₂
  have hG : G = fromBlocks P Q 0 E := by
    rw [← hg]
    exact (fromBlocks_toBlocks G).symm
  rw [hG, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hsp
  simp only [transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero] at hsp
  have hPE : Pᵀ * E = 1 := (fromBlocks_inj.mp hsp).2.1
  have hH' : (P * H * Pᵀ)ᵀ = P * H * Pᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hH, Matrix.mul_assoc]
  have hmul : g * w = siegelElt hH' * g := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hwH, coe_siegelElt,
      ← hGdef, hG, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
      zero_add]
    rw [Matrix.mul_assoc (P * H) Pᵀ E, hPE, Matrix.mul_one, add_comm]
  rw [hmul, mul_inv_cancel_right]
  exact siegelElt_mem hH'

theorem conj_mem_siegelRadicalSp_of_proj_commute [Finite K] (hr : 1 ≤ r) {p : ℕ} [CharP K p]
    {D : Matrix (Fin r) (Fin r) K} (hDs : Dᵀ = D) (hD : IsUnit D) {g : StatedSp r K}
    (hg : proj r K g * proj r K (siegelElt hDs) = proj r K (siegelElt hDs) * proj r K g)
    {w : StatedSp r K} (hw : w ∈ siegelRadicalSp r K) : g * w * g⁻¹ ∈ siegelRadicalSp r K := by
  have hex : g * siegelElt hDs * g⁻¹ = siegelElt hDs :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_proj_eq_of_pow_eq_one hr p
      (a := 1) (b := 1)
      (by rw [pow_one, conj_pow, siegelElt_pow_char, mul_one, mul_inv_cancel])
      (by rw [pow_one, siegelElt_pow_char hDs])
      (by rw [map_mul, map_mul, map_inv, hg, mul_inv_cancel_right])
  have hcomm : g * siegelElt hDs = siegelElt hDs * g :=
    calc g * siegelElt hDs = g * siegelElt hDs * g⁻¹ * g := by group
      _ = siegelElt hDs * g := by rw [hex]
  have hmat := congrArg (fun y : StatedSp r K =>
    ((y : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hcomm
  simp only [Subgroup.coe_mul, Units.val_mul, coe_siegelElt] at hmat
  exact conj_mem_siegelRadicalSp_of_toBlocks₂₁_eq_zero
    (toBlocks₂₁_eq_zero_of_commute_siegelMat hD hmat) hw

theorem eq_fromBlocks_of_mul_siegel_comm {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (σ : K ≃+* K) (i₀ : Fin r)
    (h : ∀ H : Matrix (Fin r) (Fin r) K, Hᵀ = H →
      M * fromBlocks 1 (H.map σ) 0 1 = fromBlocks 1 H 0 1 * M) :
    M = fromBlocks (M.toBlocks₁₁ i₀ i₀ • 1) M.toBlocks₁₂ 0 (M.toBlocks₁₁ i₀ i₀ • 1) ∧
      ∀ H : Matrix (Fin r) (Fin r) K, Hᵀ = H →
        M.toBlocks₁₁ i₀ i₀ • H.map σ = M.toBlocks₁₁ i₀ i₀ • H := by
  set P := M.toBlocks₁₁
  set Q := M.toBlocks₁₂
  set R := M.toBlocks₂₁
  set W := M.toBlocks₂₂
  have hM : M = fromBlocks P Q R W := (fromBlocks_toBlocks M).symm
  have key : ∀ H : Matrix (Fin r) (Fin r) K, Hᵀ = H → H * R = 0 ∧ P * H.map σ = H * W := by
    intro H hH
    have := h H hH
    rw [hM, fromBlocks_multiply, fromBlocks_multiply] at this
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
      zero_add] at this
    obtain ⟨h1, h2, -, -⟩ := fromBlocks_inj.mp this
    exact ⟨left_eq_add.mp h1, by rw [add_comm] at h2; exact add_left_cancel h2⟩
  have hR : R = 0 := by simpa using (key 1 transpose_one).1
  have hPW : P = W := by
    have := (key 1 transpose_one).2
    rwa [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one, Matrix.one_mul] at this
  have hcomm : ∀ H : Matrix (Fin r) (Fin r) K, Hᵀ = H → P * H.map σ = H * P := fun H hH => by
    rw [(key H hH).2, hPW]
  have hdiag : ∀ a i, a ≠ i → P a i = 0 := by
    intro a i hai
    have := congrFun (congrFun (hcomm (single i i 1) (transpose_single i i 1)) a) i
    rw [map_single, map_one, mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hai,
      mul_one] at this
    exact this
  have hconst : ∀ i j, P i i = P j j := by
    intro i j
    set J : Matrix (Fin r) (Fin r) K := Matrix.of fun _ _ => 1
    have hJ : Jᵀ = J := by ext; rfl
    have hJσ : J.map σ = J := by ext; simp [J]
    have := congrFun (congrFun (hcomm J hJ) i) j
    rw [hJσ, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i, Finset.sum_eq_single j]
      at this
    · simpa [J] using this
    · intro k _ hk
      rw [hdiag k j hk, mul_zero]
    · simp
    · intro k _ hk
      rw [hdiag i k (Ne.symm hk), zero_mul]
    · simp
  have hP : P = P i₀ i₀ • 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [hconst a i₀]
    · simp [hdiag a b hab, hab]
  refine ⟨?_, fun H hH => ?_⟩
  · rw [hM, hR, ← hPW, ← hP]
  · have := hcomm H hH
    rw [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one] at this
    exact this

theorem mul_self_eq_and_smul_transpose_of_similitude {c μ : K} {Q : Matrix (Fin r) (Fin r) K}
    (i₀ : Fin r)
    (h : (fromBlocks (c • 1) Q 0 (c • 1))ᵀ * fromBlocks 0 1 (-1) 0 *
        fromBlocks (c • 1) Q 0 (c • 1) =
      μ • (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    c * c = μ ∧ c • Qᵀ = c • Q := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul] at h
  simp only [transpose_smul, transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, smul_zero,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_neg, smul_smul] at h
  obtain ⟨-, h2, -, h4⟩ := fromBlocks_inj.mp h
  refine ⟨?_, ?_⟩
  · have := congrFun (congrFun h2 i₀) i₀
    simpa using this
  · rw [neg_add_eq_zero] at h4
    exact h4.symm

theorem exists_eq_conj_of_forall_fix_projSiegel [Finite K] {p : ℕ} (hp2 : p ≠ 2) [CharP K p]
    (hr : 2 ≤ r) (α : MulAut (StatedProj (StatedSp r K)))
    (hα : ∀ z ∈ (siegelRadicalSp r K).map (proj r K), α z = z) :
    ∃ z ∈ (siegelRadicalSp r K).map (proj r K), α = MulAut.conj z := by
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  obtain ⟨A, σ, rfl⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard hodd hr α
  have hcomm : ∀ H : Matrix (Fin r) (Fin r) K, Hᵀ = H →
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          fromBlocks 1 (H.map σ) 0 1 =
        fromBlocks 1 H 0 1 * ((A : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    intro H hH
    have hfix := hα _ ⟨siegelElt hH, siegelElt_mem hH, rfl⟩
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at hfix
    have hpow : (conjSp r K A (fieldSp r K σ (siegelElt hH))) ^ p = 1 := by
      rw [← map_pow, ← map_pow, siegelElt_pow_char, map_one, map_one]
    have heq := CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_proj_eq_of_pow_eq_one
      (by omega) p (a := 1) (b := 1) (by rwa [pow_one]) (by rw [pow_one, siegelElt_pow_char hH])
      hfix
    have hGL : (A : GL (Fin r ⊕ Fin r) K) *
        (fieldSp r K σ (siegelElt hH) : GL (Fin r ⊕ Fin r) K) =
        (siegelElt hH : GL (Fin r ⊕ Fin r) K) * A := by
      rw [← congrArg Subtype.val heq, coe_conjSp, inv_mul_cancel_right]
    have := congrArg Units.val hGL
    rwa [Units.val_mul, Units.val_mul, coe_fieldSp, coe_siegelElt, fromBlocks_map,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.map_zero _ (map_zero σ)] at this
  obtain ⟨hform, hσc⟩ := eq_fromBlocks_of_mul_siegel_comm σ ⟨0, by omega⟩ hcomm
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set c := M.toBlocks₁₁ ⟨0, by omega⟩ ⟨0, by omega⟩
  set Q := M.toBlocks₁₂
  obtain ⟨μ, hμ⟩ := A.2
  rw [← hM, hform] at hμ
  obtain ⟨hcμ, hQs⟩ := mul_self_eq_and_smul_transpose_of_similitude ⟨0, by omega⟩ hμ
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcμ
    exact μ.ne_zero hcμ.symm
  have hQ' : Qᵀ = Q := smul_right_injective _ hc0 hQs
  have hσ : σ = 1 := by
    ext b
    have h1 := hσc (b • 1) (by rw [transpose_smul, transpose_one])
    have h2 := congrFun (congrFun (smul_right_injective _ hc0 h1) ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h2
  subst hσ
  rw [map_one, mul_one]
  have hQc : (c⁻¹ • Q)ᵀ = c⁻¹ • Q := by rw [transpose_smul, hQ']
  refine ⟨proj r K (siegelElt hQc), ⟨_, siegelElt_mem hQc, rfl⟩, ?_⟩
  have hAu : (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r)
      (Units.mk0 c hc0) * (siegelElt hQc : GL (Fin r ⊕ Fin r) K) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_siegelElt, Units.val_mk0,
      Matrix.scalar_apply, ← smul_eq_diagonal_mul, fromBlocks_smul, smul_smul,
      mul_inv_cancel₀ hc0, one_smul, smul_zero]
    exact hform
  have hz : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 c hc0) ∈
      Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  ext t
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective t
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hAu]
  set z := GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 c hc0)
  set u := (siegelElt hQc : GL (Fin r ⊕ Fin r) K)
  have hzc := Subgroup.mem_center_iff.mp hz (u * (g : GL (Fin r ⊕ Fin r) K) * u⁻¹)
  calc z * u * (g : GL (Fin r ⊕ Fin r) K) * (z * u)⁻¹ =
        u * (g : GL (Fin r ⊕ Fin r) K) * u⁻¹ * z * z⁻¹ := by
        rw [hzc]
        group
    _ = u * (g : GL (Fin r ⊕ Fin r) K) * u⁻¹ := by group

theorem symplectic_four_square_zero_rank_two_centralizer_normal_prime_complements_trivial
    {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hr : 2 ≤ r)
    {D : Matrix (Fin r) (Fin r) K} (hDs : Dᵀ = D) (hD : IsUnit D)
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    (S : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hSC : S ≤ B ⊓ Subgroup.centralizer {MulAut.conj (proj r K (siegelElt hDs))})
    (hSn : (S.subgroupOf
      (B ⊓ Subgroup.centralizer {MulAut.conj (proj r K (siegelElt hDs))})).Normal)
    (hSp : ¬p ∣ Nat.card S) : S = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hp.ne_zero)
  have := Fintype.ofFinite K
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (show 4 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
  have hsimple : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega)
      (Or.inl (Or.inr h4))
  have hs4 : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  have hperf : Group.IsPerfect (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r K (Or.inl hs4)
  have hZ : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (StatedProj (StatedSp r K))) with h | h
    · exact h
    · have hcomm : IsMulCommutative (StatedProj (StatedSp r K)) :=
        ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a⟩⟩
      exact absurd hcomm (Group.IsPerfect.not_isMulCommutative (StatedProj (StatedSp r K)))
  have hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) := by
    refine (injective_iff_map_eq_one _).mpr fun g hg => ?_
    have hc : g ∈ Subgroup.center (StatedProj (StatedSp r K)) :=
      Subgroup.mem_center_iff.2 fun t => by
        have ht := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ t) hg
        simp only [MulAut.conj_apply, MulAut.one_apply] at ht
        calc t * g = g * t * g⁻¹ * g := by rw [ht]
          _ = g * t := by group
    rwa [hZ, Subgroup.mem_bot] at hc
  have hconj : ∀ (s : MulAut (StatedProj (StatedSp r K))) (y : StatedProj (StatedSp r K)),
      MulAut.conj (s y) = s * MulAut.conj y * s⁻¹ := by
    intro s y
    ext t
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  set x := proj r K (siegelElt hDs) with hx
  set U := (siegelRadicalSp r K).map (proj r K) with hU
  set C := Subgroup.centralizer ({x} : Set (StatedProj (StatedSp r K))) with hC
  set P₀ := (CFSG.pCore p C).map C.subtype with hP₀
  set W := P₀.map
    (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) with hW
  set L := B ⊓ Subgroup.centralizer {MulAut.conj x} with hL
  have hUp : ∀ z ∈ U, z ^ p = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_pow, pow_char_eq_one_of_mem_siegelRadicalSp hw, map_one]
  have hUcomm : ∀ z ∈ U, ∀ z' ∈ U, z * z' = z' * z := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩ _ ⟨_, ⟨v', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm v v']
  have hUC : U ≤ C := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.2 (hUcomm z hz x ⟨_, siegelElt_mem hDs, rfl⟩)
  have hUnorm : ∀ c ∈ C, ∀ z ∈ U, c * z * c⁻¹ ∈ U := by
    intro c hc z hz
    obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective c
    obtain ⟨w, hw, rfl⟩ := hz
    have hg : proj r K g * x = x * proj r K g := Subgroup.mem_centralizer_singleton_iff.1 hc
    refine ⟨g * w * g⁻¹, conj_mem_siegelRadicalSp_of_proj_commute (by omega) hDs hD hg hw, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hUP₀ : U ≤ P₀ := by
    have hnorm : (U.subgroupOf C).Normal := ⟨fun n hn c => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hUnorm c c.2 n hn⟩
    have hpg : IsPGroup p (U.subgroupOf C) := fun z => ⟨1, by
      have h := hUp _ (Subgroup.mem_subgroupOf.mp z.2)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h⟩
    have hle : U.subgroupOf C ≤ CFSG.pCore p C := le_sSup ⟨hnorm, hpg⟩
    intro z hz
    exact ⟨⟨z, hUC hz⟩, hle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hWp : IsPGroup p W := ((CFSG.pCore_isPGroup).map C.subtype).map _
  have hfix : ∀ s ∈ L, s x = x := by
    intro s hs
    apply hinj
    rw [hconj, Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2,
      mul_inv_cancel_right]
  have hres : ∀ t : MulAut (StatedProj (StatedSp r K)), t x = x → ∀ c ∈ C, t c ∈ C := by
    intro t ht c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← ht, ← map_mul, ← map_mul, hc]
  have hP₀inv : ∀ s ∈ L, ∀ y ∈ P₀, s y ∈ P₀ := by
    intro s hs y hy
    have hs1 := hfix s hs
    have hs2 : s⁻¹ x = x := by
      change s.symm x = x
      rw [MulEquiv.symm_apply_eq, hs1]
    let φ : C ≃* C :=
      { toFun := fun c => ⟨s c, hres s hs1 c c.2⟩
        invFun := fun c => ⟨s⁻¹ c, hres s⁻¹ hs2 c c.2⟩
        left_inv := fun c => Subtype.ext (by simp)
        right_inv := fun c => Subtype.ext (by simp)
        map_mul' := fun c c' =>
          Subtype.ext (map_mul s (c : StatedProj (StatedSp r K)) c') }
    obtain ⟨c, hc, rfl⟩ := hy
    have hφc : φ c ∈ CFSG.pCore p C := by
      rw [← CFSG.pCore_map_iso p φ]
      exact Subgroup.mem_map_of_mem _ hc
    exact ⟨φ c, hφc, rfl⟩
  have hWL : W ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    have hyC : y ∈ C := by
      obtain ⟨c, -, rfl⟩ := hy
      exact c.2
    refine Subgroup.mem_inf.2 ⟨hB ⟨y, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 hyC]
  have hWnorm : ∀ s ∈ L, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    rintro s hs _ ⟨y, hy, rfl⟩
    exact ⟨s y, hP₀inv s hs y hy, hconj s y⟩
  have hSnorm : ∀ y ∈ L, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    exact Subgroup.mem_subgroupOf.1
      (hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩)
  have hdisj : Disjoint S W := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hWp
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hp).2 hSp).symm
  have hcomm : ∀ s ∈ S, ∀ w ∈ W, s * w = w * s := by
    intro s hs w hw
    have h1 : s * w * s⁻¹ * w⁻¹ ∈ W := W.mul_mem (hWnorm s (hSC hs) w hw) (W.inv_mem hw)
    have h2 : s * w * s⁻¹ * w⁻¹ ∈ S := by
      have := S.mul_mem hs (hSnorm w (hWL hw) s⁻¹ (S.inv_mem hs))
      rwa [← mul_assoc, ← mul_assoc] at this
    have h3 := Subgroup.disjoint_def.1 hdisj h2 h1
    calc s * w = s * w * s⁻¹ * w⁻¹ * (w * s) := by group
      _ = w * s := by rw [h3, one_mul]
  have hSW : S ≤ W := by
    intro s hs
    have hpt : ∀ z ∈ U, s z = z := by
      intro z hz
      apply hinj
      rw [hconj, hcomm s hs _ ⟨z, hUP₀ hz, rfl⟩, mul_inv_cancel_right]
    obtain ⟨z, hz, rfl⟩ := exists_eq_conj_of_forall_fix_projSiegel hp2 hr s hpt
    exact ⟨z, hUP₀ hz, rfl⟩
  exact hdisj.eq_bot_of_le hSW

end CFSG.RankThree.Classical
