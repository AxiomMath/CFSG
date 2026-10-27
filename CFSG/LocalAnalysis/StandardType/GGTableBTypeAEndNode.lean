module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeABstar

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly

variable {d p : ℕ} {K : Type} [Field K]

theorem ggEndNode_small [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGEndNode p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hle := card_le_of_subset_conjAut hp hpK hd hpd hX hXI
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
  omega

theorem pow_act {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    {D : SpecialLinearGroup (Fin d) K} {a : MulAut L'} (ha : ∀ s, a (φ s) = φ (D * s * D⁻¹))
    (k : ℕ) : ∀ s, (a ^ k) (φ s) = φ (D ^ k * s * (D ^ k)⁻¹) := by
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    rw [pow_succ', MulAut.mul_apply, ih, ha]
    congr 1
    group

theorem const_of_commute_coordBlockSL {D' : SpecialLinearGroup (Fin d) K} {t' : Fin d → K}
    (hD' : (D' : Matrix (Fin d) (Fin d) K) = diagonal t') {i₀ : Fin d}
    (h : ∀ s ∈ coordBlockSL K ({i₀}ᶜ : Finset (Fin d)), s * D' = D' * s) :
    ∀ i j, i ≠ i₀ → j ≠ i₀ → t' i = t' j := by
  intro i j hi hj
  by_cases hij : i = j
  · rw [hij]
  · have hmem : SpecialLinearGroup.transvection hij (1 : K) ∈
        coordBlockSL K ({i₀}ᶜ : Finset (Fin d)) := by
      rw [mem_coordBlockSL_iff]
      intro a b hab
      simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at hab
      rw [CFSG.LinearGroups.coe_transvection]
      rcases hab with rfl | rfl
      · simp [Matrix.one_apply, hi]
      · simp [Matrix.one_apply, hj]
    have h1 := (commute_diagonal_iff hD').mp (h _ hmem)
    by_contra hne
    have h2 := h1 i j hne
    rw [CFSG.LinearGroups.coe_transvection] at h2
    simp [hij] at h2

theorem conj_eq_of_diagonal_smul {D' E : SpecialLinearGroup (Fin d) K} {t' u : Fin d → K}
    (hD' : (D' : Matrix (Fin d) (Fin d) K) = diagonal t')
    (hE : (E : Matrix (Fin d) (Fin d) K) = diagonal u) {c : K} (hc : ∀ i, t' i = c * u i)
    (hd : 0 < d) (s : SpecialLinearGroup (Fin d) K) : D' * s * D'⁻¹ = E * s * E⁻¹ := by
  set z := D' * E⁻¹ with hzdef
  have hEinv : (E : Matrix (Fin d) (Fin d) K) *
      ((E⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (D' : Matrix (Fin d) (Fin d) K) =
      scalar (Fin d) c * (E : Matrix (Fin d) (Fin d) K) := by
    rw [hD', hE, scalar_apply, diagonal_mul_diagonal]
    congr 1
    funext i
    exact hc i
  have hz : (z : Matrix (Fin d) (Fin d) K) = scalar (Fin d) c := by
    rw [hzdef, Matrix.SpecialLinearGroup.coe_mul, h2, Matrix.mul_assoc, hEinv, Matrix.mul_one]
  have hzc := scalars_le_center d K (mem_scalars_of_coe_eq_scalar hd hz).2
  have hD'E : D' = z * E := by rw [hzdef]; group
  rw [hD'E]
  calc z * E * s * (z * E)⁻¹ = z * (E * s * E⁻¹) * z⁻¹ := by group
    _ = (E * s * E⁻¹) * z * z⁻¹ := by rw [(Subgroup.mem_center_iff.mp hzc) (E * s * E⁻¹)]
    _ = E * s * E⁻¹ := by group

theorem ggEndNode_coprime [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    (hpd : Nat.Coprime p d) (h4 : 4 ≤ Nat.card K) (hsec : SLHasSections d K) :
    GGEndNode p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  obtain ⟨φ', hφ's, hφ'ker, hdiag, hle, hfull⟩ :=
    exists_diagonal_model hp hpK (by omega) hpd hperfSL hψ hker hperf hφs hφ hA hAI
  have hcardA : Nat.card A = p ^ (d - 1) := le_antisymm hle hr
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hdd : ζ⁻¹ ^ d = ζ⁻¹ ^ (d - 1) * ζ⁻¹ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set t₁ : Fin d → K := fun i => if i = i₀ then ζ⁻¹ ^ (d - 1) else ζ with ht₁
  have ht₁0 : t₁ i₀ = ζ⁻¹ ^ (d - 1) := by simp [ht₁]
  have ht₁j : ∀ j, j ≠ i₀ → t₁ j = ζ := fun j hj => by simp [ht₁, hj]
  have ht₁p : ∀ i, t₁ i ^ p = 1 := by
    intro i
    by_cases h : i = i₀
    · rw [h, ht₁0, ← pow_mul, mul_comm, pow_mul, inv_pow, hζp, inv_one, one_pow]
    · rw [ht₁j i h, hζp]
  have ht₁prod : ∏ i, t₁ i = 1 := by
    rw [Fintype.prod_eq_mul_prod_compl i₀ t₁,
      Finset.prod_congr rfl (fun i hi => ht₁j i (by simpa using hi)), Finset.prod_const,
      Finset.card_compl, Finset.card_singleton, Fintype.card_fin, ht₁0, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hζ0)]
  have hζd : ζ ^ d ≠ 1 := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hpd ((hζ.pow_eq_one_iff_dvd d).mp h))
  have ht0 : ∀ j, j ≠ i₀ → t₁ j ≠ t₁ i₀ := by
    intro j hj h
    rw [ht₁j j hj, ht₁0] at h
    apply hζd
    calc ζ ^ d = ζ ^ (d - 1) * ζ := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
      _ = ζ ^ (d - 1) * ζ⁻¹ ^ (d - 1) := by rw [← h]
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
  have ht1 : ∀ i j, i ≠ i₀ → j ≠ i₀ → t₁ i = t₁ j := fun i j hi hj => by
    rw [ht₁j i hi, ht₁j j hj]
  obtain ⟨a₁, ha₁A, D₁, hD₁, ha₁⟩ := hfull hcardA t₁ ht₁p ht₁prod
  have hD₁p : D₁ ^ p = 1 := by
    have h1 : t₁ ^ p = fun _ => (1 : K) := funext ht₁p
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hD₁, diagonal_pow, h1, diagonal_one]
    rfl
  have hS : 2 ≤ ({i₀}ᶜ : Finset (Fin d)).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨hL, hJcomp⟩ := layer_ggFix_eq h4 hS ht0 ht1 hφ'ker hpd hφ's hD₁ hD₁p ha₁
  set j₁ : Fin d := ⟨1, by omega⟩ with hj₁def
  have hj₁ : j₁ ≠ i₀ := by simp [hj₁def, hi₀]
  refine ⟨a₁, ha₁A, ?_, hL ▸ hJcomp, ?_⟩
  · intro h1
    have hs : SpecialLinearGroup.transvection hj₁.symm (1 : K) ∈ Subgroup.centralizer {D₁} := by
      apply mem_centralizer_of_apply_eq hφ'ker hpd hD₁p
      have h2 := (ha₁ (SpecialLinearGroup.transvection hj₁.symm (1 : K))).symm
      rw [h1, MulAut.one_apply] at h2
      exact h2
    have h2 := (entry_eq_zero_of_mem ht0 hD₁ hs hj₁).1
    rw [CFSG.LinearGroups.coe_transvection] at h2
    simp [hj₁.symm] at h2
  · intro a' ha'
    rw [hL]
    obtain ⟨D', ⟨t', hD'⟩, hD'p, ha'⟩ := hdiag a' ha'
    constructor
    · intro hfix
      have hcomm : ∀ s ∈ coordBlockSL K ({i₀}ᶜ : Finset (Fin d)), s * D' = D' * s := by
        intro s hs
        have h1 : a' (φ' s) = φ' s := hfix _ ⟨s, hs, rfl⟩
        rw [ha'] at h1
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (mem_centralizer_of_apply_eq hφ'ker hpd hD'p h1)
      have hconst := const_of_commute_coordBlockSL hD' hcomm
      have ht'p : ∀ i, t' i ^ p = 1 := by
        intro i
        have h1 : (D' : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
          rw [← Matrix.SpecialLinearGroup.coe_pow, hD'p]
          rfl
        rw [hD', diagonal_pow] at h1
        have h2 := congrFun (congrFun h1 i) i
        simpa using h2
      have hβ0 : t' j₁ ≠ 0 := fun h => by
        have h1 := ht'p j₁
        rw [h, zero_pow hp.ne_zero] at h1
        exact zero_ne_one h1
      have hprim : IsPrimitiveRoot (ζ⁻¹ ^ d) p := hζ.inv.pow_of_coprime d hpd.symm
      have : NeZero p := ⟨hp.ne_zero⟩
      obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one
        (show (t' i₀ / t' j₁) ^ p = 1 by rw [div_pow, ht'p, ht'p, div_one])
      have hc : ∀ i, t' i = (t' j₁ / ζ ^ k) * t₁ i ^ k := by
        intro i
        by_cases hi : i = i₀
        · rw [hi, ht₁0]
          have e1 : t' i₀ = t' j₁ * (ζ⁻¹ ^ d) ^ k := by
            rw [hk]
            field_simp
          rw [e1, hdd, mul_pow, inv_pow, div_eq_mul_inv]
          ring
        · rw [hconst i j₁ hi hj₁, ht₁j i hi]
          field_simp
      have hD₁k : ((D₁ ^ k : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          diagonal (fun i => t₁ i ^ k) := by
        rw [Matrix.SpecialLinearGroup.coe_pow, hD₁, diagonal_pow]
        rfl
      have hconj : ∀ s, D' * s * D'⁻¹ = D₁ ^ k * s * (D₁ ^ k)⁻¹ := fun s =>
        conj_eq_of_diagonal_smul hD' hD₁k hc (by omega) s
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      rw [zpow_natCast]
      ext l
      obtain ⟨s, rfl⟩ := hφ's l
      rw [pow_act ha₁ k s, ha', hconj]
    · intro hmem j hj
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hj1 : a₁ j = j := hJcomp.1 hj
      have hstab : a₁ ∈ MulAction.stabilizer (MulAut L') j :=
        MulAction.mem_stabilizer_iff.mpr (by rw [MulAut.smul_def]; exact hj1)
      have h1 := MulAction.mem_stabilizer_iff.mp
        ((Subgroup.zpowers_le.mpr hstab) (Subgroup.zpow_mem_zpowers a₁ m))
      rwa [MulAut.smul_def] at h1

end CFSG.StandardType.TypeA
