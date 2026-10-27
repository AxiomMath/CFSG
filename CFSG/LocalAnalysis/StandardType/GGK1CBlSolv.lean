module

public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnIdentA
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LieType.SemisimpleCentralizers.Held

private theorem ggK1Bv_witness_mulEquiv {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    {p : ℕ} (h : ∃ t a : H, t ^ p = 1 ∧ a * t ≠ t * a) :
    ∃ t a : G, t ^ p = 1 ∧ a * t ≠ t * a := by
  obtain ⟨t, a, ht, hne⟩ := h
  refine ⟨φ.symm t, φ.symm a, ?_, ?_⟩
  · rw [← map_pow φ.symm t p, ht, map_one]
  · intro hc
    exact hne (by
      have := congrArg φ hc
      simpa [map_mul] using this)

private theorem ggK1Bv_witness_subgroup {G H : Type} [Group G] [Group H] {A : Subgroup G}
    (φ : ↥A ≃* H) {p : ℕ} (h : ∃ t a : H, t ^ p = 1 ∧ a * t ≠ t * a) :
    ∃ t ∈ A, t ^ p = 1 ∧ ∃ a ∈ A, a * t ≠ t * a := by
  obtain ⟨t, a, ht, hne⟩ := h
  refine ⟨(φ.symm t : G), (φ.symm t).2, ?_, (φ.symm a : G), (φ.symm a).2, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow φ.symm t p, ht, map_one, Subgroup.coe_one]
  · intro hc
    apply hne
    have hc' : (φ.symm a) * (φ.symm t) = (φ.symm t) * (φ.symm a) :=
      Subtype.ext (by simpa [Subgroup.coe_mul] using hc)
    have := congrArg φ hc'
    simpa [map_mul] using this

private theorem ggK1Bv_perm3_witness :
    ∃ t a : Equiv.Perm (Fin 3), t ^ 3 = 1 ∧ a * t ≠ t * a := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 1, ?_, ?_⟩ <;> decide

private noncomputable def ggK1Bv_fieldEquiv {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) : K ≃+* ZMod 2 :=
  FiniteField.ringEquivOfCardEq (K := K) (K' := ZMod 2) (by rw [ZMod.card]; exact hK)

private theorem ggK1Bv_gl2_witness {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) :
    ∃ t a : Matrix.GeneralLinearGroup (Fin 2) K, t ^ 3 = 1 ∧ a * t ≠ t * a :=
  ggK1Bv_witness_mulEquiv
    ((glFieldEquiv (Fin 2) (ggK1Bv_fieldEquiv hK)).trans (s16c1610_permGL).symm)
    ggK1Bv_perm3_witness

private theorem ggK1Bv_sl2_witness {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) :
    ∃ t a : Matrix.SpecialLinearGroup (Fin 2) K, t ^ 3 = 1 ∧ a * t ≠ t * a :=
  ggK1Bv_witness_mulEquiv
    ((slFieldEquiv (Fin 2) (ggK1Bv_fieldEquiv hK)).trans (s16c1610_slPermEquiv).symm)
    ggK1Bv_perm3_witness

private theorem ggK1Bv_bar_apply_two {E : Type} [Field E]
    (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 E) (x : E) :
    hE.bar x = x ^ 2 := by
  rw [hE.bar_apply]
  norm_num

private theorem ggK1Bv_omega {E : Type} [Field E]
    (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 E)
    (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (hτ2 : ∀ x, τ x = x ^ 2) :
    ∃ c : E, c ≠ 0 ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ τ c * c = 1 := by
  obtain ⟨c, hc⟩ := hE.exists_bar_ne
  have hτc : τ c ≠ c := by
    intro h
    apply hc
    rw [ggK1Bv_bar_apply_two hE c, ← hτ2 c, h]
  have hc0 : c ≠ 0 := by
    intro h; apply hτc; rw [h]; simp
  have hc1 : c ≠ 1 := by
    intro h; apply hτc; rw [h]; simp
  haveI : Finite E := hE.finite
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = 4 := by
    rw [← Nat.card_eq_fintype_card]; simpa using hE.card
  have hc3 : c ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hcard] at this
  have hbar : τ c * c = 1 := by
    rw [hτ2 c, ← pow_succ]
    exact hc3
  exact ⟨c, hc0, hc1, hc3, hbar⟩

private theorem ggK1Bv_heldGU2_witness {E : Type} [Field E]
    (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 E)
    (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (hτ2 : ∀ x, τ x = x ^ 2) :
    ∃ t a : heldGU 2 E τ hτ, t ^ 3 = 1 ∧ a * t ≠ t * a := by
  obtain ⟨c, hc0, hc1, hc3, hbar⟩ := ggK1Bv_omega hE τ hτ hτ2
  let tm : Matrix (Fin 2) (Fin 2) E := !![c, 0; 0, 1]
  let am : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]
  have htdet : tm.det ≠ 0 := by
    rw [Matrix.det_fin_two]; simp [tm, hc0]
  have hadet : am.det ≠ 0 := by
    rw [Matrix.det_fin_two]; simp [am]
  let tGL : GL (Fin 2) E := Matrix.GeneralLinearGroup.mkOfDetNeZero tm htdet
  let aGL : GL (Fin 2) E := Matrix.GeneralLinearGroup.mkOfDetNeZero am hadet
  have htmem : tGL ∈ heldGU 2 E τ hτ := by
    rw [mem_heldGU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tm, hbar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
        Matrix.transpose_apply]
  have hamem : aGL ∈ heldGU 2 E τ hτ := by
    rw [mem_heldGU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [am, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
        Matrix.transpose_apply]
  have hc3' : c * c * c = 1 := by
    rw [← pow_two, ← pow_succ]
    exact hc3
  have ht3 : tGL ^ 3 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [tGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, tm, Matrix.mul_apply,
        Fin.sum_univ_two, pow_succ, hc3']
  have hne : aGL * tGL ≠ tGL * aGL := by
    intro hcon
    have h01 := congrArg (fun x : GL (Fin 2) E => (x : Matrix (Fin 2) (Fin 2) E) 0 1) hcon
    simp [aGL, tGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, am, tm, Matrix.mul_apply,
      Fin.sum_univ_two] at h01
    exact hc1 h01.symm
  refine ⟨⟨tGL, htmem⟩, ⟨aGL, hamem⟩, ?_, ?_⟩
  · apply Subtype.ext
    simpa [Subgroup.coe_pow] using ht3
  · intro hcon
    apply hne
    have := congrArg Subtype.val hcon
    simpa [Subgroup.coe_mul] using this

private theorem ggK1Bv_heldGU3_witness {E : Type} [Field E]
    (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 E)
    (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (hτ2 : ∀ x, τ x = x ^ 2) :
    ∃ t a : heldGU 3 E τ hτ, t ^ 3 = 1 ∧ a * t ≠ t * a := by
  obtain ⟨c, hc0, hc1, hc3, hbar⟩ := ggK1Bv_omega hE τ hτ hτ2
  let tm : Matrix (Fin 3) (Fin 3) E := !![c, 0, 0; 0, 1, 0; 0, 0, 1]
  let am : Matrix (Fin 3) (Fin 3) E := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  have htdet : tm.det ≠ 0 := by
    rw [Matrix.det_fin_three]; simp [tm, hc0]
  have hadet : am.det ≠ 0 := by
    rw [Matrix.det_fin_three]; simp [am]
  let tGL : GL (Fin 3) E := Matrix.GeneralLinearGroup.mkOfDetNeZero tm htdet
  let aGL : GL (Fin 3) E := Matrix.GeneralLinearGroup.mkOfDetNeZero am hadet
  have htmem : tGL ∈ heldGU 3 E τ hτ := by
    rw [mem_heldGU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tm, hbar, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
        Matrix.transpose_apply]
  have hamem : aGL ∈ heldGU 3 E τ hτ := by
    rw [mem_heldGU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [am, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
        Matrix.transpose_apply]
  have hc3' : c * c * c = 1 := by
    rw [← pow_two, ← pow_succ]
    exact hc3
  have ht3 : tGL ^ 3 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [tGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, tm, Matrix.mul_apply,
        Fin.sum_univ_three, pow_succ, hc3']
  have hne : aGL * tGL ≠ tGL * aGL := by
    intro hcon
    have h01 := congrArg (fun x : GL (Fin 3) E => (x : Matrix (Fin 3) (Fin 3) E) 0 1) hcon
    simp [aGL, tGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, am, tm, Matrix.mul_apply,
      Fin.sum_univ_three] at h01
    exact hc1 h01.symm
  refine ⟨⟨tGL, htmem⟩, ⟨aGL, hamem⟩, ?_, ?_⟩
  · apply Subtype.ext
    simpa [Subgroup.coe_pow] using ht3
  · intro hcon
    apply hne
    have := congrArg Subtype.val hcon
    simpa [Subgroup.coe_mul] using this

private theorem ggK1Bv_nf_eq_one {nf : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    {A : Subgroup G} {kind : ggK1CCo_Kind}
    (hw : ggK1CBl_KindWitness nf K kind A) (hh : kind.hasOrbit = true)
    (hqs : (ggK1CCo_kindOrbit nf kind).qs = false) : nf = 1 := by
  by_contra hnf
  have htrue : (ggK1CCo_kindOrbit nf kind).qs = true := by
    rcases kind with s | m | m
    · rcases eq_or_ne s 1 with hs1 | hs1
      · subst hs1
        simp [ggK1CCo_kindOrbit, hnf]
      · by_cases h2 : s = 2 ∧ nf = 1
        · exact absurd h2.2 hnf
        · simp [ggK1CCo_kindOrbit, hs1, h2]
    · have hm1 : m ≠ 1 := by
        intro h; subst h; simp [ggK1CCo_Kind.hasOrbit] at hh
      rcases m with _ | _ | m
      · simp [ggK1CCo_kindOrbit, ggMultBlockA]
      · exact absurd rfl hm1
      · simp [ggK1CCo_kindOrbit, ggMultBlockA, hnf]
    · have hm1 : m ≠ 1 := by
        intro h; subst h; simp [ggK1CCo_Kind.hasOrbit] at hh
      rcases m with _ | _ | m
      · simp [ggK1CCo_kindOrbit, ggMultBlockA, hnf]
      · exact absurd rfl hm1
      · by_cases h2 : 2 ≤ m + 1
        · simp [ggK1CCo_kindOrbit, ggMultBlockA, hnf, h2]
        · simp [ggK1CCo_kindOrbit, ggMultBlockA, hnf, h2]
  rw [hqs] at htrue
  exact Bool.noConfusion htrue

private theorem ggK1Bv_p_eq_three {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ 2 ^ 1 - 1 ∨ p ∣ 2 ^ 1 + 1) : p = 3 := by
  rcases hdvd with h | h
  · have : p = 1 := Nat.dvd_one.mp (by simpa using h)
    exact absurd this hp.ne_one
  · have h3 : p ∣ 3 := by simpa using h
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3

theorem ggK1CBl_solvable_witness {nf p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {kind : ggK1CCo_Kind}
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hw : ggK1CBl_KindWitness nf K kind A) (hh : kind.hasOrbit = true)
    (hqs : (ggK1CCo_kindOrbit nf kind).qs = false) :
    ∃ t ∈ A, t ^ p = 1 ∧ ∃ a ∈ A, a * t ≠ t * a := by
  haveI : Fintype K := Fintype.ofFinite K
  have hnf1 : nf = 1 := ggK1Bv_nf_eq_one hw hh hqs
  subst hnf1
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hcardK : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hK2
  have hp3 : p = 3 := ggK1Bv_p_eq_three hp (by simpa using hdvd)
  subst hp3
  rcases kind with s | m | m
  ·
    rcases hw with ⟨hs, W, hWac, hWmod, hWfd, B, hBalt, hBnon, hdim, ⟨e⟩⟩
    letI : AddCommGroup W := hWac
    letI : Module K W := hWmod
    haveI : FiniteDimensional K W := hWfd
    have hs1 : s = 1 := by
      by_contra hs1
      have htrue : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sp s)).qs = true := by
        by_cases h2 : s = 2
        · subst h2; simp [ggK1CCo_kindOrbit]
        · simp [ggK1CCo_kindOrbit, hs1, h2]
      rw [hqs] at htrue
      exact Bool.noConfusion htrue
    subst hs1
    obtain ⟨s', hfin, ⟨e₀⟩⟩ :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hBalt hBnon
    have hs'1 : s' = 1 := by omega
    subst hs'1
    have hSL : Nonempty (↥A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
      ⟨(e.trans e₀).trans
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm⟩
    obtain ⟨φ⟩ := hSL
    exact ggK1Bv_witness_subgroup φ (ggK1Bv_sl2_witness hcardK)
  ·
    rcases hw with ⟨hm, ⟨e⟩⟩
    have hm2 : m = 2 := by
      have hm1 : m ≠ 1 := by
        intro h; subst h; simp [ggK1CCo_Kind.hasOrbit] at hh
      rcases m with _ | _ | m
      · have htrue : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sl 0)).qs = true := by
          simp [ggK1CCo_kindOrbit, ggMultBlockA]
        rw [hqs] at htrue
        exact Bool.noConfusion htrue
      · exact absurd rfl hm1
      · have hqs' : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sl (m + 2))).qs
            = decide (¬ ((m + 2) - 1 = 1 ∧ (1 : ℕ) = 1)) := by
          simp [ggK1CCo_kindOrbit, ggMultBlockA]
        rw [hqs'] at hqs
        have hnot : ¬ ¬ ((m + 2) - 1 = 1 ∧ (1 : ℕ) = 1) := Bool.of_decide_false hqs
        have h1 : (m + 2) - 1 = 1 := by
          by_contra hcon
          exact hnot (fun h => hcon h.1)
        omega
    subst hm2
    exact ggK1Bv_witness_subgroup e (ggK1Bv_gl2_witness hcardK)
  ·
    rcases hw with ⟨hm, E, hEfield, hEfin, hE, V, hVadd, hVmod, hVfd, Hf,
      hHfsymm, hHfsep, ⟨b, hb⟩, ⟨e⟩⟩
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    letI : AddCommGroup V := hVadd
    letI : Module E V := hVmod
    haveI : FiniteDimensional E V := hVfd
    have hm23 : m = 2 ∨ m = 3 := by
      have hm1 : m ≠ 1 := by
        intro h; subst h; simp [ggK1CCo_Kind.hasOrbit] at hh
      rcases m with _ | _ | m
      · omega
      · exact absurd rfl hm1
      · by_cases h2 : 2 ≤ m + 1
        · right
          have hqs' : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.su (m + 2))).qs
              = decide (¬ ((m + 2) - 1 = 2 ∧ (1 : ℕ) = 1)) := by
            simp [ggK1CCo_kindOrbit, ggMultBlockA, h2]
          rw [hqs'] at hqs
          have hnot : ¬ ¬ ((m + 2) - 1 = 2 ∧ (1 : ℕ) = 1) := Bool.of_decide_false hqs
          have h1 : (m + 2) - 1 = 2 := by
            by_contra hcon
            exact hnot (fun h => hcon h.1)
          omega
        · left
          omega
    let ρE : E ≃+* E :=
      { toFun := hE.bar
        invFun := hE.bar
        left_inv := hE.bar_bar
        right_inv := hE.bar_bar
        map_mul' := hE.bar.map_mul
        map_add' := hE.bar.map_add }
    have hρE : ∀ x, ρE (ρE x) = x := hE.bar_bar
    have hρE2 : ∀ x, ρE x = x ^ 2 := by
      intro x; change hE.bar x = x ^ 2; rw [hE.bar_apply]; norm_num
    obtain ⟨eU⟩ :=
      CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU ρE hρE Hf b hb
    rcases hm23 with rfl | rfl
    · exact ggK1Bv_witness_subgroup (e.trans eU) (ggK1Bv_heldGU2_witness hE ρE hρE hρE2)
    · exact ggK1Bv_witness_subgroup (e.trans eU) (ggK1Bv_heldGU3_witness hE ρE hρE hρE2)

end CFSG.StandardType

end
