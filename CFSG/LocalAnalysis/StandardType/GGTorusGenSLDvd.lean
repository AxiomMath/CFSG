module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLDvdDiag
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem exists_pPart_diag_SL_dvd
    {d p : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hp : p.Prime) (s0 : SpecialLinearGroup (Fin d) K)
    (hs0 : ∃ v : Fin d → K, (s0 : Matrix (Fin d) (Fin d) K) = diagonal v)
    {c : L'} (hc : φ s0 = c) (hcp : ∃ k : ℕ, c ^ p ^ k = 1) :
    ∃ s : SpecialLinearGroup (Fin d) K,
      (∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      (∃ k : ℕ, s ^ p ^ k = 1) ∧ φ s = c := by
  classical
  have : Finite (SpecialLinearGroup (Fin d) K) := by infer_instance
  obtain ⟨m, hm⟩ := hcp
  have hN : orderOf s0 ≠ 0 := (orderOf_pos s0).ne'
  obtain ⟨e, n', hn'p, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hcop : p.Coprime n' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn'p
  have hc' : (p ^ m).Coprime n' := (hcop.symm.pow_right m).symm
  obtain ⟨t, ht⟩ := Nat.chineseRemainder hc' 1 0
  have ht1 : t ≡ 1 [MOD p ^ m] := ht.1
  have ht0 : t ≡ 0 [MOD n'] := ht.2
  refine ⟨s0 ^ t, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hs0
    exact ⟨v ^ t, by rw [Matrix.SpecialLinearGroup.coe_pow, hv, diagonal_pow]⟩
  · obtain ⟨q, hq⟩ := Nat.modEq_zero_iff_dvd.mp ht0
    refine ⟨e, ?_⟩
    have hNpow : s0 ^ (p ^ e * n') = 1 := by rw [← hN, pow_orderOf_eq_one]
    calc (s0 ^ t) ^ p ^ e = s0 ^ (t * p ^ e) := by rw [pow_mul]
      _ = s0 ^ (n' * q * p ^ e) := by rw [hq]
      _ = s0 ^ (q * (p ^ e * n')) := by congr 1; ring
      _ = (s0 ^ (p ^ e * n')) ^ q := by rw [← pow_mul]; congr 1; ring
      _ = 1 := by rw [hNpow, one_pow]
  · rw [map_pow, hc, pow_eq_pow_of_modEq ht1 hm, pow_one]

theorem ggTorusGenTableBRk_PSL_dvd
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) (hpd : p ∣ d) :
    GGTorusGenTableBRk p (projectiveSL d K) (Set.range (conjAut d K)) (d - 1) := by
  intro M _ _ L' E E₁ D' J' dm θ hE hpos hr hC hE₁E hE₁C hcard hN hD'E hCD' hD'E₁ hd1 hJ
  classical
  obtain ⟨φ', hφs, hker, hdiagE⟩ :=
    exists_model_of_position_PSL hp hpK hd hpos hr
  obtain ⟨hdec, hcent⟩ := exists_mul_of_complement_position hp hpos hC hE₁E hE₁C hcard
  have hd5 : 5 ≤ d := by
    have hp2 : p ≠ 2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one (K := K) hpK
    by_contra hlt
    have hd4 : d = 4 := by omega
    have hp4 : p ∣ 4 := by rw [hd4] at hpd; exact hpd
    have hp22 : p ∣ 2 ^ 2 := by
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h4]; exact hp4
    have hp2dvd : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hp22
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)
  refine ⟨?_, ?_⟩
  ·
    intro z hz _
    exact centralizes_center_PSL hφs hker hdiagE z hz
  ·
    intro c hc hcp _
    have hcE : c ∈ Subgroup.centralizer (E : Set M) := hcent hc
    let cL : L' := ⟨c, hc.1⟩
    have hcpL : ∃ k : ℕ, cL ^ p ^ k = 1 := by
      obtain ⟨k, hk⟩ := hcp
      exact ⟨k, Subtype.ext (by simpa [Subgroup.coe_pow] using hk)⟩
    have hc_comm : ∀ s : SpecialLinearGroup (Fin d) K,
        (∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v) → s ^ p = 1 →
          cL * φ' s = φ' s * cL := by
      intro s hs hsp
      have hφsE : ((φ' s : L') : M) ∈ E := map_diag_pTorsion_mem_E_SL hpos hdiagE s hs hsp
      have h1 := Subgroup.mem_centralizer_iff.mp hcE ((φ' s : L') : M) hφsE
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact h1.symm
    obtain ⟨s0, hs0diag, hs0eq⟩ :=
      mem_diagImage_of_commute_pTorsion_SL_all hp hpK hd5 hφs hker cL hc_comm
    obtain ⟨sp, hspdiag, hspP, hspEq⟩ :=
      exists_pPart_diag_SL_dvd (p := p) hp s0 hs0diag hs0eq hcpL
    obtain ⟨I₀, hIcard, hJeq⟩ :=
      exists_block_of_isComponentOf_centralizer_SL hφs hker hdiagE hD'E hJ
    let Gen : Set (SpecialLinearGroup (Fin d) K) :=
      {x | x ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I₀ ∧
        (∃ v : Fin d → K, (x : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
        ∃ k : ℕ, x ^ p ^ k = 1}
    have hGen_mem : ∀ x : SpecialLinearGroup (Fin d) K, x ∈ Gen ↔
        x ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I₀ ∧
          (∃ v : Fin d → K, (x : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
          ∃ k : ℕ, x ^ p ^ k = 1 := fun _ => Iff.rfl
    let A : Subgroup (SpecialLinearGroup (Fin d) K) := Subgroup.closure Gen
    have hpair : Gen.Pairwise Commute := by
      intro x hx y hy _
      obtain ⟨v, hv⟩ := ((hGen_mem x).mp hx).2.1
      obtain ⟨w, hw⟩ := ((hGen_mem y).mp hy).2.1
      exact TypeA.commute_of_diagonal hv hw
    have hAcomm : IsMulCommutative A := Subgroup.isMulCommutative_closure hpair
    let T : Subgroup (SpecialLinearGroup (Fin d) K) :=
      { carrier := {x | x ∈ A ∧ ∃ k : ℕ, x ^ p ^ k = 1}
        one_mem' := ⟨A.one_mem, ⟨0, by simp⟩⟩
        mul_mem' := by
          rintro x y ⟨hxA, k, hxk⟩ ⟨hyA, l, hyl⟩
          refine ⟨A.mul_mem hxA hyA, ⟨max k l, ?_⟩⟩
          have hxy : Commute x y := by
            have h := (isMulCommutative_iff.mp hAcomm) ⟨x, hxA⟩ ⟨y, hyA⟩
            exact Subtype.ext_iff.mp h
          have hxk' : x ^ p ^ max k l = 1 := by
            have hd' : orderOf x ∣ p ^ max k l :=
              (orderOf_dvd_iff_pow_eq_one.mpr hxk).trans (Nat.pow_dvd_pow p (le_max_left k l))
            exact orderOf_dvd_iff_pow_eq_one.mp hd'
          have hyl' : y ^ p ^ max k l = 1 := by
            have hd' : orderOf y ∣ p ^ max k l :=
              (orderOf_dvd_iff_pow_eq_one.mpr hyl).trans (Nat.pow_dvd_pow p (le_max_right k l))
            exact orderOf_dvd_iff_pow_eq_one.mp hd'
          rw [hxy.mul_pow, hxk', hyl', mul_one]
        inv_mem' := by
          rintro x ⟨hxA, k, hxk⟩
          exact ⟨A.inv_mem hxA, ⟨k, by rw [inv_pow, hxk, inv_one]⟩⟩ }
    have hAT : A ≤ T := by
      rw [show A = Subgroup.closure Gen from rfl, Subgroup.closure_le]
      intro x hx
      exact ⟨Subgroup.subset_closure hx, ((hGen_mem x).mp hx).2.2⟩
    have hAP : IsPGroup p A := fun x => by
      obtain ⟨k, hk⟩ := (hAT x.2).2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    let ψ : SpecialLinearGroup (Fin d) K →* M := L'.subtype.comp φ'
    let S : Subgroup M := Subgroup.map ψ A
    let W : Set M := Set.range (fun σ : Equiv.Perm (Fin d) => ψ (TypeA.permSL σ))
    have hS_pg : IsPGroup p S := IsPGroup.map (H := A) hAP ψ
    have hScent : S ≤ Subgroup.centralizer (E₁ : Set M) := by
      have hle : A ≤ Subgroup.comap ψ (Subgroup.centralizer (E₁ : Set M)) := by
        rw [show A = Subgroup.closure Gen from rfl, Subgroup.closure_le]
        intro x hx
        change ψ x ∈ Subgroup.centralizer (E₁ : Set M)
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        obtain ⟨v, hv⟩ := ((hGen_mem x).mp hx).2.1
        obtain ⟨t, ht⟩ := hdiagE ⟨e, hE₁E he⟩
        have hxdiag : (x : Matrix (Fin d) (Fin d) K).IsDiag := by
          rw [hv, Matrix.isDiag_iff_diagonal_diag, Matrix.diag_diagonal]
        have hact : L'.normalizerMonoidHom ⟨e, hE (hE₁E he)⟩ (φ' x) = φ' x :=
          ht.apply_of_isDiag hxdiag
        have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE (hE₁E he)⟩ (φ' x)
        have h1 : e * ψ x * e⁻¹ = ψ x := by
          change e * ((φ' x : L') : M) * e⁻¹ = ((φ' x : L') : M)
          rw [← hcoe, hact]
        change e * ψ x = ψ x * e
        calc e * ψ x = (e * ψ x * e⁻¹) * e := by group
          _ = ψ x * e := by rw [h1]
      intro y hy
      obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hy
      exact hle hxA
    have hSJ : S ≤ J' := by
      intro y hy
      obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hy
      have hxblock : x ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I₀ :=
        (Subgroup.closure_le (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I₀)).mpr
          (fun z hz => ((hGen_mem z).mp hz).1) hxA
      have hJeq' : J' = (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I₀).map ψ :=
        hJeq
      have hφmem : ψ x ∈ (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I₀).map ψ :=
        Subgroup.mem_map.mpr ⟨x, hxblock, rfl⟩
      rw [← hJeq'] at hφmem
      exact hφmem
    have hWN : W ⊆ Subgroup.normalizer (E₁ : Set M) := by
      rintro n ⟨σ, rfl⟩
      exact hN (permSL_lift_mem_normalizer_typeA hpos hker hdiagE σ)
    refine ⟨S, W, hS_pg, hScent, hSJ, hWN, ?_⟩
    have hs4 := diag_pElt_mem_closure_permConj_SL (K := K) I₀ hIcard sp hspdiag hspP
    have hψsp : ψ sp = c := by
      change L'.subtype (φ' sp) = c
      rw [hspEq]
      rfl
    have hmem : ψ sp ∈ Subgroup.closure (ψ '' (⋃ σ : Equiv.Perm (Fin d),
        (fun x => TypeA.permSL σ * x * (TypeA.permSL σ)⁻¹) '' Gen)) := by
      have h0 : ψ sp ∈ Subgroup.map ψ (Subgroup.closure (⋃ σ : Equiv.Perm (Fin d),
          (fun x => TypeA.permSL σ * x * (TypeA.permSL σ)⁻¹) '' Gen)) :=
        Subgroup.mem_map.mpr ⟨sp, hs4, rfl⟩
      rwa [MonoidHom.map_closure] at h0
    have hsubset : ψ '' (⋃ σ : Equiv.Perm (Fin d),
          (fun x => TypeA.permSL σ * x * (TypeA.permSL σ)⁻¹) '' Gen) ⊆
        ⋃ n ∈ W, (fun s : M => n * s * n⁻¹) '' (S : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image] at hz ⊢
      obtain ⟨σ, x, hxGen, rfl⟩ := hz
      refine ⟨ψ (TypeA.permSL σ), ⟨σ, rfl⟩, ψ x, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨x, Subgroup.subset_closure hxGen, rfl⟩
      · rw [map_mul, map_mul, map_inv]
    rw [hψsp] at hmem
    exact Subgroup.closure_mono hsubset hmem

theorem ggTorusGenTableBRk_PSL_all
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) :
    GGTorusGenTableBRk p (projectiveSL d K) (Set.range (conjAut d K)) (d - 1) := by
  by_cases hpd : p ∣ d
  · exact ggTorusGenTableBRk_PSL_dvd hp hpK hd hpd
  · exact ggTorusGenTableBRk_PSL hp hpK hd hpd

theorem largeEvenLabelAll_torusGenTableB_typeA
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) (hl : 3 ≤ lab.rank) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hd : 4 ≤ l + 1 := by omega
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  have hsec : TypeA.SLHasSections (l + 1) K := slHasSections_of_four_le hp hpK hd
  have hsub : (l + 1) - 2 = (l + 1) - 1 - 1 := by omega
  refine ggTorusGenTableB_of_mulEquiv (R' := projectiveSL (l + 1) K)
    (I' := Set.range (conjAut (l + 1) K)) (TypeA.recipeEquiv (l + 1) K) ?_ ?_
  · intro φ hφ
    exact TypeA.congr_recipeEquiv_mem hφ
  · refine ggTorusGenTableB_of_rk (p := p) (r := (l + 1) - 1) hp (by omega) ?_ ?_
    · rw [← hsub]
      exact TypeA.ggTorusLift_sub_two (d := l + 1) hp hpK (by omega) hsec
    · exact ggTorusGenTableBRk_PSL_all (K := K) hp hpK hd

end CFSG.StandardType
