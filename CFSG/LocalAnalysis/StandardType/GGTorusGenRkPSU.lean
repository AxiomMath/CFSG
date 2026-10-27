module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkInE
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkModel
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkDiag
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkGen
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem ggtorus_conjN_eq_self_of_diag {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t v : Fin d → K}
    (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d))
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    conjN D hD s = s := by
  refine Subtype.ext ?_
  rw [coe_conjN]
  have hcomm : D * (s : GL (Fin d) K) = (s : GL (Fin d) K) * D := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [hDt, hs]
    exact Matrix.commute_diagonal t v
  rw [hcomm]
  group

private theorem ggtorus_commute_of_diag {d n : ℕ} {K : Type} [Field K]
    {x y : ↥(unitarySU 2 n K d)}
    (hx : ∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v)
    (hy : ∃ w : Fin d → K, ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w) :
    Commute x y := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨w, hw⟩ := hy
  show x * y = y * x
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hv, hw]
  exact Matrix.commute_diagonal v w

private theorem ggtorus_exists_diag_pPart
    {d n p : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hp : p.Prime) (s0 : ↥(unitarySU 2 n K d))
    (hs0 : ∃ v : Fin d → K, ((s0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v)
    {c : L'} (hc : φ s0 = c) (hcp : ∃ k : ℕ, c ^ p ^ k = 1) :
    ∃ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      (∃ k : ℕ, s ^ p ^ k = 1) ∧ φ s = c := by
  classical
  haveI : Finite ↥(unitarySU 2 n K d) := by infer_instance
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
    exact ⟨v ^ t, by rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hv, diagonal_pow]⟩
  · obtain ⟨q, hq⟩ := Nat.modEq_zero_iff_dvd.mp ht0
    refine ⟨e, ?_⟩
    have hNpow : s0 ^ (p ^ e * n') = 1 := by rw [← hN, pow_orderOf_eq_one]
    calc (s0 ^ t) ^ p ^ e = s0 ^ (t * p ^ e) := by rw [pow_mul]
      _ = s0 ^ (n' * q * p ^ e) := by rw [hq]
      _ = s0 ^ (q * (p ^ e * n')) := by congr 1; ring
      _ = (s0 ^ (p ^ e * n')) ^ q := by rw [← pow_mul]; congr 1; ring
      _ = 1 := by rw [hNpow, one_pow]
  · rw [map_pow, hc, pow_eq_pow_of_modEq ht1 hm, pow_one]

theorem ggTorusGenTableBRk_PSU_of_ne_six_one
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (h61 : (d, n) ≠ (6, 1)) :
    GGTorusGenTableBRk p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) (d - 1) := by
  intro M _ _ L' E E₁ D' J' dm θ hE hpos hr hC hE₁E hE₁C hcard hN hD'E hCD' hD'E₁ hd1 hJ
  classical
  refine ⟨centralizes_center_pElts_rowA hK hn hd hp hpq hpd h61 hpos hr, ?_⟩
  intro c hc hcp hdisj
  obtain ⟨φ, hmodel, hdiagE⟩ :=
    exists_model_of_position_rowA hK hn hd hp hpq hpd h61 hpos hr
  obtain ⟨hdec, hcent⟩ := exists_mul_of_complement_position hp hpos hC hE₁E hE₁C hcard
  have hdE : dm ∈ E := by
    have hdmem : dm ∈ D' ⊓ E₁ := by rw [hD'E₁]; exact Subgroup.mem_zpowers dm
    exact hD'E hdmem.1
  let cL : L' := ⟨c, hc.1⟩
  have hcpL : ∃ k : ℕ, cL ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    exact ⟨k, Subtype.ext (by simpa [Subgroup.coe_pow] using hk)⟩
  have hcE : c ∈ Subgroup.centralizer (E : Set M) := hcent hc
  have hc_comm : ∀ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) →
        s ^ p = 1 → cL * φ s = φ s * cL := by
    intro s hs hsp
    have hφsE : ((φ s : L') : M) ∈ E := map_diag_pTorsion_mem_E hpos hdiagE s hs hsp
    have h1 := Subgroup.mem_centralizer_iff.mp hcE ((φ s : L') : M) hφsE
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact h1.symm
  obtain ⟨s0, hs0diag, hs0eq⟩ :=
    mem_diagImage_of_commute_pTorsion hmodel hd hp hpq cL hc_comm
  obtain ⟨sp, hspdiag, hspP, hspEq⟩ :=
    ggtorus_exists_diag_pPart (p := p) hp s0 hs0diag hs0eq hcpL
  have hcomp : IsComponentOf (J'.subgroupOf L') (ggFix (L'.normalizerMonoidHom ⟨dm, hE hdE⟩)) :=
    isComponentOf_subgroupOf_ggFix_of_decomp hE hdE hdec hD'E hCD' hD'E₁ hJ
  obtain ⟨t, ht⟩ := hdiagE ⟨dm, hdE⟩
  obtain ⟨i₀, hIcard, hJeq⟩ := exists_class_of_isComponentOf_ggFix hmodel ht hcomp
  let I : Finset (Fin d) := Finset.univ.filter fun i => t i = t i₀
  have hIcard' : 2 ≤ I.card := hIcard
  let Gen : Set ↥(unitarySU 2 n K d) :=
    {x | x ∈ TableBUE.blockSU (K := K) (n := n) I ∧
      (∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      ∃ k : ℕ, x ^ p ^ k = 1}
  have hGen_mem : ∀ x : ↥(unitarySU 2 n K d), x ∈ Gen ↔
      x ∈ TableBUE.blockSU (K := K) (n := n) I ∧
        (∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
        ∃ k : ℕ, x ^ p ^ k = 1 := fun _ => Iff.rfl
  let A : Subgroup ↥(unitarySU 2 n K d) := Subgroup.closure Gen
  have hpair : Gen.Pairwise Commute := by
    intro x hx y hy _
    exact ggtorus_commute_of_diag ((hGen_mem x).mp hx).2.1 ((hGen_mem y).mp hy).2.1
  have hAcomm : IsMulCommutative A := Subgroup.isMulCommutative_closure hpair
  let T : Subgroup ↥(unitarySU 2 n K d) :=
    { carrier := {x | x ∈ A ∧ ∃ k : ℕ, x ^ p ^ k = 1}
      one_mem' := ⟨A.one_mem, ⟨0, by simp⟩⟩
      mul_mem' := by
        rintro x y ⟨hxA, k, hxk⟩ ⟨hyA, l, hyl⟩
        refine ⟨A.mul_mem hxA hyA, ⟨max k l, ?_⟩⟩
        have hxy : Commute x y := by
          have h := (isMulCommutative_iff.mp hAcomm) ⟨x, hxA⟩ ⟨y, hyA⟩
          exact Subtype.ext_iff.mp h
        have hxk' : x ^ p ^ max k l = 1 := by
          have hd : orderOf x ∣ p ^ max k l :=
            (orderOf_dvd_iff_pow_eq_one.mpr hxk).trans (Nat.pow_dvd_pow p (le_max_left k l))
          exact orderOf_dvd_iff_pow_eq_one.mp hd
        have hyl' : y ^ p ^ max k l = 1 := by
          have hd : orderOf y ∣ p ^ max k l :=
            (orderOf_dvd_iff_pow_eq_one.mpr hyl).trans (Nat.pow_dvd_pow p (le_max_right k l))
          exact orderOf_dvd_iff_pow_eq_one.mp hd
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
  let ψ : ↥(unitarySU 2 n K d) →* M := L'.subtype.comp φ
  let S : Subgroup M := Subgroup.map ψ A
  let W : Set M := Set.range (fun σ : Equiv.Perm (Fin d) => ψ (permSU hmodel.field σ))
  have hS_pg : IsPGroup p S := IsPGroup.map (H := A) hAP ψ
  have hScent : S ≤ Subgroup.centralizer (E₁ : Set M) := by
    have hle : A ≤ Subgroup.comap ψ (Subgroup.centralizer (E₁ : Set M)) := by
      rw [show A = Subgroup.closure Gen from rfl, Subgroup.closure_le]
      intro x hx
      change ψ x ∈ Subgroup.centralizer (E₁ : Set M)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨v, hv⟩ := ((hGen_mem x).mp hx).2.1
      obtain ⟨t', D, hD, hDt, hact⟩ := hdiagE ⟨e, hE₁E he⟩
      have hconj := hact x
      rw [ggtorus_conjN_eq_self_of_diag D hD hDt x hv] at hconj
      have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE (hE₁E he)⟩ (φ x)
      have h1 : e * ((φ x : L') : M) * e⁻¹ = ((φ x : L') : M) := by
        rw [← hcoe, hconj]
      change e * ((φ x : L') : M) = ((φ x : L') : M) * e
      calc e * ((φ x : L') : M) = (e * ((φ x : L') : M) * e⁻¹) * e := by group
        _ = ((φ x : L') : M) * e := by rw [h1]
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hy
    exact hle hxA
  have hSJ : S ≤ J' := by
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hy
    have hxblock : x ∈ TableBUE.blockSU (K := K) (n := n) I :=
      (Subgroup.closure_le (TableBUE.blockSU (K := K) (n := n) I)).mpr
        (fun z hz => ((hGen_mem z).mp hz).1) hxA
    have hφmem : φ x ∈ (TableBUE.blockSU (K := K) (n := n) I).map φ :=
      Subgroup.mem_map.mpr ⟨x, hxblock, rfl⟩
    rw [← hJeq] at hφmem
    rw [Subgroup.mem_subgroupOf] at hφmem
    exact hφmem
  have hWN : W ⊆ Subgroup.normalizer (E₁ : Set M) := by
    rintro n ⟨σ, rfl⟩
    exact hN (permSU_lift_mem_normalizer_rowA (by omega) hpos hmodel hdiagE σ)
  refine ⟨S, W, hS_pg, hScent, hSJ, hWN, ?_⟩
  have hs4 := diag_pElt_mem_closure_permConj (hKd := hmodel.field) I hIcard' sp hspdiag hspP
  have hψsp : ψ sp = c := by
    change L'.subtype (φ sp) = c
    rw [hspEq]
    rfl
  have hmem : ψ sp ∈ Subgroup.closure (ψ '' (⋃ σ : Equiv.Perm (Fin d),
      (fun x => permSU hmodel.field σ * x * (permSU hmodel.field σ)⁻¹) '' Gen)) := by
    have h0 : ψ sp ∈ Subgroup.map ψ (Subgroup.closure (⋃ σ : Equiv.Perm (Fin d),
        (fun x => permSU hmodel.field σ * x * (permSU hmodel.field σ)⁻¹) '' Gen)) :=
      Subgroup.mem_map.mpr ⟨sp, hs4, rfl⟩
    rwa [MonoidHom.map_closure] at h0
  have hsubset : ψ '' (⋃ σ : Equiv.Perm (Fin d),
        (fun x => permSU hmodel.field σ * x * (permSU hmodel.field σ)⁻¹) '' Gen) ⊆
      ⋃ n ∈ W, (fun s : M => n * s * n⁻¹) '' (S : Set M) := by
    rintro y ⟨z, hz, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_image] at hz ⊢
    obtain ⟨σ, x, hxGen, rfl⟩ := hz
    refine ⟨ψ (permSU hmodel.field σ), ⟨σ, rfl⟩, ψ x, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨x, Subgroup.subset_closure hxGen, rfl⟩
    · rw [map_mul, map_mul, map_inv]
  rw [hψsp] at hmem
  exact Subgroup.closure_mono hsubset hmem

end CFSG.StandardType
