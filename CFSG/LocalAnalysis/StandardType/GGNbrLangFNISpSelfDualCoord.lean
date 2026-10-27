module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpPrimary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpSelfDualCoordAux
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpVecMap

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks

open Polynomial Module Matrix
open CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix

theorem kgfniSp_selfDualBlock_coord {K : Type} [Field K] [Fintype K] [CharP K 2] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (u : GL (Fin n ⊕ Fin n) K) (hu : u ∈ StatedSp n K) (hodd : Odd (orderOf u))
    (hup : u ^ p = 1)
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (heprim : IsPrimIdemIn (Algebra.adjoin K
      (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (h1 : (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    (hσu : Matrix.GeneralLinearGroup.map (σ : K →+* K) u = u) :
    ∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = Q ^ 2 ∧
      ∃ (eG : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε) ≃* ↥(GUFull m Q E))
        (B : GL (Fin m) E) (τ : E ≃+* E), B ∈ GUFull m Q E ∧ τ ≠ 1 ∧ Odd (orderOf τ) ∧
        ∀ g g' : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε),
          ((g' : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
              Matrix.GeneralLinearGroup.map (σ : K →+* K)
                ((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) →
            ((eG g' : GUFull m Q E) : GL (Fin m) E) =
              B * Matrix.GeneralLinearGroup.map τ.toRingHom ((eG g : GUFull m Q E) : GL (Fin m) E) *
                B⁻¹ := by
  classical
  haveI hKchar : CharP K 2 := ‹CharP K 2›
  let β : StatedSp n K := ⟨u, hu⟩
  have hoddβ : Odd (orderOf β) := by
    change Odd (orderOf (⟨u, hu⟩ : StatedSp n K))
    rw [Subgroup.orderOf_mk u hu]
    exact hodd
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  have hβp : β ^ p = 1 := by
    apply Subtype.ext
    exact hup
  have H : AltPrimaryData (spForm n K) (spLin n K β) := altPrimaryData_spLin hpK hβp
  obtain ⟨a, ha, hae'⟩ := ggJS2_exists_primaryProjection u hu hodd heprim
  have hrec : reciprocalPolynomial a = a :=
    ggJS2_reciprocal_of_selfDual u hu hodd hε ha hae'
  have haeAlg : Matrix.toLinAlgEquiv' ε = primaryProjection (spEnd β) a := by
    rw [← ggJS2_toLin'_eq_toLinAlgEquiv']
    exact hae'
  have hane1 : a ≠ X - 1 := by
    intro ha1
    apply h1
    have hxpa : (spEnd β : Module.End K (Fin n ⊕ Fin n → K)) *
        primaryProjection (spEnd β) a = primaryProjection (spEnd β) a := by
      apply LinearMap.ext
      intro v
      have hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd β) := ha1 ▸ ha
      have hv := primaryProjection_mem H.squarefree hX1 v
      rw [mem_primaryComponent_X_sub_one] at hv
      rw [ha1, Module.End.mul_apply]
      exact hv
    have hbε : (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε := by
      apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n ⊕ Fin n)).injective
      rw [map_mul, haeAlg]
      exact hxpa
    exact hbε
  have hsq2 : AdjoinRoot.root a ^ 2 ≠ 1 := by
    intro h2
    have hroot : AdjoinRoot.root a ^ orderOf β = 1 := by
      have hdvd : a ∣ (Polynomial.X ^ orderOf β - 1 : Polynomial K) := by
        refine (mem_primaryFactors.mp ha).2.2.trans ?_
        refine minpoly.dvd K (spEnd β) ?_
        rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
        change ((spLin n K β : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) ^ orderOf β = 1
        rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one β, map_one, Units.val_one]
      have h := AdjoinRoot.mk_eq_zero.mpr hdvd
      rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h
      exact h
    have hdvd2 : orderOf (AdjoinRoot.root a) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hdvdN : orderOf (AdjoinRoot.root a) ∣ orderOf β := orderOf_dvd_of_pow_eq_one hroot
    have hcop : Nat.Coprime 2 (orderOf β) := Nat.coprime_two_left.mpr hoddβ
    have hdvd1 : orderOf (AdjoinRoot.root a) ∣ 1 := by
      have h := Nat.dvd_gcd hdvd2 hdvdN
      rwa [hcop.gcd_eq_one] at h
    have hroot1 : AdjoinRoot.root a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
    have hdvdX : a ∣ (Polynomial.X - 1 : Polynomial K) := by
      apply AdjoinRoot.mk_eq_zero.mp
      rw [map_sub, AdjoinRoot.mk_X, map_one, hroot1, sub_self]
    exact hane1 (eq_of_monic_of_associated (monic_of_mem_primaryFactors ha)
      CFSG.RankThree.Classical.monic_X_sub_one
      ((irreducible_of_mem_primaryFactors ha).associated_of_dvd
        CFSG.RankThree.Classical.irreducible_X_sub_one hdvdX))
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have h0 : a.coeff 0 ≠ 0 := H.coeff_zero_ne ha
  obtain ⟨d, hd, hσd⟩ := exists_rootInv_eq_pow h0 hrec hsq2
  let E : Type := AdjoinRoot a
  let m : ℕ := Module.finrank E (primaryComponent (spEnd β) a)
  haveI : Finite E := Module.finite_of_finite K
  haveI : Fintype E := Fintype.ofFinite E
  have hcardE : Nat.card E = (Fintype.card K ^ d) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hd, Nat.card_eq_fintype_card, ← pow_mul]
    congr 1
    ring
  obtain ⟨ℓ, hchar, f, hℓprime, hKcard⟩ := FiniteField.card' (K := K)
  have hfpos : 0 < (f : ℕ) := f.pos
  have hd1 : 1 ≤ d := by
    have hpos : 0 < a.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors ha)
    rw [← CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot] at hpos
    omega
  have hE : UnitaryFieldData ℓ ((f : ℕ) * d) E := by
    refine ⟨hℓprime, Nat.mul_pos hfpos hd1, ?_⟩
    show Nat.card E = ℓ ^ (2 * ((f : ℕ) * d))
    rw [Module.natCard_eq_pow_finrank (K := K), hd, Nat.card_eq_fintype_card, hKcard,
      ← pow_mul]
    congr 1
    ring
  have hbar : ∀ z : E, hE.bar z = rootInv h0 hrec z := by
    intro z
    rw [UnitaryFieldData.bar_apply, hσd z, Nat.card_eq_fintype_card, hKcard, ← pow_mul]
  have hbarQ : ∀ z : E, hE.bar z = z ^ (Fintype.card K ^ d) := by
    intro z
    rw [hbar z, hσd z, Nat.card_eq_fintype_card]
  have hη0 : (1 : E) ≠ 0 := one_ne_zero
  have hηbar : hE.bar (1 : E) = -(1 : E) := by
    haveI : CharP E 2 :=
      @charP_of_injective_algebraMap K E _ _ _ (FaithfulSMul.algebraMap_injective K E) 2 hKchar
    rw [hbar, map_one]
    exact (CharTwo.neg_eq (1 : E)).symm
  have hsymm := H.altHermForm_isSymm ha hrec hE.bar hbar hηbar
  have hsep := H.altHermForm_separatingLeft ha hrec hE.bar hbar hη0
  obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hsymm hsep
  have hbG : ∀ i j : Fin m, H.altHermForm ha hrec hE.bar hbar (1 : E) (b i) (b j) =
      (idGram E m) i j := by
    intro i j
    rw [hb i j, idGram, Units.val_one, Matrix.one_apply]
  let S : (Fin n ⊕ Fin n → K) ≃+ (Fin n ⊕ Fin n → K) := vecMap σ
  have hS : ∀ (c : K) (v : Fin n ⊕ Fin n → K), S (c • v) = σ c • S v :=
    fun c v => vecMap_smul σ c v
  have hSx : ∀ v : Fin n ⊕ Fin n → K,
      S ((spLin n K β : Module.End K (Fin n ⊕ Fin n → K)) v) =
        (spLin n K β : Module.End K (Fin n ⊕ Fin n → K)) (S v) := by
    intro v
    exact vecMap_spEnd β hσu v
  have hsp : (spEnd β) ^ p = 1 := spEnd_pow hβp
  have haσ : a.map (σ : K →+* K) = a :=
    CFSG.StandardType.ClassicalBlocks.primaryFactors_map_eq_self_of_semilinear hp hpK hsp hσp
      S hS hSx a ha
  let T : primaryComponent (spEnd β) a ≃+ primaryComponent (spEnd β) a :=
    semilinRestrict (xe := LinearMap.GeneralLinearGroup.generalLinearEquiv K _ (spLin n K β))
      hS hSx haσ
  let tau : E ≃+* E := extAut a σ haσ
  have hTtau : ∀ (c : E) (v : primaryComponent (spEnd β) a), T (c • v) = tau c • T v :=
    semilinRestrict_smul (xe := LinearMap.GeneralLinearGroup.generalLinearEquiv K _ (spLin n K β))
      hS hSx haσ
  have hBT : ∀ u w : primaryComponent (spEnd β) a,
      spForm n K ((T u : primaryComponent (spEnd β) a) : Fin n ⊕ Fin n → K)
        ((T w : primaryComponent (spEnd β) a) : Fin n ⊕ Fin n → K) =
      σ (spForm n K (u : Fin n ⊕ Fin n → K) (w : Fin n ⊕ Fin n → K)) := by
    intro u w
    exact spForm_vecMap σ (u : Fin n ⊕ Fin n → K) (w : Fin n ⊕ Fin n → K)
  have hHsem : ∀ u w : primaryComponent (spEnd β) a,
      H.altHermForm ha hrec hE.bar hbar (1 : E) (T u) (T w) =
        tau (H.altHermForm ha hrec hE.bar hbar (1 : E) u w) := by
    have hτext : ∀ c : K, tau (algebraMap K E c) = algebraMap K E (σ c) := by
      intro c
      exact extAut_of haσ c
    intro u w
    exact kgfniSpSD_altHermForm_semilin H ha hrec hbar hτext hTtau hBT u w
  have hTorth : ∀ i j : Fin m,
      H.altHermForm ha hrec hE.bar hbar (1 : E) (T (b i)) (T (b j)) =
        if i = j then 1 else 0 := by
    intro i j
    rw [hHsem, hb i j]
    by_cases hij : i = j <;> simp [hij]
  have hBmat : ((semMat b T).map hE.bar)ᵀ * semMat b T = 1 :=
    semMat_unitary b hE hbG hTorth
  have hBmem : ((semMatUnit b T hTtau : GL (Fin m) E)) ∈
      GUFull m (Fintype.card K ^ d) E := by
    rw [ggJS2_GUFull_eq_primeFormUnitary hE hbarQ]
    rw [mem_primeFormUnitary]
    rw [coe_semMatUnit]
    simpa [idGram] using hBmat
  have hsub : glBlockCentralizer (StatedSp n K).subtype ({u} : Set (GL (Fin n ⊕ Fin n) K)) ε =
      CFSG.RankThree.Classical.spSupported β {a} := by
    exact @ggJS2_glBlockCentralizer_eq_spSupported K _ hKchar n u hu hodd ε a ha haeAlg
  have hL := supportedUnitary_le_sesq β {a}
  let e₁ : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε) ≃*
      ↥(spSupported β {a}) := MulEquiv.subgroupCongr hsub
  let e₂ : ↥(spSupported β {a}) ≃*
      ↥(supportedUnitary (spForm n K) (spLin n K β) {a}) :=
    comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β) {a}) hL
  let e₃ : ↥(supportedUnitary (spForm n K) (spLin n K β) {a}) ≃*
      ↥(sesqUnitaryGroup (H.altHermForm ha hrec hE.bar hbar (1 : E))) :=
    H.selfDualEquiv ha hrec hE.bar hbar hη0
  let e₄ : ↥(sesqUnitaryGroup (H.altHermForm ha hrec hE.bar hbar (1 : E))) ≃*
      ↥(primeFormUnitary hE (idGram E m)) :=
    sesqUnitaryGroupCoordinateEquiv hE b hbG
  let eG : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε) ≃*
      ↥(GUFull m (Fintype.card K ^ d) E) :=
    e₁.trans (e₂.trans (e₃.trans (e₄.trans
      (MulEquiv.subgroupCongr (ggJS2_GUFull_eq_primeFormUnitary hE hbarQ).symm))))
  have heG : ∀ g : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε),
      ((eG g : GUFull m (Fintype.card K ^ d) E) : GL (Fin m) E) =
        (Matrix.GeneralLinearGroup.toLin' b).symm
          (CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩ (e₂ (e₁ g))) := by
    intro g
    simp only [eG, e₁, e₂, e₃, e₄]
    conv_lhs =>
      change ((sesqUnitaryGroupCoordinateEquiv hE b hbG)
        ((H.selfDualEquiv ha hrec hE.bar hbar hη0)
          ((comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β) {a}) hL)
            ((MulEquiv.subgroupCongr hsub) g))) : GL (Fin m) E)
    rw [sesqUnitaryGroupCoordinateEquiv_apply]
    rfl
  have hsquare : ∀ g g' : ↥(glBlockCentralizer (StatedSp n K).subtype {u} ε),
      ((g' : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
          Matrix.GeneralLinearGroup.map (σ : K →+* K)
            ((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) →
      ((eG g' : GUFull m (Fintype.card K ^ d) E) : GL (Fin m) E) =
        semMatUnit b T hTtau *
          Matrix.GeneralLinearGroup.map tau.toRingHom
            ((eG g : GUFull m (Fintype.card K ^ d) E) : GL (Fin m) E) *
          (semMatUnit b T hTtau)⁻¹ := by
    intro g g' hgg
    have hpoint : ∀ v : Fin n ⊕ Fin n → K,
        ((g' : StatedSp n K) : GL (Fin n ⊕ Fin n) K) *ᵥ v =
          S (((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) *ᵥ (S.symm v)) := by
      intro v
      rw [hgg]
      exact map_mulVec_eq_vecMap σ ((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) v
    have hcoe_g : (((e₂ (e₁ g) : supportedUnitary (spForm n K) (spLin n K β) {a}) :
        LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
        Module.End K (Fin n ⊕ Fin n → K)) = spEnd (g : StatedSp n K) := by
      have h := coe_comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β) {a}) hL (e₁ g)
      change ((↑((comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β) {a}) hL) (e₁ g) :
          supportedUnitary (spForm n K) (spLin n K β) {a}) :
          LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) = spEnd (g : StatedSp n K)
      rw [h]
      rfl
    have hcoe_g' : (((e₂ (e₁ g') : supportedUnitary (spForm n K) (spLin n K β) {a}) :
        LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
        Module.End K (Fin n ⊕ Fin n → K)) = spEnd (g' : StatedSp n K) := by
      have h := coe_comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β) {a}) hL (e₁ g')
      change ((↑((comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β) {a}) hL) (e₁ g') :
          supportedUnitary (spForm n K) (spLin n K β) {a}) :
          LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) = spEnd (g' : StatedSp n K)
      rw [h]
      rfl
    have hggV : ∀ v : Fin n ⊕ Fin n → K,
        (((e₂ (e₁ g') : supportedUnitary (spForm n K) (spLin n K β) {a}) :
          LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) v =
        S ((((e₂ (e₁ g) : supportedUnitary (spForm n K) (spLin n K β) {a}) :
          LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) (S.symm v)) := by
      intro v
      rw [hcoe_g', hcoe_g]
      simpa [spEnd_apply] using hpoint v
    have hggT : ∀ w : primaryComponent (spEnd β) a,
        ((CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩
            (e₂ (e₁ g')) : Module.End (AdjoinRoot a)
              (primaryComponent (spEnd β) a)) w) =
          T ((CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩
            (e₂ (e₁ g)) : Module.End (AdjoinRoot a)
              (primaryComponent (spEnd β) a)) (T.symm w)) := by
      intro w
      apply Subtype.ext
      exact kgfniSpSD_blockRestrict_square H ha T (fun _ => rfl) (fun _ => rfl) hggV w
    have hcoord := toLin'_symm_conj_semilin (b := b) (S := T) (τ := tau) hTtau
      (CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩ (e₂ (e₁ g)))
      (CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩ (e₂ (e₁ g')))
      hggT
    rw [heG g', heG g]
    exact hcoord
  have hτne : tau ≠ 1 := by
    intro h
    exact hσ ((extAut_eq_one_iff (g := a) haσ).mp h)
  exact ⟨m, Fintype.card K ^ d, E, inferInstance, inferInstance,
    @charP_of_injective_algebraMap K E _ _ _ (FaithfulSMul.algebraMap_injective K E) 2 hKchar,
    hcardE,
    eG, semMatUnit b T hTtau, tau, hBmem, hτne, by
      have hτpow : tau ^ p = 1 := by
        ext z
        obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
        rw [kgfniSpSD_extAut_pow_apply haσ p q, hσp]
        change (AdjoinRoot.mk a) (Polynomial.map (RingHom.id K) q) =
          (AdjoinRoot.mk a) q
        rw [Polynomial.map_id]
      have hdvd : orderOf tau ∣ p := orderOf_dvd_of_pow_eq_one hτpow
      have hneq1 : orderOf tau ≠ 1 := by
        intro h
        exact hτne (orderOf_eq_one_iff.mp h)
      have hord : orderOf tau = p := by
        rcases (Nat.dvd_prime hp).mp hdvd with h | h
        · exact absurd h hneq1
        · exact h
      rw [hord]
      exact ⟨hp.odd_of_ne_two hp2, hsquare⟩⟩


end CFSG.StandardType

end
