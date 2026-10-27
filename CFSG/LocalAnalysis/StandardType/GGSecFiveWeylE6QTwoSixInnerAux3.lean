module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixInnerAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType CFSG.StandardType.USixTwo
open CFSG.RankThree.PartOne
open USixTwo TorConj TorHomKernel MainProof TorHyperplanes
open Matrix
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G} {ω : K}

open CFSG.RankThree.PartOne in
theorem b_data (hK : Nat.card K = 4)
    {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (b : ↥Bs) :
    ∃ (β : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))
      (A : GL (Fin 6) K) (a : Fin 6 → Kˣ),
      A ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) ∧
      (∀ (h h' : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
        ((h' : GL (Fin 6) K)) = A * (h : GL (Fin 6) K) * A⁻¹ →
        β (LargeEvenProjMk _ h) = LargeEvenProjMk _ h') ∧
      (∀ l l' : L, (l' : G) = (b : G) * l * (b : G)⁻¹ →
        β (piOf (K := K) θ l) = piOf (K := K) θ l') ∧
      (∀ u ∈ USixTwo.torU K, β u = u) ∧
      ((A : Matrix (Fin 6) (Fin 6) K)).IsDiag ∧
      KFU.diagU a = A := by
  classical
  obtain ⟨β, hβ_mem, hβ_ind⟩ := hI (b : G)⁻¹ (Bs.inv_mem b.2)
  obtain ⟨A, hA_GU, hA_graph⟩ := hβ_mem
  have hβ_ind' : ∀ l l' : L, (l' : G) = (b : G) * l * (b : G)⁻¹ →
      β (piOf (K := K) θ l) = piOf (K := K) θ l' := by
    intro l l' hl'
    exact hβ_ind l l' (by simpa using hl')
  have hβfix : ∀ u ∈ USixTwo.torU K, β u = u := by
    intro u hu
    rw [← hmap] at hu
    obtain ⟨l, hl, hlπ⟩ := Subgroup.mem_map.mp hu
    have hlB : (l : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp hl).1
    have hcomm : (b : G) * (l : G) = (l : G) * (b : G) :=
      congrArg (fun z : ↥Bs => (z : G)) (hBs.1.is_comm.comm b ⟨(l : G), hlB⟩)
    have hbl : (b : G) * (l : G) * (b : G)⁻¹ = (l : G) := by
      rw [hcomm]; group
    rw [← hlπ]
    exact hβ_ind' l l (by rw [hbl])
  have hAdiag : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag := by
    apply USixTwo.isDiag_of_conj_torusSU_eq_smul hK
    intro d hd
    obtain ⟨v, hv3, hvprod, hdv⟩ := KFU.mem_torusSU_iff.mp hd
    have hdSU : d ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
      rw [← hdv, mem_SU_iff (USixTwo.fieldDataFour hK)]
      constructor
      · rw [KFU.det_diagU]
        simpa using congrArg (fun u : Kˣ => (u : K)) hvprod
      · have hbar : ⇑(USixTwo.fieldDataFour hK).bar = fun y : K => y ^ 2 :=
          funext (USixTwo.fieldDataFour_bar hK)
        rw [hbar, KFU.diagU_val]
        exact diagonal_map_transpose_mul_eq_one (fun k => (v k : K))
          (fun k => congrArg (fun u : Kˣ => (u : K)) (hv3 k))
    have hdtor : LargeEvenProjMk _ ⟨d, hdSU⟩ ∈ USixTwo.torU K := by
      refine Subgroup.mem_map.mpr ⟨⟨d, hdSU⟩, ?_, rfl⟩
      rw [USixTwo.torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
      show ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag
      rw [← hdv]
      exact KFU.isDiag_diagU v
    have hu : LargeEvenProjMk _ ⟨d, hdSU⟩ ∈
        ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) := by
      rw [hmap]; exact hdtor
    obtain ⟨l, hl, hlπ⟩ := Subgroup.mem_map.mp hu
    have hfixu : β (LargeEvenProjMk _ ⟨d, hdSU⟩) = LargeEvenProjMk _ ⟨d, hdSU⟩ := by
      rw [← hlπ]
      exact hβfix _ (by rw [← hmap]; exact Subgroup.mem_map_of_mem _ hl)
    have hmemAd : A * d * A⁻¹ ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
      have h := conj_mem_largeEvenSUGroup hK hA_GU hdSU
      simpa [mul_assoc] using h
    have hgraphd : β (LargeEvenProjMk _ ⟨d, hdSU⟩) =
        LargeEvenProjMk _ ⟨A * d * A⁻¹, hmemAd⟩ :=
      hA_graph ⟨d, hdSU⟩ ⟨A * d * A⁻¹, hmemAd⟩ rfl
    have hmkeq : LargeEvenProjMk _ ⟨A * d * A⁻¹, hmemAd⟩ =
        LargeEvenProjMk _ ⟨d, hdSU⟩ := by
      rw [← hgraphd, hfixu]
    obtain ⟨z, hzN, hzeq⟩ :=
      (QuotientGroup.mk'_eq_mk' ((LargeEvenScalars (Fin 6) K).subgroupOf
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).mp hmkeq
    have hzGL : ((z : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) ∈
        LargeEvenScalars (Fin 6) K := Subgroup.mem_subgroupOf.mp hzN
    obtain ⟨c, hc⟩ := hzGL
    refine ⟨(c : K)⁻¹, ?_⟩
    have h2 : ((A * d * A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin 6) c : Matrix (Fin 6) (Fin 6) K) =
        (d : Matrix (Fin 6) (Fin 6) K) := by
      have h2' : ((⟨A * d * A⁻¹, hmemAd⟩ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
            GL (Fin 6) K) * (z : GL (Fin 6) K) =
          ((⟨d, hdSU⟩ : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) := by
        rw [← Subgroup.coe_mul, hzeq]
      rw [← hc] at h2'
      have h2'' := congrArg (fun w : GL (Fin 6) K =>
        ((w : Matrix (Fin 6) (Fin 6) K))) h2'
      simpa only [Units.val_mul] using h2''
    have h3 : ((A * d * A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        (c : K)⁻¹ • (d : Matrix (Fin 6) (Fin 6) K) := by
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
      have hc0 : (c : K) ≠ 0 := Units.ne_zero c
      ext i j
      have h := congrFun (congrFun h2 i) j
      rw [Matrix.mul_diagonal] at h
      simp only [Matrix.smul_apply, smul_eq_mul]
      calc ((A * d * A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j
          = (((A * d * A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j *
              (c : K)) * (c : K)⁻¹ := by field_simp
        _ = (d : Matrix (Fin 6) (Fin 6) K) i j * (c : K)⁻¹ := by rw [h]
        _ = (c : K)⁻¹ * (d : Matrix (Fin 6) (Fin 6) K) i j := mul_comm _ _
    exact h3
  obtain ⟨a, ha⟩ := KFU.exists_diagU_of_isDiag hAdiag
  exact ⟨β, A, a, hA_GU, hA_graph, hβ_ind', hβfix, hAdiag, ha⟩

theorem exists_pow_omega (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {c : Kˣ} (hc : c ^ 3 = 1) :
    ∃ k : ℕ, (Units.mk0 ω (by
      intro h; rw [h] at hω; norm_num at hω)) ^ k = c := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  letI : IsCyclic Kˣ := inferInstance
  let ωu : Kˣ := Units.mk0 ω (by intro h; rw [h] at hω; norm_num at hω)
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hω3 : ωu ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    show (ωu : K) ^ 3 = 1
    rw [show (ωu : K) = ω from rfl]
    linear_combination (ω - 1) * hω
  have hωne : ωu ≠ 1 := by
    intro h
    have h1 : (ωu : K) = 1 := congrArg Units.val h
    rw [show (ωu : K) = ω from rfl] at h1
    rw [h1] at hω
    have h3 : (3 : K) = 0 := by linear_combination hω
    have h2 : (2 : K) = 0 := USixTwo.two_eq_zero hK
    have h1' : (1 : K) = 0 := by linear_combination h3 - h2
    exact one_ne_zero h1'
  have hord : orderOf ωu = 3 := orderOf_eq_prime hω3 hωne
  have htop : Subgroup.zpowers ωu = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top, hcard, Nat.card_zpowers, hord]
  have hmem : c ∈ Subgroup.zpowers ωu := by rw [htop]; exact Subgroup.mem_top c
  have hfin : IsOfFinOrder ωu := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hω3⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hord] at hmem
  obtain ⟨k, hk, hkc⟩ := Finset.mem_image.mp hmem
  exact ⟨k, hkc⟩

theorem pi_delta (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs)
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {n : ↥L} (hn : piOf (K := K) θ n = Psigma hK (Equiv.swap 0 1))
    (b : ↥Bs) :
    ∃ k : ℕ, piOf (K := K) θ (deltaElem hNL n b) = (USixTwo.threeA hω) ^ k := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨β, A, a, hA_GU, hA_graph, hβ_ind, hβfix, hAdiag, hAeq⟩ :=
    b_data hK θ hmap hBs hI b
  let σ : Equiv.Perm (Fin 6) := Equiv.swap 0 1
  let P : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := permGLSU hK σ
  have hPcoe : ((P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Equiv.Perm.permMatrix K σ⁻¹ := by
    rw [show (P : GL (Fin 6) K) = TauCeti.permutationGL σ from coe_permGLSU hK σ,
      TauCeti.permutationGL_coe]
  have hPdiag : ∀ d : Fin 6 → Kˣ, (P : GL (Fin 6) K) * TauCeti.diagGL d =
      TauCeti.diagGL (fun i => d (σ.symm i)) * (P : GL (Fin 6) K) :=
    fun d => TauCeti.mul_diagGL_of_coe_eq_permMatrix (P : GL (Fin 6) K) σ⁻¹ hPcoe d
  have hdiagU_gl : ∀ d : Fin 6 → Kˣ, (KFU.diagU d : GL (Fin 6) K) = TauCeti.diagGL d := by
    intro d; apply Units.ext; rw [KFU.diagU_val, TauCeti.diagGL_coe]
  have hzmat : A⁻¹ * ((P : GL (Fin 6) K) * A * (P : GL (Fin 6) K)⁻¹) =
      KFU.diagU (fun i => (a i)⁻¹ * a (σ.symm i)) := by
    have hAinv : A⁻¹ = KFU.diagU (a⁻¹) := by
      rw [← hAeq, hdiagU_gl a, hdiagU_gl (a⁻¹)]
      exact (map_inv TauCeti.diagGL a).symm
    have h1 : (P : GL (Fin 6) K) * A * (P : GL (Fin 6) K)⁻¹ =
        KFU.diagU (fun i => a (σ.symm i)) := by
      rw [← hAeq, hdiagU_gl a, hPdiag]
      rw [mul_assoc, mul_inv_cancel, mul_one]
      exact (hdiagU_gl _).symm
    rw [hAinv, h1, hdiagU_gl (a⁻¹), hdiagU_gl (fun i => a (σ.symm i)),
      hdiagU_gl (fun i => (a i)⁻¹ * a (σ.symm i)), ← map_mul]
    congr 1
  let cvec : Fin 6 → Kˣ := fun i => (a i)⁻¹ * a (σ.symm i)
  have hcube : ∀ i, cvec i ^ 3 = 1 := by
    intro i
    rw [show cvec i = (a i)⁻¹ * a (σ.symm i) from rfl, mul_pow, inv_pow,
      USixTwo.cube_unit_eq_one hK, USixTwo.cube_unit_eq_one hK]
    simp
  have hprod : ∏ i, cvec i = 1 := by
    show ∏ i, (a i)⁻¹ * a (σ.symm i) = 1
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      Equiv.prod_comp σ.symm (fun i => a i), inv_mul_cancel]
  have hzSU : KFU.diagU cvec ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
    show KFU.diagU (fun i => (a i)⁻¹ * a (σ.symm i)) ∈ _
    rw [mem_SU_iff (USixTwo.fieldDataFour hK)]
    constructor
    · rw [KFU.det_diagU]
      have hval : ((∏ i, cvec i : Kˣ) : K) = ∏ i, ((cvec i : Kˣ) : K) := by
        simpa using (map_prod (Units.coeHom K) (fun i => cvec i) Finset.univ)
      rw [← hval, hprod, Units.val_one]
    · have hbar : ⇑(USixTwo.fieldDataFour hK).bar = fun y : K => y ^ 2 :=
        funext (USixTwo.fieldDataFour_bar hK)
      rw [hbar, KFU.diagU_val]
      exact diagonal_map_transpose_mul_eq_one (fun i => ((cvec i : Kˣ) : K))
        (fun i => congrArg (fun u : Kˣ => (u : K)) (hcube i))
  let M : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  have hMP : M P = Psigma hK σ := rfl
  have hnP : piOf (K := K) θ n = M P := by rw [hn]; rfl
  have hconj1 : MulAut.conj (piOf (K := K) θ (deltaElem hNL n b)) =
      β⁻¹ * MulAut.conj (piOf (K := K) θ n) * β *
        (MulAut.conj (piOf (K := K) θ n))⁻¹ := by
    apply MulEquiv.ext
    intro u
    obtain ⟨l, rfl⟩ := piOf_surjective θ u
    let x1 : ↥L := n⁻¹ * l * n
    let y1 : ↥L := conjBL hNL b x1
    let x2 : ↥L := n * y1 * n⁻¹
    have hx1 : (MulAut.conj (piOf (K := K) θ n))⁻¹ (piOf (K := K) θ l) =
        piOf (K := K) θ x1 := by
      rw [MulAut.conj_inv_apply]
      show (piOf (K := K) θ n)⁻¹ * piOf (K := K) θ l * piOf (K := K) θ n =
        piOf (K := K) θ (n⁻¹ * l * n)
      rw [← map_inv, ← map_mul, ← map_mul]
    have hy1 : β (piOf (K := K) θ x1) = piOf (K := K) θ y1 :=
      hβ_ind x1 y1 rfl
    have hx2 : (MulAut.conj (piOf (K := K) θ n)) (piOf (K := K) θ y1) =
        piOf (K := K) θ x2 := by
      rw [MulAut.conj_apply]
      show piOf (K := K) θ n * piOf (K := K) θ y1 * (piOf (K := K) θ n)⁻¹ =
        piOf (K := K) θ (n * y1 * n⁻¹)
      rw [← map_inv, ← map_mul, ← map_mul]
    have hx2' : (x2 : G) = (b : G) *
        ((deltaElem hNL n b * l * (deltaElem hNL n b)⁻¹ : ↥L) : G) * (b : G)⁻¹ := by
      simp only [x2, y1, x1, conjBL, deltaElem, conjBLinv, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    have h4 : β (piOf (K := K) θ (deltaElem hNL n b * l * (deltaElem hNL n b)⁻¹)) =
        piOf (K := K) θ x2 := hβ_ind _ x2 hx2'
    have h5 : β⁻¹ (piOf (K := K) θ x2) =
        piOf (K := K) θ (deltaElem hNL n b * l * (deltaElem hNL n b)⁻¹) := by
      rw [← h4, MulAut.inv_apply_self]
    rw [MulAut.conj_apply]
    rw [show (piOf (K := K) θ (deltaElem hNL n b) * piOf (K := K) θ l *
          (piOf (K := K) θ (deltaElem hNL n b))⁻¹) =
        piOf (K := K) θ (deltaElem hNL n b * l * (deltaElem hNL n b)⁻¹) from by
      rw [← map_mul, ← map_inv, ← map_mul]]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hx1, hy1, hx2, h5]
  have hconj2 : β⁻¹ * MulAut.conj (piOf (K := K) θ n) * β *
      (MulAut.conj (piOf (K := K) θ n))⁻¹ =
      MulAut.conj (M ⟨KFU.diagU cvec, hzSU⟩) := by
    apply MulEquiv.ext
    intro u
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) u
    have hmemPinv : (P : GL (Fin 6) K)⁻¹ ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
      simpa using (LargeEvenSUGroup (Fin 6) K (2 ^ 1)).inv_mem P.2
    have hmem1 : (P : GL (Fin 6) K)⁻¹ * (h : GL (Fin 6) K) * (P : GL (Fin 6) K) ∈
        LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
      have hh := conj_mem_largeEvenSUGroup hK
        (mem_largeEvenGUSet_of_mem_SU hK hmemPinv) h.2
      simpa using hh
    let h1 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      ⟨(P : GL (Fin 6) K)⁻¹ * (h : GL (Fin 6) K) * (P : GL (Fin 6) K), hmem1⟩
    have hmem2 : A * (h1 : GL (Fin 6) K) * A⁻¹ ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
      have hh := conj_mem_largeEvenSUGroup hK hA_GU h1.2
      simpa using hh
    let h2 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      ⟨A * (h1 : GL (Fin 6) K) * A⁻¹, hmem2⟩
    have hmem3 : (P : GL (Fin 6) K) * (h2 : GL (Fin 6) K) * (P : GL (Fin 6) K)⁻¹ ∈
        LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
      have hh := conj_mem_largeEvenSUGroup hK
        (mem_largeEvenGUSet_of_mem_SU hK P.2) h2.2
      simpa using hh
    let h3 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      ⟨(P : GL (Fin 6) K) * (h2 : GL (Fin 6) K) * (P : GL (Fin 6) K)⁻¹, hmem3⟩
    have hdiagU_GU : ∀ d : Fin 6 → Kˣ,
        (KFU.diagU d : GL (Fin 6) K) ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) := by
      intro d
      rw [mem_largeEvenGUSet_iff hK]
      have hbar : ⇑(USixTwo.fieldDataFour hK).bar = fun y : K => y ^ 2 :=
        funext (USixTwo.fieldDataFour_bar hK)
      rw [show (KFU.diagU d : GL (Fin 6) K) = TauCeti.diagGL d from hdiagU_gl d,
        TauCeti.diagGL_coe]
      exact diagonal_map_transpose_mul_eq_one (fun i => (d i : K))
        (fun i => congrArg (fun u : Kˣ => (u : K)) (USixTwo.cube_unit_eq_one hK (d i)))
    have hmem4 : A⁻¹ * (h3 : GL (Fin 6) K) * A ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
      have hAinvGU : A⁻¹ ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) := by
        rw [← hAeq, hdiagU_gl a, ← map_inv, ← hdiagU_gl (a⁻¹)]
        exact hdiagU_GU (a⁻¹)
      have hh := conj_mem_largeEvenSUGroup hK hAinvGU h3.2
      simpa using hh
    let h4 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      ⟨A⁻¹ * (h3 : GL (Fin 6) K) * A, hmem4⟩
    have hβh1 : β (M h1) = M h2 := hA_graph h1 h2 rfl
    have hconjinv : (MulAut.conj (M P))⁻¹ (M h) = M h1 := by
      rw [MulAut.conj_inv_apply]
      show (M P)⁻¹ * M h * M P = M h1
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    have hconj3 : (MulAut.conj (M P)) (M h2) = M h3 := by
      rw [MulAut.conj_apply]
      show M P * M h2 * (M P)⁻¹ = M h3
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    have hβinv4 : β (M h4) = M h3 := by
      have hh : (h3 : GL (Fin 6) K) = A * (h4 : GL (Fin 6) K) * A⁻¹ := by
        simp only [h4, h3, Subgroup.coe_mk]
        group
      exact hA_graph h4 h3 hh
    have h4eq : (h4 : GL (Fin 6) K) = KFU.diagU cvec * (h : GL (Fin 6) K) *
        (KFU.diagU cvec)⁻¹ := by
      simp only [h4, h3, h2, h1, Subgroup.coe_mk]
      rw [show KFU.diagU cvec = A⁻¹ * ((P : GL (Fin 6) K) * A * (P : GL (Fin 6) K)⁻¹)
        from hzmat.symm]
      group
    rw [hnP, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hconjinv, hβh1, hconj3]
    rw [show β⁻¹ (M h3) = M h4 from by rw [← hβinv4, MulAut.inv_apply_self]]
    rw [MulAut.conj_apply]
    rw [show M ⟨KFU.diagU cvec, hzSU⟩ * M h * (M ⟨KFU.diagU cvec, hzSU⟩)⁻¹ = M h4 from by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact h4eq.symm]
  have hcenter : Subgroup.center
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = ⊥ := by
    have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
    exact CFSG.StandardType.TableBUE.center_proj_eq_bot hK' (by norm_num) (by norm_num)
  have hδz : piOf (K := K) θ (deltaElem hNL n b) = M ⟨KFU.diagU cvec, hzSU⟩ := by
    apply conj_injective_of_center_eq_bot hcenter
    rw [hconj1, hconj2]
  obtain ⟨k, hk⟩ := exists_pow_omega hK hω (c := cvec 0)
    (by simpa using hcube 0)
  refine ⟨k, ?_⟩
  let ωu : Kˣ := Units.mk0 ω (by intro h; rw [h] at hω; norm_num at hω)
  let vecU : Fin 6 → Kˣ := ![ωu, ωu ^ 2, 1, 1, 1, 1]
  have hωu_val : (ωu : K) = ω := rfl
  have hωu3 : ωu ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    show (ωu : K) ^ 3 = 1
    rw [show (ωu : K) = ω from rfl]
    linear_combination (ω - 1) * hω
  have hk' : ωu ^ k = cvec 0 := hk
  have hce0 : cvec 0 = (a 0)⁻¹ * a 1 := by
    show (a 0)⁻¹ * a (σ.symm 0) = (a 0)⁻¹ * a 1
    rw [show σ.symm 0 = (1 : Fin 6) from by decide]
  have hce1 : cvec 1 = (a 1)⁻¹ * a 0 := by
    show (a 1)⁻¹ * a (σ.symm 1) = (a 1)⁻¹ * a 0
    rw [show σ.symm 1 = (0 : Fin 6) from by decide]
  have hx3 : (ωu ^ k) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm k 3, pow_mul, hωu3, one_pow]
  have hx2 : (ωu ^ k) ^ 2 = (ωu ^ k)⁻¹ := by
    calc (ωu ^ k) ^ 2 = (ωu ^ k) ^ 2 * ((ωu ^ k) * (ωu ^ k)⁻¹) := by
          rw [mul_inv_cancel, mul_one]
      _ = (ωu ^ k) ^ 3 * (ωu ^ k)⁻¹ := by group
      _ = (ωu ^ k)⁻¹ := by rw [hx3, one_mul]
  have hcvec_eq : cvec = vecU ^ k := by
    funext i
    fin_cases i
    · show cvec 0 = (vecU ^ k) 0
      rw [Pi.pow_apply, show vecU 0 = ωu from rfl, ← hk']
    · show cvec 1 = (vecU ^ k) 1
      rw [Pi.pow_apply, show vecU 1 = ωu ^ 2 from rfl]
      have h1 : cvec 1 = (ωu ^ k)⁻¹ := by
        rw [hce1]
        have hk'' : ωu ^ k = (a 0)⁻¹ * a 1 := hk'.trans hce0
        rw [hk'']
        group
      rw [h1, ← pow_mul, Nat.mul_comm 2 k, pow_mul, hx2]
    · show cvec 2 = (vecU ^ k) 2
      rw [Pi.pow_apply, show vecU 2 = 1 from rfl, one_pow]
      show (a 2)⁻¹ * a (σ.symm 2) = 1
      rw [show σ.symm 2 = (2 : Fin 6) from by decide]
      group
    · show cvec 3 = (vecU ^ k) 3
      rw [Pi.pow_apply, show vecU 3 = 1 from rfl, one_pow]
      show (a 3)⁻¹ * a (σ.symm 3) = 1
      rw [show σ.symm 3 = (3 : Fin 6) from by decide]
      group
    · show cvec 4 = (vecU ^ k) 4
      rw [Pi.pow_apply, show vecU 4 = 1 from rfl, one_pow]
      show (a 4)⁻¹ * a (σ.symm 4) = 1
      rw [show σ.symm 4 = (4 : Fin 6) from by decide]
      group
    · show cvec 5 = (vecU ^ k) 5
      rw [Pi.pow_apply, show vecU 5 = 1 from rfl, one_pow]
      show (a 5)⁻¹ * a (σ.symm 5) = 1
      rw [show σ.symm 5 = (5 : Fin 6) from by decide]
      group
  have h3A : ((threeASU hω : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) =
      TauCeti.diagGL vecU := by
    apply Units.ext
    rw [coe_threeASU, TauCeti.diagGL_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [threeAMatrix, vecU, ωu, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]
  have hthreeASU_pow : ((⟨KFU.diagU cvec, hzSU⟩ :
      ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) = (threeASU hω) ^ k := by
    apply Subtype.ext
    change (KFU.diagU cvec : GL (Fin 6) K) =
      ((threeASU hω : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) ^ k
    rw [hdiagU_gl cvec, h3A, ← map_pow, hcvec_eq]
  calc piOf (K := K) θ (deltaElem hNL n b) = M ⟨KFU.diagU cvec, hzSU⟩ := hδz
    _ = M ((threeASU hω) ^ k) := by rw [hthreeASU_pow]
    _ = (M (threeASU hω)) ^ k := by rw [map_pow]
    _ = (USixTwo.threeA hω) ^ k := rfl

end CFSG.StandardType.E6QTwo

end
