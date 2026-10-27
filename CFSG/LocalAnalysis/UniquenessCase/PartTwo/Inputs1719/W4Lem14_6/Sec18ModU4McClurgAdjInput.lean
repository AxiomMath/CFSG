module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgPsi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgKlein
public import CFSG.HardMathSupport.U4FF.Omega2
public import CFSG.HardMathSupport.U4FF.ClassTmod
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.HardMathSupport.U4FF CFSG.LocalAnalysis.RankThreeUC CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
open CFSG.Open
open CFSG.RankThree.PartOne.CTP.SU4Even
open scoped Matrix MatrixGroups

noncomputable abbrev locR101 (k : Type*) [Field k] [CharP k 2] :
    SL(4, k) →* Matrix (Fin 14) (Fin 14) k :=
  locR true false true k

theorem exists_intertwiner_locR101 {E K : Type} [Field E]
    [Field K] [CharP K 2] [Algebra E K] {σ₀ : K ≃+* K} {b c : E} (D : KleinDataEven E K σ₀ b c)
    {k : Type} [Field k] [CharP k 2] (lam : K →+* k) :
    ∃ Q₀ : GL (Fin 14) k, ∀ (G : SL(4, k)) (A : Matrix Om6Idx Om6Idx E),
      (Tm D).map lam * (A.submatrix colEquiv colEquiv).map (lam.comp (algebraMap E K)) =
          compound2 (G : Matrix (Fin 4) (Fin 4) k) * (Tm D).map lam →
        (Q₀ : Matrix (Fin 14) (Fin 14) k) * locR101 k G =
          (adjMat E b A).map (lam.comp (algebraMap E K)) * (Q₀ : Matrix (Fin 14) (Fin 14) k) := by
  classical
  have h : LocValid1 true false true := (locValid true false true).1
  let Θ : (Fin 14 → k) → Matrix (Fin 6) (Fin 6) k := fun v => theta101 h k v
  have theta_add : ∀ v w : Fin 14 → k, Θ (v + w) = Θ v + Θ w :=
    fun v w => theta101_add h k v w
  have theta_smul : ∀ (s : k) (v : Fin 14 → k), Θ (s • v) = s • Θ v :=
    fun s v => theta101_smul h k s v
  have theta_transpose : ∀ v : Fin 14 → k, (Θ v)ᵀ = Θ v :=
    fun v => theta101_transpose h k v
  have theta_diag : ∀ (v : Fin 14 → k) (i : Fin 6), Θ v i i = 0 :=
    fun v i => theta101_diag h k v i
  have theta_f0 : ∀ v : Fin 14 → k, Θ v 0 5 + Θ v 1 4 + Θ v 2 3 = 0 :=
    fun v => theta101_f0 h k v
  have theta_thPos : ∀ (v : Fin 14 → k) (j : Fin 14),
      Θ v (thPos j).1 (thPos j).2 = v j :=
    fun v j => theta101_thPos h k v j
  set γ : E →+* k := lam.comp (algebraMap E K) with hγ
  set Tl : Matrix (Fin 6) (Fin 6) k := (Tm D).map lam with hTl
  set Tli : Matrix (Fin 6) (Fin 6) k := (TmInv D).map lam with hTli
  set re : Matrix (Fin 6) (Fin 6) k ≃+* Matrix Om6Idx Om6Idx k :=
    Matrix.reindexRingEquiv k colEquiv with hre
  have hTlTli : Tl * Tli = 1 := by
    rw [hTl, hTli, ← Matrix.map_mul, tm_mul_tmInv]
    exact Matrix.map_one lam (map_zero lam) (map_one lam)
  have hTliTl : Tli * Tl = 1 := by
    rw [hTl, hTli, ← Matrix.map_mul, tmInv_mul_tm]
    exact Matrix.map_one lam (map_zero lam) (map_one lam)
  have hTlie : Tliᵀ * Tlᵀ = 1 := by
    rw [← Matrix.transpose_mul, hTlTli, Matrix.transpose_one]
  have hre_apply : ∀ X : Matrix (Fin 6) (Fin 6) k,
      re X = X.submatrix colEquiv.symm colEquiv.symm := by
    intro X
    rw [hre]
    exact Matrix.reindex_apply colEquiv colEquiv X
  have hre_mul : ∀ X Y : Matrix (Fin 6) (Fin 6) k, re (X * Y) = re X * re Y :=
    fun X Y => map_mul re X Y
  have hre_trans : ∀ X : Matrix (Fin 6) (Fin 6) k, re Xᵀ = (re X)ᵀ := by
    intro X
    rw [hre_apply, hre_apply]
    ext i j
    simp [Matrix.transpose_apply, Matrix.submatrix_apply]
  have hreTlTli : re Tl * re Tli = 1 := by
    rw [← hre_mul, hTlTli, map_one]
  have hreTliTl : re Tli * re Tl = 1 := by
    rw [← hre_mul, hTliTl, map_one]
  let Z : (Fin 14 → k) → Matrix Om6Idx Om6Idx k := fun v =>
    re (Tli * Θ v * Tliᵀ)
  have hZmem : ∀ v : Fin 14 → k, Z v ∈ adjOmega6 k (γ b) := by
    intro v
    have hm := mem_adjOmega6_tmInv_conj D lam (Θ v) (theta_transpose v)
      (theta_diag v) (theta_f0 v)
    have hZeq : Z v = ((TmInv D).map lam * Θ v * ((TmInv D).map lam)ᵀ).submatrix
        colEquiv.symm colEquiv.symm := by
      rw [show Z v = re (Tli * Θ v * Tliᵀ) from rfl, hre_apply, hTli]
    rw [hZeq]
    exact hm
  have hZadd : ∀ v w : Fin 14 → k, Z (v + w) = Z v + Z w := by
    intro v w
    have h1 : Tli * Θ (v + w) * Tliᵀ =
        Tli * Θ v * Tliᵀ + Tli * Θ w * Tliᵀ := by
      rw [theta_add v w, Matrix.mul_add, Matrix.add_mul]
    dsimp only [Z]
    rw [h1, hre_apply, Matrix.submatrix_add, hre_apply, hre_apply]
    rfl
  have hZsmul : ∀ (s : k) (v : Fin 14 → k), Z (s • v) = s • Z v := by
    intro s v
    have h1 : Tli * Θ (s • v) * Tliᵀ = s • (Tli * Θ v * Tliᵀ) := by
      rw [theta_smul s v, Matrix.mul_smul, Matrix.smul_mul]
    dsimp only [Z]
    rw [h1, hre_apply, Matrix.submatrix_smul, hre_apply]
    rfl
  let Phi : (Fin 14 → k) →ₗ[k] (Fin 14 → k) :=
    { toFun := fun v => adjCoord (Z v)
      map_add' := by
        intro v w
        rw [hZadd]
        rfl
      map_smul' := by
        intro s v
        rw [hZsmul]
        rfl }
  have hsub : ∀ v : Fin 14 → k,
      (Z v).submatrix colEquiv colEquiv = Tli * Θ v * Tliᵀ := by
    intro v
    rw [show Z v = re (Tli * Θ v * Tliᵀ) from rfl, hre_apply,
      Matrix.submatrix_submatrix]
    simp [Equiv.symm_comp_self]
  have hlin : ∀ v : Fin 14 → k,
      Tl * (Tli * Θ v * Tliᵀ) * Tlᵀ = Θ v := by
    intro v
    calc Tl * (Tli * Θ v * Tliᵀ) * Tlᵀ
        = (Tl * Tli) * Θ v * (Tliᵀ * Tlᵀ) := by noncomm_ring
      _ = Θ v := by
          rw [hTlTli, hTlie, Matrix.one_mul, Matrix.mul_one]
  have hPhi_inj : Function.Injective Phi := by
    intro v w hvw
    change adjCoord (Z v) = adjCoord (Z w) at hvw
    have hZvw : Z v = Z w := by
      rw [← adjOfCoord_adjCoord (hZmem v), ← adjOfCoord_adjCoord (hZmem w), hvw]
    have hTheta : Θ v = Θ w := by
      have h1 : Tl * (Tli * Θ v * Tliᵀ) * Tlᵀ =
          Tl * (Tli * Θ w * Tliᵀ) * Tlᵀ := by
        rw [← hsub v, ← hsub w, hZvw]
      rwa [hlin v, hlin w] at h1
    funext j
    rw [← theta_thPos v j, ← theta_thPos w j, hTheta]
  have hinj : Function.Injective (fun v : Fin 14 → k => (LinearMap.toMatrix' Phi) *ᵥ v) := by
    intro v w hvw
    exact hPhi_inj (by simpa only [LinearMap.toMatrix'_mulVec] using hvw)
  have hunit : IsUnit (LinearMap.toMatrix' Phi) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  refine ⟨hunit.unit, ?_⟩
  intro G A hGA
  have hloc : ∀ v : Fin 14 → k, Θ (locR101 k G *ᵥ v) =
      compound2 (G : Matrix (Fin 4) (Fin 4) k) * Θ v *
        (compound2 (G : Matrix (Fin 4) (Fin 4) k))ᵀ := by
    intro v
    have hv := theta101_locMat h G v
    have e : locR101 k G = (locSpec true false true h).locMat k G := rfl
    rw [e]
    exact hv
  have hAM : A.map γ = re Tli * re (compound2 (G : Matrix (Fin 4) (Fin 4) k)) * re Tl := by
    have hGA0 : Tl * (A.submatrix colEquiv colEquiv).map γ =
        compound2 (G : Matrix (Fin 4) (Fin 4) k) * Tl := by
      simpa only [hγ] using hGA
    have hGA' : re (Tl * (A.submatrix colEquiv colEquiv).map γ) =
        re (compound2 (G : Matrix (Fin 4) (Fin 4) k) * Tl) := by
      rw [hGA0]
    simp only [hre_mul] at hGA'
    have hreAM : re ((A.submatrix colEquiv colEquiv).map γ) = A.map γ := by
      rw [hre_apply]
      ext i j
      simp [Matrix.submatrix_apply, Matrix.map_apply]
    rw [hreAM] at hGA'
    calc A.map γ = re Tli * (re Tl * A.map γ) := by
          rw [← Matrix.mul_assoc, hreTliTl, Matrix.one_mul]
      _ = re Tli * (re (compound2 (G : Matrix (Fin 4) (Fin 4) k)) * re Tl) := by rw [hGA']
      _ = re Tli * re (compound2 (G : Matrix (Fin 4) (Fin 4) k)) * re Tl := by
            rw [Matrix.mul_assoc]
  have hZv : ∀ v : Fin 14 → k, Z v = re Tli * re (Θ v) * (re Tli)ᵀ := by
    intro v
    dsimp only [Z]
    simp only [hre_mul, hre_trans]
  have hZlv : ∀ v : Fin 14 → k, Z (locR101 k G *ᵥ v) =
      re Tli * re (compound2 (G : Matrix (Fin 4) (Fin 4) k)) * re (Θ v) *
        (re (compound2 (G : Matrix (Fin 4) (Fin 4) k)))ᵀ * (re Tli)ᵀ := by
    intro v
    dsimp only [Z]
    rw [hloc v]
    rw [show Tli * (compound2 (G : Matrix (Fin 4) (Fin 4) k) * Θ v *
        (compound2 (G : Matrix (Fin 4) (Fin 4) k))ᵀ) * Tliᵀ =
        (Tli * compound2 (G : Matrix (Fin 4) (Fin 4) k)) * Θ v *
          ((compound2 (G : Matrix (Fin 4) (Fin 4) k))ᵀ * Tliᵀ) by noncomm_ring]
    simp only [hre_mul, hre_trans]
    noncomm_ring
  have hkey : ∀ v : Fin 14 → k,
      Phi (locR101 k G *ᵥ v) = (adjMat E b A).map γ *ᵥ Phi v := by
    intro v
    change adjCoord (Z (locR101 k G *ᵥ v)) = (adjMat E b A).map γ *ᵥ adjCoord (Z v)
    have hZ : Z (locR101 k G *ᵥ v) = A.map γ * Z v * (A.map γ)ᵀ := by
      rw [hZlv v, hZv v, hAM]
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      have h1 : re Tl * re Tli = 1 := hreTlTli
      have h2 : (re Tli)ᵀ * (re Tl)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
      calc re Tli * re (compound2 (G : Matrix (Fin 4) (Fin 4) k)) *
            re (Θ v) *
            (re (compound2 (G : Matrix (Fin 4) (Fin 4) k)))ᵀ * (re Tli)ᵀ
          = re Tli * re (compound2 (G : Matrix (Fin 4) (Fin 4) k)) *
              ((re Tl) * (re Tli)) * re (Θ v) *
              ((re Tli)ᵀ * (re Tl)ᵀ) *
              (re (compound2 (G : Matrix (Fin 4) (Fin 4) k)))ᵀ * (re Tli)ᵀ := by
            simp only [h1, h2, Matrix.mul_one, Matrix.one_mul]
        _ = (re Tli * re (compound2 (G : Matrix (Fin 4) (Fin 4) k)) * re Tl) *
              (re Tli * re (Θ v) * (re Tli)ᵀ) *
              ((re Tl)ᵀ * ((re (compound2 (G : Matrix (Fin 4) (Fin 4) k)))ᵀ *
                (re Tli)ᵀ)) := by
            noncomm_ring
    rw [hZ]
    rw [adjCoord_conj (A.map γ) (hZmem v)]
    rw [adjMat_map γ b A]
  have hmat : LinearMap.toMatrix' Phi * locR101 k G =
      (adjMat E b A).map γ * LinearMap.toMatrix' Phi := by
    ext p q
    have h := congrFun (hkey (Pi.single q 1)) p
    rw [← LinearMap.toMatrix'_mulVec Phi (locR101 k G *ᵥ Pi.single q 1),
      ← LinearMap.toMatrix'_mulVec Phi (Pi.single q 1)] at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
      Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    simpa only [Matrix.col_apply] using h
  rw [IsUnit.unit_spec hunit]
  exact hmat

theorem adjointOmega6_of_locR101
    (S : Type) [CommGroup S] (n : ℕ) (L : Subgroup (MulAut S)) (hL : IsU4Group n L)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
    (η : ↥L ≃* ↥(SU (unitaryInvolution K 2 n) 4))
    (E : Type) [Field E] [Finite E] (hE : Nat.card E = 2 ^ n)
    (ε : S ≃* Multiplicative (Fin 14 → E)) (R : ↥L →* GL (Fin 14) E)
    (hR : ∀ (l : ↥L) (s : S), ε ((l : MulAut S) s) =
      Multiplicative.ofAdd ((R l : Matrix (Fin 14) (Fin 14) E) *ᵥ Multiplicative.toAdd (ε s)))
    (k : Type) [Field k] [CharP k 2] [Algebra E k] [Algebra K k] (P : GL (Fin 14) k) (i₀ : ℕ)
    (hP : ∀ l : ↥L, (P : Matrix (Fin 14) (Fin 14) k) *
        (R l : Matrix (Fin 14) (Fin 14) E).map (algebraMap E k) =
      locR101 k (twistHom n (frobTw K k i₀) (η l)) * (P : Matrix (Fin 14) (Fin 14) k)) :
    AdjointOmega6 n L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := one_le_of_isU4Group hL
  haveI hEchar : CharP E 2 := by
    have h := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hn hE
    haveI := ringChar.charP E
    rwa [h] at this
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic E
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hE hK hirr
  letI : Algebra E K := inst
  let Φ : spinGroup (quadMinus 3 E b c) ≃* ↥(SU (unitaryInvolution K 2 n) 4) :=
    D.phiSUEven hK hirr
  have hperfSU : Group.IsPerfect ↥(SU (unitaryInvolution K 2 n) 4) :=
    (isQuasisimple_SU hK (by norm_num) (by simp)).1
  have hSpin : Group.IsPerfect (spinGroup (quadMinus 3 E b c)) :=
    Group.IsPerfect.ofSurjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective
  let Ω := spinMinusThreeEquiv hirr h2 hSpin
  let ξ : ↥L ≃* spinGroup (quadMinus 3 E b c) := η.trans Φ.symm
  let g : ↥L → Matrix (Fin 4) (Fin 4) K := fun l =>
    ((η l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hg : ∀ l, D.PhiMon (ξ l) = g l := fun l => by
    have h1 : Φ (ξ l) = η l := Φ.apply_symm_apply (η l)
    have h3 := congrArg (fun x : ↥(SU (unitaryInvolution K 2 n) 4) =>
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h1
    exact (D.coe_PhiSUEven hirr (ξ l)).symm.trans h3
  have hSU : ∀ l, D.PhiGL (ξ l) ∈ SU (unitaryInvolution K 2 n) 4 :=
    fun l => D.PhiGL_mem_SU hirr (ξ l)
  have hW : ∀ l, Tm D * ((spinMatrix (quadMinus 3 E b c) (ξ l) : Matrix VIdx VIdx E).submatrix
      colEquiv colEquiv).map (algebraMap E K) = comp2 (g l) * Tm D := fun l => by
    rw [← hg l]
    exact tm_mul_spin D (ξ l) (hSU l)
  let lam : K →+* k := frobTw K k i₀
  let β : E →+* k := algebraMap E k
  set γ : E →+* k := lam.comp (algebraMap E K) with hγ
  obtain ⟨Q₀, hQ₀⟩ := exists_intertwiner_locR101 D lam
  have hQ : ∀ l : ↥L, (Q₀ : Matrix (Fin 14) (Fin 14) k) *
      locR101 k (twistHom n lam (η l)) =
      (adjMat E b (spinMatrix (quadMinus 3 E b c) (ξ l))).map γ *
        (Q₀ : Matrix (Fin 14) (Fin 14) k) := by
    intro l
    refine hQ₀ (twistHom n lam (η l)) (spinMatrix (quadMinus 3 E b c) (ξ l)) ?_
    have hη : (g l).map lam = (twistHom n lam (η l) : Matrix (Fin 4) (Fin 4) k) := by
      rw [← twistHom_val]
    have hcomp : comp2 (g l) = compound2 (g l) := rfl
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) K => X.map lam) (hW l)
    rw [hcomp] at h
    simp only [Matrix.map_mul, Matrix.map_map, ← compound2_map] at h
    rw [hη] at h
    simpa only [hγ, RingHom.coe_comp] using h
  let Q : GL (Fin 14) k := Q₀ * P
  have hQ' : ∀ l, (Q : Matrix (Fin 14) (Fin 14) k) *
      (R l : Matrix (Fin 14) (Fin 14) E).map β =
      (adjMat E b (spinMatrix (quadMinus 3 E b c) (ξ l))).map γ *
        (Q : Matrix (Fin 14) (Fin 14) k) := by
    intro l
    have h1 : ((Q : GL (Fin 14) k) : Matrix (Fin 14) (Fin 14) k) =
        (Q₀ : Matrix (Fin 14) (Fin 14) k) * (P : Matrix (Fin 14) (Fin 14) k) := rfl
    rw [h1, Matrix.mul_assoc, hP l, ← Matrix.mul_assoc, hQ l, Matrix.mul_assoc]
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq β γ
  let Rθ : ↥L →* GL (Fin 14) E := (Matrix.GeneralLinearGroup.map (θ : E →+* E)).comp R
  have hRθ : ∀ l, ((Rθ l : GL (Fin 14) E) : Matrix (Fin 14) (Fin 14) E) =
      (R l : Matrix (Fin 14) (Fin 14) E).map θ := fun l => rfl
  let ρ₁₄ : ↥L →* GL (Fin 14) E := (adjMatHomOmega E b c).comp (ξ.trans Ω).toMonoidHom
  have hρ : ∀ l, ((ρ₁₄ l : GL (Fin 14) E) : Matrix (Fin 14) (Fin 14) E) =
      adjMat E b (spinMatrix (quadMinus 3 E b c) (ξ l)) := by
    intro l
    change adjMat E b ((((ξ.trans Ω) l : ↥(StatedOmega (StatedQuadMinus 3 E b c))) :
      GL Om6Idx E) : Matrix Om6Idx Om6Idx E) = _
    rw [show (ξ.trans Ω) l = Ω (ξ l) from rfl]
    rw [coe_spinMinusThreeEquiv]
  obtain ⟨M, hM⟩ := exists_conj_of_conj_extend γ Rθ ρ₁₄ Q (fun l => by
    have hβγ : (R l : Matrix (Fin 14) (Fin 14) E).map β =
        ((Rθ l : GL (Fin 14) E) : Matrix (Fin 14) (Fin 14) E).map γ := by
      rw [hRθ, Matrix.map_map]
      congr 1
      ext x
      exact hθ x
    rw [← hβγ, hQ' l, hρ l])
  obtain ⟨ψ, hψ⟩ := exists_coord_equiv (Equiv.refl (Fin 14)) ε R hR θ M ρ₁₄ (fun l => by
    have h := hM l
    rw [hRθ] at h
    simpa using h)
  let ψ' : S ≃* Multiplicative ↥(adjOmega6 E b) :=
    ψ.trans (adjCoordEquiv E b).symm.toMultiplicative
  refine ⟨E, inferInstance, inferInstance, b, c, hE, hirr, ξ.trans Ω, ψ', ?_⟩
  intro l u
  have hL : ((Multiplicative.toAdd (ψ' ((l : MulAut S) u)) : ↥(adjOmega6 E b)) :
      Matrix Om6Idx Om6Idx E) =
      adjOfCoord E b (Multiplicative.toAdd (ψ ((l : MulAut S) u))) := rfl
  have hR' : ((Multiplicative.toAdd (ψ' u) : ↥(adjOmega6 E b)) :
      Matrix Om6Idx Om6Idx E) = adjOfCoord E b (Multiplicative.toAdd (ψ u)) := rfl
  rw [hL, hR', hψ l u]
  set v : Fin 14 → E := Multiplicative.toAdd (ψ u) with hv
  set A : Matrix Om6Idx Om6Idx E :=
    ((((ξ.trans Ω) l : ↥(StatedOmega (StatedQuadMinus 3 E b c))) : GL Om6Idx E) :
      Matrix Om6Idx Om6Idx E) with hA
  have hAeq : A = spinMatrix (quadMinus 3 E b c) (ξ l) := by
    rw [hA]
    exact congrArg (fun g : GL Om6Idx E => ((g : Matrix Om6Idx Om6Idx E)))
      (coe_spinMinusThreeEquiv hirr h2 hSpin (ξ l))
  have hρl : ((ρ₁₄ l : GL (Fin 14) E) : Matrix (Fin 14) (Fin 14) E) = adjMat E b A := by
    rw [hρ l, ← hAeq]
  have hiso : ∀ x : Om6Idx → E,
      StatedQuadMinus 3 E b c (A *ᵥ x) = StatedQuadMinus 3 E b c x := by
    intro x
    rw [hA]
    exact CFSG.SeitzReduction.F4Pilot.statedOmega_le_omIsoGroup
      (StatedQuadMinus 3 E b c) (ξ.trans Ω l).2 x
  have hmem : A * adjOfCoord E b v * Aᵀ ∈ adjOmega6 E b :=
    mem_adjOmega6_conj hiso (adjOfCoord_mem E b v)
  rw [hρl]
  calc adjOfCoord E b (adjMat E b A *ᵥ v)
      = adjOfCoord E b (adjMat E b A *ᵥ adjCoord (adjOfCoord E b v)) := by
          rw [adjCoord_adjOfCoord]
    _ = adjOfCoord E b (adjCoord (A * adjOfCoord E b v * Aᵀ)) := by
          rw [adjCoord_conj A (adjOfCoord_mem E b v)]
    _ = A * adjOfCoord E b v * Aᵀ := adjOfCoord_adjCoord hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
