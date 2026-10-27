module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.HardMathSupport.U4FF.Disp
import CFSG.HardMathSupport.U4FF.ClassRankF2
public import CFSG.HardMathSupport.U4FF.ClassTmodIrr
import CFSG.HardMathSupport.U4FF.ClassClassifHolds
import CFSG.HardMathSupport.U4FF.ClassFinalRep

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.HardMathSupport.U4FF
open CFSG.QuasithinUnique.Setup.Family

private lemma w183_mapCoeffs_repr {R R' M ι : Type*} [Semiring R] [Semiring R']
    [AddCommMonoid M] [Module R M] [Module R' M] (f : R ≃+* R') (b : Module.Basis ι R M)
    (h : ∀ c x, f c • x = c • x) (w : M) (i : ι) :
    (b.mapCoeffs f h).repr w i = f (b.repr w i) := by
  simp only [Module.Basis.mapCoeffs, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply]
  rfl

private lemma w183_toMatrix_mapCoeffs {R R' M ι : Type*} [Field R] [Field R']
    [AddCommGroup M] [Fintype ι] [DecidableEq ι] [Module R M] [Module R' M]
    (f : R ≃+* R') (b : Module.Basis ι R M) (h : ∀ c x, f c • x = c • x)
    (T : M →ₗ[R'] M) (T' : M →ₗ[R] M) (hT : ∀ w, T w = T' w) :
    LinearMap.toMatrix (b.mapCoeffs f h) (b.mapCoeffs f h) T =
      (LinearMap.toMatrix b b T').map f := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
  rw [hT, w183_mapCoeffs_repr, Module.Basis.mapCoeffs_apply]

private lemma w183_toMatrix_reindex {R M ι ι' : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι R M) (e : ι ≃ ι') (T : M →ₗ[R] M) :
    LinearMap.toMatrix (b.reindex e) (b.reindex e) T = (LinearMap.toMatrix b b T).reindex e e := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]

private lemma w183_u4_numerics {d : ℕ} (hd1 : 1 ≤ d) (l : Lbl 1) (hl0 : ¬ l.IsZero)
    (hdim : d * l.dim = 14) : d = 1 ∧ l = finU4Label := by
  have hldim : l.dim = locM (l.a 0) (l.b 0) (l.c 0) := by
    simp [Lbl.dim]
  have hdvd : locM (l.a 0) (l.b 0) (l.c 0) ∣ 14 :=
    ⟨d, by rw [mul_comm, ← hldim, hdim]⟩
  have htriple : l.a 0 = true ∧ l.b 0 = false ∧ l.c 0 = true := by
    rcases ha : l.a 0 with _ | _ <;> rcases hb : l.b 0 with _ | _ <;>
      rcases hc : l.c 0 with _ | _ <;>
      simp only [ha, hb, hc, locM] at hdvd ⊢
    · exfalso; exact hl0 (fun i => by fin_cases i; exact ⟨ha, hb, hc⟩)
    · exfalso; revert hdvd; norm_num
    · exfalso; revert hdvd; norm_num
    · exfalso; revert hdvd; norm_num
    · exfalso; revert hdvd; norm_num
    · exact ⟨trivial, trivial, trivial⟩
    · exfalso; revert hdvd; norm_num
    · exfalso; revert hdvd; norm_num
  have hldim14 : l.dim = 14 := by
    rw [hldim, htriple.1, htriple.2.1, htriple.2.2]
    rfl
  have hd : d = 1 := by
    rw [hldim14] at hdim
    omega
  refine ⟨hd, ?_⟩
  obtain ⟨ha, hb, hc⟩ := htriple
  cases l with
  | mk a b c =>
    have ha' : a = fun _ => true := by funext i; fin_cases i; exact ha
    have hb' : b = fun _ => false := by funext i; fin_cases i; exact hb
    have hc' : c = fun _ => true := by funext i; fin_cases i; exact hc
    rw [ha', hb', hc']
    rfl

private lemma w183_conj_involution {E V W : Type*} [Field E]
    [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]
    (Φl : W →ₗ[E] V) (Φs : V →ₗ[E] W) (B : V →ₗ[E] V)
    (h1 : ∀ u : V, Φl (Φs u) = u) (h2 : ∀ v : W, Φs (Φl v) = v)
    (hB : B.comp B = 1) :
    (Φs.comp (B.comp Φl)) * (Φs.comp (B.comp Φl)) = 1 := by
  apply LinearMap.ext
  intro v
  show Φs (B (Φl (Φs (B (Φl v))))) = v
  rw [h1 (B (Φl v))]
  have hBv : B (B (Φl v)) = Φl v := by
    have h := LinearMap.congr_fun hB (Φl v)
    simpa [Module.End.mul_eq_comp] using h
  rw [hBv, h2 v]

private lemma w183_natCard_ker_matrix {F : Type} [Field F] [Finite F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    Nat.card {y : Fin n → F // A.mulVec y = 0} = Nat.card F ^ (n - A.rank) := by
  have hiff : ∀ y : Fin n → F, (A + 1).mulVec y = y ↔ A.mulVec y = 0 := by
    intro y
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    constructor
    · intro h
      exact add_right_cancel (show A.mulVec y + y = 0 + y by rw [h, zero_add])
    · intro h
      rw [h, zero_add]
  rw [← Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  have h := CFSG.HardMathSupport.U4FF.ClassFinal.natCard_fixed_matrix (A + 1)
  rw [show (A + 1 - 1 : Matrix (Fin n) (Fin n) F) = A from by ext i j; simp] at h
  simpa using h

theorem finU4_rank_map_zmod_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 2)) {E : Type} [Field E] [Finite E] [CharP E 2] :
    (M.map (ZMod.castHom (dvd_refl 2) E)).rank = M.rank := by
  classical
  let f : ZMod 2 →+* E := ZMod.castHom (dvd_refl 2) E
  letI : Algebra (ZMod 2) E := f.toAlgebra
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let M' : Matrix (Fin n) (Fin n) (ZMod 2) := M.reindex e e
  have hmap : (M.map f).reindex e e = M'.map f := rfl
  have hM' : (M'.map f).rank = (M.map f).rank := by
    rw [← hmap, Matrix.rank_reindex]
  have hM : M'.rank = M.rank := Matrix.rank_reindex e e M
  rw [← hM', ← hM]
  let k := Module.finrank (ZMod 2) E
  have hkpos : 0 < k := by
    have : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    exact Module.finrank_pos
  have hD := w183_natCard_ker_matrix M'
  have hE := w183_natCard_ker_matrix (M'.map f)
  have hbc := CFSG.QuasithinUnique.Setup.SL2Modules.natCard_common_ker_map
    (D := ZMod 2) (E := E) f (fun _ : Unit => M')
  simp only [forall_const] at hbc
  have hEcard : Nat.card E = Nat.card (ZMod 2) ^ k :=
    CFSG.QuasithinUnique.Setup.SL2Modules.natCard_E_eq f
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have key : Nat.card (ZMod 2) ^ (k * (n - (M'.map f).rank)) =
      Nat.card (ZMod 2) ^ (k * (n - M'.rank)) := by
    calc Nat.card (ZMod 2) ^ (k * (n - (M'.map f).rank))
        = (Nat.card (ZMod 2) ^ k) ^ (n - (M'.map f).rank) := by rw [pow_mul]
      _ = (Nat.card E) ^ (n - (M'.map f).rank) := by rw [hEcard]
      _ = Nat.card {x : Fin n → E // (M'.map f).mulVec x = 0} := hE.symm
      _ = Nat.card {x : Fin n → ZMod 2 // M'.mulVec x = 0} ^ k := hbc
      _ = (Nat.card (ZMod 2) ^ (n - M'.rank)) ^ k := by rw [hD]
      _ = Nat.card (ZMod 2) ^ ((n - M'.rank) * k) := by rw [pow_mul]
      _ = Nat.card (ZMod 2) ^ (k * (n - M'.rank)) := by rw [mul_comm]
  have hexp : k * (n - (M'.map f).rank) = k * (n - M'.rank) :=
    Nat.pow_right_injective (by rw [h2]) key
  have hcancel : n - (M'.map f).rank = n - M'.rank := Nat.mul_left_cancel hkpos hexp
  have hleE : (M'.map f).rank ≤ n := by
    simpa using (M'.map f).rank_le_card_height
  have hle : M'.rank ≤ n := by
    simpa using M'.rank_le_card_height
  omega

theorem finU4_fourteen_normalizer_matrix
    {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)]
    {L : Subgroup (MulAut S)} (hL : IsU4Group 1 L) (hirr : IsIrrOn L) (hS : Nat.card S = 2 ^ 14)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (η : ↥L ≃* SU4 K 1) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (_ : Algebra K E),
      ∀ (Z : Matrix (Fin 4) (Fin 4) K) (σ : MulAut S),
        σ ∈ Subgroup.normalizer (L : Set (MulAut S)) →
        (∀ x y : ↥L, (y : MulAut S) = σ * x * σ⁻¹ → FinU4FrobPair Z (η x) (η y)) →
        ∃ N : Matrix (TIdx finU4Label) (TIdx finU4Label) E,
          (∀ x : SU4 K 1, ∃ y : SU4 K 1, FinU4FrobPair Z x y ∧
            N * Tmod K finU4Label E x = Tmod K finU4Label E y * N) ∧
          (σ * σ = 1 → N * N = 1) ∧ disp σ = (N - 1).rank := by
  classical
  obtain ⟨hSnt, xne, hxne⟩ :=
    CFSG.HardMathSupport.U4FF.ClassFinal.nontrivial_of_isU4Group hL
  haveI : Nontrivial S := hSnt
  let ρ := CFSG.HardMathSupport.U4FF.ClassFinal.binRep L η
  haveI : Fact ρ.IsIrreducible :=
    ⟨CFSG.HardMathSupport.U4FF.ClassFinal.binRep_isIrreducible η hirr⟩
  have hnt : ∃ g, ρ g ≠ 1 :=
    ⟨η xne, CFSG.HardMathSupport.U4FF.ClassFinal.binRep_ne_one L η xne hxne⟩
  have hlin : ∀ x : ↥L, ρ (η x) =
      (binaryLin ((x : ↥L) : MulAut S) : Additive S →ₗ[ZMod 2] Additive S) :=
    CFSG.HardMathSupport.U4FF.ClassFinal.binRep_eta_lin L η
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    CFSG.HardMathSupport.U4FF.u4_descent (CFSG.HardMathSupport.U4FF.classif_holds hK) hK hnt
  let D := CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ
  haveI : Finite D := CFSG.QuasithinUnique.Setup.SL2Modules.finite_endRing ρ
  letI : Field D := CFSG.QuasithinUnique.Setup.SL2Modules.endRingField ρ
  haveI : Module.Finite D (Additive S) := Module.Finite.of_finite
  haveI : Module.Free D (Additive S) := Module.Free.of_divisionRing D (Additive S)
  let m := Module.finrank D (Additive S)
  let b₀ : Module.Basis (Fin m) D (Additive S) := Module.finBasis D (Additive S)
  obtain ⟨E, hEfield, hEfin, hEchar, ιK, ιD, l, hl0, ⟨Φ⟩, hm1, hm2, hdimW⟩ := hdesc b₀
  letI : Algebra K E := ιK.toAlgebra
  have hWcard : Nat.card (Additive S) = 2 ^ 14 :=
    (Nat.card_congr Additive.toMul).trans hS
  have hfin14 : Module.finrank (ZMod 2) (Additive S) = 14 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive S)
    rw [Nat.card_zmod, hWcard] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1).symm
  have hfinmul : Module.finrank (ZMod 2) (Additive S) = d * l.dim := by
    have h1 : Nat.card (Additive S) = 2 ^ Module.finrank (ZMod 2) (Additive S) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive S), Nat.card_zmod]
    have h2 : Nat.card (Additive S) = (2 ^ d) ^ Module.finrank D (Additive S) := by
      rw [Module.natCard_eq_pow_finrank (K := D) (V := Additive S), hDcard]
    rw [h1, hdimW, ← pow_mul] at h2
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  obtain ⟨hd_eq, hl_eq⟩ := w183_u4_numerics hd1 l hl0 (hfinmul.symm.trans hfin14)
  subst l
  have hDcard2 : Nat.card D = 2 := by rw [hDcard, hd_eq]; norm_num
  have hD01 : ∀ x : D, x = 0 ∨ x = 1 := by
    obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : D)).mp hDcard2
    have hy1 : y = 1 := (hyuniq 1 one_ne_zero).symm
    intro d
    by_cases hd : d = 0
    · exact Or.inl hd
    · exact Or.inr (by rw [hyuniq d hd, hy1])
  haveI : Fintype D := Fintype.ofFinite D
  have hDftwo : Fintype.card D = 2 := by rw [← Nat.card_eq_fintype_card]; exact hDcard2
  haveI : CharP D 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) D).injective 2
  let eD : D ≃+* ZMod 2 := (ZMod.ringEquiv D hDftwo).symm
  have hcoeff : ∀ c : D, ∀ x : Additive S, eD c • x = c • x := by
    intro c x
    rcases hD01 c with h | h <;> simp [h]
  have hm : m = 14 := by
    rw [show m = Module.finrank D (Additive S) from rfl, hdimW, finU4Label_dim]
  let bZ : Module.Basis (Fin m) (ZMod 2) (Additive S) := b₀.mapCoeffs eD hcoeff
  have hcardm : Fintype.card (Fin m) = Fintype.card (TIdx finU4Label) := by
    rw [Fintype.card_fin, CFSG.HardMathSupport.U4FF.card_TIdx, finU4Label_dim]
    exact hm
  let eidx : Fin m ≃ TIdx finU4Label := Fintype.equivOfCardEq hcardm
  let b : Module.Basis (TIdx finU4Label) (ZMod 2) (Additive S) := bZ.reindex eidx
  have hcomp : (ZMod.castHom (dvd_refl 2) E) ∘ eD = ιD := by
    funext c
    rcases hD01 c with h | h <;> simp [h]
  let binD : MulAut S →* Module.End D (Additive S) :=
    { toFun := fun g =>
        { toFun := fun w => binaryLin g w
          map_add' := fun x y => (binaryLin g).map_add x y
          map_smul' := fun c x => by
            rcases hD01 c with h | h <;> simp [h] }
      map_one' := by ext w; simp
      map_mul' := fun g h => by
        ext w
        show binaryLin (g * h) w = binaryLin g (binaryLin h w)
        rw [map_mul]; rfl }
  let matHom : Module.End D (Additive S) →* Matrix (Fin m) (Fin m) D :=
    { toFun := fun f => LinearMap.toMatrix b₀ b₀ f
      map_one' := LinearMap.toMatrix_one b₀
      map_mul' := fun f g => LinearMap.toMatrix_mul (v₁ := b₀) f g }
  let mapHom : Matrix (Fin m) (Fin m) D →* Matrix (Fin m) (Fin m) E :=
    { toFun := fun A => A.map ιD
      map_one' := Matrix.map_one ιD (map_zero ιD) (map_one ιD)
      map_mul' := fun A B => Matrix.map_mul }
  let B : MulAut S →* Matrix (Fin m) (Fin m) E := mapHom.comp (matHom.comp binD)
  let M : MulAut S → Matrix (TIdx finU4Label) (TIdx finU4Label) (ZMod 2) :=
    fun g => LinearMap.toMatrix b b (binaryLin g : Additive S →ₗ[ZMod 2] Additive S)
  have hMrel : ∀ g : MulAut S,
      M g = ((LinearMap.toMatrix b₀ b₀ (binD g)).map eD).reindex eidx eidx := by
    intro g
    show LinearMap.toMatrix b b (binaryLin g : Additive S →ₗ[ZMod 2] Additive S) =
      ((LinearMap.toMatrix b₀ b₀ (binD g)).map eD).reindex eidx eidx
    rw [w183_toMatrix_reindex bZ eidx (binaryLin g : Additive S →ₗ[ZMod 2] Additive S)]
    exact congrArg (fun X : Matrix (Fin m) (Fin m) (ZMod 2) => X.reindex eidx eidx)
      (w183_toMatrix_mapCoeffs eD b₀ hcoeff (binaryLin g : Additive S →ₗ[ZMod 2] Additive S)
        (binD g) (fun w => rfl))
  have hrepD : ∀ x : ↥L,
      CFSG.QuasithinUnique.Setup.SL2Modules.repD ρ (η x) = binD x := by
    intro x
    ext w
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.repD_apply, hlin x]
    rfl
  have hBmat : ∀ x : ↥L,
      CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD (η x) = Matrix.toLin' (B x) := by
    intro x
    have h1 : CFSG.QuasithinUnique.Setup.SL2Modules.matRep b₀ (η x) =
        LinearMap.toMatrix b₀ b₀ (binD x) := by
      rw [← hrepD x]
      rfl
    rw [show CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD (η x) =
        Matrix.toLin' ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b₀ (η x)).map ιD)
      from rfl, h1]
    rfl
  refine ⟨E, hEfield, hEfin, hEchar, ιK.toAlgebra, ?_⟩
  intro Z σ hσN hFrob
  let Blin : (Fin m → E) →ₗ[E] (Fin m → E) := Matrix.toLin' (B σ)
  let Φl : (TIdx finU4Label → E) →ₗ[E] (Fin m → E) := Φ.toLinearEquiv.toLinearMap
  let Φs : (Fin m → E) →ₗ[E] (TIdx finU4Label → E) := Φ.toLinearEquiv.symm.toLinearMap
  let Nlin : (TIdx finU4Label → E) →ₗ[E] (TIdx finU4Label → E) := Φs.comp (Blin.comp Φl)
  let N : Matrix (TIdx finU4Label) (TIdx finU4Label) E := LinearMap.toMatrix' Nlin
  have hΦlΦs : ∀ u : Fin m → E, Φl (Φs u) = u :=
    fun u => by
      change Φ.toLinearEquiv (Φ.toLinearEquiv.symm u) = u
      exact Φ.toLinearEquiv.apply_symm_apply u
  have hΦsΦl : ∀ v : TIdx finU4Label → E, Φs (Φl v) = v :=
    fun v => by
      change Φ.toLinearEquiv.symm (Φ.toLinearEquiv v) = v
      exact Φ.toLinearEquiv.symm_apply_apply v
  refine ⟨N, ?_, ?_, ?_⟩
  · intro x
    set x₀ : ↥L := η.symm x with hx₀def
    have hxη : η x₀ = x := η.apply_symm_apply x
    have hmem : σ * (x₀ : MulAut S) * σ⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hσN x₀).mp x₀.2
    let y₀ : ↥L := ⟨σ * (x₀ : MulAut S) * σ⁻¹, hmem⟩
    have hy₀ : (y₀ : MulAut S) = σ * (x₀ : MulAut S) * σ⁻¹ := rfl
    refine ⟨η y₀, ?_, ?_⟩
    · rw [← hxη]; exact hFrob x₀ y₀ hy₀
    · have hB : B σ * B (x₀ : MulAut S) = B (y₀ : MulAut S) * B σ := by
        have h1 : (σ : MulAut S) * (x₀ : MulAut S) = (y₀ : MulAut S) * σ := by
          rw [hy₀]; group
        calc B σ * B (x₀ : MulAut S) = B ((σ : MulAut S) * (x₀ : MulAut S)) :=
              (map_mul B σ (x₀ : MulAut S)).symm
          _ = B ((y₀ : MulAut S) * σ) := by rw [h1]
          _ = B (y₀ : MulAut S) * B σ := map_mul B (y₀ : MulAut S) σ
      have htoLin_v : ∀ w : Fin m → E,
          Blin (CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD x w) =
          CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD (η y₀) (Blin w) := by
        intro w
        have h1 : CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD x =
            Matrix.toLin' (B x₀) := by rw [← hxη]; exact hBmat x₀
        have h2 : CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD (η y₀) =
            Matrix.toLin' (B y₀) := hBmat y₀
        rw [h1, h2]
        show Matrix.toLin' (B σ) (Matrix.toLin' (B x₀) w) =
          Matrix.toLin' (B y₀) (Matrix.toLin' (B σ) w)
        rw [← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, hB]
      have hPhi_v : ∀ v : TIdx finU4Label → E,
          Φl (Matrix.toLin' (Tmod K finU4Label E x) v) =
          CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD x (Φl v) := by
        intro v
        show Φ.toLinearEquiv (Matrix.toLin' (Tmod K finU4Label E x) v) =
          CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD x (Φ.toLinearEquiv v)
        rw [Matrix.toLin'_apply, ← CFSG.QuasithinUnique.Setup.X7.matRep_apply]
        exact CFSG.QuasithinUnique.Setup.SL2Modules.equiv_apply Φ x v
      have hPhiY_v : ∀ u : Fin m → E,
          Φs (CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD (η y₀) u) =
          Matrix.toLin' (Tmod K finU4Label E (η y₀)) (Φs u) := by
        intro u
        show Φ.toLinearEquiv.symm
            (CFSG.QuasithinUnique.Setup.SL2Modules.matRepE b₀ ιD (η y₀) u) =
          Matrix.toLin' (Tmod K finU4Label E (η y₀)) (Φ.toLinearEquiv.symm u)
        rw [Matrix.toLin'_apply, ← CFSG.QuasithinUnique.Setup.X7.matRep_apply]
        exact CFSG.QuasithinUnique.Setup.SL2Modules.equiv_apply Φ.symm (η y₀) u
      have hgoal : Nlin * Matrix.toLin' (Tmod K finU4Label E x) =
          Matrix.toLin' (Tmod K finU4Label E (η y₀)) * Nlin := by
        apply LinearMap.ext
        intro v
        show Φs (Blin (Φl (Matrix.toLin' (Tmod K finU4Label E x) v))) =
          Matrix.toLin' (Tmod K finU4Label E (η y₀)) (Φs (Blin (Φl v)))
        rw [hPhi_v v, htoLin_v (Φl v), hPhiY_v (Blin (Φl v))]
      calc N * Tmod K finU4Label E x
          = LinearMap.toMatrix' Nlin *
              LinearMap.toMatrix' (Matrix.toLin' (Tmod K finU4Label E x)) := by
            rw [LinearMap.toMatrix'_toLin']
        _ = LinearMap.toMatrix' (Nlin * Matrix.toLin' (Tmod K finU4Label E x)) := by
            rw [LinearMap.toMatrix'_mul]
        _ = LinearMap.toMatrix' (Matrix.toLin' (Tmod K finU4Label E (η y₀)) * Nlin) := by
            rw [hgoal]
        _ = LinearMap.toMatrix' (Matrix.toLin' (Tmod K finU4Label E (η y₀))) *
              LinearMap.toMatrix' Nlin := by
            rw [LinearMap.toMatrix'_mul]
        _ = Tmod K finU4Label E (η y₀) * N := by
            rw [LinearMap.toMatrix'_toLin']
  · intro hσ2
    have hBB : B σ * B σ = 1 := by rw [← map_mul, hσ2, map_one]
    have hBlin2 : Blin.comp Blin = 1 := by
      change (Matrix.toLin' (B σ)).comp (Matrix.toLin' (B σ)) = 1
      rw [← Matrix.toLin'_mul, hBB, Matrix.toLin'_one]
      rfl
    have hNlin : Nlin * Nlin = 1 :=
      w183_conj_involution Φl Φs Blin hΦlΦs hΦsΦl hBlin2
    show N * N = 1
    rw [show N * N = LinearMap.toMatrix' (Nlin * Nlin) from
      (LinearMap.toMatrix'_mul Nlin Nlin).symm, hNlin, LinearMap.toMatrix'_one]
  · have hMsub : M σ - 1 = LinearMap.toMatrix b b
        ((binaryLin σ : Additive S →ₗ[ZMod 2] Additive S) - 1) := by
      show LinearMap.toMatrix b b (binaryLin σ : Additive S →ₗ[ZMod 2] Additive S) - 1 = _
      rw [map_sub, LinearMap.toMatrix_one]
      rfl
    have hMrank : (M σ - 1).rank = disp σ := by
      rw [hMsub, Matrix.rank_eq_finrank_range_toLin _ b b, Matrix.toLin_toMatrix]
      rfl
    have hmap : (M σ).map (ZMod.castHom (dvd_refl 2) E) = (B σ).reindex eidx eidx := by
      rw [hMrel σ]
      show (((LinearMap.toMatrix b₀ b₀ (binD σ)).map eD).map
        (ZMod.castHom (dvd_refl 2) E)).reindex eidx eidx = (B σ).reindex eidx eidx
      congr 1
      rw [Matrix.map_map, hcomp]
      rfl
    have hrankMB : ((M σ).map (ZMod.castHom (dvd_refl 2) E) - 1).rank = (B σ - 1).rank := by
      rw [hmap]
      rw [show (B σ).reindex eidx eidx - 1 = (B σ - 1).reindex eidx eidx from by
        ext i j
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
          eidx.symm.injective.eq_iff]]
      rw [Matrix.rank_reindex]
    have hmap2 : ((M σ - 1).map (ZMod.castHom (dvd_refl 2) E)).rank = (B σ - 1).rank := by
      rw [← hrankMB]
      congr 1
      ext i j
      simp [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub, map_one]
    have hNrank : (N - 1).rank = (B σ - 1).rank := by
      have hNsub : N - 1 = LinearMap.toMatrix' (Nlin - 1) := by
        show LinearMap.toMatrix' Nlin - 1 = _
        rw [map_sub, LinearMap.toMatrix'_one]
      have hBlin1 : Blin - 1 = Matrix.toLin' (B σ - 1) := by
        apply LinearMap.ext
        intro v
        simp only [Blin, LinearMap.sub_apply, Module.End.one_apply, Matrix.toLin'_apply,
          Matrix.sub_mulVec, Matrix.one_mulVec]
      have hNlin1 : Nlin - 1 = Φs.comp ((Blin - 1).comp Φl) := by
        apply LinearMap.ext
        intro v
        show Φs (Blin (Φl v)) - v = Φs ((Blin - 1) (Φl v))
        rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, hΦsΦl v]
      rw [hNsub]
      show (LinearMap.toMatrix' (Nlin - 1)).rank = (B σ - 1).rank
      rw [show (LinearMap.toMatrix' (Nlin - 1)).rank =
        Module.finrank E (LinearMap.range (Nlin - 1)) from by
          rw [Matrix.rank, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']]
      have hsurj : Function.Surjective Φl := fun y => Φ.toLinearEquiv.surjective y
      rw [hNlin1, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
      rw [show Submodule.map Φs (LinearMap.range (Blin - 1)) =
        Submodule.map (Φ.toLinearEquiv.symm :
          (Fin m → E) →ₗ[E] (TIdx finU4Label → E))
          (LinearMap.range (Blin - 1)) from rfl]
      rw [LinearEquiv.finrank_map_eq, hBlin1, Matrix.rank]
      rfl
    rw [← hMrank, ← finU4_rank_map_zmod_two (E := E) (M σ - 1), hmap2]
    exact hNrank.symm

end CFSG.LocalAnalysis.WeakClosure81
