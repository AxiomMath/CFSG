module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Torus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.BenderSuzuki

open MatrixGroups PFAppendixIII PFchapter1section1
open scoped LinearAlgebra.Projectivization Pointwise

universe u v

/-! The model-specific standard-pair computations for Proposition 8.4(d).

The first branch below is the Suzuki calculation.  The PSL and PSU branches
will use the same `invertedTorus_of_standard_pair` interface after their
natural torus/Weyl calculations are exposed.
-/

public theorem suzuki_invertedTorus_of_borel
    (m : ℕ) (hm : 0 < m)
    {B : Subgroup (SuzukiMatrixGroup m)}
    (hB : IsBorelSubgroup B) (t : SuzukiMatrixGroup m)
    (ht : IsInvolution t) (htB : t ∉ B) :
    ∃ T : Subgroup (SuzukiMatrixGroup m),
      (T : Set (SuzukiMatrixGroup m)) =
          {x | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = 2 ^ (2 * m + 1) - 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  obtain ⟨rho, pinfO, S, hrho, hnormalizer, _hregular, htwoRaw⟩ :=
    suzuki_sylow_normalizer_action m hm
  letI : MulAction G Omega := MulAction.compHom Omega rho
  have hnormalizer' :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        MulAction.stabilizer G pinfO := by
    calc
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
          (MulAction.stabilizer (Equiv.Perm Omega) pinfO).comap rho :=
        hnormalizer
      _ = MulAction.stabilizer G pinfO := by
        ext g
        change (rho g) pinfO = pinfO ↔ (rho g) pinfO = pinfO
        rfl
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwoRaw a b c d hab hcd
  have hBpoint : ∃ alpha : Omega, B = MulAction.stabilizer G alpha :=
    hB.eq_stabilizer_of_sylow_normalizer S pinfO hnormalizer'
  let alpha0 : Omega := ⟨pinf, Or.inl rfl⟩
  let beta0 : Omega := ⟨p 0 0, Or.inr ⟨(0, 0), rfl⟩⟩
  have halpha0beta0 : alpha0 ≠ beta0 := by
    intro h
    have hraw : pinf = p 0 0 := congrArg Subtype.val h
    apply External.suzukiOvoidInfinity_not_mem_range m pi
    exact ⟨(0, 0), by simpa [p] using hraw.symm⟩
  let w : G :=
    ⟨SuzukiWeylGL m,
      Subgroup.subset_closure (show SuzukiWeylGL m ∈ SuzukiMatrixGeneratorSet m by
        exact Or.inr (Or.inr rfl))⟩
  have hwalpha : w • alpha0 = beta0 := by
    apply Subtype.ext
    change ((rho w alpha0 : Omega) : ℙ K (Fin 4 → K)) = p 0 0
    rw [hrho]
    simpa [w, alpha0, beta0, p, pinf] using
      (External.suzukiWeyl_smul_infinity m pi)
  have hwbeta : w • beta0 = alpha0 := by
    apply Subtype.ext
    change ((rho w beta0 : Omega) : ℙ K (Fin 4 → K)) = pinf
    rw [hrho]
    simpa [w, alpha0, beta0, p, pinf] using
      (External.suzukiWeyl_smul_zero m pi)
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  have hHleG : H ≤ G := by
    dsimp [H, G]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  let H0 : Subgroup G := H.subgroupOf G
  have hH0set : (H0 : Set G) =
      {x : G | x • alpha0 = alpha0 ∧ x • beta0 = beta0} := by
    ext x
    change ((x : G) : GL (Fin 4) K) ∈ H ↔ _
    constructor
    · intro hx
      rcases (External.suzukiTorusGL_mem_closure_iff m
        ((x : G) : GL (Fin 4) K)).mp hx with ⟨u, hu⟩
      constructor
      · apply Subtype.ext
        change ((rho x alpha0 : Omega) : ℙ K (Fin 4 → K)) = pinf
        rw [hrho, hu]
        simpa [alpha0, pinf] using
          (External.suzukiTorus_smul_infinity m u)
      · apply Subtype.ext
        change ((rho x beta0 : Omega) : ℙ K (Fin 4 → K)) = p 0 0
        rw [hrho, hu]
        simpa [beta0, p] using
          (External.suzukiTorus_smul_finite m pi hpi_sq hpi u 0 0)
    · intro hx
      apply External.suzukiMatrixGroup_mem_torus_of_fix_infinity_zero
        m pi hpi_sq hpi x
      · calc
          (Matrix.GeneralLinearGroup.toLin
              ((x : G) : GL (Fin 4) K)).toLinearEquiv • pinf =
              ((rho x alpha0 : Omega) : ℙ K (Fin 4 → K)) := by
                simpa [alpha0, pinf] using (hrho x alpha0).symm
          _ = pinf := by
            exact congrArg Subtype.val hx.1
      · calc
          (Matrix.GeneralLinearGroup.toLin
              ((x : G) : GL (Fin 4) K)).toLinearEquiv • p 0 0 =
              ((rho x beta0 : Omega) : ℙ K (Fin 4 → K)) := by
                simpa [beta0, p] using (hrho x beta0).symm
          _ = p 0 0 := by
            exact congrArg Subtype.val hx.2
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hunique, _hformula, _hFp, _hFpow, _hForder, _hclass, _hFcard,
      _hFtype, _hrootmul, _hcomm, _hcommcoord, htorus_equiv,
      _htorusconj, _hdisjoint, _hfixed⟩
  rcases htorus_equiv with ⟨eH, _heH⟩
  let eH0 : H0 ≃* H := Subgroup.subgroupOfEquivOfLe hHleG
  have hHcyclic : IsCyclic H := by
    exact eH.isCyclic.mp (inferInstance : IsCyclic Kˣ)
  have hH0cyclic : IsCyclic H0 := eH0.isCyclic.mpr hHcyclic
  have hH0comm : IsMulCommutative H0 := by
    letI : IsCyclic H0 := hH0cyclic
    exact IsCyclic.isMulCommutative
  have hT0set : (H0 : Set G) =
      {x : G | x ∈ H0 ∧ rightConjugateElem x w = x⁻¹} := by
    ext x
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      rcases (External.suzukiTorusGL_mem_closure_iff m
        ((x : G) : GL (Fin 4) K)).mp hx with ⟨u, hu⟩
      have hw_sq : (SuzukiWeylGL m) * SuzukiWeylGL m = 1 :=
        External.suzukiWeylGL_mul_self m
      have hw_inv : (SuzukiWeylGL m)⁻¹ = SuzukiWeylGL m :=
        eq_inv_of_mul_eq_one_right hw_sq
      rw [rightConjugateElem]
      apply Subtype.ext
      change (SuzukiWeylGL m)⁻¹ * ((x : G) : GL (Fin 4) K) *
          SuzukiWeylGL m = ((x : G) : GL (Fin 4) K)⁻¹
      rw [hw_inv, hu, External.suzukiWeylGL_conj_torus,
        External.suzukiTorusGL_inv]
    · intro hx
      exact hx.1
  have hH0card : Nat.card H0 = 2 ^ (2 * m + 1) - 1 := by
    calc
      Nat.card H0 = Nat.card H := Nat.card_congr eH0.toEquiv
      _ = Nat.card Kˣ := Nat.card_congr eH.toEquiv.symm
      _ = Nat.card K - 1 := Nat.card_units K
      _ = 2 ^ (2 * m + 1) - 1 := by
        rw [show Nat.card K = 2 ^ (2 * m + 1) by
          simpa [K, BinaryGaloisField] using
            GaloisField.card 2 (2 * m + 1) (by omega)]
  obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
    invertedTorus_of_standard_pair B t ht htB htwo hBpoint
      alpha0 beta0 halpha0beta0 w hwalpha hwbeta H0 H0
      hH0set hH0comm hT0set hH0cyclic
  exact ⟨T, hTset, hTcyclic, hTcard.trans hH0card⟩

public theorem pgl_invertedTorus_of_borel
    (n : ℕ) (hn : 2 ≤ n)
    [Finite (Matrix.ProjGenLinGroup (Fin 2) (BinaryGaloisField n))]
    {B : Subgroup (Matrix.ProjGenLinGroup (Fin 2)
      (BinaryGaloisField n))}
    (hB : IsBorelSubgroup B)
    (t : Matrix.ProjGenLinGroup (Fin 2) (BinaryGaloisField n))
    (ht : IsInvolution t) (htB : t ∉ B) :
    ∃ T : Subgroup (Matrix.ProjGenLinGroup (Fin 2)
      (BinaryGaloisField n)),
      (T : Set _) =
          {x | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = 2 ^ n - 1 := by
  classical
  let K := BinaryGaloisField n
  letI : Field K := instFieldGaloisField 2 n
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  let Omega := ℙ K (Fin 2 → K)
  letI : Finite G :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨rho, pinf, S, hrho, hnormalizer, _hregular, htwoRaw⟩ :=
    pgl_sylow_normalizer_action n hn
  letI : MulAction G Omega := MulAction.compHom Omega rho
  have hnormalizer' :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        MulAction.stabilizer G pinf := by
    calc
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
          (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
        hnormalizer
      _ = MulAction.stabilizer G pinf := by
        ext g
        change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
        rfl
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwoRaw a b c d hab hcd
  have hBpoint : ∃ alpha : Omega, B = MulAction.stabilizer G alpha :=
    hB.eq_stabilizer_of_sylow_normalizer S pinf hnormalizer'
  let e0 : Fin 2 → K := ![1, 0]
  let e1 : Fin 2 → K := ![0, 1]
  let e01 : Fin 2 → K := ![1, 1]
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simpa [e0] using this
  have he1 : e1 ≠ 0 := by
    intro h
    have := congrFun h 1
    simpa [e1] using this
  have he01 : e01 ≠ 0 := by
    intro h
    have := congrFun h 0
    simpa [e01] using this
  let alpha0 : Omega := Projectivization.mk K e0 he0
  let beta0 : Omega := Projectivization.mk K e1 he1
  let gamma0 : Omega := Projectivization.mk K e01 he01
  have halpha0beta0 : alpha0 ≠ beta0 := by
    intro h
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.mk_eq_mk_iff] at h
    rcases h with ⟨c, hc⟩
    have h0 := congrFun hc 0
    simpa [e0, e1] using h0
  let diagGL (k : Kˣ) : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![(k : K), 1]) (by
        simp [Matrix.det_diagonal, Fin.prod_univ_two, k.ne_zero])
  let diagHom : Kˣ →* GL (Fin 2) K :=
    { toFun := diagGL
      map_one' := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [diagGL]
      map_mul' := by
        intro k l
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] }
  let torus : Kˣ →* G :=
    Matrix.ProjGenLinGroup.mk.comp diagHom
  let wGL : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by
      simp [Matrix.det_fin_two])
  let w : G := Matrix.ProjGenLinGroup.mk wGL
  have hwalpha : w • alpha0 = beta0 := by
    change rho w alpha0 = beta0
    rw [hrho w alpha0 wGL rfl]
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [wGL, e0, e1, beta0, Matrix.mulVec, Fin.sum_univ_two]
  have hwbeta : w • beta0 = alpha0 := by
    change rho w beta0 = alpha0
    rw [hrho w beta0 wGL rfl]
    rw [show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [wGL, e0, e1, alpha0, Matrix.mulVec, Fin.sum_univ_two]
  have htorus_alpha (k : Kˣ) : torus k • alpha0 = alpha0 := by
    change rho (torus k) alpha0 = alpha0
    rw [hrho (torus k) alpha0 (diagHom k) rfl]
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨(k : K), ?_⟩
    funext i
    fin_cases i <;>
      simp [diagHom, diagGL, e0, Matrix.mulVec, Fin.sum_univ_two]
  have htorus_beta (k : Kˣ) : torus k • beta0 = beta0 := by
    change rho (torus k) beta0 = beta0
    rw [hrho (torus k) beta0 (diagHom k) rfl]
    rw [show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [diagHom, diagGL, e1, Matrix.mulVec, Fin.sum_univ_two]
  let H0 : Subgroup G :=
    MulAction.stabilizer G alpha0 ⊓ MulAction.stabilizer G beta0
  have hH0set : (H0 : Set G) =
      {x : G | x • alpha0 = alpha0 ∧ x • beta0 = beta0} := by
    ext x
    constructor
    · intro hx
      exact ⟨MulAction.mem_stabilizer_iff.mp hx.1,
        MulAction.mem_stabilizer_iff.mp hx.2⟩
    · intro hx
      exact ⟨MulAction.mem_stabilizer_iff.mpr hx.1,
        MulAction.mem_stabilizer_iff.mpr hx.2⟩
  have htorus_range_le : torus.range ≤ H0 := by
    rintro _ ⟨k, rfl⟩
    exact ⟨MulAction.mem_stabilizer_iff.mpr (htorus_alpha k),
      MulAction.mem_stabilizer_iff.mpr (htorus_beta k)⟩
  have hH0_le_range : H0 ≤ torus.range := by
    intro g hg
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hfixalpha :
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • alpha0 =
          alpha0 := by
      rw [← hrho g alpha0 A hA]
      exact MulAction.mem_stabilizer_iff.mp hg.1
    have hfixbeta :
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • beta0 =
          beta0 := by
      rw [← hrho g beta0 A hA]
      exact MulAction.mem_stabilizer_iff.mp hg.2
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff] at hfixalpha
    rw [show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff] at hfixbeta
    rcases hfixalpha with ⟨c, hc⟩
    rcases hfixbeta with ⟨d, hd⟩
    change (c : K) • e0 = Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K) e0 at hc
    change (d : K) • e1 = Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K) e1 at hd
    have hc0 := congrFun hc 0
    have hc1 := congrFun hc 1
    have hd0 := congrFun hd 0
    have hd1 := congrFun hd 1
    simp [e0, e1, Matrix.mulVec, Fin.sum_univ_two] at hc0 hc1 hd0 hd1
    change (c : K) = (A : Matrix (Fin 2) (Fin 2) K) 0 0 at hc0
    change (0 : K) = (A : Matrix (Fin 2) (Fin 2) K) 1 0 at hc1
    change (0 : K) = (A : Matrix (Fin 2) (Fin 2) K) 0 1 at hd0
    change (d : K) = (A : Matrix (Fin 2) (Fin 2) K) 1 1 at hd1
    have hA00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (c : K) := by
      exact hc0.symm
    have hA10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      exact hc1.symm
    have hA01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      exact hd0.symm
    have hA11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (d : K) := by
      exact hd1.symm
    let k : Kˣ := c * d⁻¹
    have hAdiag : A = Matrix.GeneralLinearGroup.scalar (Fin 2) d * diagHom k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.scalar, diagHom, diagGL, k,
          Matrix.mul_apply, Fin.sum_univ_two, hA00, hA01, hA10, hA11,
          mul_left_comm]
    refine ⟨k, ?_⟩
    calc
      torus k = Matrix.ProjGenLinGroup.mk (diagHom k) := rfl
      _ = Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.scalar (Fin 2) d * diagHom k) := by
            calc
              Matrix.ProjGenLinGroup.mk (diagHom k) =
                  Matrix.ProjGenLinGroup.mk
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) d) *
                      Matrix.ProjGenLinGroup.mk (diagHom k) := by
                        rw [Matrix.ProjGenLinGroup.mk_scalar, one_mul]
              _ = Matrix.ProjGenLinGroup.mk
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) d * diagHom k) := by
                      exact (map_mul Matrix.ProjGenLinGroup.mk
                        (Matrix.GeneralLinearGroup.scalar (Fin 2) d)
                        (diagHom k)).symm
      _ = Matrix.ProjGenLinGroup.mk A := congrArg _ hAdiag.symm
      _ = g := hA
  have hH0eq : H0 = torus.range := le_antisymm hH0_le_range htorus_range_le
  have htorus_gamma (k : Kˣ) :
      torus k • gamma0 =
        Projectivization.mk K ![(k : K), 1] (by simp [k.ne_zero]) := by
    change rho (torus k) gamma0 = _
    rw [hrho (torus k) gamma0 (diagHom k) rfl]
    rw [show gamma0 = Projectivization.mk K e01 he01 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [diagHom, diagGL, e01, Matrix.mulVec, Fin.sum_univ_two]
  have htorus_injective : Function.Injective torus := by
    intro k l hkl
    have hact := congrArg (fun g : G => g • gamma0) hkl
    change torus k • gamma0 = torus l • gamma0 at hact
    rw [htorus_gamma k, htorus_gamma l,
      Projectivization.mk_eq_mk_iff] at hact
    rcases hact with ⟨c, hc⟩
    have hc0 := congrFun hc 0
    have hc1 := congrFun hc 1
    simp at hc0 hc1
    apply Units.ext
    have hc_one : (c : K) = 1 := by
      simpa [Units.smul_def] using hc1
    calc
      (k : K) = (c : K) * (l : K) := hc0.symm
      _ = (l : K) := by rw [hc_one, one_mul]
  have hrangeRestrict_injective :
      Function.Injective torus.rangeRestrict := by
    intro a b hab
    apply htorus_injective
    exact congrArg Subtype.val hab
  let eRange : Kˣ ≃* torus.range :=
    MulEquiv.ofBijective torus.rangeRestrict
      ⟨hrangeRestrict_injective, MonoidHom.rangeRestrict_surjective torus⟩
  let eH0 : H0 ≃* torus.range := MulEquiv.subgroupCongr hH0eq
  have hRangeCyclic : IsCyclic torus.range :=
    eRange.isCyclic.mp (inferInstance : IsCyclic Kˣ)
  have hH0cyclic : IsCyclic H0 := eH0.isCyclic.mpr hRangeCyclic
  have hH0comm : IsMulCommutative H0 := by
    letI : IsCyclic H0 := hH0cyclic
    exact IsCyclic.isMulCommutative
  have hwGL_sq : wGL * wGL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [wGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hw_sq : w * w = 1 := by
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk wGL = 1
    rw [← map_mul, hwGL_sq, map_one]
  have hw_inv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hw_sq).symm
  have hweyl_torus (k : Kˣ) :
      rightConjugateElem (torus k) w = (torus k)⁻¹ := by
    rw [rightConjugateElem, hw_inv]
    change w * torus k * w = (torus k)⁻¹
    have hGL : wGL * diagHom k * wGL =
        Matrix.GeneralLinearGroup.scalar (Fin 2) k * diagHom k⁻¹ := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [wGL, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two]
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk (diagHom k) *
          Matrix.ProjGenLinGroup.mk wGL =
        (Matrix.ProjGenLinGroup.mk (diagHom k))⁻¹
    rw [← map_mul, ← map_mul, hGL, map_mul,
      Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    rw [map_inv diagHom k]
    exact map_inv Matrix.ProjGenLinGroup.mk (diagHom k)
  have hT0set : (H0 : Set G) =
      {x : G | x ∈ H0 ∧ rightConjugateElem x w = x⁻¹} := by
    ext x
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      rw [hH0eq] at hx
      rcases hx with ⟨k, rfl⟩
      exact hweyl_torus k
    · intro hx
      exact hx.1
  have hH0card : Nat.card H0 = 2 ^ n - 1 := by
    calc
      Nat.card H0 = Nat.card torus.range := Nat.card_congr eH0.toEquiv
      _ = Nat.card Kˣ := Nat.card_congr eRange.toEquiv.symm
      _ = Nat.card K - 1 := Nat.card_units K
      _ = 2 ^ n - 1 := by
        rw [show Nat.card K = 2 ^ n by
          simpa [K, BinaryGaloisField] using
            GaloisField.card 2 n (by omega)]
  obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
    invertedTorus_of_standard_pair B t ht htB htwo hBpoint
      alpha0 beta0 halpha0beta0 w hwalpha hwbeta H0 H0
      hH0set hH0comm hT0set hH0cyclic
  exact ⟨T, hTset, hTcyclic, hTcard.trans hH0card⟩

public theorem psl_invertedTorus_of_borel
    (n : ℕ) (hn : 2 ≤ n)
    {B : Subgroup (PSL2BinaryMatrixGroup n)}
    (hB : IsBorelSubgroup B)
    (t : PSL2BinaryMatrixGroup n)
    (ht : IsInvolution t) (htB : t ∉ B) :
    ∃ T : Subgroup (PSL2BinaryMatrixGroup n),
      (T : Set _) =
          {x | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = 2 ^ n - 1 := by
  let K := BinaryGaloisField n
  let Q := Matrix.ProjGenLinGroup (Fin 2) K
  letI : Finite Q :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let e : PSL2BinaryMatrixGroup n ≃* Q :=
    (psl_charTwo_equiv_pgl n (by omega)).some
  have hBQ : IsBorelSubgroup (B.map e.toMonoidHom) :=
    hB.map_mulEquiv e
  have het : IsInvolution (e t) :=
    IsInvolution.map_of_injective ht e.toMonoidHom e.injective
  have hetB : e t ∉ B.map e.toMonoidHom := by
    intro hetB
    apply htB
    simpa using hetB
  obtain ⟨TQ, hTQset, hTQcyclic, hTQcard⟩ :=
    pgl_invertedTorus_of_borel n hn hBQ (e t) het hetB
  obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
    invertedTorus_pullback_mulEquiv e B t TQ hTQset hTQcyclic
  exact ⟨T, hTset, hTcyclic, hTcard.trans hTQcard⟩

set_option maxHeartbeats 800000 in
public theorem psu_invertedTorus_with_centralizer_of_borel
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (n : ℕ) (hn : 2 ≤ n)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hKcard : Nat.card K = (2 ^ n) ^ 2)
    (hfixedCard : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hB : IsBorelSubgroup B)
    (t : ProjectiveSpecialUnitaryMatrixGroup J)
    (ht : IsInvolution t) (htB : t ∉ B) :
    (∃ T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      (T : Set _) =
          {x | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = 2 ^ n - 1) ∧
      ∃ z : ProjectiveSpecialUnitaryMatrixGroup J,
        z ≠ 1 ∧ z ∈ B ∧ z ∈ rightConjugate B t ∧
          z ∈ Subgroup.centralizer ({t} : Set _) := by
  classical
  let q := 2 ^ n
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  rcases External.huppert_II_10_12 J q
      (by simpa [q] using hKcard)
      (by simpa [q] using hfixedCard) hJstandard with
    ⟨_hOmegaCard, rho, pinf, _hrho, hnatural, _hUcard,
      hroot, htwoRaw, _hGcard, _hthree⟩
  rcases hroot with
    ⟨R, H, hRle, hHle, hUleNormalizer, hRinfH, hRsupH,
      hHcyclic, hRcard, _hRcomm, _hRcommCard, hHcard,
      hRregular, hRcoordinates, hHcoordinates,
      hHcoordinatesSurjective⟩
  let : MulAction G Omega := MulAction.compHom Omega rho
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    exact htwoRaw a b c d hab hcd
  let vinf : Fin 3 → K := ![1, 0, 0]
  have hvinf : vinf ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  have hisoInf :
      dotProduct (fun i => J.conj (vinf i)) (J.form.mulVec vinf) = 0 := by
    rw [hJstandard]
    simp [vinf, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  let alpha0 : Omega :=
    ⟨Projectivization.mk K vinf hvinf,
      ⟨vinf, hvinf, rfl, hisoInf⟩⟩
  let vzero : Fin 3 → K := ![0, 0, 1]
  have hvzero : vzero ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 2)
  have hisoZero :
      dotProduct (fun i => J.conj (vzero i)) (J.form.mulVec vzero) = 0 := by
    rw [hJstandard]
    simp [vzero, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  let beta0 : Omega :=
    ⟨Projectivization.mk K vzero hvzero,
      ⟨vzero, hvzero, rfl, hisoZero⟩⟩
  have halpha0beta0 : alpha0 ≠ beta0 := by
    intro h
    have hraw := congrArg Subtype.val h
    rw [show (alpha0 : P) = Projectivization.mk K vinf hvinf by rfl,
      show (beta0 : P) = Projectivization.mk K vzero hvzero by rfl,
      Projectivization.mk_eq_mk_iff] at hraw
    rcases hraw with ⟨c, hc⟩
    have h0 := congrFun hc 0
    simpa [vinf, vzero] using h0
  have hpinf : pinf = alpha0 := by
    by_contra hne
    have halphaNe : alpha0 ≠ pinf := fun h => hne h.symm
    rcases hRcoordinates with ⟨coordR, hcoordR⟩
    have hfixAlpha (r : R) : rho (r : G) alpha0 = alpha0 := by
      let z := coordR.symm r
      rcases hcoordR z with ⟨M, hM, hMproj⟩
      have hMroot : M = External.hermitianUnipotentGL J z := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (M : Matrix (Fin 3) (Fin 3) K) i j =
          (External.hermitianUnipotentGL J z :
            Matrix (Fin 3) (Fin 3) K) i j
        rw [hM, External.hermitianUnipotentGL_val]
        rfl
      have hrroot : (r : G) =
          External.hermitianUnipotentPSU J hJstandard z := by
        apply Subtype.ext
        calc
          (((r : R) : G) : Matrix.ProjGenLinGroup (Fin 3) K) =
              Matrix.ProjGenLinGroup.mk M := by simpa [z] using hMproj
          _ = Matrix.ProjGenLinGroup.mk
              (External.hermitianUnipotentGL J z) := congrArg _ hMroot
          _ = ((External.hermitianUnipotentPSU J hJstandard z : G) :
              Matrix.ProjGenLinGroup (Fin 3) K) := rfl
      rw [hrroot]
      apply Subtype.ext
      change ((rho (External.hermitianUnipotentPSU J hJstandard z)
        alpha0 : Omega) : P) = (alpha0 : P)
      rw [hnatural (External.hermitianUnipotentPSU J hJstandard z) alpha0
        (External.hermitianUnipotentSU J hJstandard z) (by rfl)]
      rw [show (alpha0 : P) = Projectivization.mk K vinf hvinf by rfl,
        Projectivization.smul_mk]
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
      refine ⟨1, ?_⟩
      change (1 : K) • vinf =
        ((External.hermitianUnipotentGL J z : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).mulVec vinf
      funext i
      fin_cases i <;>
        simp [External.hermitianUnipotentGL,
          External.hermitianUnipotentMatrix, vinf,
          Matrix.mulVec]
    rcases hRregular alpha0 alpha0 halphaNe halphaNe with
      ⟨_r0, _hr0, hunique⟩
    have hRsub : Subsingleton R :=
      ⟨fun a b => (hunique a (hfixAlpha a)).trans
        (hunique b (hfixAlpha b)).symm⟩
    have hRcardOne : Nat.card R = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hRsub, ⟨1⟩⟩
    have hqCubeOne : q ^ 3 = 1 := hRcard.symm.trans hRcardOne
    have hqOne : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hqCubeOne
    have hqGt : 1 < q := by
      dsimp [q]
      exact one_lt_pow₀ (by norm_num) (by omega)
    exact (ne_of_gt hqGt) hqOne
  have hq : 1 < q := by
    dsimp [q]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    have hRcardOne : Nat.card R = 1 := by rw [hRbot]; simp
    have hqCubeOne : q ^ 3 = 1 := hRcard.symm.trans hRcardOne
    have hqOne : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hqCubeOne
    omega
  have hnormalizerR :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G alpha0 := by
    rw [← hpinf]
    exact normalizer_eq_stabilizer_of_regular_compl R pinf hRle hR_ne
      hRregular hUleNormalizer
  have hnormalizerPinf :
      Subgroup.normalizer (R : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    change Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinf
    rw [hpinf]
    exact hnormalizerR
  have hqEven : Even q := by
    dsimp [q]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hqSqEven : Even (q ^ 2) := hqEven.pow_of_ne_zero (by norm_num)
  have hqSqPos : 0 < q ^ 2 := pow_pos (by omega) 2
  have hqSqSubOneOdd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hqSqPos hqSqEven odd_one
  have hgcdDvd : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hfactor]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact Odd.of_dvd_nat hqSqSubOneOdd (Nat.div_dvd_of_dvd hgcdDvd)
  have hHnotTwo : ¬ 2 ∣ Nat.card H := by
    intro htwoDvd
    exact (Nat.not_even_iff_odd.mpr hHodd) (even_iff_two_dvd.mpr htwoDvd)
  have hRpower : Nat.card R = 2 ^ (n * 3) := by
    simpa [q, pow_mul] using hRcard
  have hRp : IsPGroup 2 R := IsPGroup.of_card hRpower
  obtain ⟨PU, hPU⟩ :=
    exists_sylow_map_eq_of_normal_complement
      hRle hHle hUleNormalizer hRinfH hRsupH hRp hHnotTwo
  have hnormalizerLe :
      Subgroup.normalizer
          (((PU : Subgroup _).map
            ((MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho).subtype :
              Subgroup G) : Set G) ≤
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hPU]
    simpa using hnormalizerPinf.le
  obtain ⟨S, hSmap⟩ :=
    exists_sylow_map_eq_of_normalizer_le PU hnormalizerLe
  have hSR : (S : Subgroup G) = R := hSmap.trans hPU
  have hSnormalizer :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hSR]
    exact hnormalizerPinf
  have hBpoint : ∃ alpha : Omega, B = MulAction.stabilizer G alpha :=
    hB.eq_stabilizer_of_sylow_normalizer S alpha0 (by
      have hSnormalizerG :
          Subgroup.normalizer ((S : Subgroup G) : Set G) =
            MulAction.stabilizer G pinf := by
        calc
          Subgroup.normalizer ((S : Subgroup G) : Set G) =
              (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
            hSnormalizer
          _ = MulAction.stabilizer G pinf := by
            ext g
            change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
            rfl
      simpa only [hpinf] using hSnormalizerG)
  let w : G := External.hermitianWeylPSU J hJstandard
  have hwalpha : w • alpha0 = beta0 := by
    apply Subtype.ext
    change ((rho w alpha0 : Omega) : P) = (beta0 : P)
    rw [hnatural w alpha0 (External.hermitianWeylSU J hJstandard) (by rfl)]
    rw [show (alpha0 : P) = Projectivization.mk K vinf hvinf by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨1, ?_⟩
    change (1 : K) • vzero =
      ((External.hermitianWeylGL (K := K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).mulVec vinf
    funext i
    fin_cases i <;>
      simp [External.hermitianWeylGL, External.hermitianWeylMatrix,
        vinf, vzero, Matrix.mulVec]
  have hwbeta : w • beta0 = alpha0 := by
    apply Subtype.ext
    change ((rho w beta0 : Omega) : P) = (alpha0 : P)
    rw [hnatural w beta0 (External.hermitianWeylSU J hJstandard) (by rfl)]
    rw [show (beta0 : P) = Projectivization.mk K vzero hvzero by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨1, ?_⟩
    change (1 : K) • vinf =
      ((External.hermitianWeylGL (K := K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).mulVec vzero
    funext i
    fin_cases i <;>
      simp [External.hermitianWeylGL, External.hermitianWeylMatrix,
        vinf, vzero, Matrix.mulVec]
  have hwSq : w * w = 1 := by
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk (External.hermitianWeylGL (K := K)) *
        Matrix.ProjGenLinGroup.mk (External.hermitianWeylGL (K := K)) = 1
    rw [← map_mul]
    have hGL : External.hermitianWeylGL (K := K) *
        External.hermitianWeylGL (K := K) = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [External.hermitianWeylGL, External.hermitianWeylMatrix,
          Matrix.mul_apply, Fin.sum_univ_three]
    rw [hGL, map_one]
  have hwInv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hwSq).symm
  let torus : Kˣ →* G := External.hermitianTorusPSU J hJstandard
  have hH0set : (H : Set G) =
      {x : G | x • alpha0 = alpha0 ∧ x • beta0 = beta0} := by
    ext x
    constructor
    · intro hx
      have hxAlpha : x • alpha0 = alpha0 := by
        have hxU := hHle hx
        change rho x pinf = pinf at hxU
        change rho x alpha0 = alpha0
        simpa [hpinf] using hxU
      have hxBeta : x • beta0 = beta0 := by
        rcases hHcoordinates ⟨x, hx⟩ with ⟨k, M, hM, hMproj⟩
        have hMtorus : M = External.hermitianTorusGL J k := by
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          change (M : Matrix (Fin 3) (Fin 3) K) i j =
            (External.hermitianTorusGL J k :
              Matrix (Fin 3) (Fin 3) K) i j
          rw [hM, External.hermitianTorusGL_val]
          rfl
        have hxTorus : x = torus k := by
          apply Subtype.ext
          calc
            (x : Matrix.ProjGenLinGroup (Fin 3) K) =
                Matrix.ProjGenLinGroup.mk M := hMproj
            _ = Matrix.ProjGenLinGroup.mk
                (External.hermitianTorusGL J k) := congrArg _ hMtorus
            _ = ((torus k : G) : Matrix.ProjGenLinGroup (Fin 3) K) := rfl
        rw [hxTorus]
        apply Subtype.ext
        change ((rho (torus k) beta0 : Omega) : P) = (beta0 : P)
        rw [hnatural (torus k) beta0
          (External.hermitianTorusSU J hJstandard k) (by rfl)]
        rw [show (beta0 : P) = Projectivization.mk K vzero hvzero by rfl,
          Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
        refine ⟨(k : K), ?_⟩
        change (k : K) • vzero =
          ((External.hermitianTorusGL J k : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K).mulVec vzero
        funext i
        fin_cases i <;>
          simp [External.hermitianTorusGL, External.hermitianTorusMatrix,
            vzero, Matrix.mulVec]
      exact ⟨hxAlpha, hxBeta⟩
    · rintro ⟨hxAlpha, hxBeta⟩
      rcases x.property with ⟨M, hM, hMx⟩
      let Mu : J.specialSubgroup := ⟨M, hM⟩
      let Mmat : Matrix (Fin 3) (Fin 3) K := M
      have hinf := congrArg Subtype.val hxAlpha
      change ((rho x alpha0 : Omega) : P) = (alpha0 : P) at hinf
      rw [hnatural x alpha0 Mu hMx] at hinf
      change (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv •
          Projectivization.mk K vinf hvinf =
        Projectivization.mk K vinf hvinf at hinf
      rw [Projectivization.smul_mk] at hinf
      obtain ⟨a, ha⟩ :=
        (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hinf
      have hzero := congrArg Subtype.val hxBeta
      change ((rho x beta0 : Omega) : P) = (beta0 : P) at hzero
      rw [hnatural x beta0 Mu hMx] at hzero
      change (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv •
          Projectivization.mk K vzero hvzero =
        Projectivization.mk K vzero hvzero at hzero
      rw [Projectivization.smul_mk] at hzero
      obtain ⟨c, hc⟩ :=
        (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hzero
      change (a : K) • vinf = Mmat.mulVec vinf at ha
      change (c : K) • vzero = Mmat.mulVec vzero at hc
      have ha0 := congrFun ha (0 : Fin 3)
      have ha1 := congrFun ha (1 : Fin 3)
      have ha2 := congrFun ha (2 : Fin 3)
      have hc0 := congrFun hc (0 : Fin 3)
      have hc1 := congrFun hc (1 : Fin 3)
      have hc2 := congrFun hc (2 : Fin 3)
      simp [vinf, vzero, Matrix.mulVec] at ha0 ha1 ha2 hc0 hc1 hc2
      change (a : K) = Mmat 0 0 at ha0
      change (0 : K) = Mmat 1 0 at ha1
      change (0 : K) = Mmat 2 0 at ha2
      change (0 : K) = Mmat 0 2 at hc0
      change (0 : K) = Mmat 1 2 at hc1
      change (c : K) = Mmat 2 2 at hc2
      have h00 : Mmat 0 0 = a := by
        exact ha0.symm
      have h10 : Mmat 1 0 = 0 := by
        exact ha1.symm
      have h20 : Mmat 2 0 = 0 := by
        exact ha2.symm
      have h02 : Mmat 0 2 = 0 := by
        exact hc0.symm
      have h12 : Mmat 1 2 = 0 := by
        exact hc1.symm
      have h22 : Mmat 2 2 = c := by
        exact hc2.symm
      have ha0 : a ≠ 0 := by
        intro hazero
        have hMv : Mmat.mulVec vinf ≠ 0 := by
          intro hz
          apply hvinf
          exact (Matrix.mulVec_injective_of_isUnit (Units.isUnit M))
            (by simpa [Mmat] using hz)
        apply hMv
        funext i
        fin_cases i <;>
          simp [vinf, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
            h00, h10, h20, hazero]
      have hc0 : c ≠ 0 := by
        intro hczero
        have hMv : Mmat.mulVec vzero ≠ 0 := by
          intro hz
          apply hvzero
          exact (Matrix.mulVec_injective_of_isUnit (Units.isUnit M))
            (by simpa [Mmat] using hz)
        apply hMv
        funext i
        fin_cases i <;>
          simp [vzero, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
            h02, h12, h22, hczero]
      have hunit := (J.mem_specialSubgroup_iff M).mp hM |>.1
      rw [hJstandard] at hunit
      have hu01 := congrArg
        (fun X : Matrix (Fin 3) (Fin 3) K => X 0 1) hunit
      have hu21 := congrArg
        (fun X : Matrix (Fin 3) (Fin 3) K => X 2 1) hunit
      have hu02 := congrArg
        (fun X : Matrix (Fin 3) (Fin 3) K => X 0 2) hunit
      have h21 : Mmat 2 1 = 0 := by
        have hprod : J.conj a * Mmat 2 1 = 0 := by
          simpa [Mmat, HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_three, h00, h10, h20, h02, h12,
            map_zero] using hu01
        exact (mul_eq_zero.mp hprod).resolve_left ((map_ne_zero J.conj).2 ha0)
      have h01 : Mmat 0 1 = 0 := by
        have hprod : J.conj c * Mmat 0 1 = 0 := by
          simpa [Mmat, HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_three, h00, h10, h20, h02, h12, h22,
            map_zero] using hu21
        exact (mul_eq_zero.mp hprod).resolve_left ((map_ne_zero J.conj).2 hc0)
      have hac : J.conj a * c = 1 := by
        simpa [Mmat, HermitianForm.conjTranspose, Matrix.mul_apply,
          Fin.sum_univ_three, h00, h10, h20, h02, h12, h22,
          map_zero] using hu02
      have hac' : a * J.conj c = 1 := by
        have h := congrArg J.conj hac
        rw [map_mul, map_one, J.conj_involutive] at h
        exact h
      have haDiag : a = (J.conj c)⁻¹ :=
        eq_inv_of_mul_eq_one_left hac'
      have hdet := congrArg Units.val
        ((J.mem_specialSubgroup_iff M).mp hM |>.2)
      have hdet' : a * Mmat 1 1 * c = 1 := by
        have hdet0 : a * Mmat 1 1 * Mmat 2 2 = 1 := by
          simpa [Mmat, Matrix.det_fin_three, h00, h10, h20, h02, h12,
            h01, h21] using hdet
        rw [h22] at hdet0
        exact hdet0
      have hconjc0 : J.conj c ≠ 0 := (map_ne_zero J.conj).2 hc0
      have hmc : Mmat 1 1 * c = J.conj c := by
        have h := congrArg (fun y : K => J.conj c * y) hdet'
        rw [haDiag] at h
        simpa [hconjc0, mul_assoc] using h
      have hmDiag : Mmat 1 1 = J.conj c * c⁻¹ := by
        calc
          Mmat 1 1 = Mmat 1 1 * (c * c⁻¹) := by
            rw [mul_inv_cancel₀ hc0, mul_one]
          _ = (Mmat 1 1 * c) * c⁻¹ := by ring
          _ = J.conj c * c⁻¹ := by rw [hmc]
      let k : Kˣ := Units.mk0 c hc0
      have hMtorus : M = External.hermitianTorusGL J k := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change Mmat i j =
          (External.hermitianTorusGL J k :
            Matrix (Fin 3) (Fin 3) K) i j
        rw [External.hermitianTorusGL_val]
        fin_cases i <;> fin_cases j <;>
          simp [External.hermitianTorusMatrix, k, h00, h10, h20,
            h01, h21, h02, h12, h22, haDiag, hmDiag]
      obtain ⟨h, N, hN, hNproj⟩ := hHcoordinatesSurjective k
      have hNtorus : N = External.hermitianTorusGL J k := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (N : Matrix (Fin 3) (Fin 3) K) i j =
          (External.hermitianTorusGL J k :
            Matrix (Fin 3) (Fin 3) K) i j
        rw [hN, External.hermitianTorusGL_val]
        rfl
      have hxh : x = (h : G) := by
        apply Subtype.ext
        calc
          (x : Matrix.ProjGenLinGroup (Fin 3) K) =
              Matrix.ProjGenLinGroup.mk M := hMx.symm
          _ = Matrix.ProjGenLinGroup.mk N := by rw [hMtorus, hNtorus]
          _ = ((h : H) : Matrix.ProjGenLinGroup (Fin 3) K) := hNproj.symm
      rw [hxh]
      exact h.property
  have hHcomm : IsMulCommutative H := by
    let : IsCyclic H := hHcyclic
    exact IsCyclic.isMulCommutative
  let k0 := FixedBy.subfield K J.conj
  let fixedIncl : k0ˣ →* Kˣ := Units.map k0.subtype
  let fixedTorus : k0ˣ →* G := torus.comp fixedIncl
  let T0 : Subgroup G := fixedTorus.range
  have hHrange : H = torus.range := by
    apply le_antisymm
    · intro x hx
      rcases hHcoordinates ⟨x, hx⟩ with ⟨k, M, hM, hMproj⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      calc
        (torus k : Matrix.ProjGenLinGroup (Fin 3) K) =
            Matrix.ProjGenLinGroup.mk (External.hermitianTorusGL J k) := rfl
        _ = Matrix.ProjGenLinGroup.mk M := by
          congr 1
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          change (External.hermitianTorusGL J k :
              Matrix (Fin 3) (Fin 3) K) i j =
            (M : Matrix (Fin 3) (Fin 3) K) i j
          rw [External.hermitianTorusGL_val, hM]
          rfl
        _ = (x : Matrix.ProjGenLinGroup (Fin 3) K) := hMproj.symm
    · rintro x ⟨k, rfl⟩
      obtain ⟨h, M, hM, hMproj⟩ := hHcoordinatesSurjective k
      have htorusH : torus k = (h : G) := by
        apply Subtype.ext
        calc
          (torus k : Matrix.ProjGenLinGroup (Fin 3) K) =
              Matrix.ProjGenLinGroup.mk (External.hermitianTorusGL J k) := rfl
          _ = Matrix.ProjGenLinGroup.mk M := by
            congr 1
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            change (External.hermitianTorusGL J k :
                Matrix (Fin 3) (Fin 3) K) i j =
              (M : Matrix (Fin 3) (Fin 3) K) i j
            rw [External.hermitianTorusGL_val, hM]
            rfl
          _ = ((h : H) : Matrix.ProjGenLinGroup (Fin 3) K) := hMproj.symm
      rw [htorusH]
      exact h.property
  let conjUnits : Kˣ →* Kˣ := Units.map J.conj.toRingHom
  have hweylTorus (k : Kˣ) :
      rightConjugateElem (torus k) w = torus (conjUnits k)⁻¹ := by
    rw [rightConjugateElem, hwInv]
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk (External.hermitianWeylGL (K := K)) *
          Matrix.ProjGenLinGroup.mk (External.hermitianTorusGL J k) *
        Matrix.ProjGenLinGroup.mk (External.hermitianWeylGL (K := K)) =
      Matrix.ProjGenLinGroup.mk
        (External.hermitianTorusGL J (conjUnits k)⁻¹)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [External.hermitianWeylGL, External.hermitianWeylMatrix,
        External.hermitianTorusGL, External.hermitianTorusMatrix,
        conjUnits, Matrix.mul_apply, Fin.sum_univ_three, map_inv₀]
    all_goals try rw [J.conj_involutive]
    all_goals try ac_rfl
  have htorusKernelProps (k : Kˣ) (hk : torus k = 1) :
      J.conj (k : K) = (k : K)⁻¹ ∧ (k : K) ^ 3 = 1 := by
    have hpgl : Matrix.ProjGenLinGroup.mk
        (External.hermitianTorusGL J k) = 1 :=
      congrArg Subtype.val hk
    have hcenter : External.hermitianTorusGL J k ∈
        Subgroup.center (GL (Fin 3) K) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hpgl
    rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
      hcenter with ⟨c, hc⟩
    have h00 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
    have h11 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hc
    have h22 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hc
    rw [External.hermitianTorusGL_val] at h00 h11 h22
    simp [External.hermitianTorusMatrix, Matrix.scalar_apply] at h00 h11 h22
    have houter : (J.conj (k : K))⁻¹ = (k : K) :=
      h00.symm.trans h22
    have hmiddle : J.conj (k : K) * (k : K)⁻¹ = (k : K) :=
      h11.symm.trans h22
    have hconj : J.conj (k : K) = (k : K)⁻¹ := by
      apply inv_injective
      simpa using houter
    have hsq : J.conj (k : K) = (k : K) * (k : K) := by
      have h := congrArg (fun y : K => y * (k : K)) hmiddle
      simpa [mul_assoc, Units.ne_zero k] using h
    refine ⟨hconj, ?_⟩
    calc
      (k : K) ^ 3 = ((k : K) * (k : K)) * (k : K) := by ring
      _ = J.conj (k : K) * (k : K) := by rw [← hsq]
      _ = 1 := by rw [hconj, inv_mul_cancel₀ (Units.ne_zero k)]
  have hfixedInclFixed (a : k0ˣ) :
      J.conj (fixedIncl a : K) = (fixedIncl a : K) := by
    change J.conj (((a : k0) : K)) = ((a : k0) : K)
    exact (a : k0).property
  have hfixedTorusInjective : Function.Injective fixedTorus := by
    intro a b hab
    let c : k0ˣ := a * b⁻¹
    have hcKer : fixedTorus c = 1 := by
      change fixedTorus (a * b⁻¹) = 1
      calc
        fixedTorus (a * b⁻¹) = fixedTorus a * fixedTorus (b⁻¹) :=
          map_mul fixedTorus a b⁻¹
        _ = fixedTorus a * (fixedTorus b)⁻¹ :=
          congrArg (fun z : G => fixedTorus a * z) (map_inv fixedTorus b)
        _ = fixedTorus b * (fixedTorus b)⁻¹ := by rw [hab]
        _ = 1 := mul_inv_cancel _
    have hkKer : torus (fixedIncl c) = 1 := hcKer
    rcases htorusKernelProps (fixedIncl c) hkKer with ⟨hconj, hcube⟩
    have hkInv : fixedIncl c = (fixedIncl c)⁻¹ := by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val]
      exact (hfixedInclFixed c).symm.trans hconj
    have hkSquare : (fixedIncl c) ^ 2 = 1 := by
      calc
        (fixedIncl c) ^ 2 = fixedIncl c * fixedIncl c := pow_two _
        _ = (fixedIncl c)⁻¹ * fixedIncl c :=
          congrArg (fun z => z * fixedIncl c) hkInv
        _ = 1 := inv_mul_cancel _
    have hkCube : (fixedIncl c) ^ 3 = 1 := by
      apply Units.ext
      simpa using hcube
    have hkOne : fixedIncl c = 1 := by
      calc
        fixedIncl c = (fixedIncl c) ^ 3 * ((fixedIncl c) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hkCube, hkSquare, inv_one, mul_one]
    have hcOne : c = 1 :=
      (Units.map_injective k0.subtype_injective) (by simpa [fixedIncl] using hkOne)
    exact mul_inv_eq_one.mp hcOne
  have hfixedRepresentative (k : Kˣ)
      (hk : rightConjugateElem (torus k) w = (torus k)⁻¹) :
      ∃ a : k0ˣ, fixedTorus a = torus k := by
    let d : Kˣ := (conjUnits k)⁻¹ * k
    have hanti : torus (conjUnits k)⁻¹ = (torus k)⁻¹ :=
      (hweylTorus k).symm.trans hk
    have hdKer : torus d = 1 := by
      change torus ((conjUnits k)⁻¹ * k) = 1
      calc
        torus ((conjUnits k)⁻¹ * k) =
            torus (conjUnits k)⁻¹ * torus k :=
          map_mul torus (conjUnits k)⁻¹ k
        _ = (torus k)⁻¹ * torus k :=
          congrArg (fun z : G => z * torus k) hanti
        _ = 1 := inv_mul_cancel _
    rcases htorusKernelProps d hdKer with ⟨hconjD, hdCubeVal⟩
    have hconjDUnits : conjUnits d = d⁻¹ := by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val]
      exact hconjD
    have hdCube : d ^ 3 = 1 := by
      apply Units.ext
      simpa using hdCubeVal
    have hdInv : d⁻¹ = d ^ 2 := by
      calc
        d⁻¹ = d⁻¹ * 1 := by rw [mul_one]
        _ = d⁻¹ * d ^ 3 := by rw [hdCube]
        _ = d ^ 2 := by group
    have hconjMulD : conjUnits k * d = k := by
      dsimp [d]
      group
    have heFixedUnits : conjUnits (k * d) = k * d := by
      calc
        conjUnits (k * d) = conjUnits k * conjUnits d :=
          map_mul conjUnits k d
        _ = conjUnits k * d⁻¹ := by rw [hconjDUnits]
        _ = conjUnits k * d ^ 2 := by rw [hdInv]
        _ = (conjUnits k * d) * d :=
          (congrArg (fun z : Kˣ => conjUnits k * z) (pow_two d)).trans
            (mul_assoc (conjUnits k) d d).symm
        _ = k * d := by rw [hconjMulD]
    have heFixedVal :
        J.conj (((k * d : Kˣ) : K)) = ((k * d : Kˣ) : K) := by
      have h := congrArg Units.val heFixedUnits
      change J.conj (((k * d : Kˣ) : K)) = ((k * d : Kˣ) : K) at h
      exact h
    let e0 : k0 := ⟨((k * d : Kˣ) : K), heFixedVal⟩
    have he0 : e0 ≠ 0 := by
      intro hzero
      apply Units.ne_zero (k * d)
      have h := congrArg (fun z : k0 => (z : K)) hzero
      simpa [e0] using h
    let a : k0ˣ := Units.mk0 e0 he0
    have haIncl : fixedIncl a = k * d := by
      apply Units.ext
      rfl
    refine ⟨a, ?_⟩
    change torus (fixedIncl a) = torus k
    calc
      torus (fixedIncl a) = torus (k * d) := congrArg torus haIncl
      _ = torus k * torus d := map_mul torus k d
      _ = torus k * 1 := by rw [hdKer]
      _ = torus k := mul_one _
  have hT0set : (T0 : Set G) =
      {x : G | x ∈ H ∧ rightConjugateElem x w = x⁻¹} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      constructor
      · rw [hHrange]
        exact ⟨fixedIncl a, rfl⟩
      · have hfixedUnits : conjUnits (fixedIncl a) = fixedIncl a := by
          apply Units.ext
          exact hfixedInclFixed a
        change rightConjugateElem (torus (fixedIncl a)) w =
          (torus (fixedIncl a))⁻¹
        calc
          rightConjugateElem (torus (fixedIncl a)) w =
              torus (conjUnits (fixedIncl a))⁻¹ :=
            hweylTorus (fixedIncl a)
          _ = torus (fixedIncl a)⁻¹ := by rw [hfixedUnits]
          _ = (torus (fixedIncl a))⁻¹ := map_inv torus (fixedIncl a)
    · rintro ⟨hxH, hxInv⟩
      rw [hHrange] at hxH
      rcases hxH with ⟨k, rfl⟩
      exact hfixedRepresentative k hxInv
  have hfixedRangeRestrictInjective :
      Function.Injective fixedTorus.rangeRestrict := by
    intro a b hab
    apply hfixedTorusInjective
    exact congrArg Subtype.val hab
  let eT : k0ˣ ≃* T0 :=
    MulEquiv.ofBijective fixedTorus.rangeRestrict
      ⟨hfixedRangeRestrictInjective,
        MonoidHom.rangeRestrict_surjective fixedTorus⟩
  have hT0cyclic : IsCyclic T0 := by
    exact eT.isCyclic.mp (inferInstance : IsCyclic k0ˣ)
  have hT0card : Nat.card T0 = 2 ^ n - 1 := by
    have hk0card : Nat.card k0 = 2 ^ n := by
      let eFixed : k0 ≃ {x : K // J.conj x = x} := {
        toFun x := ⟨x, by
          have hxmem : (x : K) ∈ FixedBy.subfield K J.conj := by
            simpa [k0] using x.property
          have hx :=
            (FixedBy.subfield_mem_iff K J.conj (x : K)).mp hxmem
          simpa [RingAut.smul_def] using hx⟩
        invFun x := ⟨x, by
          change (x : K) ∈ FixedBy.subfield K J.conj
          apply (FixedBy.subfield_mem_iff K J.conj (x : K)).mpr
          simpa [RingAut.smul_def] using x.property⟩
        left_inv x := Subtype.ext rfl
        right_inv x := Subtype.ext rfl }
      calc
        Nat.card k0 = Nat.card {x : K // J.conj x = x} :=
          Nat.card_congr eFixed
        _ = 2 ^ n := hfixedCard
    calc
      Nat.card T0 = Nat.card k0ˣ := Nat.card_congr eT.toEquiv.symm
      _ = Nat.card k0 - 1 := Nat.card_units k0
      _ = 2 ^ n - 1 := by rw [hk0card]
  have hqGt : 2 < q := by
    dsimp [q]
    change 2 ^ 1 < 2 ^ n
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  obtain ⟨k, _hkNorm, _hkCube, hkne, hkconj⟩ :=
    External.exists_hermitian_norm_one_torus_cube_ne_one
      J q (by simpa [q] using hKcard)
        (by simpa [q] using hfixedCard) hJstandard hqGt
  have hkH : torus k ∈ H := by
    rw [hHrange]
    exact ⟨k, rfl⟩
  have hkw : torus k * w = w * torus k := by
    exact External.hermitianTorusPSU_commute_weyl_of_conj_eq_inv
      J hJstandard k hkconj
  obtain ⟨z, hzne, hzB, hzBt, hzct⟩ :=
    centralizer_borel_inter_rightConjugate_of_standard_pair
      B t ht htB htwo hBpoint alpha0 beta0 halpha0beta0
        w hwalpha hwbeta H hH0set hHcomm (torus k) hkH hkne hkw
  obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
    invertedTorus_of_standard_pair B t ht htB htwo hBpoint
      alpha0 beta0 halpha0beta0 w hwalpha hwbeta H T0
      hH0set hHcomm hT0set hT0cyclic
  exact ⟨⟨T, hTset, hTcyclic, hTcard.trans hT0card⟩,
    z, hzne, hzB, hzBt, hzct⟩

/-- The PSU inverted-torus calculation used by Proposition 8.4. -/
public theorem psu_invertedTorus_of_borel
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (n : ℕ) (hn : 2 ≤ n)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hKcard : Nat.card K = (2 ^ n) ^ 2)
    (hfixedCard : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hB : IsBorelSubgroup B)
    (t : ProjectiveSpecialUnitaryMatrixGroup J)
    (ht : IsInvolution t) (htB : t ∉ B) :
    ∃ T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      (T : Set _) =
          {x | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = 2 ^ n - 1 :=
  (psu_invertedTorus_with_centralizer_of_borel
    J n hn hKcard hfixedCard hJstandard hB t ht htB).1

/-- In the PSU model, an outside involution has a nontrivial centralizer in
the intersection of a Borel subgroup with its conjugate. -/
public theorem psu_exists_nontrivial_borel_inter_rightConjugate_centralizer
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (n : ℕ) (hn : 2 ≤ n)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hKcard : Nat.card K = (2 ^ n) ^ 2)
    (hfixedCard : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hB : IsBorelSubgroup B)
    (t : ProjectiveSpecialUnitaryMatrixGroup J)
    (ht : IsInvolution t) (htB : t ∉ B) :
    ∃ z : ProjectiveSpecialUnitaryMatrixGroup J,
      z ≠ 1 ∧ z ∈ B ∧ z ∈ rightConjugate B t ∧
        z ∈ Subgroup.centralizer ({t} : Set _) :=
  (psu_invertedTorus_with_centralizer_of_borel
    J n hn hKcard hfixedCard hJstandard hB t ht htB).2

public theorem simpleBenderAtExponent_borel_invertedTorus
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n)
    (hG : IsSimpleBenderGroupAtExponent n G)
    {B : Subgroup G} (hB : IsBorelSubgroup B)
    (t : G) (ht : IsInvolution t) (htB : t ∉ B) :
    ∃ T : Subgroup G,
      (T : Set G) =
          {x | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = 2 ^ n - 1 := by
  rcases hG with hPSL | hSuzuki | hPSU
  · rcases hPSL with ⟨e⟩
    have hBQ : IsBorelSubgroup (B.map e.toMonoidHom) :=
      hB.map_mulEquiv e
    have het : IsInvolution (e t) :=
      IsInvolution.map_of_injective ht e.toMonoidHom e.injective
    have hetB : e t ∉ B.map e.toMonoidHom := by
      intro hetB
      apply htB
      simpa using hetB
    obtain ⟨TQ, hTQset, hTQcyclic, hTQcard⟩ :=
      psl_invertedTorus_of_borel n hn hBQ (e t) het hetB
    obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
      invertedTorus_pullback_mulEquiv e B t TQ hTQset hTQcyclic
    exact ⟨T, hTset, hTcyclic, hTcard.trans hTQcard⟩
  · rcases hSuzuki with ⟨m, hnm, ⟨e⟩⟩
    have hm : 0 < m := by omega
    have hBQ : IsBorelSubgroup (B.map e.toMonoidHom) :=
      hB.map_mulEquiv e
    have het : IsInvolution (e t) :=
      IsInvolution.map_of_injective ht e.toMonoidHom e.injective
    have hetB : e t ∉ B.map e.toMonoidHom := by
      intro hetB
      apply htB
      simpa using hetB
    obtain ⟨TQ, hTQset, hTQcyclic, hTQcard⟩ :=
      suzuki_invertedTorus_of_borel m hm hBQ (e t) het hetB
    obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
      invertedTorus_pullback_mulEquiv e B t TQ hTQset hTQcyclic
    have hTQcard' : Nat.card TQ = 2 ^ n - 1 := by
      simpa [hnm] using hTQcard
    exact ⟨T, hTset, hTcyclic, hTcard.trans hTQcard'⟩
  · rcases hPSU with
    ⟨E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, ⟨e⟩⟩
    letI : Field E := hEfield
    letI : Finite E := hEfinite
    letI : Fintype E := Fintype.ofFinite E
    letI : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk
        Matrix.ProjGenLinGroup.mk_surjective
    letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_injective
        (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
          (x : Matrix.ProjGenLinGroup (Fin 3) E)) Subtype.coe_injective
    have hBQ : IsBorelSubgroup (B.map e.toMonoidHom) :=
      hB.map_mulEquiv e
    have het : IsInvolution (e t) :=
      IsInvolution.map_of_injective ht e.toMonoidHom e.injective
    have hetB : e t ∉ B.map e.toMonoidHom := by
      intro hetB
      apply htB
      simpa using hetB
    obtain ⟨TQ, hTQset, hTQcyclic, hTQcard⟩ :=
      psu_invertedTorus_of_borel J n hn hEcard hfixedCard hJ
        hBQ (e t) het hetB
    obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
      invertedTorus_pullback_mulEquiv e B t TQ hTQset hTQcyclic
    exact ⟨T, hTset, hTcyclic, hTcard.trans hTQcard⟩

public theorem proposition84_base_cyclicNormalizer_of_borel_model
    {X : Type u} [Group X] [Finite X]
    (M F N : Subgroup X) (t : X)
    (ht : IsInvolution t) (htM : t ∉ M) (htF : t ∈ F)
    (hFleN : F ≤ N)
    (hcore : twoPrimeCore F = Subgroup.center F)
    (hcoreM : (twoPrimeCore F).map F.subtype ≤ M)
    (hBorel : IsBorelSubgroup
      (((F ⊓ M).subgroupOf F).map
        (QuotientGroup.mk' (twoPrimeCore F))))
    (n : ℕ) (hn : 2 ≤ n)
    (hmodel : IsSimpleBenderGroupAtExponent n
      (F ⧸ twoPrimeCore F))
    (hlocalLeF :
      {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        x ∈ N} ⊆ F) :
    ∃ J : Subgroup X,
      (J : Set X) =
        {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
          x ∈ N} ∧
      IsCyclic J ∧ Nat.card J = 2 ^ n - 1 := by
  let Z : Subgroup F := twoPrimeCore F
  let q : F →* F ⧸ Z := QuotientGroup.mk' Z
  let B0 : Subgroup (F ⧸ Z) := ((F ⊓ M).subgroupOf F).map q
  let tF : F := ⟨t, htF⟩
  have htFInv : IsInvolution tF := IsInvolution.subtype ht htF
  have hqt : IsInvolution (q tF) := by
    constructor
    · intro hqtOne
      have htZ : tF ∈ Z :=
        (QuotientGroup.eq_one_iff tF).mp hqtOne
      apply htM
      exact hcoreM (Subgroup.mem_map_of_mem F.subtype (by
        simpa [Z] using htZ))
    · have hsq := congrArg q htFInv.sq_eq_one
      simpa using hsq
  have hBorel0 : IsBorelSubgroup B0 := by
    simpa [B0, q, Z] using hBorel
  have hqB_iff (x : F) : q x ∈ B0 ↔ (x : X) ∈ M := by
    constructor
    · intro hx
      change q x ∈ ((F ⊓ M).subgroupOf F).map q at hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, hax⟩
      change QuotientGroup.mk' Z a = QuotientGroup.mk' Z x at hax
      rcases (QuotientGroup.mk'_eq_mk' Z).mp hax with ⟨z, hz, haz⟩
      have haM : (a : X) ∈ M := ha.2
      have hzM : (z : X) ∈ M :=
        hcoreM (Subgroup.mem_map_of_mem F.subtype (by
          simpa [Z] using hz))
      have haxX := congrArg (fun y : F => (y : X)) haz
      change (a : X) * (z : X) = (x : X) at haxX
      rw [← haxX]
      exact M.mul_mem haM hzM
    · intro hxM
      change q x ∈ ((F ⊓ M).subgroupOf F).map q
      exact Subgroup.mem_map_of_mem q ⟨x.property, hxM⟩
  have hqtB : q tF ∉ B0 := by
    intro hmem
    exact htM ((hqB_iff tF).mp hmem)
  obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
    simpleBenderAtExponent_borel_invertedTorus n hn
      (by simpa [Z] using hmodel) hBorel0 (q tF) hqt hqtB
  have hTinverted : ∀ x : F ⧸ Z, x ∈ T →
      rightConjugateElem x (q tF) = x⁻¹ := by
    intro x hxT
    exact (Set.ext_iff.mp hTset x).mp hxT |>.2.2
  have hZcenter : Z ≤ Subgroup.center F := by
    dsimp [Z]
    rw [hcore]
  have hZodd : Odd (Nat.card Z) := by
    exact Nat.coprime_two_left.mp (by
      simpa [Z, twoPrimeCore] using
        (pPrimeCore_coprime_card (p := 2) (G := F)))
  obtain ⟨JF, hJFset, hJFcyclic, hJFcard⟩ :=
    invertedTorus_lift_of_central_odd_kernel
      Z hZcenter hZodd tF T hTcyclic hTinverted
  let JX : Subgroup X := JF.map F.subtype
  have hJXset : (JX : Set X) =
      {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        x ∈ N} := by
    ext x
    constructor
    · intro hxJ
      change x ∈ JF.map F.subtype at hxJ
      rcases Subgroup.mem_map.mp hxJ with ⟨xf, hxfJ, rfl⟩
      have hxfLift := (Set.ext_iff.mp hJFset xf).mp hxfJ
      have hqxfT : q xf ∈ T := by
        simpa [q] using hxfLift.1
      have hqxfData := (Set.ext_iff.mp hTset (q xf)).mp hqxfT
      have hxfM : (xf : X) ∈ M := (hqB_iff xf).mp hqxfData.1
      have hxfAnti :
          rightConjugateElem (xf : X) t = (xf : X)⁻¹ := by
        have h := congrArg (fun y : F => (y : X)) hxfLift.2
        change rightConjugateElem (xf : X) t = (xf : X)⁻¹ at h
        exact h
      have hxfInvRight :
          (xf : X)⁻¹ ∈ rightConjugate M t := by
        rw [← hxfAnti]
        exact rightConjugateElem_mem_rightConjugate hxfM
      have hxfRight : (xf : X) ∈ rightConjugate M t := by
        have h := (rightConjugate M t).inv_mem hxfInvRight
        simpa using h
      exact ⟨⟨⟨hxfM, hxfRight⟩, hxfAnti⟩, hFleN xf.property⟩
    · intro hx
      have hxF : x ∈ F := hlocalLeF hx
      let xf : F := ⟨x, hxF⟩
      have hxfM : (xf : X) ∈ M := hx.1.1.1
      have hxfAnti : rightConjugateElem xf tF = xf⁻¹ := by
        apply Subtype.ext
        exact hx.1.2
      have hqxfB : q xf ∈ B0 := (hqB_iff xf).mpr hxfM
      have hqxfAnti :
          rightConjugateElem (q xf) (q tF) = (q xf)⁻¹ := by
        simpa [rightConjugateElem] using congrArg q hxfAnti
      have hqxfRight : q xf ∈ rightConjugate B0 (q tF) := by
        have hqxfInvB : (q xf)⁻¹ ∈ B0 := B0.inv_mem hqxfB
        have hmem := rightConjugateElem_mem_rightConjugate
          (g := q tF) hqxfInvB
        have hconjInv :
            rightConjugateElem (q xf)⁻¹ (q tF) = q xf := by
          calc
            rightConjugateElem (q xf)⁻¹ (q tF) =
                (rightConjugateElem (q xf) (q tF))⁻¹ := by
              simp only [rightConjugateElem]
              group
            _ = ((q xf)⁻¹)⁻¹ := by rw [hqxfAnti]
            _ = q xf := inv_inv _
        rw [hconjInv] at hmem
        exact hmem
      have hqxfT : q xf ∈ T :=
        (Set.ext_iff.mp hTset (q xf)).mpr
          ⟨hqxfB, hqxfRight, hqxfAnti⟩
      have hxfJ : xf ∈ JF :=
        (Set.ext_iff.mp hJFset xf).mpr
          ⟨by simpa [q] using hqxfT, hxfAnti⟩
      change x ∈ JF.map F.subtype
      simpa [xf] using Subgroup.mem_map_of_mem F.subtype hxfJ
  have hJXcyclic : IsCyclic JX := by
    let inclJ : JF →* JX :=
      { toFun := fun x =>
          ⟨(x : X), Subgroup.mem_map_of_mem F.subtype x.property⟩
        map_one' := by apply Subtype.ext; rfl
        map_mul' := by intro x y; apply Subtype.ext; rfl }
    have hinclJ : Function.Surjective inclJ := by
      intro y
      rcases Subgroup.mem_map.mp y.property with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    letI : IsCyclic JF := hJFcyclic
    exact isCyclic_of_surjective inclJ hinclJ
  have hJXcard : Nat.card JX = 2 ^ n - 1 := by
    calc
      Nat.card JX = Nat.card JF := by
        simpa [JX] using
          (Subgroup.card_map_of_injective
            (K := JF) (f := F.subtype) F.subtype_injective)
      _ = Nat.card T := hJFcard
      _ = 2 ^ n - 1 := hTcard
  exact ⟨JX, hJXset, hJXcyclic, hJXcard⟩

end CFSG.BenderSuzuki
