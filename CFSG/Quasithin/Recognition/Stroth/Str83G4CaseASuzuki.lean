module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedPointwise
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleTransport
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint CFSG.LieType.Ree
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.RankThree.GF2n.SzExplicit
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped Matrix commutatorElement

section Module

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem suzukia_suzukiS_map_mulVec (c : ℕ) (u v : K) (w : Fin 4 → K) :
    ((suzukiS a u v).map (· ^ 2 ^ c)).mulVec w =
      ![w 0, u ^ 2 ^ c * w 0 + w 1,
        v ^ 2 ^ c * w 0 + (u ^ 2 ^ (a + 1)) ^ 2 ^ c * w 1 + w 2,
        (suzukiN a u v) ^ 2 ^ c * w 0 +
          (u ^ (2 ^ (a + 1) + 1) + v) ^ 2 ^ c * w 1 + u ^ 2 ^ c * w 2 + w 3] := by
  ext i
  fin_cases i <;>
    simp [suzukiS, suzukiN, Matrix.map_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem caseA_mem_suzukiZ0_of_fixes_fixed
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W)
    (hρ : IsSzNatural ρ) {u : ↥(suzukiGroup a K)} (hu : u ∈ suzukiU a K)
    (hfix : ∀ w : W, (∀ z ∈ suzukiZ0 a K, ρ z w = w) → ρ u w = w) : u ∈ suzukiZ0 a K := by
  obtain ⟨c, φ, hφ⟩ := hρ
  obtain ⟨u1, u2, hu_eq⟩ := (mem_suzukiU_iff hK).1 hu
  have hu1 : u1 = 0 := by
    let w : W := φ.symm ![0, 0, 1, 0]
    have hw : w ∈ fixedSub ρ (suzukiZ0 a K) := by
      rw [mem_fixedSub_suzukiZ0_iff hK ρ hφ]
      have hφw : φ w = ![0, 0, 1, 0] := AddEquiv.apply_symm_apply φ ![0, 0, 1, 0]
      rw [hφw]
      simp
    have hfixw : ρ u w = w := hfix w (mem_fixedSub.mp hw)
    have hfix' : ρ (suzukiSElt a K u1 u2) w = w := by
      rw [hu_eq]
      exact hfixw
    have hcoord : ((suzukiS a u1 u2).map (· ^ 2 ^ c)).mulVec (φ w) = φ w := by
      have h := congrArg φ hfix'
      rw [hφ (suzukiSElt a K u1 u2) w, coe_suzukiSElt] at h
      exact h
    have h3 : u1 ^ 2 ^ c = 0 := by
      have h := congrFun hcoord 3
      have hφw : φ w = ![0, 0, 1, 0] := AddEquiv.apply_symm_apply φ ![0, 0, 1, 0]
      rw [hφw, suzukia_suzukiS_map_mulVec] at h
      simpa using h
    exact (pow_eq_zero_iff'.mp h3).1
  rw [← hu_eq, hu1]
  exact (mem_suzukiZ0_iff hK).2 ⟨u2, rfl⟩

end Module

section Sylow

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem suzukib_exteriorSquareJ_map (c : ℕ) :
    (CFSG.LinearAlgebra.exteriorSquareJ K).map (· ^ 2 ^ c) =
      CFSG.LinearAlgebra.exteriorSquareJ K := by
  ext i j
  rw [Matrix.map_apply, CFSG.LinearAlgebra.exteriorSquareJ_apply]
  split_ifs with h
  · simp [h]
  · simp [h, zero_pow (pow_ne_zero c two_ne_zero)]

private theorem suzukib_isSzNatural_conj
    {ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W} (hρ : IsSzNatural ρ)
    (g : ↥(suzukiGroup a K)) :
    IsSzNatural (ρ.comp (MulAut.conj g).toMonoidHom) := by
  obtain ⟨c, φ, hφ⟩ := hρ
  refine ⟨c, (((CFSG.CGT.PushingUpLit.SolKNA.repToHom ρ (g⁻¹)).toAddEquiv).trans φ), ?_⟩
  intro y w
  have hcoe : ((CFSG.CGT.PushingUpLit.SolKNA.repToHom ρ (g⁻¹) : W ≃ₗ[ZMod 2] W) :
      W →ₗ[ZMod 2] W) = ρ (g⁻¹) :=
    CFSG.CGT.PushingUpLit.SolKNA.repOfG_repToHom ρ (g⁻¹)
  have hcoe_fun : ∀ x : W,
      (CFSG.CGT.PushingUpLit.SolKNA.repToHom ρ (g⁻¹) : W ≃ₗ[ZMod 2] W) x = ρ (g⁻¹) x :=
    fun x => congrArg (fun f : W →ₗ[ZMod 2] W => f x) hcoe
  have h1 : ρ (g⁻¹) ((ρ.comp (MulAut.conj g).toMonoidHom) y w) = ρ y (ρ (g⁻¹) w) := by
    have hmul : ρ (g⁻¹) * (ρ.comp (MulAut.conj g).toMonoidHom) y = ρ y * ρ (g⁻¹) := by
      have h1 : (ρ.comp (MulAut.conj g).toMonoidHom) y = ρ (MulAut.conj g y) := rfl
      rw [h1, ← map_mul, ← map_mul]
      congr 1
      rw [MulAut.conj_apply]
      group
    calc ρ (g⁻¹) ((ρ.comp (MulAut.conj g).toMonoidHom) y w)
        = (ρ (g⁻¹) * (ρ.comp (MulAut.conj g).toMonoidHom) y) w := rfl
      _ = (ρ y * ρ (g⁻¹)) w := by rw [hmul]
      _ = ρ y (ρ (g⁻¹) w) := rfl
  show φ ((CFSG.CGT.PushingUpLit.SolKNA.repToHom ρ (g⁻¹))
      ((ρ.comp (MulAut.conj g).toMonoidHom) y w)) =
    (((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ
      φ ((CFSG.CGT.PushingUpLit.SolKNA.repToHom ρ (g⁻¹)) w)
  rw [hcoe_fun, h1]
  exact hφ y (ρ (g⁻¹) w)

private theorem suzukib_J_mul_szEquiv {a : ℕ} (c : ℕ) (y : ↥(suzukiGroup a (F a))) :
    CFSG.LinearAlgebra.exteriorSquareJ (F a) *
        (((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a y : ↥(Sz a)) : GL (Fin 4) (F a)) :
          Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c) =
      (((y : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c)) *
        CFSG.LinearAlgebra.exteriorSquareJ (F a) := by
  haveI : Fintype (F a) := Fintype.ofFinite _
  have hJ : CFSG.LinearAlgebra.exteriorSquareJ (F a) *
      CFSG.LinearAlgebra.exteriorSquareJ (F a) = 1 :=
    CFSG.CGT.PushingUpLit.SolKNA.exteriorSquareJ_mul_self (F a)
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (F a) => M.map (· ^ 2 ^ c))
    (CFSG.CGT.PushingUpLit.SolKNA.szEquiv_mul_J a y)
  rw [matrix_map_pow_mul, matrix_map_pow_mul,
    suzukib_exteriorSquareJ_map (K := F a) c] at h
  let Ms := (((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a y : ↥(Sz a)) :
    GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c)
  let My := (((y : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c))
  have hh : Ms * CFSG.LinearAlgebra.exteriorSquareJ (F a) =
      CFSG.LinearAlgebra.exteriorSquareJ (F a) * My := h
  calc CFSG.LinearAlgebra.exteriorSquareJ (F a) * Ms
      = CFSG.LinearAlgebra.exteriorSquareJ (F a) * Ms *
          (CFSG.LinearAlgebra.exteriorSquareJ (F a) *
            CFSG.LinearAlgebra.exteriorSquareJ (F a)) := by
        rw [hJ, mul_one]
    _ = CFSG.LinearAlgebra.exteriorSquareJ (F a) *
          (Ms * CFSG.LinearAlgebra.exteriorSquareJ (F a)) *
            CFSG.LinearAlgebra.exteriorSquareJ (F a) := by
        simp only [mul_assoc]
    _ = CFSG.LinearAlgebra.exteriorSquareJ (F a) *
          (CFSG.LinearAlgebra.exteriorSquareJ (F a) * My) *
            CFSG.LinearAlgebra.exteriorSquareJ (F a) := by rw [hh]
    _ = (CFSG.LinearAlgebra.exteriorSquareJ (F a) *
          CFSG.LinearAlgebra.exteriorSquareJ (F a)) * My *
            CFSG.LinearAlgebra.exteriorSquareJ (F a) := by
        simp only [mul_assoc]
    _ = My * CFSG.LinearAlgebra.exteriorSquareJ (F a) := by rw [hJ, one_mul]

private noncomputable def suzukib_twistedRep (a : ℕ) (c : ℕ) :
    Representation (ZMod 2) ↥(suzukiGroup a (F a)) (Fin 4 → F a) where
  toFun y := Matrix.mulVecLin ((((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a y : ↥(Sz a)) :
      GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c))
  map_one' := by
    have hco : (((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a 1 : ↥(Sz a)) : GL (Fin 4) (F a)) :
        Matrix (Fin 4) (Fin 4) (F a)) = 1 := by
      rw [map_one]; rfl
    rw [hco, Matrix.map_one _ (by simp) (by simp), Matrix.mulVecLin_one]
    rfl
  map_mul' y z := by
    have hco : (((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a (y * z) : ↥(Sz a)) :
        GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
        (((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a y : ↥(Sz a)) : GL (Fin 4) (F a)) :
          Matrix (Fin 4) (Fin 4) (F a)) *
        (((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a z : ↥(Sz a)) : GL (Fin 4) (F a)) :
          Matrix (Fin 4) (Fin 4) (F a)) := by
      simp only [map_mul, Subgroup.coe_mul, Units.val_mul]
    rw [hco, matrix_map_pow_mul, Matrix.mulVecLin_mul]
    rfl

private theorem suzukib_isSzNatural_twistedRep (a : ℕ) (c : ℕ) :
    IsSzNatural (suzukib_twistedRep a c) := by
  have hJ : CFSG.LinearAlgebra.exteriorSquareJ (F a) *
      CFSG.LinearAlgebra.exteriorSquareJ (F a) = 1 :=
    CFSG.CGT.PushingUpLit.SolKNA.exteriorSquareJ_mul_self (F a)
  let ψ : (Fin 4 → F a) ≃+ (Fin 4 → F a) :=
    { toFun := Matrix.mulVecLin (CFSG.LinearAlgebra.exteriorSquareJ (F a))
      invFun := Matrix.mulVecLin (CFSG.LinearAlgebra.exteriorSquareJ (F a))
      left_inv := fun v => by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec]
      right_inv := fun v => by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec]
      map_add' := fun v w =>
        (Matrix.mulVecLin (CFSG.LinearAlgebra.exteriorSquareJ (F a))).map_add v w }
  refine ⟨c, ψ, ?_⟩
  intro y w
  show Matrix.mulVecLin (CFSG.LinearAlgebra.exteriorSquareJ (F a))
      ((Matrix.mulVecLin ((((CFSG.CGT.PushingUpLit.SolKNA.szEquiv a y : ↥(Sz a)) :
        GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c))) w) =
    (((y : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c)) *ᵥ
      Matrix.mulVecLin (CFSG.LinearAlgebra.exteriorSquareJ (F a)) w
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec]
  rw [suzukib_J_mul_szEquiv c y, Matrix.mulVec_mulVec]

private theorem suzukib_omegaOne_conj_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : ↥(suzukiGroup a K)) :
    (CFSG.omega₁ (G := (suzukiU a K).map (MulAut.conj g).toMonoidHom) (p := 2)).map
        ((suzukiU a K).map (MulAut.conj g).toMonoidHom).subtype =
      (suzukiZ0 a K).map (MulAut.conj g).toMonoidHom := by
  rw [← CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.map_omega₁_suzukiU (a := a) (K := K) hK]
  exact (CFSG.ProperTwoGeneratedCore.RootCenter.map_omega₁_map (MulAut.conj g)
    (suzukiU a K)).symm

private theorem suzukib_range_sub_one_eq_fixedSub_conj
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ)
    (g : ↥(suzukiGroup a K)) {z : ↥(suzukiGroup a K)}
    (hz : z ∈ (suzukiZ0 a K).map (MulAut.conj g).toMonoidHom) (hz1 : z ≠ 1) :
    LinearMap.range (ρ z - 1) =
      fixedSub ρ ((suzukiZ0 a K).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨z', hz', hz_eq⟩ := Subgroup.mem_map.mp hz
  have hz_eq' : MulAut.conj g z' = z := by
    simpa only [MulEquiv.coe_toMonoidHom] using hz_eq
  have hz'1 : z' ≠ 1 := by
    intro h; exact hz1 (by rw [← hz_eq, h, map_one])
  have h := range_sub_one_eq_fixedSub_suzukiZ0 (a := a) (K := K) hK
    (ρ.comp (MulAut.conj g).toMonoidHom) (suzukib_isSzNatural_conj hρ g) hz' hz'1
  have hρz : (ρ.comp (MulAut.conj g).toMonoidHom) z' = ρ z := by
    rw [show (ρ.comp (MulAut.conj g).toMonoidHom) z' = ρ (MulAut.conj g z') from rfl,
      hz_eq']
  rw [hρz] at h
  have hfix : fixedSub (ρ.comp (MulAut.conj g).toMonoidHom) (suzukiZ0 a K) =
      fixedSub ρ ((suzukiZ0 a K).map (MulAut.conj g).toMonoidHom) := by
    ext w
    rw [mem_fixedSub, mem_fixedSub]
    constructor
    · intro hw z hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      exact hw z' hz'
    · intro hw z' hz'
      exact hw _ (Subgroup.mem_map_of_mem _ hz')
  rw [hfix] at h
  exact h

private theorem suzukib_mem_omegaOne_conj_of_fixes_fixed
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ)
    (g : ↥(suzukiGroup a K)) {u : ↥(suzukiGroup a K)}
    (hu : u ∈ (suzukiU a K).map (MulAut.conj g).toMonoidHom)
    (hfix : ∀ w : W, w ∈ fixedSub ρ ((suzukiZ0 a K).map (MulAut.conj g).toMonoidHom) →
      ρ u w = w) :
    u ∈ (suzukiZ0 a K).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨u', hu', hu_eq⟩ := Subgroup.mem_map.mp hu
  have hu_eq' : MulAut.conj g u' = u := by
    simpa only [MulEquiv.coe_toMonoidHom] using hu_eq
  have hfix' : ∀ w : W, (∀ z ∈ suzukiZ0 a K,
      (ρ.comp (MulAut.conj g).toMonoidHom) z w = w) →
      (ρ.comp (MulAut.conj g).toMonoidHom) u' w = w := by
    intro w hw
    have hmem : w ∈ fixedSub ρ ((suzukiZ0 a K).map (MulAut.conj g).toMonoidHom) := by
      rw [mem_fixedSub]
      intro z hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      exact hw z' hz'
    have huw := hfix w hmem
    rw [show (ρ.comp (MulAut.conj g).toMonoidHom) u' = ρ u by
      rw [show (ρ.comp (MulAut.conj g).toMonoidHom) u' = ρ (MulAut.conj g u') from rfl,
        hu_eq']]
    exact huw
  exact Subgroup.mem_map.mpr ⟨u', caseA_mem_suzukiZ0_of_fixes_fixed hK
    (ρ.comp (MulAut.conj g).toMonoidHom) (suzukib_isSzNatural_conj hρ g) hu' hfix', hu_eq⟩

end Sylow

section Section

variable {G : Type} [Group G] [Finite G]

theorem caseA_le_sup_pCoreOf_of_natural_section
    {H N M T A E : Subgroup G} {a : ℕ} (ha : 1 ≤ a) (hnat : IsSzNaturalSection H N M a)
    (hHN : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) (hT : IsSylowTwoOf T H) (hAT : A ≤ T)
    (hET : E ≤ T) (hA : ∀ s : G, s ∈ A ⊔ pCoreOf 2 H ↔ s ∈ T ∧ s ^ 2 ∈ pCoreOf 2 H)
    (hAne : ¬ A ≤ pCoreOf 2 H) (hcomm : ⁅⁅N, A⁆, E⁆ ≤ M) : E ≤ A ⊔ pCoreOf 2 H := by
  classical
  have hK : Nat.card (F a) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (F a) := Fintype.ofFinite _
  obtain ⟨e, c, φ, hφsurj, hφker, hφform⟩ := hnat
  let e' : oTwoQuot ↥H ≃* ↥(suzukiGroup a (F a)) :=
    e.trans (CFSG.CGT.PushingUpLit.SolKNA.szEquiv a).symm
  let mk : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
  let Tq : Subgroup (oTwoQuot ↥H) := (T.subgroupOf H).map mk
  let Aq : Subgroup (oTwoQuot ↥H) := (A.subgroupOf H).map mk
  let Eq : Subgroup (oTwoQuot ↥H) := (E.subgroupOf H).map mk
  let ρ : Representation (ZMod 2) ↥(suzukiGroup a (F a)) (Fin 4 → F a) :=
    suzukib_twistedRep a c
  have hρ : IsSzNatural ρ := suzukib_isSzNatural_twistedRep a c
  haveI : Finite ↥(suzukiGroup a (F a)) := CFSG.LieType.Ree.finite_suzukiGroup hK
  have hQleT : pCoreOf 2 H ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT
  let S : Sylow 2 ↥H := CFSG.Quasithin.A4.toSylow hT
  have hScoe : (S : Subgroup ↥H) = T.subgroupOf H := CFSG.Quasithin.A4.toSylow_coe hT
  let TqS : Sylow 2 (oTwoQuot ↥H) :=
    S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 ↥H))
  have hTqScoe : (TqS : Subgroup (oTwoQuot ↥H)) = Tq := by
    rw [Sylow.coe_mapSurjective, hScoe]
  have hTq : IsSylowTwoOf Tq ⊤ := hTqScoe ▸
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow TqS
  let P : Subgroup ↥(suzukiGroup a (F a)) := Tq.map e'.toMonoidHom
  have hP : IsSylowTwoOf P ⊤ := by
    have htop : (⊤ : Subgroup (oTwoQuot ↥H)).map e'.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective e'.toMonoidHom
        (fun x => ⟨e'.symm x, by simp⟩)
    have h := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e').2 hTq
    rw [htop] at h
    simpa [P] using h
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.A4.exists_conj_of_isSylowTwoOf
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK) hP
  have hP_eq : P = (suzukiU a (F a)).map (MulAut.conj g).toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, (hg x).mp hx, ?_⟩
      change (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]; group
    · intro hx
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hx
      rw [← hye]
      exact (hg ((MulAut.conj g) y)).mpr (by
        change g⁻¹ * (MulAut.conj g) y * g ∈ suzukiU a (F a)
        rw [show g⁻¹ * (MulAut.conj g) y * g = y by
          rw [MulAut.conj_apply]; group]
        exact hy)
  have hQsub : (pCoreOf 2 H).subgroupOf H = pCore 2 ↥H := by
    ext x
    rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.F1.mem_pCore_iff_coe]
  have hQq : ((pCoreOf 2 H).subgroupOf H).map mk = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact (QuotientGroup.eq_one_iff y).mpr (hQsub ▸ hy)
  have hAq : Aq = (CFSG.omega₁ (G := Tq) (p := 2)).map Tq.subtype := by
    rw [CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.map_omega₁_subtype]
    apply le_antisymm
    · rintro x ⟨a, haA, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨a, hAT (Subgroup.mem_subgroupOf.mp haA), rfl⟩
      · have haA' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp haA
        have hsq : (a : G) ^ 2 ∈ pCoreOf 2 H :=
          ((hA (a : G)).mp (Subgroup.mem_sup_left haA')).2
        have hsqH : a * a ∈ pCore 2 ↥H :=
          (CFSG.Quasithin.F1.mem_pCore_iff_coe (a * a)).mpr (by simpa [pow_two] using hsq)
        show (mk a) ^ 2 = 1
        rw [pow_two, ← map_mul]
        exact (QuotientGroup.eq_one_iff (a * a)).mpr hsqH
    · rw [Subgroup.closure_le]
      rintro x ⟨hxT, hx2⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hxT
      have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
      have ht2 : (t : G) ^ 2 ∈ pCoreOf 2 H := by
        have h1 : t * t ∈ pCore 2 ↥H := by
          apply (QuotientGroup.eq_one_iff (t * t)).mp
          change mk (t * t) = 1
          rw [pow_two, ← map_mul] at hx2
          exact hx2
        simpa [pow_two] using (CFSG.Quasithin.F1.mem_pCore_iff_coe (t * t)).mp h1
      have htmem : (t : G) ∈ A ⊔ pCoreOf 2 H := (hA (t : G)).mpr ⟨htT, ht2⟩
      have htmem' : t ∈ (A ⊔ pCoreOf 2 H).subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr htmem
      have hmap : ((A ⊔ pCoreOf 2 H).subgroupOf H).map mk = Aq := by
        rw [Subgroup.subgroupOf_sup (le_trans hAT hT.1) (le_trans hQleT hT.1),
          Subgroup.map_sup, hQq, sup_bot_eq]
      have hthis : mk t ∈ ((A ⊔ pCoreOf 2 H).subgroupOf H).map mk :=
        Subgroup.mem_map.mpr ⟨t, htmem', rfl⟩
      rwa [hmap] at hthis
  have hZ : (CFSG.omega₁ (G := P) (p := 2)).map P.subtype =
      (suzukiZ0 a (F a)).map (MulAut.conj g).toMonoidHom := by
    rw [hP_eq]
    exact suzukib_omegaOne_conj_suzukiU (a := a) (K := F a) hK g
  have hA' : Aq.map e'.toMonoidHom = (CFSG.omega₁ (G := P) (p := 2)).map P.subtype := by
    rw [hAq]
    exact CFSG.ProperTwoGeneratedCore.RootCenter.map_omega₁_map e' Tq
  have hZ' : (suzukiZ0 a (F a)).map (MulAut.conj g).toMonoidHom = Aq.map e'.toMonoidHom :=
    hZ.symm.trans hA'.symm
  obtain ⟨a₀, ha₀A, ha₀ne⟩ := SetLike.not_le_iff_exists.mp hAne
  have ha₀H : a₀ ∈ H := hT.1 (hAT ha₀A)
  let aH : ↥H := ⟨a₀, ha₀H⟩
  have haH_sub : aH ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr ha₀A
  have hā'mem : e' (mk aH) ∈ Aq.map e'.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨mk aH, Subgroup.mem_map.mpr ⟨aH, haH_sub, rfl⟩, rfl⟩
  have hā'ne : e' (mk aH) ≠ 1 := by
    intro h
    have h1 : mk aH = 1 := e'.injective (by rw [h, map_one])
    exact ha₀ne ((CFSG.Quasithin.F1.mem_pCore_iff_coe aH).mp
      ((QuotientGroup.eq_one_iff aH).mp h1))
  have hā'conj : e' (mk aH) ∈ (suzukiZ0 a (F a)).map (MulAut.conj g).toMonoidHom := by
    rw [hZ']; exact hā'mem
  have hrange : LinearMap.range (ρ (e' (mk aH)) - 1) =
      fixedSub ρ ((suzukiZ0 a (F a)).map (MulAut.conj g).toMonoidHom) :=
    suzukib_range_sub_one_eq_fixedSub_conj (a := a) (K := F a) hK ρ hρ g hā'conj hā'ne
  have hEqφ : ∀ (h : ↥H) (x y : ↥N), (y : G) = (h : G) * (x : G) * (h : G)⁻¹ →
      Multiplicative.toAdd (φ y) = ρ (e' (mk h)) (Multiplicative.toAdd (φ x)) := by
    intro h x y hy
    have h1 := hφform h x y hy
    have heq : e (QuotientGroup.mk h) =
        CFSG.CGT.PushingUpLit.SolKNA.szEquiv a (e' (mk h)) := by
      have h2 : e' (mk h) =
          (CFSG.CGT.PushingUpLit.SolKNA.szEquiv a).symm (e (mk h)) := rfl
      rw [h2, MulEquiv.apply_symm_apply, QuotientGroup.mk'_apply]
    rw [h1, heq]
    rfl
  have hcentral : ∀ eH : ↥H, (eH : G) ∈ E →
      ∀ w : Fin 4 → F a, w ∈ LinearMap.range (ρ (e' (mk aH)) - 1) →
        ρ (e' (mk eH)) w = w := by
    intro eH heE w hw
    obtain ⟨v, rfl⟩ := hw
    obtain ⟨n, hn⟩ := hφsurj (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (φ n) := by rw [hn]; rfl
    rw [hv]
    have han : (aH : G) * (n : G) * (aH : G)⁻¹ ∈ N :=
      hHN (aH : G) aH.2 (n : G) n.2
    have hc1 : ⁅(aH : G), (n : G)⁆ ∈ N := by
      have h1 : ⁅(aH : G), (n : G)⁆ =
          ((aH : G) * (n : G) * (aH : G)⁻¹) * (n : G)⁻¹ := rfl
      rw [h1]
      exact Subgroup.mul_mem N han (Subgroup.inv_mem N n.2)
    have hc1' : (eH : G) * ⁅(aH : G), (n : G)⁆ * (eH : G)⁻¹ ∈ N :=
      hHN (eH : G) eH.2 _ hc1
    have hc2 : ⁅(eH : G), ⁅(aH : G), (n : G)⁆⁆ ∈ N := by
      have h1 : ⁅(eH : G), ⁅(aH : G), (n : G)⁆⁆ =
          ((eH : G) * ⁅(aH : G), (n : G)⁆ * (eH : G)⁻¹) * (⁅(aH : G), (n : G)⁆)⁻¹ := rfl
      rw [h1]
      exact Subgroup.mul_mem N hc1' (Subgroup.inv_mem N hc1)
    let c1 : ↥N := ⟨⁅(aH : G), (n : G)⁆, hc1⟩
    let c2 : ↥N := ⟨⁅(eH : G), ⁅(aH : G), (n : G)⁆⁆, hc2⟩
    have hc2M : (c2 : G) ∈ M := by
      have h1 : (c2 : G) ∈ ⁅E, ⁅N, A⁆⁆ := by
        change ⁅(eH : G), ⁅(aH : G), (n : G)⁆⁆ ∈ ⁅E, ⁅N, A⁆⁆
        rw [Subgroup.commutator_comm N A]
        exact Subgroup.commutator_mem_commutator heE
          (Subgroup.commutator_mem_commutator ha₀A n.2)
      have h2 : ⁅E, ⁅N, A⁆⁆ ≤ M := by
        rw [Subgroup.commutator_comm]
        exact hcomm
      exact h2 h1
    have hφc2 : φ c2 = 1 := by
      have hmem : c2 ∈ φ.ker := by
        rw [hφker]
        exact Subgroup.mem_subgroupOf.mpr hc2M
      exact MonoidHom.mem_ker.mp hmem
    have hstep1 : (ρ (e' (mk aH)) - 1) (Multiplicative.toAdd (φ n)) =
        Multiplicative.toAdd (φ c1) := by
      have h1 := hEqφ aH n ⟨(aH : G) * (n : G) * (aH : G)⁻¹, han⟩ rfl
      have h2 : (⟨(aH : G) * (n : G) * (aH : G)⁻¹, han⟩ : ↥N) * n⁻¹ = c1 := by
        apply Subtype.ext
        show ((aH : G) * (n : G) * (aH : G)⁻¹) * (n : G)⁻¹ = ⁅(aH : G), (n : G)⁆
        rfl
      calc (ρ (e' (mk aH)) - 1) (Multiplicative.toAdd (φ n))
          = ρ (e' (mk aH)) (Multiplicative.toAdd (φ n)) -
              Multiplicative.toAdd (φ n) := rfl
        _ = Multiplicative.toAdd (φ ⟨(aH : G) * (n : G) * (aH : G)⁻¹, han⟩) -
              Multiplicative.toAdd (φ n) := by rw [h1]
        _ = Multiplicative.toAdd (φ (⟨(aH : G) * (n : G) * (aH : G)⁻¹, han⟩ * n⁻¹)) := by
            rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
            abel
        _ = Multiplicative.toAdd (φ c1) := by rw [h2]
    have hstep2 : ρ (e' (mk eH)) (Multiplicative.toAdd (φ c1)) =
        Multiplicative.toAdd (φ c1) := by
      have h1 := hEqφ eH c1 ⟨(eH : G) * (c1 : G) * (eH : G)⁻¹, hc1'⟩ rfl
      have h2 : (⟨(eH : G) * (c1 : G) * (eH : G)⁻¹, hc1'⟩ : ↥N) = c2 * c1 := by
        apply Subtype.ext
        change (eH : G) * (c1 : G) * (eH : G)⁻¹ = (c2 : G) * (c1 : G)
        rw [show (c1 : G) = ⁅(aH : G), (n : G)⁆ from rfl,
          show (c2 : G) = ⁅(eH : G), ⁅(aH : G), (n : G)⁆⁆ from rfl]
        group
      calc ρ (e' (mk eH)) (Multiplicative.toAdd (φ c1))
          = Multiplicative.toAdd (φ ⟨(eH : G) * (c1 : G) * (eH : G)⁻¹, hc1'⟩) := h1.symm
        _ = Multiplicative.toAdd (φ (c2 * c1)) := by rw [h2]
        _ = Multiplicative.toAdd (φ c2 * φ c1) := by rw [map_mul]
        _ = Multiplicative.toAdd (φ c2) + Multiplicative.toAdd (φ c1) := by
            rw [toAdd_mul]
        _ = Multiplicative.toAdd (φ c1) := by
            rw [hφc2, toAdd_one, zero_add]
    rw [hstep1]
    exact hstep2
  have hE' : Eq.map e'.toMonoidHom ≤ Aq.map e'.toMonoidHom := by
    rintro z ⟨x, hxEq, rfl⟩
    obtain ⟨eH, heH, rfl⟩ := Subgroup.mem_map.mp hxEq
    have heE : (eH : G) ∈ E := Subgroup.mem_subgroupOf.mp heH
    have hfix : ∀ w : Fin 4 → F a,
        w ∈ fixedSub ρ ((suzukiZ0 a (F a)).map (MulAut.conj g).toMonoidHom) →
          ρ (e' (mk eH)) w = w := by
      intro w hw
      rw [← hrange] at hw
      exact hcentral eH heE w hw
    have hu : e' (mk eH) ∈ (suzukiU a (F a)).map (MulAut.conj g).toMonoidHom := by
      rw [← hP_eq]
      exact Subgroup.mem_map.mpr ⟨mk eH,
        Subgroup.mem_map.mpr ⟨eH, Subgroup.mem_subgroupOf.mpr (hET heE), rfl⟩, rfl⟩
    have hres := suzukib_mem_omegaOne_conj_of_fixes_fixed (a := a) (K := F a) hK ρ hρ g hu hfix
    rwa [hZ'] at hres
  have hEq_le_Aq : Eq ≤ Aq := by
    intro x hx
    have hx' : e' x ∈ Eq.map e'.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp (hE' hx')
    rw [e'.injective hye] at hy
    exact hy
  intro e0 he0
  have he0H : e0 ∈ H := hT.1 (hET he0)
  let eH : ↥H := ⟨e0, he0H⟩
  have heH : eH ∈ E.subgroupOf H := Subgroup.mem_subgroupOf.mpr he0
  have hmk : mk eH ∈ Eq := Subgroup.mem_map.mpr ⟨eH, heH, rfl⟩
  have hAqmem : mk eH ∈ Aq := hEq_le_Aq hmk
  obtain ⟨aH', haH', haH'eq⟩ := Subgroup.mem_map.mp hAqmem
  have haA : (aH' : G) ∈ A := Subgroup.mem_subgroupOf.mp haH'
  have hd : (aH' : G)⁻¹ * e0 ∈ pCoreOf 2 H := by
    have h1 : aH'⁻¹ * eH ∈ pCore 2 ↥H := by
      apply (QuotientGroup.eq_one_iff (aH'⁻¹ * eH)).mp
      change mk (aH'⁻¹ * eH) = 1
      rw [map_mul, map_inv, haH'eq, inv_mul_cancel]
    have h2 := (CFSG.Quasithin.F1.mem_pCore_iff_coe (aH'⁻¹ * eH)).mp h1
    simpa using h2
  have heq : e0 = (aH' : G) * ((aH' : G)⁻¹ * e0) := by group
  rw [heq]
  have h1 : (aH' : G) ∈ A ⊔ pCoreOf 2 H := Subgroup.mem_sup_left haA
  have h2 : (aH' : G)⁻¹ * e0 ∈ A ⊔ pCoreOf 2 H := Subgroup.mem_sup_right hd
  exact (A ⊔ pCoreOf 2 H).mul_mem h1 h2


end Section

end CFSG.Quasithin.Stroth

end
