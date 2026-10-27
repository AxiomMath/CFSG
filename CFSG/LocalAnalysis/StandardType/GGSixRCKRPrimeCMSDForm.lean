module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LinearAlgebra.SelfAdjointIdempotent
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes

private noncomputable abbrev rckSD_A {n g : ℕ} (s : GL (Fin n) (PSUF g)) :
    Subalgebra (PSUF g) (Matrix (Fin n) (Fin n) (PSUF g)) :=
  Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))

private lemma rckSD_uForm_adjoint_mulVec {n g : ℕ}
    (M N : Matrix (Fin n) (Fin n) (PSUF g))
    (hMN : Unitary.antidiag n * N =
      Matrix.transpose (M.map (PSUσ g).toRingHom) * Unitary.antidiag n)
    (x y : Fin n → PSUF g) :
    CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) (Matrix.mulVec M x) y =
      CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) x (Matrix.mulVec N y) := by
  let σ : PSUF g →+* PSUF g := (PSUσ g).toRingHom
  let G : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  have hσM : (fun i => σ (Matrix.mulVec M x i)) =
      Matrix.mulVec (M.map σ) (fun i => σ (x i)) := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
    simp only [Matrix.map_apply, map_sum, map_mul]
  have hmain : dotProduct (Matrix.mulVec (M.map σ) (fun i => σ (x i)))
        (Matrix.mulVec G y) =
      dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec N y)) := by
    calc dotProduct (Matrix.mulVec (M.map σ) (fun i => σ (x i))) (Matrix.mulVec G y)
        = dotProduct (Matrix.mulVec G y) (Matrix.mulVec (M.map σ) (fun i => σ (x i))) :=
          dotProduct_comm _ _
      _ = dotProduct (fun i => σ (x i))
            (Matrix.mulVec (Matrix.transpose (M.map σ)) (Matrix.mulVec G y)) :=
          (Matrix.dotProduct_transpose_mulVec (M.map σ) (fun i => σ (x i))
            (Matrix.mulVec G y)).symm
      _ = dotProduct (fun i => σ (x i))
            (Matrix.mulVec (Matrix.transpose (M.map σ) * G) y) := by rw [Matrix.mulVec_mulVec]
      _ = dotProduct (fun i => σ (x i)) (Matrix.mulVec (G * N) y) := by rw [← hMN]
      _ = dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec N y)) := by
          rw [Matrix.mulVec_mulVec]
  change dotProduct (fun i => σ (Matrix.mulVec M x i)) (Matrix.mulVec G y) =
    dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec N y))
  rw [hσM]
  exact hmain

private noncomputable def rckSD_blockForm {n g : ℕ}
    (ε : Matrix (Fin n) (Fin n) (PSUF g)) :
    (LinearMap.range (Matrix.mulVecLin ε)) →ₛₗ[(PSUσ g).toRingHom]
      (LinearMap.range (Matrix.mulVecLin ε)) →ₗ[PSUF g] PSUF g :=
  (Matrix.toLinearMapₛₗ₂ (PSUσ g).toRingHom
      (Pi.basisFun (PSUF g) (Fin n)) (Pi.basisFun (PSUF g) (Fin n))
      (Unitary.antidiag n)).domRestrict₁₂
    (LinearMap.range (Matrix.mulVecLin ε)) (LinearMap.range (Matrix.mulVecLin ε))

private lemma rckSD_blockForm_apply {n g : ℕ}
    (ε : Matrix (Fin n) (Fin n) (PSUF g))
    (x y : LinearMap.range (Matrix.mulVecLin ε)) :
    rckSD_blockForm ε x y =
      CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) := by
  change Matrix.toLinearMapₛₗ₂ (PSUσ g).toRingHom (Pi.basisFun (PSUF g) (Fin n))
      (Pi.basisFun (PSUF g) (Fin n)) (Unitary.antidiag n)
      (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
    (fun i => (PSUσ g).toRingHom ((x : Fin n → PSUF g) i)) ⬝ᵥ
      (Matrix.mulVec (Unitary.antidiag n) (y : Fin n → PSUF g))
  simp only [Matrix.toLinearMapₛₗ₂_apply, Pi.basisFun_repr, smul_eq_mul, dotProduct,
    Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma rckSD_pi_eq_zero_iff {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hεne : ε ≠ 0)
    {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    {π : rckSD_A s →ₐ[PSUF g] K}
    (hπ : RCKBlockCoord {s} ε K π) :
    ∀ a : rckSD_A s, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) (PSUF g)) * ε = 0 := by
  intro a
  constructor
  · intro ha
    have hzero : ∀ v : Fin n → PSUF g,
        Matrix.mulVec (a : Matrix (Fin n) (Fin n) (PSUF g)) (Matrix.mulVec ε v) = 0 := by
      intro v
      have h1 := hπ.2.1 a
        (⟨Matrix.mulVec ε v, ⟨v, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin ε))
      rw [ha, zero_smul] at h1
      exact h1.symm
    ext i j
    have h := hzero (Pi.single j 1)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact congrFun h i
  · intro hae
    have hact0 : ∀ w : LinearMap.range (Matrix.mulVecLin ε), (π a) • w = 0 := by
      intro w
      apply Subtype.ext
      rw [hπ.2.1 a w]
      obtain ⟨v, hv⟩ := w.2
      rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hae, Matrix.zero_mulVec]
      rfl
    have hWne : ∃ w : LinearMap.range (Matrix.mulVecLin ε), w ≠ 0 := by
      by_contra h
      exfalso
      apply hεne
      ext i j
      by_contra hij
      have hwne : (⟨Matrix.mulVec ε (Pi.single j 1),
          ⟨Pi.single j 1, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin ε)) ≠ 0 := by
        intro hw
        have h0 := congrArg (fun w : LinearMap.range (Matrix.mulVecLin ε) =>
          (w : Fin n → PSUF g) i) hw
        simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at h0
        exact hij h0
      exact h ⟨_, hwne⟩
    obtain ⟨w, hwne⟩ := hWne
    exact (smul_eq_zero.mp (hact0 w)).resolve_right hwne

private instance rckSD_A_isMulCommutative {n g : ℕ} (s : GL (Fin n) (PSUF g)) :
    IsMulCommutative (rckSD_A s) := by
  refine Algebra.isMulCommutative_adjoin (PSUF g) ?_
  rintro a ⟨t, ht, rfl⟩ b ⟨u, hu, rfl⟩ _
  rw [Set.mem_singleton_iff] at ht hu
  subst t
  subst u
  exact Commute.refl _

private lemma rckSD_antidiag_map_transpose {g n : ℕ} :
    Matrix.transpose ((Unitary.antidiag n).map (PSUσ g).toRingHom) = Unitary.antidiag n := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Unitary.antidiag, Matrix.of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h']
    exact map_one _
  · have h' : j ≠ Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h']
    exact map_zero _

private noncomputable def rckSD_adjHom {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    (hsU : s ∈ GUsub (PSUσ g) n) :
    rckSD_A s →+* rckSD_A s := by
  classical
  let σ : PSUF g →+* PSUF g := (PSUσ g).toRingHom
  let G : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := PSUF g) n)
  have hSU' : ∀ t ∈ ({s} : Set (GL (Fin n) (PSUF g))),
      Matrix.transpose ((t : Matrix (Fin n) (Fin n) (PSUF g)).map σ) * G *
        (t : Matrix (Fin n) (Fin n) (PSUF g)) = G := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    have hsU' := (mem_GUsub (σ := PSUσ g) (A := s)).mp hsU
    simpa [Unitary.conjTr, σ, G] using hsU'
  have hadjmem : ∀ a : rckSD_A s,
      formAdj σ G (a : Matrix (Fin n) (Fin n) (PSUF g)) ∈ rckSD_A s :=
    fun a => Geo.formAdj_mem_adjoin σ hG hSU' a.2
  exact
  { toFun := fun a => ⟨formAdj σ G (a : Matrix (Fin n) (Fin n) (PSUF g)), hadjmem a⟩
    map_one' := by apply Subtype.ext; exact Geo.formAdj_one σ hG
    map_zero' := by apply Subtype.ext; simp [formAdj]
    map_mul' := fun a b => by
      apply Subtype.ext
      change formAdj σ G ((a : Matrix (Fin n) (Fin n) (PSUF g)) *
          (b : Matrix (Fin n) (Fin n) (PSUF g))) =
        formAdj σ G (a : Matrix (Fin n) (Fin n) (PSUF g)) *
          formAdj σ G (b : Matrix (Fin n) (Fin n) (PSUF g))
      rw [Geo.formAdj_mul σ hG]
      exact (congrArg Subtype.val (mul_comm'
        (⟨formAdj σ G (a : Matrix (Fin n) (Fin n) (PSUF g)), hadjmem a⟩ : rckSD_A s)
        (⟨formAdj σ G (b : Matrix (Fin n) (Fin n) (PSUF g)), hadjmem b⟩ : rckSD_A s))).symm
    map_add' := fun a b => by
      apply Subtype.ext
      exact Geo.formAdj_add σ G (a : Matrix (Fin n) (Fin n) (PSUF g))
        (b : Matrix (Fin n) (Fin n) (PSUF g)) }

private lemma rckSD_adjHom_val {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    (hsU : s ∈ GUsub (PSUσ g) n) (a : rckSD_A s) :
    (rckSD_adjHom hsU a : Matrix (Fin n) (Fin n) (PSUF g)) =
      formAdj (PSUσ g).toRingHom (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) (PSUF g)) :=
  rfl

private lemma rckSD_adjHom_involutive {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    (hsU : s ∈ GUsub (PSUσ g) n) (a : rckSD_A s) :
    rckSD_adjHom hsU (rckSD_adjHom hsU a) = a := by
  apply Subtype.ext
  rw [rckSD_adjHom_val hsU, rckSD_adjHom_val hsU]
  have hσ : ∀ x : PSUF g, (PSUσ g).toRingHom ((PSUσ g).toRingHom x) = x := by
    intro x
    simpa [PSUσ] using
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive (K := PSUF g) (p := 2) (f := g + 1)
        (card_PSUF g)) x
  exact Geo.formAdj_formAdj (PSUσ g).toRingHom hσ
    (isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := PSUF g) n))
    rckSD_antidiag_map_transpose _

private lemma rckSD_adjHom_mul_eps {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hsU : s ∈ GUsub (PSUσ g) n)
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n) (rckSD_A s) ε)
    (a : rckSD_A s) :
    (rckSD_adjHom hsU a : Matrix (Fin n) (Fin n) (PSUF g)) * ε = 0 ↔
      (a : Matrix (Fin n) (Fin n) (PSUF g)) * ε = 0 := by
  let σ : PSUF g →+* PSUF g := (PSUσ g).toRingHom
  let G : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := PSUF g) n)
  have hfix : formAdj σ G (rckSD_adjHom hsU a : Matrix (Fin n) (Fin n) (PSUF g)) =
      (a : Matrix (Fin n) (Fin n) (PSUF g)) := by
    have h := congrArg Subtype.val (rckSD_adjHom_involutive hsU a)
    simpa [rckSD_adjHom_val, σ, G] using h
  have hcomm (x : rckSD_A s) :
      (x : Matrix (Fin n) (Fin n) (PSUF g)) * ε =
        ε * (x : Matrix (Fin n) (Fin n) (PSUF g)) :=
    congrArg Subtype.val (mul_comm' x ⟨ε, hε.1⟩)
  constructor
  · intro h
    have h1 : formAdj σ G
        ((rckSD_adjHom hsU a : Matrix (Fin n) (Fin n) (PSUF g)) * ε) = 0 := by
      rw [h]
      simp [formAdj]
    rw [Geo.formAdj_mul σ hG, hε.2.2.2.1, hfix] at h1
    rw [hcomm a]
    exact h1
  · intro h
    have h1 : formAdj σ G ((a : Matrix (Fin n) (Fin n) (PSUF g)) * ε) = 0 := by
      rw [h]
      simp [formAdj]
    rw [Geo.formAdj_mul σ hG, hε.2.2.2.1, ← rckSD_adjHom_val hsU a] at h1
    rw [hcomm (rckSD_adjHom hsU a)]
    exact h1

private lemma rckSD_rho_algebraMap {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
    {π : rckSD_A s →ₐ[PSUF g] K}
    {ρ : K →+* K} {adj : rckSD_A s →+* rckSD_A s}
    (hρπ : ∀ a : rckSD_A s, ρ (π a) = π (adj a))
    (hadj_mat : ∀ a : rckSD_A s, (adj a : Matrix (Fin n) (Fin n) (PSUF g)) =
      formAdj (PSUσ g).toRingHom (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) (PSUF g))) :
    ∀ l : PSUF g, ρ (algebraMap (PSUF g) K l) =
      algebraMap (PSUF g) K (PSUσ g l) := by
  intro l
  let σ : PSUF g →+* PSUF g := (PSUσ g).toRingHom
  let G : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := PSUF g) n)
  rw [← π.commutes l, ← π.commutes ((PSUσ g) l)]
  change ρ (π (algebraMap (PSUF g) (rckSD_A s) l)) =
    π (algebraMap (PSUF g) (rckSD_A s) ((PSUσ g) l))
  rw [hρπ (algebraMap (PSUF g) (rckSD_A s) l)]
  have h2 : adj (algebraMap (PSUF g) (rckSD_A s) l) =
      algebraMap (PSUF g) (rckSD_A s) ((PSUσ g) l) := by
    apply Subtype.ext
    rw [hadj_mat]
    show formAdj σ G (algebraMap (PSUF g) (Matrix (Fin n) (Fin n) (PSUF g)) l) =
      algebraMap (PSUF g) (Matrix (Fin n) (Fin n) (PSUF g)) ((PSUσ g) l)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Geo.formAdj_smul, Geo.formAdj_one σ hG]
    rfl
  rw [h2]

private lemma rckSD_rho_nontrivial {g : ℕ} {K : Type} [Field K] [Algebra (PSUF g) K]
    {ρ : K →+* K}
    (hρL : ∀ l : PSUF g, ρ (algebraMap (PSUF g) K l) =
      algebraMap (PSUF g) K (PSUσ g l)) :
    ∃ x : K, ρ x ≠ x := by
  obtain ⟨c, hc⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne
    (K := PSUF g) (p := 2) (f := g + 1) (card_PSUF g)
  refine ⟨algebraMap (PSUF g) K c, ?_⟩
  intro hid
  apply hc
  have h : algebraMap (PSUF g) K ((PSUσ g) c) = algebraMap (PSUF g) K c := by
    rw [← hρL c, hid]
  exact RingHom.injective (algebraMap (PSUF g) K) h

private lemma rckSD_rho_exists {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hsU : s ∈ GUsub (PSUσ g) n)
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n) (rckSD_A s) ε)
    {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    {π : rckSD_A s →ₐ[PSUF g] K}
    (hπ : RCKBlockCoord {s} ε K π) :
    ∃ (ρ : K ≃+* K),
      (∀ a : rckSD_A s, ρ (π a) = π (rckSD_adjHom hsU a)) ∧
      (∀ x : K, ρ (ρ x) = x) ∧ (∃ x : K, ρ x ≠ x) ∧
      (∀ l : PSUF g, ρ (algebraMap (PSUF g) K l) =
        algebraMap (PSUF g) K (PSUσ g l)) := by
  classical
  let adj := rckSD_adjHom hsU
  let πr : rckSD_A s →+* K := (π : rckSD_A s →+* K)
  have hπr : Function.Surjective πr := hπ.1
  let fr : rckSD_A s →+* K := πr.comp adj
  have hπker : ∀ a : rckSD_A s, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) (PSUF g)) * ε = 0 :=
    rckSD_pi_eq_zero_iff hε.2.2.1 hπ
  have hker : ∀ a ∈ RingHom.ker πr, fr a = 0 := by
    intro a ha
    change π (adj a) = 0
    rw [hπker (adj a)]
    change (adj a : Matrix (Fin n) (Fin n) (PSUF g)) * ε = 0
    change π a = 0 at ha
    exact (rckSD_adjHom_mul_eps hsU hε a).mpr ((hπker a).mp ha)
  let eK : rckSD_A s ⧸ RingHom.ker πr ≃+* K :=
    RingHom.quotientKerEquivOfSurjective (f := πr) hπr
  let ρhom : K →+* K :=
    (Ideal.Quotient.lift (RingHom.ker πr) fr hker).comp eK.symm.toRingHom
  have hρπ : ∀ a : rckSD_A s, ρhom (π a) = π (adj a) := by
    intro a
    have heK : eK.symm (πr a) = Ideal.Quotient.mk (RingHom.ker πr) a := by
      rw [← RingHom.quotientKerEquivOfSurjective_apply_mk (f := πr) hπr a,
        RingEquiv.symm_apply_apply]
    change (Ideal.Quotient.lift (RingHom.ker πr) fr hker) (eK.symm (πr a)) =
      π (adj a)
    rw [heK]
    exact Ideal.Quotient.lift_mk (RingHom.ker πr) fr hker
  have hρρ : ∀ k, ρhom (ρhom k) = k := by
    intro k
    obtain ⟨a, ha⟩ := hπr k
    rw [← ha]
    change ρhom (ρhom (π a)) = π a
    rw [hρπ a, hρπ (adj a)]
    have hfix2 : adj (adj a) = a := rckSD_adjHom_involutive hsU a
    rw [hfix2]
  have hinj : Function.Injective ρhom := fun x y hxy => by
    have := congrArg ρhom hxy
    rwa [hρρ x, hρρ y] at this
  have hsurj : Function.Surjective ρhom := fun x => ⟨ρhom x, hρρ x⟩
  let ρ : K ≃+* K := RingEquiv.ofBijective ρhom ⟨hinj, hsurj⟩
  have hρL : ∀ l : PSUF g, ρ (algebraMap (PSUF g) K l) =
      algebraMap (PSUF g) K (PSUσ g l) :=
    rckSD_rho_algebraMap (ρ := (ρ : K →+* K)) hρπ (fun a => rckSD_adjHom_val hsU a)
  have hnt : ∃ x : K, ρ x ≠ x := rckSD_rho_nontrivial (ρ := (ρ : K →+* K)) hρL
  exact ⟨ρ, hρπ, hρρ, hnt, hρL⟩

private lemma rckSD_rho_data {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hsU : s ∈ GUsub (PSUσ g) n)
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n) (rckSD_A s) ε)
    {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    {π : rckSD_A s →ₐ[PSUF g] K}
    (hπ : RCKBlockCoord {s} ε K π) :
    ∃ (ρ : K ≃+* K) (adj : rckSD_A s →+* rckSD_A s),
      (∀ a : rckSD_A s, (adj a : Matrix (Fin n) (Fin n) (PSUF g)) =
        formAdj (PSUσ g).toRingHom (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) (PSUF g))) ∧
      (∀ a : rckSD_A s, ρ (π a) = π (adj a)) ∧
      (∀ x : K, ρ (ρ x) = x) ∧ (∃ x : K, ρ x ≠ x) ∧
      (∀ l : PSUF g, ρ (algebraMap (PSUF g) K l) =
        algebraMap (PSUF g) K (PSUσ g l)) := by
  obtain ⟨ρ, hρπ, hρρ, hnt, hρL⟩ := rckSD_rho_exists hsU hε hπ
  exact ⟨ρ, rckSD_adjHom hsU, fun a => rfl, hρπ, hρρ, hnt, hρL⟩

private lemma rckSD_blockForm_herm {n g : ℕ}
    (ε : Matrix (Fin n) (Fin n) (PSUF g)) :
    ∀ x y : LinearMap.range (Matrix.mulVecLin ε),
      (PSUσ g).toRingHom (rckSD_blockForm ε x y) = rckSD_blockForm ε y x := by
  intro x y
  rw [rckSD_blockForm_apply, rckSD_blockForm_apply]
  exact CFSG.Timmesfeld.LieEmbed.uForm_conj (PSUσ g)
    (by
      intro c
      simpa [PSUσ] using
        (CFSG.LieType.BorelTits.unitaryInvolution_involutive (K := PSUF g) (p := 2) (f := g + 1)
          (card_PSUF g)) c)
    (x : Fin n → PSUF g) (y : Fin n → PSUF g)

private lemma rckSD_blockForm_adj {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    {π : rckSD_A s →ₐ[PSUF g] K}
    (hπ : RCKBlockCoord {s} ε K π)
    {ρ : K ≃+* K} {adj : rckSD_A s →+* rckSD_A s}
    (hadj_mat : ∀ a : rckSD_A s, (adj a : Matrix (Fin n) (Fin n) (PSUF g)) =
      formAdj (PSUσ g).toRingHom (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) (PSUF g)))
    (hρπ : ∀ a : rckSD_A s, ρ (π a) = π (adj a)) :
    ∀ (c : K) (x y : LinearMap.range (Matrix.mulVecLin ε)),
      rckSD_blockForm ε (c • x) y = rckSD_blockForm ε x (ρ c • y) := by
  intro c x y
  obtain ⟨a, rfl⟩ := hπ.1 c
  change rckSD_blockForm ε (π a • x) y = rckSD_blockForm ε x (ρ (π a) • y)
  rw [rckSD_blockForm_apply, rckSD_blockForm_apply]
  let σ : PSUF g →+* PSUF g := (PSUσ g).toRingHom
  let G : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := PSUF g) n)
  have hMN : G * formAdj σ G (a : Matrix (Fin n) (Fin n) (PSUF g)) =
      Matrix.transpose ((a : Matrix (Fin n) (Fin n) (PSUF g)).map σ) * G := by
    rw [formAdj, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
      Matrix.one_mul]
  have hx : ((π a • x : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → PSUF g) =
      Matrix.mulVec (a : Matrix (Fin n) (Fin n) (PSUF g)) (x : Fin n → PSUF g) :=
    hπ.2.1 a x
  have hy : ((ρ (π a) • y : LinearMap.range (Matrix.mulVecLin ε)) : Fin n → PSUF g) =
      Matrix.mulVec (formAdj σ G (a : Matrix (Fin n) (Fin n) (PSUF g)))
        (y : Fin n → PSUF g) := by
    rw [hρπ a]
    rw [hπ.2.1 (adj a) y, hadj_mat a]
  rw [hx, hy]
  exact rckSD_uForm_adjoint_mulVec (a : Matrix (Fin n) (Fin n) (PSUF g))
    (formAdj σ G (a : Matrix (Fin n) (Fin n) (PSUF g))) hMN
    (x : Fin n → PSUF g) (y : Fin n → PSUF g)

private lemma rckSD_blockForm_nondegenerate {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n) (rckSD_A s) ε) :
    ∀ x : LinearMap.range (Matrix.mulVecLin ε),
      (∀ y, rckSD_blockForm ε x y = 0) → x = 0 := by
  intro x hx
  let σ : PSUF g →+* PSUF g := (PSUσ g).toRingHom
  let G : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := PSUF g) n)
  have hMN : G * formAdj σ G ε = Matrix.transpose (ε.map σ) * G := by
    rw [formAdj, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
      Matrix.one_mul]
  have hxall : ∀ z : Fin n → PSUF g,
      CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) (x : Fin n → PSUF g) z = 0 := by
    intro z
    have hdecomp : z = Matrix.mulVec ε z + Matrix.mulVec (1 - ε) z := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    rw [hdecomp, CFSG.Timmesfeld.LieEmbed.uForm_add_right]
    have h1 : CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) (x : Fin n → PSUF g)
        (Matrix.mulVec ε z) = 0 := by
      have h0 := hx (⟨Matrix.mulVec ε z, ⟨z, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin ε))
      change rckSD_blockForm ε x
        (⟨Matrix.mulVec ε z, ⟨z, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin ε)) = 0 at h0
      rwa [rckSD_blockForm_apply] at h0
    have h2 : CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) (x : Fin n → PSUF g)
        (Matrix.mulVec (1 - ε) z) = 0 := by
      have hxε : Matrix.mulVec ε (x : Fin n → PSUF g) = (x : Fin n → PSUF g) := by
        obtain ⟨v, hv⟩ := x.2
        calc Matrix.mulVec ε (x : Fin n → PSUF g)
            = Matrix.mulVec ε (Matrix.mulVec ε v) := by
                rw [← hv, Matrix.mulVecLin_apply]
          _ = Matrix.mulVec (ε * ε) v := Matrix.mulVec_mulVec v ε ε
          _ = Matrix.mulVec ε v := by rw [hε.2.1]
          _ = (x : Fin n → PSUF g) := by rw [← hv, Matrix.mulVecLin_apply]
      have hstep := rckSD_uForm_adjoint_mulVec ε (formAdj σ G ε) hMN
        (x : Fin n → PSUF g) (Matrix.mulVec (1 - ε) z)
      rw [hε.2.2.2.1, hxε] at hstep
      have hzero : Matrix.mulVec ε (Matrix.mulVec (1 - ε) z) = 0 := by
        rw [Matrix.mulVec_mulVec]
        have h0 : ε * (1 - ε) = 0 := by
          rw [Matrix.mul_sub, Matrix.mul_one, hε.2.1, sub_self]
        rw [h0, Matrix.zero_mulVec]
      rw [hstep, hzero]
      simp [CFSG.Timmesfeld.LieEmbed.uForm]
    rw [h1, h2, add_zero]
  have hx0 : (fun i => σ ((x : Fin n → PSUF g) i)) = 0 := by
    refine CFSG.LinearAlgebra.eq_zero_of_forall_dotProduct_mulVec_eq_zero'
      ((Matrix.isUnit_iff_isUnit_det G).mpr hG) ?_
    intro z
    have := hxall z
    simpa [CFSG.Timmesfeld.LieEmbed.uForm, G, σ, PSUσ] using this
  apply Subtype.ext
  funext i
  exact (PSUσ g).toRingHom.injective (by
    simpa using congrFun hx0 i)

theorem rckSD_formDescent {n g : ℕ} {s : GL (Fin n) (PSUF g)} (hsU : s ∈ GUsub (PSUσ g) n)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower (PSUF g) K (LinearMap.range (Matrix.mulVecLin ε))]
    {π : Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g)))) →ₐ[PSUF g] K}
    (hπ : RCKBlockCoord {s} ε K π) :
    ∃ (ρ : K ≃+* K) (B : LinearMap.range (Matrix.mulVecLin ε) →ₛₗ[(ρ : K →+* K)]
        LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] K),
      (∀ x, ρ (ρ x) = x) ∧ (∃ x, ρ x ≠ x) ∧ (∀ x y, ρ (B x y) = B y x) ∧
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧
      ∀ x y : LinearMap.range (Matrix.mulVecLin ε),
        CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
          Algebra.trace (PSUF g) K (B x y) := by
  classical
  let W := LinearMap.range (Matrix.mulVecLin ε)
  obtain ⟨ρ, adj, hadj_mat, hρπ, hρρ, hnt, hρL⟩ := rckSD_rho_data hsU hε hπ
  have hnd := rckSD_blockForm_nondegenerate (s := s) hε
  have hadj := rckSD_blockForm_adj (s := s) hπ hadj_mat hρπ
  have hherm := rckSD_blockForm_herm (g := g) ε
  obtain ⟨B, hBsymm, hBnd, hBtrace⟩ :=
    CFSG.LieType.SemisimpleCentralizers.HeldUCD.exists_trace_form
      (L := PSUF g) (K := K) (W := W) (ρ : K →+* K) (PSUσ g).toRingHom
      hρρ hρL (rckSD_blockForm ε) hherm hadj hnd
  refine ⟨ρ, B, hρρ, hnt, hBsymm, hBnd, ?_⟩
  intro x y
  exact (rckSD_blockForm_apply ε x y).symm.trans (hBtrace x y)

end CFSG.StandardType.RCKRP
