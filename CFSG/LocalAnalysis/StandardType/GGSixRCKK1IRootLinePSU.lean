module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LieType.Universal.Unitary.Extras.Basic

public section

namespace CFSG.StandardType.RCKK1I

open Matrix CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.StandardType CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.LieType.BorelTits
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem rckRLpsu_longRootHom_injective {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    {i : Fin n} (hi : i ≠ Fin.rev i) : Function.Injective (longRootHom σ hi) := by
  intro a b hab
  have h := congrArg (fun g : SU σ n => mat σ n g i (Fin.rev i)) hab
  rw [mat_apply, mat_apply, coe_longRootHom, coe_longRootHom, longRootMatrix, longRootMatrix] at h
  simp only [Matrix.add_apply, Matrix.one_apply_ne hi, zero_add,
    Matrix.single_apply_same] at h
  exact Multiplicative.toAdd.injective (Subtype.ext h)

private theorem rckRLpsu_longTorus_mul_longRootHom {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {b : Fin n} (hb : b ≠ Fin.rev b) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) {e : F} (he : σ e = e) (he0 : e ≠ 0)
    (c : Multiplicative (traceZero σ)) :
    longTorus σ hb ζ he * longRootHom σ hb c =
      longRootHom σ hb (Multiplicative.ofAdd ⟨e * (c.toAdd : F) * e, by
        rw [mem_traceZero]
        have hc : σ (c.toAdd : F) = -(c.toAdd : F) := by
          have h := (mem_traceZero σ).mp c.toAdd.2
          linear_combination h
        rw [map_mul, map_mul, he, hc]
        ring⟩) * longTorus σ hb ζ he := by
  apply mat_injective
  rw [map_mul, map_mul]
  simp only [mat_apply]
  rw [coe_longTorus σ hb hζ he he0, coe_longRootHom, coe_longRootHom,
    longRootMatrix, longRootMatrix]
  have hd : longTorusFun b e b = e := by simp [longTorusFun]
  have hd' : longTorusFun b e (Fin.rev b) = e⁻¹ := by simp [longTorusFun, Ne.symm hb]
  have hmul1 : ∀ x : F, diagonal (longTorusFun b e) * Matrix.single b (Fin.rev b) x =
      Matrix.single b (Fin.rev b) (e * x) := by
    intro x
    ext i j
    rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
    by_cases h : i = b ∧ j = Fin.rev b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hd]
    · have h' : ¬ (b = i ∧ Fin.rev b = j) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
      simp [h']
  have hmul2 : ∀ y : F, Matrix.single b (Fin.rev b) y * diagonal (longTorusFun b e) =
      Matrix.single b (Fin.rev b) (y * e⁻¹) := by
    intro y
    ext i j
    rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
    by_cases h : i = b ∧ j = Fin.rev b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hd']
    · have h' : ¬ (b = i ∧ Fin.rev b = j) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
      simp [h']
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hmul1, hmul2]
  congr 1
  congr 1
  show e * (c.toAdd : F) = (e * (c.toAdd : F) * e) * e⁻¹
  field_simp

private theorem rckRLpsu_scalars_maxHeight {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    [Fact (Nat.Prime 2)] (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    {γ₀ : Fin (n / 2) → ℤ} (hγ₀ : γ₀ ∈ (rootDatum hF n).roots)
    (hmax : ∀ δ ∈ (rootDatum hF n).roots, ht δ ≤ ht γ₀) :
    ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (ε : Multiplicative Fq ≃* (rootDatum hF n).rootGroup γ₀),
      Nat.card Fq = 2 ^ f ∧ RCKRootLineScalars ((rootDatum hF n).rootGroup γ₀) Fq ε := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  let i₀ : Fin n := ⟨0, by omega⟩
  let j₀ : Fin n := Fin.rev i₀
  have hrev : i₀ ≠ j₀ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, j₀] at this
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((steinbergExtras hF n hn ζ hζ).ne_bot γ₀ hγ₀)
  have hxmem : (x : SU (unitaryInvolution F 2 f) n) ∈ (rootDatum hF n).rootGroup γ₀ := x.2
  have hxne : (x : SU (unitaryInvolution F 2 f) n) ≠ 1 := fun h => hx1 (Subtype.ext h)
  let c : F := mat (unitaryInvolution F 2 f) n (x : SU (unitaryInvolution F 2 f) n) i₀ j₀
  have hmat : mat (unitaryInvolution F 2 f) n (x : SU (unitaryInvolution F 2 f) n) =
      1 + Matrix.single i₀ j₀ c := by
    simpa [i₀, j₀, c] using
      mat_eq_of_mem_rootGroup_maxHeight hσ hn hγ₀ hmax hxmem
  have hc0 : c ≠ 0 := by
    intro h0
    apply hxne
    apply mat_injective
    rw [hmat, h0, Matrix.single_zero, add_zero, map_one]
  have hsum : weight n i₀ - weight n j₀ ∈ wt2 (toStd n γ₀) := by
    have hwt := hasWt_of_mem_rootGroup hσ hxmem
    have hcoeff : (mat (unitaryInvolution F 2 f) n (x : SU (unitaryInvolution F 2 f) n) - 1) i₀ j₀
        = c := by
      rw [Matrix.sub_apply, hmat, Matrix.add_apply, Matrix.one_apply_ne hrev, zero_add,
        Matrix.single_apply_same, sub_zero]
    exact hwt i₀ j₀ (by rw [hcoeff]; exact hc0)
  have hmem : weight n i₀ - weight n j₀ = toStd n γ₀ := by
    rcases (mem_wt2.mp hsum) with h | h
    · exact h
    · exact absurd h (GGRootSU.weight_sub_ne_two_smul_of_maxHeight hγ₀
        (ht_pos_of_maxHeight hγ₀ hmax) hmax i₀ j₀)
  have htop : 2 • weight n i₀ = toStd n γ₀ := by
    dsimp only [j₀] at hmem
    rw [← hmem, weight_rev', sub_neg_eq_add, two_nsmul]
  let Fq := RingHom.eqLocusField (unitaryInvolution F 2 f).toRingHom (RingHom.id F)
  haveI : CharP Fq 2 := Subfield.charP Fq 2
  have hFqcard : Nat.card Fq = 2 ^ f := by
    have hord : orderOf (unitaryInvolution F 2 f) = 2 := by
      have h2 : (unitaryInvolution F 2 f) ^ (2 : ℕ) = 1 := by
        rw [pow_two]
        ext a
        exact unitaryInvolution_involutive hF a
      refine orderOf_eq_prime (p := 2) h2 ?_
      intro h1
      obtain ⟨a, ha⟩ := exists_unitaryInvolution_ne hF
      exact ha (RingEquiv.congr_fun h1 a)
    obtain ⟨-, hcard⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf
      (K := F) (r := 2) (n := 2 * f) (p := 2) Nat.prime_two (by omega)
      (by rw [hF, ← pow_mul, mul_comm]) (unitaryInvolution F 2 f) hord
    rwa [show 2 * f / 2 = f by omega] at hcard
  let scFun : Fq → traceZero (unitaryInvolution F 2 f) := fun lam =>
    ⟨(lam : F) * (ζ : F), by
      rw [mem_traceZero, map_mul]
      have hσlam : unitaryInvolution F 2 f (lam : F) = (lam : F) :=
        RingHom.mem_eqLocusField.mp lam.2
      rw [hσlam]
      calc (lam : F) * (ζ : F) + (lam : F) * unitaryInvolution F 2 f (ζ : F)
          = (lam : F) * ((ζ : F) + unitaryInvolution F 2 f (ζ : F)) := by ring
        _ = 0 := by rw [(mem_traceZero _).mp ζ.2, mul_zero]⟩
  have hsc_inj : Function.Injective scFun := by
    intro lam mu h
    have h1 : (lam : F) * (ζ : F) = (mu : F) * (ζ : F) := congrArg Subtype.val h
    exact Subtype.ext (mul_right_cancel₀ hζ h1)
  let scAdd : Fq →+ traceZero (unitaryInvolution F 2 f) :=
    { toFun := scFun
      map_zero' := by ext; simp [scFun]
      map_add' := fun lam mu => by ext; simp [scFun, add_mul] }
  let scHom : Multiplicative Fq →* Multiplicative (traceZero (unitaryInvolution F 2 f)) :=
    scAdd.toMultiplicative
  let lrSub : Multiplicative (traceZero (unitaryInvolution F 2 f)) →*
      (rootDatum hF n).rootGroup γ₀ :=
    { toFun := fun c => ⟨longRootHom (unitaryInvolution F 2 f) hrev c,
        longRootHom_mem hσ hrev htop c⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
  let φ : Multiplicative Fq →* (rootDatum hF n).rootGroup γ₀ := lrSub.comp scHom
  have hφapply : ∀ a : Multiplicative Fq,
      (φ a : SU (unitaryInvolution F 2 f) n) =
        longRootHom (unitaryInvolution F 2 f) hrev (scHom a) := fun _ => rfl
  have hφapply' : ∀ lam : Fq, (φ (Multiplicative.ofAdd lam) : SU (unitaryInvolution F 2 f) n) =
      longRootHom (unitaryInvolution F 2 f) hrev (Multiplicative.ofAdd (scFun lam)) := by
    intro lam
    rw [hφapply]
    rfl
  have hφbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h2 : scHom a = scHom b :=
        rckRLpsu_longRootHom_injective hrev (by
          have := congrArg (fun g : (rootDatum hF n).rootGroup γ₀ =>
            (g : SU (unitaryInvolution F 2 f) n)) hab
          simpa only [hφapply] using this)
      have h3 : scFun (Multiplicative.toAdd a) = scFun (Multiplicative.toAdd b) := by
        change scAdd (Multiplicative.toAdd a) = scAdd (Multiplicative.toAdd b)
        exact Multiplicative.ofAdd.injective (by
          simpa only [scHom, AddMonoidHom.toMultiplicative_apply_apply] using h2)
      exact Multiplicative.toAdd.injective (hsc_inj h3)
    · intro y
      have hy : (y : SU (unitaryInvolution F 2 f) n) ∈
          (rootDatum hF n).rootGroup γ₀ := y.2
      let cy : F := mat (unitaryInvolution F 2 f) n (y : SU (unitaryInvolution F 2 f) n) i₀ j₀
      have hmaty : mat (unitaryInvolution F 2 f) n (y : SU (unitaryInvolution F 2 f) n) =
          1 + Matrix.single i₀ j₀ cy := by
        simpa [i₀, j₀, cy] using mat_eq_of_mem_rootGroup_maxHeight hσ hn hγ₀ hmax hy
      have hcy : cy + unitaryInvolution F 2 f cy = 0 :=
        add_eq_zero_of_mat_eq_one_add_single hn hmaty
      let lam : Fq := ⟨cy * (ζ : F)⁻¹, by
        rw [RingHom.mem_eqLocusField]
        show unitaryInvolution F 2 f (cy * (ζ : F)⁻¹) = (RingHom.id F) (cy * (ζ : F)⁻¹)
        have hσcy : unitaryInvolution F 2 f cy = -cy := by
          have h := hcy
          linear_combination h
        have hσζ : unitaryInvolution F 2 f (ζ : F) = -(ζ : F) := by
          have h := (mem_traceZero _).mp ζ.2
          linear_combination h
        rw [map_mul, map_inv₀, hσcy, hσζ, ← neg_inv, RingHom.id_apply]
        ring⟩
      refine ⟨Multiplicative.ofAdd lam, ?_⟩
      apply Subtype.ext
      apply mat_injective
      rw [hφapply', mat_apply, mat_apply, coe_longRootHom, longRootMatrix, ← mat_apply, hmaty]
      congr 1
      congr 1
      change (lam : F) * (ζ : F) = cy
      dsimp only [lam]
      rw [mul_assoc, inv_mul_cancel₀ hζ, mul_one]
  let ε : Multiplicative Fq ≃* (rootDatum hF n).rootGroup γ₀ := MulEquiv.ofBijective φ hφbij
  have hε_apply : ∀ t : Fq, (ε (Multiplicative.ofAdd t) : SU (unitaryInvolution F 2 f) n) =
      longRootHom (unitaryInvolution F 2 f) hrev (Multiplicative.ofAdd (scFun t)) :=
    fun t => hφapply' t
  refine ⟨Fq, inferInstance, inferInstance, ε, hFqcard, ?_⟩
  intro l hl
  obtain ⟨e, he⟩ := (Function.Injective.bijective_of_finite
    (CharTwo.sq_injective (R := Fq))).2 l
  have he0 : e ≠ 0 := by
    intro h0
    simp only [h0, pow_two, zero_mul] at he
    exact hl he.symm
  have hlF : (l : F) = (e : F) * (e : F) := by
    rw [← he]
    push_cast
    ring
  refine ⟨longTorus (unitaryInvolution F 2 f) hrev ζ
    (RingHom.mem_eqLocusField.mp e.2), fun t => ?_⟩
  have he0' : ((e : Fq) : F) ≠ 0 := fun h => he0 (Subtype.ext (by simpa using h))
  rw [hε_apply t, hε_apply (l * t), mul_inv_eq_iff_eq_mul]
  rw [rckRLpsu_longTorus_mul_longRootHom hσ hrev hζ (RingHom.mem_eqLocusField.mp e.2) he0'
    (Multiplicative.ofAdd (scFun t))]
  congr 1
  congr 1
  apply Subtype.ext
  dsimp only [scFun]
  change (e : F) * ((t : F) * (ζ : F)) * (e : F) = ((l * t : Fq) : F) * (ζ : F)
  push_cast
  rw [hlF]
  ring

private theorem rckRLpsu_scalars_of_actsAs {U : Type} [Group U] {D : UniversalRootDatum U}
    {γ₀ β : Fin D.rank → ℤ} (hγ₀ : γ₀ ∈ D.roots)
    {w : (coxeterMatrix D.isFiniteType).Group} {x : U} (hx : ActsAs D x w)
    (hβ : β = weylAction D.isFiniteType w γ₀) {Fq : Type} [Field Fq]
    {ε₀ : Multiplicative Fq ≃* D.rootGroup γ₀}
    (hsc : RCKRootLineScalars (D.rootGroup γ₀) Fq ε₀) :
    ∃ ε : Multiplicative Fq ≃* D.rootGroup β,
      RCKRootLineScalars (D.rootGroup β) Fq ε := by
  have hact : (D.rootGroup γ₀).map (MulAut.conj x).toMonoidHom = D.rootGroup β := by
    rw [hβ]
    exact hx γ₀ hγ₀
  let φ : Multiplicative Fq →* D.rootGroup β :=
    { toFun := fun a => ⟨x * (ε₀ a : U) * x⁻¹, by
        rw [← hact]
        exact ⟨ε₀ a, (ε₀ a).2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul, map_mul]
        group }
  have hφapply : ∀ a : Multiplicative Fq, (φ a : U) = x * (ε₀ a : U) * x⁻¹ := fun _ => rfl
  have hφbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : (ε₀ a : U) = (ε₀ b : U) := by
        have h2 : x * (ε₀ a : U) * x⁻¹ = x * (ε₀ b : U) * x⁻¹ := by
          have := congrArg (fun g : D.rootGroup β => (g : U)) hab
          simpa only [hφapply] using this
        exact mul_left_cancel (mul_right_cancel h2)
      exact ε₀.injective (Subtype.ext h1)
    · intro y
      have hy : (y : U) ∈ (D.rootGroup γ₀).map (MulAut.conj x).toMonoidHom := by
        rw [hact]
        exact y.2
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      refine ⟨ε₀.symm ⟨z, hz⟩, ?_⟩
      apply Subtype.ext
      show x * (ε₀ (ε₀.symm ⟨z, hz⟩) : U) * x⁻¹ = (y : U)
      rw [MulEquiv.apply_symm_apply]
      simpa [MulAut.conj_apply] using hzy
  let ε : Multiplicative Fq ≃* D.rootGroup β := MulEquiv.ofBijective φ hφbij
  refine ⟨ε, ?_⟩
  intro l hl
  obtain ⟨h, hh⟩ := hsc l hl
  refine ⟨x * h * x⁻¹, fun t => ?_⟩
  have hεt : (ε (Multiplicative.ofAdd t) : U) =
      x * (ε₀ (Multiplicative.ofAdd t) : U) * x⁻¹ := by
    show (φ (Multiplicative.ofAdd t) : U) = _
    rw [hφapply]
  have hεlt : (ε (Multiplicative.ofAdd (l * t)) : U) =
      x * (ε₀ (Multiplicative.ofAdd (l * t)) : U) * x⁻¹ := by
    show (φ (Multiplicative.ofAdd (l * t)) : U) = _
    rw [hφapply]
  rw [hεt, hεlt]
  calc (x * h * x⁻¹) * (x * (ε₀ (Multiplicative.ofAdd t) : U) * x⁻¹) * (x * h * x⁻¹)⁻¹
      = x * (h * (ε₀ (Multiplicative.ofAdd t) : U) * h⁻¹) * x⁻¹ := by group
    _ = x * (ε₀ (Multiplicative.ofAdd (l * t)) : U) * x⁻¹ := by rw [hh t]

theorem rckK1I_rootLine_PSU
    {n f : ℕ} (hadm : StatedLieAdmissible .PSU n 2 f) :
    0 < (ggU .PSU n f).D.rank ∧ RCKRootLineAll (ggU .PSU n f) f := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := by have := hadm.2.2.1; omega
  have e : ggU .PSU n f = ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
      rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [e]
  refine ⟨by show 0 < n / 2; omega, ?_⟩
  intro β _ hlong
  obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hlong
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (card_galoisField_two_mul 2 f hf)
  have hct := isCTGroupDatum (card_galoisField_two_mul 2 f hf) n hn ζ hζ
  obtain ⟨Fq, iFq, iFin, ε₀, hcard, hsc₀⟩ :=
    rckRLpsu_scalars_maxHeight (card_galoisField_two_mul 2 f hf) hn hf hγ₀ hmax
  obtain ⟨ε, hsc⟩ := rckRLpsu_scalars_of_actsAs hγ₀ (actsAs_nrep hct w) hβeq hsc₀
  exact ⟨Fq, iFq, iFin, ε, hcard, hsc⟩

end CFSG.StandardType.RCKK1I
