module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.Quasithin.Background.HMultFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mult
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Matrix Kronecker

theorem exists_sumOfNatVia_of_sumOfNatIsoMod_omegaPlus {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)}
    (h : SumOfNatIsoMod (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (π : ↥(StatedOmega (StatedQuadPlus 2 K)) →* ↥X),
      Nat.card K = 4 ∧
        SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadPlus 2 K))) X ⊤ ⊥ 2 π := by
  obtain ⟨I, hZ, hind, hsup, hN, hiso⟩ := h
  obtain ⟨-, K, hKfield, hKfinite, hKcard, hreal⟩ := hN 0
  obtain ⟨π, hπ⟩ := hreal
  refine ⟨K, hKfield, hKfinite, π, ?_, ?_⟩
  · rw [hKcard]
    norm_num
  · exact sumOfNatVia_of_isoMod hind hsup 0 hπ (fun i => hiso 0 i)

private theorem omegaPlusTwoNatScalarIso_aux (K : Type) [Field K] [Finite K] [CharP K 2]
    {W : Type} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
    (hK4 : Nat.card K = 4)
    {π : ↥(StatedOmega (StatedQuadPlus 2 K)) →* ↥X}
    (hsum : SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadPlus 2 K))) X ⊤ ⊥ 2 π) :
    ∃ ω ∈ Subgroup.centralizer (X : Set (MulAut W)),
      (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * ω = ω * c) ∧
      orderOf ω = 3 ∧ (∀ v : W, ω v = v → v = 1) ∧
      (∀ z ∈ Subgroup.centralizer (X : Set (MulAut W)),
        (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * z = z * c) →
          z ∈ Subgroup.zpowers ω) := by
  classical
  let ι : Type := Fin 2 ⊕ Fin 2
  let Γ : Subgroup (GL ι K) := StatedOmega (StatedQuadPlus 2 K)
  have h4 : 4 ≤ Nat.card K := by omega
  have hΓ : HasScalarCommutant Γ := hasScalarCommutant_statedOmegaPlus h4
  have hsum' : SumOfNatVia (FFModel.nat Γ) X ⊤ ⊥ 2 π := hsum
  obtain ⟨I, e, hreal, he, hblock⟩ := exists_coords_of_sumOfNatVia Γ hsum'
  have hπsurj : Function.Surjective π := (hreal 0).1
  let X' : Subgroup (MulAut (StdMod (Fin 2 × ι) K)) := natImage (diagSub 2 Γ)
  have hXmap : X.map (congrHom e) = X' := map_congrHom_eq_natImage_diag Γ hπsurj e he
  have hX'mem : ∀ x ∈ X, congrHom e x ∈ X' := fun x hx => by
    rw [← hXmap]
    exact Subgroup.mem_map_of_mem (congrHom e) hx
  have hC'mem : ∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)),
      congrHom e c ∈ Subgroup.centralizer (X' : Set (MulAut (StdMod (Fin 2 × ι) K))) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    rw [← hXmap] at hy
    obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hc x hxX]
  obtain ⟨ζ, hζgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hζcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK4]
  have hζord : orderOf ζ = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζgen, hζcard]
  have hζne : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζord
    omega
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζord]
    exact pow_orderOf_eq_one ζ
  have hζvalne : (ζ : K) ≠ 1 := fun h => hζne (Units.ext h)
  let Bζ : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) ζ
  have hBζmat : (Bζ : Matrix (Fin 2) (Fin 2) K) = (ζ : K) • 1 := by
    dsimp only [Bζ]
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  let ω' : MulAut (StdMod (Fin 2 × ι) K) := matAut (kronGL ι 2 Bζ)
  let ω : MulAut W := (MulAut.congr e).symm ω'
  have hωcongr : congrHom e ω = ω' := (MulAut.congr e).apply_symm_apply ω'
  have hω'C : ω' ∈ Subgroup.centralizer (X' : Set (MulAut (StdMod (Fin 2 × ι) K))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨⟨g, hg⟩, rfl⟩ := hy
    obtain ⟨γ, -, rfl⟩ := Subgroup.mem_map.mp hg
    dsimp only [ω']
    have hnat : natAut (diagSub 2 Γ) ⟨diagGL 2 (γ : GL ι K), hg⟩ =
        matAut (diagGL 2 (γ : GL ι K)) := rfl
    rw [hnat]
    change matHom (diagGL 2 (γ : GL ι K)) * matHom (kronGL ι 2 Bζ) =
      matHom (kronGL ι 2 Bζ) * matHom (diagGL 2 (γ : GL ι K))
    rw [← map_mul, ← map_mul, kronGL_commute_diagGL]
  have hωC : ω ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply congrHom_injective e
    rw [map_mul, map_mul, hωcongr]
    exact Subgroup.mem_centralizer_iff.mp hω'C (congrHom e x) (hX'mem x hx)
  have hcommω : ∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * ω = ω * c := by
    intro c hc
    obtain ⟨B, hB⟩ := (mem_centralizer_diag_iff (k := 2) (Γ := Γ) hΓ).mp (hC'mem c hc)
    apply congrHom_injective e
    rw [map_mul, map_mul, hωcongr, hB]
    dsimp only [ω']
    have hBζcomm : B * Bζ = Bζ * B :=
      (Matrix.GeneralLinearGroup.scalar_commute ζ B).symm
    calc matHom (kronGL ι 2 B) * matHom (kronGL ι 2 Bζ)
        = matHom (kronGL ι 2 B * kronGL ι 2 Bζ) := (map_mul matHom _ _).symm
      _ = matHom (kronGL ι 2 (B * Bζ)) := by rw [← map_mul (kronGL ι 2)]
      _ = matHom (kronGL ι 2 (Bζ * B)) := by rw [hBζcomm]
      _ = matHom (kronGL ι 2 Bζ * kronGL ι 2 B) := by rw [map_mul]
      _ = matHom (kronGL ι 2 Bζ) * matHom (kronGL ι 2 B) := map_mul matHom _ _
  have hBζ3 : Bζ ^ 3 = 1 := by
    dsimp only [Bζ]
    rw [← map_pow, hζ3, map_one]
  have hω'3 : ω' ^ 3 = 1 := by
    dsimp only [ω']
    change (matHom (kronGL ι 2 Bζ)) ^ 3 = 1
    rw [← map_pow, ← map_pow, hBζ3, map_one, map_one]
  have hω'ne : ω' ≠ 1 := by
    intro h
    dsimp only [ω'] at h
    have h1 : kronGL ι 2 Bζ = 1 := by
      apply matHom_injective
      rw [map_one]
      exact h
    have h2 : Bζ = 1 := by
      apply kronGL_injective (ι := ι) (K := K) 2
      rw [map_one]
      exact h1
    have hmat : (Bζ : Matrix (Fin 2) (Fin 2) K) 0 0 = (ζ : K) := by
      rw [hBζmat, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have h2mat : (((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 = 1 := by
      rw [Units.val_one, Matrix.one_apply_eq]
    have hζval : (ζ : K) = 1 := by
      rw [← hmat, h2, h2mat]
    exact hζne (Units.ext hζval)
  have hω'ord : orderOf ω' = 3 := orderOf_eq_prime hω'3 hω'ne
  have hscale : ∀ v : Fin 2 × ι → K, toAddMap ω' v = (ζ : K) • v := by
    intro v
    funext p
    dsimp only [ω']
    rw [toAddMap_matAut, kronGL_mulVec, hBζmat]
    rw [Finset.sum_eq_single p.1]
    · simp [Matrix.smul_apply, Matrix.one_apply, Pi.smul_apply, smul_eq_mul]
    · intro j _ hj
      simp [Matrix.smul_apply, Matrix.one_apply, hj, Ne.symm hj]
    · intro hp
      exact (hp (Finset.mem_univ _)).elim
  have hω'free : ∀ x : StdMod (Fin 2 × ι) K, ω' x = x → x = 1 := by
    intro x hx
    have hx' : toAddMap ω' (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
      simpa [toAddMap] using congrArg Multiplicative.toAdd hx
    have h2 : (ζ : K) • Multiplicative.toAdd x = Multiplicative.toAdd x := by
      rw [← hscale]
      exact hx'
    have h0 : ((ζ : K) - 1) • Multiplicative.toAdd x = 0 := by
      rw [sub_smul, one_smul, h2, sub_self]
    have hv : Multiplicative.toAdd x = 0 := by
      rcases smul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (sub_ne_zero.mpr hζvalne)
      · exact h1
    apply Multiplicative.toAdd.injective
    simpa using hv
  have hωord : orderOf ω = 3 := by
    have h := orderOf_injective (congrHom e) (congrHom_injective e) ω
    rw [hωcongr] at h
    rw [← h]
    exact hω'ord
  have hωfree : ∀ v : W, ω v = v → v = 1 := by
    intro v hv
    have h1 : congrHom e ω (e v) = e v := by
      rw [congrHom_apply, MulEquiv.symm_apply_apply, hv]
    rw [hωcongr] at h1
    exact e.injective (by simpa using hω'free (e v) h1)
  refine ⟨ω, hωC, hcommω, hωord, hωfree, ?_⟩
  intro z hzC hz
  obtain ⟨B, hB⟩ := (mem_centralizer_diag_iff (k := 2) (Γ := Γ) hΓ).mp (hC'mem z hzC)
  have hBcenter : B ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro C
    let c : MulAut W := (MulAut.congr e).symm (matAut (kronGL ι 2 C))
    have hcc : congrHom e c = matAut (kronGL ι 2 C) :=
      (MulAut.congr e).apply_symm_apply (matAut (kronGL ι 2 C))
    have hcmem' : congrHom e c ∈
        Subgroup.centralizer (X' : Set (MulAut (StdMod (Fin 2 × ι) K))) := by
      rw [hcc]
      exact (mem_centralizer_diag_iff (k := 2) (Γ := Γ) hΓ).mpr ⟨C, rfl⟩
    have hcmem : c ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff] at hcmem' ⊢
      intro x hx
      apply congrHom_injective e
      rw [map_mul, map_mul]
      exact hcmem' (congrHom e x) (hX'mem x hx)
    have h1 : congrHom e c * congrHom e z = congrHom e z * congrHom e c := by
      rw [← map_mul, ← map_mul, hz c hcmem]
    rw [hcc, hB] at h1
    have h2 : kronGL ι 2 C * kronGL ι 2 B = kronGL ι 2 B * kronGL ι 2 C := by
      apply matHom_injective
      rw [map_mul, map_mul]
      exact h1
    have h3 : kronGL ι 2 (C * B) = kronGL ι 2 (B * C) := by
      rw [map_mul, map_mul]
      exact h2
    exact kronGL_injective (ι := ι) (K := K) 2 h3
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hBcenter
  obtain ⟨u, hu⟩ := hBcenter
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hζgen u)
  have hzpow : congrHom e z = ω' ^ k := by
    dsimp only [ω']
    have h1 : (Matrix.GeneralLinearGroup.scalar (Fin 2) (ζ ^ k) : GL (Fin 2) K) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) ^ k := map_zpow _ _ _
    have h2 : kronGL ι 2 ((Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) ^ k) =
        (kronGL ι 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)) ^ k := map_zpow _ _ _
    have h3 : matAut ((kronGL ι 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)) ^ k) =
        (matAut (kronGL ι 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ))) ^ k :=
      map_zpow matHom _ _
    calc congrHom e z
        = matAut (kronGL ι 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) := by
          rw [hB, hu]
      _ = matAut (kronGL ι 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) (ζ ^ k))) := by
          rw [← hk]
      _ = matAut (kronGL ι 2 ((Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) ^ k)) := by
          rw [h1]
      _ = matAut ((kronGL ι 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)) ^ k) := by
          rw [h2]
      _ = (matAut (kronGL ι 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ))) ^ k := h3
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  calc ω ^ k = (MulAut.congr e).symm (ω' ^ k) := by
        dsimp only [ω]
        rw [map_zpow]
    _ = (MulAut.congr e).symm (congrHom e z) := by rw [hzpow]
    _ = z := (MulAut.congr e).symm_apply_apply z

theorem k_OmegaPlusFour_twoNat_scalar_of_isoMod {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)}
    (hsum : SumOfNatIsoMod (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2) :
    ∃ ω ∈ Subgroup.centralizer (X : Set (MulAut W)),
      (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * ω = ω * c) ∧
      orderOf ω = 3 ∧ (∀ v : W, ω v = v → v = 1) ∧
      (∀ z ∈ Subgroup.centralizer (X : Set (MulAut W)),
        (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * z = z * c) →
          z ∈ Subgroup.zpowers ω) := by
  classical
  obtain ⟨K, hKfield, hKfinite, π, hK4, hsumvia⟩ :=
    exists_sumOfNatVia_of_sumOfNatIsoMod_omegaPlus hsum
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := 2)
      Nat.prime_two (by rw [hK4]; norm_num)
  exact @omegaPlusTwoNatScalarIso_aux K hKfield hKfinite hchar W _ _ X hK4 π hsumvia

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
