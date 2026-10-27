module

public import CFSG.Quasithin.Background.G64RealizeSec

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem exists_scalar_of_realizes {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {V C : Subgroup W} {F : Type} [Field F] {Γ : Subgroup (GL (Fin 3) F)} {ω : Fˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hωΓ : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ Γ)
    (h : (FFModel.nat Γ).Realizes L V C) :
    ∃ z ∈ L, z ^ 3 = 1 ∧ (∀ l ∈ L, z * l = l * z) ∧ ∀ v ∈ V, z v * v⁻¹ ∈ C → v ∈ C := by
  obtain ⟨π, hπ⟩ := h
  have hπs := hπ.1
  obtain ⟨f, -, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl hπ
  set γ₀ : (FFModel.nat Γ).Gam := (⟨_, hωΓ⟩ : ↥Γ) with hγ₀
  set z : MulAut W := ((π γ₀ : ↥L) : MulAut W) with hz
  have hγ₀3 : γ₀ ^ 3 = 1 := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.scalar (Fin 3) ω) ^ 3 = 1
    rw [← map_pow, hω3, map_one]
  refine ⟨z, (π γ₀).2, ?_, ?_, ?_⟩
  · have h1 : π γ₀ ^ 3 = 1 := by rw [← map_pow, hγ₀3, map_one]
    have h2 := congrArg (fun y : ↥L => (y : MulAut W)) h1
    simpa [hz] using h2
  · intro l hl
    obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
    have hc : γ₀ * γ = γ * γ₀ := by
      obtain ⟨g, hg⟩ := γ
      apply Subtype.ext
      change Matrix.GeneralLinearGroup.scalar (Fin 3) ω * g =
        g * Matrix.GeneralLinearGroup.scalar (Fin 3) ω
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute (ω : F) (fun r => Commute.all (ω : F) r) _).eq
    have := congrArg (fun x : ↥L => (x : MulAut W)) (congrArg π hc)
    simp only [map_mul, Subgroup.coe_mul, hγ] at this
    exact this
  · intro v hv hzv
    have hzvV : z v ∈ V := hπ.2.2.2.1 (π γ₀) v hv
    have h1 : f ⟨z v, hzvV⟩ = f ⟨v, hv⟩ := by
      have h2 : f (⟨z v, hzvV⟩ * (⟨v, hv⟩ : ↥V)⁻¹) = 1 := (hfk _).mpr hzv
      rwa [map_mul, map_inv, mul_inv_eq_one] at h2
    have h3 := hfe γ₀ ⟨v, hv⟩ hzvV
    rw [h1] at h3
    set x : Fin 3 → F := Multiplicative.toAdd ((f ⟨v, hv⟩ : ↥(FFModel.nat Γ).sec) :
      (FFModel.nat Γ).Amb) with hx
    have h4 : (ω : F) • x = x := by
      have h5 := congrArg Multiplicative.toAdd h3
      change x = Multiplicative.toAdd (natAct Γ γ₀ (Multiplicative.ofAdd x)) at h5
      rw [natAct, toAdd_ofAdd, toAdd_ofAdd] at h5
      conv_rhs => rw [h5]
      change (ω : F) • x = Matrix.mulVec
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) x
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
    have hx0 : x = 0 := by
      have h6 : ((ω : F) - 1) • x = 0 := by rw [sub_smul, one_smul, h4, sub_self]
      have hne : (ω : F) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        intro h7
        exact hω1 (Units.ext h7)
      exact (smul_eq_zero.mp h6).resolve_left hne
    apply (hfk ⟨v, hv⟩).mp
    apply Subtype.ext
    have e1 : ((f ⟨v, hv⟩ : ↥(FFModel.nat Γ).sec) : (FFModel.nat Γ).Amb) =
        Multiplicative.ofAdd x := rfl
    change ((f ⟨v, hv⟩ : ↥(FFModel.nat Γ).sec) : (FFModel.nat Γ).Amb) = 1
    rw [e1, hx0]
    rfl

theorem exists_cube_root {F : Type} [Field F] [Finite F] (h3 : 3 ∣ Nat.card F - 1) :
    ∃ ω : Fˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_units]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (hcard ▸ h3)
  refine ⟨ω, ?_, ?_⟩
  · rw [← hω]
    exact pow_orderOf_eq_one ω
  · intro h1
    rw [h1, orderOf_one] at hω
    omega

theorem exists_scalar_su38 {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {V C : Subgroup W} (h : BinaryNaturalSU3 L V C 3) :
    ∃ z ∈ L, z ^ 3 = 1 ∧ (∀ l ∈ L, z * l = l * z) ∧ ∀ v ∈ V, z v * v⁻¹ ∈ C → v ∈ C := by
  obtain ⟨F, _, _, hF, hR⟩ := h
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root (F := F) (by rw [hF]; norm_num)
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈
      {A : GL (Fin 3) F | (A : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
        Matrix.transpose ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ 3))) *
          (A : Matrix (Fin 3) (Fin 3) F) = 1} := ⟨?_, ?_⟩
  · exact exists_scalar_of_realizes hω3 hω1 (Subgroup.subset_closure hmem) hR
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_const, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  · have hω9 : (ω : F) ^ (2 ^ 3) * ω = 1 := by
      rw [← pow_succ, show 2 ^ 3 + 1 = 3 * 3 by norm_num, pow_mul, ← Units.val_pow_eq_pow_val,
        hω3, Units.val_one, one_pow]
    ext i j
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    have hω8 : (ω : F) ^ 8 * ω = 1 := by simpa using hω9
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij
        simp [hω8]
      · simp [hij]
    · intro b _ hb
      split_ifs <;> simp_all
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem exists_scalar_sl34 {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {V C : Subgroup W} (h : BinaryNaturalSL L V C 3 2) :
    ∃ z ∈ L, z ^ 3 = 1 ∧ (∀ l ∈ L, z * l = l * z) ∧ ∀ v ∈ V, z v * v⁻¹ ∈ C → v ∈ C := by
  obtain ⟨F, _, _, hF, hR⟩ := h
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root (F := F) (by rw [hF]; norm_num)
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈
      {A : GL (Fin 3) F | (A : Matrix (Fin 3) (Fin 3) F).det = 1} := by
    show ((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_const, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  exact exists_scalar_of_realizes hω3 hω1 (Subgroup.subset_closure hmem) hR

theorem fixV_eq_bot_of_scalar {W : Type*} [CommGroup W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hcomm : commV L = ⊤) {z : MulAut W} (hzL : z ∈ L)
    (hz3 : z ^ 3 = 1) (hzc : ∀ l ∈ L, z * l = l * z)
    (hfp : ∀ w : W, z w * w⁻¹ ∈ fixV L → w ∈ fixV L) : fixV L = ⊥ := by
  have hzzz : ∀ w : W, z (z (z w)) = w := fun w => by
    have := congrArg (fun φ : MulAut W => φ w) hz3
    simpa [pow_succ, MulAut.mul_apply] using this
  let a : W →* W :=
    { toFun := fun w => w * z w * z (z w)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul]
        abel }
  have ha : ∀ w, a w = w * z w * z (z w) := fun w => rfl
  have haC : ∀ w, a w ∈ fixV L := by
    intro w
    apply hfp
    rw [ha, map_mul, map_mul, hzzz]
    have : z w * z (z w) * w * (w * z w * z (z w))⁻¹ = 1 := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    rw [this]
    exact (fixV L).one_mem
  have hal : ∀ l ∈ L, ∀ w, a (l w) = l (a w) := by
    intro l hl w
    have hz1 : ∀ u, z (l u) = l (z u) := fun u => by
      have := congrArg (fun φ : MulAut W => φ u) (hzc l hl)
      simpa [MulAut.mul_apply] using this
    rw [ha, ha, hz1, hz1, map_mul, map_mul]
  have hker : commV L ≤ a.ker := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hal l hl, haC w l hl,
      mul_inv_cancel]
  rw [hcomm] at hker
  rw [eq_bot_iff]
  intro c hc
  have hzc' : z c = c := hc z hzL
  have h1 : a c = c := by
    rw [ha, hzc', hzc', mul_assoc, ← sq, hW2, mul_one]
  have h2 : a c = 1 := hker (Subgroup.mem_top c)
  rw [Subgroup.mem_bot, ← h1, h2]

end CFSG.Quasithin.H13.A6.A6S20
