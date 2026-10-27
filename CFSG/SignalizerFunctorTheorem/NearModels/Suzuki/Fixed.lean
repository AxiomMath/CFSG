module

public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.LieType.Ree.SuzukiBruhatNormalForm

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.NearModels.Suzuki

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI CFSG.Open

variable {a : ℕ} {K : Type} [Field K]

theorem pow_eq_self_of_sq {x : K} (hx : x ^ 2 = x) {k : ℕ} (hk : 0 < k) : x ^ k = x := by
  induction k, hk using Nat.le_induction with
  | base => exact pow_one x
  | succ k hk ih => rw [pow_succ, ih, ← sq, hx]

theorem suzukiS_eq_of_sq {x y : K} (hx : x ^ 2 = x) (hy : y ^ 2 = y) (b : ℕ) :
    suzukiS a x y = suzukiS b x y := by
  have h1 : ∀ k, 0 < k → x ^ k = x := fun k hk => pow_eq_self_of_sq hx hk
  have h2 : ∀ k, 0 < k → y ^ k = y := fun k hk => pow_eq_self_of_sq hy hk
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, suzukiN, h1 _ (by positivity : 0 < 2 ^ (a + 1)),
      h1 _ (by positivity : 0 < 2 ^ (a + 1) + 2), h1 _ (by positivity : 0 < 2 ^ (a + 1) + 1),
      h2 _ (by positivity : 0 < 2 ^ (a + 1)), h1 _ (by positivity : 0 < 2 ^ (b + 1)),
      h1 _ (by positivity : 0 < 2 ^ (b + 1) + 2), h1 _ (by positivity : 0 < 2 ^ (b + 1) + 1),
      h2 _ (by positivity : 0 < 2 ^ (b + 1))]

variable [CharP K 2]

variable (K) in
@[expose] def primeEmb : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

theorem primeEmb_pow (y : ZMod 2) {k : ℕ} (hk : 0 < k) :
    primeEmb K y ^ k = primeEmb K y := by
  rw [← map_pow]
  congr 1
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) y with rfl | rfl
  · exact zero_pow hk.ne'
  · exact one_pow k

theorem exists_primeEmb_eq {x : K} (hx : x ^ 2 = x) : ∃ y : ZMod 2, primeEmb K y = x := by
  have h : x * (x - 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨0, (map_zero _).trans h.symm⟩
  · exact ⟨1, (map_one _).trans (sub_eq_zero.1 h).symm⟩

theorem map_primeEmb_suzukiS (u v : ZMod 2) :
    (suzukiS 0 u v).map (primeEmb K) = suzukiS a (primeEmb K u) (primeEmb K v) := by
  rw [map_suzukiS, suzukiS_eq_of_sq (a := 0) (primeEmb_pow u two_pos) (primeEmb_pow v two_pos) a]

variable (a K) in
theorem map_primeEmb_suzukiGroup_le :
    (suzukiGroup 0 (ZMod 2)).map (Matrix.GeneralLinearGroup.map (primeEmb K)) ≤
      suzukiGroup a K := by
  rw [Subgroup.map_le_iff_le_comap, suzukiGroup, Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  refine Subgroup.subset_closure ?_
  rcases hx with ⟨u, v, hx⟩ | ⟨l, hx⟩ | hx
  · refine Or.inl ⟨primeEmb K u, primeEmb K v, ?_⟩
    change (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (primeEmb K) = _
    rw [hx, map_primeEmb_suzukiS]
  · obtain rfl : l = 1 := (by decide : ∀ l : (ZMod 2)ˣ, l = 1) l
    refine Or.inr (Or.inl ⟨1, ?_⟩)
    change (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (primeEmb K) = _
    rw [hx, suzukiD_one, suzukiD_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine Or.inr (Or.inr ?_)
    change (x : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (primeEmb K) = _
    rw [hx, map_suzukiW]

variable (a K) in
@[expose] def szPrimeHom : suzukiGroup 0 (ZMod 2) →* suzukiGroup a K :=
  ((Matrix.GeneralLinearGroup.map (primeEmb K)).comp (suzukiGroup 0 (ZMod 2)).subtype).codRestrict _
    fun g => map_primeEmb_suzukiGroup_le a K (Subgroup.mem_map_of_mem _ g.2)

theorem coe_szPrimeHom (g : suzukiGroup 0 (ZMod 2)) :
    (((szPrimeHom a K g : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (primeEmb K) :=
  rfl

theorem szPrimeHom_injective : Function.Injective (szPrimeHom a K) := by
  intro g h hgh
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => (primeEmb K).injective ?_))
  have := congrArg (fun x : suzukiGroup a K => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j)
    hgh
  exact this

theorem szPrimeHom_S (u v : ZMod 2) :
    szPrimeHom a K (suzukiSElt 0 (ZMod 2) u v) = suzukiSElt a K (primeEmb K u) (primeEmb K v) :=
  suzukiSElt_ext (by rw [coe_szPrimeHom, coe_suzukiSElt, coe_suzukiSElt, map_primeEmb_suzukiS])

theorem szPrimeHom_W :
    szPrimeHom a K (suzukiWElt 0 (ZMod 2)) = suzukiWElt a K :=
  suzukiSElt_ext (by rw [coe_szPrimeHom, coe_suzukiWElt, coe_suzukiWElt, map_suzukiW])

theorem szFieldAut_szPrimeHom {σ : RingAut K} (hσ : ∀ x, σ x = x ^ 2)
    (g : suzukiGroup 0 (ZMod 2)) : szFieldAut a K σ (szPrimeHom a K g) = szPrimeHom a K g := by
  refine suzukiSElt_ext (Matrix.ext fun i j => ?_)
  change σ (primeEmb K (((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j)) =
    primeEmb K (((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j)
  rw [hσ, primeEmb_pow _ two_pos]

theorem suzukiSElt_mem_range
    {u v : K} (hu : u ^ 2 = u) (hv : v ^ 2 = v) :
    suzukiSElt a K u v ∈ (szPrimeHom a K).range := by
  obtain ⟨u₀, rfl⟩ := exists_primeEmb_eq hu
  obtain ⟨v₀, rfl⟩ := exists_primeEmb_eq hv
  exact ⟨suzukiSElt 0 (ZMod 2) u₀ v₀, szPrimeHom_S u₀ v₀⟩

theorem suzukiWElt_mem_range :
    suzukiWElt a K ∈ (szPrimeHom a K).range :=
  ⟨suzukiWElt 0 (ZMod 2), szPrimeHom_W⟩

omit [CharP K 2] in
theorem eq_one_of_map_eq {σ : RingAut K} (hσ : ∀ x, σ x = x ^ 2) {l : Kˣ}
    (h : l = Units.map (σ : K →* K) l) : l = 1 := by
  have h1 : (l : K) = (l : K) ^ 2 := by
    have := congrArg (fun x : Kˣ => (x : K)) h
    simpa [hσ] using this
  exact Units.ext (mul_left_cancel₀ l.ne_zero (by linear_combination -h1 : (l : K) * l = l * 1))

theorem mem_range_szPrimeHom_of_fixed
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {σ : RingAut K} (hσ : ∀ x, σ x = x ^ 2) {g : suzukiGroup a K}
    (hg : szFieldAut a K σ g = g) : g ∈ (szPrimeHom a K).range := by
  obtain ⟨hcases, -, huniq1, huniq2⟩ := suzuki_bruhat_normal_form hK g
  have hsq : ∀ x : K, σ x = x → x ^ 2 = x := fun x hx => (hσ x).symm.trans hx
  rcases hcases with ⟨u, v, l, rfl⟩ | ⟨u, v, l, c, d, rfl⟩
  · simp only [map_mul, szFieldAut_S, szFieldAut_D] at hg
    obtain ⟨h1, h2, h3⟩ := huniq1 u v (σ u) (σ v) l _ rfl hg.symm
    obtain rfl := eq_one_of_map_eq hσ h3
    rw [suzukiDElt_one, mul_one]
    exact suzukiSElt_mem_range (hsq u h1.symm) (hsq v h2.symm)
  · simp only [map_mul, szFieldAut_S, szFieldAut_D, szFieldAut_W] at hg
    obtain ⟨h1, h2, h3, h4, h5⟩ := huniq2 u v c d (σ u) (σ v) (σ c) (σ d) l _ rfl hg.symm
    obtain rfl := eq_one_of_map_eq hσ h3
    rw [suzukiDElt_one, mul_one]
    exact mul_mem (mul_mem (suzukiSElt_mem_range (hsq u h1.symm) (hsq v h2.symm))
      suzukiWElt_mem_range) (suzukiSElt_mem_range (hsq c h4.symm) (hsq d h5.symm))

theorem signalizerFixedSubgroup_szFieldAut
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {σ : RingAut K} (hσ : ∀ x, σ x = x ^ 2) :
    signalizerFixedSubgroup (szFieldAut a K σ) = (szPrimeHom a K).range := by
  ext g
  refine ⟨mem_range_szPrimeHom_of_fixed hK hσ, ?_⟩
  rintro ⟨h, rfl⟩
  exact szFieldAut_szPrimeHom hσ h

theorem nonempty_fixed_szFieldAut_equiv
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {σ : RingAut K} (hσ : ∀ x, σ x = x ^ 2) :
    Nonempty (signalizerFixedSubgroup (szFieldAut a K σ) ≃* suzukiGroup 0 (ZMod 2)) :=
  ⟨(MulEquiv.subgroupCongr (signalizerFixedSubgroup_szFieldAut hK hσ)).trans
    (MonoidHom.ofInjective szPrimeHom_injective).symm⟩

end CFSG.SignalizerFunctorTheorem.NearModels.Suzuki
