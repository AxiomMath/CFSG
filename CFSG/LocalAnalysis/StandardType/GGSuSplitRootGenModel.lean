module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LieType.SeitzGeneration.UnitarySplit
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.Assembly TableB CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration

private theorem eq_one_of_mem_unitaryScalars_of_not_dvd {K : Type} [Field K] {n d p : ℕ}
    (h : UnitaryFieldData 2 n K) (hd : 1 ≤ d) (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ n + 1)
    {z : ↥(unitarySU 2 n K d)} (hz : z ∈ unitaryScalars h d) (hzp : z ^ p = 1) : z = 1 := by
  obtain ⟨c, hc, -, hg⟩ := mem_unitaryScalars.mp hz
  have hcp : c ^ p = 1 := by
    have h1 : ((GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) ^ p) = 1 := by
      rw [← hg, ← Subgroup.coe_pow, hzp]
      rfl
    have h2 := congrArg (fun g : GL (Fin d) K =>
      ((g : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩)) h1
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at h2
    change ((diagonal (fun _ : Fin d => (c : K))) ^ p) ⟨0, hd⟩ ⟨0, hd⟩ = 1 at h2
    rw [Matrix.diagonal_pow] at h2
    exact Units.ext (by simpa using h2)
  have hcq : c ^ (2 ^ n + 1) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← h.norm_eq_pow]
    exact hc)
  have hcop : Nat.Coprime p (2 ^ n + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have hc1 : c = 1 := by
    have h4 := pow_gcd_eq_one (a := c) (m := p) (n := 2 ^ n + 1) |>.mpr ⟨hcp, hcq⟩
    rwa [hcop, pow_one] at h4
  have hz1 : (z : GL (Fin d) K) = 1 := by rw [hg, hc1]; rfl
  exact Subtype.ext hz1

private theorem diag_data {K : Type} [Field K] {n r ε p : ℕ} {h : UnitaryFieldData 2 n K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    {w : HypIndex r ε → (Fin (2 * r + ε) → K)}
    (hwR : ∀ a, R *ᵥ (Pi.single a (1 : K)) = w a)
    (y : ↥(unitarySU 2 n K (2 * r + ε)))
    (hev : ∀ a, ∃ c : K,
      (((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) *ᵥ
        w a = c • w a)
    (hyp : y ^ p = 1) :
    ∃ c : HypIndex r ε → K,
      ((((hypTransport h hR).symm y : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal c ∧
      (∀ a, h.bar (c a) * c (hypPartner a) = 1) ∧ (∀ a, c a ^ p = 1) := by
  classical
  choose c hc using hev
  have hcol : ∀ a, (transportInv h R *
      (((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) * R) *ᵥ
        (Pi.single a (1 : K)) = c a • (Pi.single a (1 : K)) := by
    intro a
    calc (transportInv h R *
        (((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) * R) *ᵥ
          (Pi.single a (1 : K))
        = (transportInv h R *
            (((y : GL (Fin (2 * r + ε)) K) :
              Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K))) *ᵥ
              (R *ᵥ (Pi.single a (1 : K))) := by rw [← Matrix.mulVec_mulVec]
      _ = (transportInv h R *
            (((y : GL (Fin (2 * r + ε)) K) :
              Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K))) *ᵥ w a := by rw [hwR a]
      _ = transportInv h R *ᵥ
            ((((y : GL (Fin (2 * r + ε)) K) :
              Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) *ᵥ w a) := by
            rw [← Matrix.mulVec_mulVec]
      _ = transportInv h R *ᵥ (c a • w a) := by rw [hc a]
      _ = c a • (transportInv h R *ᵥ w a) := by rw [Matrix.mulVec_smul]
      _ = c a • (transportInv h R *ᵥ (R *ᵥ (Pi.single a (1 : K)))) := by rw [hwR a]
      _ = c a • ((transportInv h R * R) *ᵥ (Pi.single a (1 : K))) := by
            rw [Matrix.mulVec_mulVec]
      _ = c a • (Pi.single a (1 : K)) := by rw [transportInv_mul hR, Matrix.one_mulVec]
  have hdiag : (transportInv h R *
      (((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) * R) =
        diagonal c := by
    refine Matrix.ext_of_mulVec_single fun a => ?_
    rw [hcol a, Matrix.mulVec_single_one]
    funext i
    rw [Matrix.col_apply]
    by_cases hia : i = a
    · subst hia; simp
    · simp [hia]
  have hcoe : ((((hypTransport h hR).symm y : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal c := by
    rw [coe_hypTransport_symm hR y]
    exact hdiag
  have hsingle : ∀ a : HypIndex r ε,
      hypForm h r ε (Pi.single a (1 : K)) (Pi.single (hypPartner a) (1 : K)) = 1 := by
    intro a
    rw [hypForm_apply, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  have hrel : ∀ a, h.bar (c a) * c (hypPartner a) = 1 := by
    intro a
    set g : hypSU h r ε := (hypTransport h hR).symm y with hg
    have hga : g • (Pi.single a (1 : K) : HypIndex r ε → K) =
        c a • (Pi.single a (1 : K) : HypIndex r ε → K) := by
      change (((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ
          (Pi.single a (1 : K) : HypIndex r ε → K) = _
      rw [show ((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal c from hcoe,
        Matrix.mulVec_single_one]
      funext i
      rw [Matrix.col_apply]
      by_cases hia : i = a
      · subst hia; simp
      · simp [hia]
    have hgb : g • (Pi.single (hypPartner a) (1 : K) : HypIndex r ε → K) =
        c (hypPartner a) • (Pi.single (hypPartner a) (1 : K) : HypIndex r ε → K) := by
      change (((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ
          (Pi.single (hypPartner a) (1 : K) : HypIndex r ε → K) = _
      rw [show ((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal c from hcoe,
        Matrix.mulVec_single_one]
      funext i
      rw [Matrix.col_apply]
      by_cases hia : i = hypPartner a
      · subst hia; simp
      · simp [hia]
    have hiso := hypForm_smul_smul h g (Pi.single a (1 : K))
      (Pi.single (hypPartner a) (1 : K))
    rw [hga, hgb, hsingle a] at hiso
    have h1 : c (hypPartner a) * h.bar (c a) = 1 := by
      simpa [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hsingle a, mul_one] using hiso
    calc h.bar (c a) * c (hypPartner a) = c (hypPartner a) * h.bar (c a) := mul_comm _ _
      _ = 1 := h1
  have hyp' : ((hypTransport h hR).symm y) ^ p = 1 := by
    rw [← map_pow, hyp, map_one]
  have hcp : ∀ a, c a ^ p = 1 := by
    intro a
    have h1 : (((((hypTransport h hR).symm y) ^ p : hypSU h r ε) :
        GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1 := by
      rw [hyp']
      simp
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe, Matrix.diagonal_pow] at h1
    simpa [Matrix.diagonal_apply_eq] using h1
  exact ⟨c, hcoe, hrel, hcp⟩

private theorem eq_one_of_mem_hypScalars_splitTorus {K : Type} [Field K] {n r ε p : ℕ}
    {h : UnitaryFieldData 2 n K} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ)
    {t : Multiplicative (Fin r → ZMod p)} (hmem : τ t ∈ hypScalars h r ε) : t = 1 := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hmem
  have hdiag : (((τ t : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (splitEntries (ε := ε) ζ (Multiplicative.toAdd t)) := by
    have h := hτ (Multiplicative.toAdd t)
    rwa [ofAdd_toAdd] at h
  have hmat : diagonal (splitEntries (ε := ε) ζ (Multiplicative.toAdd t)) =
      Matrix.scalar (HypIndex r ε) (c : K) := by
    rw [← hdiag, hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hEj : ∀ j, splitEntries (ε := ε) ζ (Multiplicative.toAdd t) (.inl j) = (c : K) := by
    intro j
    have h := congrFun (congrFun hmat (.inl j)) (.inl j)
    simpa [Matrix.scalar_apply] using h
  have hFj : ∀ j, splitEntries (ε := ε) ζ (Multiplicative.toAdd t) (.inr (.inr j)) = (c : K) := by
    intro j
    have h := congrFun (congrFun hmat (.inr (.inr j))) (.inr (.inr j))
    simpa [Matrix.scalar_apply] using h
  have hval : ∀ j, ((Multiplicative.toAdd t) j).val = 0 := by
    intro j
    have h1 : splitEntries (ε := ε) ζ (Multiplicative.toAdd t) (.inl j) =
        splitEntries (ε := ε) ζ (Multiplicative.toAdd t) (.inr (.inr j)) := by
      rw [hEj j, hFj j]
    have heq : ζ ^ ((Multiplicative.toAdd t) j).val =
        (ζ ^ ((Multiplicative.toAdd t) j).val)⁻¹ := by
      simpa [splitEntries] using h1
    have hsq : ζ ^ (2 * ((Multiplicative.toAdd t) j).val) = 1 := by
      have h1 : (ζ ^ ((Multiplicative.toAdd t) j).val) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [heq]
        exact inv_mul_cancel₀ (pow_ne_zero _ (hζ.ne_zero hp.ne_zero))
      rwa [← pow_mul, Nat.mul_comm] at h1
    have hdvd : p ∣ 2 * ((Multiplicative.toAdd t) j).val :=
      (hζ.pow_eq_one_iff_dvd _).mp hsq
    have hnot : ¬ p ∣ 2 := by
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hdvd' : p ∣ ((Multiplicative.toAdd t) j).val := by
      rcases (hp.dvd_mul).mp hdvd with h | h
      · exact absurd h hnot
      · exact h
    rcases Nat.eq_zero_or_pos ((Multiplicative.toAdd t) j).val with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd h hdvd') (by
        have := ZMod.val_lt ((Multiplicative.toAdd t) j)
        omega)
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_one]
  funext j
  exact (ZMod.val_eq_zero _).mp (hval j)

theorem exists_isCoverTorusModel
    {K : Type} [Field K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 4 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n - 1)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φa ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)),
      ∀ l, φa (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    ∃ (r ε : ℕ) (h : UnitaryFieldData 2 n K) (ζ : K)
      (τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε) (φ : hypSU h r ε →* L'),
      2 * r + ε = d ∧ ε ≤ 1 ∧ IsPrimitiveRoot ζ p ∧ h.bar ζ = ζ ∧ IsSplitTorus h ζ τ ∧
        Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (hypSU h r ε) ∧
        (∀ z ∈ φ.ker, z ^ p = 1 → z = 1) ∧ IsCoverTorusModel φ τ A ∧
        ∀ t, φ (τ t) ∈ Subgroup.center L' → t = 1 := by
  classical
  have hKpos : 0 < Nat.card K := by rw [hK]; positivity
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 : Nat.card K = 1 := by simpa using hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h
  have h := TableBU.unitaryFieldData_of_card hK hn1
  haveI : CharP K 2 := h.charP
  have hp2 : p ≠ 2 := by
    intro h2
    have hodd : Odd (2 ^ n - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ]
      refine ⟨2 ^ m - 1, ?_⟩
      have hpos : 0 < 2 ^ m := by positivity
      omega
    have h2dvd : 2 ∣ 2 ^ n - 1 := h2 ▸ hpq
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨l, hl⟩ := h2dvd
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn2 : 2 ≤ n := by
    have hpos : 0 < 2 ^ n - 1 := by
      have h1 : 1 < 2 ^ n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · omega
        · exact Nat.one_lt_two_pow (by omega)
      omega
    have hge : p ≤ 2 ^ n - 1 := Nat.le_of_dvd hpos hpq
    have h4 : 4 ≤ 2 ^ n := by omega
    have h4' : 2 ^ 2 ≤ 2 ^ n := by norm_num; exact h4
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp h4'
  have hpq' : ¬ p ∣ 2 ^ n + 1 := by
    intro hdiv
    have h2 : p ∣ 2 := by
      have hp1 : 1 ≤ 2 ^ n := Nat.one_le_pow' n 1
      have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hdiv hpq
      convert hsub using 2 <;> omega
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ d = 2 * r + ε :=
    ⟨d / 2, d % 2, by omega, by omega⟩
  have hd4 : 4 ≤ 2 * r + ε := hd
  have hd1 : 1 ≤ 2 * r + ε := by omega
  have hdq : (2 * r + ε, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + ε)) K (2 ^ n))) =
      ⊥ := TableBUE.center_proj_eq_bot hK (by omega) hdq
  let proj : ↥(unitarySU 2 n K (2 * r + ε)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + ε)) K (2 ^ n)) :=
    LargeEvenProjMk (unitarySU 2 n K (2 * r + ε))
  have hproj : Function.Surjective proj := QuotientGroup.mk'_surjective _
  set Λ : LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + ε)) K (2 ^ n)) →* MulAut L' :=
    ReflInner.liftConj ψ hψ hker
  have hΛinj : Function.Injective Λ := ReflInner.liftConj_injective hψ hker hZ
  have hΛmap : ∀ (e : LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + ε)) K (2 ^ n)))
      (l : L'), ψ (Λ e l) = e * ψ l * e⁻¹ := ReflInner.map_liftConj_apply hψ hker
  have hq : ¬((2 * r + ε) = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨h1, h2⟩
    omega
  have hAΛ : ∀ a ∈ A,
      ∃ e : LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + ε)) K (2 ^ n)), Λ e = a := by
    intro a ha
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l : L', (φa ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
    have hφp : φa ^ p = 1 := by
      refine MulEquiv.ext fun q => ?_
      obtain ⟨l, rfl⟩ := hψ q
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ :=
      CFSG.StandardType.NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn1 (by omega) hq hp
        hpq' φa hφaI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφa l, MulAut.conj_apply]
  set E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + ε)) K (2 ^ n))) :=
    A.comap Λ with hEdef
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact CFSG.Open.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hnp : ∀ z ∈ proj.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    refine eq_one_of_mem_unitaryScalars_of_not_dvd h hd1 hp hpq' ?_ hzp
    rw [unitaryScalars_eq h hd1]
    change z ∈ (LargeEvenProjMk (unitarySU 2 n K (2 * r + ε))).ker at hz
    rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hz
    exact hz
  obtain ⟨A', hA'map, -, hA'ab, hA'card⟩ :=
    TableBUE.exists_lift_of_noTorsion proj hproj hp hnp hE
  set ρ := unitaryRep (ℓ := 2) (f := n) (n := 2 * r + ε) (K := K) A' with hρdef
  let S : A' → Module.End K (Fin (2 * r + ε) → K) := fun x =>
    ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K))
  have hScomm : ∀ x y, Commute (S x) (S y) := by
    intro x y
    have hxy : x * y = y * x := Subtype.ext (CFSG.Open.IsElemAbelian.comm hA'ab x.2 y.2)
    show S x * S y = S y * S x
    simp only [S, ← Units.val_mul, ← map_mul, hxy]
  have hSpow : ∀ x, S x ^ p = 1 := by
    intro x
    have hx : x ^ p = 1 := Subtype.ext (hA'ab.2 x x.2)
    show ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K)) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  have hSiso : ∀ x v w,
      stdB h (2 * r + ε) (S x v) (S x w) = stdB h (2 * r + ε) v w :=
    fun x v w => mem_sesqUnitaryGroup.mp (unitaryRep_mem h A' x) v w
  obtain ⟨w, hw, hev⟩ := exists_adapted_hypFamily h hp hp2 hpq hε r
    (V := Fin (2 * r + ε) → K) (B := stdB h (2 * r + ε))
    (gramForm_isSymm h (by simp)) (gramForm_separatingLeft h (by simp)) (by simp)
    S hScomm hSpow hSiso
  let R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K := Matrix.of fun k x => w x k
  have hwR : ∀ a, R *ᵥ (Pi.single a (1 : K)) = w a := by
    intro a
    funext k
    simp [R]
  have hR : IsHypTransport h R := by
    change (R.map h.bar)ᵀ * R = hypGram r ε K
    ext x y
    rw [Matrix.mul_apply, ← hw x y, stdB, gramForm_apply]
    simp [R, dotProduct, Matrix.mul_apply]
  let T : hypSU h r ε ≃* ↥(unitarySU 2 n K (2 * r + ε)) := hypTransport h hR
  have hevY : ∀ y : A', ∀ a, ∃ c : K,
      ((((y : ↥(unitarySU 2 n K (2 * r + ε))) : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) *ᵥ w a = c • w a := by
    intro y a
    obtain ⟨c, hc⟩ := hev y a
    refine ⟨c, ?_⟩
    have hc' := unitaryRep_apply A' y (w a)
    rw [hc'] at hc
    simpa using hc
  have hdvdK : p ∣ Nat.card K - 1 := by
    rw [hK]
    have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [h1]
    exact dvd_mul_of_dvd_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvdK
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hbarζ : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζp
  obtain ⟨τ, hτ⟩ := exists_isSplitTorus (n := n) (r := r) (ε := ε) (p := p) h hp hζp hbarζ
  have hexists_t : ∀ (y : ↥(unitarySU 2 n K (2 * r + ε))) (hy : y ∈ A'),
      ∃ t : Multiplicative (Fin r → ZMod p), T.symm y = τ t := by
    intro y hy
    obtain ⟨c, hd, hrel, hcp⟩ := diag_data hR hwR y (hevY ⟨y, hy⟩) (hA'ab.2 y hy)
    have hbar : ∀ a, h.bar (c a) = c a := fun a =>
      bar_eq_self_of_pow_eq_one h hpq (hcp a)
    choose k hklt hk using fun a => hζ.eq_pow_of_pow_eq_one (hcp a)
    let t : Fin r → ZMod p := fun i => (k (.inl i) : ZMod p)
    have htval : ∀ i, (t i).val = k (.inl i) := fun i => ZMod.val_natCast_of_lt (hklt _)
    have hsplit : ∀ a, c a = splitEntries ζ t a := by
      intro a
      rcases a with i | j | i
      · rw [show splitEntries ζ t (.inl i) = ζ ^ (t i).val from rfl, htval i]
        exact (hk (.inl i)).symm
      · rw [show splitEntries ζ t (.inr (.inl j)) = 1 from rfl]
        have h := hrel (.inr (.inl j))
        rw [hypPartner_inr_inl, hbar] at h
        exact eq_one_of_sq_eq_one_of_pow_eq_one hp2 hp (hcp _)
          (by rw [pow_two]; exact h)
      · rw [show splitEntries ζ t (.inr (.inr i)) = (ζ ^ (t i).val)⁻¹ from rfl, htval i]
        have h := hrel (.inl i)
        rw [hypPartner_inl, hbar] at h
        rw [← hk (.inl i)] at h
        exact eq_inv_of_mul_eq_one_right h
    refine ⟨Multiplicative.ofAdd t, ?_⟩
    have hτt : (((τ (Multiplicative.ofAdd t) : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal (splitEntries ζ t) := hτ t
    apply Subtype.ext
    apply Units.ext
    rw [hd, hτt]
    congr 1
    funext a
    exact hsplit a
  have hcover : ∃ φ₀ : ↥(unitarySU 2 n K (2 * r + ε)) →* L',
      ∀ s, ψ (φ₀ s) = proj s := by
    rcases (show 2 * r + ε = 4 ∨ 5 ≤ 2 * r + ε by omega) with hd4' | hd5
    · have he : Even (2 * r + ε) := hd4' ▸ (by norm_num : Even 4)
      have hq4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      refine LineU.exists_hom_of_sections proj ψ hψ hker ?_
      intro E _ _ π hπ hcen
      exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
        (F := K) (p := 2) (f := n) (n := 2 * r + ε) hK he hd hq4 hπ hcen
    · have hd6 : (2 * r + ε, n) ≠ (6, 1) := by
        intro h
        have hn : n = 1 := congrArg Prod.snd h
        rw [hn] at hpq
        norm_num at hpq
        exact hp.one_lt.ne' hpq
      obtain ⟨-, hcov⟩ := LineU.unitaryCoverAt hK hd5 hd6
      exact hcov L' ψ hψ hker hperf
  obtain ⟨φ₀, hφ₀⟩ := hcover
  have hφ₀s : Function.Surjective φ₀ :=
    LineU.surjective_of_cover proj hproj ψ hker hperf φ₀ hφ₀
  let φ : hypSU h r ε →* L' := φ₀.comp T.toMonoidHom
  have hφsurj : Function.Surjective φ := hφ₀s.comp T.surjective
  have hker_eq : (LargeEvenProjMk (unitarySU 2 n K (2 * r + ε))).ker =
      unitaryScalars h (2 * r + ε) := by
    rw [LargeEvenProjMk, QuotientGroup.ker_mk']
    exact (unitaryScalars_eq h hd1).symm
  have hφker : φ.ker ≤ Subgroup.center (hypSU h r ε) := by
    intro g hg
    have h1 : proj (T g) = 1 := by
      have h2 := hφ₀ (T g)
      rw [show φ₀ (T g) = 1 from hg, map_one] at h2
      exact h2.symm
    have h2 : T g ∈ unitaryScalars h (2 * r + ε) := by
      have h1' : T g ∈ (LargeEvenProjMk (unitarySU 2 n K (2 * r + ε))).ker :=
        MonoidHom.mem_ker.mpr h1
      rw [hker_eq] at h1'
      exact h1'
    have h3 : g ∈ hypScalars h r ε := (mem_hypScalars_iff_transport hR g).mpr h2
    exact normOneScalars_le_center h (hypSU h r ε) (2 * r + ε) h3
  have hφkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have h1 : proj (T z) = 1 := by
      have h2 := hφ₀ (T z)
      rw [show φ₀ (T z) = 1 from hz, map_one] at h2
      exact h2.symm
    have h2 : T z ∈ unitaryScalars h (2 * r + ε) := by
      have h1' : T z ∈ (LargeEvenProjMk (unitarySU 2 n K (2 * r + ε))).ker :=
        MonoidHom.mem_ker.mpr h1
      rw [hker_eq] at h1'
      exact h1'
    have h3 : T z = 1 := eq_one_of_mem_unitaryScalars_of_not_dvd h hd1 hp hpq' h2 (by
      rw [← map_pow, hzp, map_one])
    exact T.injective (by rw [h3, map_one])
  have hfwd : ∀ a ∈ A, ∃ t : Multiplicative (Fin r → ZMod p),
      a = MulAut.conj (φ (τ t)) := by
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    have heE : e ∈ E := by
      show Λ e ∈ A
      rw [he]
      exact ha
    have hemap : e ∈ A'.map proj := by
      rw [hA'map]
      exact heE
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hemap
    obtain ⟨t, ht⟩ := hexists_t y hy
    refine ⟨t, ?_⟩
    have hφτ : φ (τ t) = φ₀ y := by
      show φ₀ (T (τ t)) = φ₀ y
      rw [← ht, MulEquiv.apply_symm_apply]
    calc a = Λ e := he.symm
      _ = Λ (proj y) := by rw [hye]
      _ = MulAut.conj (φ₀ y) := ReflInner.liftConj_eq hψ hker (hφ₀ y)
      _ = MulAut.conj (φ (τ t)) := by rw [hφτ]
  have hmodel : IsCoverTorusModel φ τ A := by
    intro a
    constructor
    · exact hfwd a
    · rintro ⟨t, rfl⟩
      apply hsc (φ (τ t))
      · intro b hb
        obtain ⟨t', ht'⟩ := hfwd b hb
        have hcomm : τ t' * τ t = τ t * τ t' := by
          rw [← map_mul, ← map_mul, mul_comm]
        rw [ht', MulAut.conj_apply, ← map_mul, hcomm, map_mul, mul_assoc, mul_inv_cancel,
          mul_one]
      · have ht : t ^ p = 1 := by
          refine Multiplicative.toAdd.injective ?_
          rw [toAdd_pow, toAdd_one]
          funext i
          simp [Pi.smul_apply, nsmul_eq_mul]
        have htτ : (τ t) ^ p = 1 := by rw [← map_pow, ht, map_one]
        rw [← map_pow, htτ, map_one]
  refine ⟨r, ε, h, ζ, τ, φ, rfl, hε, hζ, hbarζ, hτ, hφsurj, hφker, hφkerp, hmodel, ?_⟩
  intro t ht
  have h1 : ψ (φ (τ t)) = 1 := by
    have hmem : ψ (φ (τ t)) ∈
        Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + ε)) K (2 ^ n))) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := hψ q
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subgroup.mem_center_iff.mp ht l)
    rwa [hZ, Subgroup.mem_bot] at hmem
  have h2 : proj (T (τ t)) = 1 := by
    have h3 := hφ₀ (T (τ t))
    rw [show φ₀ (T (τ t)) = φ (τ t) from rfl, h1] at h3
    exact h3.symm
  have h3 : T (τ t) ∈ unitaryScalars h (2 * r + ε) := by
    have h2' : T (τ t) ∈ (LargeEvenProjMk (unitarySU 2 n K (2 * r + ε))).ker :=
      MonoidHom.mem_ker.mpr h2
    rw [hker_eq] at h2'
    exact h2'
  have h4 : τ t ∈ hypScalars h r ε := (mem_hypScalars_iff_transport hR (τ t)).mpr h3
  exact eq_one_of_mem_hypScalars_splitTorus hp hp2 hζ hτ h4

theorem card_le_of_three {K : Type} [Field K] {n p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n - 1) {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φa ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n)),
      ∀ l, φa (ψ l) = ψ (a l)) :
    Nat.card A ≤ p := by
  classical
  have hKpos : 0 < Nat.card K := by rw [hK]; positivity
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 : Nat.card K = 1 := by simpa using hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h
  have h := TableBU.unitaryFieldData_of_card hK hn1
  haveI : CharP K 2 := h.charP
  have hp2 : p ≠ 2 := by
    intro h2
    have hodd : Odd (2 ^ n - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ]
      refine ⟨2 ^ m - 1, ?_⟩
      have hpos : 0 < 2 ^ m := by positivity
      omega
    have h2dvd : 2 ∣ 2 ^ n - 1 := h2 ▸ hpq
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨l, hl⟩ := h2dvd
    omega
  have hn2 : 2 ≤ n := by
    have hpos : 0 < 2 ^ n - 1 := by
      have h1 : 1 < 2 ^ n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · omega
        · exact Nat.one_lt_two_pow (by omega)
      omega
    have hge : p ≤ 2 ^ n - 1 := Nat.le_of_dvd hpos hpq
    have h4 : 4 ≤ 2 ^ n := by
      have := hp.two_le
      omega
    have h4' : 2 ^ 2 ≤ 2 ^ n := by norm_num; exact h4
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp h4'
  have hpq' : ¬ p ∣ 2 ^ n + 1 := by
    intro hdiv
    have h2 : p ∣ 2 := by
      have hp1 : 1 ≤ 2 ^ n := Nat.one_le_pow' n 1
      have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hdiv hpq
      convert hsub using 2 <;> omega
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdq : (3, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have h3 : n = 1 := Nat.pow_right_injective (a := 2) (by norm_num) (by
      show 2 ^ n = 2 ^ 1
      rw [h2])
    omega
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) = ⊥ :=
    TableBUE.center_proj_eq_bot hK (by norm_num) hdq
  let proj : ↥(unitarySU 2 n K 3) →*
      LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)) :=
    LargeEvenProjMk (unitarySU 2 n K 3)
  have hproj : Function.Surjective proj := QuotientGroup.mk'_surjective _
  set Λ : LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)) →* MulAut L' :=
    ReflInner.liftConj ψ hψ hker
  have hΛinj : Function.Injective Λ := ReflInner.liftConj_injective hψ hker hZ
  have hΛmap : ∀ (e : LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) (l : L'),
      ψ (Λ e l) = e * ψ l * e⁻¹ := ReflInner.map_liftConj_apply hψ hker
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have h3 : n = 1 := Nat.pow_right_injective (a := 2) (by norm_num) (by
      show 2 ^ n = 2 ^ 1
      rw [h2])
    omega
  have hAΛ : ∀ a ∈ A, ∃ e : LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)), Λ e = a := by
    intro a ha
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l : L', (φa ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
    have hφp : φa ^ p = 1 := by
      refine MulEquiv.ext fun q => ?_
      obtain ⟨l, rfl⟩ := hψ q
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ :=
      CFSG.StandardType.NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn1 (by omega) hq hp
        hpq' φa hφaI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφa l, MulAut.conj_apply]
  set E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) := A.comap Λ
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact CFSG.Open.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hmapA : E.map Λ = A := by
    ext a
    constructor
    · rintro ⟨e, he, rfl⟩
      exact he
    · intro ha
      obtain ⟨e, he⟩ := hAΛ a ha
      exact ⟨e, by show Λ e ∈ A; rw [he]; exact ha, he⟩
  have hAE : Nat.card E = Nat.card A := by
    rw [← hmapA]
    exact Nat.card_congr (Subgroup.equivMapOfInjective E Λ hΛinj).toEquiv
  have hnp : ∀ z ∈ proj.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    refine eq_one_of_mem_unitaryScalars_of_not_dvd h (by norm_num) hp hpq' ?_ hzp
    rw [unitaryScalars_eq h (by norm_num : 1 ≤ 3)]
    change z ∈ (LargeEvenProjMk (unitarySU 2 n K 3)).ker at hz
    rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hz
    exact hz
  obtain ⟨A', hA'map, -, hA'ab, hA'card⟩ :=
    TableBUE.exists_lift_of_noTorsion proj hproj hp hnp hE
  have hcardA : Nat.card A' = Nat.card A := by rw [hA'card, hAE]
  set ρ := unitaryRep (ℓ := 2) (f := n) (n := 3) (K := K) A' with hρdef
  let S : A' → Module.End K (Fin 3 → K) := fun x =>
    ((ρ x : LinearMap.GeneralLinearGroup K (Fin 3 → K)) : Module.End K (Fin 3 → K))
  have hScomm : ∀ x y, Commute (S x) (S y) := by
    intro x y
    have hxy : x * y = y * x := Subtype.ext (CFSG.Open.IsElemAbelian.comm hA'ab x.2 y.2)
    show S x * S y = S y * S x
    simp only [S, ← Units.val_mul, ← map_mul, hxy]
  have hSpow : ∀ x, S x ^ p = 1 := by
    intro x
    have hx : x ^ p = 1 := Subtype.ext (hA'ab.2 x x.2)
    show ((ρ x : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
      Module.End K (Fin 3 → K)) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  have hSiso : ∀ x v w, stdB h 3 (S x v) (S x w) = stdB h 3 v w :=
    fun x v w => mem_sesqUnitaryGroup.mp (unitaryRep_mem h A' x) v w
  obtain ⟨w, hw, hev⟩ := exists_adapted_hypFamily h hp hp2 hpq (by norm_num : 1 ≤ 1) (ε := 1) 1
    (V := Fin 3 → K) (B := stdB h 3)
    (gramForm_isSymm h (by simp)) (gramForm_separatingLeft h (by simp)) (by simp)
    S hScomm hSpow hSiso
  let R : Matrix (Fin 3) (HypIndex 1 1) K := Matrix.of fun k x => w x k
  have hwR : ∀ a, R *ᵥ (Pi.single a (1 : K)) = w a := by
    intro a
    funext k
    simp [R]
  have hR : IsHypTransport (r := 1) (ε := 1) h R := by
    change (R.map h.bar)ᵀ * R = hypGram 1 1 K
    ext x y
    rw [Matrix.mul_apply, ← hw x y, stdB, gramForm_apply]
    simp [R, dotProduct, Matrix.mul_apply]
  let T : hypSU h 1 1 ≃* ↥(unitarySU 2 n K 3) := by
    have h' : hypSU h 1 1 ≃* ↥(unitarySU 2 n K (2 * 1 + 1)) := hypTransport h hR
    exact h'
  have hevY : ∀ y : A', ∀ a, ∃ c : K,
      ((((y : ↥(unitarySU 2 n K 3)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) *ᵥ w a = c • w a := by
    intro y a
    obtain ⟨c, hc⟩ := hev y a
    refine ⟨c, ?_⟩
    have hc' := unitaryRep_apply A' y (w a)
    rw [hc'] at hc
    simpa using hc
  have hdiagY : ∀ y : A', ∃ c : HypIndex 1 1 → K,
      ((((T.symm (y : ↥(unitarySU 2 n K 3)) : hypSU h 1 1) : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal c) ∧
      (∀ a, c a ^ p = 1) ∧ c (.inr (.inl 0)) = 1 ∧
      c (.inr (.inr 0)) = (c (.inl 0))⁻¹ := by
    intro y
    obtain ⟨c, hd, hrel, hcp⟩ := diag_data hR hwR (y : ↥(unitarySU 2 n K 3))
      (hevY y) (hA'ab.2 y y.2)
    refine ⟨c, hd, hcp, ?_, ?_⟩
    · have hz := hrel (.inr (.inl 0))
      rw [hypPartner_inr_inl] at hz
      have hbar : h.bar (c (.inr (.inl 0))) = c (.inr (.inl 0)) :=
        bar_eq_self_of_pow_eq_one h hpq (hcp _)
      rw [hbar] at hz
      exact eq_one_of_sq_eq_one_of_pow_eq_one hp2 hp (hcp _)
        (by rw [pow_two]; exact hz)
    · have he := hrel (.inl 0)
      rw [hypPartner_inl] at he
      have hbar : h.bar (c (.inl 0)) = c (.inl 0) :=
        bar_eq_self_of_pow_eq_one h hpq (hcp _)
      rw [hbar] at he
      exact eq_inv_of_mul_eq_one_right he
  let χ : A' → K := fun y =>
    ((((T.symm (y : ↥(unitarySU 2 n K 3)) : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K)) (.inl 0) (.inl 0)
  have hχpow : ∀ y, χ y ^ p = 1 := by
    intro y
    obtain ⟨c, hd, hcp, -, -⟩ := hdiagY y
    have h1 : χ y = c (.inl 0) := by
      simp [χ, hd, Matrix.diagonal_apply_eq]
    rw [h1]
    exact hcp (.inl 0)
  have hχinj : Function.Injective χ := by
    intro y y' hyy'
    obtain ⟨c, hd, hcp, hcz, hcf⟩ := hdiagY y
    obtain ⟨c', hd', hcp', hcz', hcf'⟩ := hdiagY y'
    have hχ : c (.inl 0) = c' (.inl 0) := by
      simpa [χ, hd, hd', Matrix.diagonal_apply_eq] using hyy'
    have hc : c = c' := by
      funext a
      rcases a with i | j | i
      · have hi : i = 0 := Subsingleton.elim i 0
        rw [hi]
        exact hχ
      · have hj : j = 0 := Subsingleton.elim j 0
        rw [hj, hcz, hcz']
      · have hi : i = 0 := Subsingleton.elim i 0
        rw [hi, hcf, hcf', hχ]
    have hT : (T.symm (y : ↥(unitarySU 2 n K 3)) : hypSU h 1 1) =
        (T.symm (y' : ↥(unitarySU 2 n K 3)) : hypSU h 1 1) := by
      apply Subtype.ext
      apply Units.ext
      rw [hd, hd', hc]
    exact Subtype.ext (T.symm.injective hT)
  let χu : A' → rootsOfUnity p K := fun y =>
    ⟨Units.mk0 (χ y) (fun h0 => by
        have h := hχpow y
        rw [h0, zero_pow hp.ne_zero] at h
        exact zero_ne_one h),
      (mem_rootsOfUnity p _).mpr (Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact hχpow y))⟩
  have hχuinj : Function.Injective χu := by
    intro y y' h
    apply hχinj
    have := congrArg (fun u : rootsOfUnity p K => ((u : Kˣ) : K)) h
    simpa [χu] using this
  have hle : Nat.card A' ≤ Nat.card (rootsOfUnity p K) :=
    Nat.card_le_card_of_injective χu hχuinj
  calc Nat.card A = Nat.card A' := hcardA.symm
    _ ≤ Nat.card (rootsOfUnity p K) := hle
    _ ≤ p := card_rootsOfUnity K p

end CFSG.StandardType.SuSplitRootGen

end
