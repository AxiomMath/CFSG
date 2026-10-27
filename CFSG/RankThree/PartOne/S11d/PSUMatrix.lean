module

public import CFSG.RankThree.PartOne.S11d.PSUFix
public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.OddIso

section Bridge

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

abbrev linOf (g : GL (Fin n) K) : Module.End K (Fin n → K) :=
  Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)

theorem linOf_apply (g : GL (Fin n) K) (v : Fin n → K) :
    linOf g v = (g : Matrix (Fin n) (Fin n) K) *ᵥ v := Matrix.toLin'_apply _ _

theorem linOf_mul (g g' : GL (Fin n) K) : linOf (g * g') = linOf g * linOf g' := by
  simp only [linOf, Units.val_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

theorem linOf_one : linOf (1 : GL (Fin n) K) = 1 := by
  simp [linOf, Matrix.toLin'_one, Module.End.one_eq_id]

theorem linOf_pow (g : GL (Fin n) K) (k : ℕ) : linOf (g ^ k) = linOf g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, linOf_one]
  | succ k ih => rw [pow_succ, linOf_mul, ih, pow_succ]

theorem linOf_injective : Function.Injective (linOf : GL (Fin n) K → Module.End K (Fin n → K)) :=
  fun _ _ e => Units.ext (Matrix.toLin'.injective e)

theorem linOf_isom {g : GL (Fin n) K} (hg : g ∈ primeFormUnitary h (idGram K n))
    (v w : Fin n → K) : idForm h n (linOf g v) (linOf g w) = idForm h n v w :=
  mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff g).mpr hg) v w

theorem bar_det_mul_det {g : GL (Fin n) K} (hg : g ∈ primeFormUnitary h (idGram K n)) :
    h.bar (g : Matrix (Fin n) (Fin n) K).det * (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h1 := mem_primeFormUnitary.mp hg
  simp only [idGram, Units.val_one, Matrix.mul_one] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  have h3 : ((g : Matrix (Fin n) (Fin n) K).map h.bar).det =
      h.bar (g : Matrix (Fin n) (Fin n) K).det := by
    rw [RingHom.map_det]; rfl
  rw [h3] at h2
  exact h2

theorem det_eq_one_of_unitary {g : GL (Fin n) K} (hg : g ∈ primeFormUnitary h (idGram K n))
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ F + 1) (hgp : g ^ p = 1) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  set d := (g : Matrix (Fin n) (Fin n) K).det with hd
  have hdp : d ^ p = 1 := by
    have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K).det) hgp
    simpa [Units.val_pow_eq_pow_val, Matrix.det_pow] using this
  have hdq : d ^ (2 ^ F + 1) = 1 := by
    have := bar_det_mul_det h hg
    rw [← hd, UnitaryFieldData.bar_apply, ← pow_succ] at this
    exact this
  have hcop : Nat.Coprime p (2 ^ F + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have := pow_gcd_eq_one.mpr ⟨hdp, hdq⟩
  rwa [hcop, pow_one] at this

theorem exists_gramSU_of_isom (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ F + 1)
    {u : Module.End K (Fin n → K)} (hup : u ^ p = 1)
    (hiso : ∀ v w, idForm h n (u v) (u w) = idForm h n v w) :
    ∃ g ∈ gramSU h (idGram K n), linOf g = u := by
  let uU : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    ⟨u, u ^ (p - 1), by rw [← pow_succ', Nat.sub_add_cancel hp.pos, hup],
      by rw [← pow_succ, Nat.sub_add_cancel hp.pos, hup]⟩
  have hmem : uU ∈ sesqUnitaryGroup (idForm h n) := fun x y => hiso x y
  obtain ⟨g, hg⟩ := exists_toLinU hmem
  have hgu : linOf (g : GL (Fin n) K) = u :=
    congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (z : Module.End K (Fin n → K))) hg
  have hgp : (g : GL (Fin n) K) ^ p = 1 := by
    apply linOf_injective
    rw [linOf_pow, hgu, hup, linOf_one]
  refine ⟨(g : GL (Fin n) K), (mem_gramSU_iff_unitary h).mpr ⟨g.2, ?_⟩, hgu⟩
  exact det_eq_one_of_unitary h g.2 hp hpq hgp

end Bridge

section Torus

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

@[expose] noncomputable def diagGL : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => K)).symm.toMonoidHom

theorem coe_diagGL (a : Fin n → Kˣ) :
    (diagGL a : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun i => ((a i : Kˣ) : K)) := rfl

theorem diagGL_injective : Function.Injective (diagGL : (Fin n → Kˣ) → GL (Fin n) K) := by
  intro a b hab
  funext i
  apply Units.ext
  have := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
    hab) i) i
  simpa [coe_diagGL] using this

theorem diagGL_mem_unitary (a : Fin n → Kˣ) (hN : ∀ i, (a i : K) ^ (2 ^ F + 1) = 1) :
    diagGL a ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one, coe_diagGL]
  have : ((Matrix.diagonal fun i => ((a i : Kˣ) : K)).map h.bar)ᵀ =
      Matrix.diagonal fun i => h.bar ((a i : Kˣ) : K) := by
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  rw [this, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, UnitaryFieldData.bar_apply]
    rw [← pow_succ]
    exact hN i
  · simp [hij]

theorem det_diagGL (a : Fin n → Kˣ) :
    (diagGL a : Matrix (Fin n) (Fin n) K).det = ∏ i, ((a i : Kˣ) : K) := by
  rw [coe_diagGL, Matrix.det_diagonal]

theorem det_diagGL_mulSingle (i : Fin n) (x : Kˣ) :
    (diagGL (Pi.mulSingle i x) : Matrix (Fin n) (Fin n) K).det = x := by
  rw [det_diagGL, Fintype.prod_eq_single i]
  · simp
  · intro j hj
    simp [hj]

theorem not_dvd_of_rank [Finite K] (hn : 3 ≤ n) (hp : p.Prime)
    (hrank : CFSG.pRank p ↥(gramSU h (idGram K n)) ≤ 1) : ¬ p ∣ 2 ^ F + 1 := by
  intro hpq
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card Kˣ = (2 ^ F) ^ 2 - 1 := by rw [Nat.card_units, h.card_eq_sq]
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [hcard]
    have h1 : (2 ^ F) ^ 2 - 1 = (2 ^ F + 1) * (2 ^ F - 1) := by
      have : 1 ≤ 2 ^ F := Nat.one_le_two_pow
      zify [this, (by nlinarith : 1 ≤ (2 ^ F) ^ 2)]
      ring
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζq : ((ζ : Kˣ) : K) ^ (2 ^ F + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    have : ζ ^ (2 ^ F + 1) = 1 := by rw [hk, pow_mul, hζp, one_pow]
    simpa using congrArg (fun u : Kˣ => (u : K)) this
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := fun e => by simpa [i0, i1] using congrArg Fin.val e
  have h02 : i0 ≠ i2 := fun e => by simpa [i0, i2] using congrArg Fin.val e
  have h12 : i1 ≠ i2 := fun e => by simpa [i1, i2] using congrArg Fin.val e
  have hu : ∀ (i : Fin n) (x : Kˣ), (x : K) ^ (2 ^ F + 1) = 1 →
      diagGL (Pi.mulSingle i x) ∈ primeFormUnitary h (idGram K n) := by
    intro i x hx
    refine diagGL_mem_unitary h _ fun j => ?_
    by_cases hij : j = i
    · subst hij; simpa using hx
    · simp [hij]
  have hζ' : (((ζ⁻¹ : Kˣ)) : K) ^ (2 ^ F + 1) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hζq, inv_one]
  have hmem : ∀ (i j : Fin n), i ≠ j →
      diagGL (Pi.mulSingle i ζ) * diagGL (Pi.mulSingle j ζ⁻¹) ∈ gramSU h (idGram K n) := by
    intro i j hij
    refine (mem_gramSU_iff_unitary h).mpr ⟨mul_mem (hu i ζ hζq) (hu j ζ⁻¹ hζ'), ?_⟩
    rw [Units.val_mul, Matrix.det_mul, det_diagGL_mulSingle, det_diagGL_mulSingle,
      Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero ζ)]
  let D₁ : ↥(gramSU h (idGram K n)) := ⟨_, hmem i0 i1 h01⟩
  let D₂ : ↥(gramSU h (idGram K n)) := ⟨_, hmem i1 i2 h12⟩
  have hcomm : Commute D₁ D₂ := by
    apply Subtype.ext
    change diagGL (Pi.mulSingle i0 ζ) * diagGL (Pi.mulSingle i1 ζ⁻¹) *
        (diagGL (Pi.mulSingle i1 ζ) * diagGL (Pi.mulSingle i2 ζ⁻¹)) =
      diagGL (Pi.mulSingle i1 ζ) * diagGL (Pi.mulSingle i2 ζ⁻¹) *
        (diagGL (Pi.mulSingle i0 ζ) * diagGL (Pi.mulSingle i1 ζ⁻¹))
    simp only [← map_mul]
    congr 1
    exact mul_comm _ _
  have hpow : ∀ (i j : Fin n),
      (diagGL (Pi.mulSingle i ζ) * diagGL (Pi.mulSingle j ζ⁻¹)) ^ p = 1 := by
    intro i j
    rw [← map_mul, ← map_pow, ← map_one (diagGL (n := n) (K := K))]
    congr 1
    funext k
    by_cases hk : k = i <;> by_cases hk' : k = j <;>
      simp [Pi.mulSingle_apply, hk, hk', hζp, inv_pow]
  have h2 := two_le_pRank_of_two_elements (P := ↥(gramSU h (idGram K n))) hp (e₁ := D₁) (e₂ := D₂)
    hcomm (Subtype.ext (hpow i0 i1)) (Subtype.ext (hpow i1 i2)) (fun i j hij => by
      have h1 := congrArg (fun g : ↥(gramSU h (idGram K n)) => (g : GL (Fin n) K)) hij
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one] at h1
      change (diagGL (Pi.mulSingle i0 ζ) * diagGL (Pi.mulSingle i1 ζ⁻¹)) ^ i *
        (diagGL (Pi.mulSingle i1 ζ) * diagGL (Pi.mulSingle i2 ζ⁻¹)) ^ j = 1 at h1
      rw [← map_mul, ← map_mul, ← map_zpow, ← map_zpow, ← map_mul,
        ← map_one (diagGL (n := n) (K := K))] at h1
      have h3 := diagGL_injective h1
      have e0 := congrArg (Pi.evalMonoidHom (fun _ : Fin n => Kˣ) i0) h3
      have e2 := congrArg (Pi.evalMonoidHom (fun _ : Fin n => Kˣ) i2) h3
      simp only [map_mul, map_zpow, map_one, Pi.evalMonoidHom_apply] at e0 e2
      simp [h01, h02, Ne.symm h02, Ne.symm h12] at e0 e2
      refine ⟨?_, ?_⟩
      · have : (orderOf ζ : ℤ) ∣ i := orderOf_dvd_iff_zpow_eq_one.mpr e0
        rwa [hζ] at this
      · have : (orderOf ζ : ℤ) ∣ j := orderOf_dvd_iff_zpow_eq_one.mpr e2
        rwa [hζ] at this)
  omega

end Torus

section Cyclic

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

theorem dvd_of_natMod_aux {p : ℕ} (hp : 0 < p) (i : ℤ) (h : p ∣ (i % p).toNat) : (p : ℤ) ∣ i := by
  have hlt : (i % p).toNat < p := by
    have h1 : i % p < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
    have h2 : (0 : ℤ) ≤ i % p := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    omega
  have h0 : (i % p).toNat = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
  have h2 : (0 : ℤ) ≤ i % p := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  exact Int.dvd_of_emod_eq_zero (by omega)

theorem zpow_eq_pow_natMod_aux {G : Type*} [Group G] {g : G} {p : ℕ} (hp : 0 < p)
    (hg : g ^ p = 1) (i : ℤ) : g ^ i = g ^ (i % p).toNat := by
  have h1 : i = (p : ℤ) * (i / p) + i % p := (Int.mul_ediv_add_emod i p).symm
  have h2 : (0 : ℤ) ≤ i % p := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  conv_lhs => rw [h1]
  rw [_root_.zpow_add, _root_.zpow_mul, zpow_natCast, hg, _root_.one_zpow, one_mul,
    ← zpow_natCast, Int.toNat_of_nonneg h2]

theorem cyclic_of_rank [Finite K] (hp : p.Prime) (hodd : Odd p) (hpq : ¬ p ∣ 2 ^ F + 1)
    {A : GL (Fin n) K} (hA : A ∈ gramSU h (idGram K n)) (hAp : A ^ p = 1) (hA1 : A ≠ 1)
    (hrank : CFSG.pRank p ↥(gramSU h (idGram K n)) ≤ 1) :
    IsCyclicOn (linOf A) (LinearMap.range (linOf A - 1)) := by
  by_contra hnc
  have : CharP K 2 := h.charP
  have hB := idForm_isSymm h n
  have hBl := idForm_separatingLeft h n
  have hAU : A ∈ primeFormUnitary h (idGram K n) := ((mem_gramSU_iff_unitary h).mp hA).1
  have hAB := linOf_isom h hAU
  have hÂp : linOf A ^ p = 1 := by rw [← linOf_pow, hAp, linOf_one]
  have hW : LinearMap.range (linOf A - 1) ≠ ⊥ := by
    intro hbot
    apply hA1
    apply linOf_injective
    rw [linOf_one]
    refine LinearMap.ext fun v => ?_
    have h0 : (linOf A - 1) v = 0 := by
      have hv : (linOf A - 1) v ∈ LinearMap.range (linOf A - 1) := ⟨v, rfl⟩
      rw [hbot] at hv
      exact (Submodule.mem_bot K).mp hv
    exact sub_eq_zero.mp (by simpa using h0)
  obtain ⟨M, hMW, hM0, hMW', hMinv, hMn⟩ := exists_splitH h.exists_bar_ne
    (hermitian_of_isSymm hB) (fun v hv => hBl v hv) hAB hodd hÂp hW hnc
  obtain ⟨u, hiso, hcomm, hup, hindep⟩ := exists_independentH hp (hermitian_of_isSymm hB) hAB
    hodd hÂp hMW hM0 hMW' hMinv hMn
  obtain ⟨g, hg, hgu⟩ := exists_gramSU_of_isom h hp hpq hup hiso
  have hga : g * A = A * g := linOf_injective (by rw [linOf_mul, linOf_mul, hgu]; exact hcomm)
  have hgp : g ^ p = 1 := linOf_injective (by rw [linOf_pow, hgu, hup, linOf_one])
  have hgp' : (⟨g, hg⟩ : ↥(gramSU h (idGram K n))) ^ p = 1 := Subtype.ext hgp
  have hAp' : (⟨A, hA⟩ : ↥(gramSU h (idGram K n))) ^ p = 1 := Subtype.ext hAp
  have h2 := two_le_pRank_of_two_elements (P := ↥(gramSU h (idGram K n))) hp
    (e₁ := ⟨g, hg⟩) (e₂ := ⟨A, hA⟩) (Subtype.ext hga) hgp' hAp' (fun i j hij => by
      rw [zpow_eq_pow_natMod_aux hp.pos hgp' i, zpow_eq_pow_natMod_aux hp.pos hAp' j] at hij
      have h3 : u ^ (i % p).toNat * (linOf A) ^ (j % p).toNat = 1 := by
        have := congrArg (fun x : ↥(gramSU h (idGram K n)) => linOf (x : GL (Fin n) K)) hij
        simpa [linOf_mul, linOf_pow, hgu, linOf_one] using this
      obtain ⟨h4, h5⟩ := hindep _ _ h3
      exact ⟨dvd_of_natMod_aux hp.pos i h4, dvd_of_natMod_aux hp.pos j h5⟩)
  omega

include h in
theorem two_le_finrank_fix [Finite K] (hodd : Odd p) {A Y : GL (Fin n) K} (hAp : A ^ p = 1)
    (hcyc : IsCyclicOn (linOf A) (LinearMap.range (linOf A - 1))) (hYc : Y * A = A * Y)
    (hY2 : Y ^ 2 = 1) (hY1 : Y ≠ 1) : 2 ≤ Module.finrank K (LinearMap.ker (linOf A - 1)) := by
  by_contra hlt
  push Not at hlt
  have : CharP K 2 := h.charP
  have hÂp : linOf A ^ p = 1 := by rw [← linOf_pow, hAp, linOf_one]
  have hcommY : linOf Y * linOf A = linOf A * linOf Y := by
    rw [← linOf_mul, ← linOf_mul, hYc]
  have hY2' : linOf Y ^ (2 ^ 1) = 1 := by rw [pow_one, ← linOf_pow, hY2, linOf_one]
  have hW := eq_id_on_range_of_two_pow hodd hÂp hcyc hcommY hY2'
  have hV : ∀ v ∈ LinearMap.ker (linOf A - 1), linOf Y v ∈ LinearMap.ker (linOf A - 1) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have := congrArg (fun f : Module.End K (Fin n → K) => f v) hcommY
    simp only [Module.End.mul_apply] at this
    have hv' : linOf A v = v := sub_eq_zero.mp hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← this, hv']
  have hV1 : ∀ v ∈ LinearMap.ker (linOf A - 1), linOf Y v = v := by
    obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp (Nat.lt_succ_iff.mp hlt)
    obtain ⟨c₀, hc₀⟩ := hv₀ ⟨linOf Y (v₀ : Fin n → K), hV _ v₀.2⟩
    have hc₀' : linOf Y (v₀ : Fin n → K) = c₀ • (v₀ : Fin n → K) :=
      (congrArg Subtype.val hc₀).symm
    intro v hv
    obtain ⟨c, hc⟩ := hv₀ ⟨v, hv⟩
    have hc' : v = c • (v₀ : Fin n → K) := (congrArg Subtype.val hc).symm
    by_cases hv0 : (v₀ : Fin n → K) = 0
    · rw [hc', hv0, smul_zero, map_zero]
    · have h1 : linOf Y (linOf Y (v₀ : Fin n → K)) = (v₀ : Fin n → K) := by
        have := congrArg (fun f : Module.End K (Fin n → K) => f (v₀ : Fin n → K))
          (show linOf Y * linOf Y = 1 by rw [← linOf_mul, ← sq, hY2, linOf_one])
        simpa [Module.End.mul_apply] using this
      rw [hc₀', map_smul, hc₀'] at h1
      have h2 : (c₀ * c₀ - 1) • (v₀ : Fin n → K) = 0 := by
        rw [sub_smul, mul_smul, one_smul, h1, sub_self]
      have h3 : c₀ * c₀ - 1 = 0 := (smul_eq_zero.mp h2).resolve_right hv0
      have h4 : c₀ = 1 := by
        have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have : (c₀ - 1) ^ 2 = 0 := by linear_combination h3 - (c₀) * h2' + h2'
        exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
      rw [hc', map_smul, hc₀', h4, one_smul]
  apply hY1
  apply linOf_injective
  rw [linOf_one]
  refine LinearMap.ext fun v => ?_
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range hodd hÂp v
  rw [map_add, hV1 v₁ hv₁, hW w hw]
  rfl

end Cyclic

end CFSG.RankThree.PartOne
