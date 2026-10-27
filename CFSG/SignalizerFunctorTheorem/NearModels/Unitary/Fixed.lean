module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix

namespace CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

namespace Fixed

theorem galoisField_pow_card {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : n ≠ 0)
    (z : GaloisField p n) : z ^ p ^ n = z := by
  have := Fintype.ofFinite (GaloisField p n)
  have hcard := GaloisField.card p n hn
  rw [Nat.card_eq_fintype_card] at hcard
  rw [← hcard]
  exact FiniteField.pow_card z

theorem pow_four_pow_eq_self {M : Type*} [Monoid M] {w : M} (hw : w ^ 4 = w) (m : ℕ) :
    w ^ 4 ^ m = w := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, ih, hw]

theorem pow_two_pow_eq_sq_of_pow_four_eq {M : Type*} [CommMonoid M] {y : M} (hy : y ^ 4 = y)
    {p : ℕ} (hp : Odd p) : y ^ 2 ^ p = y ^ 2 := by
  obtain ⟨m, rfl⟩ := hp
  have h4 : (y ^ 2) ^ 4 = y ^ 2 := by
    rw [← pow_mul, show 2 * 4 = 4 * 2 by norm_num, pow_mul, hy]
  rw [show 2 ^ (2 * m + 1) = 2 * 4 ^ m by rw [pow_succ, pow_mul]; ring, pow_mul,
    pow_four_pow_eq_self h4]

theorem nonempty_ringHom_gf4 {p : ℕ} (hp : p ≠ 0) :
    Nonempty (GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p)) := by
  have hdvd : Module.finrank (ZMod 2) (GaloisField 2 (2 * 1)) ∣
      Module.finrank (ZMod 2) (GaloisField 2 (2 * p)) := by
    rw [GaloisField.finrank 2 (by norm_num), GaloisField.finrank 2 (by omega)]
    exact Nat.mul_dvd_mul_left 2 (one_dvd p)
  exact ⟨(FiniteField.nonempty_algHom_of_finrank_dvd hdvd).some.toRingHom⟩

variable {p : ℕ}

theorem pow_four_map (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p))
    (z : GaloisField 2 (2 * 1)) : ι z ^ 4 = ι z := by
  have h := galoisField_pow_card (p := 2) (n := 2 * 1) (by norm_num) z
  rw [← map_pow]
  norm_num at h
  rw [h]

theorem mem_range_of_pow_four_eq (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p))
    {y : GaloisField 2 (2 * p)} (hy : y ^ 4 = y) : y ∈ Set.range ι := by
  classical
  by_contra hyr
  have := Fintype.ofFinite (GaloisField 2 (2 * 1))
  have hcard : Fintype.card (GaloisField 2 (2 * 1)) = 4 := by
    have := GaloisField.card 2 (2 * 1) (by norm_num)
    rw [Nat.card_eq_fintype_card] at this
    simpa using this
  have hne : (Polynomial.X ^ 4 - Polynomial.X : Polynomial (GaloisField 2 (2 * p))) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero _ (by norm_num)
  have key := Polynomial.card_le_degree_of_subset_roots
    (p := (Polynomial.X ^ 4 - Polynomial.X : Polynomial (GaloisField 2 (2 * p))))
    (Z := insert y (Finset.univ.image ι)) (fun x hx => by
      rw [Finset.mem_val, Finset.mem_insert, Finset.mem_image] at hx
      rw [Polynomial.mem_roots hne]
      rcases hx with rfl | ⟨z, -, rfl⟩
      · simp [hy]
      · simp [pow_four_map ι z])
  rw [Finset.card_insert_of_notMem (by simpa using hyr),
    Finset.card_image_of_injective _ ι.injective, Finset.card_univ, hcard,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ (by norm_num)] at key
  omega

theorem frob4_comp (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p)) :
    (frob4 p).comp ι = ι :=
  RingHom.ext fun z => by rw [RingHom.comp_apply, frob4_apply, pow_four_map]

section PGL

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {R S : Type*} [CommRing R]
  [CommRing S]

theorem mem_range_scalar_of_map_mem {σ : R →+* S} (hσ : Function.Injective σ)
    {B : Matrix n n R} (hB : B.map σ ∈ Set.range (Matrix.scalar n)) :
    B ∈ Set.range (Matrix.scalar n) := by
  obtain ⟨c, hc⟩ := hB
  obtain ⟨i⟩ := ‹Nonempty n›
  have hcii : c = σ (B i i) := by
    simpa using congrFun (congrFun hc i) i
  refine ⟨B i i, Matrix.map_injective hσ ?_⟩
  show (Matrix.scalar n (B i i)).map σ = B.map σ
  rw [← hc, hcii]
  ext a b
  by_cases hab : a = b <;> simp [Matrix.scalar_apply, hab]

theorem projGenLinGroup_map_injective {σ : R →+* S} (hσ : Function.Injective σ) :
    Function.Injective (ProjGenLinGroup.map (n := n) σ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  induction g using ProjGenLinGroup.induction_on with | mk A =>
  rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact mem_range_scalar_of_map_mem hσ hg

end PGL

theorem eq_one_of_mul_scalar_eq_map (hp : p.Prime) (hp3 : p ≠ 3)
    (A : GL (Fin 3) (GaloisField 2 (2 * p)))
    (hdet : (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))).det = 1)
    (u : (GaloisField 2 (2 * p))ˣ)
    (hu : A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.map (frob4 p) A) :
    u = 1 := by
  have hent : ∀ i j, (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) i j * u =
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) i j ^ 4 := by
    intro i j
    have := (GeneralLinearGroup.ext_iff _ _).mp hu i j
    simpa [frob4_apply, Matrix.scalar_apply, Matrix.mul_diagonal, val_glMap] using this
  have hu3 : u ^ 3 = 1 := by
    have := congrArg GeneralLinearGroup.det hu
    rw [map_mul, GeneralLinearGroup.det_scalar, GeneralLinearGroup.map_det] at this
    have hd : GeneralLinearGroup.det A = 1 := Units.ext (by simpa using hdet)
    simpa [hd] using this
  obtain ⟨i, j, hij⟩ : ∃ i j, (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) i j ≠ 0 := by
    by_contra! h
    have hA0 : (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) = 0 := Matrix.ext h
    rw [hA0, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  set a := (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) i j
  have hv3 : (u : GaloisField 2 (2 * p)) ^ 3 = 1 := by
    simpa using congrArg Units.val hu3
  have hv4 : (u : GaloisField 2 (2 * p)) ^ 4 = u := by
    rw [show 4 = 3 + 1 by norm_num, pow_succ, hv3, one_mul]
  have h4 : a ^ 4 = a * u := (hent i j).symm
  have hpow : ∀ k : ℕ, a ^ 4 ^ k = a * (u : GaloisField 2 (2 * p)) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a ^ 4 ^ (k + 1) = (a ^ 4 ^ k) ^ 4 := by rw [pow_succ, pow_mul]
        _ = (a * (u : GaloisField 2 (2 * p)) ^ k) ^ 4 := by rw [ih]
        _ = a ^ 4 * ((u : GaloisField 2 (2 * p)) ^ 4) ^ k := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k 4]
        _ = a * (u : GaloisField 2 (2 * p)) ^ (k + 1) := by rw [h4, hv4]; ring
  have hfull : a ^ 4 ^ p = a := by
    have := galoisField_pow_card (p := 2) (n := 2 * p) (by have := hp.pos; omega) a
    rwa [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num] at this
  have hup : (u : GaloisField 2 (2 * p)) ^ p = 1 := by
    have h1 : a * (u : GaloisField 2 (2 * p)) ^ p = a * 1 := by rw [← hpow p, hfull, mul_one]
    exact mul_left_cancel₀ hij h1
  have hup' : u ^ p = 1 := Units.ext (by simpa using hup)
  exact (pow_eq_one_iff_of_coprime ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)).mp
    ⟨hup', hu3⟩

theorem map_bar_gf4 (hp : Odd p) (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p))
    (z : GaloisField 2 (2 * 1)) :
    ι ((unitaryFieldData_galoisField (le_refl 1)).bar z) =
      (unitaryFieldData_galoisField hp.pos).bar (ι z) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow,
    pow_two_pow_eq_sq_of_pow_four_eq (pow_four_map ι z) hp, pow_one]

theorem map_mem_psu3 (hp : Odd p) (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p))
    {x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * 1))} (hx : x ∈ PSU3 2 1) :
    ProjGenLinGroup.map ι x ∈ PSU3 2 p := by
  rw [psu3_eq_map_gramSU (le_refl 1), Subgroup.mem_map] at hx
  obtain ⟨A, hA, rfl⟩ := hx
  rw [psu3_eq_map_gramSU hp.pos, Subgroup.mem_map]
  refine ⟨GeneralLinearGroup.map ι A, ?_, ProjGenLinGroup.map_mk _ _ |>.symm⟩
  have := map_mem_gramSU ι (map_bar_gf4 hp ι) _ hA
  rwa [antidiagGram_map] at this

@[expose] noncomputable def psu3Map (hp : Odd p)
    (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p)) : PSU3 2 1 →* PSU3 2 p :=
  ((ProjGenLinGroup.map ι).comp (PSU3 2 1).subtype).codRestrict (PSU3 2 p)
    fun x => map_mem_psu3 hp ι x.2

theorem coe_psu3Map (hp : Odd p) (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p))
    (x : PSU3 2 1) : (psu3Map hp ι x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
      ProjGenLinGroup.map ι (x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * 1))) := rfl

theorem psu3Map_injective (hp : Odd p) (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p)) :
    Function.Injective (psu3Map hp ι) := fun _ _ hxy =>
  Subtype.ext (projGenLinGroup_map_injective ι.injective (congrArg Subtype.val hxy))

theorem exists_map_eq_of_map_frob4_eq (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (ι : GaloisField 2 (2 * 1) →+* GaloisField 2 (2 * p))
    {y : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))} (hy : y ∈ PSU3 2 p)
    (hfix : ProjGenLinGroup.map (frob4 p) y = y) :
    ∃ x ∈ PSU3 2 1, ProjGenLinGroup.map ι x = y := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  rw [psu3_eq_map_gramSU hodd.pos, Subgroup.mem_map] at hy
  obtain ⟨A, hA, rfl⟩ := hy
  rw [ProjGenLinGroup.map_mk] at hfix
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hfix.symm
  have hu1 := eq_one_of_mul_scalar_eq_map hp hp3 A hA.2 u hu
  subst hu1
  rw [map_one, mul_one] at hu
  have hrange : ∀ i j, (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * p))) i j ∈
      Set.range ι := fun i j => by
    apply mem_range_of_pow_four_eq ι
    have := (GeneralLinearGroup.ext_iff _ _).mp hu i j
    rw [GeneralLinearGroup.map_apply, frob4_apply] at this
    exact this.symm
  obtain ⟨A₁, hA₁, hA₁A⟩ := exists_map_eq_of_mem_gramSU ι (map_bar_gf4 hodd ι)
    (antidiagGram _) (by rwa [antidiagGram_map]) hrange
  refine ⟨ProjGenLinGroup.mk A₁, ?_, ?_⟩
  · rw [psu3_eq_map_gramSU (le_refl 1)]
    exact Subgroup.mem_map_of_mem _ hA₁
  · rw [ProjGenLinGroup.map_mk, hA₁A]

end Fixed

theorem nonempty_fixedSubgroup_mulEquiv_psu3_two_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (τ : MulAut (PSU3 2 p))
    (hτ : ∀ x : PSU3 2 p,
      ((τ x : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
        ProjGenLinGroup.map (frob4 p)
          (x : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p)))) :
    Nonempty (signalizerFixedSubgroup τ ≃* PSU3 2 1) := by
  obtain ⟨ι⟩ := Fixed.nonempty_ringHom_gf4 hp.ne_zero
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hmem : ∀ x : PSU3 2 1, Fixed.psu3Map hodd ι x ∈ signalizerFixedSubgroup τ := fun x => by
    show τ (Fixed.psu3Map hodd ι x) = Fixed.psu3Map hodd ι x
    refine Subtype.ext ?_
    rw [hτ, Fixed.coe_psu3Map, ← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp,
      Fixed.frob4_comp]
  let Ψ : PSU3 2 1 →* signalizerFixedSubgroup τ := (Fixed.psu3Map hodd ι).codRestrict _ hmem
  have hΨ : Function.Bijective Ψ := by
    refine ⟨fun x y hxy => Fixed.psu3Map_injective hodd ι (congrArg Subtype.val hxy),
      fun y => ?_⟩
    have hy : τ y.1 = y.1 := y.2
    obtain ⟨z, hz, hzy⟩ := Fixed.exists_map_eq_of_map_frob4_eq hp hp2 hp3 ι y.1.2
      (by rw [← hτ, hy])
    exact ⟨⟨z, hz⟩, Subtype.ext (Subtype.ext hzy)⟩
  exact ⟨(MulEquiv.ofBijective Ψ hΨ).symm⟩

end CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
