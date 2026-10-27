module

public import CFSG.RankThree.PartOne.S13K.Sp6Conj
public import CFSG.RankThree.PartOne.S12.Sec136Inputs

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.KFQ
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem phiv_pow {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool} {x : Fin 3 → (Qext K)ˣ}
    (hx : ∀ i, x i ^ p = 1) : ∀ j, phiv π ε x j ^ p = 1 := by
  intro j
  simp only [phiv, Pi.mul_apply, Pi.inv_apply, mul_pow, inv_pow, sact_pow hx j, hx j, inv_one,
    one_mul]

theorem exists_sgn (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {g : ↥(M10 K)}
    (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹)) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
      ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1),
        g * tor10 hpq x hx * g⁻¹ = tor10 hpq (sact π ε x) (sact_pow hx) := by
  have hg' : ∀ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) →
      ∃ y : Fin 3 → (Qext K)ˣ, g.1 * torusEquiv x * g.1⁻¹ = torusEquiv y := by
    intro x hx
    obtain ⟨y, -, hy⟩ := hg1 (tor10 hpq x hx) (tor10_isTor hpq x hx)
    exact ⟨y, hy⟩
  obtain ⟨π, ε, hπ⟩ := normalizer_torus_units hp hp2 hpq g.1 hg'
  refine ⟨π, ε, fun x hx => ?_⟩
  obtain ⟨y, -, hy⟩ := hg1 (tor10 hpq x hx) (tor10_isTor hpq x hx)
  have hyx : y = sact π ε x := by
    funext j
    have h := hπ x y hx hy (π.symm j)
    rwa [Equiv.apply_symm_apply] at h
  apply Subtype.ext
  change g.1 * torusEquiv x * g.1⁻¹ = torusEquiv (sact π ε x)
  rw [← hyx]
  exact hy

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} (C : Sp6Ctx p A c L E f K)

@[expose] noncomputable def eT (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) : E :=
  ⟨C.phi (tor10 C.hpq' x hx), (C.phi_mem_E_iff _).mpr (tor10_isTor C.hpq' x hx)⟩

theorem eT_injective {x y : Fin 3 → (Qext K)ˣ} {hx : ∀ i, x i ^ p = 1} {hy : ∀ i, y i ^ p = 1}
    (h : C.eT x hx = C.eT y hy) : x = y := by
  have h1 : (C.eT x hx : G) = (C.eT y hy : G) := congrArg Subtype.val h
  have h2 : tor10 C.hpq' x hx = tor10 C.hpq' y hy := C.phi_injective h1
  exact torusEquiv_injective (congrArg Subtype.val h2)

theorem eT_one : C.eT (1 : Fin 3 → (Qext K)ˣ) (fun _ => one_pow _) = 1 := by
  apply Subtype.ext
  change C.phi (tor10 C.hpq' 1 _) = 1
  have : tor10 C.hpq' (1 : Fin 3 → (Qext K)ˣ) (fun _ => one_pow _) = 1 :=
    Subtype.ext torusEquiv_one
  rw [this, map_one]

theorem eT_mul (x y : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) (hy : ∀ i, y i ^ p = 1) :
    C.eT x hx * C.eT y hy = C.eT (x * y) (pow_unit_of_pow hx hy) := by
  apply Subtype.ext
  change C.phi (tor10 C.hpq' x hx) * C.phi (tor10 C.hpq' y hy) = C.phi (tor10 C.hpq' (x * y) _)
  rw [← map_mul, tor10_mul]

theorem eT_inv (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) :
    (C.eT x hx)⁻¹ = C.eT x⁻¹ (fun i => by simp [inv_pow, hx i]) := by
  apply Subtype.ext
  change (C.phi (tor10 C.hpq' x hx))⁻¹ = C.phi (tor10 C.hpq' x⁻¹ _)
  rw [← map_inv, tor10_inv]

theorem eT_pow (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) (n : ℕ) :
    (C.eT x hx) ^ n = C.eT (x ^ n) (fun i => by
      simp only [Pi.pow_apply]
      rw [← pow_mul, mul_comm, pow_mul, hx i, one_pow]) := by
  apply Subtype.ext
  change (C.phi (tor10 C.hpq' x hx)) ^ n = C.phi (tor10 C.hpq' (x ^ n) _)
  rw [← map_pow, tor10_npow]

theorem tAut_apply_coe {g : ↥(M10 K)} (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g)) (e : E) (x : ↥(M10 K)) (i : ℤ)
    (he : (e : G) = C.phi x * c ^ i) :
    ((E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩ e : E) : G) =
      C.phi (g * x * g⁻¹) * c ^ i := by
  change C.phi g * (e : G) * (C.phi g)⁻¹ = _
  rw [he, C.conj_phi_mul_zpow]

theorem tAut_congr {g g' : ↥(M10 K)} (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g))
    (hg1' : ∀ x, IsTor p x → IsTor p (g' * x * g'⁻¹))
    (hg2' : ∀ x, IsTor p x → IsTor p (g'⁻¹ * x * g'))
    (h : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1),
      g * tor10 C.hpq' x hx * g⁻¹ = g' * tor10 C.hpq' x hx * g'⁻¹) :
    E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩ =
      E.normalizerMonoidHom ⟨C.phi g', C.mem_normalizer hg1' hg2'⟩ := by
  refine MulEquiv.ext fun e => Subtype.ext ?_
  obtain ⟨x, hx, i, hei⟩ := C.exists_decomp e.2
  rw [C.tAut_apply_coe hg1 hg2 e x i hei, C.tAut_apply_coe hg1' hg2' e x i hei]
  obtain ⟨a, ha, hxa⟩ := hx
  have hxe : x = tor10 C.hpq' a ha := Subtype.ext hxa
  rw [hxe, h a ha]

theorem tAut_eT {g : ↥(M10 K)} (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g)) {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool}
    (hπε : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1),
      g * tor10 C.hpq' x hx * g⁻¹ = tor10 C.hpq' (sact π ε x) (sact_pow hx))
    (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) :
    E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩ (C.eT x hx) =
      C.eT (sact π ε x) (sact_pow hx) := by
  apply Subtype.ext
  change C.phi g * C.phi (tor10 C.hpq' x hx) * (C.phi g)⁻¹ =
    C.phi (tor10 C.hpq' (sact π ε x) _)
  rw [← map_inv, ← map_mul, ← map_mul, hπε x hx]

theorem reflShape_of_isAutReflection (hp5 : 5 ≤ p) {g : ↥(M10 K)}
    (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g)) {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool}
    (hπε : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1),
      g * tor10 C.hpq' x hx * g⁻¹ = tor10 C.hpq' (sact π ε x) (sact_pow hx))
    (hrefl : IsAutReflection p E (E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩)) :
    ReflShape π ε := by
  set t := E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩ with ht
  have hp : p.Prime := C.h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot hp C.hp2 C.hpq'
  obtain ⟨hord, hcard⟩ := hrefl
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hord, sq] at this
  have hact : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1),
      t (C.eT x hx) = C.eT (sact π ε x) (sact_pow hx) := fun x hx => C.tAut_eT hg1 hg2 hπε x hx
  refine classify hζ hp5 ?_ ?_ ?_
  · intro x hx
    have h1 : t (t (C.eT x hx)) = C.eT x hx := by
      rw [← MulAut.mul_apply, htt, MulAut.one_apply]
    rw [hact, hact] at h1
    exact C.eT_injective h1
  · by_contra hall
    push Not at hall
    have h1 : t = 1 := by
      refine MulEquiv.ext fun e => Subtype.ext ?_
      obtain ⟨x, hx, i, hei⟩ := C.exists_decomp e.2
      rw [C.tAut_apply_coe hg1 hg2 e x i hei]
      obtain ⟨a, ha, hxa⟩ := hx
      have hxe : x = tor10 C.hpq' a ha := Subtype.ext hxa
      have hfix : g * tor10 C.hpq' a ha * g⁻¹ = tor10 C.hpq' a ha := by
        rw [hπε a ha]
        exact Subtype.ext (by simp only [tor10_coe]; rw [hall a ha])
      rw [hxe, hfix, ← hxe, ← hei]
      rfl
    rw [h1, orderOf_one] at hord
    omega
  · intro x x' hx hx' hphi
    have hmv : ∀ (y : Fin 3 → (Qext K)ˣ) (hy : ∀ i, y i ^ p = 1),
        t (C.eT y hy) * (C.eT y hy)⁻¹ = C.eT (phiv π ε y) (phiv_pow hy) := by
      intro y hy
      rw [hact, C.eT_inv, C.eT_mul]
      rfl
    let mv : (y : Fin 3 → (Qext K)ˣ) → (∀ i, y i ^ p = 1) → ↥(autMoved E t) := fun y hy =>
      ⟨C.eT (phiv π ε y) (phiv_pow hy), by
        rw [← hmv y hy]
        exact Subgroup.subset_closure ⟨C.eT y hy, rfl⟩⟩
    have hmvne : mv x hx ≠ 1 := by
      intro h
      apply hphi
      have h1 : C.eT (phiv π ε x) (phiv_pow hx) = 1 := congrArg Subtype.val h
      rw [← C.eT_one] at h1
      exact C.eT_injective h1
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_of_prime_card (g' := mv x' hx') hcard hmvne)
    refine ⟨n, ?_⟩
    have h1 : C.eT (phiv π ε x') (phiv_pow hx') = (C.eT (phiv π ε x) (phiv_pow hx)) ^ n :=
      (congrArg Subtype.val hn).symm
    rw [C.eT_pow] at h1
    exact C.eT_injective h1

theorem exists_shape {t : MulAut E} (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool), ReflShape π ε ∧ t = C.tSgn π ε := by
  obtain ⟨w, hwL, hwN, rfl⟩ := CFSG.RankThree.PartOne.Sec12Three.mem_torusImage_iff.mp htL
  obtain ⟨g, rfl⟩ := C.exists_phi_eq hwL
  have hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹) := by
    intro x hx
    rw [← C.phi_mem_E_iff]
    have h1 := (Subgroup.mem_normalizer_iff.mp hwN (C.phi x)).mp ((C.phi_mem_E_iff x).mpr hx)
    simpa [map_mul, map_inv] using h1
  have hg2 := C.hg2_of_hg1 hg1
  obtain ⟨π, ε, hπε⟩ := exists_sgn C.h.prime C.hp2 C.hpq' hg1
  have hshape : ReflShape π ε :=
    C.reflShape_of_isAutReflection (CFSG.RankThree.PartOne.Sec12Three.five_le C.h) hg1 hg2 hπε ht.1
  refine ⟨π, ε, hshape, ?_⟩
  refine C.tAut_congr hg1 hg2 (sg10_hg1 C.hpq' π ε) (C.hg2_of_hg1 (sg10_hg1 C.hpq' π ε)) ?_
  intro x hx
  rw [hπε x hx]
  exact (Subtype.ext (sgnPerm_conj C.hpq' π ε x (sact π ε x) hx (fun i => rfl))).symm

end Sp6Ctx

theorem kfAt_row10 (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E ≠ A) (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f) :
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFAt p E f t := by
  intro t ht htL
  obtain ⟨K, _, _, _, ⟨C⟩⟩ := exists_sp6ctx hGA h hF hEA hf hpq hmodel
  obtain ⟨π, ε, hshape, rfl⟩ := C.exists_shape ht htL
  exact C.kfAt_tSgn_of_shape hshape

theorem KF136At_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF136At := by
  unfold KF136At
  intro G _ _ p A c L E f h hF _ _ hEA hf hpq hmodel t ht htL
  exact kfAt_row10 hGA h hF hEA hf hpq hmodel t ht htL

end CFSG.RankThree.PartOne.S13K
