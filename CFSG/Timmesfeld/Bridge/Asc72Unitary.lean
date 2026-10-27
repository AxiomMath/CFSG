module

public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.Open
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.BenderSuzuki.External Matrix

theorem exists_unit_pow_succ_eq_one {K : Type*} [Field K] [Finite K] {q : ℕ} (hq : 4 ≤ q)
    (hcard : Nat.card K = q ^ 2) : ∃ c : Kˣ, c ^ (q + 1) = 1 ∧ c ^ 3 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  have hord : orderOf g = (q - 1) * (q + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard, hsq]
  refine ⟨g ^ (q - 1), ?_, fun h => ?_⟩
  · rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  · rw [← pow_mul] at h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have h3 : q + 1 ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
    have := Nat.le_of_dvd (by norm_num) h3
    omega

section Model

variable {K : Type*} [Field K] (J : HermitianForm 3 K)

theorem torusGL_commute_root {c : Kˣ} (hc : (c : K) * J.conj c = 1) {M : GL (Fin 3) K} {b : K}
    (hM : (M : Matrix (Fin 3) (Fin 3) K) = !![1, 0, b; 0, 1, 0; 0, 0, 1]) :
    Commute (torusGL J c) M := by
  have hinv : (J.conj (c : K))⁻¹ = c := by
    rw [eq_inv_of_mul_eq_one_right hc, inv_inv]
  change torusGL J c * M = M * torusGL J c
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, torusGL_val, hM, torusMatrix, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
include hJ

theorem commute_torusPSU_of_root {c : Kˣ} (hc : (c : K) * J.conj c = 1)
    {g : ProjectiveSpecialUnitaryMatrixGroup J} {M : GL (Fin 3) K} {b : K}
    (hM : (M : Matrix (Fin 3) (Fin 3) K) = !![1, 0, b; 0, 1, 0; 0, 0, 1])
    (hg : (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M) :
    Commute g (torusPSU J hJ c) := by
  change g * torusPSU J hJ c = torusPSU J hJ c * g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, torusPSU_val, hg, ← map_mul, ← map_mul,
    (torusGL_commute_root J hc hM).eq]

theorem torusPSU_ne_one {c : Kˣ} (hc : (c : K) * J.conj c = 1) (h3 : c ^ 3 ≠ 1) :
    torusPSU J hJ c ≠ 1 := by
  intro h
  have h' : ProjGenLinGroup.mk (torusGL J c) = 1 := by
    rw [← torusPSU_val J hJ c, h]
    rfl
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h'
  obtain ⟨d, hd⟩ := h'
  rw [torusGL_val, torusMatrix] at hd
  have h00 := congrFun (congrFun hd 0) 0
  have h11 := congrFun (congrFun hd 1) 1
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    at h00 h11
  have key : (c : K) * c = J.conj c := by
    rw [← (eq_div_iff c.ne_zero).mp (h00.symm.trans h11)]
  apply h3
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three, key, hc]

end Model

theorem mem_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {g y : G} :
    y ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * y * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem orderOf_mul_mul_inv {G : Type*} [Group G] (a b : G) :
    orderOf (a * b * a⁻¹) = orderOf b := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem exists_ne_one_commute_of_unitary {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    {t : ProjectiveSpecialUnitaryMatrixGroup J} (ht : orderOf t = 2) :
    ∃ c : ProjectiveSpecialUnitaryMatrixGroup J, c ≠ 1 ∧ Commute t c ∧
      ∀ z ∈ Subgroup.center (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
        Commute (z : ProjectiveSpecialUnitaryMatrixGroup J) c := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hfBB := bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ
  obtain ⟨hconj, -, -, -, -, rho, -, -, -, htwo, hstabα, -, hUnormal, -, hUT, -, -, -, ⟨S, hS⟩,
    -, -, -, -, hinvB, -, ⟨w, -, hwα, hwβ⟩, hswap⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide) with hα
  set β := unitaryOuterIsotropicPoint J hJ 2 (by decide) with hβ
  set U := (hermitianUnipotentPSU J hJ).range with hU
  set B := unitaryCoordinateStabilizer J 0 with hB
  have hmemB : ∀ g : G, g ∈ B ↔ rho g α = α := fun g => by
    rw [← hstabα]
    rfl
  have hUB : ∀ u ∈ U, u ∈ B := fun u hu => hUT ▸ Subgroup.mem_sup_left hu
  have hαβ : α ≠ β := fun h => unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h).symm
  obtain ⟨c, hcq, hc3⟩ := exists_unit_pow_succ_eq_one (K := K) (q := 2 ^ f)
    (by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf) hcard
  have hcK : (c : K) * J.conj c = 1 := by
    rw [hconj, ← pow_succ', ← Units.val_pow_eq_pow_val, hcq, Units.val_one]
  set τ : G := torusPSU J hJ c with hτ
  have hτ1 : τ ≠ 1 := torusPSU_ne_one J hJ hcK hc3
  have hτα : ∀ g : G, rho g α = α → orderOf g = 2 → Commute g τ := by
    intro g hg hg2
    obtain ⟨b, M, -, -, hM, hgM⟩ := (hinvB g).mp ⟨(hmemB g).mpr hg, hg2⟩
    exact commute_torusPSU_of_root J hJ hcK hM hgM
  have hτw : Commute w τ := by
    have h := (hswap w hwα hwβ).1 c
    have hcinv : (c ^ (2 ^ f))⁻¹ = c := by
      rw [inv_eq_iff_eq_inv]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hcq])
    rw [hcinv] at h
    change w * τ = τ * w
    calc w * τ = w * (w⁻¹ * τ * w) := by rw [h]
      _ = τ * w := by group
  have hτβ : ∀ g : G, rho g β = β → orderOf g = 2 → Commute g τ := by
    intro g hg hg2
    have hs : rho (w⁻¹ * g * w) α = α := by
      rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hwα, hg,
        Equiv.Perm.inv_eq_iff_eq, hwα]
    have hs2 : orderOf (w⁻¹ * g * w) = 2 := by
      rw [← inv_inv w, inv_inv w⁻¹, orderOf_mul_mul_inv, hg2]
    have hcs := hτα _ hs hs2
    have hg' : g = w * (w⁻¹ * g * w) * w⁻¹ := by group
    rw [hg']
    exact (hτw.mul_left hcs).mul_left hτw.inv_left
  have hτZ : ∀ z ∈ U, (∀ u ∈ U, Commute u z) → Commute z τ := by
    intro z hz hcz
    have hsq : z ^ 2 = 1 := by
      have hzS : z ∈ (S : Subgroup G) := hS ▸ hz
      have := (hfBB S).2.2.1 ⟨z, hzS⟩ (Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (hcz g (hS ▸ g.2)).eq)
      exact congrArg Subtype.val this
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h1 | h2
    · rw [orderOf_eq_one_iff] at h1
      rw [h1]
      exact Commute.one_left τ
    · exact hτα z ((hmemB z).mp (hUB z hz)) h2
  have hconjU : ∀ h : G, rho h α = α → ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    have := hUnormal.conj_mem ⟨u, hUB u hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨h, (hmemB h).mpr hh⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hconjZ : ∀ h : G, rho h α = α → ∀ z ∈ U, (∀ u ∈ U, Commute u z) →
      h * z * h⁻¹ ∈ U ∧ ∀ u ∈ U, Commute u (h * z * h⁻¹) := by
    intro h hh z hz hcz
    refine ⟨hconjU h hh z hz, fun u hu => ?_⟩
    have hh' : rho h⁻¹ α = α := by
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hh]
    have h1 := (hcz _ (hconjU h⁻¹ hh' u hu)).conj h
    have e : h * (h⁻¹ * u * h⁻¹⁻¹) * h⁻¹ = u := by group
    rwa [e] at h1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  set t' := g * t * g⁻¹ with ht'
  have ht'2 : orderOf t' = 2 := by rw [ht', orderOf_mul_mul_inv, ht]
  obtain ⟨S', hS'⟩ := IsPGroup.exists_le_sylow (p := 2) (P := Subgroup.zpowers t')
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one]))
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S S'
  have hxt : x⁻¹ * t' * x ∈ (S : Subgroup G) := by
    have h := hS' (Subgroup.mem_zpowers t')
    rw [← hx] at h
    exact mem_smul_sylow_iff.mp h
  have hfix : rho t' (rho x α) = rho x α := by
    have h1 := (hmemB _).mp (hUB _ (hS ▸ hxt))
    rwa [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_eq_iff_eq] at h1
  obtain ⟨h, hhα, hcomm⟩ : ∃ h : G, rho h α = α ∧ Commute (h * t' * h⁻¹) τ := by
    by_cases hp : rho x α = α
    · refine ⟨1, by rw [map_one, Equiv.Perm.one_apply], ?_⟩
      rw [one_mul, inv_one, mul_one]
      exact hτα t' (hp ▸ hfix) ht'2
    · obtain ⟨h, hh1, hh2⟩ := htwo α (rho x α) α β (Ne.symm hp) hαβ
      refine ⟨h, hh1, hτβ _ ?_ (by rw [orderOf_mul_mul_inv, ht'2])⟩
      rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hh2,
        Equiv.Perm.inv_eq_iff_eq.mpr rfl, hfix]
  set φ := MulAut.conj (h * g) with hφ
  refine ⟨φ.symm τ, (MulEquiv.map_ne_one_iff φ.symm).mpr hτ1, ?_, fun z hz => ?_⟩
  · have e : φ t = h * t' * h⁻¹ := by
      rw [hφ, MulAut.conj_apply, ht']
      group
    have := (e ▸ hcomm).map φ.symm
    rwa [MulEquiv.symm_apply_apply] at this
  · have hzS : g * (z : G) * g⁻¹ ∈ U := by
      rw [← hS, ← hg, mem_smul_sylow_iff]
      simp [mul_assoc]
    have hzc : ∀ u ∈ U, Commute u (g * (z : G) * g⁻¹) := by
      intro u hu
      rw [← hS, ← hg, mem_smul_sylow_iff] at hu
      have h2 : Commute (g⁻¹ * u * g) (z : G) :=
        Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hz ⟨_, hu⟩)
      have h3 := h2.conj g
      have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
      rwa [e] at h3
    obtain ⟨-, hcZ⟩ := hconjZ h hhα _ hzS hzc
    have e : φ z = h * (g * (z : G) * g⁻¹) * h⁻¹ := by
      rw [hφ, MulAut.conj_apply]
      group
    have := (e ▸ hτZ _ (hconjU h hhα _ hzS) hcZ).map φ.symm
    rwa [MulEquiv.symm_apply_apply] at this

theorem exists_ne_one_commute_of_psu3 {X : Type*} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* PSU3Model n) (Q : Sylow 2 X) {t : X} (ht : orderOf t = 2) :
    ∃ c : X, c ≠ 1 ∧ Commute t c ∧
      ∀ z ∈ Subgroup.center (Q : Subgroup X), Commute (z : X) c := by
  let J := binaryQuadraticHermitian n (by omega)
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 // J.conj x = x} =
      2 ^ n := quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e'⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hEcard hfixed
  let φ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e'.symm
  have : Finite X := Finite.of_injective φ φ.injective
  let Q' : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Q.mapSurjective (f := φ.toMonoidHom) φ.surjective
  obtain ⟨c, hc1, htc, hzc⟩ := exists_ne_one_commute_of_unitary J n hn hEcard hfixed hJ Q'
    (t := φ t) (by rw [MulEquiv.orderOf_eq]; exact ht)
  refine ⟨φ.symm c, (MulEquiv.map_ne_one_iff φ.symm).mpr hc1, ?_, fun z hz => ?_⟩
  · have := htc.map φ.symm
    rwa [MulEquiv.symm_apply_apply] at this
  · have hz' : (⟨φ z, Subgroup.mem_map_of_mem _ z.2⟩ : (Q' : Subgroup _)) ∈
        Subgroup.center (Q' : Subgroup _) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨y, hy⟩
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      apply Subtype.ext
      have h1 := Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hz ⟨y', hy'⟩)
      simp only [Subgroup.coe_mul] at h1 ⊢
      change φ y' * φ z = φ z * φ y'
      rw [← map_mul, ← map_mul, h1]
    have := (hzc _ hz').map φ.symm
    rwa [MulEquiv.symm_apply_apply] at this

theorem closure_insert_center_ne_top_of_psu3 {X : Type*} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* PSU3Model n) (Q : Sylow 2 X) {t : X} (ht : orderOf t = 2) :
    Subgroup.closure (insert t ((Subgroup.center (Q : Subgroup X)).map
      (Q : Subgroup X).subtype : Set X)) ≠ ⊤ := by
  have : Finite (PSU3Model n) := by
    have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
      Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
    exact Subtype.finite
  have : Finite X := Finite.of_injective e e.injective
  have hB : IsBenderGroup X := IsBenderGroup.isPSU3 n hn e
  obtain ⟨c, hc1, htc, hzc⟩ := exists_ne_one_commute_of_psu3 hn e Q ht
  intro htop
  have hle : Subgroup.closure (insert t ((Subgroup.center (Q : Subgroup X)).map
      (Q : Subgroup X).subtype : Set X)) ≤ Subgroup.centralizer {c} := by
    rw [Subgroup.closure_le]
    rintro x (rfl | ⟨z, hz, rfl⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr htc.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc z hz).eq
  rw [htop] at hle
  have hcZ : c ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))
  have := IsBenderGroup.isSimpleGroup hB
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
  · rw [h, Subgroup.mem_bot] at hcZ
    exact hc1 hcZ
  · obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
    have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

end CFSG.Timmesfeld.Bridge.Asc72
