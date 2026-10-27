module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovX
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovQa
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {X : Type*} [Group X] [Finite X] {Z R T : Subgroup X} {s : X}

private theorem card_R0 (h : CoverX X Z R T s) {R₀ : Subgroup X} (hdisj : Disjoint R₀ Z)
    (hsup : Z ⊔ R₀ = R) : Nat.card R₀ = 9 := by
  haveI : Z.Normal := Subgroup.normal_of_le_center h.Z_central
  have hnorm : R₀ ≤ Subgroup.normalizer (Z : Set X) := Subgroup.le_normalizer_of_normal
  have hc := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z R₀ hnorm
    hdisj.symm
  rw [hsup, h.card_R, h.card_Z] at hc
  omega

private theorem card_P (h : CoverX X Z R T s) {R₀ : Subgroup X} (hR₀R : R₀ ≤ R)
    (hdisj : Disjoint R₀ Z) (hsup : Z ⊔ R₀ = R) {P : Type*} [Group P] (π : T →* P)
    (hπ : Function.Surjective π) (hker : ∀ t : T, π t = 1 ↔ (t : X) ∈ R₀) :
    Nat.card P = 81 := by
  have hKR : Subgroup.map T.subtype π.ker = R₀ := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
      exact (hker t).mp (MonoidHom.mem_ker.mp ht)
    · intro hx
      have hxT : x ∈ T := h.R_le_T (hR₀R hx)
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxT⟩, MonoidHom.mem_ker.mpr ((hker ⟨x, hxT⟩).mpr hx), rfl⟩
  have hK : Nat.card π.ker = 9 := by
    rw [← Subgroup.card_subtype T π.ker, hKR, card_R0 h hdisj hsup]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [h.card_T, hK] at hq
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  omega

private theorem conj_memT (h : CoverX X Z R T s) (t : T) : s * (t : X) * s⁻¹ ∈ T :=
  (Subgroup.mem_normalizer_iff.mp h.s_normT (t : X)).mp t.2

private theorem conj_pow_memT (h : CoverX X Z R T s) (k : ℕ) (t : T) :
    s ^ k * (t : X) * (s ^ k)⁻¹ ∈ T :=
  (Subgroup.mem_normalizer_iff.mp (pow_mem h.s_normT k) (t : X)).mp t.2

private theorem pow_conj_mem {R₀ : Subgroup X} (hsR₀ : ∀ x ∈ R₀, s * x * s⁻¹ ∈ R₀) (n : ℕ) :
    ∀ x ∈ R₀, s ^ n * x * (s ^ n)⁻¹ ∈ R₀ := by
  induction n with
  | zero =>
    intro x hx
    simpa using hx
  | succ n ih =>
    intro x hx
    have h1 := hsR₀ _ (ih x hx)
    rw [pow_succ']
    simpa only [mul_inv_rev, mul_assoc] using h1

private theorem mem_of_conj_mem {R₀ : Subgroup X} (h8 : s ^ 8 = 1)
    (hsR₀ : ∀ x ∈ R₀, s * x * s⁻¹ ∈ R₀) {x : X} (hx : s * x * s⁻¹ ∈ R₀) : x ∈ R₀ := by
  have key := pow_conj_mem hsR₀ 7 _ hx
  have h7 : s ^ 7 = s⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact h8
  have e : s ^ 7 * (s * x * s⁻¹) * (s ^ 7)⁻¹ = x := by
    rw [h7, inv_inv]
    group
  rwa [e] at key

private theorem exists_sigma (h : CoverX X Z R T s) {R₀ : Subgroup X}
    (hsR₀ : ∀ x ∈ R₀, s * x * s⁻¹ ∈ R₀) {P : Type*} [Group P] [Finite P] (π : T →* P)
    (hπ : Function.Surjective π) (hker : ∀ t : T, π t = 1 ↔ (t : X) ∈ R₀) :
    ∃ σ : MulAut P, ∀ t : T, ∀ ht : s * (t : X) * s⁻¹ ∈ T, σ (π t) = π ⟨s * t * s⁻¹, ht⟩ := by
  let c : T →* T :=
    { toFun := fun t => ⟨s * t * s⁻¹, conj_memT h t⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hle : π.ker ≤ (π.comp c).ker := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    show π (c t) = 1
    exact (hker (c t)).mpr (hsR₀ _ ((hker t).mp ht))
  let ψ : P →* P := π.liftOfSurjective hπ ⟨π.comp c, hle⟩
  have hψ : ∀ t : T, ψ (π t) = π (c t) := fun t =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨π.comp c, hle⟩ t
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    obtain ⟨t, rfl⟩ := hπ p
    rw [hψ t] at hp
    exact (hker t).mpr (mem_of_conj_mem h.s_pow hsR₀ (x := (t : X)) ((hker (c t)).mp hp))
  refine ⟨MulEquiv.ofBijective ψ (Finite.injective_iff_bijective.mp hinj), fun t ht => ?_⟩
  exact (hψ t).trans (congrArg π (Subtype.ext rfl))

private theorem sigma_pow_apply (h : CoverX X Z R T s) {P : Type*} [Group P] (π : T →* P)
    (σ : MulAut P) (hσ : ∀ t : T, ∀ ht : s * (t : X) * s⁻¹ ∈ T, σ (π t) = π ⟨s * t * s⁻¹, ht⟩)
    (k : ℕ) (t : T) :
    (σ ^ k) (π t) = π ⟨s ^ k * (t : X) * (s ^ k)⁻¹, conj_pow_memT h k t⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm : s * (s ^ k * (t : X) * (s ^ k)⁻¹) * s⁻¹ ∈ T :=
      conj_memT h ⟨s ^ k * (t : X) * (s ^ k)⁻¹, conj_pow_memT h k t⟩
    rw [pow_succ' σ k, MulAut.mul_apply, ih,
      hσ ⟨s ^ k * (t : X) * (s ^ k)⁻¹, conj_pow_memT h k t⟩ hm]
    congr 1
    apply Subtype.ext
    simp only [pow_succ', mul_inv_rev, mul_assoc]

private theorem sigma_pow_eight (h : CoverX X Z R T s) {P : Type*} [Group P] (π : T →* P)
    (hπ : Function.Surjective π) (σ : MulAut P)
    (hσ : ∀ t : T, ∀ ht : s * (t : X) * s⁻¹ ∈ T, σ (π t) = π ⟨s * t * s⁻¹, ht⟩) :
    σ ^ 8 = 1 := by
  ext p
  obtain ⟨t, rfl⟩ := hπ p
  rw [sigma_pow_apply h π σ hσ 8 t, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  simp [h.s_pow]

private theorem ker_inf_Z (h : CoverX X Z R T s) {R₀ : Subgroup X} (hdisj : Disjoint R₀ Z)
    {P : Type*} [Group P] (π : T →* P) (hker : ∀ t : T, π t = 1 ↔ (t : X) ∈ R₀) :
    ∀ t ∈ Z.subgroupOf T, π t = 1 → t = 1 := by
  intro t ht hπt
  have htR : (t : X) ∈ R₀ ⊓ Z := ⟨(hker t).mp hπt, Subgroup.mem_subgroupOf.mp ht⟩
  rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at htR
  exact Subtype.ext htR

private theorem card_Zh (h : CoverX X Z R T s) {P : Type*} [Group P] (π : T →* P)
    (hZ : ∀ t ∈ Z.subgroupOf T, π t = 1 → t = 1) :
    Nat.card ((Z.subgroupOf T).map π) = 3 := by
  have hinj : Function.Injective
      (fun u : Z.subgroupOf T => (⟨π u.1, Subgroup.mem_map_of_mem π u.2⟩ :
        (Z.subgroupOf T).map π)) := by
    intro a b hab
    have hab' : π a.1 = π b.1 := congrArg Subtype.val hab
    have h1 : π (a.1 * b.1⁻¹) = 1 := by rw [map_mul, map_inv, hab', mul_inv_cancel]
    have h2 := hZ _ ((Z.subgroupOf T).mul_mem a.2 ((Z.subgroupOf T).inv_mem b.2)) h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hsurj : Function.Surjective
      (fun u : Z.subgroupOf T => (⟨π u.1, Subgroup.mem_map_of_mem π u.2⟩ :
        (Z.subgroupOf T).map π)) := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨t, ht⟩, Subtype.ext rfl⟩
  have hZT : Z ≤ T := h.Z_le_R.trans h.R_le_T
  have e1 := Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  have e2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZT).toEquiv
  rw [← e1, e2, h.card_Z]

private theorem central_Zh (h : CoverX X Z R T s) {P : Type*} [Group P] (π : T →* P)
    (hπ : Function.Surjective π) : (Z.subgroupOf T).map π ≤ Subgroup.center P := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨u, rfl⟩ := hπ g
  have hzc : (t : X) ∈ Subgroup.center X := h.Z_central (Subgroup.mem_subgroupOf.mp ht)
  have hcomm : (u : X) * (t : X) = (t : X) * (u : X) := Subgroup.mem_center_iff.mp hzc (u : X)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm

private theorem sigma_Zh (h : CoverX X Z R T s) {P : Type*} [Group P] (π : T →* P)
    (σ : MulAut P)
    (hσ : ∀ t : T, ∀ ht : s * (t : X) * s⁻¹ ∈ T, σ (π t) = π ⟨s * t * s⁻¹, ht⟩) :
    ∀ y ∈ (Z.subgroupOf T).map π, σ y = y := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  have hzc : (t : X) ∈ Subgroup.center X := h.Z_central (Subgroup.mem_subgroupOf.mp ht)
  have hst : s * (t : X) = (t : X) * s := Subgroup.mem_center_iff.mp hzc s
  rw [hσ t (conj_memT h t)]
  congr 1
  apply Subtype.ext
  show s * (t : X) * s⁻¹ = (t : X)
  rw [hst, mul_inv_cancel_right]

private theorem nonab_P (h : CoverX X Z R T s) {R₀ : Subgroup X} (hR₀R : R₀ ≤ R)
    {P : Type*} [Group P] (π : T →* P) (hker : ∀ t : T, π t = 1 ↔ (t : X) ∈ R₀) :
    ∃ x y : P, x * y * x⁻¹ * y⁻¹ ∉ (Z.subgroupOf T).map π := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nonab
  obtain ⟨c, hcdef⟩ : ∃ c : T, c = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩)⁻¹ * (⟨y, hy⟩)⁻¹ :=
    ⟨_, rfl⟩
  have hPc : π c = π ⟨x, hx⟩ * π ⟨y, hy⟩ * (π ⟨x, hx⟩)⁻¹ * (π ⟨y, hy⟩)⁻¹ := by
    simp only [hcdef, map_mul, map_inv]
  have hXc : (c : X) = x * y * x⁻¹ * y⁻¹ := by
    simp [hcdef]
  refine ⟨π ⟨x, hx⟩, π ⟨y, hy⟩, fun hmem => hxy ?_⟩
  rw [← hPc] at hmem
  obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hmem
  have h1 : π (z⁻¹ * c) = 1 := by rw [map_mul, map_inv, hzeq, inv_mul_cancel]
  have h2 : ((z⁻¹ * c : T) : X) ∈ R₀ := (hker _).mp h1
  have hzR : (z : X) ∈ R := h.Z_le_R (Subgroup.mem_subgroupOf.mp hz)
  have hcR : (c : X) ∈ R := by
    have e : (c : X) = (z : X) * ((z⁻¹ * c : T) : X) := by simp
    rw [e]
    exact R.mul_mem hzR (hR₀R h2)
  rw [hXc] at hcR
  exact hcR

private theorem singer_P (h : CoverX X Z R T s) {P : Type*} [Group P] (π : T →* P)
    (hπ : Function.Surjective π) (σ : MulAut P)
    (hσ2 : ∀ t : T, (σ ^ 2) (π t) = π ⟨s ^ 2 * (t : X) * (s ^ 2)⁻¹, conj_pow_memT h 2 t⟩)
    (W : Subgroup P) (hZW : (Z.subgroupOf T).map π ≤ W) (hWi : W.index = 3)
    (heq : W.map (σ ^ 2).toMonoidHom = W) : False := by
  obtain ⟨W', hW'⟩ : ∃ W' : Subgroup X, W' = (W.comap π).map T.subtype := ⟨_, rfl⟩
  have hmem : ∀ t : T, (t : X) ∈ W' ↔ π t ∈ W := by
    intro t
    rw [hW']
    constructor
    · intro ht
      obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.mp ht
      have hut' : u = t := Subtype.ext hut
      rw [← hut']
      exact hu
    · intro ht
      exact Subgroup.mem_map_of_mem T.subtype (Subgroup.mem_comap.mpr ht)
  have hW'T : W' ≤ T := by
    intro x hx
    rw [hW'] at hx
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact u.2
  have hZW' : Z ≤ W' := by
    intro z hz
    have hzT : z ∈ T := h.R_le_T (h.Z_le_R hz)
    have hzZ : (⟨z, hzT⟩ : T) ∈ Z.subgroupOf T := Subgroup.mem_subgroupOf.mpr hz
    exact (hmem ⟨z, hzT⟩).mpr (hZW (Subgroup.mem_map_of_mem π hzZ))
  have hsub : W'.subgroupOf T = W.comap π := by
    ext t
    rw [Subgroup.mem_subgroupOf]
    exact hmem t
  have hrel : W'.relIndex T = 3 := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_comap_of_surjective W hπ, hWi]
  have hfix : ∀ x : P, (σ ^ 2) x ∈ W ↔ x ∈ W := by
    intro x
    constructor
    · intro hx
      have hx' : (σ ^ 2) x ∈ W.map (σ ^ 2).toMonoidHom := by
        rw [heq]
        exact hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      have hyx' : y = x := (σ ^ 2).injective hyx
      rw [← hyx']
      exact hy
    · intro hx
      have hx' : (σ ^ 2) x ∈ W.map (σ ^ 2).toMonoidHom := Subgroup.mem_map_of_mem _ hx
      rw [heq] at hx'
      exact hx'
  have hnormT : ∀ n : X, n ∈ T ↔ s ^ 2 * n * (s ^ 2)⁻¹ ∈ T := fun n =>
    Subgroup.mem_normalizer_iff.mp (pow_mem h.s_normT 2) n
  have hnorm : s ^ 2 ∈ Subgroup.normalizer (W' : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    by_cases hn : n ∈ T
    · have hn2 : s ^ 2 * n * (s ^ 2)⁻¹ ∈ T := (hnormT n).mp hn
      have e1 : n ∈ W' ↔ π ⟨n, hn⟩ ∈ W := hmem ⟨n, hn⟩
      have e2 : s ^ 2 * n * (s ^ 2)⁻¹ ∈ W' ↔ π ⟨s ^ 2 * n * (s ^ 2)⁻¹, hn2⟩ ∈ W :=
        hmem ⟨s ^ 2 * n * (s ^ 2)⁻¹, hn2⟩
      have e3 : (σ ^ 2) (π ⟨n, hn⟩) = π ⟨s ^ 2 * n * (s ^ 2)⁻¹, hn2⟩ := hσ2 ⟨n, hn⟩
      have e4 : (σ ^ 2) (π ⟨n, hn⟩) ∈ W ↔ s ^ 2 * n * (s ^ 2)⁻¹ ∈ W' := by
        rw [e3]
        exact e2.symm
      exact e1.trans ((hfix (π ⟨n, hn⟩)).symm.trans e4)
    · have hnW : n ∉ W' := fun hW => hn (hW'T hW)
      have hn2 : s ^ 2 * n * (s ^ 2)⁻¹ ∉ W' := fun hW => hn ((hnormT n).mpr (hW'T hW))
      exact ⟨fun hh => absurd hh hnW, fun hh => absurd hh hn2⟩
  exact h.singer W' hW'T hZW' hrel hnorm

theorem coverP_of_coverX (h : CoverX X Z R T s) {R₀ : Subgroup X} (hR₀R : R₀ ≤ R)
    (hdisj : Disjoint R₀ Z) (hsup : Z ⊔ R₀ = R) (hsR₀ : ∀ x ∈ R₀, s * x * s⁻¹ ∈ R₀)
    {P : Type*} [Group P] [Finite P] (π : T →* P) (hπ : Function.Surjective π)
    (hker : ∀ t : T, π t = 1 ↔ (t : X) ∈ R₀) :
    ∃ (σ : MulAut P) (Zh : Subgroup P), CoverP P σ Zh ∧
      (∀ t : T, ∀ ht : s * (t : X) * s⁻¹ ∈ T, σ (π t) = π ⟨s * t * s⁻¹, ht⟩) ∧
      (∀ z : Z, π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩ ∈ Zh) ∧
      (∀ z z' : Z, π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩ = π ⟨z', h.R_le_T (h.Z_le_R z'.2)⟩ → z = z') ∧
      (∀ y ∈ Zh, ∃ z : Z, π ⟨z, h.R_le_T (h.Z_le_R z.2)⟩ = y) := by
  obtain ⟨σ, hσ⟩ := exists_sigma h hsR₀ π hπ hker
  have hσ2 := sigma_pow_apply h π σ hσ 2
  have hZ := ker_inf_Z h hdisj π hker
  have hPc : Nat.card P = 81 := card_P h hR₀R hdisj hsup π hπ hker
  have hpg : IsPGroup 3 P := IsPGroup.of_card (n := 4) (hPc.trans (by norm_num))
  refine ⟨σ, (Z.subgroupOf T).map π, ⟨central_Zh h π hπ, card_Zh h π hZ, hPc, hpg,
    nonab_P h hR₀R π hker, sigma_pow_eight h π hπ σ hσ, sigma_Zh h π σ hσ,
    fun W hZW hWi heq => singer_P h π hπ σ hσ2 W hZW hWi heq⟩, hσ, ?_, ?_, ?_⟩
  · intro z
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr z.2)
  · intro z z' hzz
    have ha : (⟨(z : X), h.R_le_T (h.Z_le_R z.2)⟩ : T) ∈ Z.subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr z.2
    have hb : (⟨(z' : X), h.R_le_T (h.Z_le_R z'.2)⟩ : T) ∈ Z.subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr z'.2
    have hab := hZ _ ((Z.subgroupOf T).mul_mem ha ((Z.subgroupOf T).inv_mem hb))
      (by rw [map_mul, map_inv, hzz, mul_inv_cancel])
    have hab2 : (⟨(z : X), h.R_le_T (h.Z_le_R z.2)⟩ : T) =
        ⟨(z' : X), h.R_le_T (h.Z_le_R z'.2)⟩ := mul_inv_eq_one.mp hab
    have hXX : (z : X) = (z' : X) := congrArg (fun t : T => (t : X)) hab2
    exact Subtype.ext hXX
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨(t : X), Subgroup.mem_subgroupOf.mp ht⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
