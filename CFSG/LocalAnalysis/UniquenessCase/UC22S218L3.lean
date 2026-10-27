module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Facts
public import CFSG.Quasithin.Vol2.KGFact4413L3X
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinAut
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.RankThree.PartOne.LIT.RankPSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (exists_mulEquiv_projectiveSL_of_lieModel)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj proj_eq_one_iff scalars
  projUnitriangular conjAut fieldAut fieldAut_proj semilinearAutGroup mem_semilinearAutGroup_iff)
open CFSG.Quasithin.H13.KG4413 (dg3 coe_dg3 dL3 dL3_inf dL3_le_normalizer gammaZero_dL3 w0L3
  wJ_mul_dg3_mul_wJ conjAut_dL3_mem not_dvd_index_of_isPSL3 pow_eq_one_of_isPSL3)
open CFSG.Quasithin.H13.L32A.C.SkPf (mem_centMod centMod_map normalizer_map isSylowTwoOf_sylow)
open CFSG.Quasithin.SteinbergBS (gammaZero upperTriangular_of_semilinear_normalizes
  exists_eq_semilinear_mul_gammaZero)
open CFSG.QuasithinUnique.Setup.X7a (wJ wJ_inv even_rank_two_residual_linear)
open CFSG.AGLEmbedding.ParabAutIrr (lin_power_map exists_pow_two_of_ringEquiv)
open CFSG.LocalAnalysis.GLTheoremA.H81.LinA3 (exists_eq_conjAut_mul_fieldAut_of_odd_pow)

theorem uc22s218_l3_not_three_dvd {s : ℕ} (hs : Odd s) : ¬ 3 ∣ 2 ^ s - 1 := by
  obtain ⟨k, rfl⟩ := hs
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have h3 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [h2]
    omega
  generalize 2 ^ (2 * k + 1) = X at h3 ⊢
  omega

private theorem mem_of_mem_map_equiv {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    {U : Subgroup M} {x : M} (h : e x ∈ U.map e.toMonoidHom) : x ∈ U := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h
  exact h

private theorem congr_apply_apply {M M' : Type} [Group M] [Group M'] (e : M ≃* M') (α : MulAut M)
    (x : M) : MulAut.congr e α (e x) = e (α x) := by
  show e (α (e.symm (e x))) = e (α x)
  rw [MulEquiv.symm_apply_apply]

private theorem map_congr_eq {M M' : Type} [Group M] [Group M'] (e : M ≃* M') {U : Subgroup M}
    {α : MulAut M} (h : U.map α.toMonoidHom = U) :
    (U.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom = U.map e.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have h1 : α u ∈ U.map α.toMonoidHom := ⟨u, hu, rfl⟩
    rw [h] at h1
    refine ⟨α u, h1, ?_⟩
    exact (congr_apply_apply e α u).symm
  · rintro ⟨u, hu, rfl⟩
    have h1 : u ∈ U.map α.toMonoidHom := by rw [h]; exact hu
    obtain ⟨v, hv, rfl⟩ := h1
    refine ⟨e v, ⟨v, hv, rfl⟩, ?_⟩
    exact (congr_apply_apply e α v).trans rfl

private theorem mem_iff_of_map_eq {M : Type} [Group M] {U : Subgroup M} {α : MulAut M}
    (h : U.map α.toMonoidHom = U) (z : M) : z ∈ U ↔ α z ∈ U := by
  constructor
  · intro hz
    rw [← h]
    exact ⟨z, hz, rfl⟩
  · intro hz
    rw [← h] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    have : y = z := α.injective hyz
    rwa [this] at hy

@[expose] noncomputable def uc22s218_l3_dt (K : Type) [Field K] : Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp ((dg3 (F := K)).comp (MonoidHom.inl Kˣ Kˣ))

section Cartan

variable {K : Type} [Field K]

private theorem dt_apply (x : Kˣ) : uc22s218_l3_dt K x = proj 3 K (dg3 (x, 1)) := rfl

private theorem dt_mem (x : Kˣ) : uc22s218_l3_dt K x ∈ dL3 K :=
  ⟨dg3 (x, 1), ⟨(x, 1), rfl⟩, rfl⟩

private theorem dg3_scalar {t : Kˣ × Kˣ} (h : dg3 t ∈ scalars 3 K) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧ t = (c, c) := by
  obtain ⟨c, hc, hA⟩ := h
  refine ⟨c, hc, Prod.ext (Units.ext ?_) (Units.ext ?_)⟩
  · simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 0) 0
  · simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 1) 1

private theorem dt_injective : Function.Injective (uc22s218_l3_dt K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : proj 3 K (dg3 (x, 1)) = 1 := hx
  obtain ⟨c, -, hc⟩ := dg3_scalar (proj_eq_one_iff.1 hx')
  exact (congrArg Prod.fst hc).trans (congrArg Prod.snd hc).symm

private theorem dL3_comm {a b : projectiveSL 3 K} (ha : a ∈ dL3 K) (hb : b ∈ dL3 K) :
    a * b = b * a := by
  obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hb
  have e : ∀ s t : Kˣ × Kˣ, proj 3 K (dg3 s) * proj 3 K (dg3 t) = proj 3 K (dg3 (s * t)) :=
    fun s t => by rw [map_mul, map_mul]
  rw [e, e, mul_comm]

theorem uc22s218_l3_exists_elemAbelian {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hℓK : ℓ ∣ Nat.card K - 1) [Finite K] :
    ∃ A : Subgroup (projectiveSL 3 K), A ≤ dL3 K ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ (by rw [Nat.card_units]; exact hℓK)
  have hpow : ∀ x : ↥(zpowers ζ), x ^ ℓ = 1 := fun x => by
    rw [← hζ, ← Nat.card_zpowers]
    exact pow_card_eq_one'
  let f : (↥(zpowers ζ) × ↥(zpowers ζ)) →* projectiveSL 3 K :=
    (proj 3 K).comp ((dg3 (F := K)).comp ((zpowers ζ).subtype.prodMap (zpowers ζ).subtype))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : proj 3 K (dg3 ((x.1 : Kˣ), (x.2 : Kˣ))) = 1 := hx
    obtain ⟨c, hc3, hc⟩ := dg3_scalar (proj_eq_one_iff.1 hx')
    have h1 : (x.1 : Kˣ) = c := congrArg Prod.fst hc
    have h2 : (x.2 : Kˣ) = c := congrArg Prod.snd hc
    have hcℓ : c ^ ℓ = 1 := by
      have := congrArg Subtype.val (hpow x.1)
      simpa [← h1] using this
    have hcop : Nat.gcd 3 ℓ = 1 := (Nat.coprime_primes Nat.prime_three hℓ).2 (Ne.symm hℓ3)
    have hc1 : c = 1 := by
      have h := pow_gcd_eq_one.2 ⟨hc3, hcℓ⟩
      rwa [hcop, pow_one] at h
    exact Prod.ext (Subtype.ext (h1.trans hc1)) (Subtype.ext (h2.trans hc1))
  refine ⟨(⊤ : Subgroup (↥(zpowers ζ) × ↥(zpowers ζ))).map f, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨dg3 ((x.1 : Kˣ), (x.2 : Kˣ)), ⟨((x.1 : Kˣ), (x.2 : Kˣ)), rfl⟩, rfl⟩
  · exact CFSG.SectionRank.isElemAbelian_map
      ⟨inferInstance, fun x _ => Prod.ext (hpow x.1) (hpow x.2)⟩ f
  · rw [Subgroup.card_map_of_injective hf, Subgroup.card_top, Nat.card_prod, Nat.card_zpowers, hζ,
      sq]

end Cartan

section Action

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem map_dg3 (σ : K ≃+* K) {j : ℕ} (hj : ∀ x : K, σ x = x ^ 2 ^ j) (t : Kˣ × Kˣ) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (dg3 t) = dg3 (t.1 ^ 2 ^ j, t.2 ^ 2 ^ j) := by
  obtain ⟨x, y⟩ := t
  have hx : σ (x : K) = ((x ^ 2 ^ j : Kˣ) : K) := by rw [hj, Units.val_pow_eq_pow_val]
  have hy : σ (y : K) = ((y ^ 2 ^ j : Kˣ) : K) := by rw [hj, Units.val_pow_eq_pow_val]
  ext i k
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_dg3, coe_dg3]
  fin_cases i <;> fin_cases k <;> simp [RingHom.mapMatrix_apply, hx, hy]

omit [Finite K] in
private theorem gammaZero_dt (x : Kˣ) : gammaZero K (uc22s218_l3_dt K x) = uc22s218_l3_dt K x := by
  rw [gammaZero_dL3 (dt_mem x)]
  have hinv : ((dg3 (x, 1))⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) = dg3 (x⁻¹, 1) := by
    rw [← map_inv]
    simp
  rw [dt_apply, w0L3, ← map_inv (proj 3 K) (dg3 (x, 1)), ← map_inv (proj 3 K) wJ, wJ_inv, hinv,
    ← map_mul, ← map_mul, wJ_mul_dg3_mul_wJ]
  simp

private theorem semilinear_dt {A : GL (Fin 3) K}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) (σ : K ≃+* K) :
    ∃ j : ℕ, ∀ x : Kˣ, (conjAut 3 K A * fieldAut 3 K σ) (uc22s218_l3_dt K x) *
      (uc22s218_l3_dt K (x ^ 2 ^ j))⁻¹ ∈ projUnitriangular 3 K := by
  obtain ⟨j, hj⟩ := exists_pow_two_of_ringEquiv σ
  refine ⟨j, fun x => ?_⟩
  have h1 : fieldAut 3 K σ (uc22s218_l3_dt K x) = uc22s218_l3_dt K (x ^ 2 ^ j) := by
    rw [dt_apply, fieldAut_proj, map_dg3 σ hj, dt_apply]
    simp
  rw [MulAut.mul_apply, h1]
  have hd : uc22s218_l3_dt K (x ^ 2 ^ j) ∈ dL3 K := dt_mem _
  have h2 := (Subgroup.mem_normalizer_iff.mp (dL3_le_normalizer hd) _).mp (conjAut_dL3_mem hA hd)
  rwa [mul_inv_cancel_left] at h2

theorem uc22s218_l3_torus_action {β : MulAut (projectiveSL 3 K)}
    (hβ : (projUnitriangular 3 K).map β.toMonoidHom = projUnitriangular 3 K) :
    ∃ j : ℕ, ∀ x : Kˣ, β (uc22s218_l3_dt K x) * (uc22s218_l3_dt K (x ^ 2 ^ j))⁻¹ ∈
      projUnitriangular 3 K := by
  by_cases hs : β ∈ semilinearAutGroup 3 K
  · obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hs
    exact semilinear_dt (upperTriangular_of_semilinear_normalizes hβ) σ
  · obtain ⟨A, σ, hA, rfl⟩ := exists_eq_semilinear_mul_gammaZero hβ hs
    obtain ⟨j, hj⟩ := semilinear_dt hA σ
    refine ⟨j, fun x => ?_⟩
    rw [MulAut.mul_apply, gammaZero_dt]
    exact hj x

theorem uc22s218_l3_pow_action_model {β : MulAut (projectiveSL 3 K)}
    (hβ : (projUnitriangular 3 K).map β.toMonoidHom = projUnitriangular 3 K) {m : ℕ}
    (hm : Odd m) (hβm : β ^ m = 1) :
    ∃ k : ℕ, ∀ b ∈ normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)),
      β b * (b ^ k)⁻¹ ∈ projUnitriangular 3 K := by
  obtain ⟨A, σ, hAσ⟩ := exists_eq_conjAut_mul_fieldAut_of_odd_pow (n := 3) (by norm_num) hm hβm
  exact lin_power_map (n := 3) (by norm_num) (mem_semilinearAutGroup_iff.2 ⟨A, σ, hAσ⟩)
    (mem_iff_of_map_eq hβ)

theorem uc22s218_l3_exists_mem_centMod_model {n s : ℕ} (hK : Nat.card K = 2 ^ n) (hs : Odd s)
    (hsn : s ∣ n) : ∃ d : projectiveSL 3 K, orderOf d = 2 ^ s - 1 ∧
      ∀ β : MulAut (projectiveSL 3 K), (∃ e : ℕ, β ^ 2 ^ e = 1) →
        (projUnitriangular 3 K).map β.toMonoidHom = projUnitriangular 3 K →
          d ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod (projUnitriangular 3 K) β := by
  obtain ⟨t, ht⟩ := uc22p218c_exists_orderOf_units hK hsn
  have ht' : t ^ 2 ^ s = t := by
    have h1 : t ^ (2 ^ s - 1) = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := s)), pow_succ, h1, one_mul]
  refine ⟨uc22s218_l3_dt K t, by rw [orderOf_injective _ dt_injective, ht], fun β hβ hβU => ?_⟩
  obtain ⟨e, he⟩ := hβ
  obtain ⟨j, hj⟩ := uc22s218_l3_torus_action hβU
  have h1 := uc22p218c_iterate_mul_inv_mem hβU (uc22s218_l3_dt K) (fun x => x ^ 2 ^ j) hj (2 ^ e) t
  rw [he, MulAut.one_apply, uc22p218c_iterate_pow_two_pow, ← map_inv, ← map_mul] at h1
  have h2 : t * (t ^ 2 ^ (j * 2 ^ e))⁻¹ = 1 := by
    apply dt_injective
    rw [map_one]
    have h3 : uc22s218_l3_dt K (t * (t ^ 2 ^ (j * 2 ^ e))⁻¹) ∈ dL3 K ⊓ projUnitriangular 3 K :=
      ⟨dt_mem _, h1⟩
    rwa [dL3_inf, Subgroup.mem_bot] at h3
  have h4 : t ^ 2 ^ j = t :=
    uc22p218c_pow_two_pow_eq_of_mul_two_pow hs ht' e (mul_inv_eq_one.1 h2).symm
  refine mem_centMod.2 ⟨dL3_le_normalizer (dt_mem t), ?_⟩
  have h5 := hj t
  rwa [h4] at h5

end Action

section Model

theorem uc22s218_l3_exists_model {Y : Type} [Group Y] {n : ℕ} (hY : IsL3 Y n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (Y ≃* projectiveSL 3 K) := by
  obtain ⟨K, hF, hfin, hK, he⟩ := exists_mulEquiv_projectiveSL_of_lieModel hY
  exact ⟨K, hF, hfin, finite_field_prime_power_characteristic Nat.prime_two
    (LieModel.admissible hY).2.1 hK, hK, he⟩

theorem uc22s218_l3_torus {Y : Type} [Group Y] {n : ℕ} (hY : IsL3 Y n) :
    ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ℓ ≠ 3 →
        ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2 := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_l3_exists_model hY
  refine ⟨(dL3 K).map e.symm.toMonoidHom, ?_, fun ℓ hℓ hℓn hℓ3 => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, dL3_comm hx hy]
  · obtain ⟨A, hAT, hAe, hAc⟩ := uc22s218_l3_exists_elemAbelian hℓ hℓ3 (by rw [hK]; exact hℓn)
    refine ⟨A.map e.symm.toMonoidHom, Subgroup.map_mono hAT,
      CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hAc]

theorem uc22s218_l3_pRank_le_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsL3 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_l3_exists_model hY
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 K)]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSL_three_le (LieModel.admissible hY).2.1 hK hp hp2

theorem uc22s218_l3_pRank_eq_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsL3 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup Y) = 2 := by
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hr3 : r ≠ 3 := fun h => uc22s218_l3_not_three_dvd hs (h ▸ hrs)
  refine le_antisymm (uc22s218_l3_pRank_le_two hY hr hr2) ?_
  obtain ⟨T, -, hT⟩ := uc22s218_l3_torus hY
  obtain ⟨A, -, hAe, hAc⟩ := hT r hr (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)) hr3
  exact CFSG.SectionRank.le_pRank hr.one_lt le_top hAe hAc

theorem uc22s218_l3_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsL3 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY' := LieModel.statedClassicalModel hY (by decide)
  obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
  rw [Sylow.card_eq_index_normalizer P]
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hr3 : r ≠ 3 := fun h => uc22s218_l3_not_three_dvd hs (h ▸ hrs)
  have hr5 := hr.five_le_of_ne_two_of_ne_three hr2 hr3
  exact not_dvd_index_of_isPSL3 hY' (isSylowTwoOf_sylow P) hr (by omega)
    (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))

theorem uc22s218_l3_eq_one_of_pow_eq_one {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsL3 Y n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n - 1)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {b : Y} (hb : b ∈ normalizer (U : Set Y))
    (hbp : b ^ p = 1) : b = 1 := by
  have hY' := LieModel.statedClassicalModel hY (by decide)
  have hodd : Odd (orderOf b) := (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hbp)
  have h2 := pow_eq_one_of_isPSL3 hY' hU hb hodd
  have hcop : Nat.Coprime p (2 ^ n - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have h := pow_gcd_eq_one.2 ⟨hbp, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

theorem uc22s218_l3_pow_action {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsL3 Y n)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {α : MulAut Y} (hα : U.map α.toMonoidHom = U)
    {m : ℕ} (hm : Odd m) (hαm : α ^ m = 1) :
    ∃ k : ℕ, ∀ b ∈ normalizer (U : Set Y), α b * (b ^ k)⁻¹ ∈ U := by
  have hY' := LieModel.statedClassicalModel hY (by decide)
  obtain ⟨K, _, _, _, ψ, hK, hψU, -, -⟩ := even_rank_two_residual_linear hY' hU
  have hβU : (projUnitriangular 3 K).map (MulAut.congr ψ α).toMonoidHom =
      projUnitriangular 3 K := by
    rw [← hψU]
    exact map_congr_eq ψ hα
  have hβm : MulAut.congr ψ α ^ m = 1 := by rw [← map_pow, hαm, map_one]
  obtain ⟨k, hk⟩ := uc22s218_l3_pow_action_model hβU hm hβm
  refine ⟨k, fun b hb => ?_⟩
  have hb' : ψ b ∈ normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
    rw [← hψU, normalizer_map]
    exact Subgroup.mem_map_of_mem ψ.toMonoidHom hb
  have h := hk (ψ b) hb'
  have e1 : MulAut.congr ψ α (ψ b) * ((ψ b) ^ k)⁻¹ = ψ (α b * (b ^ k)⁻¹) := by
    rw [map_mul, map_inv, map_pow, congr_apply_apply]
  rw [e1, ← hψU] at h
  exact mem_of_mem_map_equiv ψ h

theorem uc22s218_l3_exists_mem_centMod {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsL3 Y n)
    {s : ℕ} {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) (hs : Odd s) (hsn : s ∣ n) :
    ∃ d : Y, orderOf d = 2 ^ s - 1 ∧ ∀ α : MulAut Y, (∃ e : ℕ, α ^ 2 ^ e = 1) →
      U.map α.toMonoidHom = U → d ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod U α := by
  have hY' := LieModel.statedClassicalModel hY (by decide)
  obtain ⟨K, _, _, _, ψ, hK, hψU, -, -⟩ := even_rank_two_residual_linear hY' hU
  obtain ⟨d₀, hd₀o, hd₀⟩ := uc22s218_l3_exists_mem_centMod_model hK hs hsn
  refine ⟨ψ.symm d₀, by rw [MulEquiv.orderOf_eq, hd₀o], fun α hα hαU => ?_⟩
  obtain ⟨e, he⟩ := hα
  have h1 := hd₀ (MulAut.congr ψ α) ⟨e, by rw [← map_pow, he, map_one]⟩
    (by rw [← hψU]; exact map_congr_eq ψ hαU)
  rw [← hψU, centMod_map, MulEquiv.symm_apply_apply] at h1
  exact Subgroup.mem_map_equiv.1 h1

theorem torusFacts218_L3 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsL3 Y n) :
    TorusFacts218 Y n (fun p => p ∣ 2 ^ n - 1 ∧ p ≠ 3) (fun p => ¬ p ∣ 2 ^ n - 1) where
  tor_of_dvd := fun hs hsn _ hrs =>
    ⟨hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn),
      fun h => uc22s218_l3_not_three_dvd hs (h ▸ hrs)⟩
  pRank_eq_two := fun hs hsn hr hrs => uc22s218_l3_pRank_eq_two hY hs hsn hr hrs
  not_dvd_card_sylow := fun hs hsn hr hrs => uc22s218_l3_not_dvd_card_sylow hY hs hsn hr hrs
  pow_action := fun {U} hU {α} hα {m} hm hαm => uc22s218_l3_pow_action hY hU hα hm hαm
  exists_mem_centMod := fun {s U} hU hs hsn => uc22s218_l3_exists_mem_centMod hY hU hs hsn
  exists_pair := by
    obtain ⟨T, hTc, hTE⟩ := uc22s218_l3_torus hY
    intro s r p hs hsn hr hrd hp hTp _
    have hr3 : r ≠ 3 := fun h => uc22s218_l3_not_three_dvd hs (h ▸ hrd)
    obtain ⟨A, hAT, hAe, hAc⟩ :=
      hTE r hr (hrd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)) hr3
    obtain ⟨Q, hQT, hQe, hQc⟩ := hTE p hp hTp.1 hTp.2
    refine ⟨A, Q, hAe, hAc, hQe, hQc, fun x hx => ⟨1, fun e he => ?_⟩⟩
    rw [pow_one, mul_inv_eq_iff_eq_mul]
    exact hTc x (hQT hx) e (hAT he)
  eq_one_of_pow_eq_one := fun {p} hp hp2 hOut {U} hU {b} hb hbp =>
    uc22s218_l3_eq_one_of_pow_eq_one hY hp hp2 hOut hU hb hbp
  pRank_le_two := fun hp hp2 _ => uc22s218_l3_pRank_le_two hY hp hp2

end Model

end CFSG.LocalAnalysis.UniquenessCase.UC22
