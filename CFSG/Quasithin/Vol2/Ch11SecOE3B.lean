module

public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Assembly.LowTwoRank Matrix Subgroup

@[expose] def R2Shape (r : ℕ) (X : Type) [Group X] : Prop :=
  CFSG.IsQuasisimple X ∧ (∀ z ∈ center X, z ^ 3 = 1) ∧
    (∃ E : Subgroup X, CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2) ∧
    StatedClassicalModel (X ⧸ center X) .PSL 3 r 1

variable {K : Type} [Field K]

@[expose] def uE (a b : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, a; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_uE (a b : K) :
    ((uE a b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, a; 0, 1, b; 0, 0, 1] := rfl

theorem uE_mul (a b c d : K) : uE a b * uE c d = uE (a + c) (b + d) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uE, coe_uE, coe_uE]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

@[expose] def uHom (K : Type) [Field K] : Multiplicative (K × K) →* SpecialLinearGroup (Fin 3) K
    where
  toFun x := uE (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uE]
  map_mul' x y := by
    rw [uE_mul]
    rfl

theorem uHom_injective : Function.Injective (uHom K) := by
  intro x y h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 2) h
  simp only [uHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_uE] at h1 h2
  apply Multiplicative.toAdd.injective
  exact Prod.ext (by simpa using h1) (by simpa using h2)

theorem center_pow_three {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ center _) : x ^ 3 = 1 := by
  obtain ⟨c, hc, hcx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hc3 : c ^ 3 = 1 := by simpa using hc
  have h3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← hcx, ← map_pow, hc3, map_one]
  have := congrFun (congrFun h3 i) j
  rwa [← Matrix.SpecialLinearGroup.coe_pow] at this

theorem r2Shape_SL3 [Finite K] {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    R2Shape r (SpecialLinearGroup (Fin 3) K) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r := charP_of_card_eq_prime_pow (p := r) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  refine ⟨CFSG.LieType.Universal.SpecialLinear.isQuasisimple (F := K) (m := 2) le_rfl,
    fun z hz => center_pow_three hz, ⟨(uHom K).range, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have hx : x ^ r = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      refine Prod.ext ?_ ?_
      · change r • (Multiplicative.toAdd x).1 = 0
        rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      · change r • (Multiplicative.toAdd x).2 = 0
        rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rw [hx, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective uHom_injective).toEquiv]
    change Nat.card (K × K) = r ^ 2
    rw [Nat.card_prod, hK, sq]
  · refine ⟨⟨hr, le_rfl, by norm_num, ?_, ?_⟩, K, inferInstance, inferInstance,
      by rw [hK, pow_one], ⟨projectiveSpecialLinearGroupEquivStatedProj 3 K⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega

end CFSG.Quasithin.Vol2.Ch11.OE3

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Assembly.LowTwoRank Matrix Subgroup

variable {K : Type} [Field K] {X Y : Type} [Group X] [Group Y]

theorem statedPSL_of_mulEquiv {n p f : ℕ} (e : X ≃* Y) (h : StatedClassicalModel X .PSL n p f) :
    StatedClassicalModel Y .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem eq_one_of_pow_three {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) {x : X} (h3 : x ^ 3 = 1)
    (hxr : x ^ r = 1) : x = 1 := by
  have hcop : Nat.Coprime 3 r :=
    (Nat.coprime_primes Nat.prime_three hr).mpr (by omega)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one hxr))

theorem R2Shape.of_surjective {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (h : R2Shape r X)
    {φ : X →* Y} (hs : Function.Surjective φ) (hnt : ∃ x, φ x ≠ 1) : R2Shape r Y := by
  obtain ⟨hq, hZ, ⟨E, hE, hEc⟩, hM⟩ := h
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hnt
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hek : (e : X) ∈ φ.ker := he
    exact Subtype.ext (eq_one_of_pow_three hr hr5 (hZ _ (hker hek)) (hE.2 e e.2))
  have hrange : (φ.comp E.subtype).range = E.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hs hnt, ?_,
    ⟨E.map φ, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩, ?_⟩
  · intro z hz
    rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hq hs hker] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [← map_pow, hZ x hx, map_one]
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  · rw [← hrange, ← hEc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · exact statedPSL_of_mulEquiv (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hs
      hker) hM

theorem uE_ne_one : uE (1 : K) 0 ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h
  simp [coe_uE] at this

theorem uE_not_mem_center : uE (1 : K) 0 ∉ center (SpecialLinearGroup (Fin 3) K) := by
  intro h
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have := congrFun (congrFun hc 0) 2
  simp [coe_uE, Matrix.scalar_apply] at this

theorem r2Shape_of_isSL3 {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (h : IsSL3 r X) : R2Shape r X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  let ψ : SpecialLinearGroup (Fin 3) K →* X :=
    ((specialLinearGroupEquivStatedSL 3 K).trans e.symm).toMonoidHom
  refine (r2Shape_SL3 hr hK).of_surjective hr hr5 (φ := ψ) (MulEquiv.surjective _) ⟨uE 1 0, ?_⟩
  intro h1
  apply uE_ne_one (K := K)
  exact ((specialLinearGroupEquivStatedSL 3 K).trans e.symm).injective (h1.trans (map_one _).symm)

theorem r2Shape_of_isPSL {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (h : IsPSL 3 r 1 X) :
    R2Shape r X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = r := by rw [hK, pow_one]
  let ψ : SpecialLinearGroup (Fin 3) K →* X :=
    (e.symm.toMonoidHom.comp (projectiveSpecialLinearGroupEquivStatedProj 3 K).toMonoidHom).comp
      (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 3) K)))
  have hψ : Function.Surjective ψ :=
    (e.symm.surjective.comp (projectiveSpecialLinearGroupEquivStatedProj 3 K).surjective).comp
      (QuotientGroup.mk'_surjective _)
  refine (r2Shape_SL3 hr hK').of_surjective hr hr5 hψ ⟨uE 1 0, ?_⟩
  intro h1
  apply uE_not_mem_center (K := K)
  have h3 : e.symm ((projectiveSpecialLinearGroupEquivStatedProj 3 K)
      (QuotientGroup.mk' (center (SpecialLinearGroup (Fin 3) K)) (uE 1 0))) = 1 := h1
  rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff _).mp h3

end CFSG.Quasithin.Vol2.Ch11.OE3
