module

public import CFSG.RankThree.PartOne.KF.R8Torus
public import CFSG.RankThree.PartOne.KF.SpSylow

public section

namespace CFSG.RankThree.PartOne.KFQ

open CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def M8 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  (LinearEquiv.det : (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) →* Kˣ).ker

theorem mem_M8_iff (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : g ∈ M8 K ↔ LinearEquiv.det g = 1 :=
  MonoidHom.mem_ker

omit [Finite K] [CharP K 2] in
theorem det_eq_one_of_pow_eq_one {V : Type*} [AddCommGroup V] [Module K V] (hp : p.Prime)
    (hnd : ¬ p ∣ Nat.card K - 1) (g : V ≃ₗ[K] V) (hg : g ^ p = 1) : LinearEquiv.det g = 1 := by
  have h1 : (LinearEquiv.det g) ^ p = 1 := by rw [← map_pow, hg, map_one]
  have hcop : Nat.Coprime p (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have h3 : orderOf (LinearEquiv.det g) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (LinearEquiv.det g) ∣ Nat.card Kˣ := orderOf_dvd_natCard _
  have : orderOf (LinearEquiv.det g) = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h4
  exact orderOf_eq_one_iff.mp this

theorem d8Emb_mem_M8 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (v : D8Mod p (Qext K)) : d8Emb v ∈ M8 K :=
  (mem_M8_iff _).mpr (det_eq_one_of_pow_eq_one hp (not_dvd_pred hp hp2 hpq) _ (d8Emb_pow v))

theorem finrank_qv : Module.finrank K (QV K (Fin 2)) = 4 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_qext]

@[expose] noncomputable def qvBasis (K : Type) [Field K] [Finite K] [CharP K 2] :
    Module.Basis (Fin 4) K (QV K (Fin 2)) :=
  Module.finBasisOfFinrankEq K (QV K (Fin 2)) finrank_qv

@[expose] noncomputable def glEquiv :
    (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ≃* GL (Fin 4) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (QV K (Fin 2))).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (qvBasis K)).toMulEquiv)

theorem det_glEquiv (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :
    ((glEquiv g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = (LinearEquiv.det g : K) := by
  rw [LinearEquiv.coe_det]
  exact LinearMap.det_toMatrix (qvBasis K) (g : QV K (Fin 2) →ₗ[K] QV K (Fin 2))

theorem factorization_card_gl (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).factorization p =
      2 * (Nat.card (Qext K)ˣ).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_congr (glEquiv (K := K)).toEquiv]
  have hcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hpK : ¬ p ∣ Fintype.card K := by
    intro h
    rw [← hcard] at h
    have h1 : p ∣ 1 := (Nat.dvd_add_right h).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hq : ((Fintype.card K : ℕ) : ZMod p) = -1 := by
    have h1 : (((Nat.card K + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    rw [Nat.cast_add, Nat.cast_one, hcard] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = 2 := by
    rw [hq]
    refine orderOf_neg_one.trans ?_
    have : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
    rw [this]
    simp [hp2]
  rw [CFSG.GroupTheory.WeirSylow.factorization_card_GL (hp.odd_of_ne_two hp2) K hpK 4, hord]
  have h2 : padicValNat p ((4 / 2).factorial) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have : p ∣ 2 := by simpa [Nat.factorial] using h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rw [h2, add_zero, Nat.card_units, FiniteField.natCard_extension K 2 2,
    Nat.factorization_def _ hp, hcard]
  norm_num [mul_comm]

theorem coprime_card_units_four : Nat.Coprime (Nat.card Kˣ) 4 := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
  have h2 : Even (2 ^ (n : ℕ)) := (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  have h1 : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
  have hodd : Odd (2 ^ (n : ℕ) - 1) := Nat.Even.sub_odd h1 h2 odd_one
  have h3 : Nat.Coprime (2 ^ (n : ℕ) - 1) 2 := Nat.coprime_two_right.mpr hodd
  have : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [this]
  exact Nat.Coprime.pow_right 2 h3

section Scalar

omit [Finite K] [CharP K 2]

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem smulOfUnit_apply (a : Kˣ) (v : V) :
    (LinearEquiv.smulOfUnit a : V ≃ₗ[K] V) v = (a : K) • v := rfl

theorem smulOfUnit_comm (a : Kˣ) (h : V ≃ₗ[K] V) :
    (LinearEquiv.smulOfUnit a : V ≃ₗ[K] V) * h = h * (LinearEquiv.smulOfUnit a : V ≃ₗ[K] V) := by
  refine LinearEquiv.ext fun v => ?_
  show (a : K) • h v = h ((a : K) • v)
  rw [map_smul]

theorem det_smulOfUnit [FiniteDimensional K V] (a : Kˣ) :
    LinearEquiv.det (LinearEquiv.smulOfUnit a : V ≃ₗ[K] V) = a ^ Module.finrank K V := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have : ((LinearEquiv.smulOfUnit a : V ≃ₗ[K] V) : V →ₗ[K] V) = (a : K) • LinearMap.id := by
    ext v; exact smulOfUnit_apply a v
  rw [this, LinearMap.det_smul]
  simp

theorem exists_scalar_det [FiniteDimensional K V] {n : ℕ} (hn : Module.finrank K V = n)
    (hcop : Nat.Coprime (Nat.card Kˣ) n) (g : V ≃ₗ[K] V) :
    ∃ a : Kˣ, LinearEquiv.det ((LinearEquiv.smulOfUnit a : V ≃ₗ[K] V) * g) = 1 := by
  obtain ⟨a, ha⟩ := (powCoprime hcop).surjective (LinearEquiv.det g)⁻¹
  refine ⟨a, ?_⟩
  rw [map_mul, det_smulOfUnit, hn]
  have : a ^ n = (LinearEquiv.det g)⁻¹ := ha
  rw [this, inv_mul_cancel]

end Scalar

section Sylow

variable [Fact p.Prime]

@[expose] def pairHom {L : Type} [Field L] (S : Subgroup Lˣ) : ↥S × ↥S →* (Fin 2 → Lˣ) where
  toFun x := ![(x.1 : Lˣ), (x.2 : Lˣ)]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i <;> simp

@[expose] noncomputable def sylowHom (S : Subgroup (Qext K)ˣ) :
    ↥S × ↥S →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  torusHom.comp (pairHom S)

theorem sylowHom_injective (S : Subgroup (Qext K)ˣ) : Function.Injective (sylowHom (K := K) S) := by
  intro x y h
  have h0 := congrArg (fun g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) => g (fun _ => 1) 0) h
  have h1 := congrArg (fun g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) => g (fun _ => 1) 1) h
  simp only [sylowHom, MonoidHom.comp_apply, torusHom_apply, torusEquiv_apply, pairHom,
    MonoidHom.coe_mk, OneHom.coe_mk, mul_one] at h0 h1
  exact Prod.ext (Subtype.ext (Units.ext (by simpa using h0)))
    (Subtype.ext (Units.ext (by simpa using h1)))

theorem card_sylowHom_range (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (S : Sylow p (Qext K)ˣ) :
    Nat.card (sylowHom (K := K) (S : Subgroup (Qext K)ˣ)).range =
      p ^ (Nat.card (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).factorization p := by
  have hinj := sylowHom_injective (K := K) (S : Subgroup (Qext K)ˣ)
  rw [factorization_card_gl (Fact.out) hp2 hpq,
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_prod, Sylow.card_eq_multiplicity S, ← sq, ← pow_mul, mul_comm]

end Sylow

instance : Finite (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  Finite.of_equiv _ (glEquiv (K := K)).symm.toEquiv

theorem exists_conj_into_T8 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (X : Subgroup ↥(M8 K)) (hX : ∀ x ∈ X, x ^ p = 1) :
    ∃ g : ↥(M8 K), ∀ x ∈ X, g * x * g⁻¹ ∈
      (d8Emb : D8Mod p (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).range.subgroupOf
        (M8 K) := by
  have : Fact p.Prime := ⟨hp⟩
  let S : Sylow p (Qext K)ˣ := default
  let P := (sylowHom (K := K) (S : Subgroup (Qext K)ˣ)).range
  have hPcard : Nat.card P = p ^ (Nat.card (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).factorization p :=
    card_sylowHom_range hp2 hpq S
  let X' : Subgroup (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) := X.map (M8 K).subtype
  have hX' : ∀ x ∈ X', x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hX x hx
    simpa using congrArg Subtype.val this
  obtain ⟨g, hg⟩ := exists_conj_le_sylow P hPcard X' hX'
  obtain ⟨a, ha⟩ := exists_scalar_det finrank_qv coprime_card_units_four g
  set z := (LinearEquiv.smulOfUnit a : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) with hz
  have hgM : z * g ∈ M8 K := (mem_M8_iff _).mpr ha
  refine ⟨⟨z * g, hgM⟩, fun x hx => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  have hconj : ((⟨z * g, hgM⟩ * x * ⟨z * g, hgM⟩⁻¹ : ↥(M8 K)) :
      QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = g * (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * g⁻¹ := by
    show z * g * (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * (z * g)⁻¹ = g * x * g⁻¹
    have hzc : ∀ h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2), z * h * z⁻¹ = h := fun h => by
      rw [hz, smulOfUnit_comm a h, mul_inv_cancel_right]
    calc z * g * (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * (z * g)⁻¹
        = z * (g * x * g⁻¹) * z⁻¹ := by group
      _ = g * x * g⁻¹ := hzc _
  rw [hconj]
  have hmem := hg (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ⟨x, hx, rfl⟩
  obtain ⟨⟨s, t⟩, hst⟩ := hmem
  have hxp : (g * (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * g⁻¹) ^ p = 1 := by
    have hxp0 : (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ^ p = 1 := by
      simpa using congrArg Subtype.val (hX x hx)
    rw [conj_pow, hxp0, mul_one, mul_inv_cancel]
  have hstp : (s, t) ^ p = 1 := by
    apply sylowHom_injective (K := K) (S : Subgroup (Qext K)ˣ)
    rw [map_pow, hst, hxp, map_one]
  have hs : (s : (Qext K)ˣ) ^ p = 1 := by
    have := congrArg Prod.fst hstp
    simpa using congrArg Subtype.val this
  have ht : (t : (Qext K)ˣ) ^ p = 1 := by
    have := congrArg Prod.snd hstp
    simpa using congrArg Subtype.val this
  refine ⟨(⟨(s : (Qext K)ˣ), (mem_rootsOfUnity p _).mpr hs⟩,
    ⟨(t : (Qext K)ˣ), (mem_rootsOfUnity p _).mpr ht⟩), ?_⟩
  rw [← hst]
  show torusEquiv (d8Pair _) = torusEquiv (pairHom _ (s, t))
  congr 1

end CFSG.RankThree.PartOne.KFQ
