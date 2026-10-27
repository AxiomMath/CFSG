module

public import CFSG.Walter.Ree.T2Interface
public import CFSG.Walter.Ree.WardThompson

public section

namespace CFSG.Walter.Ree.T2.RType

open CFSG.Walter.Ward
open scoped Pointwise

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem ι_apply (n : ThompsonN k σ) : R.ι n = ((R.e.symm n : R.N) : G) := rfl

theorem ι_injective : Function.Injective R.ι := fun _ _ h =>
  R.e.symm.injective (Subtype.ext h)

theorem ι_mem (n : ThompsonN k σ) : R.ι n ∈ R.N := (R.e.symm n).2

theorem exists_ι {g : G} (hg : g ∈ R.N) : ∃ n, g = R.ι n :=
  ⟨R.e ⟨g, hg⟩, by simp [ι_apply]⟩

theorem mem_N_iff (g : G) : g ∈ R.N ↔ ∃ n, g = R.ι n :=
  ⟨R.exists_ι, fun ⟨n, hn⟩ => hn ▸ R.ι_mem n⟩

theorem pglK_mul_self : pglK * pglK = 1 := by decide

theorem K_mul_K : R.K * R.K = 1 := by
  rw [← R.base_k, ← map_mul]
  have : PGammaL28.k * PGammaL28.k = 1 := Subtype.ext pglK_mul_self
  rw [this, map_one]

theorem K_inv_eq : R.K⁻¹ = R.K := inv_eq_of_mul_eq_one_right R.K_mul_K

theorem K_mul_torus (t : kˣ) :
    R.K * R.ι (ThompsonN.torus σ t) = R.ι (ThompsonN.torus σ t⁻¹) * R.K := by
  have h : R.K⁻¹ * R.ι (ThompsonN.torus σ t) * R.K = R.ι (ThompsonN.torus σ t⁻¹) := R.K_inv t
  rw [R.K_inv_eq] at h
  calc R.K * R.ι (ThompsonN.torus σ t) = R.K * R.ι (ThompsonN.torus σ t) * (R.K * R.K) := by
        rw [R.K_mul_K, mul_one]
    _ = (R.K * R.ι (ThompsonN.torus σ t) * R.K) * R.K := by group
    _ = _ := by rw [h]

theorem torus_mul_K (t : kˣ) :
    R.ι (ThompsonN.torus σ t) * R.K = R.K * R.ι (ThompsonN.torus σ t⁻¹) := by
  rw [R.K_mul_torus, inv_inv]

theorem K_not_mem_N : R.K ∉ R.N := R.K_not_mem

theorem card_N :
    Nat.card R.N = R.hyp.q ^ 3 * (R.hyp.q - 1) :=
  (ward_thompsonIHyp R.hyp R.P).card

theorem card_G :
    Nat.card G = R.hyp.q ^ 3 * (R.hyp.q ^ 3 + 1) * (R.hyp.q - 1) :=
  (ward_order R.hyp).2

theorem q_eq :
    ∃ n ≥ 1, R.hyp.q = 3 ^ (2 * n + 1) := (ward_order R.hyp).1

section Card

variable [Finite k]

omit [CharP k 3] in
theorem card_thompsonN : Nat.card (ThompsonN k σ) = Nat.card k ^ 3 * (Nat.card k - 1) :=
  ThompsonN.card σ

theorem card_k : Nat.card k = R.hyp.q := by
  have h1 : Nat.card k ^ 3 * (Nat.card k - 1) = R.hyp.q ^ 3 * (R.hyp.q - 1) := by
    rw [← card_thompsonN, ← R.card_N]
    exact (Nat.card_congr R.e.toEquiv).symm
  have hk : 2 ≤ Nat.card k := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial k)
    omega
  have hq : 3 ≤ R.hyp.q := R.hyp.three_le_q
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have a1 : Nat.card k ^ 3 < R.hyp.q ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
    have a2 : Nat.card k - 1 < R.hyp.q - 1 := by omega
    have : Nat.card k ^ 3 * (Nat.card k - 1) < R.hyp.q ^ 3 * (R.hyp.q - 1) :=
      Nat.mul_lt_mul'' a1 a2
    omega
  · have a1 : R.hyp.q ^ 3 < Nat.card k ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
    have a2 : R.hyp.q - 1 < Nat.card k - 1 := by omega
    have : R.hyp.q ^ 3 * (R.hyp.q - 1) < Nat.card k ^ 3 * (Nat.card k - 1) :=
      Nat.mul_lt_mul'' a1 a2
    omega

include R in
theorem coprime_q :
    Nat.Coprime (Nat.card k ^ 3) (Nat.card k - 1) := by
  rw [R.card_k]
  refine Nat.Coprime.pow_left 3 ?_
  have h1 : 1 ≤ R.hyp.q := by have := R.hyp.three_le_q; omega
  rw [Nat.coprime_comm, Nat.coprime_self_sub_left h1]
  exact Nat.coprime_one_left _

end Card

theorem mem_P_of_orderOf_dvd [Finite k] (hcop : Nat.Coprime (Nat.card k ^ 3) (Nat.card k - 1))
    {m : ThompsonN k σ} (h : orderOf m ∣ Nat.card k ^ 3) : m ∈ ThompsonN.P σ := by
  rw [ThompsonN.mem_P]
  have h1 : orderOf m.κ ∣ Nat.card k ^ 3 := by
    have := orderOf_map_dvd (ThompsonN.kappaHom σ) m
    exact this.trans h
  have h2 : orderOf m.κ ∣ Nat.card k - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard m.κ
  have := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp this

theorem orderOf_dvd_of_mem_P [Finite k] {p : ThompsonN k σ} (hp : p ∈ ThompsonN.P σ) :
    orderOf p ∣ Nat.card k ^ 3 := by
  rw [← ThompsonN.card_P (σ := σ)]
  exact Subgroup.orderOf_dvd_natCard _ hp

variable [Finite k]

theorem mem_P_iff
    (x : G) : x ∈ (R.P : Subgroup G) ↔ ∃ p ∈ ThompsonN.P σ, x = R.ι p := by
  set Q : Subgroup G := (ThompsonN.P σ).map R.ι with hQ
  have hle : (R.P : Subgroup G) ≤ Q := by
    intro x hx
    obtain ⟨n, rfl⟩ := R.exists_ι (Subgroup.le_normalizer hx)
    refine ⟨n, ?_, rfl⟩
    apply mem_P_of_orderOf_dvd R.coprime_q
    have h1 : orderOf (R.ι n) ∣ Nat.card (R.P : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hx
    rw [orderOf_injective R.ι R.ι_injective n] at h1
    have hP : Nat.card (R.P : Subgroup G) = R.hyp.q ^ 3 :=
      (WardLocal.ward_two_three R.hyp R.P).1
    rwa [hP, ← R.card_k] at h1
  have hcard : Nat.card Q ≤ Nat.card (R.P : Subgroup G) := by
    rw [hQ, Subgroup.card_map_of_injective R.ι_injective, ThompsonN.card_P,
      (WardLocal.ward_two_three R.hyp R.P).1, R.card_k]
  have heq : (R.P : Subgroup G) = Q := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq, hQ, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

theorem ι_mem_P
    {p : ThompsonN k σ} (hp : p ∈ ThompsonN.P σ) : R.ι p ∈ (R.P : Subgroup G) :=
  (R.mem_P_iff _).mpr ⟨p, hp, rfl⟩

omit [Finite k] in
theorem inf_conj_K :
    (R.P : Subgroup G) ⊓ (MulAut.conj R.K • (R.P : Subgroup G)) = ⊥ := by
  rcases (WardLocal.ward_two_three R.hyp R.P).2.1 R.K with h | h
  · exact h
  · exfalso
    apply R.K_not_mem
    have hle : (R.P : Subgroup G) ≤ MulAut.conj R.K • (R.P : Subgroup G) := inf_eq_left.mp h
    have heq : (R.P : Subgroup G) = MulAut.conj R.K • (R.P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [WardLocal.card_conj_smul])
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ y, y ∈ (R.P : Subgroup G) ↔ R.K * y * R.K ∈ (R.P : Subgroup G) := by
      intro y
      conv_lhs => rw [heq]
      rw [WardLocal.mem_conj_smul_iff, R.K_inv_eq]
    rw [R.K_inv_eq]
    exact key x

theorem eq_one_of_K_mul_mem
    {p : ThompsonN k σ} (hp : p ∈ ThompsonN.P σ)
    (h : R.K * R.ι p * R.K ∈ R.N) : p = 1 := by
  obtain ⟨m, hm⟩ := R.exists_ι h
  have hpP := R.ι_mem_P hp
  have hmP : m ∈ ThompsonN.P σ := by
    apply mem_P_of_orderOf_dvd R.coprime_q
    rw [← orderOf_injective R.ι R.ι_injective m, ← hm]
    have : orderOf (R.K * R.ι p * R.K) = orderOf (R.ι p) := by
      have := WardLocal.orderOf_conj' R.K (R.ι p)
      rwa [R.K_inv_eq] at this
    rw [this, orderOf_injective R.ι R.ι_injective p]
    exact orderOf_dvd_of_mem_P hp
  have h1 : R.ι m ∈ (R.P : Subgroup G) ⊓ (MulAut.conj R.K • (R.P : Subgroup G)) := by
    refine Subgroup.mem_inf.mpr ⟨R.ι_mem_P hmP, ?_⟩
    rw [WardLocal.mem_conj_smul_iff, ← hm, R.K_inv_eq,
      show R.K * (R.K * R.ι p * R.K) * R.K = (R.K * R.K) * R.ι p * (R.K * R.K) by group,
      R.K_mul_K, one_mul, mul_one]
    exact hpP
  rw [R.inf_conj_K, Subgroup.mem_bot] at h1
  have h2 : R.K * R.ι p * R.K = 1 := hm.trans h1
  have h3 : R.ι p = 1 := by
    calc R.ι p = R.K * (R.K * R.ι p * R.K) * R.K := by
          rw [show R.K * (R.K * R.ι p * R.K) * R.K = (R.K * R.K) * R.ι p * (R.K * R.K) by group,
            R.K_mul_K, one_mul, mul_one]
      _ = 1 := by rw [h2, mul_one, R.K_mul_K]
  exact R.ι_injective (h3.trans (map_one R.ι).symm)

@[expose] noncomputable def presMap (x : ThompsonN k σ × ThompsonN.P σ) : G :=
  R.ι x.1 * R.K * R.ι x.2

theorem presMap_injective :
    Function.Injective R.presMap := by
  rintro ⟨n, p⟩ ⟨n', p'⟩ h
  simp only [presMap] at h
  have h1 : R.K * R.ι ((p : ThompsonN k σ) * (p' : ThompsonN k σ)⁻¹) * R.K = R.ι (n⁻¹ * n') := by
    rw [map_mul, map_mul, map_inv, map_inv]
    have : R.ι n * R.K * R.ι p * (R.ι p')⁻¹ = R.ι n' * R.K := by rw [h]; group
    calc R.K * (R.ι p * (R.ι p')⁻¹) * R.K
        = (R.ι n)⁻¹ * (R.ι n * R.K * R.ι p * (R.ι p')⁻¹) * R.K := by group
      _ = (R.ι n)⁻¹ * (R.ι n' * R.K) * R.K := by rw [this]
      _ = (R.ι n)⁻¹ * R.ι n' := by rw [mul_assoc, mul_assoc, R.K_mul_K, mul_one]
  have hp1 : (p : ThompsonN k σ) * (p' : ThompsonN k σ)⁻¹ = 1 := by
    apply R.eq_one_of_K_mul_mem
    · exact (ThompsonN.P σ).mul_mem p.2 ((ThompsonN.P σ).inv_mem p'.2)
    · rw [h1]; exact R.ι_mem _
  have hpp : p = p' := Subtype.ext (mul_inv_eq_one.mp hp1)
  subst hpp
  have hnn : R.ι n = R.ι n' := mul_right_cancel (mul_right_cancel h)
  rw [R.ι_injective hnn]

omit [Finite k] in
theorem presMap_not_mem (x : ThompsonN k σ × ThompsonN.P σ) : R.presMap x ∉ R.N := by
  intro h
  apply R.K_not_mem
  have : R.K = (R.ι x.1)⁻¹ * R.presMap x * (R.ι x.2)⁻¹ := by
    simp only [presMap]; group
  rw [this]
  exact R.N.mul_mem (R.N.mul_mem (R.N.inv_mem (R.ι_mem _)) h) (R.N.inv_mem (R.ι_mem _))

theorem range_presMap :
    Set.range R.presMap = (R.N : Set G)ᶜ := by
  have hsub : Set.range R.presMap ⊆ (R.N : Set G)ᶜ := by
    rintro _ ⟨x, rfl⟩; exact R.presMap_not_mem x
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_range_of_injective R.presMap_injective, Set.ncard_compl (R.N : Set G),
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, R.card_N, R.card_G, Nat.card_prod,
    ThompsonN.card, ThompsonN.card_P, R.card_k]
  have h : R.hyp.q ^ 3 * (R.hyp.q ^ 3 + 1) * (R.hyp.q - 1) =
      R.hyp.q ^ 3 * (R.hyp.q - 1) * R.hyp.q ^ 3 + R.hyp.q ^ 3 * (R.hyp.q - 1) := by ring
  rw [h, Nat.add_sub_cancel]

theorem thompsonPresentation :
    ThompsonPresentation R.ι R.N R.K := by
  refine ⟨fun g hg => ?_, fun ν ν' x y z x' y' z' h => ?_⟩
  · have hg' : g ∈ Set.range R.presMap := by rw [R.range_presMap]; exact hg
    obtain ⟨⟨ν, p, hp⟩, rfl⟩ := hg'
    refine ⟨ν, p.α, p.β, p.γ, ?_⟩
    simp only [presMap]
    congr 2
    rw [ThompsonN.eq_of_mem_P hp]
    rfl
  · have hP : ∀ a b c : k, pp σ a b c ∈ ThompsonN.P σ := fun _ _ _ => rfl
    have := R.presMap_injective (a₁ := (ν, ⟨pp σ x y z, hP _ _ _⟩))
      (a₂ := (ν', ⟨pp σ x' y' z', hP _ _ _⟩)) h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    have hx := congrArg ThompsonN.α h2
    have hy := congrArg ThompsonN.β h2
    have hz := congrArg ThompsonN.γ h2
    exact ⟨h1, hx, hy, hz⟩

theorem exists_pres {g : G} (hg : g ∉ R.N) :
    ∃ (ν : ThompsonN k σ) (v : k × k × k), g = R.ι ν * R.K * R.ι (pp σ v.1 v.2.1 v.2.2) := by
  obtain ⟨ν, x, y, z, h⟩ := R.thompsonPresentation.1 g hg
  exact ⟨ν, (x, y, z), h⟩

theorem pres_unique
    {ν ν' : ThompsonN k σ} {v v' : k × k × k}
    (h : R.ι ν * R.K * R.ι (pp σ v.1 v.2.1 v.2.2) = R.ι ν' * R.K * R.ι (pp σ v'.1 v'.2.1 v'.2.2)) :
    ν = ν' ∧ v = v' := by
  obtain ⟨h1, h2, h3, h4⟩ := R.thompsonPresentation.2 _ _ _ _ _ _ _ _ h
  exact ⟨h1, Prod.ext h2 (Prod.ext h3 h4)⟩

end CFSG.Walter.Ree.T2.RType
