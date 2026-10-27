module

public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace SzF53B2

section Pure

theorem normal_eq_top_of_odd_index_perm_five {N : Subgroup (Equiv.Perm (Fin 5))} [N.Normal]
    (hodd : ¬ 2 ∣ N.index) : N = ⊤ := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA : (alternatingGroup (Fin 5)).index = 2 := alternatingGroup.index_eq_two
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by rw [Nat.card_perm]; simp [Nat.factorial]
  have hdvd : N.index ∣ 120 := by
    rw [← h120]
    exact Subgroup.index_dvd_card N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5)))
    with h | h
  · exfalso
    have hdis : Disjoint N (alternatingGroup (Fin 5)) := Subgroup.subgroupOf_eq_bot.mp h
    have hinf : N ⊓ alternatingGroup (Fin 5) = ⊥ := disjoint_iff.mp hdis
    have h1 : (N ⊓ alternatingGroup (Fin 5)).index ≤ N.index * (alternatingGroup (Fin 5)).index :=
      Subgroup.index_inf_le
    rw [hinf, Subgroup.index_bot, h120, hA] at h1
    have h2 : 60 ≤ N.index := by omega
    obtain ⟨k, hk⟩ := hdvd
    have hk' : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have : N.index * 3 ≤ N.index * k := Nat.mul_le_mul_left _ hk3
      omega
    interval_cases k <;> omega
  · have hle : alternatingGroup (Fin 5) ≤ N := Subgroup.subgroupOf_eq_top.mp h
    have h1 : N.index ∣ (alternatingGroup (Fin 5)).index := Subgroup.index_dvd_of_le hle
    rw [hA] at h1
    have : N.index = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · exact absurd ⟨1, by omega⟩ hodd
    exact Subgroup.index_eq_one.mp this

variable {G : Type} [Group G]

theorem eq_of_normal_odd_index_perm_five {X C : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (hCX : C ≤ X)
    (hCn : X ≤ Subgroup.normalizer (C : Set G)) (hQC : pCoreOf 2 X ≤ C)
    (hodd : ¬ 2 ∣ C.relIndex X) : C = X := by
  obtain ⟨ι⟩ := hq
  let π : ↥X →* Equiv.Perm (Fin 5) :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))
  have hπ : Function.Surjective π := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = CFSG.Open.pCore 2 ↥X := by
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have : (C.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCn
  have hkerle : π.ker ≤ C.subgroupOf X := by
    rw [hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hQC ⟨x, hx, rfl⟩
  have : ((C.subgroupOf X).map π).Normal := Subgroup.Normal.map inferInstance π hπ
  have hcomap : ((C.subgroupOf X).map π).comap π = C.subgroupOf X := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.mpr hkerle
  have hidx : ((C.subgroupOf X).map π).index = C.relIndex X := by
    rw [← Subgroup.index_comap_of_surjective _ hπ, hcomap]
    rfl
  have htop := normal_eq_top_of_odd_index_perm_five (N := (C.subgroupOf X).map π) (by rwa [hidx])
  have h1 : C.relIndex X = 1 := by rw [← hidx, htop, Subgroup.index_top]
  exact le_antisymm hCX (Subgroup.relIndex_eq_one.mp h1)

theorem card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm]; simp [Nat.factorial]

theorem card_le_four_of_exp_two_five {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 120)
    (x : X) (hx2 : x ^ 2 ≠ 1) (hx4 : x ^ 4 = 1)
    {E : Subgroup X} (hE2 : ∀ a ∈ E, a ^ 2 = 1) : Nat.card E ≤ 4 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 E := by
    intro y
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hE2 y y.2
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card E ∣ 120 := hcard ▸ E.card_subgroup_dvd_card
  rw [hn] at hdvd hlt
  have hn3 : n = 3 := by
    have h1 : 3 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> simp at hlt
    have h2' : n ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 h
      have : 16 ∣ 120 := dvd_trans (by simpa using this) hdvd
      omega
    omega
  subst hn3
  have hidx : E.index = 15 := by
    have := E.card_mul_index
    rw [hn, hcard] at this
    omega
  let SE : Sylow 2 X := hpg.toSylow (by rw [hidx]; decide)
  have hxpg : IsPGroup 2 (Subgroup.zpowers x) := by
    have hod : orderOf x ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one hx4
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hod
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  obtain ⟨S', hS'⟩ := hxpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' SE
  have hmem : g * x * g⁻¹ ∈ E := by
    have hxS : x ∈ (S' : Subgroup X) := hS' (Subgroup.mem_zpowers x)
    have h3 : g * x * g⁻¹ ∈ ((g • S' : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.conj_inv_apply, mul_assoc] using hxS
    rw [hg] at h3
    exact h3
  have := hE2 _ hmem
  apply hx2
  have e : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
  rw [e] at this
  have : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
  rw [this, ‹g * x ^ 2 * g⁻¹ = 1›]
  group

def x5 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

theorem x5_sq_ne : x5 ^ 2 ≠ 1 := by decide
theorem x5_four : x5 ^ 4 = 1 := by decide

theorem relIndex_pCoreOf_le_four_five {X A : Subgroup G}
    (hX : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (hAX : A ≤ X)
    (hsq : ∀ a ∈ A, a ^ 2 ∈ pCoreOf 2 X) : (pCoreOf 2 X ⊓ A).relIndex A ≤ 4 := by
  obtain ⟨ι⟩ := hX
  let f : ↥A →* OTwoQuot X :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)).comp (Subgroup.inclusion hAX)
  have hker : f.ker = (pCoreOf 2 X).subgroupOf A := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) (Subgroup.inclusion hAX e) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hye⟩
      have : y = Subgroup.inclusion hAX e := Subtype.ext hye
      rwa [this] at hy
  have hidx : (pCoreOf 2 X).relIndex A = Nat.card f.range := by
    rw [← Subgroup.index_ker f, hker]
    rfl
  have hsq' : ∀ a ∈ f.range.map ι.toMonoidHom, a ^ 2 = 1 := by
    rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    show ι (f e) ^ 2 = 1
    have hmem : ((e ^ 2 : ↥A) : G) ∈ pCoreOf 2 X := by simpa using hsq e e.2
    have hker1 : e ^ 2 ∈ f.ker := by
      rw [hker]
      exact hmem
    have hf : f (e ^ 2) = 1 := hker1
    rw [← map_pow ι, ← map_pow f, hf, map_one]
  have hc := card_le_four_of_exp_two_five (X := Equiv.Perm (Fin 5)) card_perm_five x5 x5_sq_ne
    x5_four hsq'
  rw [Subgroup.card_map_of_injective ι.injective] at hc
  have h1 : (pCoreOf 2 X ⊓ A).relIndex A = (pCoreOf 2 X).relIndex A := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.inf_subgroupOf_right]
  rw [h1, hidx]
  exact hc

end Pure

end SzF53B2

end CFSG.Quasithin
