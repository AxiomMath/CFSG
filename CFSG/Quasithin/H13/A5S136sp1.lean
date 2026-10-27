module

public import CFSG.Quasithin.H13.A5S136sz1
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13.A5.SpComp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G] {T K : Subgroup G}

theorem mem_of_inner (hsyl : IsSylowTwoOf (T ⊓ K) K)
    (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) (hT : IsPGroup 2 T) {s : G} (hs : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (K : Set G)) {k : G} (hkK : k ∈ K)
    (hk : ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹) : k ∈ T ⊓ K := by
  have hk' : ∀ x ∈ K, s⁻¹ * x * s = k⁻¹ * x * k := by
    intro x hx
    have := hk _ (SzPair.conj_inv_mem_of_mem_normalizer hsN hx)
    rw [show s * (s⁻¹ * x * s) * s⁻¹ = x by group] at this
    calc s⁻¹ * x * s = k⁻¹ * (k * (s⁻¹ * x * s) * k⁻¹) * k := by group
      _ = k⁻¹ * x * k := by rw [← this]
  have hkN : k ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hk x hx.2]
      exact ⟨T.mul_mem (T.mul_mem hs hx.1) (T.inv_mem hs),
        SzPair.conj_mem_of_mem_normalizer hsN hx.2⟩
    · intro hx
      have hxK : k * x * k⁻¹ ∈ K := hx.2
      have e := hk' _ hxK
      rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group] at e
      rw [← e]
      exact ⟨T.mul_mem (T.mul_mem (T.inv_mem hs) hx.1) hs,
        SzPair.conj_inv_mem_of_mem_normalizer hsN hxK⟩
  obtain ⟨m, hm⟩ := hT ⟨s, hs⟩
  have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hkpow : ∀ j : ℕ, ∀ x ∈ K, s ^ j * x * (s ^ j)⁻¹ = k ^ j * x * (k ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      calc s ^ (j + 1) * x * (s ^ (j + 1))⁻¹ = s ^ j * (s * x * s⁻¹) * (s ^ j)⁻¹ := by
            rw [pow_succ]; group
        _ = k ^ j * (s * x * s⁻¹) * (k ^ j)⁻¹ :=
            ih _ (SzPair.conj_mem_of_mem_normalizer hsN hx)
        _ = k ^ j * (k * x * k⁻¹) * (k ^ j)⁻¹ := by rw [hk x hx]
        _ = k ^ (j + 1) * x * (k ^ (j + 1))⁻¹ := by rw [pow_succ]; group
  have hk2 : k ^ 2 ^ m = 1 := by
    refine hZ _ (K.pow_mem hkK _) fun y hy => ?_
    have := hkpow (2 ^ m) y hy
    rw [hsm, one_mul, inv_one, mul_one] at this
    calc k ^ 2 ^ m * y = k ^ 2 ^ m * y * (k ^ 2 ^ m)⁻¹ * k ^ 2 ^ m := by group
      _ = y * k ^ 2 ^ m := by rw [← this]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkp : IsPGroup 2 (Subgroup.zpowers k) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨m, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk2, one_zpow]
  have hP : IsPGroup 2 ↥((T ⊓ K) ⊔ Subgroup.zpowers k) :=
    hsyl.2.1.to_sup_of_normal_left' hkp ((Subgroup.zpowers_le).2 hkN)
  have heq := hsyl.eq_of_le le_sup_left (sup_le inf_le_right ((Subgroup.zpowers_le).2 hkK)) hP
  have hmem : k ∈ (T ⊓ K) ⊔ Subgroup.zpowers k := Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
  rwa [heq] at hmem

omit [Finite G] in
theorem omegaOneCenter_le (P : Subgroup G) : omegaOneCenterOf P ≤ P :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1.1

omit [Finite G] in
theorem omegaOneCenter_comm (P : Subgroup G) {u : G} (hu : u ∈ omegaOneCenterOf P) {y : G}
    (hy : y ∈ P) : u * y = y * u := by
  have hle : omegaOneCenterOf P ≤ Subgroup.centralizer ({y} : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx.1.2 y hy).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)

omit [Finite G] in
theorem omegaOneCenter_elemAb (P : Subgroup G) : IsElemAbelian 2 (omegaOneCenterOf P) := by
  refine ⟨⟨⟨fun a b => Subtype.ext
    (omegaOneCenter_comm P a.2 (omegaOneCenter_le P b.2))⟩⟩, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy hx2 hy2 =>
    have hc : x * y = y * x := omegaOneCenter_comm P hx (omegaOneCenter_le P hy)
    rw [(Commute.mul_pow hc 2), hx2, hy2, one_mul]
  | inv x hx hx2 => rw [inv_pow, hx2, inv_one]

omit [Finite G] in
theorem conj_mem_omegaOneCenter {P : Subgroup G} {g u : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hu : u ∈ omegaOneCenterOf P) :
    g * u * g⁻¹ ∈ omegaOneCenterOf P := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨SzPair.conj_mem_of_mem_normalizer hg hx.1.1, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' := SzPair.conj_inv_mem_of_mem_normalizer hg hy
      have e := Subgroup.mem_centralizer_iff.mp hx.1.2 _ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [e]
        _ = g * x * g⁻¹ * y := by group
    · rw [show (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group, hx.2]
      group
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

theorem mem_normalizer_baum_of_le (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (K : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ K) K) (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1)
    (hinn : ∀ s ∈ T, (∀ u ∈ omegaOneCenterOf (T ⊓ K), s * u * s⁻¹ = u) →
      ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (omegaOneCenterOf (T ⊓ K) : Set G))
    {b : G} (hbK : b ∈ K) (hbN : b ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    b ∈ Subgroup.normalizer (baum T : Set G) := by
  set U := omegaOneCenterOf (T ⊓ K) with hU
  have hUT : U ≤ T := (omegaOneCenter_le _).trans inf_le_left
  rw [baum_eq_baum_centralizer (omegaOneCenter_elemAb _) hUT hJ]
  refine normalizer_le_normalizer_baum _ ?_
  have key : ∀ g ∈ K, g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
      ∀ c ∈ T ⊓ Subgroup.centralizer (U : Set G),
        g * c * g⁻¹ ∈ T ⊓ Subgroup.centralizer (U : Set G) := by
    intro g hgK hgN c hc
    obtain ⟨hcT, hcU⟩ := Subgroup.mem_inf.mp hc
    have hcU' : ∀ u ∈ U, c * u * c⁻¹ = u := by
      intro u hu
      rw [← Subgroup.mem_centralizer_iff.mp hcU u hu]
      group
    obtain ⟨k, hkK, hk⟩ := hinn c hcT hcU'
    have hkP := mem_of_inner hsyl hZ hT hcT (hTN hcT) hkK hk
    set d := k⁻¹ * c with hd
    have hdK : d ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have e1 := hk x hx
      calc x * d = k⁻¹ * (k * x * k⁻¹) * c := by rw [hd]; group
        _ = k⁻¹ * (c * x * c⁻¹) * c := by rw [e1]
        _ = d * x := by rw [hd]; group
    have hgd : g * d = d * g := Subgroup.mem_centralizer_iff.mp hdK g hgK
    have hceq : g * c * g⁻¹ = (g * k * g⁻¹) * d := by
      have hc' : c = k * d := by rw [hd]; group
      rw [hc']
      calc g * (k * d) * g⁻¹ = (g * k * g⁻¹) * (g * d * g⁻¹) := by group
        _ = (g * k * g⁻¹) * d := by rw [hgd]; group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hceq]
      have hgk : g * k * g⁻¹ ∈ T ⊓ K := SzPair.conj_mem_of_mem_normalizer hgN hkP
      have hdT : d ∈ T := by
        rw [hd]
        exact T.mul_mem (T.inv_mem hkP.1) hcT
      exact T.mul_mem hgk.1 hdT
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : g⁻¹ * u * g ∈ U := by
        have := conj_mem_omegaOneCenter (Subgroup.inv_mem _ hgN) hu
        rwa [inv_inv] at this
      have e := Subgroup.mem_centralizer_iff.mp hcU _ hu'
      calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by rw [e]
        _ = g * c * g⁻¹ * u := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key b hbK hbN c
  · intro hc
    have := key b⁻¹ (K.inv_mem hbK) (Subgroup.inv_mem _ hbN) _ hc
    simpa [mul_assoc] using this

end CFSG.Quasithin.H13.A5.SpComp
