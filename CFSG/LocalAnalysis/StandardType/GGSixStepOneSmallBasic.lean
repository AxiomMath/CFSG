module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompPCore
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section Perfect

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem ggEq_bot_of_isPGroup_of_perfect {q : ℕ} [Fact q.Prime] {K : Subgroup Γ}
    (hq : IsPGroup q K) (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  have : Group.IsNilpotent ↥K := hq.isNilpotent
  have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hK]
  have hder : ∀ k : ℕ, (derivedSeries (↥K) k : Subgroup ↥K) = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, htop]
  obtain ⟨k, hk⟩ := (Group.isSolvable_def ↥K).mp inferInstance
  rw [hder k] at hk
  rw [eq_bot_iff]
  intro g hg
  have : (⟨g, hg⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
  rw [hk, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

theorem ggNot_isPGroup_of_isQuasisimple {q : ℕ} [Fact q.Prime] {K : Subgroup Γ}
    (hK : CFSG.Assembly.IsQuasisimple ↥K) (hq : IsPGroup q K) : False := by
  have hKK := commutator_self_eq_of_isQuasisimple hK
  apply commutator_ne_bot_of_isQuasisimple hK
  rw [hKK]
  exact ggEq_bot_of_isPGroup_of_perfect hq hKK

theorem ggCommutator_eq_bot_of_isComponentOf {q : ℕ} [Fact q.Prime] {K N X : Subgroup Γ}
    (hK : IsComponentOf K X) (hNX : N ≤ X) (hKN : K ≤ Subgroup.normalizer (N : Set Γ))
    (hN : IsPGroup q N) : ⁅K, N⁆ = ⊥ := by
  have hYX : K ⊔ N ≤ X := sup_le hK.1 hNX
  have hKY : IsComponentOf K (K ⊔ N) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK le_sup_left hYX
  have hYN : K ⊔ N ≤ Subgroup.normalizer (N : Set Γ) := sup_le hKN Subgroup.le_normalizer
  have hNn : (N.subgroupOf (K ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hYN
  have hNs : IsSubnormal N (K ⊔ N) := IsSubnormal.step le_sup_right hNn (IsSubnormal.refl _)
  rcases isComponentOf_le_or_commutator_eq_bot hKY hNs with h | h
  · exact (ggNot_isPGroup_of_isQuasisimple hK.2.2 (hN.to_le h)).elim
  · exact h

end Perfect

section Coprime

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggIsElementaryAbelian {p : ℕ} {D : Subgroup G} (hD : IsElemAbelian p D) :
    CFSG.IsElementaryAbelian p ↥D :=
  { toIsMulCommutative := hD.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun d =>
      Subtype.ext (by simpa using hD.2 d d.2) }

theorem ggExists_invariant_two_subgroup {p : ℕ} [Fact p.Prime] {D X : Subgroup G}
    (hD : IsElemAbelian p D) (hDX : D ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬ p ∣ Nat.card X) (h2 : 2 ∣ Nat.card X) :
    ∃ T : Subgroup G, T ≤ X ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ D ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian p ↥D := ggIsElementaryAbelian hD
  let : MulDistribMulAction ↥D ↥X := MulDistribMulAction.compHom ↥X (Subgroup.inclusion hDX)
  obtain ⟨S, hS⟩ := CFSG.SolvableHall.exists_invariant_sylow (A := ↥D) (H := ↥X) hX 2
  set T : Subgroup G := (S : Subgroup X).map X.subtype with hT
  have hconj : ∀ d ∈ D, ∀ t ∈ T, d * t * d⁻¹ ∈ T := by
    rintro d hd _ ⟨s, hs, rfl⟩
    exact ⟨_, hS ⟨d, hd⟩ s hs, rfl⟩
  refine ⟨T, Subgroup.map_subtype_le _, ?_, S.isPGroup'.map X.subtype, ?_⟩
  · intro h
    have hS1 : (S : Subgroup X) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ Subtype.coe_injective).mp h
    have := S.not_dvd_index
    rw [hS1, Subgroup.index_bot] at this
    exact this h2
  · intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨hconj d hd t, fun ht => ?_⟩
    have := hconj d⁻¹ (D.inv_mem hd) _ ht
    simpa [mul_assoc] using this

omit [Finite G] in
theorem ggMem_normalizer_inf_of {V W : Subgroup G} {g : G}
    (hV : g ∈ Subgroup.normalizer (V : Set G)) (hW : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer ((V ⊓ W : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp hV h) (Subgroup.mem_normalizer_iff.mp hW h)

theorem ggLe_centralizer_of_generation {p : ℕ} [Fact p.Prime] {D Q S : Subgroup G}
    (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) (hQ : ¬ p ∣ Nat.card Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hS : ∀ d ∈ D, d ≠ 1 →
      S ≤ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G)) :
    S ≤ Subgroup.centralizer (Q : Set G) := by
  have : CFSG.IsElementaryAbelian p ↥D := ggIsElementaryAbelian hD
  let : MulDistribMulAction ↥D ↥Q := MulDistribMulAction.compHom ↥Q (Subgroup.inclusion hDQ)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥D) (H := ↥Q)
    (le_of_eq hDc.symm) hQ
  have hC : (⊤ : Subgroup ↥Q) ≤ (Subgroup.centralizer (S : Set G)).subgroupOf Q := by
    rw [← hgen]
    refine iSup₂_le fun a ha => ?_
    intro y hy
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a y).1 hy
    have hc : (a : G) * y * (a : G)⁻¹ = y := congrArg Subtype.val hfix
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hyC : (y : G) ∈ Q ⊓ Subgroup.centralizer {(a : G)} := by
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * a = (a : G) * y * (a : G)⁻¹ * a := by rw [hc]
        _ = a * y := by rw [inv_mul_cancel_right]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((Subgroup.mem_centralizer_iff.mp (hS a a.2 ha1 hs)) y hyC).symm
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have := hC (Subgroup.mem_top (⟨q, hq⟩ : ↥Q))
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at this
  exact (this s hs).symm

theorem ggCommutator_eq_bot_of_odd {J V W : Subgroup G} (hJJ : ⁅J, J⁆ = J)
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hJW : J ≤ Subgroup.normalizer (W : Set G))
    (hV : IsPGroup 2 V) (hodd : Odd (Nat.card (⁅J, W⁆ : Subgroup G))) (hle : ⁅J, V⁆ ≤ W) :
    ⁅J, V⁆ = ⊥ := by
  have hJU : J ≤ Subgroup.normalizer ((V ⊓ W : Subgroup G) : Set G) :=
    fun j hj => ggMem_normalizer_inf_of (hJV hj) (hJW hj)
  have hJUc : ⁅J, V ⊓ W⁆ = ⊥ := by
    have h1 : ⁅J, V ⊓ W⁆ ≤ V ⊓ W := Subgroup.le_normalizer_iff_commutator_le_right.mp hJU
    have h2 : ⁅J, V ⊓ W⁆ ≤ ⁅J, W⁆ := Subgroup.commutator_mono le_rfl inf_le_right
    obtain ⟨k, hk⟩ := (hV.to_le (h1.trans inf_le_left)).exists_card_eq
    have hdvd : Nat.card (⁅J, V ⊓ W⁆ : Subgroup G) ∣ Nat.card (⁅J, W⁆ : Subgroup G) :=
      Subgroup.card_dvd_of_le h2
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  have hJVU : ⁅J, V⁆ ≤ V ⊓ W := le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hJV) hle
  have h1 : ⁅⁅J, V⁆, J⁆ = ⊥ := by
    have h := Subgroup.commutator_mono (le_refl J) hJVU
    rw [hJUc] at h
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.mp h
  have h2 : ⁅⁅V, J⁆, J⁆ = ⊥ := by rw [Subgroup.commutator_comm V J]; exact h1
  have h3 : ⁅⁅J, J⁆, V⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hJJ] at h3

omit [Finite G] in
theorem ggExists_centralizer_mul {p : ℕ} [Fact p.Prime] {A A₀ : Subgroup G} {x : G}
    (hA₀A : A₀ ≤ A) (hxA₀ : x ∈ Subgroup.normalizer (A₀ : Set G)) (hxp : x ^ p = 1)
    (hcop : ¬ p ∣ Nat.card A₀) (hc : ⁅A, Subgroup.zpowers x⁆ ≤ A₀) {a : G} (ha : a ∈ A) :
    ∃ c ∈ A ⊓ Subgroup.centralizer {x}, c⁻¹ * a ∈ A₀ := by
  have hP : IsPGroup p (Subgroup.zpowers x) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hxp, one_zpow, Subgroup.coe_one]
  have hPA₀ : Subgroup.zpowers x ≤ Subgroup.normalizer (A₀ : Set G) :=
    Subgroup.zpowers_le.mpr hxA₀
  have hmem : ∀ g ∈ Subgroup.zpowers x, ∀ w ∈ A₀, a⁻¹ * (g * (a * w) * g⁻¹) ∈ A₀ := by
    intro g hg w hw
    have h1 : a⁻¹ * g * a * g⁻¹ ∈ A₀ := by
      have := hc (Subgroup.commutator_mem_commutator (A.inv_mem ha) hg)
      rwa [commutatorElement_def, inv_inv] at this
    have h2 : g * w * g⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.mp (hPA₀ hg) w).mp hw
    have he : a⁻¹ * (g * (a * w) * g⁻¹) = (a⁻¹ * g * a * g⁻¹) * (g * w * g⁻¹) := by group
    rw [he]
    exact A₀.mul_mem h1 h2
  let act : MulAction ↥(Subgroup.zpowers x) ↥A₀ :=
    { smul := fun g w => ⟨a⁻¹ * ((g : G) * (a * w) * (g : G)⁻¹), hmem g g.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        change a⁻¹ * (((1 : ↥(Subgroup.zpowers x)) : G) * (a * w) *
          ((1 : ↥(Subgroup.zpowers x)) : G)⁻¹) = w
        simp)
      mul_smul := fun g h w => Subtype.ext (by
        change a⁻¹ * (((g * h : ↥(Subgroup.zpowers x)) : G) * (a * w) *
            ((g * h : ↥(Subgroup.zpowers x)) : G)⁻¹) =
          a⁻¹ * ((g : G) * (a * (a⁻¹ * ((h : G) * (a * w) * (h : G)⁻¹))) * (g : G)⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨w, hw⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card ↥A₀ hcop
  have hfix := (MulAction.mem_fixedPoints.mp hw) ⟨x, Subgroup.mem_zpowers x⟩
  have hfix' : a⁻¹ * (x * (a * w) * x⁻¹) = w := congrArg Subtype.val hfix
  have hxc : x * (a * w) * x⁻¹ = a * w := by
    calc x * (a * w) * x⁻¹ = a * (a⁻¹ * (x * (a * w) * x⁻¹)) := by group
      _ = a * w := by rw [hfix']
  refine ⟨a * w, Subgroup.mem_inf.mpr ⟨A.mul_mem ha (hA₀A w.2), ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * w * x = x * (a * w) * x⁻¹ * x := by rw [hxc]
      _ = x * (a * w) := by group
  · have he : (a * (w : G))⁻¹ * a = (w : G)⁻¹ := by group
    rw [he]
    exact A₀.inv_mem w.2

end Coprime

end CFSG.StandardType
