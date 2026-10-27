module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem6B
public import CFSG.Quasithin.Background.E2SeventeenSolv
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Aux
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_zpowers_sup_eq_bot_ch626 {P : Subgroup G} (hP : IsPGroup 2 P) {ρ σ : G}
    (hρ : Odd (orderOf ρ)) (hσ : σ * σ = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσP : σ ∉ P)
    (hσN : σ ∈ Subgroup.normalizer (P : Set G)) :
    P ⊓ (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) = ⊥ := by
  have hodd : ∀ c ∈ Subgroup.zpowers ρ, c ∈ P → c = 1 := fun c hc hcP => by
    obtain ⟨k, hk⟩ := hP ⟨c, hcP⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact E2.eq_one_of_odd_orderOf_of_pow_two_pow
      (Odd.of_dvd_nat hρ (orderOf_dvd_of_mem_zpowers hc)) hk'
  have hσN' : Subgroup.zpowers σ ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [E2.conj_eq_inv_of_mem_zpowers hrel hc]
      exact (Subgroup.zpowers ρ).inv_mem hc
    · intro hc
      have h1 := E2.conj_eq_inv_of_mem_zpowers hrel hc
      have e : σ * (σ * c * σ⁻¹) * σ⁻¹ = c := by
        calc σ * (σ * c * σ⁻¹) * σ⁻¹ = (σ * σ) * c * (σ * σ)⁻¹ := by group
          _ = c := by rw [hσ]; group
      rw [e] at h1
      rw [h1]
      exact (Subgroup.zpowers ρ).inv_mem hc
  rw [eq_bot_iff]
  rintro g ⟨hgP, hgS⟩
  rw [Subgroup.mem_bot]
  have hgS' : g ∈ ((Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ : Subgroup G) : Set G) := hgS
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hσN'] at hgS'
  obtain ⟨c, hc, y, hy, rfl⟩ := hgS'
  replace hgP : c * y ∈ P := hgP
  show c * y = 1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hσ2 : σ ^ (2 : ℤ) = 1 := by rw [zpow_two, hσ]
  rw [zpow_eq_zpow_emod k hσ2] at hgP ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero, mul_one] at hgP ⊢
    exact hodd c hc hgP
  · rw [h, zpow_one] at hgP ⊢
    exfalso
    have h1 : σ * (c * σ) * σ⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hσN _).mp hgP
    have e1 : σ * (c * σ) * σ⁻¹ = c⁻¹ * σ := by
      rw [← E2.conj_eq_inv_of_mem_zpowers hrel hc]
      group
    rw [e1] at h1
    have h2 : c * σ * (c⁻¹ * σ)⁻¹ = c ^ 2 ^ 1 := by
      rw [pow_one, pow_two]
      group
    have hc2 : c ^ 2 ^ 1 = 1 := by
      have := P.mul_mem hgP (P.inv_mem h1)
      rw [h2] at this
      exact hodd _ (Subgroup.pow_mem _ hc _) this
    have hc1 : c = 1 := E2.eq_one_of_odd_orderOf_of_pow_two_pow
      (Odd.of_dvd_nat hρ (orderOf_dvd_of_mem_zpowers hc)) hc2
    rw [hc1, one_mul] at hgP
    exact hσP hgP

theorem pCoreOf_le_of_perm_three_ch626 {I D : Subgroup G} (φ : ↥I →* Equiv.Perm (Fin 3))
    (hφ : Function.Surjective φ) (hker : φ.ker = D.subgroupOf I) : pCoreOf 2 I ≤ D := by
  have key : ∀ τ : Equiv.Perm (Fin 3), τ ^ 2 = 1 →
      (∀ σ : Equiv.Perm (Fin 3), (τ * (σ * τ * σ⁻¹)) ^ 2 = 1) → τ = 1 := by decide +kernel
  have hcases : ∀ τ : Equiv.Perm (Fin 3), τ ^ 2 = 1 ∨ τ ^ 3 = 1 := by decide
  have hsq : ∀ z : ↥I, (z : G) ∈ pCoreOf 2 I → φ z ^ 2 = 1 := by
    intro z hz
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 I ⟨z, hz⟩
    have hk' : (z : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hk'' : φ z ^ 2 ^ k = 1 := by
      have hz1 : z ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [← map_pow, hz1, map_one]
    rcases hcases (φ z) with h | h
    · exact h
    · have h1 : orderOf (φ z) ∣ 3 := orderOf_dvd_of_pow_eq_one h
      have hodd : Odd (orderOf (φ z)) := Odd.of_dvd_nat (by decide) h1
      rw [E2.eq_one_of_odd_orderOf_of_pow_two_pow hodd hk'', one_pow]
  intro x hx
  have hxI : x ∈ I := pCoreOf_le 2 I hx
  have hτ := key (φ ⟨x, hxI⟩) (hsq ⟨x, hxI⟩ hx) (fun σ => ?_)
  · have : (⟨x, hxI⟩ : ↥I) ∈ φ.ker := hτ
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  · obtain ⟨y, rfl⟩ := hφ σ
    have hyN : (y : G) ∈ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 I (Subgroup.le_normalizer y.2)
    have hmem : ((⟨x, hxI⟩ * (y * ⟨x, hxI⟩ * y⁻¹) : ↥I) : G) ∈ pCoreOf 2 I := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (pCoreOf 2 I).mul_mem hx ((Subgroup.mem_normalizer_iff.mp hyN x).mp hx)
    have := hsq _ hmem
    simpa [map_mul, map_inv] using this

namespace Pair626

variable {X Y : Subgroup G}

omit [Finite G] in
theorem A_le_normalizer_U :
    Y ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((X ⊓ Subgroup.normalizer (Y : Set G) : Subgroup G) : Set G) :=
  fun _ ha => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨ha.2, Subgroup.le_normalizer (Subgroup.le_normalizer ha.1)⟩

omit [Finite G] in
theorem U_le_normalizer_A :
    X ⊓ Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((Y ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) :=
  fun _ hu => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hu.2, Subgroup.le_normalizer (Subgroup.le_normalizer hu.1)⟩

omit [Finite G] in
theorem U_inf_A :
    (X ⊓ Subgroup.normalizer (Y : Set G)) ⊓ (Y ⊓ Subgroup.normalizer (X : Set G)) = X ⊓ Y :=
  le_antisymm (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    (le_inf B_le_U B_le_A)

omit [Finite G] in
theorem mem_Q {q : G}
    (hq : q ∈ (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))) :
    ∃ u ∈ X ⊓ Subgroup.normalizer (Y : Set G), ∃ a ∈ Y ⊓ Subgroup.normalizer (X : Set G),
      u * a = q := by
  have hq' : q ∈ (((X ⊓ Subgroup.normalizer (Y : Set G)) ⊔
      (Y ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) := hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ A_le_normalizer_U] at hq'
  obtain ⟨u, hu, a, ha, rfl⟩ := hq'
  exact ⟨u, hu, a, ha, rfl⟩

theorem card_Q (p : Pair626 X Y) :
    Nat.card ↥((X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))) =
      32 := by
  have h := card_sup_mul_card_inf_ch62 (A := X ⊓ Subgroup.normalizer (Y : Set G))
    (B := Y ⊓ Subgroup.normalizer (X : Set G)) A_le_normalizer_U
  rw [U_inf_A, p.cardB, p.card_U, p.card_A] at h
  omega

omit [Finite G] in
theorem Q_le_centralizer_B (p : Pair626 X Y) :
    (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G)) ≤
      Subgroup.centralizer ((X ⊓ Y : Subgroup G) : Set G) :=
  sup_le (fun _ hu => Subgroup.mem_centralizer_iff.mpr fun _ hb =>
      B2F.isElemAbelian_comm p.elemX hb.1 hu.1)
    (fun _ ha => Subgroup.mem_centralizer_iff.mpr fun _ hb =>
      B2F.isElemAbelian_comm p.elemY hb.2 ha.1)

omit [Finite G] in
theorem mul_self_mem_B (p : Pair626 X Y) {q : G}
    (hq : q ∈ (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))) :
    q * q ∈ X ⊓ Y := by
  obtain ⟨u, hu, a, ha, rfl⟩ := mem_Q hq
  have hui : u⁻¹ = u := inv_eq_self_ch626 p.elemX hu.1
  have hai : a⁻¹ = a := inv_eq_self_ch626 p.elemY ha.1
  have h1 := comm_mem_B' ha hu
  rw [hui, hai] at h1
  have e : u * a * (u * a) = u * a * u * a := by group
  rw [e]
  exact h1

theorem mem_B_of_mem_center (p : Pair626 X Y) {c : G}
    (hc : c ∈ (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G)))
    (hcomm : ∀ g ∈ (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G)),
      g * c = c * g) : c ∈ X ⊓ Y := by
  obtain ⟨u, hu, a, ha, rfl⟩ := mem_Q hc
  have haU : ∀ u' ∈ X ⊓ Subgroup.normalizer (Y : Set G), a * u' = u' * a := by
    intro u' hu'
    have h1 := hcomm u' (Subgroup.mem_sup_left hu')
    have huu : u' * u = u * u' := B2F.isElemAbelian_comm p.elemX hu'.1 hu.1
    calc a * u' = u⁻¹ * ((u * a) * u') := by group
      _ = u⁻¹ * (u' * (u * a)) := by rw [← h1]
      _ = u⁻¹ * ((u' * u) * a) := by group
      _ = u⁻¹ * ((u * u') * a) := by rw [huu]
      _ = u' * a := by group
  have huA : ∀ a' ∈ Y ⊓ Subgroup.normalizer (X : Set G), u * a' = a' * u := by
    intro a' ha'
    have h1 := hcomm a' (Subgroup.mem_sup_right ha')
    have haa : a * a' = a' * a := B2F.isElemAbelian_comm p.elemY ha.1 ha'.1
    calc u * a' = (u * (a' * a)) * a⁻¹ := by group
      _ = (u * (a * a')) * a⁻¹ := by rw [haa]
      _ = ((u * a) * a') * a⁻¹ := by group
      _ = (a' * (u * a)) * a⁻¹ := by rw [← h1]
      _ = a' * u := by group
  have haB := p.mem_B_of_commute_U ha haU
  have huB : u ∈ X ⊓ Y := by
    have := p.symm.mem_B_of_commute_U hu huA
    rwa [inf_comm] at this
  exact (X ⊓ Y).mul_mem huB haB

theorem isExtraspecialPlus (p : Pair626 X Y) :
    E2.IsExtraspecialPlus 2
      ((X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))) := by
  set Q := (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))
    with hQ
  have hBQ : X ⊓ Y ≤ Q := B_le_U.trans le_sup_left
  have hcen : Subgroup.center ↥Q = (X ⊓ Y).subgroupOf Q := by
    ext c
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact p.mem_B_of_mem_center c.2 (fun g hg => congrArg Subtype.val (h ⟨g, hg⟩))
    · intro hcB g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (p.Q_le_centralizer_B g.2) c hcB).symm
  have hZcard : Nat.card ↥(Subgroup.center ↥Q) = 2 := by
    rw [hcen, ← p.cardB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
  have hsq : ∀ z : ↥Q ⧸ Subgroup.center ↥Q, z ^ 2 = 1 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H g =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hcen, Subgroup.mem_subgroupOf]
    have h1 : ((g ^ 2 : ↥Q) : G) = (g : G) * (g : G) := by simp [pow_two]
    rw [h1]
    exact p.mul_self_mem_B g.2
  have hEA : IsElementaryAbelian 2 (↥Q ⧸ Subgroup.center ↥Q) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
    exact (Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_of_pow_eq_one (hsq g)) a b).eq
  have hnt : Nontrivial (↥Q ⧸ Subgroup.center ↥Q) := by
    have hBU : X ⊓ Y < X ⊓ Subgroup.normalizer (Y : Set G) := lt_of_le_of_ne B_le_U fun h => by
      have h1 : Nat.card ↥(X ⊓ Y) = Nat.card ↥(X ⊓ Subgroup.normalizer (Y : Set G)) := by rw [h]
      rw [p.cardB, p.card_U] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨u, hu, huB⟩ := IsConcreteLE.exists_of_lt hBU
    refine nontrivial_of_ne ((⟨u, Subgroup.mem_sup_left hu⟩ : ↥Q) : ↥Q ⧸ Subgroup.center ↥Q) 1
      fun h => huB ?_
    rw [QuotientGroup.eq_one_iff, hcen, Subgroup.mem_subgroupOf] at h
    exact h
  exact ⟨⟨hZcard, hEA, hnt⟩, p.card_Q.trans (by norm_num), X ⊓ Subgroup.normalizer (Y : Set G),
    le_sup_left, B2F.isElemAbelian_mono inf_le_left p.elemX, p.card_U.trans (by norm_num)⟩

theorem conj_mem_Q (p : Pair626 X Y) {x q : G} (hx : x ∈ X)
    (hq : q ∈ (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))) :
    x * q * x⁻¹ ∈
      (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G)) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := mem_Q hq
  have hxu : x * u = u * x := B2F.isElemAbelian_comm p.elemX hx hu.1
  have h1 := p.comm_mem_U hx ha
  have e : x * (u * a) * x⁻¹ = u * (x * a * x⁻¹ * a⁻¹) * a := by
    calc x * (u * a) * x⁻¹ = (x * u) * a * x⁻¹ := by group
      _ = (u * x) * a * x⁻¹ := by rw [hxu]
      _ = u * (x * a * x⁻¹ * a⁻¹) * a := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
    (Subgroup.mem_sup_left h1)) (Subgroup.mem_sup_right ha)

theorem X_le_normalizer_Q (p : Pair626 X Y) :
    X ≤ Subgroup.normalizer
      (((X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G)) :
        Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨fun hq => p.conj_mem_Q hx hq, fun hq => ?_⟩
  have := p.conj_mem_Q (X.inv_mem hx) hq
  have e : x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q := by group
  rwa [e] at this

theorem sup_le_normalizer_Q (p : Pair626 X Y) :
    X ⊔ Y ≤ Subgroup.normalizer
      (((X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G)) :
        Subgroup G) : Set G) := by
  have hY := p.symm.X_le_normalizer_Q
  rw [sup_comm (Y ⊓ Subgroup.normalizer (X : Set G))] at hY
  exact sup_le p.X_le_normalizer_Q hY

omit [Finite G] in
theorem exists_mem_not_mem_U (p : Pair626 X Y) :
    ∃ v ∈ X, v ∉ X ⊓ Subgroup.normalizer (Y : Set G) := by
  by_contra h
  push Not at h
  have h1 : (X ⊓ Subgroup.normalizer (Y : Set G)).relIndex X = 1 :=
    Subgroup.relIndex_eq_one.mpr h
  rw [p.idxU] at h1
  norm_num at h1

theorem rho_data (p : Pair626 X Y) {v w : G} (hv : v ∈ X)
    (hvU : v ∉ X ⊓ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y)
    (hwA : w ∉ Y ⊓ Subgroup.normalizer (X : Set G)) :
    orderOf ((v * w) ^ 4) = 3 ∧ v * (v * w) ^ 4 * v⁻¹ = ((v * w) ^ 4)⁻¹ ∧
      v * v = 1 ∧ v ≠ 1 ∧
      v ∉ (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))
    with hQ
  have hv2 : v * v = 1 := mul_self_eq_one_ch626 p.elemX hv
  have hw2 : w * w = 1 := mul_self_eq_one_ch626 p.elemY hw
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hr3 := p.pow_three_mem hv hvU hw hwA
  have hr6 : (v * w) ^ 3 * (v * w) ^ 3 = 1 := mul_self_eq_one_ch626 p.elemY hr3.1
  have hQU : Q ≤ Subgroup.normalizer ((X ⊓ Subgroup.normalizer (Y : Set G) : Subgroup G) :
      Set G) := sup_le Subgroup.le_normalizer A_le_normalizer_U
  have hrQ : v * w ∉ Q := by
    intro h
    have h1 := conjSub_eq_of_mem_normalizer' (hQU h)
    rw [p.conjSub_U_eq hv hvU hw hwA] at h1
    have h2 := p.cardB
    rw [← U_inf_A, h1, inf_idem, p.card_U] at h2
    norm_num at h2
  have hr4 : (v * w) ^ 4 = (v * w) ^ 3 * (v * w) := pow_succ _ 3
  have hρQ : (v * w) ^ 4 ∉ Q := by
    intro h
    apply hrQ
    have e : v * w = ((v * w) ^ 3)⁻¹ * (v * w) ^ 4 := by rw [hr4]; group
    rw [e]
    exact Q.mul_mem (Q.inv_mem (Subgroup.mem_sup_right hr3)) h
  have hρ1 : (v * w) ^ 4 ≠ 1 := fun h => hρQ (h ▸ Q.one_mem)
  have hρ3 : ((v * w) ^ 4) ^ 3 = 1 := by
    have e : ((v * w) ^ 4) ^ 3 = ((v * w) ^ 3 * (v * w) ^ 3) * ((v * w) ^ 3 * (v * w) ^ 3) := by
      group
    rw [e, hr6, one_mul]
  have hvr : v * (v * w) * v⁻¹ = (v * w)⁻¹ := by
    rw [mul_inv_rev, hvi, hwi]
    calc v * (v * w) * v = (v * v) * w * v := by group
      _ = w * v := by rw [hv2, one_mul]
  have hAN : Q ≤ Subgroup.normalizer ((Y ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) :
      Set G) := sup_le U_le_normalizer_A Subgroup.le_normalizer
  have hvQ : v ∉ Q := by
    intro h
    apply hvU
    have hA := conjSub_eq_of_mem_normalizer' (hAN h)
    have hle : Y ⊓ Subgroup.normalizer (X : Set G) ≤ conjSub v Y := by
      rw [← hA]
      exact conjSub_mono _ inf_le_left
    exact ⟨hv, mem_normalizer_of_conjSub_eq_ch626 (p.uniqY v hle)⟩
  refine ⟨orderOf_eq_prime hρ3 hρ1, ?_, hv2, fun h => hvU (h ▸ Subgroup.one_mem _), hvQ⟩
  rw [← conj_pow, hvr, inv_pow]

theorem exists_surjective_perm_three (p : Pair626 X Y) :
    ∃ φ : ↥(X ⊔ Y) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
      φ.ker = ((X ⊓ Subgroup.normalizer (Y : Set G)) ⊔
        (Y ⊓ Subgroup.normalizer (X : Set G))).subgroupOf (X ⊔ Y) := by
  set Q := (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))
    with hQ
  obtain ⟨v, hv, hvU⟩ := p.exists_mem_not_mem_U
  obtain ⟨w, hw, hwA⟩ := p.symm.exists_mem_not_mem_U
  obtain ⟨hρ, hvρ, hv2, hv1, hvQ⟩ := p.rho_data hv hvU hw hwA
  obtain ⟨e⟩ := E2.nonempty_zpowers_sup_mulEquiv_perm_three hρ hv2 hv1 hvρ
  have hr3 := p.pow_three_mem hv hvU hw hwA
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 5) (by rw [p.card_Q]; norm_num)
  have hvI : v ∈ X ⊔ Y := Subgroup.mem_sup_left hv
  have hwI : w ∈ X ⊔ Y := Subgroup.mem_sup_right hw
  have hρI : (v * w) ^ 4 ∈ X ⊔ Y := Subgroup.pow_mem _ ((X ⊔ Y).mul_mem hvI hwI) _
  have hN := p.sup_le_normalizer_Q
  have hQI : Q ≤ X ⊔ Y := sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hSI : Subgroup.zpowers ((v * w) ^ 4) ⊔ Subgroup.zpowers v ≤ X ⊔ Y :=
    sup_le (Subgroup.zpowers_le.mpr hρI) (Subgroup.zpowers_le.mpr hvI)
  have hinf := inf_zpowers_sup_eq_bot_ch626 hQ2 (hρ ▸ (by decide : Odd 3)) hv2 hvρ hvQ
    (p.X_le_normalizer_Q hv)
  set S := Subgroup.zpowers ((v * w) ^ 4) ⊔ Subgroup.zpowers v with hS
  have hρS : (v * w) ^ 4 ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hvS : v ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hsup : X ⊔ Y ≤ S ⊔ Q := by
    have hXS : X ≤ S ⊔ Q := by
      intro x hx
      by_cases hxU : x ∈ X ⊓ Subgroup.normalizer (Y : Set G)
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hxU)
      · have h1 := mul_mem_of_relIndex_two_ch626 p.idxU (X.inv_mem hv) hx
          (fun h => hvU (by simpa using (X ⊓ Subgroup.normalizer (Y : Set G)).inv_mem h)) hxU
        have e : x = v * (v⁻¹ * x) := by group
        rw [e]
        exact (S ⊔ Q).mul_mem (Subgroup.mem_sup_left hvS)
          (Subgroup.mem_sup_right (Subgroup.mem_sup_left h1))
    have hwSQ : w ∈ S ⊔ Q := by
      have e : w = v⁻¹ * ((v * w) ^ 4 * ((v * w) ^ 3)⁻¹) := by
        rw [pow_succ' (v * w) 3]
        group
      rw [e]
      exact (S ⊔ Q).mul_mem (Subgroup.mem_sup_left (S.inv_mem hvS))
        ((S ⊔ Q).mul_mem (Subgroup.mem_sup_left hρS)
          (Subgroup.mem_sup_right (Q.inv_mem (Subgroup.mem_sup_right hr3))))
    have hYS : Y ≤ S ⊔ Q := by
      intro y hy
      by_cases hyA : y ∈ Y ⊓ Subgroup.normalizer (X : Set G)
      · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right hyA)
      · have h1 := mul_mem_of_relIndex_two_ch626 p.idxA (Y.inv_mem hw) hy
          (fun h => hwA (by simpa using (Y ⊓ Subgroup.normalizer (X : Set G)).inv_mem h)) hyA
        have e : y = w * (w⁻¹ * y) := by group
        rw [e]
        exact (S ⊔ Q).mul_mem hwSQ (Subgroup.mem_sup_right (Subgroup.mem_sup_right h1))
    exact sup_le hXS hYS
  exact E2.exists_surjective_ker_of_complement hQI hSI hN hsup hinf e

theorem comm_mem_oTwoUpper (p : Pair626 X Y) {v w u : G} (hv : v ∈ X)
    (hvU : v ∉ X ⊓ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y)
    (hwA : w ∉ Y ⊓ Subgroup.normalizer (X : Set G))
    (hu : u ∈ X ⊓ Subgroup.normalizer (Y : Set G)) :
    u * w * u⁻¹ * w⁻¹ ∈ oTwoUpper (X ⊔ Y) := by
  obtain ⟨hρ, -, hv2, -, -⟩ := p.rho_data hv hvU hw hwA
  have hvI : v ∈ X ⊔ Y := Subgroup.mem_sup_left hv
  have hwI : w ∈ X ⊔ Y := Subgroup.mem_sup_right hw
  have huI : u ∈ X ⊔ Y := Subgroup.mem_sup_left hu.1
  have hρI : (v * w) ^ 4 ∈ X ⊔ Y := Subgroup.pow_mem _ ((X ⊔ Y).mul_mem hvI hwI) _
  have hρN : (v * w) ^ 4 ∈ oTwoUpper (X ⊔ Y) :=
    mem_oTwoUpper_of_odd hρI (hρ ▸ (by decide : Odd 3))
  have hIN : X ⊔ Y ≤ Subgroup.normalizer (oTwoUpper (X ⊔ Y) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoUpper _)
  have h1 : u * (v * w) ^ 4 * u⁻¹ ∈ oTwoUpper (X ⊔ Y) :=
    (Subgroup.mem_normalizer_iff.mp (hIN huI) _).mp hρN
  have h2 := (oTwoUpper (X ⊔ Y)).mul_mem h1 ((oTwoUpper (X ⊔ Y)).inv_mem hρN)
  have h3 := (Subgroup.mem_normalizer_iff.mp (hIN hvI) _).mp h2
  have hr3A := p.pow_three_mem hv hvU hw hwA
  have hruA := p.conj_mem_A hv hvU hw hwA hu
  have hc : (v * w) ^ 3 * ((v * w) * u * (v * w)⁻¹) = ((v * w) * u * (v * w)⁻¹) * (v * w) ^ 3 :=
    B2F.isElemAbelian_comm p.elemY hr3A.1 hruA.1
  have hρu : (v * w) ^ 4 * u * ((v * w) ^ 4)⁻¹ = (v * w) * u * (v * w)⁻¹ := by
    rw [pow_succ (v * w) 3]
    calc (v * w) ^ 3 * (v * w) * u * ((v * w) ^ 3 * (v * w))⁻¹ =
          (v * w) ^ 3 * ((v * w) * u * (v * w)⁻¹) * ((v * w) ^ 3)⁻¹ := by group
      _ = ((v * w) * u * (v * w)⁻¹) * (v * w) ^ 3 * ((v * w) ^ 3)⁻¹ := by rw [hc]
      _ = (v * w) * u * (v * w)⁻¹ := by group
  have hvu : v * u = u * v := B2F.isElemAbelian_comm p.elemX hv hu.1
  have e : v * (u * (v * w) ^ 4 * u⁻¹ * ((v * w) ^ 4)⁻¹) * v⁻¹ = u * w * u⁻¹ * w⁻¹ := by
    have e1 : u * (v * w) ^ 4 * u⁻¹ * ((v * w) ^ 4)⁻¹ =
        u * ((v * w) ^ 4 * u * ((v * w) ^ 4)⁻¹)⁻¹ := by group
    rw [e1, hρu]
    calc v * (u * ((v * w) * u * (v * w)⁻¹)⁻¹) * v⁻¹ =
          (v * u) * v * w * u⁻¹ * w⁻¹ * (v⁻¹ * v⁻¹) := by group
      _ = (u * v) * v * w * u⁻¹ * w⁻¹ * (v⁻¹ * v⁻¹) := by rw [hvu]
      _ = u * (v * v) * w * u⁻¹ * w⁻¹ * (v * v)⁻¹ := by group
      _ = u * w * u⁻¹ * w⁻¹ := by rw [hv2]; group
  rwa [e] at h3

theorem pCoreOf_le_oTwoUpper (p : Pair626 X Y) : pCoreOf 2 (X ⊔ Y) ≤ oTwoUpper (X ⊔ Y) := by
  set Q := (X ⊓ Subgroup.normalizer (Y : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (X : Set G))
    with hQ
  set N := oTwoUpper (X ⊔ Y) with hNdef
  obtain ⟨φ, hφ, hker⟩ := p.exists_surjective_perm_three
  refine (pCoreOf_le_of_perm_three_ch626 φ hφ hker).trans ?_
  obtain ⟨v, hv, hvU⟩ := p.exists_mem_not_mem_U
  obtain ⟨w, hw, hwA⟩ := p.symm.exists_mem_not_mem_U
  have hYX : oTwoUpper (Y ⊔ X) = N := by rw [sup_comm]
  have hwu : ∀ u ∈ X ⊓ Subgroup.normalizer (Y : Set G), w * u * w⁻¹ * u⁻¹ ∈ N := by
    intro u hu
    have := N.inv_mem (p.comm_mem_oTwoUpper hv hvU hw hwA hu)
    have e : (u * w * u⁻¹ * w⁻¹)⁻¹ = w * u * w⁻¹ * u⁻¹ := by group
    rwa [e] at this
  have hva : ∀ a ∈ Y ⊓ Subgroup.normalizer (X : Set G), v * a * v⁻¹ * a⁻¹ ∈ N := by
    intro a ha
    have := N.inv_mem (hYX ▸ p.symm.comm_mem_oTwoUpper hw hwA hv hvU ha)
    have e : (a * v * a⁻¹ * v⁻¹)⁻¹ = v * a * v⁻¹ * a⁻¹ := by group
    rwa [e] at this
  have hBN : X ⊓ Y ≤ N := by
    obtain ⟨a₁, ha₁, ha₁B⟩ : ∃ a₁ ∈ Y ⊓ Subgroup.normalizer (X : Set G), a₁ ∉ X ⊓ Y := by
      by_contra h
      push Not at h
      have := Subgroup.card_le_of_le (show Y ⊓ Subgroup.normalizer (X : Set G) ≤ X ⊓ Y from h)
      rw [p.card_A, p.cardB] at this
      omega
    have hu₁ := p.comm_mem_U hv ha₁
    have hu₁B := p.comm_not_mem_B hv hvU ha₁ ha₁B
    obtain ⟨a₀, ha₀, hne⟩ : ∃ a₀ ∈ Y ⊓ Subgroup.normalizer (X : Set G),
        (v * a₁ * v⁻¹ * a₁⁻¹) * a₀ ≠ a₀ * (v * a₁ * v⁻¹ * a₁⁻¹) := by
      by_contra h
      push Not at h
      apply hu₁B
      have := p.symm.mem_B_of_commute_U hu₁ h
      rwa [inf_comm] at this
    obtain ⟨b, hb, hba⟩ := p.symm.exists_comm_comm_eq hw hwA hv hvU ha₀
    have hn₀ := hwu _ (p.comm_mem_U hv ha₀)
    rw [hba] at hn₀
    set u₁ := v * a₁ * v⁻¹ * a₁⁻¹ with hu₁def
    have hc := N.mul_mem (N.mul_mem (N.mul_mem (hva a₁ ha₁) hn₀) (N.inv_mem (hva a₁ ha₁)))
      (N.inv_mem hn₀)
    have hbu : b * u₁ = u₁ * b := B2F.isElemAbelian_comm p.elemX hb.2 hu₁.1
    have hcB := comm_mem_B' ha₀ hu₁
    have hbc : b * (u₁ * a₀ * u₁⁻¹ * a₀⁻¹) = (u₁ * a₀ * u₁⁻¹ * a₀⁻¹) * b :=
      B2F.isElemAbelian_comm p.elemX hb.2 hcB.1
    have e : u₁ * (b * a₀) * u₁⁻¹ * (b * a₀)⁻¹ = u₁ * a₀ * u₁⁻¹ * a₀⁻¹ := by
      calc u₁ * (b * a₀) * u₁⁻¹ * (b * a₀)⁻¹ = (u₁ * b) * a₀ * u₁⁻¹ * a₀⁻¹ * b⁻¹ := by group
        _ = (b * u₁) * a₀ * u₁⁻¹ * a₀⁻¹ * b⁻¹ := by rw [hbu]
        _ = b * (u₁ * a₀ * u₁⁻¹ * a₀⁻¹) * b⁻¹ := by group
        _ = (u₁ * a₀ * u₁⁻¹ * a₀⁻¹) * b * b⁻¹ := by rw [hbc]
        _ = u₁ * a₀ * u₁⁻¹ * a₀⁻¹ := by group
    rw [e] at hc
    have hc1 : u₁ * a₀ * u₁⁻¹ * a₀⁻¹ ≠ 1 := by
      intro h1
      apply hne
      calc u₁ * a₀ = u₁ * a₀ * u₁⁻¹ * a₀⁻¹ * (a₀ * u₁) := by group
        _ = a₀ * u₁ := by rw [h1, one_mul]
    have hzp : Subgroup.zpowers (u₁ * a₀ * u₁⁻¹ * a₀⁻¹) = X ⊓ Y := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcB)
      rw [p.cardB]
      have : Subgroup.zpowers (u₁ * a₀ * u₁⁻¹ * a₀⁻¹) ≠ ⊥ := by
        rwa [Ne, Subgroup.zpowers_eq_bot]
      exact (Subgroup.one_lt_card_iff_ne_bot _).mpr this
    rw [← hzp]
    exact Subgroup.zpowers_le.mpr hc
  have hUN : X ⊓ Subgroup.normalizer (Y : Set G) ≤ N := by
    intro u hu
    obtain ⟨b, hb, hbu⟩ := p.exists_comm_comm_eq hv hvU hw hwA hu
    have h1 := hva _ (p.symm.comm_mem_U hw hu)
    rw [hbu] at h1
    have e : u = b⁻¹ * (b * u) := by group
    rw [e]
    exact N.mul_mem (N.inv_mem (hBN hb)) h1
  have hAN : Y ⊓ Subgroup.normalizer (X : Set G) ≤ N := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := p.symm.exists_comm_comm_eq hw hwA hv hvU ha
    have h1 := hwu _ (p.comm_mem_U hv ha)
    rw [hba] at h1
    have e : a = b⁻¹ * (b * a) := by group
    rw [e]
    exact N.mul_mem (N.inv_mem (hBN (by rwa [inf_comm] at hb))) h1
  exact sup_le hUN hAN

end Pair626

end CFSG.Quasithin.H13
