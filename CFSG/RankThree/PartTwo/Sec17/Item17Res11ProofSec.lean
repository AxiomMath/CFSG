module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofFrob
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res11

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_inf {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH x, hK x]

theorem mem_of_pow_two_pow_eq_one [Finite G] {R : Subgroup G} {x : G} {m j : ℕ} (hm : Odd m)
    (h2 : x ^ 2 ^ j = 1) (hxm : x ^ m ∈ R) : x ∈ R := by
  have hdvd : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime m (orderOf x) :=
    Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm))
  by_cases h1 : orderOf x = 1
  · rw [orderOf_eq_one_iff.mp h1]
    exact one_mem _
  obtain ⟨t, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (lt_of_le_of_ne (orderOf_pos x) (Ne.symm h1))
  have e : x = (x ^ m) ^ t := by
    rw [← pow_mul, ← pow_mod_orderOf, ht.2, pow_one]
  rw [e]
  exact pow_mem hxm t

theorem conj_mem_of_commutator_le {P R : Subgroup G} (hPP : ⁅P, P⁆ ≤ R) {x r : G} (hx : x ∈ P)
    (hrP : r ∈ P) (hr : r ∈ R) : x * r * x⁻¹ ∈ R := by
  have h := hPP (Subgroup.commutator_mem_commutator hx hrP)
  rw [commutatorElement_def] at h
  rw [show x * r * x⁻¹ = x * r * x⁻¹ * r⁻¹ * r by group]
  exact mul_mem h hr

@[expose] def secCen (X P R : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ X ∧ y ∈ Subgroup.normalizer (P : Set G) ∧
    y ∈ Subgroup.normalizer (R : Set G) ∧ ∀ x ∈ P, y * x * y⁻¹ * x⁻¹ ∈ R}
  one_mem' := ⟨one_mem _, one_mem _, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haX, haP, haR, ha⟩ ⟨hbX, hbP, hbR, hb⟩
    refine ⟨mul_mem haX hbX, mul_mem haP hbP, mul_mem haR hbR, fun x hx => ?_⟩
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem haR (hb x hx)) (ha x hx)
  inv_mem' := by
    rintro a ⟨haX, haP, haR, ha⟩
    refine ⟨inv_mem haX, inv_mem haP, inv_mem haR, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a⁻¹⁻¹ ∈ P := conj_mem (inv_mem haP) hx
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ =
        (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (ha _ hx')

theorem le_normalizer_secCen [Finite G] {X P R : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXR : X ≤ Subgroup.normalizer (R : Set G)) :
    X ≤ Subgroup.normalizer ((secCen X P R : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨hyX, hyP, hyR, hy'⟩ := hy
  refine ⟨mul_mem (mul_mem hg hyX) (inv_mem hg), mul_mem (mul_mem (hXP hg) hyP)
    (inv_mem (hXP hg)), mul_mem (mul_mem (hXR hg) hyR) (inv_mem (hXR hg)), fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ P := conj_mem (inv_mem (hXP hg)) hx
  have e : g * y * g⁻¹ * x * (g * y * g⁻¹)⁻¹ * x⁻¹ =
      g * (y * (g⁻¹ * x * g⁻¹⁻¹) * y⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
  rw [e]
  exact conj_mem (hXR hg) (hy' _ hx')

theorem le_of_odd_section [Finite G] {M T U P R X : Subgroup G} {c : G} {m : ℕ} (hm : Odd m)
    (hRP : R ≤ P) (hPP : ⁅P, P⁆ ≤ R) (hodd : ∀ x ∈ P, x ^ m ∈ R) (hP3 : ¬ 3 ∣ Nat.card P)
    (hRM : R ≤ M) (hc3 : c ^ 3 = 1) (hcM : c ∈ M)
    (hCc : Subgroup.centralizer ({c} : Set G) ≤ M) (hcX : c ∈ X) (hUX : U ≤ X)
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hUT : U ≤ T) (hT2 : IsPGroup 2 T) (hMT : M ≤ Subgroup.normalizer (T : Set G))
    (hU2 : ∀ u ∈ U, u * u = 1) (hUM : U ≤ M) (hcU : c ∈ Subgroup.normalizer (U : Set G))
    (hUab : ∀ u ∈ U, ∀ w ∈ U, u * w = w * u)
    (hUc : ∀ u ∈ U, u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) = 1)
    (hC : ∀ C : Subgroup G, C ≤ X → X ≤ Subgroup.normalizer (C : Set G) → U ≤ C → c ∈ C) :
    P ≤ M := by
  have hRD : R ≤ P ⊓ M := le_inf hRP hRM
  have hDP : P ⊓ M ≤ P := inf_le_left
  have hD3 : ¬ 3 ∣ Nat.card (P ⊓ M : Subgroup G) := fun h =>
    hP3 (h.trans (Subgroup.card_dvd_of_le hDP))
  have hR3 : ¬ 3 ∣ Nat.card R := fun h => hP3 (h.trans (Subgroup.card_dvd_of_le hRP))
  have hcP : c ∈ Subgroup.normalizer (P : Set G) := hXP hcX
  have hcD : c ∈ Subgroup.normalizer ((P ⊓ M : Subgroup G) : Set G) :=
    mem_normalizer_inf hcP (Subgroup.le_normalizer hcM)
  have hc3' : c * c * c = 1 := by rw [← pow_three', hc3]
  have hfpf : ∀ x ∈ P, x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) ∈ P ⊓ M := by
    intro x hx
    have hxc : c * x * c⁻¹ ∈ P := conj_mem hcP hx
    have hxcc : c * (c * x * c⁻¹) * c⁻¹ ∈ P := conj_mem hcP hxc
    have hzP : x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) ∈ P :=
      mul_mem (mul_mem hx hxc) hxcc
    have e1 : c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = x := by
      rw [show c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ by group,
        hc3']
      group
    have hcomm : (x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹))⁻¹ *
        (c * (x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)) * c⁻¹) ∈ P ⊓ M := by
      rw [show c * (x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)) * c⁻¹ =
          (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) * (c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹) by
          group, e1]
      have e3 : (x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹))⁻¹ *
          ((c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) * x) =
          ⁅((c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹))⁻¹, x⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e3]
      exact hRD (hPP (Subgroup.commutator_mem_commutator (inv_mem (mul_mem hxc hxcc))
        (inv_mem hx)))
    obtain ⟨z', hz', hcz'⟩ := exists_commute_of_coset hc3 hcD hD3 hcomm
    set z := x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) with hz
    have hz'P : z' ∈ P := by
      rw [show z' = z * (z⁻¹ * z') by group]
      exact mul_mem hzP (hDP hz')
    have hz'M : z' ∈ M := hCc (Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc z' * c = (c * z' * c⁻¹) * c := by rw [hcz']
        _ = c * z' := by group))
    rw [show z = z' * (z⁻¹ * z')⁻¹ by group]
    exact mul_mem ⟨hz'P, hz'M⟩ (inv_mem hz')
  have hfrob : ∀ u ∈ U, ∀ x ∈ P, u * x * u⁻¹ * x⁻¹ ∈ P ⊓ M := by
    intro u hu x hx
    have huX := hUX hu
    exact conj_mul_inv_mem_of_fpf (hPP.trans hRD) hm (fun y hy => hRD (hodd y hy)) hc3 hcP hcD
      (hXP huX) (mem_normalizer_inf (hXP huX) (Subgroup.le_normalizer (hUM hu)))
      (hU2 u hu) (hUab u hu _ (conj_mem hcU hu)) (hUc u hu) hfpf hx
  have hUR : ∀ u ∈ U, ∀ x ∈ P, u * x * u⁻¹ * x⁻¹ ∈ R := by
    intro u hu x hx
    have hdD := hfrob u hu x hx
    have hu2 : u * u = 1 := hU2 u hu
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have e1 : u * (u * x * u⁻¹ * x⁻¹) * u⁻¹ = (u * x * u⁻¹ * x⁻¹)⁻¹ := by
      have e : (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u⁻¹ * x⁻¹ * u⁻¹ := by
        rw [show (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ by group, huinv]
      rw [e, show u * (u * x * u⁻¹ * x⁻¹) * u⁻¹ = (u * u) * x * u⁻¹ * x⁻¹ * u⁻¹ by group, hu2,
        one_mul]
    have hV : u * (u * x * u⁻¹ * x⁻¹) * u⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹ ∈ T := by
      have h1 : (u * x * u⁻¹ * x⁻¹) * u⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹ ∈ T :=
        conj_mem (hMT hdD.2) (inv_mem (hUT hu))
      rw [show u * (u * x * u⁻¹ * x⁻¹) * u⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹ =
        u * ((u * x * u⁻¹ * x⁻¹) * u⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹) by group]
      exact mul_mem (hUT hu) h1
    rw [e1] at hV
    obtain ⟨j, hj⟩ := hT2 ⟨_, hV⟩
    have h : ((u * x * u⁻¹ * x⁻¹)⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h2 : (u * x * u⁻¹ * x⁻¹) ^ 2 ^ (j + 1) = 1 := by
      generalize u * x * u⁻¹ * x⁻¹ = d at h ⊢
      have e : (d⁻¹ * d⁻¹) ^ 2 ^ j = (d ^ 2 ^ (j + 1))⁻¹ := by
        rw [show d⁻¹ * d⁻¹ = (d ^ 2)⁻¹ by group, inv_pow, ← pow_mul, pow_succ, mul_comm]
      rw [← inv_eq_one, ← e, h]
    exact mem_of_pow_two_pow_eq_one hm h2 (hodd _ (hDP hdD))
  have hUC : U ≤ secCen X P R := fun u hu =>
    ⟨hUX hu, hXP (hUX hu), hXR (hUX hu), hUR u hu⟩
  have hcC := hC (secCen X P R) (fun y hy => hy.1) (le_normalizer_secCen hXP hXR) hUC
  intro x hx
  have h1 : x⁻¹ * (c * x * c⁻¹) ∈ R := by
    have h := hcC.2.2.2 x hx
    rw [show x⁻¹ * (c * x * c⁻¹) = x⁻¹ * (c * x * c⁻¹ * x⁻¹) * x⁻¹⁻¹ by group]
    exact conj_mem_of_commutator_le hPP (inv_mem hx) (mul_mem (conj_mem hcP hx) (inv_mem hx)) h
  obtain ⟨x', hx', hcx'⟩ := exists_commute_of_coset hc3 (hXR hcX) hR3 h1
  have hx'M : x' ∈ M := hCc (Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc x' * c = (c * x' * c⁻¹) * c := by rw [hcx']
      _ = c * x' := by group))
  rw [show x = x' * (x⁻¹ * x')⁻¹ by group]
  exact mul_mem hx'M (hRM (inv_mem hx'))

theorem exists_sylow_normalized [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {E Y : Subgroup G} (hE : IsPGroup p E) (hY : ¬ p ∣ Nat.card Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ T : Sylow q ↥Y,
      E ≤ Subgroup.normalizer (((T : Subgroup ↥Y).map Y.subtype : Subgroup G) : Set G) := by
  let φ : E →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hEY)
  let : MulDistribMulAction E Y := MulDistribMulAction.compHom Y φ
  have hcard : ¬ p ∣ Nat.card (Sylow q Y) := fun h => hY (h.trans
    ((Sylow.card_dvd_index (Classical.arbitrary (Sylow q Y))).trans (Subgroup.index_dvd_card _)))
  obtain ⟨S, hS⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q Y) hcard
  have hSinv : ∀ e : E, ∀ s ∈ (S : Subgroup Y), e • s ∈ (S : Subgroup Y) := by
    intro e s hs
    have hmem : e • s ∈ ((e • S : Sylow q Y) : Subgroup Y) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨s, hs, rfl⟩
    rwa [hS e] at hmem
  refine ⟨S, fun e he => ?_⟩
  have hconj : ∀ e ∈ E, ∀ t ∈ (S : Subgroup Y).map Y.subtype,
      e * t * e⁻¹ ∈ (S : Subgroup Y).map Y.subtype := by
    rintro e he _ ⟨s, hs, rfl⟩
    exact ⟨_, hSinv ⟨e, he⟩ s hs, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨hconj e he t, fun ht => ?_⟩
  have := hconj e⁻¹ (E.inv_mem he) _ ht
  simpa [mul_assoc] using this

theorem le_of_two_section [Finite G] {A M P R : Subgroup G} {a : ℕ} (hRP : R ≤ P)
    (hPR : P ≤ Subgroup.normalizer (R : Set G)) (h2 : ∀ x ∈ P, x ^ 2 ^ a ∈ R) (hRM : R ≤ M)
    (hA : IsPGroup 3 A) (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hP3 : ¬ 3 ∣ Nat.card P)
    (hS : ∀ S : Subgroup G, S ≤ P → IsPGroup 2 S → A ≤ Subgroup.normalizer (S : Set G) →
      S ≤ M) : P ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := exists_sylow_normalized (q := 2) hA hP3 hAP
  have hSP : (T : Subgroup ↥P).map P.subtype ≤ P := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 ((T : Subgroup ↥P).map P.subtype) := T.isPGroup'.map P.subtype
  have hSM := hS _ hSP hS2 hT
  have hN : (R.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mpr hPR
  have hQ2 : IsPGroup 2 (↥P ⧸ R.subgroupOf P) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact h2 x x.2
  have hsurj := QuotientGroup.mk'_surjective (R.subgroupOf P)
  have htop : ((T.mapSurjective hsurj : Sylow 2 (↥P ⧸ R.subgroupOf P)) :
      Subgroup (↥P ⧸ R.subgroupOf P)) = ⊤ :=
    ((T.mapSurjective hsurj).is_maximal' (hQ2.to_subgroup ⊤) le_top).symm
  intro x hx
  have hmem : QuotientGroup.mk' (R.subgroupOf P) ⟨x, hx⟩ ∈
      ((T.mapSurjective hsurj : Sylow 2 (↥P ⧸ R.subgroupOf P)) :
        Subgroup (↥P ⧸ R.subgroupOf P)) := by
    rw [htop]
    trivial
  rw [Sylow.coe_mapSurjective] at hmem
  obtain ⟨s, hsT, hs⟩ := hmem
  have hsx : ((s : G))⁻¹ * x ∈ R := by
    have h := QuotientGroup.eq.mp hs
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hsM : (s : G) ∈ M := hSM ⟨s, hsT, rfl⟩
  rw [show x = (s : G) * ((s : G)⁻¹ * x) by group]
  exact mul_mem hsM (hRM hsx)

theorem le_of_isSolvable [Finite G] {O M Γ : Subgroup G} {a m : ℕ} (hO : Group.IsSolvable O)
    (hΓO : Γ ≤ Subgroup.normalizer (O : Set G)) (hcard : Nat.card O = 2 ^ a * m)
    (hstepA : ∀ R P : Subgroup G, R ≤ P → P ≤ O → Γ ≤ Subgroup.normalizer (R : Set G) →
      Γ ≤ Subgroup.normalizer (P : Set G) → ⁅P, P⁆ ≤ R → (∀ x ∈ P, x ^ m ∈ R) → R ≤ M →
        P ≤ M)
    (hstepB : ∀ R P : Subgroup G, R ≤ P → P ≤ O → Γ ≤ Subgroup.normalizer (R : Set G) →
      Γ ≤ Subgroup.normalizer (P : Set G) → ⁅P, P⁆ ≤ R → (∀ x ∈ P, x ^ 2 ^ a ∈ R) → R ≤ M →
        P ≤ M) :
    O ≤ M := by
  set ds : ℕ → Subgroup G := fun n => (derivedSeries ↥O n).map O.subtype with hds
  have hds0 : ds 0 = O := by
    simp only [hds, derivedSeries_zero]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hdsS : ∀ n, ds (n + 1) = ⁅ds n, ds n⁆ := fun n => by
    simp only [hds, derivedSeries_succ, Subgroup.map_commutator]
  have hdsO : ∀ n, ds n ≤ O := fun n => Subgroup.map_subtype_le _
  have hdsΓ : ∀ n, Γ ≤ Subgroup.normalizer (ds n : Set G) := by
    intro n
    induction n with
    | zero => rw [hds0]; exact hΓO
    | succ n ih => rw [hdsS]; exact le_normalizer_commutator_of ih ih
  obtain ⟨N, hN⟩ := hO.solvable
  have hdsN : ds N = ⊥ := by
    simp only [hds, hN, Subgroup.map_bot]
  have step : ∀ n, ds (n + 1) ≤ M → ds n ≤ M := by
    intro n hRM
    have hPP : ⁅ds n, ds n⁆ ≤ ds (n + 1) := (hdsS n).ge
    have hRP : ds (n + 1) ≤ ds n := by
      rw [hdsS]
      exact Subgroup.commutator_le_self _
    let Po : Subgroup G :=
      { carrier := {x | x ∈ ds n ∧ x ^ m ∈ ds (n + 1)}
        one_mem' := ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
        mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1,
          mul_pow_mem_of_commutator_le hPP hx.1 hy.1 m hx.2 hy.2⟩
        inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow]; exact inv_mem hx.2⟩ }
    have hRPo : ds (n + 1) ≤ Po := fun r hr => ⟨hRP hr, pow_mem hr m⟩
    have hPoP : Po ≤ ds n := fun x hx => hx.1
    have hΓPo : Γ ≤ Subgroup.normalizer (Po : Set G) := fun g hg =>
      Subgroup.mem_normalizer_fintype fun x hx =>
        ⟨conj_mem (hdsΓ n hg) hx.1, by rw [conj_pow]; exact conj_mem (hdsΓ (n + 1) hg) hx.2⟩
    have hPoM : Po ≤ M := hstepA _ Po hRPo (hPoP.trans (hdsO n)) (hdsΓ (n + 1)) hΓPo
      ((Subgroup.commutator_mono hPoP hPoP).trans hPP) (fun x hx => hx.2) hRM
    refine hstepB Po (ds n) hPoP (hdsO n) hΓPo (hdsΓ n) (hPP.trans hRPo) (fun x hx => ?_) hPoM
    refine ⟨pow_mem hx _, ?_⟩
    have hxO : x ∈ O := hdsO n hx
    have h1 : (⟨x, hxO⟩ : ↥O) ^ Nat.card O = 1 := pow_card_eq_one'
    have h2 : x ^ Nat.card O = 1 := by
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← pow_mul, ← hcard, h2]
    exact one_mem _
  have key : ∀ k, ds (N - k) ≤ M := by
    intro k
    induction k with
    | zero => rw [Nat.sub_zero, hdsN]; exact bot_le
    | succ k ih =>
      by_cases hk : k < N
      · have e : N - k = N - (k + 1) + 1 := by omega
        rw [e] at ih
        exact step _ ih
      · rw [show N - (k + 1) = N - k by omega]
        exact ih
  have := key N
  rwa [Nat.sub_self, hds0] at this

end CFSG.RankThree.PartTwo.Sec17.Proof17Res11
