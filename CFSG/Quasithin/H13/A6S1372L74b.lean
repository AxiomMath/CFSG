module

public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6L74

variable {M : Type} [Group M] [Finite M]

theorem eq_bot_of_nilpotent {C N : Subgroup M} (hNC : N ≤ C)
    (hCN : C ≤ Subgroup.normalizer (N : Set M)) (hnil : Group.IsNilpotent N)
    (hp : ∀ p : ℕ, p.Prime → pCoreOf p C = ⊥) : N = ⊥ := by
  set N' : Subgroup ↥C := N.subgroupOf C with hN'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mpr hCN
  have hN'nil : Group.IsNilpotent ↥N' :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  have h1 := CFSG.normal_nilpotent_le_sup_pCore hN'n hN'nil
  have h2 : ∀ q : (Nat.card ↥C).primeFactors.attach, CFSG.pCore q.1.1 ↥C = ⊥ := by
    intro q
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have h3 := hp q.1.1 hq
    unfold pCoreOf at h3
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h3
  have h4 : N' = ⊥ := by
    rw [eq_bot_iff]
    refine h1.trans (iSup_le fun q => ?_)
    rw [h2 q]
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hNC hx⟩ : ↥C) ∈ N' := hx
  rw [h4, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hx'

theorem exists_component_of_pCoreOf {C : Subgroup M} (hp : ∀ p : ℕ, p.Prime → pCoreOf p C = ⊥)
    (hC : C ≠ ⊥) : ∃ K, IsComponentOf K C := by
  by_contra hno
  push Not at hno
  have hF : quasithinGenFitting C = ⊥ := by
    rw [eq_bot_iff]
    refine sup_le (sSup_le fun N hN => ?_) (sSup_le fun K hK => absurd hK (hno K))
    obtain ⟨hNC, hNn, hnil⟩ := hN
    have hCN : C ≤ Subgroup.normalizer (N : Set M) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mp hNn
    rw [eq_bot_of_nilpotent hNC hCN hnil hp]
  have h := centralizer_quasithinGenFitting_le C
  rw [hF] at h
  apply hC
  rw [eq_bot_iff]
  intro x hx
  refine h ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]

theorem exists_comp_or_odd {X C : Subgroup M} (hCX : C ≤ X)
    (hXC : X ≤ Subgroup.normalizer (C : Set M))
    (hO2 : ∀ P : Subgroup M, P ≤ X → X ≤ Subgroup.normalizer (P : Set M) → IsPGroup 2 P → P = ⊥)
    (hC : C ≠ ⊥) :
    (∃ K, IsComponentOf K C) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ N : Subgroup M, N ≤ C ∧
        X ≤ Subgroup.normalizer (N : Set M) ∧ N ≠ ⊥ ∧ IsPGroup p N ∧
        ∀ N' : Subgroup M, N' ≤ N → X ≤ Subgroup.normalizer (N' : Set M) → N' = ⊥ ∨ N' = N := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ pCoreOf p C ≠ ⊥
  · right
    obtain ⟨p, hp, hp2, hne⟩ := h
    have : Fact p.Prime := ⟨hp⟩
    have hPX : X ≤ Subgroup.normalizer (pCoreOf p C : Set M) :=
      hXC.trans (normalizer_le_normalizer_pCoreOf p C)
    obtain ⟨N, ⟨hNP, hXN, hN1⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
      (fun N : Subgroup M => N ≤ pCoreOf p C ∧ X ≤ Subgroup.normalizer (N : Set M) ∧ N ≠ ⊥)
      ⟨pCoreOf p C, le_rfl, hPX, hne⟩
    refine ⟨p, hp, hp2, N, hNP.trans (pCoreOf_le p C), hXN, hN1,
      (pCoreOf_isPGroup p C).to_le hNP, fun N' hN'N hXN' => ?_⟩
    by_cases h1 : N' = ⊥
    · exact Or.inl h1
    · exact Or.inr (le_antisymm hN'N (hmin ⟨hN'N.trans hNP, hXN', h1⟩ hN'N))
  · left
    push Not at h
    refine exists_component_of_pCoreOf (fun p hp => ?_) hC
    by_cases hp2 : p = 2
    · subst hp2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact hO2 _ ((pCoreOf_le 2 C).trans hCX)
        (hXC.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
    · exact h p hp hp2

theorem minimal_isElemAbelian {X N : Subgroup M} {p : ℕ} [hp : Fact p.Prime] (hN : N ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (N : Set M)) (hNp : IsPGroup p N)
    (hmin : ∀ N' : Subgroup M, N' ≤ N → X ≤ Subgroup.normalizer (N' : Set M) →
      N' = ⊥ ∨ N' = N) :
    (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ ∀ a ∈ N, a ^ p = 1 := by
  have hZX : X ≤ Subgroup.normalizer
      ((N ⊓ Subgroup.centralizer (N : Set M) : Subgroup M) : Set M) := fun x hx =>
    F7.mem_normalizer_inf (hXN hx) (InternalSec.le_normalizer_centralizer hXN hx)
  have hNnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hZnt : Nontrivial ↥(Subgroup.center ↥N) := hNp.center_nontrivial
  have hZ1 : (N ⊓ Subgroup.centralizer (N : Set M) : Subgroup M) ≠ ⊥ := by
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥N))
    intro h
    apply hz1
    have hzN : ((z : ↥N) : M) ∈ N ⊓ Subgroup.centralizer (N : Set M) := by
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [h, Subgroup.mem_bot] at hzN
    exact Subtype.ext (Subtype.ext hzN)
  have hZ : (N ⊓ Subgroup.centralizer (N : Set M) : Subgroup M) = N :=
    (hmin _ inf_le_left hZX).resolve_left hZ1
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ N ⊓ Subgroup.centralizer (N : Set M) := hZ.symm ▸ hb
    exact Subgroup.mem_centralizer_iff.mp hb'.2 a ha
  refine ⟨hcomm, ?_⟩
  set Ω : Subgroup M :=
    { carrier := {a | a ∈ N ∧ a ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hcomm a ha.1 b hb.1) p), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨N.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ } with hΩ
  have hΩX : X ≤ Subgroup.normalizer (Ω : Set M) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨haN, hap⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hXN hx) a).mp haN, by rw [conj_pow, hap]; group⟩
    · rintro ⟨haN, hap⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hXN hx) a).mpr haN, ?_⟩
      have h1 : (x * a ^ p * x⁻¹) = 1 := by rw [← conj_pow, hap]
      calc a ^ p = x⁻¹ * (x * a ^ p * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
  have hΩ1 : Ω ≠ ⊥ := by
    obtain ⟨n, hn0, hn⟩ := hNp.nontrivial_iff_card.mp hNnt
    have hdvd : p ∣ Nat.card ↥N := by
      rw [hn]
      exact dvd_pow_self p hn0.ne'
    obtain ⟨⟨a, haN⟩, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hdvd
    intro h
    have hmem : a ∈ Ω := ⟨haN, by
      have := pow_orderOf_eq_one (⟨a, haN⟩ : ↥N)
      rw [ha] at this
      exact congrArg Subtype.val this⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : orderOf (⟨a, haN⟩ : ↥N) = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hmem
    rw [ha] at h1
    exact hp.out.one_lt.ne' h1
  have hΩN : Ω = N := (hmin Ω (fun a ha => ha.1) hΩX).resolve_left hΩ1
  intro a ha
  have ha' : a ∈ Ω := hΩN.symm ▸ ha
  exact ha'.2

end A6L74

end CFSG.Quasithin.H13.A6
