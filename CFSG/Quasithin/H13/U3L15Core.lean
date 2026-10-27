module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.SteinbergCBIrreducibleTI
public import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.BlueprintB2Reduced
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem isKleinFour_of_card_four' {S : Type*} [Group S] (hc : Nat.card S = 4)
    (hsq : ∀ s : S, s * s = 1) : IsKleinFour S := by
  refine ⟨hc, ?_⟩
  have hpow : ∀ s : S, s ^ 2 = 1 := fun s => by rw [pow_two]; exact hsq s
  have hdvd : Monoid.exponent S ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have : Subsingleton S := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_unique (α := S)
    omega
  · exact h2

theorem pow_mem_mul_of_normalizes' {L : Subgroup G} {l t : G} (hl : l ∈ L)
    (ht : t ∈ normalizer (L : Set G)) (n : ℕ) : ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', he⟩ := ih
    have htn : t ^ n ∈ normalizer (L : Set G) := pow_mem ht n
    refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' ((mem_normalizer_iff.1 htn l).1 hl), ?_⟩
    rw [pow_succ, he]
    group

theorem mem_of_pow_two_pow_mem {K : Subgroup G} {x : G} {k m : ℕ} (hk : x ^ 2 ^ k ∈ K)
    (hm : Odd m) (hxm : x ^ m = 1) : x ∈ K := by
  have hcop : (2 ^ k).Coprime (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxm)
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm))
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hc, ← pow_mul]
  rw [pow_mul]
  exact K.pow_mem hk c

theorem oTwoRes_sup_le' [Finite G] {A Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ normalizer (A : Set G)) : oTwoRes (A ⊔ Q) ≤ A := by
  have hmul : ((A ⊔ Q : Subgroup G) : Set G) = (A : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨hy, m, hm, hym⟩
  obtain ⟨a, ha, q, hq, rfl⟩ : y ∈ (A : Set G) * (Q : Set G) := by rw [← hmul]; exact hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨q, hq⟩
  have hq2 : q ^ 2 ^ k = 1 := by
    rw [← Subgroup.orderOf_coe] at hk
    rw [← hk]
    exact pow_orderOf_eq_one q
  obtain ⟨a', ha', he⟩ := pow_mem_mul_of_normalizes' ha (hQA hq) (2 ^ k)
  have h1 : (a * q) ^ 2 ^ k ∈ A := by rw [he, hq2, mul_one]; exact ha'
  exact mem_of_pow_two_pow_mem h1 hm hym

theorem oTwoRes_mono' {X Y : Subgroup G} (h : X ≤ Y) : oTwoRes X ≤ oTwoRes Y := by
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  exact Subgroup.subset_closure ⟨h hx, m, hm, hxm⟩

theorem commutatorElement_mul_center {H : Type*} [Group H] (a b c : H) (hc : c ∈ center H) :
    ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have hc' := Subgroup.mem_center_iff.mp hc
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_assoc a c b, ← hc' b]
  group

theorem eq_top_of_sup_center_eq_top' {H : Type*} [Group H] (hH : commutator H = ⊤)
    {M : Subgroup H} (h : M ⊔ Subgroup.center H = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← hH, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨m', hm', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  have e1 : ⁅m * z, m' * z'⁆ = ⁅m, m'⁆ := by
    rw [commutatorElement_mul_center _ _ _ hz, ← commutatorElement_inv,
      commutatorElement_mul_center _ _ _ hz', commutatorElement_inv]
  rw [e1, commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

theorem exists_two_pow_eq_one [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) {g : G}
    (hg : g ∈ P) : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨g, hg⟩
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe] at hk
  rw [← hk]
  exact pow_orderOf_eq_one g

theorem isPGroup_two_of_forall' [Finite G] {K : Subgroup G}
    (h : ∀ c ∈ K, ∃ k : ℕ, c ^ 2 ^ k = 1) : IsPGroup 2 K := by
  intro c
  obtain ⟨k, hk⟩ := h c c.2
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simpa using hk

theorem perm3_sq_or_cube (π : Equiv.Perm (Fin 3)) : π ^ 2 = 1 ∨ π ^ 3 = 1 := by
  revert π
  decide

theorem perm3_cube_of_odd {π : Equiv.Perm (Fin 3)} {m : ℕ} (hm : Odd m) (h : π ^ m = 1) :
    π ^ 3 = 1 := by
  rcases perm3_sq_or_cube π with h2 | h3
  · have hcop : Nat.Coprime (orderOf π) m :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2) (Nat.coprime_two_left.2 hm)
    have h1 : orderOf π = 1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h)
    rw [orderOf_eq_one_iff.1 h1, one_pow]
  · exact h3

theorem perm3_sq_of_two_pow {π : Equiv.Perm (Fin 3)} {k : ℕ} (h : π ^ 2 ^ k = 1) : π ^ 2 = 1 := by
  rcases perm3_sq_or_cube π with h2 | h3
  · exact h2
  · have hcop : Nat.Coprime (orderOf π) (2 ^ k) :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3)
        (Nat.Coprime.pow_right k (by norm_num))
    have h1 : orderOf π = 1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h)
    rw [orderOf_eq_one_iff.1 h1, one_pow]

theorem perm3_conj_inv {π τ : Equiv.Perm (Fin 3)} (hπ : π ^ 3 = 1) (hτ : τ ^ 2 = 1)
    (hτ1 : τ ≠ 1) : τ * π⁻¹ * τ⁻¹ = π := by
  revert π τ
  decide

theorem perm3_gen {σ τ : Equiv.Perm (Fin 3)} (hσ : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτ : τ ^ 2 = 1)
    (hτ1 : τ ≠ 1) (π : Equiv.Perm (Fin 3)) :
    ∃ (i : Fin 3) (j : Fin 2), π = σ ^ (i : ℕ) * τ ^ (j : ℕ) := by
  revert σ τ π
  decide +kernel

theorem perm3_comm_ne {ρ σ : Equiv.Perm (Fin 3)} (hρ : ρ ^ 2 = 1) (hρ1 : ρ ≠ 1)
    (hσ : σ ^ 3 = 1) (hσ1 : σ ≠ 1) : (ρ * (σ * ρ * σ⁻¹)) ^ 2 ≠ 1 := by
  revert ρ σ
  decide +kernel

section Psi

variable {W : Subgroup G} [IsKleinFour ↥W]

@[expose] noncomputable def psiV2 (W : Subgroup G) [IsKleinFour ↥W] :
    normalizer (W : Set G) →* Equiv.Perm (Fin 3) :=
  (kleinFourAutomorphismEquivSymmetricThree ↥W).toMonoidHom.comp (conjAct W)

theorem psiV2_eq_one_iff {g : normalizer (W : Set G)} :
    psiV2 W g = 1 ↔ (g : G) ∈ centralizer (W : Set G) := by
  rw [← A1b.conjAct_eq_one_iff]
  unfold psiV2
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

end Psi

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [mem_inf, mem_inf]
  exact and_congr (hA x) (hB x)

theorem mem_normalizer_centralizer {W : Subgroup G} {g : G} (hg : g ∈ normalizer (W : Set G)) :
    g ∈ normalizer (centralizer (W : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (W : Set G), ∀ c ∈ centralizer (W : Set G),
      g * c * g⁻¹ ∈ centralizer (W : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : g⁻¹ * w * g ∈ W := by
      have := (mem_normalizer_iff.1 (inv_mem hg) w).1 hw
      simpa using this
    have := hc _ hw'
    calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * w := by group
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact key g hg c
  · intro h
    have := key g⁻¹ (inv_mem hg) _ h
    simpa [mul_assoc] using this

theorem mem_reducedAggregate' [Finite G] {E : Subgroup G} {v : G}
    (hv : v ∈ reducedAggregate E) :
    v ∈ pCoreOf 2 E ∧ (∀ k ∈ pCoreOf 2 E, k * v = v * k) ∧ v ^ 2 = 1 := by
  obtain ⟨r, hr, rfl⟩ := hv
  obtain ⟨-, -, hRc⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥E) 2
  obtain ⟨h1, h2, h3⟩ := BlueprintB2.mem_centerTorsion_iff.1 (hRc hr)
  have hc : CFSG.inSubgroup (CFSG.pCore 2) E = pCoreOf 2 E := by
    rw [CFSG.inSubgroup, CFSG.Open.pCoreOf]
  refine ⟨?_, fun k hk => ?_, ?_⟩
  · rw [← hc]
    exact ⟨r, h1, rfl⟩
  · rw [← hc] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact congrArg Subtype.val (h2 k' hk')
  · have := congrArg Subtype.val h3
    simpa using this

theorem coe_mem_pCoreOf_iff {p : ℕ} {H : Subgroup G} {h : ↥H} :
    (h : G) ∈ pCoreOf p H ↔ h ∈ CFSG.pCore p ↥H := CFSG.mem_openPCoreOf_iff h

theorem sup_pCoreOf_eq_of_quasisimple {L N : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hNL : N ≤ L)
    (hLN : L ≤ normalizer (N : Set G)) (hZ : ¬ N ≤ A6.o2Z L) : N ⊔ pCoreOf 2 L = L := by
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  let π : ↥L →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNn : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.1 (hLN l.2) n).1 hn
    simpa using this
  let N' : Subgroup Q := (N.subgroupOf L).map π
  have hN'n : N'.Normal := hNn.map π hπ
  let ρ : Q →* Q ⧸ center Q := QuotientGroup.mk' (center Q)
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hN''n : (N'.map ρ).Normal := hN'n.map ρ hρ
  have hsimp : IsSimpleGroup (Q ⧸ center Q) := hq.2.1
  refine le_antisymm (sup_le hNL (LieType.BorelTits.pCoreOf_le 2 L)) ?_
  rcases hsimp.eq_bot_or_eq_top_of_normal (N'.map ρ) with h | h
  · exfalso
    apply hZ
    intro n hn
    have hnL := hNL hn
    have hc : π ⟨n, hnL⟩ ∈ center Q := by
      have h1 : ρ (π ⟨n, hnL⟩) = 1 := by
        have : ρ (π ⟨n, hnL⟩) ∈ N'.map ρ :=
          mem_map_of_mem ρ (mem_map_of_mem π (by rw [mem_subgroupOf]; exact hn))
        rw [h] at this
        exact (mem_bot).1 this
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨n, hnL⟩, hc, rfl⟩
  · have hsup : N' ⊔ center Q = ⊤ := by
      rw [eq_top_iff]
      intro q _
      have hq' : ρ q ∈ N'.map ρ := by rw [h]; exact mem_top _
      obtain ⟨n', hn', he⟩ := mem_map.1 hq'
      have hz : n'⁻¹ * q ∈ center Q := by
        rw [← QuotientGroup.eq_one_iff (N := center Q)]
        change ρ (n'⁻¹ * q) = 1
        rw [map_mul, map_inv, he, inv_mul_cancel]
      have : q = n' * (n'⁻¹ * q) := by group
      rw [this]
      exact mul_mem (mem_sup_left hn') (mem_sup_right hz)
    have hN' : N' = ⊤ := eq_top_of_sup_center_eq_top' hq.1.commutator_eq_top hsup
    intro l hl
    have hlq : π ⟨l, hl⟩ ∈ N' := by rw [hN']; exact mem_top _
    obtain ⟨n, hn, he⟩ := mem_map.1 hlq
    have hk : n⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L)]
      change π (n⁻¹ * ⟨l, hl⟩) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hk' : ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := coe_mem_pCoreOf_iff.2 hk
    have : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact mul_mem (mem_sup_left (mem_subgroupOf.1 hn)) (mem_sup_right hk')

theorem normalizer_le_normalizer_oTwoRes (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (oTwoRes H : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ oTwoRes H, g * y * g⁻¹ ∈ oTwoRes H := by
    intro g hg y hy
    have hle : oTwoRes H ≤ (oTwoRes H).comap (MulAut.conj g).toMonoidHom := by
      rw [oTwoRes, closure_le]
      rintro x ⟨hx, m, hm, hxm⟩
      refine subset_closure ⟨(mem_normalizer_iff.1 hg x).1 hx, m, hm, ?_⟩
      change (g * x * g⁻¹) ^ m = 1
      rw [conj_pow, hxm]
      group
    exact hle hy
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro h
    have := key g⁻¹ (inv_mem hg) _ h
    simpa [mul_assoc] using this

theorem eq_one_of_two_pow_three_pow {c : G} {j k : ℕ} (h2 : c ^ 2 ^ j = 1) (h3 : c ^ 3 ^ k = 1) :
    c = 1 := by
  have hc : Nat.Coprime (2 ^ j) (3 ^ k) := Nat.Coprime.pow j k (by norm_num)
  have h1 : orderOf c ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rwa [hc.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

structure Core15 (G : Type) [Group G] [Finite G] (T L V V₂ X : Subgroup G) : Prop where
  h13 : QTH13 G T L
  irr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V
  zv : V ⊓ centralizer (L : Set G) = ⊥
  v2 : A6.IsV2 T V V₂
  T_le_NL : T ≤ normalizer (L : Set G)
  T_le_NV : T ≤ normalizer (V : Set G)
  quasi : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  q1 : ¬ pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)
  X_le_L : X ≤ L
  X_le_NV2 : X ≤ normalizer (V₂ : Set G)
  T_le_NX : T ≤ normalizer (X : Set G)
  X_res : oTwoRes X = X
  X_act : ∃ x ∈ X, x ^ 3 = 1 ∧ x ∉ centralizer (V₂ : Set G)
  X_ker : IsPGroup 2 ↥(X ⊓ centralizer (V₂ : Set G))
  X_o2Z : ¬ X ≤ A6.o2Z L
  gen : ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) → Nat.card V₃ = 8 →
    autOn (X ⊔ L ⊓ normalizer (V₃ : Set G)) V = autOn L V

namespace Core15

variable [Finite G] {T L V V₂ X : Subgroup G} (S : Core15 G T L V V₂ X)
include S

theorem sq_V {v : G} (hv : v ∈ V) : v ^ 2 = 1 := (mem_reducedAggregate' (S.irr.1 hv)).2.2

theorem comm_V {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  ((mem_reducedAggregate' (S.irr.1 hb)).2.1 a (mem_reducedAggregate' (S.irr.1 ha)).1)

theorem isEA : CFSG.IsElementaryAbelian 2 V :=
  BlueprintB2.isElementaryAbelian_iff.2 ⟨fun _ ha _ hb => S.comm_V ha hb, fun _ hv => S.sq_V hv⟩

theorem L_le_NV : L ≤ normalizer (V : Set G) := S.irr.2.2.1

theorem V2_le_V : V₂ ≤ V := S.v2.2.1

theorem V1_le_V2 : fsuV1 T V ≤ V₂ := S.v2.1

theorem T_le_NV2 : T ≤ normalizer (V₂ : Set G) := S.v2.2.2.1

theorem card_V2 : Nat.card V₂ = 4 := S.v2.2.2.2

theorem kleinV2 : IsKleinFour ↥V₂ :=
  isKleinFour_of_card_four' S.card_V2 fun s => Subtype.ext (by
    have := S.sq_V (S.V2_le_V s.2)
    rw [pow_two] at this
    simpa using this)

theorem T_le_G1 : T ≤ A6.g1 T V := by
  intro t ht
  have hZ : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) := by
    rw [quasithinOmegaOneCenter, closure_le]
    rintro z ⟨hz, -⟩
    exact hz.2
  refine mem_normalizer_inf (S.T_le_NV ht) ?_
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : t * x * t⁻¹ = x := by
      rw [(mem_centralizer_iff.1 (hZ hx)) t ht, mul_inv_cancel_right]
    rwa [this]
  · intro hx
    have : t * x * t⁻¹ = x := by
      have h1 : t * (t * x * t⁻¹) = (t * x * t⁻¹) * t := (mem_centralizer_iff.1 (hZ hx)) t ht
      calc t * x * t⁻¹ = t⁻¹ * (t * (t * x * t⁻¹)) := by group
        _ = t⁻¹ * ((t * x * t⁻¹) * t) := by rw [h1]
        _ = x := by group
    rwa [this] at hx

theorem sylow_G1 : IsSylowTwoOf T (A6.g1 T V) := by
  refine ⟨S.T_le_G1, S.h13.sylow.1, fun h2 => S.h13.sylow.2 ?_⟩
  rw [← Subgroup.relIndex_mul_index S.T_le_G1]
  exact Dvd.dvd.mul_right h2 _

theorem Q1_le_T : pCoreOf 2 (A6.g1 T V) ≤ T := pCoreOf_two_le_of_isSylowTwoOf S.sylow_G1

omit S in
theorem isP_Q1 : IsPGroup 2 (pCoreOf 2 (A6.g1 T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem Q1_le_NV2 : pCoreOf 2 (A6.g1 T V) ≤ normalizer (V₂ : Set G) := S.Q1_le_T.trans S.T_le_NV2

theorem Q1_le_NX : pCoreOf 2 (A6.g1 T V) ≤ normalizer (X : Set G) := S.Q1_le_T.trans S.T_le_NX

theorem CV2_le_G1 : centralizer (V₂ : Set G) ≤ A6.g1 T V :=
  (Subgroup.centralizer_le S.V1_le_V2).trans (Subgroup.centralizer_le_normalizer _)

theorem CV2_le_NQ1 : centralizer (V₂ : Set G) ≤ normalizer (pCoreOf 2 (A6.g1 T V) : Set G) :=
  S.CV2_le_G1.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _)

@[expose] noncomputable def psi : normalizer (V₂ : Set G) →* Equiv.Perm (Fin 3) :=
  @psiV2 G _ V₂ S.kleinV2

theorem psi_eq_one_iff {g : normalizer (V₂ : Set G)} :
    S.psi g = 1 ↔ (g : G) ∈ centralizer (V₂ : Set G) :=
  @psiV2_eq_one_iff G _ V₂ S.kleinV2 g

theorem psi_pow_eq_one {g : G} (hg : g ∈ normalizer (V₂ : Set G)) {n : ℕ} (h : g ^ n = 1) :
    S.psi ⟨g, hg⟩ ^ n = 1 := by
  rw [← map_pow]
  have : (⟨g, hg⟩ : normalizer (V₂ : Set G)) ^ n = 1 := Subtype.ext (by simpa using h)
  rw [this, map_one]

theorem psi_ne_one {g : G} (hg : g ∈ normalizer (V₂ : Set G))
    (h : g ∉ centralizer (V₂ : Set G)) : S.psi ⟨g, hg⟩ ≠ 1 :=
  fun h1 => h ((S.psi_eq_one_iff).1 h1)

theorem exists_x0_q0 : ∃ x₀ ∈ X, x₀ ^ 3 = 1 ∧ x₀ ∉ centralizer (V₂ : Set G) ∧
    ∃ q₀ ∈ pCoreOf 2 (A6.g1 T V), q₀ ∉ centralizer (V₂ : Set G) ∧ ∃ k : ℕ, q₀ ^ 2 ^ k = 1 := by
  obtain ⟨x₀, hx, h3, hc⟩ := S.X_act
  obtain ⟨q₀, hq, hqc⟩ := Set.not_subset.1 S.q1
  exact ⟨x₀, hx, h3, hc, q₀, hq, hqc, exists_two_pow_eq_one isP_Q1 hq⟩

theorem decomp {g : G} (hg : g ∈ normalizer (V₂ : Set G)) :
    ∃ y ∈ X ⊔ pCoreOf 2 (A6.g1 T V), y⁻¹ * g ∈ centralizer (V₂ : Set G) := by
  obtain ⟨x₀, hx, h3, hc, q₀, hq, hqc, k, hk⟩ := S.exists_x0_q0
  have hxN := S.X_le_NV2 hx
  have hqN := S.Q1_le_NV2 hq
  have hσ3 := S.psi_pow_eq_one hxN h3
  have hσ1 := S.psi_ne_one hxN hc
  have hτ2 := perm3_sq_of_two_pow (S.psi_pow_eq_one hqN hk)
  have hτ1 := S.psi_ne_one hqN hqc
  obtain ⟨i, j, hij⟩ := perm3_gen hσ3 hσ1 hτ2 hτ1 (S.psi ⟨g, hg⟩)
  let a : normalizer (V₂ : Set G) := ⟨x₀, hxN⟩ ^ (i : ℕ) * ⟨q₀, hqN⟩ ^ (j : ℕ)
  refine ⟨x₀ ^ (i : ℕ) * q₀ ^ (j : ℕ),
    mul_mem (mem_sup_left (pow_mem hx _)) (mem_sup_right (pow_mem hq _)), ?_⟩
  have h1 : S.psi (a⁻¹ * ⟨g, hg⟩) = 1 := by
    rw [map_mul, map_inv, hij]
    simp only [a, map_mul, map_pow]
    group
  have h2 := (S.psi_eq_one_iff).1 h1
  simpa [a] using h2

theorem I2_le :
    conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) ≤
      X ⊔ pCoreOf 2 (A6.g1 T V) := by
  refine conjClosure_le fun h hh q hq => ?_
  obtain ⟨y, hy, hc⟩ := S.decomp hh
  have hcq : (y⁻¹ * h) * q * (y⁻¹ * h)⁻¹ ∈ pCoreOf 2 (A6.g1 T V) :=
    (mem_normalizer_iff.1 (S.CV2_le_NQ1 hc) q).1 hq
  have : h * q * h⁻¹ = y * ((y⁻¹ * h) * q * (y⁻¹ * h)⁻¹) * y⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hy (mem_sup_right hcq)) (inv_mem hy)

theorem X_le_I2 : X ≤ conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) := by
  set I₂ := conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) with hI₂
  obtain ⟨x₀, -, -, -, q₀, hq, hqc, k, hk⟩ := S.exists_x0_q0
  have hqN := S.Q1_le_NV2 hq
  have hτ2 := perm3_sq_of_two_pow (S.psi_pow_eq_one hqN hk)
  have hτ1 := S.psi_ne_one hqN hqc
  have hNI : normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) :=
    le_normalizer_conjClosure _ _
  rw [← S.X_res]
  refine (closure_le _).2 ?_
  rintro x ⟨hx, m, hm, hxm⟩
  have hxN := S.X_le_NV2 hx
  have hπ3 := perm3_cube_of_odd hm (S.psi_pow_eq_one hxN hxm)
  set w := x * q₀ * x⁻¹ * q₀⁻¹ with hw
  have hwI : w ∈ I₂ := mul_mem (mem_conjClosure hxN hq) (inv_mem (le_conjClosure _ _ hq))
  have hwX : w ∈ X := by
    have h1 : q₀ * x⁻¹ * q₀⁻¹ ∈ X := (mem_normalizer_iff.1 (S.Q1_le_NX hq) x⁻¹).1 (inv_mem hx)
    rw [show w = x * (q₀ * x⁻¹ * q₀⁻¹) by rw [hw]; group]
    exact mul_mem hx h1
  have hwN : w ∈ normalizer (V₂ : Set G) :=
    mul_mem (mul_mem (mul_mem hxN hqN) (inv_mem hxN)) (inv_mem hqN)
  have hxw : x * w ∈ X ⊓ centralizer (V₂ : Set G) := by
    refine ⟨mul_mem hx hwX, ?_⟩
    have he : (⟨x * w, mul_mem hxN hwN⟩ : normalizer (V₂ : Set G)) =
        ⟨x, hxN⟩ * (⟨x, hxN⟩ * ⟨q₀, hqN⟩ * ⟨x, hxN⟩⁻¹ * ⟨q₀, hqN⟩⁻¹) := Subtype.ext (by
          simp [hw])
    have h1 : S.psi ⟨x * w, mul_mem hxN hwN⟩ = 1 := by
      rw [he, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hc := perm3_conj_inv hπ3 hτ2 hτ1
      calc S.psi ⟨x, hxN⟩ * (S.psi ⟨x, hxN⟩ * S.psi ⟨q₀, hqN⟩ * (S.psi ⟨x, hxN⟩)⁻¹ *
            (S.psi ⟨q₀, hqN⟩)⁻¹) =
          S.psi ⟨x, hxN⟩ * S.psi ⟨x, hxN⟩ *
            (S.psi ⟨q₀, hqN⟩ * (S.psi ⟨x, hxN⟩)⁻¹ * (S.psi ⟨q₀, hqN⟩)⁻¹) := by group
        _ = S.psi ⟨x, hxN⟩ ^ 3 := by rw [hc, pow_three, mul_assoc]
        _ = 1 := hπ3
    exact (S.psi_eq_one_iff).1 h1
  obtain ⟨k', hk'⟩ := exists_two_pow_eq_one S.X_ker hxw
  set y := x * w with hy
  have hyX : y ∈ X := hxw.1
  have hyK : y ∈ normalizer ((X ⊓ I₂ : Subgroup G) : Set G) :=
    mem_normalizer_inf (le_normalizer hyX) (hNI (mul_mem hxN hwN))
  have hl : y * w⁻¹ * y⁻¹ ∈ X ⊓ I₂ :=
    (mem_normalizer_iff.1 hyK w⁻¹).1 (inv_mem ⟨hwX, hwI⟩)
  obtain ⟨l', hl', he⟩ := pow_mem_mul_of_normalizes' hl hyK (2 ^ k')
  have hxe : y * w⁻¹ * y⁻¹ * y = x := by rw [hy]; group
  rw [hxe, hk', mul_one] at he
  have hxK : x ∈ X ⊓ I₂ := mem_of_pow_two_pow_mem (he ▸ hl') hm hxm
  exact hxK.2

theorem I2_eq :
    conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) =
      X ⊔ pCoreOf 2 (A6.g1 T V) :=
  le_antisymm S.I2_le (sup_le S.X_le_I2 (le_conjClosure _ _))

theorem I2_le_NV2 :
    conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) ≤ normalizer (V₂ : Set G) := by
  rw [S.I2_eq]
  exact sup_le S.X_le_NV2 S.Q1_le_NV2

theorem oTwoRes_I2 :
    oTwoRes (conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) = X := by
  rw [S.I2_eq]
  refine le_antisymm (oTwoRes_sup_le' isP_Q1 S.Q1_le_NX) ?_
  calc X = oTwoRes X := S.X_res.symm
    _ ≤ oTwoRes (X ⊔ pCoreOf 2 (A6.g1 T V)) := oTwoRes_mono' le_sup_left

theorem NV2_le_NX : normalizer (V₂ : Set G) ≤ normalizer (X : Set G) := by
  have h := (le_normalizer_conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))).trans
    (normalizer_le_normalizer_oTwoRes _)
  rwa [S.oTwoRes_I2] at h

theorem isP_CI2 : IsPGroup 2 ↥(conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) ⊓
    centralizer (V₂ : Set G)) := by
  refine isPGroup_two_of_forall' fun g hg => ?_
  have hgI := hg.1
  rw [S.I2_eq] at hgI
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left X _ S.Q1_le_NX
  have hgm : g ∈ (X : Set G) * (pCoreOf 2 (A6.g1 T V) : Set G) := by rw [← hmul]; exact hgI
  obtain ⟨a, ha, q, hq, rfl⟩ := hgm
  obtain ⟨b, hb⟩ := exists_two_pow_eq_one isP_Q1 hq
  obtain ⟨a', ha', he⟩ := pow_mem_mul_of_normalizes' ha (S.Q1_le_NX hq) (2 ^ b)
  rw [hb, mul_one] at he
  have hm : (a * q) ^ 2 ^ b ∈ X ⊓ centralizer (V₂ : Set G) := ⟨he ▸ ha', pow_mem hg.2 _⟩
  obtain ⟨c, hc⟩ := exists_two_pow_eq_one S.X_ker hm
  exact ⟨b + c, by rw [pow_add, pow_mul, hc]⟩

theorem CI2_eq : conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) ⊓
    centralizer (V₂ : Set G) =
      pCoreOf 2 (conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) := by
  set I₂ := conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) with hI₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ S.isP_CI2
    intro g hg
    exact mem_normalizer_inf (le_normalizer hg) (mem_normalizer_centralizer (S.I2_le_NV2 hg))
  · intro g hg
    have hgI : g ∈ I₂ := LieType.BorelTits.pCoreOf_le 2 _ hg
    refine ⟨hgI, ?_⟩
    by_contra hgc
    obtain ⟨x₀, hx, h3, hc, -⟩ := S.exists_x0_q0
    have hxI := S.X_le_I2 hx
    have hgN := S.I2_le_NV2 hgI
    have hxN := S.X_le_NV2 hx
    have hP : IsPGroup 2 (pCoreOf 2 I₂) := LieType.BorelTits.pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := exists_two_pow_eq_one hP hg
    have hρ2 := perm3_sq_of_two_pow (S.psi_pow_eq_one hgN hk)
    have hρ1 := S.psi_ne_one hgN hgc
    have hσ3 := S.psi_pow_eq_one hxN h3
    have hσ1 := S.psi_ne_one hxN hc
    have hg' : x₀ * g * x₀⁻¹ ∈ pCoreOf 2 I₂ :=
      (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 I₂ hxI) g).1 hg
    obtain ⟨k', hk'⟩ := exists_two_pow_eq_one hP (mul_mem hg hg')
    have hNgg : g * (x₀ * g * x₀⁻¹) ∈ normalizer (V₂ : Set G) :=
      mul_mem hgN (mul_mem (mul_mem hxN hgN) (inv_mem hxN))
    have h1 := perm3_sq_of_two_pow (S.psi_pow_eq_one hNgg hk')
    have he : (⟨g * (x₀ * g * x₀⁻¹), hNgg⟩ : normalizer (V₂ : Set G)) =
        ⟨g, hgN⟩ * (⟨x₀, hxN⟩ * ⟨g, hgN⟩ * ⟨x₀, hxN⟩⁻¹) := Subtype.ext (by simp)
    rw [he, map_mul, map_mul, map_mul, map_inv] at h1
    exact perm3_comm_ne hρ2 hρ1 hσ3 hσ1 h1

theorem quot_I2 : Nonempty (↥(conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) ⧸
    CFSG.pCore 2 ↥(conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) ≃*
      Equiv.Perm (Fin 3)) := by
  set I₂ := conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)) with hI₂
  let ψI : ↥I₂ →* Equiv.Perm (Fin 3) := S.psi.comp (Subgroup.inclusion S.I2_le_NV2)
  have hsurj : Function.Surjective ψI := by
    intro π
    obtain ⟨x₀, hx, h3, hc, q₀, hq, hqc, k, hk⟩ := S.exists_x0_q0
    have hxN := S.X_le_NV2 hx
    have hqN := S.Q1_le_NV2 hq
    obtain ⟨i, j, hij⟩ := perm3_gen (S.psi_pow_eq_one hxN h3) (S.psi_ne_one hxN hc)
      (perm3_sq_of_two_pow (S.psi_pow_eq_one hqN hk)) (S.psi_ne_one hqN hqc) π
    refine ⟨⟨x₀, S.X_le_I2 hx⟩ ^ (i : ℕ) * ⟨q₀, le_conjClosure _ _ hq⟩ ^ (j : ℕ), ?_⟩
    rw [hij, map_mul, map_pow, map_pow]
    rfl
  have hker : ψI.ker = CFSG.pCore 2 ↥I₂ := by
    ext g
    rw [MonoidHom.mem_ker, ← coe_mem_pCoreOf_iff, ← S.CI2_eq]
    change S.psi (Subgroup.inclusion S.I2_le_NV2 g) = 1 ↔ _
    rw [S.psi_eq_one_iff]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψI hsurj)⟩

theorem CQ1_le : pCoreOf 2 (A6.g1 T V) ⊓ centralizer (V₂ : Set G) ≤
    pCoreOf 2 (conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) :=
  S.CI2_eq ▸ inf_le_inf_right _ (le_conjClosure _ _)

theorem O2I2_le : pCoreOf 2 (conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) ≤
    pCoreOf 2 (normalizer (V₂ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 _).trans S.I2_le_NV2)
    ((le_normalizer_conjClosure _ _).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem pRank_CV2_open : CFSG.Open.pRank 3 (centralizer (V₂ : Set G)) ≤ 1 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.SectionRank.pRank_le (G := G) (p := 3) (by norm_num) fun E hE hEA => ?_
  by_contra hlt
  have hEc := hEA.1
  have hE3 : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hEA.2 e e.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE3
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp_all
    · exact h
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 (n := 2)
    (by rw [hn]; exact pow_dvd_pow 3 hn2)
  set E' := H.map E.subtype with hE'
  have hE'card : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective E.subtype_injective, hH]
  have hE'E : E' ≤ E := map_subtype_le H
  have hE'C : E' ≤ centralizer (V₂ : Set G) := hE'E.trans hE
  have hCN : centralizer (V₂ : Set G) ≤ normalizer (V₂ : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hE'X : E' ≤ normalizer (X : Set G) := (hE'C.trans hCN).trans S.NV2_le_NX
  have hE'3 : IsPGroup 3 E' := IsPGroup.of_card hE'card
  set B := X ⊔ E' with hB
  have hBX : B ≤ normalizer (X : Set G) := sup_le le_normalizer hE'X
  have hBN : B ≤ normalizer (V₂ : Set G) := sup_le S.X_le_NV2 (hE'C.trans hCN)
  obtain ⟨x₀, hx, hx3, hxc, -⟩ := S.exists_x0_q0
  have hxB : x₀ ∈ B := mem_sup_left hx
  have hpE : IsPGroup 3 (E'.subgroupOf B) :=
    hE'3.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hpE
  have hx1 : (⟨x₀, hxB⟩ : ↥B) ≠ 1 := by
    intro h
    apply hxc
    rw [show x₀ = 1 from congrArg Subtype.val h]
    exact one_mem _
  have hxo : orderOf (⟨x₀, hxB⟩ : ↥B) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hx3)) hx1
  have hpx : IsPGroup 3 (zpowers (⟨x₀, hxB⟩ : ↥B)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨P', hP'⟩ := IsPGroup.exists_le_sylow hpx
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq (↥B) P' P
  have hbx : b * ⟨x₀, hxB⟩ * b⁻¹ ∈ (P : Subgroup ↥B) := by
    have h1 : MulAut.conj b • (⟨x₀, hxB⟩ : ↥B) ∈ MulAut.conj b • (P' : Subgroup ↥B) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP' (mem_zpowers _))
    have h2 : MulAut.conj b • (⟨x₀, hxB⟩ : ↥B) ∈ ((b • P' : Sylow 3 ↥B) : Subgroup ↥B) := h1
    rw [hb] at h2
    simpa [MulAut.smul_def] using h2
  set p := (b : G) * x₀ * (b : G)⁻¹ with hp
  have hpX : p ∈ X := (mem_normalizer_iff.1 (hBX b.2) x₀).1 hx
  have hpN : p ∈ normalizer (V₂ : Set G) := S.X_le_NV2 hpX
  have hpc : p ∉ centralizer (V₂ : Set G) := by
    intro h
    apply hxc
    have := (mem_normalizer_iff.1 (mem_normalizer_centralizer (inv_mem (hBN b.2))) p).1 h
    simpa [hp, mul_assoc] using this
  have hp3 : p ^ 3 = 1 := by rw [hp, conj_pow, hx3]; group
  have hcomm : ∀ e ∈ E', p * e = e * p := by
    intro e he
    have heB : e ∈ B := mem_sup_right he
    have heP : (⟨e, heB⟩ : ↥B) ∈ (P : Subgroup ↥B) := hP (by rw [mem_subgroupOf]; exact he)
    set c := p * e * p⁻¹ * e⁻¹ with hc
    have hcX : c ∈ X ⊓ centralizer (V₂ : Set G) := by
      refine mem_inf.2 ⟨?_, ?_⟩
      · have h1 : e * p⁻¹ * e⁻¹ ∈ X := (mem_normalizer_iff.1 (hE'X he) p⁻¹).1 (inv_mem hpX)
        rw [show c = p * (e * p⁻¹ * e⁻¹) by rw [hc]; group]
        exact mul_mem hpX h1
      · have h1 : p * e * p⁻¹ ∈ centralizer (V₂ : Set G) :=
          (mem_normalizer_iff.1 (mem_normalizer_centralizer hpN) e).1 (hE'C he)
        exact mul_mem h1 (inv_mem (hE'C he))
    have hcP : (⟨p, mem_sup_left hpX⟩ : ↥B) * ⟨e, heB⟩ * ⟨p, mem_sup_left hpX⟩⁻¹ *
        ⟨e, heB⟩⁻¹ ∈ (P : Subgroup ↥B) := by
      have hpP : (⟨p, mem_sup_left hpX⟩ : ↥B) ∈ (P : Subgroup ↥B) := by
        convert hbx using 1
      exact mul_mem (mul_mem (mul_mem hpP heP) (inv_mem hpP)) (inv_mem heP)
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨_, hcP⟩
    have hk' : c ^ 3 ^ k = 1 := by
      have := congrArg (fun z : ↥(P : Subgroup ↥B) => ((z : ↥B) : G)) hk
      simpa [hc] using this
    obtain ⟨j, hj⟩ := exists_two_pow_eq_one S.X_ker hcX
    have hc1 := eq_one_of_two_pow_three_pow hj hk'
    rw [hc] at hc1
    calc p * e = (p * e * p⁻¹ * e⁻¹) * (e * p) := by group
      _ = e * p := by rw [hc1, one_mul]
  have hpE' : p ∉ E' := fun h => hpc (hE'C h)
  have hp1 : p ≠ 1 := fun h => hpc (h ▸ one_mem _)
  have hpo : orderOf p = 3 := orderOf_eq_prime hp3 hp1
  have hinf : zpowers p ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyp, hyE⟩
    by_contra hy1
    have hy1' : y ≠ 1 := fun h => hy1 (h ▸ one_mem _)
    have hz : zpowers y = zpowers p := by
      refine eq_of_le_of_card_ge (zpowers_le.2 hyp) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hpo]
      have hyo : orderOf y ∣ 3 := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hyp
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← zpow_natCast (p ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp3,
          one_zpow]
      rcases (Nat.dvd_prime Nat.prime_three).1 hyo with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hy1'
      · rw [h]
    apply hpE'
    have : p ∈ zpowers y := hz ▸ mem_zpowers p
    exact (zpowers_le.2 hyE) this
  have hc' : ∀ (x : ↥(zpowers p)) (y : ↥E'), Commute ((zpowers p).subtype x) (E'.subtype y) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (hcomm y hy) k))
  let f : ↥(zpowers p) × ↥E' →* G := MonoidHom.noncommCoprod _ _ hc'
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hyp : (y : G) ∈ zpowers p := by
      rw [eq_inv_of_mul_eq_one_right hxy']
      exact inv_mem x.2
    have hy1 : (y : G) = 1 := by
      have : (y : G) ∈ zpowers p ⊓ E' := ⟨hyp, y.2⟩
      rw [hinf, mem_bot] at this
      exact this
    rw [hy1, mul_one] at hxy'
    rw [show x = 1 from Subtype.ext hxy', show y = 1 from Subtype.ext hy1]
    rfl
  have hEc' : ∀ a b : ↥E', a * b = b * a := fun a b =>
    Subtype.ext (by
      have := mul_comm' (⟨a, hE'E a.2⟩ : ↥E) ⟨b, hE'E b.2⟩
      simpa using congrArg Subtype.val this)
  have hle : 2 + 1 ≤ CFSG.Open.pRank 3 (normalizer (V₂ : Set G)) := by
    refine CFSG.SectionRank.le_pRank_of_injective (A := ↥(zpowers p) × ↥E') (by norm_num)
      ?_ ?_ ?_ f hf ?_
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
      refine Prod.ext ?_ (hEc' y₁ y₂)
      obtain ⟨k₁, hk₁⟩ := mem_zpowers_iff.1 x₁.2
      obtain ⟨k₂, hk₂⟩ := mem_zpowers_iff.1 x₂.2
      apply Subtype.ext
      change (x₁ : G) * x₂ = x₂ * x₁
      rw [← hk₁, ← hk₂, ← zpow_add, ← zpow_add, add_comm]
    · rintro ⟨x, y⟩
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 x.2
        change (x : G) ^ 3 = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp3, one_zpow]
      · change (y : G) ^ 3 = 1
        exact hEA.2 y (hE'E y.2)
    · rw [Nat.card_prod, Nat.card_zpowers, hpo, hE'card]
      norm_num
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      exact mul_mem (zpowers_le.2 hpN x.2) ((hE'C.trans hCN) y.2)
  have hV2ne : V₂ ≠ ⊥ := by
    intro h
    have := S.card_V2
    rw [h, card_bot] at this
    norm_num at this
  have hV2p : IsPGroup 2 V₂ := IsPGroup.of_card (n := 2) (by rw [S.card_V2]; norm_num)
  have hloc : IsTwoLocal (normalizer (V₂ : Set G)) := ⟨V₂, hV2ne, hV2p, rfl⟩
  have hev := A1b.pRank_le_evenRank Nat.prime_three (by norm_num) hloc
  have hq : CFSG.Open.evenRank G ≤ 2 := S.h13.qtke.2.2
  omega

theorem pRank_CV2 : CFSG.pRank 3 ↥(centralizer (V₂ : Set G)) ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine (CFSG.SectionRank.pRank_le_map (by norm_num) (centralizer (V₂ : Set G)).subtype
    (centralizer (V₂ : Set G)).subtype_injective ⊤).trans ?_
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact S.pRank_CV2_open

theorem CV3_le_NL {V₃ : Subgroup G} (h23 : V₂ ≤ V₃) (h3V : V₃ ≤ V)
    (hT3 : T ≤ normalizer (V₃ : Set G)) (hc3 : Nat.card V₃ = 8) :
    centralizer (V₃ : Set G) ≤ normalizer (L : Set G) := by
  have hCV : centralizer (V : Set G) ≤ normalizer (V₃ : Set G) :=
    (Subgroup.centralizer_le h3V).trans (Subgroup.centralizer_le_normalizer _)
  have hAL : X ⊔ L ⊓ normalizer (V₃ : Set G) = L := by
    refine le_antisymm (sup_le S.X_le_L inf_le_left) fun l hl => ?_
    have hlN := S.L_le_NV hl
    have hmem : conjAct V ⟨l, hlN⟩ ∈ autOn (X ⊔ L ⊓ normalizer (V₃ : Set G)) V := by
      rw [S.gen V₃ h23 h3V hT3 hc3]
      exact A1b.conjAct_mem_autOn hlN hl
    obtain ⟨a, ha, he⟩ := mem_map.1 hmem
    rw [mem_subgroupOf] at ha
    have h1 : conjAct V (a⁻¹ * ⟨l, hlN⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h2 := A1b.conjAct_eq_one_iff.1 h1
    have haL : (a : G) ∈ L := (sup_le S.X_le_L inf_le_left) ha
    have h3 : (a : G)⁻¹ * l ∈ L ⊓ normalizer (V₃ : Set G) :=
      mem_inf.2 ⟨mul_mem (inv_mem haL) hl, hCV (by simpa using h2)⟩
    have : l = a * ((a : G)⁻¹ * l) := by group
    rw [this]
    exact mul_mem ha (mem_sup_right h3)
  set N := conjClosure X (L ⊓ normalizer (V₃ : Set G)) with hN
  have hNL : N ≤ L := conjClosure_le fun n hn x hx =>
    mul_mem (mul_mem hn.1 (S.X_le_L hx)) (inv_mem hn.1)
  have hLN : L ≤ normalizer (N : Set G) := by
    rw [← hAL]
    exact sup_le ((le_conjClosure X _).trans le_normalizer) (le_normalizer_conjClosure _ _)
  have hNZ : ¬ N ≤ A6.o2Z L := fun h => S.X_o2Z ((le_conjClosure X _).trans h)
  have hsup := sup_pCoreOf_eq_of_quasisimple S.quasi hNL hLN hNZ
  have hNeq : N = L := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine S.h13.faithful.2.1 N hNL ((normal_subgroupOf_iff_le_normalizer hNL).2 hLN) ?_
    intro x hx
    have hOL : pCoreOf 2 L ≤ normalizer (N : Set G) :=
      (LieType.BorelTits.pCoreOf_le 2 L).trans hLN
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left N (pCoreOf 2 L) hOL
    have hxm : x ∈ (N : Set G) * (pCoreOf 2 L : Set G) := by
      rw [← hmul, hsup]
      exact hx
    obtain ⟨a, ha, o, ho, rfl⟩ := hxm
    obtain ⟨k, hk⟩ := exists_two_pow_eq_one (LieType.BorelTits.pCoreOf_isPGroup 2 L) ho
    obtain ⟨a', ha', he⟩ := pow_mem_mul_of_normalizes' ha (hOL ho) (2 ^ k)
    rw [hk, mul_one] at he
    exact ⟨k, he ▸ ha'⟩
  have hCX : centralizer (V₃ : Set G) ≤ normalizer (X : Set G) :=
    ((Subgroup.centralizer_le h23).trans (Subgroup.centralizer_le_normalizer _)).trans
      S.NV2_le_NX
  have key : ∀ c ∈ centralizer (V₃ : Set G), ∀ y ∈ N, c * y * c⁻¹ ∈ N := by
    intro c hc y hy
    have hle : N ≤ N.comap (MulAut.conj c).toMonoidHom := conjClosure_le fun n hn x hx => by
      change c * (n * x * n⁻¹) * c⁻¹ ∈ N
      have hc' : n⁻¹ * c * n ∈ centralizer (V₃ : Set G) := by
        have := (mem_normalizer_iff.1 (mem_normalizer_centralizer (inv_mem hn.2)) c).1 hc
        simpa using this
      have hx' : (n⁻¹ * c * n) * x * (n⁻¹ * c * n)⁻¹ ∈ X :=
        (mem_normalizer_iff.1 (hCX hc') x).1 hx
      have : c * (n * x * n⁻¹) * c⁻¹ = n * ((n⁻¹ * c * n) * x * (n⁻¹ * c * n)⁻¹) * n⁻¹ := by
        group
      rw [this]
      exact mem_conjClosure hn hx'
    exact hle hy
  intro c hc
  rw [← hNeq, mem_normalizer_iff]
  intro y
  constructor
  · exact key c hc y
  · intro h
    have := key c⁻¹ (inv_mem hc) _ h
    simpa [mul_assoc] using this

theorem stmt6 {V₃ : Subgroup G} (h23 : V₂ ≤ V₃) (h3V : V₃ ≤ V)
    (hT3 : T ≤ normalizer (V₃ : Set G)) (hc3 : Nat.card V₃ = 8) :
    centralizer (V₃ : Set G) ≤ normalizer (V : Set G) := by
  have hirr : ∀ W : Subgroup G, W ≤ V → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
      W = ⊥ ∨ W = V := by
    intro W hWV hW
    have hLW : L ≤ normalizer (W : Set G) := by
      intro l hl
      rw [mem_normalizer_iff]
      intro w
      constructor
      · exact hW l hl w
      · intro h
        have := hW l⁻¹ (inv_mem hl) _ h
        simpa [mul_assoc] using this
    have h := S.irr.2.2.2.2.2.1 W (by rw [S.zv]; exact bot_le) hWV hLW
    rwa [S.zv] at h
  have hV3ne : V₃ ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hc3
    norm_num at hc3
  obtain ⟨-, hTI2, -⟩ := SteinbergCB.irreducible_local_module_is_TI_in_local_normalizer
    (M := normalizer (L : Set G)) le_normalizer
    ((normal_subgroupOf_iff_le_normalizer le_normalizer).2 le_rfl) S.irr.2.1 S.isEA S.L_le_NV
    hirr
  exact fun c hc => (hTI2 V₃ hV3ne h3V ⟨S.CV3_le_NL h23 h3V hT3 hc3 hc,
    Subgroup.centralizer_le_normalizer _ hc⟩).2

theorem stmt6_comm {V₃ : Subgroup G} (h23 : V₂ ≤ V₃) (h3V : V₃ ≤ V)
    (hT3 : T ≤ normalizer (V₃ : Set G)) (hc3 : Nat.card V₃ = 8)
    (hmod : ∀ c ∈ normalizer (V : Set G) ⊓ normalizer (L : Set G) ⊓ centralizer (V₃ : Set G),
      ∀ v ∈ V, ⁅v, c⁆ ∈ fsuV1 T V) :
    ⁅V, centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V :=
  Subgroup.commutator_le.2 fun v hv c hc =>
    hmod c ⟨⟨S.stmt6 h23 h3V hT3 hc3 hc, S.CV3_le_NL h23 h3V hT3 hc3 hc⟩, hc⟩ v hv

theorem stmt {P : Prop} {I₂ : Subgroup G}
    (hI₂ : I₂ = conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G)))
    (hmod : P → ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
      Nat.card V₃ = 8 →
      ∀ c ∈ normalizer (V : Set G) ⊓ normalizer (L : Set G) ⊓ centralizer (V₃ : Set G),
        ∀ v ∈ V, ⁅v, c⁆ ∈ fsuV1 T V) :
    normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (A6.g1 T V) ∧
      I₂ ⊓ centralizer (V₂ : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pCoreOf 2 (A6.g1 T V) ⊓ centralizer (V₂ : Set G) ≤ pCoreOf 2 I₂ ∧
      pCoreOf 2 I₂ ≤ pCoreOf 2 (normalizer (V₂ : Set G)) ∧
      CFSG.pRank 3 ↥(centralizer (V₂ : Set G)) ≤ 1 ∧
      ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
        Nat.card V₃ = 8 →
          centralizer (V₃ : Set G) ≤ normalizer (V : Set G) ∧
            (P → ⁅V, centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V) := by
  subst hI₂
  exact ⟨le_normalizer_conjClosure _ _, S.I2_eq, S.CI2_eq, S.quot_I2, S.oTwoRes_I2, S.CQ1_le,
    S.O2I2_le, S.pRank_CV2, fun V₃ h23 h3V hT3 hc3 =>
      ⟨S.stmt6 h23 h3V hT3 hc3, fun hP => S.stmt6_comm h23 h3V hT3 hc3
        (hmod hP V₃ h23 h3V hT3 hc3)⟩⟩

end Core15

end CFSG.Quasithin.H13.U3
