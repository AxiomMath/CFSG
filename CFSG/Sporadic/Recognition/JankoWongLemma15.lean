module

public import CFSG.Sporadic.Recognition.JankoWongLemma14

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

theorem exists_fixed_of_inverts_of_odd_support {σ c : Perm (Fin 8)} (hσ : σ ^ 2 = 1)
    (hodd : Odd c.support.card) (hinv : σ * c * σ⁻¹ = c⁻¹) : ∃ x, σ x = x := by
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    have := congrArg (fun q : Perm (Fin 8) => q x) hσ
    simpa [pow_two] using this
  have h1 : σ * c = c⁻¹ * σ := by
    calc σ * c = (σ * c * σ⁻¹) * σ := by group
      _ = c⁻¹ * σ := by rw [hinv]
  have hmem : ∀ x, x ∈ c.support → σ x ∈ c.support := by
    intro x hx
    rw [mem_support] at hx ⊢
    intro hcx
    apply hx
    have h2 : σ (c x) = c⁻¹ (σ x) := by
      have := congrArg (fun q : Perm (Fin 8) => q x) h1
      simpa using this
    have h3 : c⁻¹ (σ x) = σ x := (Equiv.Perm.inv_eq_iff_eq).mpr hcx.symm
    rw [h3] at h2
    exact σ.injective h2
  let f : c.support → c.support := fun x => ⟨σ x, hmem x x.2⟩
  have hf : ∀ x, f (f x) = x := fun x => Subtype.ext (hσσ x)
  have hcard : Odd (Nat.card c.support) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hodd
  obtain ⟨x, hx⟩ := exists_fixed_of_sq_eq_one_odd hf hcard
  exact ⟨x, congrArg Subtype.val hx⟩

theorem dvd_card_of_fixed_point_free {α : Type*} [Finite α] (f : Function.End α) {p : ℕ}
    [Fact p.Prime] (hf : f ^ p = 1) (hfix : ∀ x, f x ≠ x) : p ∣ Nat.card α := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hf' : f ^ p ^ 1 = 1 := by simpa using hf
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) hf'
  have hfixed : Function.fixedPoints f = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact hfix x
  have : IsEmpty ↑(Function.fixedPoints f) := Set.isEmpty_coe_sort.mpr hfixed
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_of_isEmpty (α := ↑(Function.fixedPoints f))] at hmod
  exact (Nat.modEq_zero_iff_dvd).mp hmod

section KleinFourCard

variable {C : Type*} [Group C]

theorem card_kleinFourSubgroup {u v : C} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (hc : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    Nat.card (kleinFourSubgroup hu hv hc) = 4 := by
  have huu : u * u = 1 := by rwa [← pow_two]
  have hztne1 : u * v ≠ 1 := fun h => huv (by
    have : v = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right huu).symm)
  have hzne : u ≠ u * v := fun h => hv1 (by
    have := congrArg (fun w => u⁻¹ * w) h
    simpa using this.symm)
  have htne : v ≠ u * v := fun h => hu1 (by
    have := congrArg (fun w => w * v⁻¹) h
    simpa using this.symm)
  have h1 : Nat.card (kleinFourSubgroup hu hv hc) = ({1, u, v, u * v} : Set C).ncard :=
    Nat.card_coe_set_eq ({1, u, v, u * v} : Set C)
  rw [h1, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair htne]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨huv, hzne⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hu1.symm, hv1.symm, fun h => hztne1 h.symm⟩

end KleinFourCard

section ConjEnd

variable {G : Type*} [Group G]

@[expose] def conjEnd {X : Set G} {r : G} (hX : ∀ y ∈ X, r * y * r⁻¹ ∈ X) : Function.End X :=
  fun y => ⟨r * y * r⁻¹, hX y y.2⟩

theorem conjEnd_pow {X : Set G} {r : G} (hX : ∀ y ∈ X, r * y * r⁻¹ ∈ X) (n : ℕ) (y : X) :
    (((conjEnd hX) ^ n) y : G) = r ^ n * (y : G) * (r ^ n)⁻¹ := by
  induction n generalizing y with
  | zero => simp; rfl
  | succ n ih =>
    rw [pow_succ]
    show (((conjEnd hX) ^ n) (conjEnd hX y) : G) = _
    rw [ih]
    show r ^ n * (r * (y : G) * r⁻¹) * (r ^ n)⁻¹ = r ^ (n + 1) * (y : G) * (r ^ (n + 1))⁻¹
    group

end ConjEnd

section Gen

variable {G : Type*} [Group G]

theorem conj_eq_or_inv_gen {x g : G} (hx3 : orderOf x = 3)
    (hg : g ∈ normalizer (zpowers x : Set G)) :
    g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
  have hx1 : x ≠ 1 := fun e => by rw [e, orderOf_one] at hx3; omega
  have hmem : g * x * g⁻¹ ∈ zpowers x :=
    (Subgroup.mem_normalizer_iff.mp hg x).mp (Subgroup.mem_zpowers x)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hmod : x ^ (n % 3) = x ^ n := by
    have := zpow_mod_orderOf x n
    rwa [hx3] at this
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exfalso
    rw [h] at hmod
    have h1 : g * x * g⁻¹ = 1 := by rw [← hn, ← hmod]; simp
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · left
    rw [h] at hmod
    rw [← hn, ← hmod]; simp
  · right
    rw [h] at hmod
    rw [← hn, ← hmod]
    have h2 : x ^ 2 * x = 1 := by
      rw [← pow_succ]
      have := pow_orderOf_eq_one x
      rwa [hx3] at this
    calc x ^ ((2 : ℤ)) = x ^ 2 := by norm_cast
      _ = x⁻¹ := eq_inv_of_mul_eq_one_left h2

theorem card_eq_two_mul_inf_centralizer {x e : G} (hx3 : orderOf x = 3) {U : Subgroup G}
    (hUN : U ≤ normalizer (zpowers x : Set G)) (heU : e ∈ U) (hex : e * x * e⁻¹ = x⁻¹) :
    Nat.card U = 2 * Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have hx1 : x ≠ 1 := fun e => by rw [e, orderOf_one] at hx3; omega
  have hinv_ne : x⁻¹ ≠ x := fun h => by
    have h2 : x * x = 1 := by
      calc x * x = x⁻¹ * x := by rw [h]
        _ = 1 := inv_mul_cancel x
    have := orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rwa [pow_two])
    rw [hx3] at this
    norm_num at this
  set K : Subgroup U := (centralizer ({x} : Set G)).subgroupOf U with hK
  have hmem : ∀ y : U, y ∈ K ↔ (y : G) * x * (y : G)⁻¹ = x := fun y => by
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      ← mul_inv_eq_iff_eq_mul]
  have hidx : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨e, heU⟩, fun b => ?_⟩
    have hbe : (b * ⟨e, heU⟩ : U) = ⟨(b : G) * e, U.mul_mem b.2 heU⟩ := rfl
    rcases conj_eq_or_inv_gen hx3 (hUN b.2) with hb | hb
    · refine Or.inr ⟨(hmem b).mpr hb, fun hbeK => ?_⟩
      have h1 := (hmem _).mp hbeK
      rw [hbe] at h1
      have : (b : G) * e * x * ((b : G) * e)⁻¹ = x⁻¹ := by
        calc (b : G) * e * x * ((b : G) * e)⁻¹ = (b : G) * (e * x * e⁻¹) * (b : G)⁻¹ := by group
          _ = (b : G) * x⁻¹ * (b : G)⁻¹ := by rw [hex]
          _ = ((b : G) * x * (b : G)⁻¹)⁻¹ := by group
          _ = x⁻¹ := by rw [hb]
      exact hinv_ne (by rw [← this]; exact h1)
    · refine Or.inl ⟨?_, fun hbK => ?_⟩
      · rw [hbe] at *
        apply (hmem _).mpr
        calc (b : G) * e * x * ((b : G) * e)⁻¹ = (b : G) * (e * x * e⁻¹) * (b : G)⁻¹ := by group
          _ = (b : G) * x⁻¹ * (b : G)⁻¹ := by rw [hex]
          _ = ((b : G) * x * (b : G)⁻¹)⁻¹ := by group
          _ = x := by rw [hb, inv_inv]
      · have h1 := (hmem _).mp hbK
        rw [hb] at h1
        exact hinv_ne h1
  have hKcard : Nat.card K = Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    rw [hK, ← Subgroup.inf_subgroupOf_right, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : U ⊓ centralizer ({x} : Set G) ≤ U)).toEquiv
  have h1 := Subgroup.card_mul_index K
  rw [hidx, hKcard] at h1
  omega

theorem mem_normalizer_zpowers_of_inv {x e : G} (hex : e * x * e⁻¹ = x⁻¹) :
    e ∈ normalizer (zpowers x : Set G) := by
  have h1 : e⁻¹ * x⁻¹ * e = x := by
    calc e⁻¹ * x⁻¹ * e = e⁻¹ * (e * x * e⁻¹) * e := by rw [hex]
      _ = x := by group
  have hex' : e⁻¹ * x * e = x⁻¹ := by
    calc e⁻¹ * x * e = (e⁻¹ * x⁻¹ * e)⁻¹ := by group
      _ = x⁻¹ := by rw [h1]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : e * x ^ n * e⁻¹ = (x⁻¹) ^ n := by rw [← hex]; exact conj_zpow.symm
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) n
  · intro hh
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : h = (x⁻¹) ^ m := by
      calc h = e⁻¹ * (e * h * e⁻¹) * e := by group
        _ = e⁻¹ * x ^ m * e := by rw [← hm]
        _ = (e⁻¹ * x * e) ^ m := by
            have := conj_zpow (a := e⁻¹) (b := x) (i := m)
            simpa using this.symm
        _ = (x⁻¹) ^ m := by rw [hex']
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) m

theorem centralizer_le_normalizer_zpowers (x : G) :
    centralizer ({x} : Set G) ≤ normalizer (zpowers x : Set G) := by
  have h := Subgroup.centralizer_le_normalizer (G := G) ((zpowers x : Subgroup G) : Set G)
  have e : centralizer (((zpowers x : Subgroup G)) : Set G) = centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [e] at h

end Gen

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

@[expose] def ocl (x : G) : Set G := {y | ∃ g ∈ c.NG, y = g * x * g⁻¹}

theorem card_ocl_mul (x : G) :
    Nat.card (c.ocl x) * Nat.card (c.NG ⊓ centralizer ({x} : Set G) : Subgroup G) =
      Nat.card c.NG := by
  classical
  set K : Subgroup ↥c.NG := (centralizer ({x} : Set G)).subgroupOf c.NG with hK
  let f : ↥c.NG ⧸ K → ↥(c.ocl x) := Quotient.lift
    (fun g => ⟨(g : G) * x * (g : G)⁻¹, g, g.2, rfl⟩)
    (fun g g' h => by
      have h1 : (g : G)⁻¹ * (g' : G) ∈ centralizer ({x} : Set G) := Subgroup.mem_subgroupOf.mp
        (QuotientGroup.leftRel_apply.mp h)
      have h2 : (g : G)⁻¹ * (g' : G) * x = x * ((g : G)⁻¹ * (g' : G)) :=
        Subgroup.mem_centralizer_singleton_iff.mp h1
      apply Subtype.ext
      show (g : G) * x * (g : G)⁻¹ = (g' : G) * x * (g' : G)⁻¹
      calc (g : G) * x * (g : G)⁻¹
          = (g : G) * ((g : G)⁻¹ * (g' : G) * x * ((g : G)⁻¹ * (g' : G))⁻¹) * (g : G)⁻¹ := by
            rw [mul_inv_eq_iff_eq_mul.mpr h2]
        _ = (g' : G) * x * (g' : G)⁻¹ := by group)
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      induction u using Quotient.inductionOn
      induction v using Quotient.inductionOn
      rename_i g g'
      have h1 : (g : G) * x * (g : G)⁻¹ = (g' : G) * x * (g' : G)⁻¹ := congrArg Subtype.val huv
      refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      show (g : G)⁻¹ * (g' : G) * x = x * ((g : G)⁻¹ * (g' : G))
      calc (g : G)⁻¹ * (g' : G) * x
          = (g : G)⁻¹ * ((g' : G) * x * (g' : G)⁻¹) * (g' : G) := by group
        _ = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g' : G) := by rw [h1]
        _ = x * ((g : G)⁻¹ * (g' : G)) := by group
    · rintro ⟨y, g, hg, rfl⟩
      exact ⟨Quotient.mk _ ⟨g, hg⟩, rfl⟩
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have hKcard : Nat.card K = Nat.card (c.NG ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    rw [hK, ← Subgroup.inf_subgroupOf_right, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      c.NG ⊓ centralizer ({x} : Set G) ≤ c.NG)).toEquiv
  rw [hKcard, Nat.card_congr (Equiv.ofBijective f hf)] at hmul
  exact hmul.symm

theorem ocl_subset_OG {x : G} (hx : x ∈ c.OG) : c.ocl x ⊆ (c.OG : Set G) := by
  rintro _ ⟨g, hg, rfl⟩
  exact c.conj_mem_OG_of_mem_NG hg hx

theorem NG_inf_centralizer_s : c.NG ⊓ centralizer ({c.s} : Set G) = c.Cg :=
  inf_eq_right.mpr c.Cg_le_NG

theorem card_ocl_s :
    Nat.card (c.ocl c.s) = 60 := by
  obtain ⟨-, hCg, hNG, -⟩ := c.lemma14
  have h := c.card_ocl_mul c.s
  rw [c.NG_inf_centralizer_s, hCg, hNG] at h
  omega

theorem aG_cube : (c.a : G) ^ 3 = 1 := (c.Xs_pow_three (x := (c.a : G)) (Or.inl rfl)).1

theorem aG_ne_one : (c.a : G) ≠ 1 := (c.Xs_pow_three (x := (c.a : G)) (Or.inl rfl)).2

theorem false_of_klein_four_centralizing_a {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hc : u * v = v * u)
    (hua : u * (c.a : G) = (c.a : G) * u) (hva : v * (c.a : G) = (c.a : G) * v) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := kleinFourSubgroup hu hv hc with hV
  have hV4 : Nat.card V = 4 := card_kleinFourSubgroup hu hv hc hu1 hv1 huv
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  set Ca : Subgroup G := centralizer ({(c.a : G)} : Set G) with hCa
  have hVC : V ≤ Ca := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases (mem_kleinFourSubgroup hu hv hc).mp hy with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact hua
    · rw [h]; exact hva
    · rw [h]
      calc u * v * (c.a : G) = u * (v * (c.a : G)) := by group
        _ = u * ((c.a : G) * v) := by rw [hva]
        _ = (u * (c.a : G)) * v := by group
        _ = ((c.a : G) * u) * v := by rw [hua]
        _ = (c.a : G) * (u * v) := by group
  have hV' : IsPGroup 2 (V.subgroupOf Ca) := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVC).symm
  obtain ⟨T, hT⟩ := hV'.exists_le_sylow
  have hT8 : Nat.card T = 8 := S.card_sylow_centralizer_type3 c.ha3 c.cycleType_a T
  set TG : Subgroup G := (T : Subgroup ↥Ca).map Ca.subtype with hTG
  have hTGcard : Nat.card TG = 8 := by
    rw [hTG, Subgroup.card_map_of_injective Ca.subtype_injective]; exact hT8
  have hTG2 : IsPGroup 2 TG := T.isPGroup'.map Ca.subtype
  have hTGa : ∀ t ∈ TG, t * (c.a : G) = (c.a : G) * t := by
    rintro _ ⟨t, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp t.2
  have hVTG : V ≤ TG := fun y hy => ⟨⟨y, hVC hy⟩, hT (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hne : TG ≠ ⊥ := fun e => by rw [e] at hTGcard; simp at hTGcard
  have hu' : u ∈ V := (mem_kleinFourSubgroup hu hv hc).mpr (Or.inr (Or.inl rfl))
  have hv' : v ∈ V := (mem_kleinFourSubgroup hu hv hc).mpr (Or.inr (Or.inr (Or.inl rfl)))
  rcases S.two_subgroup_centralizer_cases c.aG_cube c.aG_ne_one hTG2 hne hTGa with h | ⟨-, huniq⟩
  · rw [hTGcard] at h; omega
  · exact huv (huniq u (hVTG hu') v (hVTG hv') hu hv hu1 hv1)

theorem false_of_centralizing_inverting_pair {v w : G} (hv2 : v ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v ≠ w) (hva : v * (c.a : G) = (c.a : G) * v)
    (hwv : w * v = v * w) (hwa : w * (c.a : G) * w⁻¹ = (c.a : G)⁻¹) : False := by
  obtain ⟨k, hk⟩ := isConj_iff.mp (S.oneClass S.z v S.order_z (orderOf_eq_prime hv2 hv1))
  have key : ∀ y : G, y * v = v * y → k⁻¹ * y * k ∈ S.H := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k⁻¹ * y * k * S.z = k⁻¹ * y * (k * S.z * k⁻¹) * k := by group
      _ = k⁻¹ * (y * v) * k := by rw [hk]; group
      _ = k⁻¹ * (v * y) * k := by rw [hy]
      _ = S.z * (k⁻¹ * y * k) := by rw [← hk]; group
  let a' : S.H := ⟨k⁻¹ * (c.a : G) * k, key _ hva.symm⟩
  let w' : S.H := ⟨k⁻¹ * w * k, key _ hwv⟩
  have hconjpow : ∀ (g : G) (m : ℕ), (k⁻¹ * g * k) ^ m = k⁻¹ * g ^ m * k := fun g m => by
    simpa using conj_pow (a := k⁻¹) (b := g) (i := m)
  have ha'3 : a' ^ 3 = 1 := Subtype.ext (by
    show (k⁻¹ * (c.a : G) * k) ^ 3 = 1
    rw [hconjpow, c.aG_cube]; group)
  have hw'2 : w' ^ 2 = 1 := Subtype.ext (by
    show (k⁻¹ * w * k) ^ 2 = 1
    rw [hconjpow, hw2]; group)
  have ha'1 : a' ≠ 1 := fun e => c.aG_ne_one (by
    have h1 : k⁻¹ * (c.a : G) * k = 1 := congrArg Subtype.val e
    calc (c.a : G) = k * (k⁻¹ * (c.a : G) * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hw'1 : w' ≠ 1 := fun e => hw1 (by
    have h1 : k⁻¹ * w * k = 1 := congrArg Subtype.val e
    calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hw'z : w' ≠ zIn S.z := fun e => hvw (by
    have h1 : k⁻¹ * w * k = S.z := congrArg Subtype.val e
    calc v = k * S.z * k⁻¹ := hk.symm
      _ = k * (k⁻¹ * w * k) * k⁻¹ := by rw [h1]
      _ = w := by group)
  have hρa'1 : S.ρ a' ≠ 1 := by
    intro e
    rcases S.cover.mem_ker_iff.mp e with h1 | h1
    · exact ha'1 h1
    · rw [h1] at ha'3
      have : (zIn S.z) ^ 3 = zIn S.z := by rw [pow_succ, S.cover.sq_eq_one, one_mul]
      rw [this] at ha'3
      exact S.cover.ne_one ha'3
  have hρa'3 : (S.ρ a') ^ 3 = 1 := by rw [← map_pow, ha'3, map_one]
  have hcyc : (S.ρ a').cycleType = {3} := by
    rcases cycleType_of_cube_eq_one_ne_one hρa'3 hρa'1 with ht | ht
    · exact ht
    · exfalso
      exact S.not_isConj_type3_type33 c.ha3 ha'3 c.cycleType_a ht
        (isConj_iff.mpr ⟨k⁻¹, by show k⁻¹ * (c.a : G) * k⁻¹⁻¹ = k⁻¹ * (c.a : G) * k; simp⟩)
  have hs3 : (S.ρ a').support.card = 3 := by rw [← sum_cycleType, hcyc]; simp
  have hty := S.cover.type2222_of_involution hw'2 hw'1 hw'z
  have hfpf := fpf_of_type2222 hty
  have hinv : w' * a' * w'⁻¹ = a'⁻¹ := by
    apply Subtype.ext
    show k⁻¹ * w * k * (k⁻¹ * (c.a : G) * k) * (k⁻¹ * w * k)⁻¹ = (k⁻¹ * (c.a : G) * k)⁻¹
    calc k⁻¹ * w * k * (k⁻¹ * (c.a : G) * k) * (k⁻¹ * w * k)⁻¹
        = k⁻¹ * (w * (c.a : G) * w⁻¹) * k := by group
      _ = (k⁻¹ * (c.a : G) * k)⁻¹ := by rw [hwa]; group
  have hρinv : S.ρ w' * S.ρ a' * (S.ρ w')⁻¹ = (S.ρ a')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  have hρ2 : (S.ρ w') ^ 2 = 1 := by rw [← map_pow, hw'2, map_one]
  obtain ⟨x, hx⟩ := exists_fixed_of_inverts_of_odd_support hρ2 (by rw [hs3]; decide) hρinv
  exact hfpf x hx

theorem inf_centralizer_five_eq_bot
    {r : G}
    (hrNG : r ∈ c.NG) (hr5 : orderOf r = 5) : c.OG ⊓ centralizer ({r} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h81 := c.card_OG_eq_81
  have hrN : ∀ q ∈ c.OG, r * q * r⁻¹ ∈ c.OG := fun q hq => c.conj_mem_OG_of_mem_NG hrNG hq
  have hmod := card_modEq_card_inf_centralizer_of_pow_prime (Q := c.OG) (p := 5)
    (by rw [← hr5]; exact pow_orderOf_eq_one r) hrN
  have hdvd : Nat.card ↥(c.OG ⊓ centralizer ({r} : Set G)) ∣ 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num, ← h81]; exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hj3⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hj04 : j = 0 ∨ j = 4 := by
    rw [h81, hj3] at hmod
    unfold Nat.ModEq at hmod
    interval_cases j <;> simp_all
  rcases hj04 with h0 | h4
  · have : Nat.card ↥(c.OG ⊓ centralizer ({r} : Set G)) = 1 := by rw [hj3, h0]; rfl
    exact Subgroup.card_eq_one.mp this
  · exfalso
    have hfull : c.OG ⊓ centralizer ({r} : Set G) = c.OG := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      rw [hj3, h4, h81]; norm_num
    have hrO : r ∈ c.OG := c.centralizer_OG_le r (fun y hy => by
      have : y ∈ c.OG ⊓ centralizer ({r} : Set G) := by rw [hfull]; exact hy
      exact Subgroup.mem_centralizer_singleton_iff.mp this.2)
    have h1 := orderOf_dvd_natCard (⟨r, hrO⟩ : c.OG)
    rw [Subgroup.orderOf_mk, hr5, h81] at h1
    omega

theorem ocl_a_subset_OG :
    c.ocl (c.a : G) ⊆ (c.OG : Set G) :=
  c.ocl_subset_OG (c.PG_le_OG c.card_OG_eq_81 c.a_mem_PG)

theorem ne_one_of_mem_ocl_a {y : G} (hy : y ∈ c.ocl (c.a : G)) : y ≠ 1 := by
  obtain ⟨g, -, rfl⟩ := hy
  intro e
  apply c.aG_ne_one
  have h1 : g⁻¹ * (g * (c.a : G) * g⁻¹) * g = (c.a : G) := by group
  rw [e] at h1
  simpa using h1.symm

theorem five_dvd_card_ocl_a
    :
    5 ∣ Nat.card (c.ocl (c.a : G)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, hNG, -⟩ := c.lemma14
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.NG) 5 (by rw [hNG]; norm_num)
  have hr5 : orderOf (r : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hr
  have hX : ∀ y ∈ c.ocl (c.a : G), (r : G) * y * (r : G)⁻¹ ∈ c.ocl (c.a : G) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨(r : G) * g, c.NG.mul_mem r.2 hg, by group⟩
  have hf : (conjEnd hX) ^ 5 = 1 := by
    funext y
    apply Subtype.ext
    show (((conjEnd hX) ^ 5) y : G) = (y : G)
    have hr5' : (r : G) ^ 5 = 1 := by rw [← hr5]; exact pow_orderOf_eq_one _
    have := conjEnd_pow hX 5 y
    rw [hr5'] at this
    simpa using this
  have hfix : ∀ y, conjEnd hX y ≠ y := by
    intro y hy
    have hy' : (r : G) * (y : G) * (r : G)⁻¹ = (y : G) := congrArg Subtype.val hy
    have hyOG : (y : G) ∈ c.OG := c.ocl_a_subset_OG y.2
    have hyC : (y : G) ∈ centralizer ({(r : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * (r : G) = ((r : G) * (y : G) * (r : G)⁻¹) * (r : G) := by rw [hy']
        _ = (r : G) * (y : G) := by group
    have hbot := c.inf_centralizer_five_eq_bot r.2 hr5
    have : (y : G) ∈ c.OG ⊓ centralizer ({(r : G)} : Set G) := ⟨hyOG, hyC⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact c.ne_one_of_mem_ocl_a y.2 this
  exact dvd_card_of_fixed_point_free (conjEnd hX) hf hfix

theorem false_of_klein_four_normalizing_a {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hc : u * v = v * u)
    (hun : u ∈ normalizer (zpowers (c.a : G) : Set G))
    (hvn : v ∈ normalizer (zpowers (c.a : G) : Set G)) : False := by
  have hord : orderOf (c.a : G) = 3 := orderOf_eq_prime c.aG_cube c.aG_ne_one
  have hcomm : ∀ {y : G}, y * (c.a : G) * y⁻¹ = (c.a : G) → y * (c.a : G) = (c.a : G) * y :=
    fun {y} h => by
      calc y * (c.a : G) = (y * (c.a : G) * y⁻¹) * y := by group
        _ = (c.a : G) * y := by rw [h]
  have hu2' : u * u = 1 := by rwa [← pow_two]
  have hv2' : v * v = 1 := by rwa [← pow_two]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2'
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2'
  rcases conj_eq_or_inv_gen hord hun with hu' | hu'
  · rcases conj_eq_or_inv_gen hord hvn with hv' | hv'
    · exact c.false_of_klein_four_centralizing_a hu hv hu1 hv1 huv hc (hcomm hu') (hcomm hv')
    · exact c.false_of_centralizing_inverting_pair hu hv hu1 hv1 huv (hcomm hu') hc.symm hv'
  · rcases conj_eq_or_inv_gen hord hvn with hv' | hv'
    · exact c.false_of_centralizing_inverting_pair hv hu hv1 hu1 huv.symm (hcomm hv') hc hu'
    ·
      have huv2 : (u * v) ^ 2 = 1 := by
        rw [(show Commute u v from hc).mul_pow, hu, hv, one_mul]
      have huv1 : u * v ≠ 1 := fun h => huv (by
        have := eq_inv_of_mul_eq_one_right h
        exact (this.trans huinv).symm)
      have huvu : u * v ≠ u := fun h => hv1 (by
        have := congrArg (fun w => u⁻¹ * w) h
        simpa using this)
      have hcen : u * v * (c.a : G) * (u * v)⁻¹ = (c.a : G) := by
        calc u * v * (c.a : G) * (u * v)⁻¹ = u * (v * (c.a : G) * v⁻¹) * u⁻¹ := by group
          _ = u * (c.a : G)⁻¹ * u⁻¹ := by rw [hv']
          _ = (u * (c.a : G) * u⁻¹)⁻¹ := by group
          _ = (c.a : G) := by rw [hu', inv_inv]
      refine c.false_of_centralizing_inverting_pair huv2 hu huv1 hu1 huvu (hcomm hcen) ?_ hu'
      calc u * (u * v) = v := by rw [← mul_assoc, hu2', one_mul]
        _ = (u * v) * u := by
          calc v = u * (u * v) := by rw [← mul_assoc, hu2', one_mul]
            _ = u * (v * u) := by rw [← hc]
            _ = (u * v) * u := by group


theorem d_ne_z : (c.d : G) ≠ S.z := fun e => by
  have h1 : c.d = zIn S.z := Subtype.ext e
  have h2 := congrArg S.ρ h1
  rw [c.hd, S.cover.rho_z] at h2
  have h3 := congrArg Perm.cycleType h2
  rw [cycleType_permD, cycleType_one] at h3
  simp at h3

theorem card_ocl_a_ne_ten
    :
    Nat.card (c.ocl (c.a : G)) ≠ 10 := by
  intro hn10
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hNG, -⟩ := c.lemma14
  have hord : orderOf (c.a : G) = 3 := orderOf_eq_prime c.aG_cube c.aG_ne_one
  obtain ⟨e, heBg, hea⟩ := c.exists_mem_Bg_inv_a
  have heNG : e ∈ c.NG := c.Bg_le_NG heBg
  have hCacard : Nat.card (c.NG ⊓ centralizer ({(c.a : G)} : Set G) : Subgroup G) = 5832 := by
    have h := c.card_ocl_mul (c.a : G)
    rw [hn10, hNG] at h
    omega
  set U : Subgroup G := c.NG ⊓ normalizer (zpowers (c.a : G) : Set G) with hU
  have heU : e ∈ U := ⟨heNG, mem_normalizer_zpowers_of_inv hea⟩
  have hUCa : U ⊓ centralizer ({(c.a : G)} : Set G) = c.NG ⊓ centralizer ({(c.a : G)} : Set G) := by
    ext y
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, centralizer_le_normalizer_zpowers _ h2⟩, h2⟩
  have hUcard : Nat.card U = 2 * 5832 := by
    rw [card_eq_two_mul_inf_centralizer hord inf_le_right heU hea, hUCa, hCacard]
  have hf2U : (Nat.card U).factorization 2 = 4 := by
    rw [hUcard]
    have : (2 * 5832 : ℕ) = 2 ^ 4 * 729 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    have h729 : (729 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h729]
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥U) := inferInstance
  have hT₁ : Nat.card T₁ = 16 := by
    rw [T₁.card_eq_multiplicity, hf2U]; norm_num
  set T₁G : Subgroup G := (T₁ : Subgroup ↥U).map U.subtype with hT₁G
  have hT₁Gcard : Nat.card T₁G = 16 := by
    rw [hT₁G, Subgroup.card_map_of_injective U.subtype_injective]; exact hT₁
  have hT₁GU : T₁G ≤ U := Subgroup.map_subtype_le _
  have hT₁GNG : T₁G ≤ c.NG := hT₁GU.trans inf_le_left
  have hT₂card : Nat.card (T₁G.subgroupOf c.NG) = 2 ^ (Nat.card c.NG).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁GNG).toEquiv, hT₁Gcard,
      c.factorization_two_NG]; norm_num
  let T₂ : Sylow 2 ↥c.NG := Sylow.ofCard (T₁G.subgroupOf c.NG) hT₂card
  obtain ⟨g, hg⟩ := sylow_conj_mem c.SylBn T₂
  have hT₂mem : ∀ x : ↥c.NG, x ∈ (T₂ : Subgroup ↥c.NG) → (x : G) ∈ T₁G := fun x hx => by
    have : x ∈ T₁G.subgroupOf c.NG := by simpa [T₂] using hx
    exact Subgroup.mem_subgroupOf.mp this
  have hzB : c.zNG ∈ (c.SylBn : Subgroup ↥c.NG) := by
    rw [c.SylBn_coe]; exact Subgroup.mem_subgroupOf.mpr c.z_mem_Bg
  have hdNG : (c.d : G) ∈ c.NG := c.Bg_le_NG c.d_mem_Bg
  have hdB : (⟨(c.d : G), hdNG⟩ : ↥c.NG) ∈ (c.SylBn : Subgroup ↥c.NG) := by
    rw [c.SylBn_coe]; exact Subgroup.mem_subgroupOf.mpr c.d_mem_Bg
  have hzmem : g * c.zNG * g⁻¹ ∈ (T₂ : Subgroup ↥c.NG) := by
    rw [hg]
    have : g⁻¹ * (g * c.zNG * g⁻¹) * g = c.zNG := by group
    rw [this]; exact hzB
  have hdmem : g * (⟨(c.d : G), hdNG⟩ : ↥c.NG) * g⁻¹ ∈ (T₂ : Subgroup ↥c.NG) := by
    rw [hg]
    have : g⁻¹ * (g * (⟨(c.d : G), hdNG⟩ : ↥c.NG) * g⁻¹) * g = ⟨(c.d : G), hdNG⟩ := by group
    rw [this]; exact hdB
  set u : G := ((g * c.zNG * g⁻¹ : ↥c.NG) : G) with hu
  set v : G := ((g * (⟨(c.d : G), hdNG⟩ : ↥c.NG) * g⁻¹ : ↥c.NG) : G) with hv
  have hun : u ∈ normalizer (zpowers (c.a : G) : Set G) := (hT₁GU (hT₂mem _ hzmem)).2
  have hvn : v ∈ normalizer (zpowers (c.a : G) : Set G) := (hT₁GU (hT₂mem _ hdmem)).2
  have hu' : u = (g : G) * S.z * (g : G)⁻¹ := rfl
  have hv' : v = (g : G) * (c.d : G) * (g : G)⁻¹ := rfl
  have hd2 : (c.d : G) ^ 2 = 1 := by rw [pow_two]; exact c.dG_sq
  have hconj : ∀ (w : G) (m : ℕ), ((g : G) * w * (g : G)⁻¹) ^ m = (g : G) * w ^ m * (g : G)⁻¹ :=
    fun w m => by simp
  have hu2 : u ^ 2 = 1 := by rw [hu', hconj, z_sq (S := S)]; group
  have hv2 : v ^ 2 = 1 := by rw [hv', hconj, hd2]; group
  have hu1 : u ≠ 1 := fun e => z_ne_one' (S := S) (by
    have h1 : (g : G) * S.z * (g : G)⁻¹ = 1 := by rw [← hu']; exact e
    calc S.z = (g : G)⁻¹ * ((g : G) * S.z * (g : G)⁻¹) * (g : G) := by group
      _ = 1 := by rw [h1]; group)
  have hv1 : v ≠ 1 := fun e => by
    have h1 : (g : G) * (c.d : G) * (g : G)⁻¹ = 1 := by rw [← hv']; exact e
    have : (c.d : G) = 1 := by
      calc (c.d : G) = (g : G)⁻¹ * ((g : G) * (c.d : G) * (g : G)⁻¹) * (g : G) := by group
        _ = 1 := by rw [h1]; group
    exact c.d_ne_z (by
      have h3 : c.d = 1 := Subtype.ext this
      have h4 := congrArg S.ρ h3
      rw [c.hd, map_one] at h4
      have h5 := congrArg Perm.cycleType h4
      rw [cycleType_permD, cycleType_one] at h5
      simp at h5)
  have huv : u ≠ v := fun e => c.d_ne_z (by
    have h1 : (g : G) * S.z * (g : G)⁻¹ = (g : G) * (c.d : G) * (g : G)⁻¹ := by
      rw [← hu', ← hv']; exact e
    exact (mul_left_cancel (mul_right_cancel h1)).symm)
  have hc : u * v = v * u := by
    rw [hu', hv']
    calc (g : G) * S.z * (g : G)⁻¹ * ((g : G) * (c.d : G) * (g : G)⁻¹)
        = (g : G) * (S.z * (c.d : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((c.d : G) * S.z) * (g : G)⁻¹ := by rw [c.d_comm_z.symm]
      _ = (g : G) * (c.d : G) * (g : G)⁻¹ * ((g : G) * S.z * (g : G)⁻¹) := by group
  exact c.false_of_klein_four_normalizing_a hu2 hv2 hu1 hv1 huv hc hun hvn

theorem ocl_nonempty (x : G) : Nonempty (c.ocl x) :=
  ⟨⟨x, 1, c.NG.one_mem, by group⟩⟩

theorem ne_one_of_mem_ocl {x y : G} (hx : x ≠ 1) (hy : y ∈ c.ocl x) : y ≠ 1 := by
  obtain ⟨g, -, rfl⟩ := hy
  intro e
  apply hx
  have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e] at h1
  simpa using h1.symm

theorem factorization_58320 : (58320 : ℕ).factorization 2 = 4 := by
  have : (58320 : ℕ) = 2 ^ 4 * 3645 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  have h : (3645 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h]

theorem two_dvd_card_ocl_a
    :
    2 ∣ Nat.card (c.ocl (c.a : G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hNG, -⟩ := c.lemma14
  have h := c.card_ocl_mul (c.a : G)
  rw [hNG] at h
  set Ca' : Subgroup G := c.NG ⊓ centralizer ({(c.a : G)} : Set G) with hCa'
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥Ca') := inferInstance
  set TG : Subgroup G := (T : Subgroup ↥Ca').map Ca'.subtype with hTG
  have hTGa : ∀ t ∈ TG, t * (c.a : G) = (c.a : G) * t := by
    rintro _ ⟨t, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp t.2.2
  have hTG2 : IsPGroup 2 TG := T.isPGroup'.map _
  have hTGcard : Nat.card TG = 2 ^ (Nat.card Ca').factorization 2 := by
    rw [hTG, Subgroup.card_map_of_injective Ca'.subtype_injective, T.card_eq_multiplicity]
  have hdvd8 : Nat.card TG ∣ 8 := by
    by_cases hbot : TG = ⊥
    · rw [hbot]; simp
    · rcases S.two_subgroup_centralizer_cases c.aG_cube c.aG_ne_one hTG2 hbot hTGa with
        h4 | ⟨h8, -⟩
      · exact h4.trans (by norm_num)
      · exact h8
  have hf3 : (Nat.card Ca').factorization 2 ≤ 3 := by
    rw [hTGcard] at hdvd8
    have : 2 ^ (Nat.card Ca').factorization 2 ∣ 2 ^ 3 := by simpa using hdvd8
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hn0 : Nat.card (c.ocl (c.a : G)) ≠ 0 := by
    have := c.ocl_nonempty (c.a : G)
    exact Nat.card_pos.ne'
  have := congrArg (fun m => m.factorization 2) h
  simp only [Nat.factorization_mul hn0 Nat.card_pos.ne', Finsupp.add_apply, factorization_58320]
    at this
  exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn0).mpr (by omega)

theorem ocl_s_subset_OG : c.ocl c.s ⊆ (c.OG : Set G) :=
  c.ocl_subset_OG (c.zpowers_le_OG (Subgroup.mem_zpowers c.s))

theorem card_ocl_a_le
    :
    Nat.card (c.ocl (c.a : G)) ≤ 20 := by
  have hs := c.card_ocl_s
  have hdisj : Disjoint (c.ocl (c.a : G)) (c.ocl c.s) := by
    rw [Set.disjoint_left]
    rintro y ⟨g, hg, hy1⟩ ⟨h, hh, hy2⟩
    refine S.not_isConj_type3_type33 c.ha3 c.x_cube c.cycleType_a c.x_type
      (isConj_iff.mpr ⟨h⁻¹ * g, ?_⟩)
    have hgh : g * (c.a : G) * g⁻¹ = h * c.s * h⁻¹ := hy1.symm.trans hy2
    show h⁻¹ * g * (c.a : G) * (h⁻¹ * g)⁻¹ = c.s
    calc h⁻¹ * g * (c.a : G) * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * (c.a : G) * g⁻¹) * h := by group
      _ = h⁻¹ * (h * c.s * h⁻¹) * h := by rw [hgh]
      _ = c.s := by group
  have hsub : c.ocl (c.a : G) ∪ c.ocl c.s ⊆ ((c.OG : Set G) \ {1}) := by
    rintro y (hy | hy)
    · exact ⟨c.ocl_a_subset_OG hy, c.ne_one_of_mem_ocl c.aG_ne_one hy⟩
    · exact ⟨c.ocl_s_subset_OG hy, c.ne_one_of_mem_ocl c.s_ne_one hy⟩
  have hfin : ((c.OG : Set G) \ {1}).Finite := Set.toFinite _
  have h1 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at h1
  have h2 : ((c.OG : Set G) \ {1}).ncard = 80 := by
    rw [Set.ncard_sdiff_singleton_of_mem c.OG.one_mem]
    have h81 := c.card_OG_eq_81
    have : (c.OG : Set G).ncard = 81 := by rw [← Nat.card_coe_set_eq]; exact h81
    omega
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h1
  rw [hs] at h1
  omega

theorem card_ocl_a
    :
    Nat.card (c.ocl (c.a : G)) = 20 := by
  have h5 := c.five_dvd_card_ocl_a
  have h2 := c.two_dvd_card_ocl_a
  have hle := c.card_ocl_a_le
  have hne := c.card_ocl_a_ne_ten
  have hpos : 0 < Nat.card (c.ocl (c.a : G)) := by
    have := c.ocl_nonempty (c.a : G)
    exact Nat.card_pos
  omega

theorem factorization_three_58320 : (58320 : ℕ).factorization 3 = 6 := by
  have : (58320 : ℕ) = 3 ^ 6 * 80 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  have h : (80 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h]

theorem card_NG_inf_centralizer_a
    :
    Nat.card (c.NG ⊓ centralizer ({(c.a : G)} : Set G) : Subgroup G) = 2916 := by
  obtain ⟨-, -, hNG, -⟩ := c.lemma14
  have h := c.card_ocl_mul (c.a : G)
  rw [c.card_ocl_a, hNG] at h
  omega

theorem exists_sylow_three_NG
    :
    ∃ W : Subgroup G, IsPGroup 3 W ∧ Nat.card W = 3 ^ 6 ∧ c.OG ≤ W ∧ W ≤ c.NG ∧
      (∀ w ∈ W, w * (c.a : G) = (c.a : G) * w) ∧
      ∀ R : Subgroup G, R ≤ c.NG → IsPGroup 3 R → Nat.card R ≤ 3 ^ 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hNG, -⟩ := c.lemma14
  set Ca' : Subgroup G := c.NG ⊓ centralizer ({(c.a : G)} : Set G) with hCa'
  have hCa'NG : Ca' ≤ c.NG := inf_le_left
  have hCacard : Nat.card Ca' = 2916 := c.card_NG_inf_centralizer_a
  have hf3 : (Nat.card Ca').factorization 3 = 6 := by
    rw [hCacard]
    have : (2916 : ℕ) = 3 ^ 6 * 4 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three]
    have h : (4 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h]
  obtain ⟨W₀⟩ : Nonempty (Sylow 3 ↥Ca') := inferInstance
  set W₁ : Subgroup G := (W₀ : Subgroup ↥Ca').map Ca'.subtype with hW₁
  have hW₁card : Nat.card W₁ = 3 ^ 6 := by
    rw [hW₁, Subgroup.card_map_of_injective Ca'.subtype_injective, W₀.card_eq_multiplicity, hf3]
  have hW₁NG : W₁ ≤ c.NG := (Subgroup.map_subtype_le _).trans hCa'NG
  have hW₁p : IsPGroup 3 W₁ := W₀.isPGroup'.map _
  have hW₁' : IsPGroup 3 (W₁.subgroupOf c.NG) :=
    hW₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hW₁NG).symm
  obtain ⟨W₂, hW₂⟩ := hW₁'.exists_le_sylow
  have hf3NG : (Nat.card c.NG).factorization 3 = 6 := by rw [hNG]; exact factorization_three_58320
  have hW₂card : Nat.card W₂ = 3 ^ 6 := by rw [W₂.card_eq_multiplicity, hf3NG]
  set W : Subgroup G := (W₂ : Subgroup ↥c.NG).map c.NG.subtype with hW
  have hWcard : Nat.card W = 3 ^ 6 := by
    rw [hW, Subgroup.card_map_of_injective c.NG.subtype_injective, hW₂card]
  have hWle : W₁ ≤ W := by
    intro y hy
    exact ⟨⟨y, hW₁NG hy⟩, hW₂ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hWeq : W₁ = W := Subgroup.eq_of_le_of_card_ge hWle (by rw [hWcard, hW₁card])
  refine ⟨W, W₂.isPGroup'.map _, hWcard, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  ·
    have hOn : (c.OG.subgroupOf c.NG).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer c.OG_le_NG).mpr (le_refl _)
    have hOp : IsPGroup 3 (c.OG.subgroupOf c.NG) :=
      c.isPGroup_three_OG.of_equiv (Subgroup.subgroupOfEquivOfLe c.OG_le_NG).symm
    have := hOp.le_sylow_of_normal W₂
    intro y hy
    exact ⟨⟨y, c.OG_le_NG hy⟩, this (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · intro w hw
    rw [← hWeq] at hw
    obtain ⟨w', -, rfl⟩ := hw
    exact Subgroup.mem_centralizer_singleton_iff.mp w'.2.2
  · intro R hR hRp
    have hR' : IsPGroup 3 (R.subgroupOf c.NG) :=
      hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
    obtain ⟨T, hT⟩ := hR'.exists_le_sylow
    have hTcard : Nat.card T = 3 ^ 6 := by rw [T.card_eq_multiplicity, hf3NG]
    have := Subgroup.card_le_of_le hT
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv, hTcard] at this
    exact this

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
