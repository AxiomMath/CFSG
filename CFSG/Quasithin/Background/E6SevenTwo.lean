module

public import CFSG.Quasithin.Background.E6TenBlock

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_zpow_of_mem {U : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (U : Set G))
    {x : G} (hx : x ∈ U ⊔ Subgroup.zpowers c) : ∃ u ∈ U, ∃ k : ℤ, x = u * c ^ k := by
  have hset : ((U ⊔ Subgroup.zpowers c : Subgroup G) : Set G) =
      (U : Set G) * (Subgroup.zpowers c : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U _ (Subgroup.zpowers_le.2 hcN)
  have hx' : x ∈ ((U ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨u, hu, y, ⟨k, rfl⟩, rfl⟩ := hx'
  exact ⟨u, hu, k, rfl⟩

theorem exists_inner_of_alt3 {U : Subgroup G} {c g : G} (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU1 : U ≠ ⊥) (hc3 : orderOf c = 3) (hcN : c ∈ Subgroup.normalizer (U : Set G))
    (hcfix : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u)
    (hgN : g ∈ Subgroup.normalizer ((U ⊔ Subgroup.zpowers c : Subgroup G) : Set G))
    (hgU : ∀ u ∈ U, g * u = u * g) :
    ∃ u ∈ U, ∀ l ∈ U ⊔ Subgroup.zpowers c, g * l * g⁻¹ = u * l * u⁻¹ := by
  have hgc : g * c * g⁻¹ ∈ U ⊔ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.1 hgN c).1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  obtain ⟨u₀, hu₀, k, hk⟩ := exists_mul_zpow_of_mem hcN hgc
  have hact : ∀ u ∈ U, c ^ (k - 1) * u * (c ^ (k - 1))⁻¹ = u := by
    intro u hu
    have hcu : c * u * c⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hcN u).1 hu
    have h1 : (g * c * g⁻¹) * u * (g * c * g⁻¹)⁻¹ = c * u * c⁻¹ := by
      have e : (g * c * g⁻¹) * u * (g * c * g⁻¹)⁻¹ = g * (c * (g⁻¹ * u * g) * c⁻¹) * g⁻¹ := by
        group
      have hgu : g⁻¹ * u * g = u := by rw [mul_assoc, ← hgU u hu, inv_mul_cancel_left]
      rw [e, hgu, hgU _ hcu, mul_inv_cancel_right]
    have hckN : c ^ k ∈ Subgroup.normalizer (U : Set G) := Subgroup.zpow_mem _ hcN k
    have hcku : c ^ k * u * (c ^ k)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hckN u).1 hu
    have h2 : (u₀ * c ^ k) * u * (u₀ * c ^ k)⁻¹ = c ^ k * u * (c ^ k)⁻¹ := by
      have e : (u₀ * c ^ k) * u * (u₀ * c ^ k)⁻¹ = u₀ * (c ^ k * u * (c ^ k)⁻¹) * u₀⁻¹ := by
        group
      rw [e, hUc u₀ hu₀ _ hcku, mul_inv_cancel_right]
    rw [hk] at h1
    rw [h2] at h1
    have e : c ^ (k - 1) * u * (c ^ (k - 1))⁻¹ = c⁻¹ * (c ^ k * u * (c ^ k)⁻¹) * c := by
      rw [zpow_sub_one]
      group
    rw [e, h1]
    group
  have hck : c ^ (k - 1) = 1 := by
    by_contra hne
    have hcmem : c ∈ Subgroup.zpowers (c ^ (k - 1)) := by
      have hp : (orderOf c).Prime := by rw [hc3]; norm_num
      have h1 : orderOf (c ^ (k - 1)) = 3 := by
        have hd : orderOf (c ^ (k - 1)) ∣ 3 := by
          rw [← hc3]
          exact orderOf_dvd_of_pow_eq_one (by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
              pow_orderOf_eq_one, one_zpow])
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hd with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hne
        · exact h
      have hle : Subgroup.zpowers (c ^ (k - 1)) ≤ Subgroup.zpowers c :=
        Subgroup.zpowers_le.2 (Subgroup.zpow_mem_zpowers c _)
      have hcard : Nat.card (Subgroup.zpowers c) ≤ Nat.card (Subgroup.zpowers (c ^ (k - 1))) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, h1, hc3]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm ▸ Subgroup.mem_zpowers c
    obtain ⟨m, hm⟩ := hcmem
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    apply hcfix u hu (fun h => hu1 (Subtype.ext h))
    have hpow : ∀ j : ℤ, ∀ w ∈ U, (c ^ (k - 1)) ^ j * w * ((c ^ (k - 1)) ^ j)⁻¹ = w := by
      intro j
      induction j using Int.induction_on with
      | zero => intro w _; simp
      | succ i ih =>
        intro w hw
        have hw' : c ^ (k - 1) * w * (c ^ (k - 1))⁻¹ = w := hact w hw
        calc (c ^ (k - 1)) ^ ((i : ℤ) + 1) * w * ((c ^ (k - 1)) ^ ((i : ℤ) + 1))⁻¹
            = (c ^ (k - 1)) ^ (i : ℤ) * (c ^ (k - 1) * w * (c ^ (k - 1))⁻¹) *
                ((c ^ (k - 1)) ^ (i : ℤ))⁻¹ := by rw [zpow_add_one]; group
          _ = w := by rw [hw', ih w hw]
      | pred i ih =>
        intro w hw
        have hw' : (c ^ (k - 1))⁻¹ * w * c ^ (k - 1) = w := by
          have := hact w hw
          calc (c ^ (k - 1))⁻¹ * w * c ^ (k - 1)
              = (c ^ (k - 1))⁻¹ * (c ^ (k - 1) * w * (c ^ (k - 1))⁻¹) * c ^ (k - 1) := by
                rw [this]
            _ = w := by group
        calc (c ^ (k - 1)) ^ (-(i : ℤ) - 1) * w * ((c ^ (k - 1)) ^ (-(i : ℤ) - 1))⁻¹
            = (c ^ (k - 1)) ^ (-(i : ℤ)) * ((c ^ (k - 1))⁻¹ * w * c ^ (k - 1)) *
                ((c ^ (k - 1)) ^ (-(i : ℤ)))⁻¹ := by rw [zpow_sub_one]; group
          _ = w := by rw [hw', ih w hw]
    have hm' : (c ^ (k - 1)) ^ m = c := hm
    have := hpow m (u : G) hu
    rwa [hm'] at this
  have hck' : c ^ k = c := by
    have : c ^ k = c ^ (k - 1) * c := by rw [← zpow_add_one, sub_add_cancel]
    rw [this, hck, one_mul]
  rw [hck'] at hk
  let φ : ↥U →* ↥U :=
    { toFun := fun u => ⟨(u : G) * (c * u * c⁻¹)⁻¹,
        U.mul_mem u.2 (U.inv_mem ((Subgroup.mem_normalizer_iff.1 hcN u).1 u.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have ha := (Subgroup.mem_normalizer_iff.1 hcN a).1 a.2
        have hb := (Subgroup.mem_normalizer_iff.1 hcN b).1 b.2
        show (a : G) * b * (c * (a * b) * c⁻¹)⁻¹ = (a : G) * (c * a * c⁻¹)⁻¹ * (b * (c * b * c⁻¹)⁻¹)
        have e : c * ((a : G) * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        have hx := U.inv_mem ha
        have hy := U.inv_mem hb
        rw [e, mul_inv_rev]
        calc (a : G) * b * ((c * b * c⁻¹)⁻¹ * (c * a * c⁻¹)⁻¹)
            = a * (b * ((c * b * c⁻¹)⁻¹ * (c * a * c⁻¹)⁻¹)) := by rw [mul_assoc]
          _ = a * (b * ((c * a * c⁻¹)⁻¹ * (c * b * c⁻¹)⁻¹)) := by rw [hUc _ hy _ hx]
          _ = a * ((b * (c * a * c⁻¹)⁻¹) * (c * b * c⁻¹)⁻¹) := by rw [mul_assoc (b : G)]
          _ = a * (((c * a * c⁻¹)⁻¹ * b) * (c * b * c⁻¹)⁻¹) := by rw [hUc b b.2 _ hx]
          _ = a * (c * a * c⁻¹)⁻¹ * (b * (c * b * c⁻¹)⁻¹) := by group) }
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : G) * (c * u * c⁻¹)⁻¹ = 1 := congrArg Subtype.val hu
    have h2 : c * (u : G) * c⁻¹ = u := (mul_inv_eq_one.1 h1).symm
    by_contra hne
    exact hcfix u u.2 (fun h => hne (Subtype.ext h)) h2
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hφinj
  obtain ⟨u, hu⟩ := hφsurj ⟨u₀, hu₀⟩
  have huc : (u : G) * c * (u : G)⁻¹ = u₀ * c := by
    have h1 : (u : G) * (c * u * c⁻¹)⁻¹ = u₀ := congrArg Subtype.val hu
    rw [← h1]
    group
  refine ⟨u, u.2, ?_⟩
  let X : Subgroup G :=
    { carrier := {l | g * l * g⁻¹ = u * l * (u : G)⁻¹}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        show g * (a * b) * g⁻¹ = u * (a * b) * (u : G)⁻¹
        calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          _ = (u * a * (u : G)⁻¹) * (u * b * (u : G)⁻¹) := by rw [ha, hb]
          _ = u * (a * b) * (u : G)⁻¹ := by group
      inv_mem' := fun {a} ha => by
        show g * a⁻¹ * g⁻¹ = u * a⁻¹ * (u : G)⁻¹
        calc g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          _ = (u * a * (u : G)⁻¹)⁻¹ := by rw [ha]
          _ = u * a⁻¹ * (u : G)⁻¹ := by group }
  have hle : U ⊔ Subgroup.zpowers c ≤ X := by
    refine sup_le (fun w hw => ?_) (Subgroup.zpowers_le.2 ?_)
    · show g * w * g⁻¹ = u * w * (u : G)⁻¹
      rw [hgU w hw, hUc u u.2 w hw, mul_inv_cancel_right, mul_inv_cancel_right]
    · show g * c * g⁻¹ = u * c * (u : G)⁻¹
      rw [hk, huc]
  exact fun l hl => hle hl

omit [Finite G] in
theorem eq_of_ne_one_of_card_le_two {X : Type*} [Group X] [Finite X] (h : Nat.card X ≤ 2)
    {x y : X} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  by_contra hxy
  let f : Fin 3 → X := fun i => if i = 0 then 1 else if i = 1 then x else y
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij
    all_goals first
      | rfl
      | (exfalso; simp only [Fin.reduceFinMk, Fin.isValue, ↓reduceIte] at hij
         first
          | exact hx hij.symm | exact hx hij | exact hy hij.symm | exact hy hij
          | exact hxy hij | exact hxy hij.symm)
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem relIndex_le_two_of_alt3 {K L Q V : Subgroup G} (hK : CharTwo K) (hL : IsBlock2 K L)
    (h3 : IsAltType L 3) (hQ : IsSylowTwoOf Q K) (hJ : L = ⁅L, thompsonJ Q⁆) (hVQ : V ≤ Q)
    (hQV : Q ≤ Subgroup.centralizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQU, hU4, hUsq, hUc, hL12, hZ, c, hcL, hc3, hcN, hcfix, hLeq⟩ :=
    IsShort2.alt3_structure hL.1 h3
  set U := blockU L with hUdef
  have hUL : U ≤ L := (C1.blockU_le_blockQ hL.1).trans (C1.blockQ_le L)
  have hUQ : U ≤ Q := by
    rw [← hQU]
    exact (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hL.2.1 hL.2.2).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQ)
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hU4
    norm_num at hU4
  have hUsyl : IsSylowTwoOf U L := by
    refine ⟨hUL, hQ.2.1.to_le hUQ, ?_⟩
    have h1 := Subgroup.relIndex_mul_card U L
    rw [inf_eq_left.2 hUL, hU4, hL12] at h1
    have h3' : U.relIndex L = 3 := by omega
    rw [← Subgroup.relIndex, h3']
    decide
  have hVU : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu =>
    (Subgroup.mem_centralizer_iff.1 (hQV (hUQ hu)) v hv)
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := fun v hv =>
    mem_normalizer_of_commute_sylow hK hL hUsyl (hQ.1 (hVQ hv)) (hVU v hv)
  rw [hLeq] at hVN
  have hinner : ∀ v ∈ V, ∃ u ∈ U, ∀ l ∈ U ⊔ Subgroup.zpowers c, v * l * v⁻¹ = u * l * u⁻¹ :=
    fun v hv => exists_inner_of_alt3 hUc hU1 hc3 hcN hcfix (hVN v hv) (hVU v hv)
  have huniq : ∀ a ∈ U, ∀ b ∈ U, (∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹) → a = b := by
    intro a ha b hb hab
    have h1 := hZ (b⁻¹ * a) (L.mul_mem (L.inv_mem (hUL hb)) (hUL ha)) fun l hl => by
      have := hab l hl
      calc b⁻¹ * a * l = b⁻¹ * (a * l * a⁻¹) * a := by group
        _ = b⁻¹ * (b * l * b⁻¹) * a := by rw [this]
        _ = l * (b⁻¹ * a) := by group
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  have hJN : thompsonJ Q ≤ Subgroup.normalizer (L : Set G) := by
    intro q hq
    have h1 := A3.sup_le_normalizer_commutator L (thompsonJ Q) (Subgroup.mem_sup_right hq)
    rwa [← hJ] at h1
  obtain ⟨q, hqJ, hqU⟩ : ∃ q ∈ thompsonJ Q, ∃ u ∈ U, q * u * q⁻¹ ≠ u := by
    by_contra hall
    push Not at hall
    have hc : ∀ q ∈ thompsonJ Q, ∀ l ∈ L, l * q * l⁻¹ * q⁻¹ ∈ U := by
      intro q hq
      have hqN : q ∈ Subgroup.normalizer ((U ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := by
        rw [← hLeq]; exact hJN hq
      have hqU : ∀ u ∈ U, q * u = u * q := fun u hu => by
        have := hall q hq u hu
        calc q * u = (q * u * q⁻¹) * q := by group
          _ = u * q := by rw [this]
      obtain ⟨w, hw, hwl⟩ := exists_inner_of_alt3 hUc hU1 hc3 hcN hcfix hqN hqU
      intro l hl
      rw [hLeq] at hl
      have e : l * q * l⁻¹ * q⁻¹ = l * (q * l * q⁻¹)⁻¹ := by group
      rw [e, hwl l hl]
      obtain ⟨u, hu, k, rfl⟩ := exists_mul_zpow_of_mem hcN hl
      have hckN : c ^ k ∈ Subgroup.normalizer (U : Set G) := Subgroup.zpow_mem _ hcN k
      have e2 : u * c ^ k * (w * (u * c ^ k) * w⁻¹)⁻¹ =
          u * (c ^ k * w * (c ^ k)⁻¹) * u⁻¹ * w⁻¹ := by group
      rw [e2]
      exact U.mul_mem (U.mul_mem (U.mul_mem hu ((Subgroup.mem_normalizer_iff.1 hckN w).1 hw))
        (U.inv_mem hu)) (U.inv_mem hw)
    have hle : L ≤ U := by
      calc L = ⁅L, thompsonJ Q⁆ := hJ
        _ ≤ U := by
          rw [Subgroup.commutator_le]
          intro l hl q hq
          rw [commutatorElement_def]
          exact hc q hq l hl
    have := Subgroup.card_le_of_le hle
    rw [hU4, hL12] at this
    norm_num at this
  obtain ⟨u₁, hu₁, hqu₁⟩ := hqU
  have hqQ : q ∈ Q := thompsonJ_le_self Q hqJ
  have hqNL : q ∈ Subgroup.normalizer (L : Set G) := hJN hqJ
  have hqNU : q ∈ Subgroup.normalizer (U : Set G) := C1.mem_normalizer_blockU hqNL
  set CU := U ⊓ Subgroup.centralizer ({q} : Set G) with hCUdef
  have hCU2 : Nat.card CU ≤ 2 := by
    have hlt : CU < U := by
      refine lt_of_le_of_ne inf_le_left fun he => hqu₁ ?_
      have : u₁ ∈ CU := he ▸ hu₁
      rw [← Subgroup.mem_centralizer_singleton_iff.1 this.2, mul_inv_cancel_right]
    have hdvd := Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card CU ≠ Nat.card U := fun he =>
      (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge hlt.le he.ge)
    rw [hU4] at hdvd hne
    have h4 : Nat.card CU ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [this] at h4
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    omega
  have hinner' : ∀ v ∈ V, ∃ u ∈ CU, ∀ l ∈ L, v * l * v⁻¹ = u * l * u⁻¹ := by
    intro v hv
    obtain ⟨u, hu, hul⟩ := hinner v hv
    have hul' : ∀ l ∈ L, v * l * v⁻¹ = u * l * u⁻¹ := fun l hl => hul l (hLeq ▸ hl)
    refine ⟨u, Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hul'⟩
    have hqu : q * u * q⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hqNU u).1 hu
    have hvq : q * v = v * q := (Subgroup.mem_centralizer_iff.1 (hQV hqQ) v hv).symm
    have key := huniq (q * u * q⁻¹) hqu u hu fun l hl => by
      have hql : q⁻¹ * l * q ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hqNL) l).1 hl
        simpa using this
      have h1 := hul' _ hql
      have hvq' : v = q⁻¹ * v * q := by rw [mul_assoc, ← hvq, inv_mul_cancel_left]
      calc q * u * q⁻¹ * l * (q * u * q⁻¹)⁻¹ = q * (u * (q⁻¹ * l * q) * u⁻¹) * q⁻¹ := by group
        _ = q * (v * (q⁻¹ * l * q) * v⁻¹) * q⁻¹ := by rw [h1]
        _ = (q * v * q⁻¹) * l * (q * v * q⁻¹)⁻¹ := by group
        _ = v * l * v⁻¹ := by rw [hvq, mul_inv_cancel_right]
        _ = u * l * u⁻¹ := hul' l hl
    symm
    calc q * u = (q * u * q⁻¹) * q := by group
      _ = u * q := by rw [key]
  have htwo : ∀ v₁ ∈ V, ∀ v₂ ∈ V, v₁ ∉ Subgroup.centralizer (L : Set G) →
      v₂ ∉ Subgroup.centralizer (L : Set G) → v₁⁻¹ * v₂ ∈ Subgroup.centralizer (L : Set G) := by
    intro v₁ hv₁ v₂ hv₂ hn₁ hn₂
    obtain ⟨a, ha, hal⟩ := hinner' v₁ hv₁
    obtain ⟨b, hb, hbl⟩ := hinner' v₂ hv₂
    have hne1 : ∀ {w x : G}, x ∈ CU → w ∉ Subgroup.centralizer (L : Set G) →
        (∀ l ∈ L, w * l * w⁻¹ = x * l * x⁻¹) → x ≠ 1 := by
      intro w x _ hw hxl hx1
      apply hw
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := hxl l hl
      rw [hx1] at this
      simp only [one_mul, inv_one, mul_one] at this
      calc l * w = (w * l * w⁻¹) * w := by rw [this]
        _ = w * l := by group
    have ha1 := hne1 ha hn₁ hal
    have hb1 := hne1 hb hn₂ hbl
    have hab : a = b := by
      have := eq_of_ne_one_of_card_le_two hCU2 (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)
        (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
    subst hab
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hal l hl
    have h2 := hbl l hl
    calc l * (v₁⁻¹ * v₂) = v₁⁻¹ * (v₁ * l * v₁⁻¹) * v₂ := by group
      _ = v₁⁻¹ * (v₂ * l * v₂⁻¹) * v₂ := by rw [h1, h2]
      _ = v₁⁻¹ * v₂ * l := by group
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  by_cases hVC : V ≤ Subgroup.centralizer (L : Set G)
  · have hCV : C = V := inf_eq_left.2 hVC
    rw [hCV, Subgroup.relIndex_self]
    norm_num
  obtain ⟨v₀, hv₀, hv₀C⟩ := Set.not_subset.1 hVC
  have hsurj : Function.Surjective (fun p : Bool × ↥C =>
      (⟨if p.1 then v₀ * p.2 else p.2, by
        rcases p with ⟨b, x⟩
        cases b
        · exact x.2.1
        · exact V.mul_mem hv₀ x.2.1⟩ : ↥V)) := by
    rintro ⟨v, hv⟩
    by_cases hvC : v ∈ Subgroup.centralizer (L : Set G)
    · exact ⟨(false, ⟨v, hv, hvC⟩), rfl⟩
    · refine ⟨(true, ⟨v₀⁻¹ * v, V.mul_mem (V.inv_mem hv₀) hv, htwo v₀ hv₀ v hv hv₀C hvC⟩), ?_⟩
      apply Subtype.ext
      show v₀ * (v₀⁻¹ * v) = v
      group
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
  have h1 := Subgroup.relIndex_mul_card C V
  rw [inf_eq_left.2 (inf_le_left : C ≤ V)] at h1
  have hpos : 0 < Nat.card C := Nat.card_pos
  have h2 : C.relIndex V * Nat.card C ≤ 2 * Nat.card C := by rw [h1]; exact hcard
  exact Nat.le_of_mul_le_mul_right h2 hpos

end E6
end CFSG.Quasithin
