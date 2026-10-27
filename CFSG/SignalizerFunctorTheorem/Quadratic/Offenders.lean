module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
public import CFSG.SignalizerFunctorTheorem.Quadratic.PrimeCore
public import CFSG.SignalizerFunctorTheorem.Quadratic.Hyperplane
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fact p.Prime] [Finite V]
  {H : Subgroup (LGL p V)}

theorem le_normalizer_Qp {A : Subgroup (LGL p V)} (hA : A ≤ H) :
    A ≤ Subgroup.normalizer (Qp p H : Set (LGL p V)) :=
  hA.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (Qp_le (p := p) H)).mp
    (Qp_normal (p := p) H))

omit [Fact p.Prime] in
theorem eq_one_of_pow_eq_one_of_coprime {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (hg : g ∈ S) (hS : Nat.Coprime p (Nat.card S)) (h : g ^ p = 1) : g = 1 := by
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf g ∣ Nat.card S := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : S)
    rwa [Subgroup.orderOf_mk g hg] at this
  have h3 : orderOf g ∣ Nat.gcd p (Nat.card S) := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hS] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem eq_bot_of_le_Qp {A : Subgroup (LGL p V)} (hA : IsElemAb p A) (h : A ≤ Qp p H) :
    A = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  exact eq_one_of_pow_eq_one_of_coprime (h ha) (coprime_card_Qp (p := p) H) (hA.2 a ha)

theorem exists_hyperplane_not_le (hH : Hyp H) {A : Subgroup (LGL p V)} (hA : IsAV H A)
    (hA1 : A ≠ ⊥) :
    ∃ B : Subgroup (LGL p V), B ≤ A ∧ Nat.card A = p * Nat.card B ∧
      ¬ (Qp p H ⊓ Subgroup.centralizer (B : Set (LGL p V)) ≤
          Subgroup.centralizer (A : Set (LGL p V))) := by
  by_contra hcon
  have hall : ∀ B : Subgroup (LGL p V), B ≤ A → Nat.card A = p * Nat.card B →
      Qp p H ⊓ Subgroup.centralizer (B : Set (LGL p V)) ≤
        Subgroup.centralizer (A : Set (LGL p V)) :=
    fun B hBA hBc => by_contra fun hBQ => hcon ⟨B, hBA, hBc, hBQ⟩
  have hcover := hyperplane_cover hA.2.1 hA1 (coprime_card_Qp (p := p) H) (le_normalizer_Qp hA.1)
  have hQ : Qp p H ≤ Subgroup.centralizer (A : Set (LGL p V)) :=
    hcover.trans (iSup₂_le fun B hB => hall B hB.1 hB.2)
  have hAQ : A ≤ Qp p H := by
    intro a ha
    have hac : a ∈ Subgroup.centralizer (Qp p H : Set (LGL p V)) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        ((Subgroup.mem_centralizer_iff.mp (hQ hq)) a ha).symm
    exact hH.centralizer_le_Qp ⟨hA.1 ha, hac⟩
  exact hA1 (eq_bot_of_le_Qp hA.2.1 hAQ)

theorem exists_two_hyperplanes_not_le (hH : Hyp H) {A : Subgroup (LGL p V)} (hA : IsAV H A)
    (hAp : p < Nat.card A) :
    ∃ B₁ B₂ : Subgroup (LGL p V), B₁ ≤ A ∧ B₂ ≤ A ∧ B₁ ≠ B₂ ∧
      Nat.card A = p * Nat.card B₁ ∧ Nat.card A = p * Nat.card B₂ ∧
      ¬ (Qp p H ⊓ Subgroup.centralizer (B₁ : Set (LGL p V)) ≤
          Subgroup.centralizer (A : Set (LGL p V))) ∧
      ¬ (Qp p H ⊓ Subgroup.centralizer (B₂ : Set (LGL p V)) ≤
          Subgroup.centralizer (A : Set (LGL p V))) := by
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hAp
    exact absurd hAp (not_lt.mpr (Fact.out : p.Prime).one_lt.le)
  obtain ⟨B₀, hB₀A, hB₀c, hB₀Q⟩ := exists_hyperplane_not_le hH hA hA1
  by_contra hcon
  have key : ∀ B : Subgroup (LGL p V), B ≤ A → Nat.card A = p * Nat.card B →
      ¬ (Qp p H ⊓ Subgroup.centralizer (B : Set (LGL p V)) ≤
          Subgroup.centralizer (A : Set (LGL p V))) → B = B₀ := by
    intro B hBA hBc hBQ
    by_contra hne
    exact hcon ⟨B, B₀, hBA, hB₀A, hne, hBc, hB₀c, hBQ, hB₀Q⟩
  have hcover := hyperplane_cover hA.2.1 hA1 (coprime_card_Qp (p := p) H) (le_normalizer_Qp hA.1)
  have hQ : Qp p H ≤ Subgroup.centralizer (B₀ : Set (LGL p V)) := by
    refine hcover.trans (iSup₂_le fun B hB => ?_)
    by_cases hBQ : Qp p H ⊓ Subgroup.centralizer (B : Set (LGL p V)) ≤
        Subgroup.centralizer (A : Set (LGL p V))
    · exact hBQ.trans (Subgroup.centralizer_le (by exact_mod_cast hB₀A))
    · rw [key B hB.1 hB.2 hBQ]
      exact inf_le_right
  have hB₀Q' : B₀ ≤ Qp p H := by
    intro a ha
    have hac : a ∈ Subgroup.centralizer (Qp p H : Set (LGL p V)) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        ((Subgroup.mem_centralizer_iff.mp (hQ hq)) a ha).symm
    exact hH.centralizer_le_Qp ⟨hA.1 (hB₀A ha), hac⟩
  have hB₀bot : B₀ = ⊥ := eq_bot_of_le_Qp (hA.2.1.mono hB₀A) hB₀Q'
  rw [hB₀bot, Subgroup.card_bot, mul_one] at hB₀c
  omega

theorem IsElemAb.comm_mem {p : ℕ} {G : Type*} [Group G] {A : Subgroup G} (hA : IsElemAb p A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm hA ha hb

theorem key_hyperplane (_hH : Hyp H) {A B : Subgroup (LGL p V)} (hA : IsAV H A) (hBA : B ≤ A)
    (hcard : Nat.card A = p * Nat.card B)
    (hQ : ¬ (Qp p H ⊓ Subgroup.centralizer (B : Set (LGL p V)) ≤
          Subgroup.centralizer (A : Set (LGL p V)))) :
    Nat.card B * Nat.card (fixSub B) = Nat.card A * Nat.card (fixSub A) ∧ IsAV H B := by
  have hQ1 : Nat.card B * Nat.card (fixSub B) ≤ Nat.card A * Nat.card (fixSub A) :=
    hA.2.2 B hBA
  have hBelem : IsElemAb p B := hA.2.1.mono hBA
  have hle : fixSub A ≤ fixSub B := fixSub_anti B A hBA
  have hne : fixSub A ≠ fixSub B := by
    intro heq
    obtain ⟨q, hqm, hqn⟩ := IsConcreteLE.not_le_iff_exists.mp hQ
    have hex : ∃ a ∈ A, a * q ≠ q * a := by
      by_contra hcon
      apply hqn
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      by_contra h
      exact hcon ⟨a, ha, h⟩
    obtain ⟨a, ha, haq⟩ := hex
    have hqQ : q ∈ Qp p H := hqm.1
    have hqC : q ∈ Subgroup.centralizer (B : Set (LGL p V)) := hqm.2
    set K : Subgroup (LGL p V) :=
      kerOn (Qp p H ⊓ Subgroup.centralizer (B : Set (LGL p V))) (fixSub B) with hK
    have hKQ : K ≤ Qp p H := fun g hg => hg.1.1
    have hKbot : K = ⊥ := by
      refine eq_bot_of_pq hBelem.isPGroup ?_ ?_ ?_
      · exact (coprime_card_Qp (p := p) H).coprime_dvd_right (Subgroup.card_dvd_of_le hKQ)
      · intro x hx y hy
        exact Subgroup.mem_centralizer_iff.mp hy.1.2 x hx
      · exact fun v hv g hg => hg.2 v hv
    have hnorm := le_normalizer_Qp hA.1 ha
    have hgK : q * a * q⁻¹ * a⁻¹ ∈ K := by
      refine ⟨⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩, ?_⟩
      · have h1 : a * q⁻¹ * a⁻¹ ∈ Qp p H :=
          (Subgroup.mem_normalizer_iff.mp hnorm _).mp (inv_mem hqQ)
        have h2 : q * a * q⁻¹ * a⁻¹ = q * (a * q⁻¹ * a⁻¹) := by group
        rw [h2]
        exact mul_mem hqQ h1
      · intro b hb
        have hbq : Commute b q := Subgroup.mem_centralizer_iff.mp hqC b hb
        have hba : Commute b a := IsElemAb.comm_mem hA.2.1 (hBA hb) ha
        exact ((hbq.mul_right hba).mul_right hbq.inv_right).mul_right hba.inv_right
      · intro w hw
        have hwA : w ∈ fixSub A := heq ▸ hw
        have h1 : a⁻¹ w = w := hwA a⁻¹ (inv_mem ha)
        have h2 : q⁻¹ w ∈ fixSub B := by
          intro b hb
          have hbq0 : Commute b q := Subgroup.mem_centralizer_iff.mp hqC b hb
          have hbq : Commute b q⁻¹ := hbq0.inv_right
          have h3 : (b * q⁻¹) w = (q⁻¹ * b) w := by rw [hbq.eq]
          change b (q⁻¹ w) = q⁻¹ w
          rw [show b (q⁻¹ w) = (b * q⁻¹) w from rfl, h3]
          change q⁻¹ (b w) = q⁻¹ w
          rw [hw b hb]
        have h3 : a (q⁻¹ w) = q⁻¹ w := (heq ▸ h2 : q⁻¹ w ∈ fixSub A) a ha
        change q (a (q⁻¹ (a⁻¹ w))) = w
        rw [h1, h3, apply_inv_apply']
    rw [hKbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hgK
    exact haq hgK.symm
  have hlt : fixSub A < fixSub B := lt_of_le_of_ne hle hne
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  have hpow : p * Nat.card (fixSub A) ≤ Nat.card (fixSub B) := by
    rw [card_eq_pow_finrank, card_eq_pow_finrank, ← pow_succ']
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hfr
  have hge : Nat.card A * Nat.card (fixSub A) ≤ Nat.card B * Nat.card (fixSub B) :=
    calc Nat.card A * Nat.card (fixSub A) = Nat.card B * (p * Nat.card (fixSub A)) := by
          rw [hcard]; ring
      _ ≤ Nat.card B * Nat.card (fixSub B) := Nat.mul_le_mul_left _ hpow
  have heq' := le_antisymm hQ1 hge
  exact ⟨heq', hBA.trans hA.1, hBelem, fun D hD => heq' ▸ hA.2.2 D (hD.trans hBA)⟩

theorem card_range_mul_card_ker (f : V →ₗ[ZMod p] V) :
    Nat.card (LinearMap.range f) * Nat.card (LinearMap.ker f) = Nat.card V := by
  have hV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    simpa [Nat.card_zmod] using this
  rw [card_eq_pow_finrank, card_eq_pow_finrank, hV, ← pow_add,
    LinearMap.finrank_range_add_finrank_ker]

theorem card_mul_fixSub (hH : Hyp H) {A : Subgroup (LGL p V)} (hA : IsAV H A) :
    Nat.card A * Nat.card (fixSub A) = Nat.card V := by
  suffices h : ∀ n, ∀ A : Subgroup (LGL p V), Nat.card A = n → IsAV H A →
      Nat.card A * Nat.card (fixSub A) = Nat.card V from h _ A rfl hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hA
    by_cases hA1 : A = ⊥
    · subst hA1
      rw [Subgroup.card_bot, fixSub_bot, one_mul]
      exact Nat.card_congr Submodule.topEquiv.toEquiv
    · obtain ⟨B, hBA, hcard, hQ⟩ := exists_hyperplane_not_le hH hA hA1
      obtain ⟨heq, hBV⟩ := key_hyperplane hH hA hBA hcard hQ
      have hBpos : 0 < Nat.card B := Nat.card_pos
      have hlt : Nat.card B < n := by
        have := (Fact.out : p.Prime).two_le
        rw [← hn, hcard]
        nlinarith
      rw [← heq]
      exact ih (Nat.card B) hlt B rfl hBV

@[expose] def stabQuot (U : Submodule (ZMod p) V) : Subgroup (LGL p V) where
  carrier := {g | ∀ v, g v - v ∈ U}
  one_mem' := fun v => by
    change v - v ∈ U
    simp
  mul_mem' := fun {a b} ha hb v => by
    have h : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
      change a (b v) - v = _
      abel
    rw [h]
    exact U.add_mem (ha (b v)) (hb v)
  inv_mem' := fun {a} ha v => by
    have h : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
      rw [apply_inv_apply']
      abel
    rw [h]
    exact U.neg_mem (ha (a⁻¹ v))

omit [Finite V] in
theorem commSub_zpowers (a : LGL p V) :
    commSub (Subgroup.zpowers a) =
      LinearMap.range ((a : V →ₗ[ZMod p] V) - LinearMap.id) := by
  apply le_antisymm
  · rw [commSub_le_iff]
    have h : Subgroup.zpowers a ≤
        stabQuot (LinearMap.range ((a : V →ₗ[ZMod p] V) - LinearMap.id)) :=
      Subgroup.zpowers_le.mpr fun v => ⟨v, rfl⟩
    exact fun g hg v => h hg v
  · rintro _ ⟨v, rfl⟩
    exact sub_mem_commSub _ (Subgroup.mem_zpowers a) v

omit [Fact p.Prime] [Finite V] in
theorem fixSub_zpowers (a : LGL p V) :
    fixSub (Subgroup.zpowers a) = LinearMap.ker ((a : V →ₗ[ZMod p] V) - LinearMap.id) := by
  ext v
  rw [LinearMap.mem_ker, mem_fixSub]
  constructor
  · intro h
    have h1 := h a (Subgroup.mem_zpowers a)
    change a v - v = 0
    rw [h1, sub_self]
  · intro h g hg
    have hav : a v = v := sub_eq_zero.mp h
    have hmem : a ∈ MulAction.stabilizer (LGL p V) v := hav
    exact (Subgroup.zpowers_le.mpr hmem) hg

omit [Finite V] in
theorem exists_zpowers_eq_of_card_eq {A : Subgroup (LGL p V)} (hp : Nat.card A = p) :
    ∃ a : LGL p V, A = Subgroup.zpowers a := by
  have : IsCyclic A := isCyclic_of_prime_card hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  refine ⟨(g : LGL p V), le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr g.2)⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem IsAVMin.card_eq (hH : Hyp H) {A : Subgroup (LGL p V)} (hA : IsAVMin H A) :
    Nat.card A = p ∧ Nat.card (commSub A) = p ∧ commSub A ≤ fixSub A := by
  obtain ⟨hAV, hne, hmin⟩ := hA
  have hA1 : A ≠ ⊥ := fun h => hne (h ▸ commSub_bot)
  obtain ⟨B, hBA, hcard, hQ⟩ := exists_hyperplane_not_le hH hAV hA1
  obtain ⟨_, hBV⟩ := key_hyperplane hH hAV hBA hcard hQ
  have hB1 : B = ⊥ := by
    by_contra hB1
    have hc : commSub B ≠ ⊥ := fun h => hB1 ((commSub_eq_bot_iff B).mp h)
    have hBA' : B = A := hmin B hBV hc hBA
    subst hBA'
    have hpos : 0 < Nat.card B := Nat.card_pos
    have := (Fact.out : p.Prime).two_le
    nlinarith
  have hAp : Nat.card A = p := by rw [hcard, hB1, Subgroup.card_bot, mul_one]
  obtain ⟨a, rfl⟩ := exists_zpowers_eq_of_card_eq hAp
  have hV := card_mul_fixSub hH hAV
  have hrk := card_range_mul_card_ker ((a : V →ₗ[ZMod p] V) - LinearMap.id)
  have hcommcard : Nat.card (commSub (Subgroup.zpowers a)) = p := by
    rw [commSub_zpowers]
    rw [fixSub_zpowers, hAp] at hV
    have hkpos : 0 < Nat.card (LinearMap.ker ((a : V →ₗ[ZMod p] V) - LinearMap.id)) :=
      Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hkpos (hrk.trans hV.symm)
  exact ⟨hAp, hcommcard, commSub_le_fixSub_of_card hAV.2.1.isPGroup hcommcard⟩

theorem le_iSup_isAVMin (hH : Hyp H) {A : Subgroup (LGL p V)} (hA : IsAV H A) :
    A ≤ ⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B := by
  have hp := (Fact.out : p.Prime)
  suffices h : ∀ n, ∀ A : Subgroup (LGL p V), Nat.card A = n → IsAV H A →
      A ≤ ⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B from h _ A rfl hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hA
    by_cases hA1 : A = ⊥
    · rw [hA1]
      exact bot_le
    obtain ⟨B₀, hB₀A, hB₀c, hB₀Q⟩ := exists_hyperplane_not_le hH hA hA1
    by_cases hpA : Nat.card A = p
    · have hmin : IsAVMin H A := by
        refine ⟨hA, fun h => hA1 ((commSub_eq_bot_iff A).mp h), ?_⟩
        intro B _ hBc hBA
        have hB1 : B ≠ ⊥ := fun h => hBc (h ▸ commSub_bot)
        have hdvd : Nat.card B ∣ p := by
          have h := Subgroup.card_dvd_of_le hBA
          rwa [hpA] at h
        have hBne : Nat.card B ≠ 1 := fun h => hB1 (Subgroup.card_eq_one.mp h)
        have hBp : Nat.card B = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hBne
        exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hpA, hBp])
      exact le_iSup₂_of_le A hmin le_rfl
    · have hB₀pos : 0 < Nat.card B₀ := Nat.card_pos
      have hAp : p < Nat.card A := by
        have h2 := hp.two_le
        rcases Nat.lt_or_ge 1 (Nat.card B₀) with h | h
        · rw [hB₀c]
          nlinarith
        · exfalso
          apply hpA
          have h1 : Nat.card B₀ = 1 := by omega
          rw [hB₀c, h1, mul_one]
      obtain ⟨B₁, B₂, h1A, h2A, hne, hc1, hc2, hQ1, hQ2⟩ :=
        exists_two_hyperplanes_not_le hH hA hAp
      obtain ⟨_, hV₁⟩ := key_hyperplane hH hA h1A hc1 hQ1
      obtain ⟨_, hV₂⟩ := key_hyperplane hH hA h2A hc2 hQ2
      have hlt : ∀ B : Subgroup (LGL p V), Nat.card A = p * Nat.card B → Nat.card B < n := by
        intro B hc
        have hpos : 0 < Nat.card B := Nat.card_pos
        have h2 := hp.two_le
        rw [← hn, hc]
        nlinarith
      have hle₁ := ih (Nat.card B₁) (hlt B₁ hc1) B₁ rfl hV₁
      have hle₂ := ih (Nat.card B₂) (hlt B₂ hc2) B₂ rfl hV₂
      have hsup : A ≤ B₁ ⊔ B₂ := by
        have hS : B₁ ⊔ B₂ ≤ A := sup_le h1A h2A
        have hd2 : Nat.card ↥(B₁ ⊔ B₂) ∣ Nat.card A := Subgroup.card_dvd_of_le hS
        obtain ⟨m, hm⟩ : Nat.card B₁ ∣ Nat.card ↥(B₁ ⊔ B₂) :=
          Subgroup.card_dvd_of_le le_sup_left
        have hB₁pos : 0 < Nat.card B₁ := Nat.card_pos
        have hm_dvd : m ∣ p := by
          have h3 : Nat.card B₁ * m ∣ Nat.card B₁ * p := by
            rw [← hm, mul_comm (Nat.card B₁) p, ← hc1]
            exact hd2
          exact Nat.dvd_of_mul_dvd_mul_left hB₁pos h3
        have hcard12 : Nat.card B₁ = Nat.card B₂ :=
          Nat.eq_of_mul_eq_mul_left hp.pos (hc1.symm.trans hc2)
        rcases (Nat.dvd_prime hp).mp hm_dvd with h | h
        · exfalso
          have hS1 : B₁ = B₁ ⊔ B₂ :=
            Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, h, mul_one])
          have hB₂le : B₂ ≤ B₁ := hS1 ▸ le_sup_right
          exact hne (Subgroup.eq_of_le_of_card_ge hB₂le hcard12.le).symm
        · have hge : Nat.card A ≤ Nat.card ↥(B₁ ⊔ B₂) := by
            rw [hm, h, hc1, mul_comm]
          exact (Subgroup.eq_of_le_of_card_ge hS hge).symm.le
      exact hsup.trans (sup_le hle₁ hle₂)

end CFSG.SignalizerFunctorTheorem.Quadratic


