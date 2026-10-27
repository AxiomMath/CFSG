module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KInter
public import CFSG.Quasithin.EmptyFaithful.SBc16GAct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

namespace K

section K0

variable {G : Type} [Group G]

noncomputable def K0 (X K : Subgroup G) : Subgroup G :=
  K ⊓ (SBc16.actHom X).ker.map (Subgroup.normalizer (X : Set G)).subtype

theorem mem_K0 {X K : Subgroup G} {k : G} :
    k ∈ K0 X K ↔ k ∈ K ∧ ∃ hk : k ∈ Subgroup.normalizer (X : Set G),
      SBc16.actHom X ⟨k, hk⟩ = 1 := by
  unfold K0
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hkK, y, hy, rfl⟩
    exact ⟨hkK, y.2, hy⟩
  · rintro ⟨hkK, hk, h⟩
    exact ⟨hkK, ⟨k, hk⟩, h, rfl⟩

theorem K0_le (X K : Subgroup G) : K0 X K ≤ K := inf_le_left

theorem commutator_mem_of_mem_K0 {X K : Subgroup G} {k : G} (hk : k ∈ K0 X K) :
    ∀ x ∈ X, k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 X := by
  obtain ⟨-, hkN, h⟩ := mem_K0.1 hk
  exact (SBc16.actHom_eq_one_iff X hkN).1 h

theorem conj_mem_K0 {X K : Subgroup G} {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K0 X K) :
    g * k * g⁻¹ ∈ K0 X K := by
  obtain ⟨hkK, hkN, h⟩ := mem_K0.1 hk
  refine mem_K0.2 ⟨(Subgroup.mem_normalizer_iff.mp hgK k).mp hkK,
    (Subgroup.normalizer (X : Set G)).mul_mem ((Subgroup.normalizer (X : Set G)).mul_mem hgX hkN)
      ((Subgroup.normalizer (X : Set G)).inv_mem hgX), ?_⟩
  have e : (⟨g * k * g⁻¹, (Subgroup.normalizer (X : Set G)).mul_mem
      ((Subgroup.normalizer (X : Set G)).mul_mem hgX hkN)
      ((Subgroup.normalizer (X : Set G)).inv_mem hgX)⟩ : ↥(Subgroup.normalizer (X : Set G))) =
      ⟨g, hgX⟩ * ⟨k, hkN⟩ * ⟨g, hgX⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, h, mul_one, map_inv, mul_inv_cancel]

theorem mem_normalizer_K0 {X K : Subgroup G} {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer (K0 X K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨conj_mem_K0 hgX hgK, fun h => ?_⟩
  have h1 := conj_mem_K0 ((Subgroup.normalizer (X : Set G)).inv_mem hgX)
    ((Subgroup.normalizer (K : Set G)).inv_mem hgK) h
  simpa [mul_assoc] using h1

noncomputable abbrev Csub (H X : Subgroup G) : Subgroup G :=
  K0 X (oTwoUpper H) ⊔ pCoreOf 2 (oTwoUpper H)

theorem Q_le_Csub (H X : Subgroup G) : pCoreOf 2 (oTwoUpper H) ≤ Csub H X := le_sup_right

theorem Csub_le (H X : Subgroup G) : Csub H X ≤ oTwoUpper H :=
  sup_le (K0_le _ _) (pCoreOf_le 2 _)

end K0

section Setting

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem S_le_normalizer_Csub (c : P4Ctx T Mc M H B₀ I X)
    (hXI : I ≤ Subgroup.normalizer (X : Set G)) :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Csub H X : Set G) := fun _ hs =>
  mem_normalizer_sup (mem_normalizer_K0 (S_le_normalizer_X c hXI hs) (S_le_normalizer_K c hs))
    (S_le_normalizer_Q c hs)

theorem exists_mem_K0_of_E (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G))
    (hq : IsLnTwoQuot X 3) {E : Subgroup G} (hEK : E ≤ oTwoUpper H)
    (hE9 : Nat.card E = 3 ^ 2) : ∃ x ∈ E, x ≠ 1 ∧ x ∈ K0 X (oTwoUpper H) := by
  have hEN : E ≤ Subgroup.normalizer (X : Set G) := hEK.trans (K_le_normalizer_X c hXI)
  let ρ : ↥E →* MulAut (OTwoQuot X) := (SBc16.actHom X).comp (Subgroup.inclusion hEN)
  have h1 := SBc16.card_eq_card_range_mul_card_ker ρ
  have h2 : Nat.card ρ.range ∣ 336 := by
    rw [← card_mulAut_quot_X hq]
    exact Subgroup.card_subgroup_dvd_card _
  by_contra hcon
  push Not at hcon
  have hker : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxE : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact hcon x x.2 hxE (mem_K0.2 ⟨hEK x.2, hEN x.2, hx⟩)
  rw [hker, Subgroup.card_bot, mul_one, hE9] at h1
  rw [← h1] at h2
  norm_num at h2

theorem not_mem_Csub (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G))
    (hq : IsLnTwoQuot X 3) {e : G} (heK : e ∈ oTwoUpper H) (heX : e ∈ X) (he3 : orderOf e = 3) :
    e ∉ Csub H X := by
  intro h
  have hKX := K_le_normalizer_X c hXI
  have hnorm : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (K0 X (oTwoUpper H) : Set G) :=
    fun o ho => mem_normalizer_K0 (hKX (pCoreOf_le 2 _ ho))
      (Subgroup.le_normalizer (pCoreOf_le 2 _ ho))
  obtain ⟨k₀, hk₀, o, ho, rfl⟩ : ∃ k₀ ∈ K0 X (oTwoUpper H), ∃ o ∈ pCoreOf 2 (oTwoUpper H),
      k₀ * o = e := by
    have := (Subgroup.coe_mul_of_right_le_normalizer_left (K0 X (oTwoUpper H))
      (pCoreOf 2 (oTwoUpper H)) hnorm) ▸ (show e ∈ ((Csub H X : Subgroup G) : Set G) from h)
    obtain ⟨a, ha, b, hb, hab⟩ := this
    exact ⟨a, ha, b, hb, hab⟩
  have hkN : k₀ ∈ Subgroup.normalizer (X : Set G) := hKX (K0_le _ _ hk₀)
  have hoN : o ∈ Subgroup.normalizer (X : Set G) := hKX (pCoreOf_le 2 _ ho)
  have heN : k₀ * o ∈ Subgroup.normalizer (X : Set G) := Subgroup.mul_mem _ hkN hoN
  have hρ : SBc16.actHom X ⟨k₀ * o, heN⟩ = SBc16.actHom X ⟨o, hoN⟩ := by
    have e1 : (⟨k₀ * o, heN⟩ : ↥(Subgroup.normalizer (X : Set G))) = ⟨k₀, hkN⟩ * ⟨o, hoN⟩ := rfl
    obtain ⟨-, hk', h0⟩ := mem_K0.1 hk₀
    rw [e1, map_mul, h0, one_mul]
  have h3 : SBc16.actHom X ⟨k₀ * o, heN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨k₀ * o, heN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using he3 ▸ pow_orderOf_eq_one (k₀ * o))
    rw [this, map_one]
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 (oTwoUpper H) ⟨o, ho⟩
  have h2j : SBc16.actHom X ⟨k₀ * o, heN⟩ ^ 2 ^ j = 1 := by
    rw [hρ, ← map_pow]
    have : (⟨o, hoN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 ^ j = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hj)
    rw [this, map_one]
  have hone : SBc16.actHom X ⟨k₀ * o, heN⟩ = 1 := by
    have hd : orderOf (SBc16.actHom X ⟨k₀ * o, heN⟩) ∣ Nat.gcd 3 (2 ^ j) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2j)
    rw [(Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hcomm := (SBc16.actHom_eq_one_iff X heN).1 hone
  have hcentral : (QuotientGroup.mk ⟨k₀ * o, heX⟩ : OTwoQuot X) = 1 := by
    refine eq_one_of_central_quot_X hq fun t => ?_
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective t
    exact (mk_commute_iff ⟨k₀ * o, heX⟩ ⟨x, hx⟩).2 (hcomm x hx)
  exact B.false_of_orderOf_three_mem (pCoreOf_isPGroup 2 X)
    ((mk_eq_one_iff_mem_pCoreOf ⟨k₀ * o, heX⟩).1 hcentral) he3

theorem relIndex_Csub (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G))
    (hq : IsLnTwoQuot X 3) : (pCoreOf 2 (oTwoUpper H)).relIndex (Csub H X) = 3 := by
  obtain ⟨E, hEK, hE, hE9⟩ := c.exists_E9
  obtain ⟨e, heE, heo⟩ := exists_inf_of_E c hXI hq hEK hE hE9
  obtain ⟨x, hxE, hx1, hxK0⟩ := exists_mem_K0_of_E c hXI hq hEK hE9
  have hab := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (oTwoUpper H)) (Csub H X)
    (oTwoUpper H) (Q_le_Csub H X) (Csub_le H X)
  rw [c.relIndex_K] at hab
  have ha : (pCoreOf 2 (oTwoUpper H)).relIndex (Csub H X) ≠ 1 := by
    intro h1
    have hle := Subgroup.relIndex_eq_one.1 h1
    have hxC : x ∈ pCoreOf 2 (oTwoUpper H) := hle (Subgroup.mem_sup_left hxK0)
    exact B.false_of_orderOf_three_mem (pCoreOf_isPGroup 2 _) hxC
      (orderOf_eq_prime (hE.2 x hxE) hx1)
  have hb : (Csub H X).relIndex (oTwoUpper H) ≠ 1 := by
    intro h1
    have hle := Subgroup.relIndex_eq_one.1 h1
    exact not_mem_Csub c hXI hq (hEK heE.1) heE.2 heo (hle (hEK heE.1))
  have hdvd : (pCoreOf 2 (oTwoUpper H)).relIndex (Csub H X) ∣ 9 := ⟨_, hab.symm⟩
  have hle9 := Nat.le_of_dvd (by norm_num) hdvd
  generalize (pCoreOf 2 (oTwoUpper H)).relIndex (Csub H X) = a at *
  generalize (Csub H X).relIndex (oTwoUpper H) = b at *
  interval_cases a <;> omega

end Setting

end K

end S15223P4

end CFSG.Quasithin
