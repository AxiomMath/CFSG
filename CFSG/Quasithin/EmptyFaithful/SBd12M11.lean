module

public import CFSG.Quasithin.EmptyFaithful.SBd12Lift
public import CFSG.Quasithin.EmptyFaithful.SBd11Ctx
public import CFSG.Quasithin.Background.F420M11

public section

namespace CFSG.Quasithin.SBd12

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBd11

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem pCore_le_center_of_center_eq {L : Subgroup G} (h : centerOf L = pCoreOf 2 L) :
    CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := by
  intro x hx
  have hx' : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
  rw [← h] at hx'
  exact mem_centerOf_iff_center.1 hx'

theorem false_of_m11 (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hYL : Yp ≤ L)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, k, hk2, hQ, hcard⟩ := card_form_of_struct c.facts11.struct_Yp
  let e' : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Quasithin.F420.M11G := e
  let ψ : ↥Yp →* CFSG.Quasithin.F420.M11G :=
    e'.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hYL))
  have hker : ∀ y : ↥Yp, y ∈ ψ.ker ↔ Subgroup.inclusion hYL y ∈ CFSG.pCore 2 ↥L := by
    intro y
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hpc2 : IsPGroup 2 (CFSG.pCore 2 ↥L) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hpcc := pCore_le_center_of_center_eq c.c33.center_eq
  have hK2 : IsPGroup 2 ψ.ker := by
    intro z
    obtain ⟨m, hm⟩ := hpc2 ⟨_, (hker z.1).1 z.2⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 := congrArg (fun w : ↥(CFSG.pCore 2 ↥L) => (w : ↥L)) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    apply Subgroup.inclusion_injective hYL
    simpa [map_pow] using h1
  have hKc : ∀ z ∈ ψ.ker, ∀ x : ↥Yp, z * x = x * z := by
    intro z hz x
    have h1 := Subgroup.mem_center_iff.1 (hpcc ((hker z).1 hz)) (Subgroup.inclusion hYL x)
    apply Subgroup.inclusion_injective hYL
    simpa [map_mul] using h1.symm
  have hL : Nat.card CFSG.Quasithin.F420.M11G = 7920 :=
    CFSG.Semidihedral.GL2Recognition.card_nativeM11
  have hprod := Subgroup.card_ker_mul_card_range ψ
  have hr7920 : Nat.card ψ.range ∣ 7920 := hL ▸ Subgroup.card_subgroup_dvd_card ψ.range
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥Yp) := inferInstance
  have h9 : 9 ∣ Nat.card P := by
    refine pow_dvd_card_sylow (k := 2) P ?_
    rw [hcard]
    exact Dvd.dvd.mul_left (pow_dvd_pow 3 hk2) _
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).1 hK2
  have hrY : Nat.card ψ.range ∣ 2 ^ b * 3 ^ k := by
    rw [← hcard, ← hprod]
    exact Dvd.intro_left _ rfl
  have hr144 : Nat.card ψ.range ∣ 144 := by
    have hcop : Nat.Coprime (Nat.card ψ.range) 55 :=
      Nat.Coprime.coprime_dvd_left hrY
        (Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.pow_left b (by norm_num),
          Nat.Coprime.pow_left k (by norm_num)⟩)
    exact hcop.dvd_of_dvd_mul_right (show Nat.card ψ.range ∣ 144 * 55 by simpa using hr7920)
  have h9r : 9 ∣ Nat.card ψ.range := by
    have h3k : 3 ^ k ∣ Nat.card ψ.range := by
      have h1 : 3 ^ k ∣ Nat.card ψ.ker * Nat.card ψ.range := by
        rw [hprod, hcard]
        exact Dvd.intro_left _ rfl
      have hcop : Nat.Coprime (3 ^ k) (Nat.card ψ.ker) := by
        rw [hi]
        exact Nat.Coprime.pow k i (by norm_num)
      exact hcop.dvd_of_dvd_mul_left h1
    exact (pow_dvd_pow 3 hk2).trans h3k
  by_cases hr72 : Nat.card ψ.range ∣ 72
  ·
    have hcard' : Nat.card ↥Yp ∣ 8 * Nat.card ψ.ker * Nat.card P := by
      rw [← hprod]
      have h72 : (72 : ℕ) ∣ 8 * Nat.card P := Nat.mul_dvd_mul_left 8 h9
      calc Nat.card ψ.ker * Nat.card ψ.range ∣ Nat.card ψ.ker * 72 :=
            Nat.mul_dvd_mul_left _ hr72
        _ ∣ Nat.card ψ.ker * (8 * Nat.card P) := Nat.mul_dvd_mul_left _ h72
        _ = 8 * Nat.card ψ.ker * Nat.card P := by ring
    obtain ⟨R, hR0, hRn, hRp⟩ := exists_normal_three_of_normalizing P h9 hK2
      (le_normalizer_of_commute (fun a ha x _ => hKc a ha x)) hcard'
    exact false_of_pCoreOf_three_ne_bot c hYL (pCoreOf_three_ne_bot_of_normal R hR0 hRn hRp)
  · have hr : Nat.card ψ.range = 144 := by
      have hmem : Nat.card ψ.range ∈ Nat.divisors 144 := Nat.mem_divisors.2 ⟨hr144, by norm_num⟩
      have hd : Nat.divisors 144 = {1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} := by
        decide +kernel
      rw [hd] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        first | exact h | (exfalso; rw [h] at h9r hr72; revert h9r hr72; decide)
    set Q : Subgroup ↥Yp := CFSG.Open.pCore 2 ↥Yp with hQdef
    have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Yp) 2
    have hQn : Q.Normal := inferInstance
    have hKQ : ψ.ker ≤ Q := le_pCore 2 inferInstance hK2
    set Qb : Subgroup CFSG.Quasithin.F420.M11G := Q.map ψ with hQb
    have hQcard : Nat.card ψ.ker * Nat.card Qb = Nat.card Q := by
      let f : ↥Q →* CFSG.Quasithin.F420.M11G := ψ.comp Q.subtype
      have h1 := Subgroup.card_ker_mul_card_range f
      have hker' : f.ker = ψ.ker.subgroupOf Q := by
        ext q
        simp [f, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      have hrange : f.range = Qb := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have hc : Nat.card (ψ.ker.subgroupOf Q) = Nat.card ψ.ker :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKQ).toEquiv
      rw [hker', hrange, hc] at h1
      exact h1
    have hQbcard : Nat.card Qb = 16 := by
      have hdvd : Nat.card Qb ∣ 2 ^ b := ⟨Nat.card ψ.ker, by rw [← hQ, ← hQcard, mul_comm]⟩
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hK0 : 0 < Nat.card ψ.ker := Nat.card_pos
      have h1 : Nat.card ψ.ker * 144 = Nat.card ψ.ker * (2 ^ j * 3 ^ k) := by
        calc Nat.card ψ.ker * 144 = Nat.card ↥Yp := by rw [← hr, hprod]
          _ = 2 ^ b * 3 ^ k := hcard
          _ = Nat.card Q * 3 ^ k := by rw [hQ]
          _ = Nat.card ψ.ker * (2 ^ j * 3 ^ k) := by rw [← hQcard, hjeq]; ring
      have h2 : 2 ^ j * 3 ^ k = 144 := (Nat.eq_of_mul_eq_mul_left hK0 h1).symm
      have hj7 : j ≤ 7 := by
        by_contra hc
        have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ j ≤ 144 := Nat.le_of_dvd (by norm_num) ⟨3 ^ k, h2.symm⟩
        omega
      have hk4 : k ≤ 4 := by
        by_contra hc
        have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 3 ^ k ≤ 144 := Nat.le_of_dvd (by norm_num) ⟨2 ^ j, by rw [← h2]; ring⟩
        omega
      have hj4 : j = 4 := by
        interval_cases j <;> interval_cases k <;> simp at h2 ⊢
      rw [hjeq, hj4]
      norm_num
    have hQbS : CFSG.Open.quasithinIsSylowTwo Qb := by
      refine ⟨hQ2.map ψ, ?_⟩
      have h1 := Subgroup.card_mul_index Qb
      rw [hQbcard, hL] at h1
      omega
    have hQbn : ∀ y : ↥Yp, ∀ q ∈ Qb, ψ y * q * (ψ y)⁻¹ ∈ Qb := by
      intro y q hq
      obtain ⟨q0, hq0, rfl⟩ := Subgroup.mem_map.1 hq
      exact ⟨y * q0 * y⁻¹, hQn.conj_mem q0 hq0 y, by simp [map_mul, map_inv]⟩
    have hQbnt : Nontrivial Qb := by
      have : Fintype Qb := Fintype.ofFinite _
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hQbcard]
      norm_num
    have hcen := (hQ2.map ψ).center_nontrivial
    obtain ⟨⟨z0, hz0c⟩, hz01⟩ := exists_ne (1 : ↥(Subgroup.center ↥Qb))
    set zb : CFSG.Quasithin.F420.M11G := (z0 : CFSG.Quasithin.F420.M11G) with hzb
    have hzb1 : zb ≠ 1 := fun h => hz01 (Subtype.ext (Subtype.ext h))
    have hzbQ : zb ∈ Qb := z0.2
    have hzbc : ∀ q ∈ Qb, zb * q = q * zb := fun q hq =>
      congrArg (fun w : ↥Qb => (w : CFSG.Quasithin.F420.M11G))
        ((Subgroup.mem_center_iff.1 hz0c ⟨q, hq⟩).symm)
    have hSCW := CFSG.Quasithin.F420.smallCentralizerWitness_m11
    have hzc : ∀ y : ↥Yp, ψ y * zb = zb * ψ y := by
      intro y
      set u := ψ y * zb * (ψ y)⁻¹ with hu
      have huQ : ∀ s ∈ Qb, u * s = s * u := by
        intro s hs
        have hs' : (ψ y)⁻¹ * s * ψ y ∈ Qb := by
          have := hQbn y⁻¹ s hs
          simpa [map_inv] using this
        have h1 := hzbc _ hs'
        calc u * s = ψ y * (zb * ((ψ y)⁻¹ * s * ψ y)) * (ψ y)⁻¹ := by rw [hu]; group
          _ = ψ y * (((ψ y)⁻¹ * s * ψ y) * zb) * (ψ y)⁻¹ := by rw [h1]
          _ = s * u := by rw [hu]; group
      have hu1 : u ≠ 1 := by
        intro h
        apply hzb1
        calc zb = (ψ y)⁻¹ * (ψ y * zb * (ψ y)⁻¹) * ψ y := by group
          _ = 1 := by rw [← hu, h]; group
      rcases CFSG.Quasithin.F420.centralizer_le_two hSCW hQbS u zb huQ hzbc with h | h | h
      · exact absurd h hu1
      · exact absurd h hzb1
      · calc ψ y * zb = (ψ y * zb * (ψ y)⁻¹) * ψ y := by group
          _ = zb * ψ y := by rw [← hu, h]
    obtain ⟨z, hzQ, hzψ⟩ := Subgroup.mem_map.1 hzbQ
    have hzN : z ∈ Subgroup.normalizer ((P : Subgroup ↥Yp) : Set ↥Yp) := by
      refine mem_normalizer_of_map_mem_normalizer ψ hK2 hKc P ?_
      rw [hzψ]
      have hcomm : ∀ a ∈ Subgroup.zpowers zb, ∀ x ∈ (P : Subgroup ↥Yp).map ψ, a * x = x * a := by
        intro a ha x hx
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact (Commute.zpow_left (show Commute zb (ψ p) from (hzc p).symm) n).eq
      exact le_normalizer_of_commute hcomm (Subgroup.mem_zpowers zb)
    set A : Subgroup ↥Yp := Subgroup.zpowers z ⊔ ψ.ker with hA
    have hAQ : A ≤ Q := sup_le (Subgroup.zpowers_le.2 hzQ) hKQ
    have hA2 : IsPGroup 2 A := hQ2.to_le hAQ
    have hAN : A ≤ Subgroup.normalizer ((P : Subgroup ↥Yp) : Set ↥Yp) :=
      sup_le (Subgroup.zpowers_le.2 hzN) (le_normalizer_of_commute (fun a ha x _ => hKc a ha x))
    have hKA : ψ.ker ≤ A := le_sup_right
    have hzA : z ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    have hzK : z ∉ ψ.ker := by
      intro h
      apply hzb1
      rw [← hzψ]
      exact h
    have hrel : (ψ.ker).relIndex A ≠ 1 := by
      intro h
      exact hzK ((Subgroup.relIndex_eq_one.1 h) hzA)
    have hrelcard : (ψ.ker).relIndex A * Nat.card ψ.ker = Nat.card A := by
      have := Subgroup.relIndex_mul_card (H := ψ.ker) (K := A)
      rwa [inf_eq_left.2 hKA] at this
    obtain ⟨j', hj'⟩ := (IsPGroup.iff_card).1 hA2
    have hreldvd : (ψ.ker).relIndex A ∣ 2 ^ j' := ⟨Nat.card ψ.ker, by rw [← hj', ← hrelcard]⟩
    have h2rel : 2 ∣ (ψ.ker).relIndex A := by
      obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hreldvd
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hrel (by simpa using hs)
      rw [hs]
      exact dvd_pow_self 2 hs0
    have h9' := h9
    have hcard' : Nat.card ↥Yp ∣ 8 * Nat.card A * Nat.card P := by
      obtain ⟨s', hs'⟩ := h2rel
      obtain ⟨p', hp'⟩ := h9'
      have hY : Nat.card ↥Yp = Nat.card ψ.ker * 144 := by rw [← hr, hprod]
      refine ⟨s' * p', ?_⟩
      rw [hY, ← hrelcard, hs', hp']
      ring
    obtain ⟨R, hR0, hRn, hRp⟩ := exists_normal_three_of_normalizing P h9 hA2 hAN hcard'
    exact false_of_pCoreOf_three_ne_bot c hYL (pCoreOf_three_ne_bot_of_normal R hR0 hRn hRp)

end CFSG.Quasithin.SBd12
