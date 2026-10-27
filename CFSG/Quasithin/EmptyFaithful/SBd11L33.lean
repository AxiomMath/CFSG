module

public import CFSG.Quasithin.EmptyFaithful.SBd11Ctx
public import CFSG.Quasithin.H13.KGFactL33
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.SBd11

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem false_of_l33 (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hYL : Yp ≤ L)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 3 1) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, k, hk2, hQ, hcard⟩ := card_form_of_struct c.facts11.struct_Yp
  have hh := h
  obtain ⟨-, F, _, _, hcardF, ⟨e⟩⟩ := hh
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 3 :=
    (Nat.card_eq_fintype_card (α := F)).symm.trans (hcardF.trans (pow_one 3))
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let φ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.H13.A5.KGL33.center_SL_eq_bot hF)).trans
        QuotientGroup.quotientBot)
  have hL : Nat.card ↥L = 5616 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hcardF]
    decide +kernel
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥Yp) := inferInstance
  have h3k : 3 ^ k ∣ Nat.card P := by
    refine pow_dvd_card_sylow P ?_
    rw [hcard]
    exact Dvd.intro_left _ rfl
  have hb16 : 2 ^ b ∣ 16 := by
    have h2b : 2 ^ b ∣ Nat.card ↥Yp := by
      rw [hcard]
      exact Dvd.intro _ rfl
    have h1 : 2 ^ b ∣ 5616 := by
      rw [← hL]
      exact h2b.trans (Subgroup.card_dvd_of_le hYL)
    have hcop : Nat.Coprime (2 ^ b) 351 := Nat.Coprime.pow_left b (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (show 2 ^ b ∣ 16 * 351 by simpa using h1)
  have hb4 : b ≤ 4 := by
    have := Nat.le_of_dvd (by norm_num) hb16
    by_contra hc
    have : 2 ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hb3 : b ≤ 3
  ·
    have hcard' : Nat.card ↥Yp ∣ 8 * Nat.card (⊥ : Subgroup ↥Yp) * Nat.card P := by
      rw [Subgroup.card_bot, mul_one, hcard]
      exact Nat.mul_dvd_mul (by
        have : 2 ^ b ∣ 2 ^ 3 := pow_dvd_pow 2 hb3
        simpa using this) h3k
    obtain ⟨R, hR0, hRn, hRp⟩ := exists_normal_three_of_card_dvd P
      (Dvd.dvd.trans (pow_dvd_pow 3 hk2) h3k)
      (by simpa using (IsPGroup.of_card (p := 2) (G := ↥(⊥ : Subgroup ↥Yp)) (n := 0) (by simp)))
      (fun z hz x _ => by rw [Subgroup.mem_bot.1 hz]; simp) hcard'
    exact false_of_pCoreOf_three_ne_bot c hYL (pCoreOf_three_ne_bot_of_normal R hR0 hRn hRp)
  · have hb : b = 4 := by omega
    subst hb
    set Q' : Subgroup ↥Yp := CFSG.Open.pCore 2 ↥Yp with hQ'def
    have hQ'2 : IsPGroup 2 Q' := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Yp) 2
    have hQ'card : Nat.card Q' = 16 := by rw [hQ]; norm_num
    have hQ'n : Q'.Normal := inferInstance
    let ι : ↥Yp →* ↥L := Subgroup.inclusion hYL
    have hι : Function.Injective ι := Subgroup.inclusion_injective hYL
    set QL : Subgroup ↥L := Q'.map ι with hQL
    have hQLcard : Nat.card QL = 16 := by rw [Subgroup.card_map_of_injective hι]; exact hQ'card
    have hQL2 : IsPGroup 2 QL := hQ'2.map ι
    have hQLidx : ¬ 2 ∣ QL.index := by
      have := Subgroup.card_mul_index QL
      rw [hQLcard, hL] at this
      omega
    let P₂ : Sylow 2 ↥L := hQL2.toSylow hQLidx
    have hnt : Nontrivial Q' := by
      have : Fintype Q' := Fintype.ofFinite _
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hQ'card]
      norm_num
    have := hQ'2.center_nontrivial
    obtain ⟨⟨z₀, hz₀c⟩, hz₀1⟩ := exists_ne (1 : ↥(Subgroup.center ↥Q'))
    have hz1 : (z₀ : ↥Yp) ≠ 1 := fun h => hz₀1 (Subtype.ext (Subtype.ext h))
    have hzq : ∀ q ∈ Q', (z₀ : ↥Yp) * q = q * z₀ := fun q hq =>
      congrArg (fun w : ↥Q' => (w : ↥Yp)) ((Subgroup.mem_center_iff.1 hz₀c ⟨q, hq⟩).symm)
    obtain ⟨hP2, hC⟩ := CFSG.Quasithin.H13.A5.KGL33.sl3_criterion hF φ
    have hkey : ∀ y : ↥Yp, y * (z₀ : ↥Yp) * y⁻¹ = z₀ := by
      intro y
      have hu : ∀ t ∈ (P₂ : Subgroup ↥L), ι (y * (z₀ : ↥Yp) * y⁻¹) * t = t * ι (y * (z₀ : ↥Yp) * y⁻¹) := by
        intro t ht
        have ht' : t ∈ QL := ht
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 ht'
        have hq' : y⁻¹ * q * y⁻¹⁻¹ ∈ Q' := hQ'n.conj_mem q hq y⁻¹
        have h1 := hzq _ hq'
        rw [← map_mul, ← map_mul]
        congr 1
        calc y * (z₀ : ↥Yp) * y⁻¹ * q = y * ((z₀ : ↥Yp) * (y⁻¹ * q * y⁻¹⁻¹)) * y⁻¹ := by group
          _ = y * ((y⁻¹ * q * y⁻¹⁻¹) * z₀) * y⁻¹ := by rw [h1]
          _ = q * (y * (z₀ : ↥Yp) * y⁻¹) := by group
      have hw : ∀ t ∈ (P₂ : Subgroup ↥L), ι (z₀ : ↥Yp) * t = t * ι (z₀ : ↥Yp) := by
        intro t ht
        have ht' : t ∈ QL := ht
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 ht'
        rw [← map_mul, ← map_mul, hzq q hq]
      have hu1 : ι (y * (z₀ : ↥Yp) * y⁻¹) ≠ 1 := by
        intro h1
        have := hι (h1.trans (map_one ι).symm)
        apply hz1
        calc (z₀ : ↥Yp) = y⁻¹ * (y * (z₀ : ↥Yp) * y⁻¹) * y := by group
          _ = 1 := by rw [this]; group
      have hw1 : ι (z₀ : ↥Yp) ≠ 1 := fun h1 => hz1 (hι (h1.trans (map_one ι).symm))
      have huw := CFSG.Quasithin.H13.A5.KGL33.eq_of_mem_centralizer_sylow hP2 hC P₂ hu hw hu1 hw1
      exact hι huw
    set Z : Subgroup ↥Yp := Subgroup.zpowers (z₀ : ↥Yp) with hZdef
    have hZQ : Z ≤ Q' := Subgroup.zpowers_le.2 z₀.2
    have hZ2 : IsPGroup 2 Z := hQ'2.to_le hZQ
    have hZc : ∀ z ∈ Z, ∀ x : ↥Yp, z * x = x * z := by
      intro z hz x
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hc : Commute (z₀ : ↥Yp) x := by
        have := hkey x
        have h2 : x * (z₀ : ↥Yp) = z₀ * x := by
          calc x * (z₀ : ↥Yp) = (x * (z₀ : ↥Yp) * x⁻¹) * x := by group
            _ = z₀ * x := by rw [this]
        exact h2.symm
      exact (Commute.zpow_left hc n).eq
    have hZeven : 2 ∣ Nat.card Z := by
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hZ2
      have hm0 : m ≠ 0 := by
        rintro rfl
        have h1 : Nat.card Z = 1 := by simpa using hm
        have h2 : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z h1
        exact hz1 (Subgroup.mem_bot.1 (h2 ▸ Subgroup.mem_zpowers (z₀ : ↥Yp)))
      rw [hm]
      exact dvd_pow_self 2 hm0
    have hcard' : Nat.card ↥Yp ∣ 8 * Nat.card Z * Nat.card P := by
      rw [hcard]
      obtain ⟨c1, hc1⟩ := hZeven
      obtain ⟨c2, hc2⟩ := h3k
      rw [hc1, hc2]
      exact ⟨c1 * c2, by ring⟩
    obtain ⟨R, hR0, hRn, hRp⟩ := exists_normal_three_of_card_dvd P
      (Dvd.dvd.trans (pow_dvd_pow 3 hk2) h3k) hZ2 (fun z hz x _ => hZc z hz x) hcard'
    exact false_of_pCoreOf_three_ne_bot c hYL (pCoreOf_three_ne_bot_of_normal R hR0 hRn hRp)

end CFSG.Quasithin.SBd11
