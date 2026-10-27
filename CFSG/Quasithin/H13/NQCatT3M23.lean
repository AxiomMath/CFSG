module

public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.Quasithin.H13.NQCatT3Inv
public import CFSG.Quasithin.Background.E2TwoProofSporM23
public import CFSG.Quasithin.EmptyFaithful.ModHM23b
public import CFSG.Quasithin.H13.NQCatT3Lat
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import Certificates.Certificate7160

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint CFSG.Sporadic.Schreier
  CFSG.Quasithin.E2P.SporB
open scoped Pointwise

theorem evalW_mem (w : List ℕ) : M23T3.evalW w ∈ NativeSporadic.M23 := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
    simp only [M23T3.evalW]
    refine Subgroup.mul_mem _ ?_ ih
    split_ifs
    · exact m23GenA.2
    · exact m23GenB.2

theorem pow_three_of_e9 {G : Type} [Group G] [Finite G] {u v : G} (hu3 : u ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvu : v ≠ u)
    (hvu2 : v ≠ u ^ 2) {m : ℕ} (hG : Nat.card G = 3 ^ 2 * m) (hm : ¬ 3 ∣ m) {z : G} {k : ℕ}
    (hz : z ^ (3 ^ k) = 1) : z ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hE
  have hEset : (E : Set G) = (Subgroup.zpowers u : Set G) * (Subgroup.zpowers v : Set G) := by
    apply coe_sup_of_perm
    intro b hb a ha
    refine ⟨a, ha, b, hb, ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow huv.symm j i).eq
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    have he' : e ∈ (E : Set G) := he
    rw [hEset] at he'
    obtain ⟨a, ha, b, hb, hab⟩ := he'
    have hab' : a * b = e := hab
    rw [← hab']
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc' : Commute (u ^ i) (v ^ j) := Commute.zpow_zpow huv i j
    rw [hc'.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i,
      mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hu3, hv3, one_zpow,
      one_zpow, one_mul]
  have hE3 : IsPGroup 3 ↥E := IsPGroup.iff_orderOf.mpr fun e => by
    have h1 : orderOf e ∣ 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one (hEexp e e.2)
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h' | h'
    · exact ⟨0, by rw [h', pow_zero]⟩
    · exact ⟨1, by rw [h', pow_one]⟩
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hvE : v ∉ Subgroup.zpowers u := by
    intro hv
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hmod : u ^ i = u ^ (i % 3) := by
      have := (zpow_mod_orderOf u i).symm
      rwa [huo, Nat.cast_ofNat] at this
    have hm' : 0 ≤ i % 3 ∧ i % 3 < 3 :=
      ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
    · exact hv1 (by rw [← hi, hmod, h, zpow_zero])
    · exact hvu (by rw [← hi, hmod, h, zpow_one])
    · exact hvu2 (by rw [← hi, hmod, h, zpow_ofNat])
  have hlt : Subgroup.zpowers u < E :=
    lt_of_le_of_ne le_sup_left fun h => hvE (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have h3lt : 3 < Nat.card E := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [Nat.card_zpowers, huo] at this
  have hEc : Nat.card E = 9 := by
    obtain ⟨n, hn⟩ := hE3.exists_card_eq
    have hdvd : 3 ^ n ∣ 3 ^ 2 * m := hn ▸ hG ▸ Subgroup.card_subgroup_dvd_card E
    have hn2 : n ≤ 2 := by
      by_contra hn3
      have h1 : 3 ^ 3 ∣ 3 ^ 2 * m := (pow_dvd_pow 3 (by omega)).trans hdvd
      rw [pow_succ] at h1
      exact hm ((Nat.mul_dvd_mul_iff_left (by positivity)).mp h1)
    rw [hn] at h3lt ⊢
    interval_cases n
    · norm_num at h3lt
    · norm_num at h3lt
    · norm_num
  let ES : Sylow 3 G := hE3.toSylow (by
    have h1 := Subgroup.card_mul_index E
    rw [hEc, hG] at h1
    have h2 : E.index = m := by omega
    rw [h2]
    exact hm)
  have hz3 : IsPGroup 3 ↥(Subgroup.zpowers z) := by
    have hdvd : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hz
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  obtain ⟨P, hP⟩ := hz3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G ES P
  have hzP : z ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers z)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzP
  have h1 := hEexp _ hzP
  simp only [MulAut.smul_def, MulAut.conj_inv_apply] at h1
  have h2 : (g⁻¹ * z * g) ^ 3 = g⁻¹ * z ^ 3 * g := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [h2] at h1
  calc z ^ 3 = g * (g⁻¹ * z ^ 3 * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem m23_not_normal
    {j : ℕ}
    (hj : j ∈ [10, 11, 12, 13, 14]) :
    ¬ m23CtxB.Y j ≤ Subgroup.normalizer (m23CtxB.S : Set ↥NativeSporadic.M23) := by
  rw [CFSG.Quasithin.H.MathieuLat.m23Ctx_Y, CFSG.Quasithin.H.MathieuLat.m23Ctx_S]
  exact Certificates.certificate7160.1 j hj

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_m23
    (h : Star513 Q R S B D) (hQ : IsSporadic .M23 ↥Q)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    (∀ d ∈ D, d ^ 3 ∈ Subgroup.centralizer (Q : Set A)) ∧
      ∃ t ∈ S ⊓ Q, ∀ d ∈ D, t * d * t⁻¹ * d ∈ Subgroup.centralizer (Q : Set A) := by
  obtain ⟨hu3, hv3, huv, hu1, hv1, hvu, hvu2⟩ : M23T3.e9 := Certificates.certificate7160.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc23 : Subgroup.center ↥NativeSporadic.M23 = ⊥ := m23_center_eq_bot'
  have : IsSimpleGroup ↥NativeSporadic.M23 := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  have : Finite ↥NativeSporadic.M23 := CFSG.Sporadic.Mathieu.fam_m23_simplicity.1
  obtain ⟨e₀⟩ : Nonempty (↥Q ≃* ↥NativeSporadic.M23) := hQ
  have hM : Group.IsPerfect ↥NativeSporadic.M23 := isPerfect_of_center_eq_bot hc23
  have hZ : Subgroup.center ↥Q = ⊥ := by
    have h1 := Subgroup.map_center_eq e₀
    rw [hc23] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).mp h1
  let ψ : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥NativeSporadic.M23 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₀)
  have hperf : Group.IsPerfect ↥Q :=
    Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
  have hQperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hperf
  have hcen : Subgroup.center (↥Q ⧸ Subgroup.center ↥Q) = ⊥ :=
    @Group.IsPerfect.center_quotient_center_eq_bot ↥Q _ hperf
  have hinn := oddInner_of_mulEquiv ψ (oddInner_of_card_le hc23 (m23_mulAut_card.trans (by omega)))
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q ⧸ Subgroup.center ↥Q := MulEquiv.refl _
  obtain ⟨x, hx, k, hxk⟩ := iPart_eq_zpowers e hcen hinn h hD3
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨U, hU⟩ : ∃ U : ↥NativeSporadic.M23, (U : Equiv.Perm (Fin 23)) = M23T3.u :=
      ⟨⟨M23T3.u, by unfold M23T3.u; exact Subgroup.pow_mem _ (evalW_mem _) _⟩, rfl⟩
    obtain ⟨V, hV⟩ : ∃ V : ↥NativeSporadic.M23, (V : Equiv.Perm (Fin 23)) = M23T3.v :=
      ⟨⟨M23T3.v, by unfold M23T3.v; exact evalW_mem _⟩, rfl⟩
    have h9 : ψ x ^ 3 = 1 := pow_three_of_e9 (u := U) (v := V)
      (Subtype.ext (by rw [Subgroup.coe_pow, hU, Subgroup.coe_one]; exact hu3))
      (Subtype.ext (by rw [Subgroup.coe_pow, hV, Subgroup.coe_one]; exact hv3))
      (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hU, hV]; exact huv))
      (fun h => hu1 (by rw [← hU, h, Subgroup.coe_one]))
      (fun h => hv1 (by rw [← hV, h, Subgroup.coe_one]))
      (fun h => hvu (by rw [← hU, ← hV, h]))
      (fun h => hvu2 (by rw [← hU, ← hV, h, Subgroup.coe_pow])) (m := 1133440)
      (by norm_num [CFSG.Sporadic.Schreier.m23_card]) (by norm_num) (k := k)
      (by rw [← map_pow, hxk, map_one])
    exact ψ.injective (by rw [map_pow, h9, map_one])
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hperm := perm_D e hinn h hcen
  rw [hx] at hperm
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ pImg Q e (S ⊓ Q), t * x * t⁻¹ = x⁻¹ := by
    by_cases hx1 : x = 1
    · exact ⟨1, Subgroup.one_mem _, by simp [hx1]⟩
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    refine exists_inv_of_perm hT2 hxo hperm fun hxN => ?_
    set T := pImg Q e (S ⊓ Q) with hTdef
    have hU := ModH.M23b.m23_S_sylow
    let US : Sylow 2 ↥NativeSporadic.M23 := hU.2.1.toSylow (by
      have := hU.2.2
      have e : (m23CtxB.S.subgroupOf ⊤).index = m23CtxB.S.index := Subgroup.relIndex_top_right _
      rwa [e] at this)
    let TS : Sylow 2 ↥NativeSporadic.M23 :=
      (hT2.toSylow hTi).mapSurjective (f := ψ.toMonoidHom) ψ.surjective
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M23 TS US
    have hST : m23CtxB.S = (T.map ψ.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      have h1 : (US : Subgroup ↥NativeSporadic.M23) = m23CtxB.S := rfl
      rw [← h1, ← hg, Sylow.coe_subgroup_smul]
      rfl
    have hTc : Nat.card T = 128 := by
      have h1 := ModH.M23b.m23_S_card
      rwa [hST, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective ψ.injective] at h1
    have hY : Nat.card ↥(Subgroup.zpowers x ⊔ T) = 384 := by
      rw [card_sup_of_perm hperm (by rw [Nat.card_zpowers, hxo, hTc]; norm_num), Nat.card_zpowers,
        hxo, hTc]
    set Y := ((Subgroup.zpowers x ⊔ T).map ψ.toMonoidHom).map (MulAut.conj g).toMonoidHom
      with hYdef
    have hSY : m23CtxB.S ≤ Y := by
      rw [hST]
      exact Subgroup.map_mono (Subgroup.map_mono le_sup_right)
    have hYc : Nat.card Y = 384 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective ψ.injective, hY]
    have hYN : Y ≤ Subgroup.normalizer (m23CtxB.S : Set ↥NativeSporadic.M23) := by
      rw [hST]
      refine (Subgroup.map_mono (Subgroup.map_mono
        (sup_le (Subgroup.zpowers_le.mpr hxN) Subgroup.le_normalizer))).trans ?_
      exact (Subgroup.map_mono (Subgroup.le_normalizer_map _)).trans (Subgroup.le_normalizer_map _)
    rcases ModH.M23b.m23_overgroup hSY with htop | ⟨j, hj, hYj⟩
    · rw [htop, Subgroup.card_top, CFSG.Sporadic.Schreier.m23_card] at hYc
      norm_num at hYc
    · have hj' : j ∈ [10, 11, 12, 13, 14] := by
        have h2 := ModH.M23b.m23_card_Y hj
        rw [← hYj, hYc] at h2
        revert h2
        interval_cases j <;> decide
      exact m23_not_normal hj' (hYj ▸ hYN)
  obtain ⟨t₀, ht₀Q, ht₀S, rfl⟩ := (mem_pImg Q e).1 ht
  exact ⟨pow_three_mem_centralizer e hinn h hQperf hx hx3,
    t₀, ht₀S, conj_mul_mem_centralizer e hinn h hQperf hx ht₀Q htx⟩

end CFSG.Quasithin.H13.NQCat.T3
