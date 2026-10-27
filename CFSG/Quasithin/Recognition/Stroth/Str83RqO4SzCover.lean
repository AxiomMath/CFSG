module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Goldschmidt
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexSz
import CFSG.Quasithin.Vol2.Ch10SecQ3CQ
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem szc_Gv_inf_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Gv 0 ⊓ t.Gv 1 = S ⊔ t.K := by
  have h := t.Gw_add_one 0
  rw [zero_add] at h
  rw [← h, t.Gw_zero_one hfr.hF, t.sup_K_eq_bigB]

private theorem szc_K_le_normalizer_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer (S : Set G) :=
  le_sup_right.trans (t.sup_K_eq_bigB.le.trans hfr.hN)

private theorem szc_Q_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 0 ≤ S := by
  rw [t.Qv_zero]
  exact Q1_le_S hfr.hF

private theorem szc_Q_le_Gv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 0 ≤ t.Gv 1 := by
  have h := (t.Qv_le_Gv hfr 0).2
  simpa using h

private theorem szc_Q_le_Gv_neg_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 0 ≤ t.Gv (-1) := by
  have h := (t.Qv_le_Gv hfr 0).1
  simpa using h

private theorem szc_conj_mem {H : Subgroup G} {g y : G} (hg : g ∈ normalizer (H : Set G))
    (hy : y ∈ H) : g * y * g⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hg y).mp hy

private theorem szc_mem_Q_of_pow_eq_one {x : G} (hx : x ∈ t.Qv 0 ⊔ t.K) {j : ℕ}
    (hxj : x ^ 2 ^ j = 1) : x ∈ t.Qv 0 := by
  have hKQ : t.K ≤ normalizer (t.Qv 0 : Set G) := t.K_le_normalizer_Qv 0
  obtain ⟨q, hq, k, hk, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hKQ).1 hx
  have hkodd : Odd (orderOf k) :=
    t.hHall.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨q', hq', h⟩ := A4.exists_pow_mul_eq hq (hKQ hk) (2 ^ j)
  rw [hxj] at h
  have hkj : k ^ 2 ^ j ∈ t.Qv 0 := by
    have : k ^ 2 ^ j = q'⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    rw [this]
    exact inv_mem hq'
  exact mul_mem hq (B1Red.mem_of_two_pow_mem_of_odd hkj hkodd)

private theorem szc_inf_B_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {H : Subgroup G} (hH : H ≤ t.Gv 0) (hK : t.K ≤ H) (hHS : H ⊓ S ≤ t.Qv 0) :
    (H ⊔ t.Qv 0) ⊓ (t.Gv 0 ⊓ t.Gv 1) ≤ t.Qv 0 ⊔ t.K := by
  intro x ⟨hxH, hxB⟩
  rw [t.szc_Gv_inf_eq hfr] at hxB
  obtain ⟨s, hs, k, hk, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (t.szc_K_le_normalizer_S hfr)).1 hxB
  have hQH : H ≤ normalizer (t.Qv 0 : Set G) := hH.trans (t.Gv_le_normalizer_Qv 0)
  have hsHQ : s ∈ H ⊔ t.Qv 0 := by
    have : s = (s * k) * k⁻¹ := by group
    rw [this]
    exact mul_mem hxH (mem_sup_left (inv_mem (hK hk)))
  rw [sup_comm] at hsHQ
  obtain ⟨q, hq, h, hh, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQH).1 hsHQ
  have hhS : h ∈ S := by
    have : h = q⁻¹ * (q * h) := by group
    rw [this]
    exact mul_mem (inv_mem (t.szc_Q_le_S hfr hq)) hs
  have hhQ : h ∈ t.Qv 0 := hHS ⟨hh, hhS⟩
  exact mul_mem (mem_sup_left (mul_mem hq hhQ)) (mem_sup_right hk)

private theorem szc_conj_x₁_inv_mem {y : G} (hy : y ∈ t.Gv 0 ⊓ t.Gv (-1)) :
    t.x₁⁻¹ * y * t.x₁ ∈ t.Gv 0 ⊓ t.Gv 1 := by
  have h0 := t.map_Gv_x₁ 0
  have h1 := t.map_Gv_x₁ 1
  rw [neg_zero] at h0
  refine ⟨?_, ?_⟩
  · have := hy.1
    rw [← h0] at this
    exact mem_map_conj_iff.mp this
  · have := hy.2
    rw [← h1] at this
    exact mem_map_conj_iff.mp this

private theorem szc_two_elt_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 0) (hK : t.K ≤ H)
    (htr : CosetTrans H (t.Gv 0) (t.Gv 1)) (hHS : H ⊓ S ≤ t.Qv 0) {u : G}
    (hu : u ∈ H ⊔ t.Qv 0) {j : ℕ} (huj : u ^ 2 ^ j = 1) : u ∈ t.Qv 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHQ0 : H ⊔ t.Qv 0 ≤ t.Gv 0 := sup_le hH (t.Qv_le_Gv_self 0)
  have hP : IsPGroup 2 (zpowers u) := by
    have hdvd : orderOf u ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one huj
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hPle : zpowers u ≤ t.Gv 0 := (zpowers_le.mpr hu).trans hHQ0
  obtain ⟨g, hg, hPg⟩ := t.exists_le_conj_of_isPGroup hfr 0 hP hPle
  obtain ⟨n, ⟨hnH, hn0⟩, hc⟩ := htr g hg
  have hc0 : n⁻¹ * g ∈ t.Gv 0 := mul_mem (inv_mem hn0) hg
  have hcB : n⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 1 := ⟨hc0, hc⟩
  have hu01 : g⁻¹ * u * g ∈ t.Gv 0 ⊓ t.Gv 1 := by
    have := mem_map_conj_iff.mp (hPg (mem_zpowers u))
    simpa using this
  set c : G := n⁻¹ * g with hcdef
  have hnu : n⁻¹ * u * n = c * (g⁻¹ * u * g) * c⁻¹ := by rw [hcdef]; group
  have hnuB : n⁻¹ * u * n ∈ t.Gv 0 ⊓ t.Gv 1 := by
    rw [hnu]
    exact mul_mem (mul_mem hcB hu01) (inv_mem hcB)
  have hnuH : n⁻¹ * u * n ∈ H ⊔ t.Qv 0 :=
    mul_mem (mul_mem (mem_sup_left (inv_mem hnH)) hu) (mem_sup_left hnH)
  have hnuQK := t.szc_inf_B_le hfr hH hK hHS ⟨hnuH, hnuB⟩
  have hnuj : (n⁻¹ * u * n) ^ 2 ^ j = 1 := by
    have h := conj_pow (a := n⁻¹) (b := u) (i := 2 ^ j)
    rw [inv_inv] at h
    rw [h, huj]; group
  have hnuQ := t.szc_mem_Q_of_pow_eq_one hnuQK hnuj
  have hnN : n ∈ normalizer (t.Qv 0 : Set G) := t.Gv_le_normalizer_Qv 0 hn0
  have := szc_conj_mem hnN hnuQ
  simpa [mul_assoc] using this

private theorem szc_exists_mem_not_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 0) (hK : t.K ≤ H)
    (htr : CosetTrans H (t.Gv 0) (t.Gv 1)) : ∃ h ∈ H ⊓ S, h ∉ t.Qv 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hHS : H ⊓ S ≤ t.Qv 0 := fun h hh => hcon h hh
  set Q := t.Qv 0 with hQdef
  obtain ⟨n, ⟨hnH, hn0⟩, hb1⟩ := htr t.x₁ t.x₁_mem_Gv_zero
  have hb0 : n⁻¹ * t.x₁ ∈ t.Gv 0 := mul_mem (inv_mem hn0) t.x₁_mem_Gv_zero
  have hbB : n⁻¹ * t.x₁ ∈ t.Gv 0 ⊓ t.Gv 1 := ⟨hb0, hb1⟩
  set b : G := n⁻¹ * t.x₁ with hbdef
  have hnb : n = t.x₁ * b⁻¹ := by rw [hbdef]; group
  have hQKm : Q ⊔ t.K ≤ t.Gv 0 ⊓ t.Gv (-1) :=
    sup_le (le_inf (t.Qv_le_Gv_self 0) (t.szc_Q_le_Gv_neg_one hfr))
      (le_inf (t.K_le_Gv 0) (t.K_le_Gv (-1)))
  have hle : Q ⊔ t.K ≤ (Q ⊔ t.K).map (MulAut.conj n).toMonoidHom := by
    intro y hy
    refine mem_map_conj_iff.mpr ?_
    have hyH : n⁻¹ * y * n ∈ H ⊔ Q := by
      have hyHQ : y ∈ H ⊔ Q := (sup_le le_sup_right (hK.trans le_sup_left)) hy
      exact mul_mem (mul_mem (mem_sup_left (inv_mem hnH)) hyHQ) (mem_sup_left hnH)
    have hyB : n⁻¹ * y * n ∈ t.Gv 0 ⊓ t.Gv 1 := by
      have h1 := t.szc_conj_x₁_inv_mem (hQKm hy)
      have : n⁻¹ * y * n = b * (t.x₁⁻¹ * y * t.x₁) * b⁻¹ := by rw [hnb]; group
      rw [this]
      exact mul_mem (mul_mem hbB h1) (inv_mem hbB)
    exact t.szc_inf_B_le hfr hH hK hHS ⟨hyH, hyB⟩
  have hcard : Nat.card ((Q ⊔ t.K).map (MulAut.conj n).toMonoidHom) ≤ Nat.card ↥(Q ⊔ t.K) :=
    (Subgroup.card_map_of_injective (MulAut.conj n).injective).le
  have hM : Q ⊔ t.K = (Q ⊔ t.K).map (MulAut.conj n).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hnQ : n ∈ normalizer (Q : Set G) := t.Gv_le_normalizer_Qv 0 hn0
  have hQmap : Q.map (MulAut.conj n).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnQ
  have hsup : Q ⊔ t.K = Q ⊔ t.K.map (MulAut.conj n).toMonoidHom := by
    conv_lhs => rw [hM]
    rw [Subgroup.map_sup, hQmap]
  have hKo : Odd (Nat.card t.K) := t.hHall.2.1
  have hKno : Odd (Nat.card (t.K.map (MulAut.conj n).toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hQp : IsPGroup 2 Q := t.isPGroup_Qv 0
  have hKQ : t.K ≤ normalizer (Q : Set G) := t.K_le_normalizer_Qv 0
  have hKnQ : t.K.map (MulAut.conj n).toMonoidHom ≤ normalizer (Q : Set G) :=
    (le_sup_right.trans hsup.symm.le).trans (sup_le Subgroup.le_normalizer hKQ)
  have hcop : ∀ {M : Subgroup G}, Odd (Nat.card M) → Q ⊓ M = ⊥ := by
    intro M hM
    obtain ⟨m, hm⟩ := hQp.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hM)
  obtain ⟨m, hmQ, hmK⟩ := Vol2.Ch10.SecB.C11AmS.exists_conj_of_complement hQp hKo hKQ hKnQ
    (hcop hKo) (hcop hKno) hsup
  set y : G := m * n with hydef
  have hyK : y ∈ normalizer (t.K : Set G) := by
    have e1 : t.K.map (MulAut.conj y).toMonoidHom =
        (t.K.map (MulAut.conj n).toMonoidHom).map (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [hydef, mul_assoc]
    have e : t.K.map (MulAut.conj y).toMonoidHom = t.K := by
      rw [e1, hmK, Subgroup.map_map]
      conv_rhs => rw [← Subgroup.map_id t.K]
      congr 1
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e
  have hmG1 : m ∈ t.Gv 1 := t.szc_Q_le_Gv_one hfr hmQ
  have hy0 : y ∈ t.Gv 0 := mul_mem (t.Qv_le_Gv_self 0 hmQ) hn0
  have hyP1 : y ∈ P1 L1 L2 S := by rw [← t.Gv_zero]; exact hy0
  have hx₁1 : t.x₁ ∉ t.Gv 1 := t.x₁_not_mem_Gv_one
  have hyn1 : y ∉ t.Gv 1 := by
    intro hy1
    apply hx₁1
    have hn1 : n ∈ t.Gv 1 := by
      have : n = m⁻¹ * y := by rw [hydef]; group
      rw [this]
      exact mul_mem (inv_mem hmG1) hy1
    have : t.x₁ = n * b := by rw [hbdef]; group
    rw [this]
    exact mul_mem hn1 hb1
  have hreg := t.track.reg₁
  have hya : t.x₁⁻¹ * y ∈ t.Gv 1 := by
    rcases hreg y hyP1 hyK with h | h
    · exact (hyn1 (by rw [t.Gv_one]; exact h)).elim
    · rw [t.Gv_one]; exact h
  have hyx : y * t.x₁ ∈ t.Gv 1 := by
    have hzP1 : y * t.x₁ ∈ P1 L1 L2 S := by
      rw [← t.Gv_zero]; exact mul_mem hy0 t.x₁_mem_Gv_zero
    rcases hreg (y * t.x₁) hzP1 (mul_mem hyK t.track.x₁_norm) with h | h
    · rw [t.Gv_one]; exact h
    · exfalso
      apply hx₁1
      have h' : t.x₁⁻¹ * (y * t.x₁) ∈ t.Gv 1 := by rw [t.Gv_one]; exact h
      have : t.x₁ = (t.x₁⁻¹ * y)⁻¹ * (t.x₁⁻¹ * (y * t.x₁)) := by group
      rw [this]
      exact mul_mem (inv_mem hya) h'
  have hyy : y * y ∈ t.Gv 1 := by
    have : y * y = (y * t.x₁) * (t.x₁⁻¹ * y) := by group
    rw [this]
    exact mul_mem hyx hya
  have hyHQ : y ∈ H ⊔ Q := mul_mem (mem_sup_right hmQ) (mem_sup_left hnH)
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hyo : (y ^ o) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hko, pow_orderOf_eq_one]
  have hyoQ : y ^ o ∈ Q :=
    t.szc_two_elt_mem hfr hH hK htr hHS (pow_mem hyHQ o) hyo
  apply hyn1
  obtain ⟨i, rfl⟩ := ho
  have hyo1 : y ^ (2 * i + 1) ∈ t.Gv 1 := t.szc_Q_le_Gv_one hfr hyoQ
  have hy2i : (y * y) ^ i ∈ t.Gv 1 := pow_mem hyy i
  have hpow : y ^ (2 * i + 1) = (y * y) ^ i * y := by rw [pow_succ, pow_mul, sq]
  have : y = ((y * y) ^ i)⁻¹ * y ^ (2 * i + 1) := by rw [hpow]; group
  rw [this]
  exact mul_mem (inv_mem hy2i) hyo1

private theorem szc_inf_L1_ne_map_x₁ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    S ⊓ L1 ≠ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom := by
  intro heq
  have hTG01 : S ⊓ L1 ≤ t.Gw 0 1 :=
    inf_le_left.trans (by rw [t.Gw_zero_one hfr.hF]; exact le_sup_right)
  have hT'G : (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom ≤ t.Gw (-1) 0 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hTG01
    have e := t.track.map_win_x₁ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 0 1
    rw [neg_zero] at e
    exact h.trans e.le
  have hTGm : S ⊓ L1 ≤ t.Gw (-1) 1 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -1 ∨ 0 ≤ i by omega) with rfl | h3
    · have hy' : y ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom := heq ▸ hy
      exact mem_win_iff.mp (hT'G hy') (-1) le_rfl (by norm_num)
    · exact mem_win_iff.mp (hTG01 hy) i h3 h2
  have hTQ : S ⊓ L1 ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num) (by norm_num)
      hfr.hF.1.h1.sylow.2.1 hTGm
  have hSQ : S = t.Qv 0 ⊔ (S ⊓ L1) := by
    rw [t.Qv_zero, sup_comm]
    exact S_eq_sup_left hfr
  have hSle : S ≤ t.Qv 0 := hSQ.le.trans (sup_le le_rfl hTQ)
  have hQS : (t.Qv 0).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
  have h9 := (t.relIndex_Qv_pCoreOf hfr 0).2
  rw [zero_add, t.pCoreOf_Gw_zero_one hfr, if_pos (by norm_num : Even (0 : ℤ)), hQS] at h9
  have h4 : 1 < (2 ^ (2 * a + 1)) ^ 2 :=
    Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  rw [← h9] at h4
  exact lt_irrefl _ h4

theorem L1_le_oTwoPrime_sup_Qv_zero
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 0) (hK : t.K ≤ H)
    (htr : CosetTrans H (t.Gv 0) (t.Gv 1)) : L1 ≤ oTwoPrime H ⊔ t.Qv 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, ⟨hhH, hhS⟩, hhQ⟩ := t.szc_exists_mem_not_mem hfr hH hK htr
  have hSp : IsPGroup 2 S := hfr.hF.1.h1.pgroup
  have hD1K : t.D1 ≤ t.K := le_sup_left
  have hTsyl : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hQ1 : pCoreOf 2 L1 ≤ t.Qv 0 := by
    rw [t.Qv_zero]
    exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1
  set V : Subgroup G := oTwoPrime H ⊔ t.Qv 0 with hVdef
  have hhV : h ∈ V := by
    have hP : IsPGroup 2 ↥(H ⊓ S) := hSp.to_le inf_le_right
    exact mem_sup_left (le_oTwoPrime_of_isPGroup hP inf_le_left ⟨hhH, hhS⟩)
  set X : Subgroup G := V ⊓ (S ⊓ L1) with hXdef
  have hXT : X ≤ S ⊓ L1 := inf_le_right
  have hVN : t.D1 ≤ normalizer (V : Set G) := fun d hd =>
    F1.le_normalizer_sup (X := zpowers d)
      (zpowers_le.mpr (le_normalizer_oTwoPrime H (hK (hD1K hd))))
      (zpowers_le.mpr (t.K_le_normalizer_Qv 0 (hD1K hd))) (mem_zpowers d)
  have hXD : t.D1 ≤ normalizer (X : Set G) := fun d hd =>
    A4.mem_normalizer_inf (hVN hd) (t.hD1hall.1.trans inf_le_right hd)
  have hX : ¬ X ≤ pCoreOf 2 L1 := by
    intro hXle
    apply hhQ
    have hSQ : S = t.Qv 0 ⊔ (S ⊓ L1) := by
      rw [t.Qv_zero, sup_comm]
      exact S_eq_sup_left hfr
    have hP1Q : P1 L1 L2 S ≤ normalizer (t.Qv 0 : Set G) := by
      rw [← t.Gv_zero]
      exact t.Gv_le_normalizer_Qv 0
    have hTQ : S ⊓ L1 ≤ normalizer (t.Qv 0 : Set G) :=
      inf_le_right.trans ((le_sup_left : L1 ≤ P1 L1 L2 S).trans hP1Q)
    have hhS' : h ∈ t.Qv 0 ⊔ (S ⊓ L1) := hSQ ▸ hhS
    obtain ⟨q, hq, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTQ).1 hhS'
    have hsX : s ∈ X := by
      refine ⟨?_, hs⟩
      have : s = q⁻¹ * (q * s) := by group
      rw [this]
      exact mul_mem (mem_sup_right (inv_mem hq)) hhV
    exact mul_mem hq (hQ1 (hXle hsX))
  have hKI := mem_sup_pCoreOf_of_torus_of_sz hfr.ha hfr.hSz hTsyl t.hD1hall hXT hXD hX
  have hT : ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 → x ∈ V ⊔ pCoreOf 2 L1 := by
    intro x hx hxx
    exact (sup_le_sup_right (inf_le_left : X ≤ V) (pCoreOf 2 L1)) (hKI x hx hxx)
  obtain ⟨n, ⟨hnH, hn0⟩, hb1⟩ := htr t.x₁ t.x₁_mem_Gv_zero
  have hb0 : n⁻¹ * t.x₁ ∈ t.Gv 0 := mul_mem (inv_mem hn0) t.x₁_mem_Gv_zero
  have hbB : n⁻¹ * t.x₁ ∈ bigB L1 L2 S := by
    have h := t.Gw_add_one 0
    rw [zero_add] at h
    rw [← t.Gw_zero_one hfr.hF, h]
    exact ⟨hb0, hb1⟩
  have hBL1 : bigB L1 L2 S ≤ normalizer (L1 : Set G) := bigB_le_normalizer_of_hyp111 hfr.hF.1
  have hP1L1 : P1 L1 L2 S ≤ normalizer (L1 : Set G) := sup_le Subgroup.le_normalizer hBL1
  have hbT : n⁻¹ * t.x₁ ∈ normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
    A4.mem_normalizer_inf (hfr.hN hbB) (hBL1 hbB)
  have hnL1 : n ∈ normalizer (L1 : Set G) := hP1L1 (by rw [← t.Gv_zero]; exact hn0)
  have hnO : n ∈ normalizer (pCoreOf 2 L1 : Set G) := by
    have hL1map : L1.map (MulAut.conj n).toMonoidHom = L1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnL1
    have e : (pCoreOf 2 L1).map (MulAut.conj n).toMonoidHom = pCoreOf 2 L1 := by
      have h := pCoreOf_conjSub n L1
      unfold conjSub at h
      rw [hL1map] at h
      exact h.symm
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e
  have hnV : n ∈ normalizer ((V ⊔ pCoreOf 2 L1 : Subgroup G) : Set G) := by
    have hnV0 : n ∈ normalizer (V : Set G) :=
      F1.le_normalizer_sup (X := zpowers n) (zpowers_le.mpr (le_normalizer_oTwoPrime H hnH))
        (zpowers_le.mpr (t.Gv_le_normalizer_Qv 0 hn0)) (mem_zpowers n)
    exact F1.le_normalizer_sup (X := zpowers n) (zpowers_le.mpr hnV0) (zpowers_le.mpr hnO)
      (mem_zpowers n)
  have hx₁L1 : t.x₁ ∈ normalizer (L1 : Set G) :=
    hP1L1 (by rw [← t.Gv_zero]; exact t.x₁_mem_Gv_zero)
  have hT'syl : IsSylowTwoOf ((S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom) L1 := by
    have hx₁map : L1.map (MulAut.conj t.x₁).toMonoidHom = L1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx₁L1
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₁) hTsyl
    rwa [hx₁map] at h
  have hT' : ∀ x ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom, x * x ∈ pCoreOf 2 L1 →
      x ∈ V ⊔ pCoreOf 2 L1 := by
    intro x hx hxx
    have hw : t.x₁⁻¹ * x * t.x₁ ∈ S ⊓ L1 := mem_map_conj_iff.mp hx
    set y : G := (n⁻¹ * t.x₁) * (t.x₁⁻¹ * x * t.x₁) * (n⁻¹ * t.x₁)⁻¹ with hydef
    have hyT : y ∈ S ⊓ L1 := szc_conj_mem hbT hw
    have hxy : x = n * y * n⁻¹ := by rw [hydef]; group
    have hyy : y * y ∈ pCoreOf 2 L1 := by
      have : y * y = n⁻¹ * (x * x) * n := by rw [hxy]; group
      rw [this]
      have := szc_conj_mem (inv_mem hnO) hxx
      simpa using this
    rw [hxy]
    exact szc_conj_mem hnV (hT y hyT hyy)
  have hfin := le_sup_pCoreOf_of_sylow_ne_of_sz hfr.ha hfr.hSz hTsyl hT'syl
    (t.szc_inf_L1_ne_map_x₁ hfr) hT hT'
  exact hfin.trans (sup_le le_rfl (hQ1.trans le_sup_right))

theorem ArcSz.LX_sup_Qv_zero_eq
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : t.ArcSz X) :
    t.LX X 0 ⊔ t.Qv 0 = L1 ⊔ t.Qv 0 := by
  have hH : t.MX X 0 ≤ t.Gv 0 := inf_le_right
  have hK : t.K ≤ t.MX X 0 := le_inf hX.K_le (t.K_le_Gv 0)
  have htr : CosetTrans (t.MX X 0) (t.Gv 0) (t.Gv 1) := by
    intro g hg
    obtain ⟨n, hn, hng⟩ := hX.trans₀ g hg
    exact ⟨n, ⟨hn, hn.2⟩, hng⟩
  refine le_antisymm (sup_le ?_ le_sup_right) ?_
  · rw [← t.oTwoPrime_Gv_zero hfr]
    exact Subgroup.closure_mono fun x hx => ⟨hH hx.1, hx.2⟩
  · exact sup_le (t.L1_le_oTwoPrime_sup_Qv_zero hfr hH hK htr) le_sup_right

end Track

end CFSG.Quasithin.Stroth.Rq

end
