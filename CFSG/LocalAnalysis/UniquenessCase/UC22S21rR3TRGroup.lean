module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TTorus
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbs64
import CFSG.LocalAnalysis.GH72.Sec4Basic
import CFSG.Fischer.Aut.Complete
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Blueprint Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3t_not_dvd_card_N0 {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K}) {q : ℕ}
    (hq : q.Prime) (hqL : ¬ q ∣ Nat.card L) :
    ¬ q ∣ Nat.card (uc22r3tN0 D.T D.M L) := by
  have hKL : L ≤ normalizer (K : Set G) := uc22p22u_calC_normalizes hK hL hne
  have hcard : Nat.card (L ⊔ K : Subgroup G) * Nat.card (L ⊓ K : Subgroup G) =
      Nat.card L * Nat.card K :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hKL
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; simp
  obtain ⟨g, -, hgK⟩ := hKmem
  have hκ : Nat.card K = Nat.card L := by
    rw [hgK, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hdiv : Nat.card (L ⊔ K : Subgroup G) ∣ Nat.card L * Nat.card L := by
    have h := hcard
    rw [hκ] at h
    rw [← h]
    exact dvd_mul_right _ _
  have hqsup : ¬ q ∣ Nat.card (L ⊔ K : Subgroup G) := by
    intro hd
    have h1 : q ∣ Nat.card L * Nat.card L := hd.trans hdiv
    rw [← pow_two] at h1
    exact hqL (hq.dvd_of_dvd_pow h1)
  intro hd
  refine hqsup (hd.trans ?_)
  rw [← uc22r3t_conjClosure_eq_sup hset]
  exact Subgroup.card_dvd_of_le (uc22r3tN0_le_conjClosure D.T D.M L)

private theorem uc22r3t_mem_normalizer_N0 {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {b : G} (hbM : b ∈ D.M) (hbT : b ∈ normalizer (D.T : Set G))
    (hbL : b ∈ normalizer (L : Set G)) :
    b ∈ normalizer (uc22r3tN0 D.T D.M L : Set G) := by
  have hX : D.M ≤ normalizer (conjClosure D.M L : Set G) :=
    (uc22p22u_conjClosure_isProd (M := D.M) (X := D.M) le_rfl Subgroup.le_normalizer hL).2.1
  change b ∈ normalizer (((conjClosure D.M L ⊓ normalizer (D.T : Set G) : Subgroup G) ⊓
    normalizer (L : Set G)) : Set G)
  have h1 : b ∈ normalizer ((conjClosure D.M L ⊓ normalizer (D.T : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hX hbM, Subgroup.le_normalizer hbT⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, Subgroup.le_normalizer hbL⟩

private theorem uc22r3t_inducedQuotInfAut_conj (L : Subgroup G) {a x : G}
    (ha : a ∈ normalizer (L : Set G)) (hx : x ∈ normalizer (L : Set G))
    (hax : a * x * a⁻¹ ∈ normalizer (L : Set G)) :
    inducedQuotInfAut L (a * x * a⁻¹) hax =
      inducedQuotInfAut L a ha * inducedQuotInfAut L x hx * (inducedQuotInfAut L a ha)⁻¹ := by
  have h2 : (⟨a * x * a⁻¹, hax⟩ : normalizer (L : Set G)) =
      ⟨a, ha⟩ * ⟨x, hx⟩ * ⟨a, ha⟩⁻¹ := Subtype.ext (by simp)
  calc inducedQuotInfAut L (a * x * a⁻¹) hax
      = inducedQuotInfAutHom L ⟨a * x * a⁻¹, hax⟩ := rfl
    _ = inducedQuotInfAutHom L (⟨a, ha⟩ * ⟨x, hx⟩ * ⟨a, ha⟩⁻¹) := by rw [h2]
    _ = inducedQuotInfAutHom L ⟨a, ha⟩ * inducedQuotInfAutHom L ⟨x, hx⟩ *
        (inducedQuotInfAutHom L ⟨a, ha⟩)⁻¹ := by rw [map_mul, map_mul, map_inv]

private theorem uc22r3t_theta_conj_ne_one_of_mem {L : Subgroup G} {a x : G}
    (ha : a ∈ normalizer (L : Set G)) (hx : x ∈ normalizer (L : Set G))
    (hax : a * x * a⁻¹ ∈ normalizer (L : Set G))
    (hθ : inducedQuotInfAut L x hx ≠ 1) :
    inducedQuotInfAut L (a * x * a⁻¹) hax ≠ 1 := by
  rw [uc22r3t_inducedQuotInfAut_conj L ha hx hax]
  intro h1
  apply hθ
  calc inducedQuotInfAut L x hx
      = (inducedQuotInfAut L a ha)⁻¹ * (inducedQuotInfAut L a ha *
          inducedQuotInfAut L x hx * (inducedQuotInfAut L a ha)⁻¹) *
          inducedQuotInfAut L a ha := by group
    _ = 1 := by rw [h1]; group

private theorem uc22r3t_theta_eq_conj_of_mem_conjClosure {M L K : Subgroup G}
    (hL : L ∈ calC M) (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K})
    {z : G} (hzX : z ∈ conjClosure M L) (hzn : z ∈ normalizer (L : Set G)) :
    ∃ u : BarInf L ⧸ Subgroup.center (BarInf L),
      inducedQuotInfAut L z hzn = MulAut.conj u := by
  have hLK : L ≤ normalizer (K : Set G) := uc22p22u_calC_normalizes hK hL hne
  have hzmem : z ∈ (L : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L K hLK,
      ← uc22r3t_conjClosure_eq_sup hset]
    exact hzX
  obtain ⟨l, hlL, k, hkK, rfl⟩ := Set.mem_mul.1 hzmem
  have hln : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have hkn : k ∈ normalizer (L : Set G) := uc22p22u_calC_normalizes hL hK (Ne.symm hne) hkK
  refine ⟨piBarInf L ⟨l, hlL⟩, ?_⟩
  have hm := inducedQuotInfAut_mul L hln hkn hzn
  rw [hm, uc22r3t_theta_eq_conj hlL hln,
    uc22r3t_theta_eq_one_of_mem_ne hL hK (Ne.symm hne) hkK hkn, mul_one]

private theorem uc22r3t_exists_sylow_normalized {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {q : ℕ} (hq : q.Prime) (hqL : ¬ q ∣ Nat.card L)
    {b : G} (hbM : b ∈ D.M) (hbT : b ∈ normalizer (D.T : Set G))
    (hbL : b ∈ normalizer (L : Set G)) (hbo : orderOf b = q) {r : ℕ} (hr : r.Prime)
    {y : G} (hyN0 : y ∈ uc22r3tN0 D.T D.M L) (hyo : orderOf y = r) :
    ∃ (Q : Subgroup G) (c : G), Q ≤ uc22r3tN0 D.T D.M L ∧ IsPGroup r Q ∧
      b ∈ normalizer (Q : Set G) ∧ c ∈ uc22r3tN0 D.T D.M L ∧ c * y * c⁻¹ ∈ Q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hbN : b ∈ normalizer (uc22r3tN0 D.T D.M L : Set G) :=
    uc22r3t_mem_normalizer_N0 hL hbM hbT hbL
  have hBp : IsPGroup q (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  obtain ⟨Q, hQN0, hQr, hQfull, hBQ⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E.exists_sylow_normalized_of_not_dvd'
      (p := q) (q := r) (uc22r3tN0 D.T D.M L) (Subgroup.zpowers b) hBp
      (Subgroup.zpowers_le.2 hbN) (uc22r3t_not_dvd_card_N0 hL hK hne hset hq hqL)
  have hNne : Nat.card (uc22r3tN0 D.T D.M L) ≠ 0 :=
    Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have hfull : Nat.card Q = r ^ (Nat.card (uc22r3tN0 D.T D.M L)).factorization r := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQr
    have hdvd : r ^ k ∣ Nat.card (uc22r3tN0 D.T D.M L) := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hQN0
    have hkle : k ≤ (Nat.card (uc22r3tN0 D.T D.M L)).factorization r :=
      (hr.pow_dvd_iff_le_factorization hNne).1 hdvd
    have hge : (Nat.card (uc22r3tN0 D.T D.M L)).factorization r ≤ k := by
      have h1 := hQfull _ (Nat.ordProj_dvd (Nat.card (uc22r3tN0 D.T D.M L)) r)
      rw [hk] at h1
      exact (Nat.pow_dvd_pow_iff_le_right hr.one_lt).1 h1
    rw [hk, le_antisymm hkle hge]
  have hyP : IsPGroup r (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hSyl : CFSG.ABGLocalTools.IsSylowOf r Q (uc22r3tN0 D.T D.M L) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hQN0 hfull
  obtain ⟨c, hcN0, hcy⟩ := CFSG.GH72.exists_mem_conj_mem_of_isSylowOf hSyl hyN0 hyP
  exact ⟨Q, c, hQN0, hQr, Subgroup.zpowers_le.1 hBQ, hcN0, hcy⟩

private theorem uc22r3t_exists_barElt {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {q : ℕ} (hSz : IsSz (Bar2 L) q) {r : ℕ}
    (hr : r.Prime) {y c : G} (hcL : c ∈ normalizer (L : Set G))
    (hyL : y ∈ normalizer (L : Set G)) (hyθ : inducedQuotInfAut L y hyL ≠ 1)
    (hzX : c * y * c⁻¹ ∈ conjClosure M L) (hzN : c * y * c⁻¹ ∈ normalizer (L : Set G))
    (hzo : orderOf (c * y * c⁻¹) = r) :
    ∃ u : BarInf L ⧸ Subgroup.center (BarInf L), u ≠ 1 ∧ orderOf u = r ∧
      inducedQuotInfAut L (c * y * c⁻¹) hzN = MulAut.conj u := by
  have hθz : inducedQuotInfAut L (c * y * c⁻¹) hzN ≠ 1 :=
    uc22r3t_theta_conj_ne_one_of_mem hcL hyL hzN hyθ
  obtain ⟨u, hzu⟩ := uc22r3t_theta_eq_conj_of_mem_conjClosure hL hK hne hset hzX hzN
  have hθz_ord : orderOf (inducedQuotInfAut L (c * y * c⁻¹) hzN) = r := by
    have hd := orderOf_inducedQuotInfAut_dvd L hzN
    rw [hzo] at hd
    rcases (Nat.dvd_prime hr).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hθz
    · exact h
  have hu1 : u ≠ 1 := by
    intro h1
    exact hθz (by rw [hzu, h1, map_one])
  have hu2 : orderOf u ∣ r := by
    have h1 : MulAut.conj (u ^ r) = 1 := by
      rw [map_pow, ← hzu, ← hθz_ord]
      exact pow_orderOf_eq_one _
    exact orderOf_dvd_iff_pow_eq_one.2 ((uc22r3t_conj_eq_one_iff hL hSz).1 h1)
  have hdvd : r ∣ orderOf u := by
    rw [← hθz_ord, hzu]
    exact orderOf_map_dvd (MulAut.conj : (BarInf L ⧸ Subgroup.center (BarInf L)) →*
      MulAut (BarInf L ⧸ Subgroup.center (BarInf L))) u
  rcases (Nat.dvd_prime hr).1 hu2 with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hu1
  · exact ⟨u, hu1, h, hzu⟩

private theorem uc22r3t_fixed_of_commute {L : Subgroup G} {b z : G}
    (hbL : b ∈ normalizer (L : Set G)) (hzn : z ∈ normalizer (L : Set G))
    {u : BarInf L ⧸ Subgroup.center (BarInf L)}
    (hzu : inducedQuotInfAut L z hzn = MulAut.conj u)
    (hinj : ∀ v : BarInf L ⧸ Subgroup.center (BarInf L), MulAut.conj v = 1 → v = 1)
    (hcomm : b * z = z * b) :
    inducedQuotInfAut L b hbL u = u := by
  have hbz : b * z * b⁻¹ = z := by rw [hcomm]; group
  have hbzn : b * z * b⁻¹ ∈ normalizer (L : Set G) := by rw [hbz]; exact hzn
  have hθeq : inducedQuotInfAut L (b * z * b⁻¹) hbzn = inducedQuotInfAut L z hzn :=
    congrArg (inducedQuotInfAutHom L) (Subtype.ext hbz)
  have hconjz : inducedQuotInfAut L b hbL * MulAut.conj u * (inducedQuotInfAut L b hbL)⁻¹ =
      MulAut.conj u := by
    rw [← hzu, ← uc22r3t_inducedQuotInfAut_conj L hbL hzn hbzn, hθeq]
  have h2 : MulAut.conj (inducedQuotInfAut L b hbL u) = MulAut.conj u := by
    rw [← CFSG.Fischer.mul_conj_mul_inv]
    exact hconjz
  have h3 : MulAut.conj (inducedQuotInfAut L b hbL u * u⁻¹) = 1 := by
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 : inducedQuotInfAut L b hbL u * u⁻¹ = 1 := hinj _ h3
  rwa [mul_inv_eq_one] at h4

private theorem uc22r3t_ne_commute_of_conj {M L : Subgroup G}
    (hL : L ∈ calC M) {q : ℕ} (hSz : IsSz (Bar2 L) q) (hq : q.Prime) (hq7 : 7 ≤ q)
    {r : ℕ} (hr : r.Prime) (hrq : r ∣ 2 ^ q - 1) {b z : G}
    (hbL : b ∈ normalizer (L : Set G)) (hbo : orderOf b = q)
    (hθ : inducedQuotInfAut L b hbL ∉ (MulAut.conj).range)
    (hzn : z ∈ normalizer (L : Set G)) {u : BarInf L ⧸ Subgroup.center (BarInf L)}
    (hu1 : u ≠ 1) (huo : orderOf u = r) (hzu : inducedQuotInfAut L z hzn = MulAut.conj u)
    (hcomm : b * z = z * b) : False := by
  have hinj : ∀ v : BarInf L ⧸ Subgroup.center (BarInf L), MulAut.conj v = 1 → v = 1 :=
    fun v hv => (uc22r3t_conj_eq_one_iff hL hSz).1 hv
  have hfix : inducedQuotInfAut L b hbL u = u :=
    uc22r3t_fixed_of_commute hbL hzn hzu hinj hcomm
  have hX : IsSz (BarInf L ⧸ Subgroup.center (BarInf L)) q :=
    lieModel_xbar_of_lieModel_bar2 hL.2.2 (center_eq_bot_of_isSz hL.2.2 hSz) hSz
  have hαo : orderOf (inducedQuotInfAut L b hbL) = q := by
    have hd := orderOf_inducedQuotInfAut_dvd L hbL
    rw [hbo] at hd
    rcases (Nat.dvd_prime hq).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) fun h1 => hθ ⟨1, by rw [h1, map_one]⟩
    · exact h
  have hαq : inducedQuotInfAut L b hbL ^ q = 1 := by
    rw [← hαo]; exact pow_orderOf_eq_one _
  have h2q : 2 * q < r := uc22r3t_two_mul_lt_of_dvd hq (by omega) hr hrq
  exact uc22r3t_sz_fixed_false hX hq hαq hθ hr (by omega) (by omega) huo hfix

theorem uc22r3t_exists_rgroup {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {q : ℕ} (hSz : IsSz (Bar2 L) q) {r : ℕ}
    (hr : r.Prime) (hrq : r ∣ 2 ^ q - 1) (hq : q.Prime) (hq7 : 7 ≤ q)
    (hqL : ¬ q ∣ Nat.card L) {b : G} (hbM : b ∈ D.M) (hbo : orderOf b = q)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hθ : inducedQuotInfAut L b hbL ∉ (MulAut.conj).range) :
    ∃ R : Subgroup G, IsPGroup r R ∧ R ≤ D.M ∧ R ≤ normalizer (D.T : Set G) ∧
      b ∈ normalizer (R : Set G) ∧ ∃ z ∈ R, b * z ≠ z * b := by
  obtain ⟨y, hyX, hyL, hyo, hyT, hyθ⟩ :=
    uc22r3t_exists_rElt hL hK hne hset hSz hr hrq
  have hyN0 : y ∈ uc22r3tN0 D.T D.M L := ⟨⟨hyX, hyT⟩, hyL⟩
  obtain ⟨Q, c, hQN0, hQr, hbQ, hcN0, hcy⟩ :=
    uc22r3t_exists_sylow_normalized hL hK hne hset hq hqL hbM hbT hbL hbo hr hyN0 hyo
  refine ⟨Q, hQr, ?_, ?_, hbQ, ?_⟩
  · exact hQN0.trans ((uc22r3tN0_le_conjClosure D.T D.M L).trans
      (uc22p22u_conjClosure_isProd (M := D.M) (X := D.M) le_rfl
        Subgroup.le_normalizer hL).1)
  · exact hQN0.trans (uc22r3tN0_le_normalizer_T D.T D.M L)
  by_contra hcon
  push Not at hcon
  have hzN0 : c * y * c⁻¹ ∈ uc22r3tN0 D.T D.M L := hQN0 hcy
  have hzn : c * y * c⁻¹ ∈ normalizer (L : Set G) :=
    uc22r3tN0_le_normalizer_L D.T D.M L hzN0
  have hcL : c ∈ normalizer (L : Set G) := uc22r3tN0_le_normalizer_L D.T D.M L hcN0
  have hzo : orderOf (c * y * c⁻¹) = r := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
  obtain ⟨u, hu1, huo, hzu⟩ :=
    uc22r3t_exists_barElt hL hK hne hset hSz hr hcL hyL hyθ
      (uc22r3tN0_le_conjClosure D.T D.M L hzN0) hzn hzo
  exact uc22r3t_ne_commute_of_conj hL hSz hq hq7 hr hrq hbL hbo hθ hzn hu1 huo hzu
    (hcon (c * y * c⁻¹) hcy)

end CFSG.LocalAnalysis.UniquenessCase.UC22
