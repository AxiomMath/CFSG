module

public import CFSG.Quasithin.Vol2.Ch12Sec7L22b
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Vol2.Ch12Sec7FinA
public import CFSG.Quasithin.Vol2.Ch12Sec7L24

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_centralizer_V {V : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) v).1 hv
    simpa using this
  have h := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * v := by group

omit [Finite G] in
theorem le_normalizer_inf_centralizer_V {M V X : Subgroup G} (hXM : X ≤ M)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    X ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ c ∈ M ⊓ Subgroup.centralizer (V : Set G),
      x * c * x⁻¹ ∈ M ⊓ Subgroup.centralizer (V : Set G) := fun x hx c hc =>
    ⟨M.mul_mem (M.mul_mem (hXM hx) hc.1) (M.inv_mem (hXM hx)),
      conj_mem_centralizer_V (hXV hx) hc.2⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key x hx c, fun hc => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hc
  rwa [show x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c by group] at this

theorem R2_le_M {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    R2 T L V ≤ Subgroup.normalizer (L : Set G) := by
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer h.hyp.normalizes
  intro r hr
  have hr1 : r ∈ L ⊔ pCoreOf 2 (L ⊔ T) := ((pCoreOf_le 2 _) hr).1
  exact sup_le Subgroup.le_normalizer ((pCoreOf_le 2 _).trans hLT) hr1

theorem eq_V2_of_corank_le_two (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2)
    (h10 : Lemma12_7_10) {T L V : Subgroup G} {t : G} (hS : Setting1273 G T L V t)
    {B D : Subgroup G} (hBV : B ≤ V) (hm : mQuot V B ≤ 2)
    (hDN : D ≤ Subgroup.normalizer (V : Set G)) (hDB : D ≤ Subgroup.centralizer (B : Set G))
    (hDV : ¬ D ≤ Subgroup.centralizer (V : Set G)) :
    ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom = V2 T L V ∧
      D.map (MulAut.conj l).toMonoidHom ≤
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hV64, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hV2 := isPGroup_V hS.hyp
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hS.hyp.hyp hv⟩
  have hBe : IsElemAbelian 2 B := B2F.isElemAbelian_mono hBV hVe
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hS.hyp.hyp.irrPlus.2.2.1
  have hLM : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hcardB : Nat.card V = 2 ^ mQuot V B * Nat.card B := card_eq_two_pow_mul hV2 hBV
  have hrkB : Nat.card B = 2 ^ rk ↥B := card_eq_two_pow_of_isPGroup (hV2.to_le hBV)
  have hrk : mQuot V B + rk ↥B = 6 := by
    rw [hV64, hrkB, ← pow_add] at hcardB
    exact (Nat.pow_right_injective (le_refl 2) hcardB).symm
  have hB16 : 16 ≤ Nat.card B := by
    rw [hrkB]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ rk ↥B := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨U, hUB, -, hUm⟩ := exists_mem_le_mQuot_eq hBe (c := 3 - mQuot V B) (by omega) B.one_mem
  have hU3 : mQuot V U = 3 := by rw [mQuot_add hUB hBV, hUm]; omega
  have hUV : U ≤ V := hUB.trans hBV
  have hU8 : Nat.card U = 8 := by
    have h := card_eq_two_pow_mul hV2 hUV
    rw [hV64, hU3] at h
    norm_num at h
    omega
  have hDM : D ≤ Subgroup.normalizer (L : Set G) := hDN.trans (normalizer_V_le h331 h1222 hS.hyp)
  have hDU : D ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf hDM (hDB.trans (Subgroup.centralizer_le hUB))
  obtain ⟨d, hdD, hdV⟩ := Set.not_subset.1 hDV
  rcases (h10 G T L V t hS).2.2.2.1 U hUV hU3 with h1 | ⟨l, hl, -, -, hCl⟩ |
      ⟨y, -, -, hy2, hUy, i, hi, hiy, hCi⟩
  ·
    exact absurd (((h1 ▸ hDU) hdD).2) hdV
  ·
    have hlN : l ∈ Subgroup.normalizer (V : Set G) := hLV hl
    have hDl : D.map (MulAut.conj l).toMonoidHom ≤
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V := by
      rw [← hCl]
      rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLM hl) (hDM hx))
        (Subgroup.inv_mem _ (hLM hl)), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, hu, rfl⟩
      have hxu : u * x = x * u := Subgroup.mem_centralizer_iff.1 (hDU hx).2 u hu
      show l * u * l⁻¹ * (l * x * l⁻¹) = l * x * l⁻¹ * (l * u * l⁻¹)
      calc l * u * l⁻¹ * (l * x * l⁻¹) = l * (u * x) * l⁻¹ := by group
        _ = l * (x * u) * l⁻¹ := by rw [hxu]
        _ = l * x * l⁻¹ * (l * u * l⁻¹) := by group
    refine ⟨l, hl, ?_, hDl⟩
    have hR2N : R2 T L V ≤ Subgroup.normalizer
        ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
          Set G) :=
      le_normalizer_inf_centralizer_V (R2_le_M hS.hyp) (R2_le_normalizer h1222 hS.hyp)
    obtain ⟨c, hc, r, hr, hcr⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hR2N).1
      (hDl ⟨d, hdD, rfl⟩)
    change l * d * l⁻¹ = c * r at hcr
    have hrV : r ∉ Subgroup.centralizer (V : Set G) := by
      intro hrV
      apply hdV
      have h1 : l * d * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
        rw [hcr]
        exact Subgroup.mul_mem _ hc.2 hrV
      have h2 := conj_mem_centralizer_V (Subgroup.inv_mem _ hlN) h1
      rwa [show l⁻¹ * (l * d * l⁻¹) * l⁻¹⁻¹ = d by group] at h2
    obtain ⟨-, -, -, -, ⟨hV2line, -, -, -, hR2C, -⟩, -, -⟩ := h2 G T L V hS.hyp
    have hCr := hR2C r hr hrV
    have hBl : B.map (MulAut.conj l).toMonoidHom ≤ V2 T L V := by
      rintro _ ⟨b, hb, rfl⟩
      show l * b * l⁻¹ ∈ V2 T L V
      rw [← hCr]
      have hlb : l * b * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hlN b).1 (hBV hb)
      refine Subgroup.mem_inf.2 ⟨hlb, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hdb : b * d = d * b := Subgroup.mem_centralizer_iff.1 (hDB hdD) b hb
      have hcb : c * (l * b * l⁻¹) = l * b * l⁻¹ * c :=
        (Subgroup.mem_centralizer_iff.1 hc.2 _ hlb).symm
      have hdl : l * b * l⁻¹ * (l * d * l⁻¹) = l * d * l⁻¹ * (l * b * l⁻¹) := by
        calc l * b * l⁻¹ * (l * d * l⁻¹) = l * (b * d) * l⁻¹ := by group
          _ = l * (d * b) * l⁻¹ := by rw [hdb]
          _ = l * d * l⁻¹ * (l * b * l⁻¹) := by group
      rw [hcr] at hdl
      have h3 : c * (l * b * l⁻¹ * r) = c * (r * (l * b * l⁻¹)) := by
        calc c * (l * b * l⁻¹ * r) = (c * (l * b * l⁻¹)) * r := by group
          _ = (l * b * l⁻¹ * c) * r := by rw [hcb]
          _ = l * b * l⁻¹ * (c * r) := by group
          _ = c * r * (l * b * l⁻¹) := hdl
          _ = c * (r * (l * b * l⁻¹)) := by group
      exact mul_left_cancel h3
    have h16 : Nat.card ↥(V2 T L V) = 16 := hV2line.2
    have hcard : Nat.card ↥(V2 T L V) ≤ Nat.card ↥(B.map (MulAut.conj l).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, h16]
      exact hB16
    exact Subgroup.eq_of_le_of_card_ge hBl hcard
  ·
    exfalso
    have hiN := le_normalizer_inf_centralizer_V (M := Subgroup.normalizer (L : Set G)) (V := V)
      ((Subgroup.zpowers_le).2 hi.1) ((Subgroup.zpowers_le).2 hi.2)
    have hdmem : d ∈ (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔
        Subgroup.zpowers i := by
      rw [sup_comm, ← hCi]
      exact hDU hdD
    obtain ⟨c, hc, w, hw, hcw⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hiN).1 hdmem
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
    have hi2 : i * i ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := hiy ⟨v, hv⟩
      have h2 := hiy (y ⟨v, hv⟩)
      rw [← MulAut.mul_apply, hyy, MulAut.one_apply, h1] at h2
      have h3 : v = i * (i * v * i⁻¹) * i⁻¹ := h2
      calc v * (i * i) = i * (i * v * i⁻¹) * i⁻¹ * (i * i) := by rw [← h3]
        _ = i * i * v := by group
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    ·
      apply hdV
      rw [hcw, hm, zpow_mul, zpow_two]
      exact Subgroup.mul_mem _ hc.2 (Subgroup.zpow_mem _ hi2 m)
    ·
      obtain ⟨e, he_eq⟩ : ∃ e : G, e = (i * i) ^ m := ⟨_, rfl⟩
      have he : e ∈ Subgroup.centralizer (V : Set G) := he_eq ▸ Subgroup.zpow_mem _ hi2 m
      have hd : d = c * (e * i) := by rw [hcw, hm, zpow_add, zpow_one, zpow_mul, zpow_two, he_eq]
      have hBU : B ≤ U := by
        intro b hb
        have hbV := hBV hb
        have hx : i * b * i⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hi.2 b).1 hbV
        have hdb : d * b * d⁻¹ = b := by
          have := Subgroup.mem_centralizer_iff.1 (hDB hdD) b hb
          rw [← this]
          group
        have hex : (i * b * i⁻¹) * e = e * (i * b * i⁻¹) :=
          Subgroup.mem_centralizer_iff.1 he _ hx
        have hcx : (i * b * i⁻¹) * c = c * (i * b * i⁻¹) :=
          Subgroup.mem_centralizer_iff.1 hc.2 _ hx
        have hdx : d * b * d⁻¹ = i * b * i⁻¹ := by
          rw [hd]
          calc c * (e * i) * b * (c * (e * i))⁻¹ = c * (e * (i * b * i⁻¹) * e⁻¹) * c⁻¹ := by
                group
            _ = c * (i * b * i⁻¹) * c⁻¹ := by rw [← hex]; group
            _ = i * b * i⁻¹ := by rw [← hcx]; group
        have hib : i * b * i⁻¹ = b := hdx.symm.trans hdb
        have hyb : y ⟨b, hbV⟩ = ⟨b, hbV⟩ := Subtype.ext (by rw [hiy]; exact hib)
        have hfix : (⟨b, hbV⟩ : ↥V) ∈ fixV (Subgroup.zpowers y) := mem_fixV_zpowers.2 hyb
        rw [hUy]
        exact ⟨⟨b, hbV⟩, hfix, rfl⟩
      have := Subgroup.card_le_of_le hBU
      rw [hU8] at this
      omega

theorem not_le_M (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) {H X : Subgroup G}
    (hL1T : L1 T L V ⊔ T = H ⊓ Subgroup.normalizer (L : Set G)) (hXH : X ≤ H)
    (h5 : 5 ∣ Nat.card X) : ¬ X ≤ Subgroup.normalizer (L : Set G) := by
  intro hXM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcomm, -, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  obtain ⟨-, -, -, -, -, ⟨-, hset, -, -⟩, -⟩ := h2 G T L V hS.hyp
  have hL1 : L1 T L V ∈ {I : Subgroup G | I ≤ P1 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
      oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} := by
    rw [hset]
    exact Set.mem_insert _ _
  obtain ⟨-, hTL1, -, hL13⟩ := hL1
  obtain ⟨⟨x, hxX⟩, hx5⟩ := exists_prime_orderOf_dvd_card' 5 h5
  rw [Subgroup.orderOf_mk] at hx5
  have hxLT : x ∈ L1 T L V ⊔ T := by
    rw [hL1T]
    exact ⟨hXH hxX, hXM hxX⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hS.hyp.hyp.sylow.1 hTL1 hxLT
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) := by
    rw [hx5]
    exact Nat.Coprime.pow_left _ (by norm_num)
  have hxL1 : x ∈ L1 T L V := (Subgroup.zpowers_le.2 hk) (A4.mem_zpowers_pow_of_coprime hcop)
  have h5L1 : 5 ∣ Nat.card (L1 T L V) := by
    rw [← hx5]
    exact Subgroup.orderOf_dvd_natCard _ hxL1
  have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 (L1 T L V)) (K := L1 T L V)
  rw [inf_of_le_left (pCoreOf_le 2 _), hL13] at hmul
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (pCoreOf_isPGroup 2 (L1 T L V))
  rw [← hmul, hn] at h5L1
  have hc : Nat.Coprime 5 (3 * 2 ^ n) :=
    Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.pow_right _ (by norm_num))
  exact absurd (Nat.Coprime.eq_one_of_dvd hc h5L1) (by norm_num)

end S127

end CFSG.Quasithin.H13
