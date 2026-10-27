module

public import CFSG.Quasithin.H13.KGFactT3J4Lat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LieType.SteinbergBRUnitaryThreePerfect
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3Ker

public section

namespace CFSG.Quasithin.H13.KGT3J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad
open CFSG.Quasithin.A312M24 CFSG.Quasithin.J4Fam

theorem card_sup_two {G : Type*} [Group G] [Finite G] {H P : Subgroup G}
    (hPH : P ≤ Subgroup.normalizer (H : Set G)) {n a u : ℕ} (hP : Nat.card P = 2 ^ n)
    (hH : Nat.card H = 2 ^ a * u) (hu : Odd u) (hG : ¬ 2 ^ (n + 1) ∣ Nat.card G) :
    Nat.card ↥(H ⊔ P) = 2 ^ n * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPH
  have hIP : IsPGroup 2 ↥(H ⊓ P) :=
    (IsPGroup.of_card hP).to_le inf_le_right
  obtain ⟨t, ht⟩ := hIP.exists_card_eq
  have htH : 2 ^ t ∣ 2 ^ a * u := by
    rw [← ht, ← hH]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hta : t ≤ a := by
    by_contra hlt
    have h1 : 2 ^ (a + 1) ∣ 2 ^ a * u :=
      (Nat.pow_dvd_pow 2 (by omega)).trans htH
    rw [pow_succ] at h1
    have h2 : 2 ∣ u := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h2)
  obtain ⟨d, rfl⟩ : ∃ d, a = t + d := ⟨a - t, by omega⟩
  rw [ht, hH, hP] at h
  have hX : Nat.card ↥(H ⊔ P) = 2 ^ d * u * 2 ^ n := by
    have h1 : Nat.card ↥(H ⊔ P) * 2 ^ t = (2 ^ d * u * 2 ^ n) * 2 ^ t := by
      rw [h, pow_add]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [hX]
    ring
  · exfalso
    apply hG
    refine Dvd.dvd.trans ?_ (Subgroup.card_subgroup_dvd_card (H ⊔ P))
    rw [hX, pow_succ]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    exact ⟨2 ^ e * u, by ring⟩

theorem not_dvd_card_J : ¬ 2 ^ 22 ∣ Nat.card J := by
  rw [card_J j4Facts]
  norm_num

theorem card_C0 :
    Nat.card (Subgroup.centralizer (V0 : Set J)) = 2 ^ 18 * 15 := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe D_le_M3).toEquiv, card_Dm j4Facts]
  norm_num

theorem le_of_perfect {G : Type*} [Group G] [Finite G] {R P K : Subgroup G}
    (hPR : P ≤ Subgroup.normalizer (R : Set G)) (hP2 : IsPGroup 2 P) (hKX : K ≤ R ⊔ P)
    (hKp : ⁅K, K⁆ = K) : K ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : R ≤ R ⊔ P := le_sup_left
  have hPX : P ≤ R ⊔ P := le_sup_right
  have hXN : R ⊔ P ≤ Subgroup.normalizer (R : Set G) := sup_le Subgroup.le_normalizer hPR
  have : (R.subgroupOf (R ⊔ P)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  set π : ↥(R ⊔ P) →* ↥(R ⊔ P) ⧸ R.subgroupOf (R ⊔ P) := QuotientGroup.mk' _ with hπ
  have htop : (P.subgroupOf (R ⊔ P)).map π = ⊤ := by
    have h1 : R.subgroupOf (R ⊔ P) ⊔ P.subgroupOf (R ⊔ P) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hRX hPX, Subgroup.subgroupOf_self]
    have h2 : (R.subgroupOf (R ⊔ P)).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
    rw [← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _), ← h1,
      Subgroup.map_sup, h2, bot_sup_eq]
  have hq : IsPGroup 2 ↥((P.subgroupOf (R ⊔ P)).map π) :=
    (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm).map π
  set K' := K.subgroupOf (R ⊔ P) with hK'
  have hK'p : ⁅K', K'⁆ = K' := by
    apply Subgroup.map_injective (R ⊔ P).subtype_injective
    rw [Subgroup.map_commutator, hK', Subgroup.map_subgroupOf_eq_of_le hKX, hKp]
  have himg : K'.map π = ⊥ := by
    refine CFSG.QuasithinUnique.Setup.Layer.eq_bot_of_perfect_of_isPGroup Nat.prime_two ?_
      (hq.to_le (htop ▸ le_top))
    rw [← Subgroup.map_commutator, hK'p]
  intro k hk
  have h1 : π ⟨k, hKX hk⟩ = 1 := by
    have : π ⟨k, hKX hk⟩ ∈ K'.map π := ⟨⟨k, hKX hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [himg] at this
    exact this
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem conj_mem_centralizer {G : Type*} [Group G] {V : Subgroup G} {m c : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    m * c * m⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : m⁻¹ * v * m ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) v).mp hv
    simpa using this
  have h := hc _ hv'
  calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [h]
    _ = m * c * m⁻¹ * v := by group

theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] [Finite G] (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := fun _ hm =>
  CFSG.Quasithin.H13.NQCat.T513.mem_normalizer_of_conj_mem fun _ hc => conj_mem_centralizer hm hc

theorem overgroup_local [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {Y : Subgroup J} (hP : P0 ≤ Y) (hY : Y ≠ ⊤) :
    Y ≤ Hj ∨ Y ≤ Subgroup.centralizer ({J4Loc.z0} : Set J) ∨
      Y ≤ Subgroup.normalizer (V0 : Set J) := by
  by_cases hs : Group.IsSolvable ↥Y
  · exact overgroup_of_solvable hP hs
  · exact CFSG.Quasithin.J4Ov.j4OvergroupLocal_holds Y hP hY hs

theorem sup_le_M3 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {Y : Subgroup J} (hP : P0 ≤ Y)
    (hY : Nat.card Y = 2 ^ 21 * 15) : Y ≤ Subgroup.normalizer (V0 : Set J) := by
  have hF := j4Facts
  have hne : Y ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, card_J hF] at hY
    norm_num at hY
  have hHj : ¬ Y ≤ Hj := by
    intro hYH
    rcases card_of_le_Hj hP hYH with h | ⟨j, hj, hc⟩
    · rw [h, card_Hj hF] at hY
      norm_num at hY
    · rw [hY] at hc
      have h15 : memIdx[j]! = 15 :=
        (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ 21) (by rw [← hc]; ring)).symm
      revert h15
      revert j
      decide
  rcases overgroup_local hP hne with h | h | h
  · exact absurd h hHj
  · rcases CFSG.Quasithin.J4M2.J4M2Lattice hF hP h with h2 | h2 | h2
    · exact absurd h2 hHj
    · exact h2
    · exfalso
      rw [h2, CFSG.Quasithin.J4M2.card_M2 hF] at hY
      norm_num at hY
  · exact h

theorem le_centralizer_V0
    {R : Subgroup J} (hRM : R ≤ Subgroup.normalizer (V0 : Set J)) (hRp : ⁅R, R⁆ = R) {a : ℕ}
    (hRc : Nat.card R = 2 ^ a * 15) : R ≤ Subgroup.centralizer (V0 : Set J) := by
  have hM := j4Facts.mat
  set R' := R.subgroupOf (Subgroup.normalizer (V0 : Set J)) with hR'
  set K := R'.map V0.normalizerMonoidHom with hK
  have hR'p : ⁅R', R'⁆ = R' := by
    apply Subgroup.map_injective (Subgroup.normalizer (V0 : Set J)).subtype_injective
    rw [Subgroup.map_commutator, hR', Subgroup.map_subgroupOf_eq_of_le hRM, hRp]
  have hKp : ⁅K, K⁆ = K := by rw [hK, ← Subgroup.map_commutator, hR'p]
  have hK1 : Nat.card K ∣ 2 ^ a * 15 := by
    rw [← hRc, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv]
    exact Subgroup.card_map_dvd R' V0.normalizerMonoidHom
  have hK2 : Nat.card K ∣ 7 * 24 := by
    have := Subgroup.card_subgroup_dvd_card K
    rwa [CFSG.Quasithin.J4Rad.card_mulAut_V0 hM] at this
  have hcop : Nat.Coprime (Nat.card K) 7 := by
    refine Nat.Coprime.coprime_dvd_left hK1 ?_
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.pow_left _ (by norm_num), by norm_num⟩
  have hK24 : Nat.card K ∣ 2 ^ 3 * 3 ^ 1 :=
    (Nat.Coprime.dvd_of_dvd_mul_left hcop hK2).trans (by norm_num)
  have hKs : Group.IsSolvable K := by
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 hK24
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
    have : Fintype K := Fintype.ofFinite K
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])
  have hbot : K = ⊥ := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hKp
  intro r hr
  have h1 : (⟨r, hRM hr⟩ : ↥(Subgroup.normalizer (V0 : Set J))) ∈ V0.normalizerMonoidHom.ker := by
    have : V0.normalizerMonoidHom ⟨r, hRM hr⟩ ∈ K :=
      ⟨⟨r, hRM hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [MonoidHom.mem_ker, CFSG.Quasithin.J4Rad.normalizerMonoidHom_eq_one_iff'] at h1
  exact h1

theorem le_normalizer_of_M3
    {R : Subgroup J}
    (hRC : R ≤ Subgroup.centralizer (V0 : Set J)) (hPR : P0 ≤ Subgroup.normalizer (R : Set J))
    (hRp : ⁅R, R⁆ = R) (hRP : Nat.card ↥(R ⊔ P0) = 2 ^ 21 * 15)
    (hPM : P0 ≤ Subgroup.normalizer (V0 : Set J)) :
    Subgroup.normalizer (V0 : Set J) ≤ Subgroup.normalizer (R : Set J) := by
  have hF := j4Facts
  have hPC : P0 ≤ Subgroup.normalizer (Subgroup.centralizer (V0 : Set J) : Set J) :=
    hPM.trans (normalizer_le_normalizer_centralizer V0)
  have hC0P : Nat.card ↥(Subgroup.centralizer (V0 : Set J) ⊔ P0) = 2 ^ 21 * 15 :=
    card_sup_two hPC (card_P0 hF.mat hF) card_C0 (by decide) not_dvd_card_J
  have heq : R ⊔ P0 = Subgroup.centralizer (V0 : Set J) ⊔ P0 :=
    Subgroup.eq_of_le_of_card_ge (sup_le_sup_right hRC P0) (by rw [hC0P, hRP])
  have hP2 : IsPGroup 2 P0 := IsPGroup.of_card (card_P0 hF.mat hF)
  intro m hm
  refine CFSG.Quasithin.H13.NQCat.T513.mem_normalizer_of_conj_mem fun x hx => ?_
  have hK : R.map (MulAut.conj m).toMonoidHom ≤ R := by
    refine le_of_perfect hPR hP2 ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      rw [heq]
      exact Subgroup.mem_sup_left (conj_mem_centralizer hm (hRC hr))
    · rw [← Subgroup.map_commutator, hRp]
  exact hK ⟨x, hx, rfl⟩

theorem CV_le_of_mem
    {Z : Subgroup J} (hPZ : P0 ≤ Z) {b : J} (hbCV : b ∈ CV)
    (hbZ : b ∈ Z) (hb3 : orderOf b = 3) : CV ≤ Z := by
  have hF := j4Facts
  have hPN : P0 ≤ Subgroup.normalizer (CV : Set J) := by
    intro p hp
    refine CFSG.Quasithin.H13.NQCat.T513.mem_normalizer_of_conj_mem fun x hx => ?_
    have hpNV := P0_le_NV hp
    refine Subgroup.mem_inf.mpr ⟨Hj.mul_mem (Hj.mul_mem hpNV.1 hx.1) (Hj.inv_mem hpNV.1), ?_⟩
    exact conj_mem_centralizer hpNV.2 hx.2
  have hCVc : Nat.card CV = 2 ^ 18 * 3 := by
    rw [card_CV hF]
    norm_num
  have h1 := card_sup_two hPN (card_P0 hF.mat hF) hCVc (by decide) not_dvd_card_J
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPN
  rw [h1, hCVc, card_P0 hF.mat hF] at h2
  have h3 : Nat.card ↥(CV ⊓ P0) = 2 ^ 18 := by
    have h4 : 2 ^ 21 * 3 * Nat.card ↥(CV ⊓ P0) = 2 ^ 21 * 3 * 2 ^ 18 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h4
  set W := (CV ⊓ P0) ⊔ Subgroup.zpowers b with hW
  have hWCV : W ≤ CV := sup_le inf_le_left (Subgroup.zpowers_le.mpr hbCV)
  have hd1 : 2 ^ 18 ∣ Nat.card W := h3 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hd2 : 3 ∣ Nat.card W := by
    rw [← hb3, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le le_sup_right
  have hd : 2 ^ 18 * 3 ∣ Nat.card W := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd1 hd2
  have hWeq : W = CV :=
    Subgroup.eq_of_le_of_card_ge hWCV (hCVc ▸ Nat.le_of_dvd Nat.card_pos hd)
  rw [← hWeq]
  exact sup_le (inf_le_right.trans hPZ) (Subgroup.zpowers_le.mpr hbZ)

theorem sup_le_M3_of_three [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {E : Subgroup J} {m : ℕ}
    (hm : m = 2 ∨ m = 3) (hZ : Nat.card ↥(E ⊔ P0) = 3 ^ m * 2 ^ 21) {b : J}
    (hbC : b ∈ Subgroup.centralizer (V0 : Set J)) (hbE : b ∈ E) (hb3 : orderOf b = 3) :
    E ⊔ P0 ≤ Subgroup.normalizer (V0 : Set J) := by
  have hF := j4Facts
  have hPZ : P0 ≤ E ⊔ P0 := le_sup_right
  have hs : Group.IsSolvable ↥(E ⊔ P0) := by
    have : Fintype ↥(E ⊔ P0) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hZ, mul_comm])
  have hHj : E ⊔ P0 ≤ Hj → E ⊔ P0 ≤ Subgroup.normalizer (V0 : Set J) := by
    intro hZH
    rcases hm with rfl | rfl
    · have hbCV : b ∈ CV := Subgroup.mem_inf.mpr ⟨hZH (Subgroup.mem_sup_left hbE), hbC⟩
      have hCV := CV_le_of_mem hPZ hbCV (Subgroup.mem_sup_left hbE) hb3
      have hZ9 : Nat.card ↥(E ⊔ P0) = 9 * 2 ^ 21 := by rw [hZ]; norm_num
      exact (le_NV_of_card_nine hPZ hZH hZ9 hCV).trans inf_le_right
    · exfalso
      rcases card_of_le_Hj hPZ hZH with h | ⟨j, hj, hc⟩
      · rw [h, card_Hj hF] at hZ
        norm_num at hZ
      · rw [hZ] at hc
        have h27 : memIdx[j]! = 27 :=
          (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ 21) (by rw [← hc]; ring)).symm
        revert h27
        revert j
        decide
  rcases overgroup_of_solvable hPZ hs with h | h | h
  · exact hHj h
  · rcases CFSG.Quasithin.J4M2.J4M2Lattice hF hPZ h with h2 | h2 | h2
    · exact hHj h2
    · exact h2
    · exfalso
      rw [h2, CFSG.Quasithin.J4M2.card_M2 hF] at hZ
      rcases hm with rfl | rfl <;> norm_num at hZ
  · exact h

theorem core [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {R E : Subgroup J} (hRp : ⁅R, R⁆ = R) {a : ℕ} (hRc : Nat.card R = 2 ^ a * 15)
    (hPR : P0 ≤ Subgroup.normalizer (R : Set J)) (hE3 : IsPGroup 3 ↥E) (hE9 : 9 ≤ Nat.card E)
    (hEP : Nat.card ↥(E ⊔ P0) = Nat.card E * 2 ^ 21) {b : J} (hbR : b ∈ R) (hbE : b ∈ E)
    (hb3 : orderOf b = 3) : E ≤ Subgroup.normalizer (R : Set J) := by
  have hF := j4Facts
  have hRP : Nat.card ↥(R ⊔ P0) = 2 ^ 21 * 15 :=
    card_sup_two hPR (card_P0 hF.mat hF) hRc (by decide) not_dvd_card_J
  have hRPM := sup_le_M3 le_sup_right hRP
  have hRC := le_centralizer_V0 (le_sup_left.trans hRPM) hRp hRc
  have hN := le_normalizer_of_M3 hRC hPR hRp hRP (le_sup_right.trans hRPM)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hE3.exists_card_eq
  have hm23 : m = 2 ∨ m = 3 := by
    have hdvd : 3 ^ m ∣ Nat.card J := hm ▸ Subgroup.card_subgroup_dvd_card E
    rw [card_J hF] at hdvd
    have hm3 : m ≤ 3 := by
      by_contra hm4
      have : 3 ^ 4 ∣ 86775571046077562880 := (pow_dvd_pow 3 (by omega)).trans hdvd
      revert this
      norm_num
    have hm2 : 2 ≤ m := by
      by_contra hm1
      have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  have hZ : Nat.card ↥(E ⊔ P0) = 3 ^ m * 2 ^ 21 := by rw [hEP, hm]
  exact le_sup_left.trans ((sup_le_M3_of_three hm23 hZ (hRC hbR) hbE hb3).trans hN)

end CFSG.Quasithin.H13.KGT3J4
