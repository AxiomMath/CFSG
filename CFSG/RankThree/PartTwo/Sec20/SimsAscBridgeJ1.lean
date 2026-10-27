module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeTypes
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411J1
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeG0
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeJ1Group
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.Sporadic.Schreier.J1Outer
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Walter.PSL2Facts.Even
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Blueprint
open scoped Pointwise

theorem asc82Item1411_J1_le
    (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S)
    (hJ : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃* NativeSporadic.J1))
    (hS : Nat.card (S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 2) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_noSmall h
    (fun _ hAS _ => (relIndex_pCore_le_card_map_of_hyp1411 h hAS).trans hS)
    (noSmall1411_of_J1 h hJ)

namespace AscBridge

variable {G : Type} [Group G] [Finite G]

theorem eq_of_ne_one_of_card_le_two {E : Type*} [Group E] [Finite E] (hE : Nat.card E ≤ 2)
    {a b : E} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (![1, a, b] : Fin 3 → E) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin] at h
  omega

theorem commute_of_mem_normalizer_of_card_le_two {Γ : Type*} [Group Γ] {E : Subgroup Γ}
    [Finite E] (hE : Nat.card E ≤ 2) {x ε : Γ} (hx : x ∈ Subgroup.normalizer (E : Set Γ))
    (hε : ε ∈ E) : x * ε = ε * x := by
  by_cases h1 : ε = 1
  · rw [h1, mul_one, one_mul]
  have hε' : x * ε * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hx ε).mp hε
  have h2 : x * ε * x⁻¹ ≠ 1 := by
    intro h
    apply h1
    have := congrArg (fun y => x⁻¹ * y * x) h
    simpa [mul_assoc] using this
  have heq : (⟨x * ε * x⁻¹, hε'⟩ : E) = ⟨ε, hε⟩ :=
    eq_of_ne_one_of_card_le_two hE (fun h => h2 (congrArg Subtype.val h))
      (fun h => h1 (congrArg Subtype.val h))
  have h3 : x * ε * x⁻¹ = ε := congrArg Subtype.val heq
  calc x * ε = x * ε * x⁻¹ * x := by group
    _ = ε * x := by rw [h3]

theorem card_map_mul_card_inf_inSubgroup_pPrimeCore {G : Type} [Group G] [Finite G]
    {H U : Subgroup G} (hUH : U ≤ H) :
    Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) *
      Nat.card (U ⊓ inSubgroup (CFSG.pPrimeCore 3) H : Subgroup G) = Nat.card U := by
  have h1 := Subgroup.relIndex_mul_card (H := (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)).ker)
    (K := U.subgroupOf H)
  rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk'] at h1
  have h2 : Nat.card (CFSG.pPrimeCore 3 ↥H ⊓ U.subgroupOf H : Subgroup ↥H) =
      Nat.card (U ⊓ inSubgroup (CFSG.pPrimeCore 3) H : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.map_inf_eq _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hUH,
      inf_comm]
    rfl
  have h3 : Nat.card (U.subgroupOf H) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv
  rw [h2, h3] at h1
  exact h1

theorem four_dvd_card_kTwenty_quotient {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    {i j : Fin 4} {P : Subgroup G} (hset : Setting204 G A M L N c T i j P) :
    4 ∣ Nat.card (↥(kTwenty M c) ⧸ CFSG.pCore 2 ↥(kTwenty M c)) := by
  rcases hset.kType with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, hn0, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv]
    have hn1 : n ≠ 0 := by
      obtain ⟨k, rfl⟩ := hn
      omega
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n hn1] at h
    have h8 : 8 ∣ Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) *
        Nat.gcd 3 (2 ^ n - 1) := by
      rw [h]
      refine Dvd.dvd.mul_right ?_ _
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have hcop : Nat.Coprime 8 (Nat.gcd 3 (2 ^ n - 1)) :=
      Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) (by norm_num)
    exact (show (4 : ℕ) ∣ 8 by norm_num).trans (hcop.dvd_of_dvd_mul_right h8)
  · rw [Nat.card_congr (e.trans (Sec4.projSLEquivPSL (GaloisField 2 n))).toEquiv,
      CFSG.Walter.psl2_even_card (by omega)]
    obtain ⟨k, rfl⟩ := hn
    refine Dvd.dvd.mul_right ?_ _
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 (by omega)

section J1


variable {M X T : Subgroup G} {c : G}

theorem yAlpha_eq_top_of_J1
    (hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G))
    (e : ↥(yAlpha M X T c) ≃* NativeSporadic.J1) : yAlpha M X T c = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  haveI := CFSG.pPrimeCore_normal (p := 3) (G := ↥YR)
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  set Yb := yAlpha M X T c with hYbdef
  set Rb := (R.subgroupOf YR).map π with hRbdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYRY : YR ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hRY
  have hYn : (Y.subgroupOf YR).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hYRY
  haveI hYbn : Yb.Normal := hYn.map π (QuotientGroup.mk'_surjective _)
  have hsup : Yb ⊔ Rb = ⊤ := by
    rw [hYbdef, hRbdef, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hRb2 : IsPGroup 2 Rb := (hR2.comap_subtype (K := YR)).map π
  have hZ : Subgroup.center ↥Yb = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [center_J1_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  set C := Subgroup.centralizer (Yb : Set (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)) with hCdef
  have hCn : C.Normal := by
    refine ⟨fun w hw g => Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ Yb := by
      have h := hYbn.conj_mem u hu g⁻¹
      rwa [inv_inv] at h
    have h := Subgroup.mem_centralizer_iff.mp hw _ hu'
    calc u * (g * w * g⁻¹) = g * ((g⁻¹ * u * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
      _ = g * w * g⁻¹ * u := by group
  have hCYb : ∀ w ∈ C, w ∈ Yb → w = 1 := by
    intro w hw hwY
    have hcen : (⟨w, hwY⟩ : ↥Yb) ∈ Subgroup.center ↥Yb := by
      rw [Subgroup.mem_center_iff]
      intro u
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hw u u.2)
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hC2 : IsPGroup 2 C := by
    intro w
    have hw : (w : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) ∈
        ((Yb : Set (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)) * (Rb : Set (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR))) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Yb Rb
        (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hYbn).ge), hsup]
      trivial
    obtain ⟨y, hy, r, hr, hyr⟩ := hw
    obtain ⟨a, ha⟩ := hRb2 ⟨r, hr⟩
    have hra : r ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine hCYb _ (C.pow_mem w.2 _) ?_
    have hy1 : QuotientGroup.mk' Yb y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    have hq : QuotientGroup.mk' Yb ((w : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) ^ 2 ^ a) = 1 := by
      rw [map_pow, ← hyr, map_mul, hy1, one_mul, ← map_pow, hra, map_one]
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hCbot : C = ⊥ := by
    have hle : C ≤ CFSG.pPrimeCore 3 (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) :=
      le_sSup ⟨hCn, Res6.coprime_card_of_isPGroup Nat.prime_three (by norm_num) hC2⟩
    rwa [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3, le_bot_iff] at hle
  rw [eq_top_iff]
  intro z _
  set ψ : MulAut NativeSporadic.J1 := e.symm.trans ((MulAut.conjNormal z).trans e) with hψ
  obtain ⟨g, hg⟩ := (CFSG.Sporadic.Schreier.at_j1_schreier).2.1 ψ
  set y := e.symm g with hydef
  have hconj : ∀ u ∈ Yb, z * u * z⁻¹ =
      (y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) * u * (y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)⁻¹ := by
    intro u hu
    have h1 : ψ (e ⟨u, hu⟩) = g * e ⟨u, hu⟩ * g⁻¹ := by rw [hg]; rfl
    have h2 : MulAut.conjNormal z (⟨u, hu⟩ : ↥Yb) = y * ⟨u, hu⟩ * y⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, hydef, MulEquiv.apply_symm_apply, ← h1, hψ]
      simp
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    simpa using h3
  have hyz : (y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)⁻¹ * z ∈ C := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h := hconj u hu
    calc u * ((y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)⁻¹ * z)
        = (y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)⁻¹ * ((y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) * u *
          (y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)⁻¹) * z := by group
      _ = (y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)⁻¹ * (z * u * z⁻¹) * z := by rw [h]
      _ = (y : ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)⁻¹ * z * u := by group
  rw [hCbot, Subgroup.mem_bot, inv_mul_eq_one] at hyz
  rw [← hyz]
  exact y.2

theorem card_rAlpha_le_two_of_J1 {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (e : ↥(yAlpha M X T c) ≃* NativeSporadic.J1) :
    Nat.card (((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf
      (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map (QuotientGroup.mk'
        (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))))) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  set Rb := (R.subgroupOf YR).map π with hRbdef
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKX : K ≤ X := le_sup_left.trans hKTX
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hKYR : K ≤ YR := hKY.trans le_sup_left
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c)
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have htop := yAlpha_eq_top_of_J1 hRY e
  set eΓ : (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) ≃* NativeSporadic.J1 :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e) with heΓ
  have hΓ : Nat.card (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) = 175560 :=
    (Nat.card_congr eΓ.toEquiv).trans CFSG.Sporadic.J1.card_J1
  have hc3 := Res6.orderOf_c_of_setting204 hset
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hcYR : c ∈ YR := hKYR hcK
  set cb := π ⟨c, hcYR⟩ with hcbdef
  have hcb3 : orderOf cb = 3 := by
    have h1 : cb ^ 3 = 1 := by
      rw [hcbdef, ← map_pow]
      have : (⟨c, hcYR⟩ : ↥YR) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc3, pow_orderOf_eq_one])
      rw [this, map_one]
    refine orderOf_eq_prime h1 fun h => ?_
    rw [hcbdef, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have hdvd : orderOf (⟨c, hcYR⟩ : ↥YR) ∣ Nat.card (CFSG.pPrimeCore 3 ↥YR) := by
      rw [← Subgroup.orderOf_mk _ h]
      exact orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hc3] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card hdvd
  set O := CFSG.Open.pCoreOf 2 K with hOdef
  have hOK : O ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  set E := (O.subgroupOf YR).map π with hEdef
  have hE2 : IsPGroup 2 E :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_subtype (K := YR)).map π
  have hEcard : Nat.card E ≤ 2 := by
    have hK1 := card_map_mul_card_inf_inSubgroup_pPrimeCore hKYR
    have hE1 := card_map_mul_card_inf_inSubgroup_pPrimeCore (hOK.trans hKYR)
    have hinf : O ⊓ K₀ = K ⊓ K₀ :=
      le_antisymm (inf_le_inf_right _ hOK)
        (le_inf (inf_inSubgroup_pPrimeCore_le hset hKYR) inf_le_right)
    replace hE1 : Nat.card E * Nat.card (K ⊓ K₀ : Subgroup G) = Nat.card O := by
      rw [← hinf]
      exact hE1
    replace hK1 : Nat.card ((K.subgroupOf YR).map π) * Nat.card (K ⊓ K₀ : Subgroup G) =
        Nat.card K := hK1
    have hKq : Nat.card K = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) * Nat.card O := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
      congr 1
      exact (Subgroup.card_map_of_injective K.subtype_injective).symm
    have hpos : 0 < Nat.card (K ⊓ K₀ : Subgroup G) := Nat.card_pos
    have hKb : Nat.card ((K.subgroupOf YR).map π) =
        Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) * Nat.card E := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [hK1, hKq, ← hE1, mul_assoc]
    have hdvd : Nat.card ((K.subgroupOf YR).map π) ∣ 175560 :=
      hΓ ▸ Subgroup.card_subgroup_dvd_card _
    rw [hKb] at hdvd
    obtain ⟨m, hm⟩ := hE2.exists_card_eq
    have h4 := four_dvd_card_kTwenty_quotient hset
    have h4E : 4 * 2 ^ m ∣ 175560 := (Nat.mul_dvd_mul_right h4 _).trans (hm ▸ hdvd)
    rw [hm]
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m <;> norm_num
    · exfalso
      have h16 : 16 ∣ 4 * 2 ^ m := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm2
        rw [pow_add]
        exact Dvd.intro (2 ^ k) (by ring)
      have := h16.trans h4E
      norm_num at this
  have hcO : c ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hcK
  have hcE : cb ∈ Subgroup.normalizer (E : Set (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR)) := by
    refine Subgroup.mem_normalizer_fintype fun ε hε => ?_
    obtain ⟨o, ho, rfl⟩ := hε
    refine ⟨⟨c, hcYR⟩ * o * ⟨c, hcYR⟩⁻¹,
      (Subgroup.mem_normalizer_iff.mp hcO _).mp (Subgroup.mem_subgroupOf.mp ho), ?_⟩
    simp only [map_mul, map_inv, hcbdef]
  have hcEc : ∀ ε ∈ E, cb * ε = ε * cb := fun ε hε =>
    commute_of_mem_normalizer_of_card_le_two hEcard hcE hε
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer
      (hset.sylow.le.trans (le_normalizer_normalClosureIn M c)))
  have hRKO : R ⊓ K ≤ O :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => Sec20.mem_normalizer_inf_of_mem (hKR hk) (Subgroup.le_normalizer hk))
      (hR2.to_le inf_le_left)
  have hcr : ∀ r ∈ R, c * r * c⁻¹ * r⁻¹ ∈ O := by
    intro r hr
    refine hRKO ⟨R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKR hcK) r).mp hr) (R.inv_mem hr),
      ?_⟩
    have h : r * c⁻¹ * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hRK hr) _).mp (K.inv_mem hcK)
    have e' : c * r * c⁻¹ * r⁻¹ = c * (r * c⁻¹ * r⁻¹) := by group
    rw [e']
    exact K.mul_mem hcK h
  have hcomm : ∀ x ∈ Rb, x * cb = cb * x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    set ε := cb * π r * cb⁻¹ * (π r)⁻¹ with hεdef
    have hεE : ε ∈ E := by
      refine ⟨⟨c, hcYR⟩ * r * ⟨c, hcYR⟩⁻¹ * r⁻¹, hcr r hrR, ?_⟩
      simp only [map_mul, map_inv, hεdef, hcbdef]
    have hε2 : ε * ε = 1 := by
      have hdvd : orderOf ε ∣ Nat.card E := by
        rw [← Subgroup.orderOf_mk ε hεE]
        exact orderOf_dvd_natCard _
      have hpos : 0 < Nat.card E := Nat.card_pos
      have h2 : orderOf ε ∣ 2 := by
        rcases (show Nat.card E = 1 ∨ Nat.card E = 2 by omega) with h | h
        · rw [h] at hdvd
          exact hdvd.trans (by norm_num)
        · rwa [h] at hdvd
      rw [← sq]
      exact orderOf_dvd_iff_pow_eq_one.mp h2
    have h1 : cb * π r * cb⁻¹ = ε * π r := by rw [hεdef]; group
    have hcbε : cb * ε * cb⁻¹ = ε := by
      rw [hcEc ε hεE, mul_inv_cancel_right]
    have h2 : cb ^ 2 * π r * (cb ^ 2)⁻¹ = π r := by
      calc cb ^ 2 * π r * (cb ^ 2)⁻¹ = cb * (cb * π r * cb⁻¹) * cb⁻¹ := by
            rw [sq, mul_inv_rev]
            group
        _ = cb * (ε * π r) * cb⁻¹ := by rw [h1]
        _ = (cb * ε * cb⁻¹) * (cb * π r * cb⁻¹) := by group
        _ = ε * (ε * π r) := by rw [hcbε, h1]
        _ = π r := by rw [← mul_assoc, hε2, one_mul]
    have h3 : Commute (cb ^ 2) (π r) := by
      have := congrArg (· * cb ^ 2) h2
      simp only [inv_mul_cancel_right] at this
      exact this
    have hcb3' : cb ^ 3 = 1 := by simpa [hcb3] using pow_orderOf_eq_one cb
    have h4 : (cb ^ 2) ^ 2 = cb := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hcb3', one_mul]
    rw [← h4]
    exact (h3.pow_left 2).eq.symm
  have hRb2 : IsPGroup 2 Rb := (hR2.comap_subtype (K := YR)).map π
  exact card_le_two_of_commute_J1 eΓ hcb3 hRb2 hcomm

theorem exists_mul_ne_mul_J1 : ∃ a b : NativeSporadic.J1, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hZ := center_J1_eq_bot
  have hnt : Nontrivial NativeSporadic.J1 := CFSG.Sporadic.J1.fam_j1_simplicity.2.1
  obtain ⟨a, ha⟩ := exists_ne (1 : NativeSporadic.J1)
  have : a ∈ Subgroup.center NativeSporadic.J1 :=
    Subgroup.mem_center_iff.mpr fun b => hcomm b a
  rw [hZ, Subgroup.mem_bot] at this
  exact ha this

theorem isPerfect_J1 : Group.IsPerfect NativeSporadic.J1 := by
  have := CFSG.Sporadic.J1.isSimpleGroup_J1
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup exists_mul_ne_mul_J1).1.1

theorem hyp1411_of_J1 {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (e : ↥(yAlpha M X T c) ≃* NativeSporadic.J1) {G₀ : Subgroup G}
    (hG₀ : Minimal (CoverYR M X T c) G₀) :
    Hyp1411 ↥G₀ (perfectResidual ↥G₀) ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀) ∧
      Nonempty ((perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) ≃*
        NativeSporadic.J1) ∧
      Nat.card (((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  set K₀ := oThreePrimeYR M X T c with hK₀def
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  obtain ⟨hRG, hGYR, hcov⟩ := hG₀.prop
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c)
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have htop := yAlpha_eq_top_of_J1 hRY e
  set eΓ : (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) ≃* NativeSporadic.J1 :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e) with heΓ
  set Φ : ↥G₀ →* ↥YR ⧸ CFSG.pPrimeCore 3 ↥YR := π.comp (Subgroup.inclusion hGYR) with hΦ
  have hGK₀ : G₀ ≤ Subgroup.normalizer (K₀ : Set G) :=
    hGYR.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 YR)
  have hΦs : Function.Surjective Φ := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hx : (x : G) ∈ ((G₀ : Set G) * (K₀ : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right G₀ K₀ hGK₀, hcov]
      exact x.2
    obtain ⟨g, hg, k, hk, hgk⟩ := hx
    obtain ⟨k', hk', hk'k⟩ := Subgroup.mem_map.mp hk
    refine ⟨⟨g, hg⟩, ?_⟩
    have hxe : x = Subgroup.inclusion hGYR ⟨g, hg⟩ * k' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      rw [← hgk]
      exact congrArg _ hk'k.symm
    have hk1 : π k' = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk'
    rw [hΦ, MonoidHom.comp_apply, hxe, map_mul, hk1, mul_one]
  have hO := inSubgroup_pPrimeCore_eq_of_minimal hG₀
  have hΦker : Φ.ker = CFSG.pPrimeCore 3 ↥G₀ := by
    ext g
    rw [MonoidHom.mem_ker, hΦ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h2 : (g : G) ∈ G₀ ⊓ K₀ := ⟨g.2, ⟨_, h, rfl⟩⟩
      have h2' : (g : G) ∈ inSubgroup (CFSG.pPrimeCore 3) G₀ := by
        rw [hO]
        exact h2
      obtain ⟨g', hg', hg'g⟩ := h2'
      have hgg : g' = g := Subtype.ext hg'g
      rw [← hgg]
      exact hg'
    · intro h
      have h2 : (g : G) ∈ inSubgroup (CFSG.pPrimeCore 3) G₀ := ⟨g, h, rfl⟩
      rw [hO] at h2
      obtain ⟨y, hy, hyg⟩ := h2.2
      have hyi : Subgroup.inclusion hGYR g = y := Subtype.ext hyg.symm
      rw [hyi]
      exact hy
  set Ψ : (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) ≃* (↥YR ⧸ CFSG.pPrimeCore 3 ↥YR) :=
    (QuotientGroup.quotientMulEquivOfEq hΦker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs) with hΨ
  have hΨmk : ∀ g : ↥G₀, Ψ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀) g) = Φ g := fun g => rfl
  set eG : (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) ≃* NativeSporadic.J1 := Ψ.trans eΓ with heG
  have hJs : IsSimpleGroup NativeSporadic.J1 := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hsimple : IsSimpleGroup (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hJs eG
  have hJnab := exists_mul_ne_mul_J1
  have hnab : ∃ a b : ↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJnab
    refine ⟨eG.symm a, eG.symm b, fun h => hab ?_⟩
    have := congrArg eG h
    simpa using this
  obtain ⟨hqs, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have hF : CFSG.generalizedFitting (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) = ⊤ :=
    CFSG.WholeGroup.generalizedFitting_eq_top_of_isQuasisimple hqs
  have hperf : Group.IsPerfect (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) := hqs.1
  have hnt : Nontrivial (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) := hsimple.toNontrivial
  have hLchar := (CFSG.perfect_residual_characterization (G := ↥G₀)).2.1
  have hLperf := (CFSG.perfect_residual_characterization (G := ↥G₀)).2.2.1
  have hLmap : (perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) = ⊤ := by
    haveI hn : ((perfectResidual ↥G₀).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))) with h | h
    · exfalso
      have hle : perfectResidual ↥G₀ ≤ CFSG.pPrimeCore 3 ↥G₀ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
        exact h
      have hsolv : Group.IsSolvable (↥G₀ ⧸ CFSG.pPrimeCore 3 ↥G₀) :=
        ((CFSG.perfect_residual_characterization (G := ↥G₀)).2.2.2.2.1 _).mpr hle
      exact Group.IsPerfect.not_isSolvable _ hsolv
    · exact h
  have hLO : perfectResidual ↥G₀ ⊔ CFSG.pPrimeCore 3 ↥G₀ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀) g ∈
        (perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) := by
      rw [hLmap]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, hlg⟩ := hg
    have hk : l⁻¹ * g ∈ CFSG.pPrimeCore 3 ↥G₀ := by
      rw [← QuotientGroup.eq]
      exact hlg
    have e' : g = l * (l⁻¹ * g) := by group
    rw [e']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hk)
  set S₀ := R.subgroupOf G₀ with hS₀def
  have hQS : CFSG.pCore 2 ↥G₀ ≤ S₀ := by
    intro g hg
    rw [hS₀def, Subgroup.mem_subgroupOf]
    exact pCoreOf_le_of_minimal hset hX hG₀ ⟨g, hg, rfl⟩
  have hmin : ∀ H : Subgroup ↥G₀, CFSG.pCore 2 ↥G₀ ≤ H → H ⊔ CFSG.pPrimeCore 3 ↥G₀ = ⊤ →
      H = ⊤ := fun H hQH hcovH => eq_top_of_minimal hset hX hG₀ H hQH hcovH
  have hSL : S₀ ⊔ perfectResidual ↥G₀ = ⊤ := by
    refine hmin _ (hQS.trans le_sup_left) ?_
    rw [eq_top_iff, ← hLO]
    exact sup_le_sup_right le_sup_right _
  refine ⟨⟨generalizedFitting_eq_of_minimal hset hX hG₀, inferInstance,
    (Subgroup.isPerfect_iff).mp hLperf, hF.trans hLmap.symm, hR2.comap_subtype, hQS, hSL,
    hmin⟩, ⟨(MulEquiv.subgroupCongr hLmap).trans (Subgroup.topEquiv.trans eG)⟩, ?_⟩
  have hS : (S₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))).map Ψ.toMonoidHom =
      (R.subgroupOf YR).map π := by
    ext z
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨Subgroup.inclusion hGYR s, hs, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxR : (x : G) ∈ R := hx
      refine ⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀) ⟨x, hRG hxR⟩,
        ⟨⟨x, hRG hxR⟩, hxR, rfl⟩, ?_⟩
      rfl
  rw [← Subgroup.card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective, hS]
  exact card_rAlpha_le_two_of_J1 hset hX e

end J1

end AscBridge

open AscBridge in
theorem step204AscJ1_holds :
    Step204AscJ1 := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2 hYK ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hRdef
  obtain ⟨G₀, hG₀⟩ := exists_minimal_coverYR M X T c
  obtain ⟨hhyp, hJ, hS⟩ := hyp1411_of_J1 hset hX e hG₀
  obtain ⟨i₁, i₂, h12, h1, h2, hn1, hn2⟩ := asc82Item1411_J1_le ↥G₀ _ _ hhyp hJ hS
  obtain ⟨k, hk1, hk2⟩ :=
    Res6.exists_mem_inter_of_ne h12 h1 h2 hset.ne hset.ne_three_left hset.ne_three_right
  have hkn : (Sec18.fourChar (R.subgroupOf G₀) k).Normal := by
    rcases hk1 with rfl | rfl
    · exact hn1
    · exact hn2
  have hk3 : k ≠ 3 := by
    rcases hk2 with rfl | rfl
    · exact hset.ne_three_left
    · exact hset.ne_three_right
  have hRG : R ≤ G₀ := hG₀.prop.1
  have hmap := Res5.map_fourChar_subgroupOf hRG k hk3
  have hGN : G₀ ≤ Subgroup.normalizer (Sec18.fourChar R k : Set G) := by
    intro g hg
    rw [← hmap]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hkn.conj_mem y hy ⟨g, hg⟩, ?_⟩
    simp
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hRY : R ≤ Subgroup.normalizer (yTwenty X c : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c)
  have hY : Group.IsPerfect ↥(yAlpha M X T c) := by
    have := isPerfect_J1
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcov := coveredByNormalizer_of_coverYR hRY hY hG₀.prop hGN
  rcases hk2 with rfl | rfl
  · exact Or.inl hcov
  · exact Or.inr hcov

end CFSG.RankThree.PartTwo.Sec20
