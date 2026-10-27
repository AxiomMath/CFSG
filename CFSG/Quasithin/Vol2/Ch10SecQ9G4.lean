module

public import CFSG.Quasithin.Vol2.Ch10SecQ34NC
public import CFSG.Quasithin.Vol2.Ch10SecB3Ind
public import CFSG.Quasithin.Vol2.Ch10SecQ9G2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

namespace RCtx

variable {T L I R H : Subgroup G} (c : RCtx T L I R H)
include c

theorem false_of_natural (hK : LocalSQTK G) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {t : G} (ht : t ∈ T)
    {X K : Subgroup G} (hX : X = L ∨ X = CFSG.conjugate L t)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X ≤ K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (he0 : IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup ↥(modO2Image H K)))
    (hnat : NaturalSL2Action p ↥(modO2Image H K) (CFSG.fittingSubgroup ↥(modO2Image H K)))
    {O : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hO : O = (CFSG.fittingSubgroup ↥(modO2Image H K)).map (modO2Image H K).subtype)
    (N : Subgroup ↥(modO2Image H X ⊔ O)) [N.Normal]
    (hN : N = O.subgroupOf (modO2Image H X ⊔ O))
    (h5 : IsSL2 5 (↥(modO2Image H X ⊔ O) ⧸ N)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.hyp
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set F := CFSG.fittingSubgroup ↥(modO2Image H K) with hF
  set Fb := F.map (modO2Image H K).subtype with hFb
  obtain ⟨-, -, hXL0, ⟨eX⟩⟩ := SecB.li_data h37 h38 hyp ht hX
  have hXH : X ≤ H := hXL0.trans c.fsuL0_le
  have hKbN : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have h1 := SecB.modO2Image_le_normalizer' (H := H) (A := H) (B := K) hKn
    have h2 : modO2Image H H = ⊤ := by
      rw [modO2Image, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rwa [h2] at h1
  have hFn : Fb.Normal := by
    refine ⟨fun f hf g => ?_⟩
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := modO2Image H K) (CFSG.fittingSubgroup ↥(modO2Image H K)) (hKbN (Subgroup.mem_top g))
    exact (Subgroup.mem_normalizer_iff.mp h1 f).mp hf
  have hFnil : Group.IsNilpotent ↥Fb :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (modO2Image H K).subtype_injective)
  have hFF : Fb ≤ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := le_sSup ⟨hFn, hFnil⟩
  obtain ⟨e0⟩ := he0
  have hcardF : Nat.card ↥F = p ^ 2 := by
    rw [Nat.card_congr (e0.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
  have hcardFb : Nat.card ↥Fb = p ^ 2 := by
    rw [hFb, Subgroup.card_map_of_injective (modO2Image H K).subtype_injective, hcardF]
  have hOodd : Odd (Nat.card ↥O) := by rw [hO, hcardFb]; exact hpodd.pow
  have hOn : O.Normal := by rw [hO]; exact hFn
  have hsL : IsSimpleGroup (ModO2 L) := SecA.isSimpleGroup_of_not_normal h37 h38
    hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  obtain ⟨fX⟩ := SecB.nonempty_modO2_modO2Image hXH
  have hsX : IsSimpleGroup (↥(modO2Image H X) ⧸ CFSG.pCore 2 ↥(modO2Image H X)) :=
    (fX.trans eX).isSimpleGroup
  obtain ⟨x, hx, hxinv⟩ :=
    SecB.C10P34.exists_mem_conj_eq_inv (SecB.modO2Image_mono' hXK) hO hp2 hnat N hN h5
  have hXO : modO2Image H X ⊓ O = ⊥ := SecB.C10P34.inf_eq_bot_of_sl2_five hOodd hsX N hN h5
  have hFnt : Nontrivial ↥F := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardF]
    exact one_lt_pow₀ hp.one_lt (by norm_num)
  obtain ⟨f₀, hf₀⟩ := exists_ne (1 : ↥F)
  set fH : ↥H ⧸ CFSG.pCore 2 ↥H := ((f₀ : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H) with hfH
  have hfHFb : fH ∈ Fb := ⟨f₀, f₀.2, rfl⟩
  have hfH1 : fH ≠ 1 := by
    intro h
    apply hf₀
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hord : orderOf fH ∣ p ^ 2 := by
    have h1 := orderOf_dvd_natCard (⟨fH, hfHFb⟩ : ↥Fb)
    rwa [Subgroup.orderOf_mk, hcardFb] at h1
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) fH
  have hwF : (w : G) ∈ oTwoFIn H := C2Six.mem_oTwoFIn_iff.mpr (by
    rw [show (QuotientGroup.mk w : ↥H ⧸ CFSG.pCore 2 ↥H) = fH from hw]
    exact hFF hfHFb)
  have hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      (⟨(w : G), C2Six.oTwoFIn_le hwF⟩ : ↥H))).Coprime 3 := by
    rw [show (⟨(w : G), C2Six.oTwoFIn_le hwF⟩ : ↥H) = w from rfl, hw]
    exact Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left 2
      ((Nat.coprime_primes hp Nat.prime_three).mpr (by omega)))
  have hwM : (w : G) ∈ fsuM T L := c.mem_fsuM_of_coprime_three hK h331 h37 h38 hwF hcop
  have hnodd : Odd (orderOf fH) := (hpodd.pow (n := 2)).of_dvd_nat hord
  have hwn : w ^ orderOf fH ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow,
      show (QuotientGroup.mk w : ↥H ⧸ CFSG.pCore 2 ↥H) = fH from hw, pow_orderOf_eq_one]
  obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (⟨_, hwn⟩ : ↥(CFSG.pCore 2 ↥H))
  have hb' : (w ^ orderOf fH) ^ 2 ^ b = 1 := by
    have h1 := congrArg Subtype.val hb
    simpa using h1
  have hw'n : ((w ^ 2 ^ b : ↥H) : G) ^ orderOf fH = 1 := by
    rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, hb', Subgroup.coe_one]
  have hw'M : ((w ^ 2 ^ b : ↥H) : G) ∈ fsuM T L := by
    rw [Subgroup.coe_pow]
    exact pow_mem hwM _
  have hw'N : ((w ^ 2 ^ b : ↥H) : G) ∈ Subgroup.normalizer (X : Set G) := by
    rcases hX with h | h
    · rw [h]
      exact SecB.mem_normalizer_of_pow_prime h37 h38 hyp hw'M hnodd hw'n
    · rw [h]
      exact SecB.mem_normalizer_conjugate_of_pow_prime h37 h38 hyp hw'M hnodd hw'n ht
  set g : ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk (w ^ 2 ^ b) with hg
  have hgf : g = fH ^ 2 ^ b := by
    rw [hg, QuotientGroup.mk_pow, show (QuotientGroup.mk w : ↥H ⧸ CFSG.pCore 2 ↥H) = fH from hw]
  have hgO : g ∈ O := by
    rw [hO, hgf]
    exact pow_mem hfHFb _
  have hg1 : g ≠ 1 := by
    rw [hgf]
    intro h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hnodd
      exact Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hk0⟩) hnodd
    rw [hk0, pow_zero] at hk
    exact hfH1 (orderOf_eq_one_iff.mp hk)
  have hgN : ∀ y ∈ modO2Image H X, g * y * g⁻¹ ∈ modO2Image H X := by
    intro y hy
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨w ^ 2 ^ b * y0 * (w ^ 2 ^ b)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hy0 ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp hw'N (y0 : G)).mp hy0
      simpa using h1
    · simp only [map_mul, map_inv, QuotientGroup.mk'_apply, hg]
  have hcomm : g * x * g⁻¹ * x⁻¹ ∈ modO2Image H X ⊓ O := by
    refine ⟨(modO2Image H X).mul_mem (hgN x hx) ((modO2Image H X).inv_mem hx), ?_⟩
    have h1 : x * g⁻¹ * x⁻¹ ∈ O := hOn.conj_mem _ (O.inv_mem hgO) x
    have e : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
    rw [e]
    exact O.mul_mem hgO h1
  rw [hXO, Subgroup.mem_bot] at hcomm
  have hgx : x * g * x⁻¹ = g := by
    have h1 : g * x = x * g := by
      calc g * x = (g * x * g⁻¹ * x⁻¹) * (x * g) := by group
        _ = x * g := by rw [hcomm, one_mul]
    calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [h1]
      _ = g := by group
  have hinv := hxinv g hgO
  rw [hgx] at hinv
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    calc g * g = g * g⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel g
  have hgord : orderOf g ∣ p ^ 2 := by
    have h1 := orderOf_dvd_natCard (⟨g, hgO⟩ : ↥O)
    rwa [Subgroup.orderOf_mk, hO, hcardFb] at h1
  have hgodd : Odd (orderOf g) := (hpodd.pow (n := 2)).of_dvd_nat hgord
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg2) with h | h
  · exact hg1 (orderOf_eq_one_iff.mp h)
  · rw [h] at hgodd
    exact Nat.not_odd_iff_even.mpr even_two hgodd

end RCtx

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
