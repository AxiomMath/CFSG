module

public import CFSG.Quasithin.H13.L32NLem14413g
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct
public import CFSG.Quasithin.H13.L32NLem1434
public import CFSG.Quasithin.H13.L32NLem14413b
public import CFSG.Quasithin.Vol2.Ch11SecSZK

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6
open CFSG.Quasithin.H13.L32A
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace XCtx

variable {T L V V₂ X : Subgroup G} {g : G} {C : XCtx G T L V V₂ X g} (K : C.Coords)

@[expose] noncomputable def Coords.res {Y : Subgroup G} (hY : Y ≤ lOne L V₂ ⊔ X ⊔ T) :
    ↥Y →* SL3.S :=
  K.φ.comp (Subgroup.inclusion hY)

theorem Coords.res_surjective {Y : Subgroup G} (hY : Y ≤ lOne L V₂ ⊔ X ⊔ T)
    (hφ : (Y.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤) : Function.Surjective (K.res hY) := by
  intro A
  have hA : A ∈ (Y.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ := hφ ▸ Subgroup.mem_top _
  obtain ⟨⟨y, hyH⟩, hyY, rfl⟩ := hA
  exact ⟨⟨y, hyY⟩, rfl⟩

theorem Coords.card_Lp_quot (h1434 : Lemma1434One) {Lp : Subgroup G}
    (hLp : Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T))
    (hφ : (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤) :
    Nat.card (↥Lp ⧸ CFSG.pCore 2 ↥Lp) = 60 ∨ Nat.card (↥Lp ⧸ CFSG.pCore 2 ↥Lp) = 168 := by
  have hLpH : Lp ≤ lOne L V₂ ⊔ X ⊔ T := le_of_mem_cComp hLp
  have hZ : ⁅quasithinOmegaOneCenter T, Lp⁆ ≠ ⊥ := by
    intro hb
    obtain ⟨⟨l, hlL⟩, hlt⟩ := K.res_surjective hLpH hφ t10
    have hc : K.z * l * K.z⁻¹ * l⁻¹ = 1 := by
      have := Subgroup.commutator_mem_commutator K.hz.2 hlL
      rw [hb, Subgroup.mem_bot] at this
      exact this
    have hN : l ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
      have h2 : Nat.card ↥(fsuV1 T V) = 2 := by simpa using C.s1282.v1.2.1
      rw [normalizer_eq_centralizer_of_card_two h2 K.hz K.hz1, Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      calc K.z * l = (K.z * l * K.z⁻¹ * l⁻¹) * l * K.z := by group
        _ = l * K.z := by rw [hc, one_mul]
    have hX1 := K.inX1_of ⟨l, hLpH hlL⟩ hN
    rw [show K.φ ⟨l, hLpH hlL⟩ = t10 from hlt] at hX1
    exact not_inX1_t10 hX1
  have hLf := Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter C.hyp.fsu.qtke C.hyp.fsu.sylow
    (isLocal_of_mem_cComp_of_sylow C.sylow_H3 C.pCoreOf_H3_ne_bot hLp) hZ
  rcases h1434 G T L C.hyp.hyp Lp hLf with he | hlin
  · obtain ⟨e⟩ := he
    left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  · right
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlin
    rw [Nat.card_congr e.toEquiv, SL3.card_S]

theorem Coords.isPGroup_ker_Lp (h1434 : Lemma1434One) {Lp : Subgroup G}
    (hLp : Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T))
    (hφ : (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤) {l : G} (hl : l ∈ Lp)
    (h1 : K.φ ⟨l, le_of_mem_cComp hLp hl⟩ = 1) : ∃ k : ℕ, l ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLpH : Lp ≤ lOne L V₂ ⊔ X ⊔ T := le_of_mem_cComp hLp
  set ψ := K.res hLpH with hψ
  have hsurj := K.res_surjective hLpH hφ
  have hcard1 : Nat.card ↥Lp = 168 * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv, SL3.card_S]
  have : (CFSG.pCore 2 ↥Lp).Normal := CFSG.pCore_normal
  have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Lp)
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Lp)).exists_card_eq
  have hker : IsPGroup 2 ↥ψ.ker := by
    rcases K.card_Lp_quot h1434 hLp hφ with h60 | h168
    · exfalso
      rw [h60, hn, hcard1] at hcard2
      have h7 : 7 ∣ 60 * 2 ^ n := hcard2 ▸ Dvd.dvd.mul_right (by norm_num : (7 : ℕ) ∣ 168) _
      rcases (Nat.Prime.dvd_mul (by norm_num)).mp h7 with h | h
      · norm_num at h
      · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)
    · rw [h168, hn, hcard1] at hcard2
      exact IsPGroup.of_card (n := n) (by omega)
  obtain ⟨k, hk⟩ := hker ⟨⟨l, hl⟩, h1⟩
  exact ⟨k, by simpa using congrArg (fun x : ↥ψ.ker => ((x : ↥Lp) : G)) hk⟩

theorem Coords.exists_s {Lp : Subgroup G} (hLp : Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T))
    (hφ : (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤) {p : SL3.S} (hp : p ∈ SL3.P0) :
    ∃ s ∈ T ⊓ Lp, ∃ hs : s ∈ lOne L V₂ ⊔ X ⊔ T, K.φ ⟨s, hs⟩ = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLpH : Lp ≤ lOne L V₂ ⊔ X ⊔ T := le_of_mem_cComp hLp
  have hsurj := K.res_surjective hLpH hφ
  have hS : IsSylowTwoOf (T ⊓ Lp) Lp :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' (subnormal_of_mem_cComp hLp) C.sylow_H3
  have hS' := Setup.Wreath.isSylowTwoOf_map_hom hS (K.res hLpH)
  rw [MonoidHom.range_eq_top.mpr hsurj] at hS'
  set P := ((T ⊓ Lp).subgroupOf Lp).map (K.res hLpH) with hP
  have hPle : P ≤ SL3.P0 := by
    rintro _ ⟨⟨t, htL⟩, ht, rfl⟩
    have htT : t ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
    exact Subgroup.mem_inf.mpr ⟨K.inX1_of ⟨t, hLpH htL⟩ (C.s1282.v1.2.2 htT),
      K.inX2_of ⟨t, hLpH htL⟩ (C.TV₂ htT)⟩
  have hPcard : Nat.card P = 8 := by
    obtain ⟨j, hj⟩ := hS'.2.1.exists_card_eq
    have hidx : ¬ 2 ∣ P.index := by
      have := hS'.2.2
      rwa [show (P.subgroupOf ⊤).index = P.relIndex ⊤ from rfl, Subgroup.relIndex_top_right]
        at this
    have hmul := P.card_mul_index
    rw [hj, SL3.card_S] at hmul
    have hj3 : j ≤ 3 := by
      by_contra hj3
      have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have : 2 ^ 4 ∣ 168 := h16.trans (Dvd.intro _ hmul)
      norm_num at this
    rw [hj]
    interval_cases j <;> omega
  have hPeq : P = SL3.P0 := Subgroup.eq_of_le_of_card_ge hPle (by rw [SL3.card_P0, hPcard])
  rw [← hPeq] at hp
  obtain ⟨⟨s, hsL⟩, hs, rfl⟩ := hp
  exact ⟨s, Subgroup.mem_subgroupOf.mp hs, hLpH hsL, rfl⟩

theorem Coords.pow_three {y : G} (hy : y ∈ lOne L V₂ ⊔ X ⊔ T) (hodd : Odd (orderOf y))
    (h83 : K.φ ⟨y, hy⟩ ^ 8 = 1 ∨ K.φ ⟨y, hy⟩ ^ 3 = 1) : K.φ ⟨y, hy⟩ ^ 3 = 1 := by
  refine pow_three_of_odd hodd ?_ h83
  rw [← map_pow]
  have : (⟨y, hy⟩ : ↥(lOne L V₂ ⊔ X ⊔ T)) ^ orderOf y = 1 :=
    Subtype.ext (by simp [pow_orderOf_eq_one])
  rw [this, map_one]

theorem Coords.X_ker {r : G} (hr : r ∈ X) (h1 : K.φ ⟨r, X_le_H3 hr⟩ = 1) :
    ∃ k : ℕ, r ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := K.res (Y := X) X_le_H3 with hψ
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
  have hX : Nat.card ↥X = 3 * 2 ^ m := by
    have h := Subgroup.relIndex_mul_card (pCoreOf 2 X) X
    rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X), C.Y.2.2.2.1, hm] at h
    exact h.symm
  have hXker : Nat.card ↥X = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hker : IsPGroup 2 ↥ψ.ker := by
    have hdvd : Nat.card ψ.ker ∣ 3 * 2 ^ m := hX ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Nat.dvd_mul.mp hdvd
    obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd₂
    rcases (Nat.dvd_prime Nat.prime_three).mp hd₁ with rfl | rfl
    · exact IsPGroup.of_card (n := b) (by rw [← hd, one_mul])
    exfalso
    have hrange : IsPGroup 2 ↥ψ.range := by
      have h2 : Nat.card ψ.range ∣ 2 ^ m := by
        refine ⟨2 ^ b, ?_⟩
        have h3 : 3 * 2 ^ m = 3 * (Nat.card ψ.range * 2 ^ b) := by
          rw [← hX, hXker, ← hd]; ring
        omega
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      exact IsPGroup.of_card hc
    have hXC : X ≤ Subgroup.centralizer ((⁅V₂, X⁆ : Subgroup G) : Set G) := by
      conv_lhs => rw [← C.Y.2.2.1]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨hxX, hodd⟩
      obtain ⟨k, hk⟩ := hrange ⟨ψ ⟨x, hxX⟩, ⟨x, hxX⟩, rfl⟩
      have hk' : ψ ⟨x, hxX⟩ ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have ho : orderOf (ψ ⟨x, hxX⟩) = 1 := by
        have hd1 : orderOf (ψ ⟨x, hxX⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
        have hd2 : orderOf (ψ ⟨x, hxX⟩) ∣ orderOf x := by
          have := orderOf_map_dvd ψ ⟨x, hxX⟩
          rwa [Subgroup.orderOf_mk] at this
        have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
          Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
        have := Nat.dvd_gcd hd1 hd2
        rw [Nat.Coprime.gcd_eq_one hcop] at this
        exact Nat.dvd_one.mp this
      exact (K.φ_eq_one_iff ⟨x, X_le_H3 hxX⟩).mp (orderOf_eq_one_iff.mp ho)
    have hbot : ⁅V₂, X⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hXC hx) v (C.V2X hv)).symm
    have := C.Y.2.2.2.2.1
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨k, hk⟩ := hker ⟨⟨r, hr⟩, h1⟩
  exact ⟨k, by simpa using congrArg (fun x : ↥ψ.ker => ((x : ↥X) : G)) hk⟩

theorem Coords.X_le_Lp {Lp : Subgroup G} (hLp : Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T))
    (hφ : (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤)
    (hN : lOne L V₂ ⊔ X ⊔ T ≤ Subgroup.normalizer (Lp : Set G)) : X ≤ Lp := by
  rw [← C.Y.2.2.1]
  apply (Subgroup.closure_le _).mpr
  rintro y ⟨hyX, hodd⟩
  have hX1 := K.inX1_of ⟨y, X_le_H3 hyX⟩ (C.Y.1 hyX)
  have h3 := K.pow_three (X_le_H3 hyX) hodd (pow_eight_or_three_X1 _ hX1)
  obtain ⟨p, hpl, hpinv⟩ := exists_inv_X1 _ hX1 h3
  obtain ⟨s, ⟨hsT, hsL⟩, hsH, hsp⟩ := K.exists_s hLp hφ (P0list_le p hpl)
  exact absorb K.φ hN X_le_H3 (fun r hr h1 => K.X_ker hr h1) hyX hodd hsL (C.Y.2.1 hsT) hsH
    (by rw [hsp]; exact hpinv)

theorem Coords.L2_ker {r : G} (hr : r ∈ lOne L V₂)
    (h1 : K.φ ⟨r, (le_sup_left.trans le_sup_left : lOne L V₂ ≤ lOne L V₂ ⊔ X ⊔ T) hr⟩ = 1) :
    ∃ k : ℕ, r ^ 2 ^ k = 1 := by
  have hrC := (K.φ_eq_one_iff _).mp h1
  have hrP : r ∈ p128 T L V := C.inf_normalizer_le_p128 (oTwoUpper_le _ hr)
  have hrC₂ : r ∈ Subgroup.centralizer (V₂ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv => Subgroup.mem_centralizer_iff.mp hrC v (C.V2X hv)
  obtain ⟨k, hk⟩ := L128P.isPGroup_centralizer_p128 C.h1222 C.s1282.hyp C.s1282.v1 C.plane.2
    ⟨r, hrP, hrC₂⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem Coords.L2_le_Lp {Lp : Subgroup G} (hLp : Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T))
    (hφ : (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤)
    (hN : lOne L V₂ ⊔ X ⊔ T ≤ Subgroup.normalizer (Lp : Set G)) : lOne L V₂ ≤ Lp := by
  have hL2H : lOne L V₂ ≤ lOne L V₂ ⊔ X ⊔ T := le_sup_left.trans le_sup_left
  apply (Subgroup.closure_le _).mpr
  rintro y ⟨⟨hyL, hyN⟩, hodd⟩
  have hyL2 : y ∈ lOne L V₂ := Subgroup.subset_closure ⟨⟨hyL, hyN⟩, hodd⟩
  have hX2 := K.inX2_of ⟨y, hL2H hyL2⟩ hyN
  have h3 := K.pow_three (hL2H hyL2) hodd (pow_eight_or_three_X2 _ hX2)
  obtain ⟨p, hpl, hpinv⟩ := exists_inv_X2 _ hX2 h3
  obtain ⟨s, ⟨hsT, hsL⟩, hsH, hsp⟩ := K.exists_s hLp hφ (P0list_le p hpl)
  exact absorb K.φ hN hL2H (fun r hr h1 => K.L2_ker hr h1) hyL2 hodd hsL
    (C.T_le_normalizer_L2 hsT) hsH (by rw [hsp]; exact hpinv)

end XCtx

theorem XCtx.quasithinO2QuotientIso_H3 (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (h1434 : Lemma1434One) {T L V V₂ X : Subgroup G} {g : G} (C : XCtx G T L V V₂ X g) :
    quasithinO2QuotientIso (lOne L V₂ ⊔ X ⊔ T) SL3.S := by
  obtain ⟨K⟩ := C.nonempty_coords
  obtain ⟨Lp, hLp, hφ⟩ := K.exists_Lp h39
  have hN := K.normal_Lp h37 hLp hφ
  have hH3 : lOne L V₂ ⊔ X ⊔ T ≤ Lp ⊔ T :=
    sup_le (sup_le ((K.L2_le_Lp hLp hφ hN).trans le_sup_left)
      ((K.X_le_Lp hLp hφ hN).trans le_sup_left)) le_sup_right
  refine quasithinO2QuotientIso_SL3_of_surj C.H3_le_normalizer K.e K.surjective ?_
  rintro ⟨r, hrH, hrC⟩
  obtain ⟨k, hk⟩ := L128P.exists_two_pow_mem_of_le_sup C.hyp.fsu.sylow.1
    (XCtx.T_le_H3.trans hN) hH3 hrH
  have h1 : K.φ ⟨r ^ 2 ^ k, pow_mem hrH _⟩ = 1 :=
    (K.φ_eq_one_iff _).mpr (pow_mem hrC _)
  obtain ⟨j, hj⟩ := K.isPGroup_ker_Lp h1434 hLp hφ hk h1
  refine ⟨k + j, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_add, pow_mul, hj]

end CFSG.Quasithin.H13.L14413
