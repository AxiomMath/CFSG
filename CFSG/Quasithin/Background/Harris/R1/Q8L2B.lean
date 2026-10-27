module

public import CFSG.Quasithin.Background.Harris.R1.Q8Ker
public import CFSG.Quasithin.Background.Harris.R1.Q8Aux

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

theorem card_quot_sup_zpowers_seven {P : Subgroup G} {t : G}
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (ht7 : orderOf t = 7) (hP7 : ¬ 7 ∣ Nat.card P) :
    Nat.card (↥(P ⊔ Subgroup.zpowers t) ⧸
      P.subgroupOf (P ⊔ Subgroup.zpowers t)) = 7 := by
  classical
  have hp7 : Nat.Prime 7 := by norm_num
  set H : Subgroup G := P ⊔ Subgroup.zpowers t with hH
  have hPH : P ≤ H := le_sup_left
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHn : H ≤ Subgroup.normalizer (P : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htP)
  haveI hN : (P.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHn
  show Nat.card (↥H ⧸ P.subgroupOf H) = 7
  ·
    let φ : Subgroup.zpowers t →* ↥H ⧸ P.subgroupOf H :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion (le_sup_right : Subgroup.zpowers t ≤ H))
    have hφ : Function.Surjective φ := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨l, hl, w, hw, hx⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
          (show Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) from
            Subgroup.zpowers_le.mpr htP)).mp x.2
        refine ⟨⟨w, hw⟩, ?_⟩
        show QuotientGroup.mk (Subgroup.inclusion _ ⟨w, hw⟩) = QuotientGroup.mk x
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hwN : w⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
          (Subgroup.normalizer (P : Set G)).inv_mem (Subgroup.zpowers_le.mpr htP hw)
        have h1 := (Subgroup.mem_normalizer_iff.mp hwN l).mp hl
        show w⁻¹ * (x : G) ∈ P
        rw [hx]
        have e : w⁻¹ * (l * w) = w⁻¹ * l * w⁻¹⁻¹ := by group
        rw [e]; exact h1
    have hd : Nat.card (↥H ⧸ P.subgroupOf H) ∣ 7 := by
      have := Subgroup.card_dvd_of_surjective hφ
      rwa [Nat.card_zpowers, ht7] at this
    rcases (Nat.dvd_prime hp7).mp hd with h1 | h1
    · exfalso
      have hall : ∀ x : ↥H, x ∈ P.subgroupOf H := by
        intro x
        have := Subgroup.index_eq_one.mp h1
        rw [this]; exact Subgroup.mem_top x
      have htL : t ∈ P := Subgroup.mem_subgroupOf.mp (hall ⟨t, htH⟩)
      have : orderOf (⟨t, htL⟩ : ↥P) ∣ Nat.card P := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, ht7] at this
      exact hP7 this
    · exact h1

theorem card_sup_zpowers_seven {P : Subgroup G} {t : G} (htP : t ∈ Subgroup.normalizer (P : Set G))
    (ht7 : orderOf t = 7) (hP7 : ¬ 7 ∣ Nat.card P) :
    Nat.card ↥(P ⊔ Subgroup.zpowers t) = 7 * Nat.card P := by
  classical
  set H : Subgroup G := P ⊔ Subgroup.zpowers t with hH
  have hPH : P ≤ H := le_sup_left
  have hHn : H ≤ Subgroup.normalizer (P : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htP)
  haveI hN : (P.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHn
  have hNc : Nat.card (P.subgroupOf H) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf H),
    card_quot_sup_zpowers_seven htP ht7 hP7, hNc]

theorem bigB_eq_borelOf {K1 L2 S Zs : Subgroup G} (hset : R1SettingLegacyBare K1 L2 S Zs)
    (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) : bigB K1 L2 S = borelOf K1 S := by
  have hSB : S ≤ borelOf K1 S := by
    have := F1.sylow_le_borelOf K1 S
    rwa [inf_eq_left.mpr hSK] at this
  refine le_antisymm (sup_le (sup_le le_rfl ((F112J2.borelOf_L2_le_S hset hR).trans hSB)) hSB)
    (le_sup_left.trans le_sup_left)

theorem borelOf_le_normalizer_S {K1 S : Subgroup G} (hSK : S ≤ K1) :
    borelOf K1 S ≤ Subgroup.normalizer (S : Set G) := by
  have := (F1.borelOf_le_normalizer K1 S)
  rwa [inf_eq_left.mpr hSK] at this

theorem card_borelOf {K1 L2 S Zs : Subgroup G} {Ω : Type} [Fintype Ω]
    (C : FamCtx K1 L2 S Zs Ω) (hc9 : Fintype.card Ω = 9) :
    9 * Nat.card ↥(borelOf K1 S) = Nat.card ↥K1 := by
  classical
  letI : MulAction ↥K1 Ω := MulAction.compHom Ω C.D.act
  have : MulAction.IsPretransitive ↥K1 Ω := ⟨fun x y => by
    refine ⟨C.D.kf y * (C.D.kf x)⁻¹, ?_⟩
    show C.D.act (C.D.kf y * (C.D.kf x)⁻¹) x = y
    have h1 : C.D.act (C.D.kf x)⁻¹ x = C.D.pt := by
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact (C.D.kf_spec x).symm
    rw [map_mul, Equiv.Perm.mul_apply, h1, C.D.kf_spec]⟩
  have hidx : (MulAction.stabilizer ↥K1 C.D.pt).index = 9 := by
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, hc9]
  have h2 : 9 * Nat.card (MulAction.stabilizer ↥K1 C.D.pt) = Nat.card ↥K1 := by
    rw [← hidx]
    exact Subgroup.index_mul_card _
  have hst : MulAction.stabilizer ↥K1 C.D.pt = (borelOf K1 S).subgroupOf K1 := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact C.D.stab k
  rw [hst, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F1.borelOf_le K1 S)).toEquiv] at h2
  exact h2

theorem card_L2S {K1 L2 S Zs : Subgroup G} {Ω : Type} (C : FamCtx K1 L2 S Zs Ω) :
    Nat.card ↥(L2 ⊔ S) = 3 * Nat.card ↥S := by
  have h3 : S.relIndex (L2 ⊔ S) = 3 := F112J2.relIndex_L2S C.hR C.h.s3
  have h := Subgroup.index_mul_card (S.subgroupOf (L2 ⊔ S))
  have hc : Nat.card (S.subgroupOf (L2 ⊔ S)) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [hc] at h
  rw [← h]
  rw [Subgroup.relIndex] at h3
  rw [h3]

theorem card_L2B {K1 L2 S Zs : Subgroup G} {Ω : Type} [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hc9 : Fintype.card Ω = 9) (hL : IsL2Quot 3 (OTwoQuot K1)) (hSK : S ≤ K1)
    (hK : Nat.card ↥K1 = 258048) (hS : Nat.card ↥S = 2 ^ 12) :
    Nat.card ↥(L2 ⊔ bigB K1 L2 S) = 86016 := by
  classical
  have hp7 : Nat.Prime 7 := by norm_num
  have hB := bigB_eq_borelOf C.h C.hR hSK
  have hB1 : Nat.card ↥(borelOf K1 S) = 28672 := by
    have := card_borelOf C hc9
    omega
  obtain ⟨t, htK, htB, ht7⟩ := exists_order_seven C hc9 hL
  have htS : t ∈ Subgroup.normalizer (S : Set G) := borelOf_le_normalizer_S hSK htB
  have hn7 : ¬ 7 ∣ Nat.card ↥S := by
    rw [hS]
    intro h
    have := hp7.dvd_of_dvd_pow h
    omega
  have hSt := card_sup_zpowers_seven htS ht7 hn7
  have hSB : S ≤ borelOf K1 S := by
    have := F1.sylow_le_borelOf K1 S
    rwa [inf_eq_left.mpr hSK] at this
  have hSt_eq : S ⊔ Subgroup.zpowers t = borelOf K1 S :=
    Subgroup.eq_of_le_of_card_ge (sup_le hSB (Subgroup.zpowers_le.mpr htB))
      (by rw [hB1, hSt, hS]; norm_num)
  have htL : t ∈ Subgroup.normalizer (L2 : Set G) := C.h.hyp.h2.borel_le htB
  have htP : t ∈ Subgroup.normalizer ((L2 ⊔ S : Subgroup G) : Set G) :=
    le_normalizer_sup_aux (X := Subgroup.zpowers t) (Subgroup.zpowers_le.mpr htL)
      (Subgroup.zpowers_le.mpr htS) (Subgroup.mem_zpowers t)
  have hP := card_L2S C
  have hn7' : ¬ 7 ∣ Nat.card ↥(L2 ⊔ S) := by
    rw [hP, hS]
    intro h
    rcases hp7.dvd_mul.mp h with h | h
    · omega
    · have := hp7.dvd_of_dvd_pow h
      omega
  have := card_sup_zpowers_seven htP ht7 hn7'
  rw [hB, ← hSt_eq, ← sup_assoc, this, hP, hS]
  norm_num

theorem exists_L2B_eq {K1 L2 S Zs : Subgroup G} {Ω : Type} [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hc9 : Fintype.card Ω = 9) (hL : IsL2Quot 3 (OTwoQuot K1)) (hSK : S ≤ K1)
    (hK : Nat.card ↥K1 = 258048) (hS : Nat.card ↥S = 2 ^ 12) :
    ∃ t : G, orderOf t = 7 ∧ t ∈ borelOf K1 S ∧
      L2 ⊔ bigB K1 L2 S = (L2 ⊔ S) ⊔ Subgroup.zpowers t ∧
      t ∈ Subgroup.normalizer ((L2 ⊔ S : Subgroup G) : Set G) ∧ ¬ 7 ∣ Nat.card ↥(L2 ⊔ S) := by
  classical
  have hp7 : Nat.Prime 7 := by norm_num
  have hB := bigB_eq_borelOf C.h C.hR hSK
  have hB1 : Nat.card ↥(borelOf K1 S) = 28672 := by
    have := card_borelOf C hc9
    omega
  obtain ⟨t, htK, htB, ht7⟩ := exists_order_seven C hc9 hL
  have htS : t ∈ Subgroup.normalizer (S : Set G) := borelOf_le_normalizer_S hSK htB
  have hn7 : ¬ 7 ∣ Nat.card ↥S := by
    rw [hS]
    intro h
    have := hp7.dvd_of_dvd_pow h
    omega
  have hSt := card_sup_zpowers_seven htS ht7 hn7
  have hSB : S ≤ borelOf K1 S := by
    have := F1.sylow_le_borelOf K1 S
    rwa [inf_eq_left.mpr hSK] at this
  have hSt_eq : S ⊔ Subgroup.zpowers t = borelOf K1 S :=
    Subgroup.eq_of_le_of_card_ge (sup_le hSB (Subgroup.zpowers_le.mpr htB))
      (by rw [hB1, hSt, hS]; norm_num)
  have htL : t ∈ Subgroup.normalizer (L2 : Set G) := C.h.hyp.h2.borel_le htB
  have htP : t ∈ Subgroup.normalizer ((L2 ⊔ S : Subgroup G) : Set G) :=
    le_normalizer_sup_aux (X := Subgroup.zpowers t) (Subgroup.zpowers_le.mpr htL)
      (Subgroup.zpowers_le.mpr htS) (Subgroup.mem_zpowers t)
  have hP := card_L2S C
  refine ⟨t, ht7, htB, ?_, htP, ?_⟩
  · rw [hB, ← hSt_eq, ← sup_assoc]
  · rw [hP, hS]
    intro h
    rcases hp7.dvd_mul.mp h with h | h
    · omega
    · have := hp7.dvd_of_dvd_pow h
      omega

theorem pCore_L2B_eq {K1 L2 S Zs : Subgroup G} {Ω : Type} [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hc9 : Fintype.card Ω = 9) (hL : IsL2Quot 3 (OTwoQuot K1)) (hSK : S ≤ K1)
    (hK : Nat.card ↥K1 = 258048) (hS : Nat.card ↥S = 2 ^ 12) :
    pCoreOf 2 (L2 ⊔ bigB K1 L2 S) = pCoreOf 2 (L2 ⊔ S) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht7, htB, hX, htP, hn7⟩ := exists_L2B_eq C hc9 hL hSK hK hS
  have hq := card_quot_sup_zpowers_seven htP ht7 hn7
  rw [← hX] at hq
  set X : Subgroup G := L2 ⊔ bigB K1 L2 S with hXdef
  set P : Subgroup G := L2 ⊔ S with hPdef
  have hPX : P ≤ X := by rw [hX]; exact le_sup_left
  have hXn : X ≤ Subgroup.normalizer (P : Set G) := by
    rw [hX]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htP)
  haveI hN : (P.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXn
  have hle : pCoreOf 2 X ≤ P := by
    intro x hx
    have hxX : x ∈ X := pCoreOf_le 2 X hx
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨x, hx⟩
    have h1 : (QuotientGroup.mk (⟨x, hxX⟩ : ↥X) : ↥X ⧸ P.subgroupOf X) ^ 2 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨x, hxX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      rw [this]; rfl
    have h7 : (QuotientGroup.mk (⟨x, hxX⟩ : ↥X) : ↥X ⧸ P.subgroupOf X) ^ 7 = 1 := by
      have := pow_card_eq_one' (G := ↥X ⧸ P.subgroupOf X)
        (x := (QuotientGroup.mk (⟨x, hxX⟩ : ↥X) : ↥X ⧸ P.subgroupOf X))
      rwa [hq] at this
    have h8 := pow_gcd_eq_one.mpr ⟨h1, h7⟩
    have hg : Nat.gcd (2 ^ k) 7 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hg, pow_one] at h8
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h8)
  refine le_antisymm ?_ ?_
  ·
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
      (hPX.trans (le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 P).trans hPX) (le_normalizer_pCoreOf_of_le_normalizer hXn)
      (pCoreOf_isPGroup 2 P)

theorem centralizer_L2B_le {K1 L2 S Zs : Subgroup G} {Ω : Type} [Fintype Ω]
    (C : FamCtx K1 L2 S Zs Ω) (hc9 : Fintype.card Ω = 9) (hL : IsL2Quot 3 (OTwoQuot K1))
    (hSK : S ≤ K1) (hK : Nat.card ↥K1 = 258048) (hS : Nat.card ↥S = 2 ^ 12) :
    ∀ x ∈ L2 ⊔ bigB K1 L2 S, x ∈ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S) : Set G) →
      x ∈ pCoreOf 2 (L2 ⊔ S) := by
  intro x hx hxc
  have hB := bigB_eq_borelOf C.h C.hR hSK
  have hSB : S ≤ borelOf K1 S := by
    have := F1.sylow_le_borelOf K1 S
    rwa [inf_eq_left.mpr hSK] at this
  have hX : L2 ⊔ S ⊔ borelOf K1 S = L2 ⊔ bigB K1 L2 S := by
    rw [hB, sup_assoc, sup_eq_right.mpr hSB]
  have hct := C.h.hyp.h2.charTwo
  rw [hX] at hct
  have hQ := pCore_L2B_eq C hc9 hL hSK hK hS
  rw [← hQ] at hxc ⊢
  exact hct ⟨hx, hxc⟩

end CFSG.Quasithin.Background.Harris.R1
