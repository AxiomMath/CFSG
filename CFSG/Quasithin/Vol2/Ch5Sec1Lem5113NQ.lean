module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NQBase
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.Quasithin.Vol2.Ch11SecA11Nonquasi
public import CFSG.Quasithin.Vol2.Ch1Five
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Type

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Star513

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem false_of_quasisimple (hst : Star513 Q R S B D)
    (hnot : ¬ D ≤ Subgroup.normalizer (R : Set A)) (hQq : CFSG.IsQuasisimple ↥Q)
    (hZ : Odd (Nat.card (Subgroup.center ↥Q))) {z : A} (hzQ : z ∈ Q) (hz2 : z * z = 1)
    (hz1 : z ≠ 1)
    (hcase : (IsSL2 5 (↥R ⧸ CFSG.oddCore ↥R) ∧ Q = R ⊔ oddCoreSub Q) ∨
      (IsSL2 5 (↥R ⧸ CFSG.oddCore ↥R) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥Q ⧸ CFSG.oddCore ↥Q))) : False := by
  have hw2 : (⟨z, hzQ⟩ : ↥Q) * ⟨z, hzQ⟩ = 1 := Subtype.ext hz2
  have hwO : (⟨z, hzQ⟩ : ↥Q) ∉ CFSG.oddCore ↥Q := fun h =>
    hz1 (congrArg Subtype.val
      (eq_one_of_mul_self_of_odd CFSG.ABGLocalTools.odd_card_oddCore h hw2))
  have hOZ : CFSG.oddCore ↥Q ≤ Subgroup.center ↥Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQq (CFSG.oddCore_normal (G := ↥Q)) with
      h | h
    · exfalso
      apply hwO
      rw [h]
      exact Subgroup.mem_top _
    · exact h
  have hZO : Subgroup.center ↥Q ≤ CFSG.oddCore ↥Q :=
    CFSG.ABGLocalTools.le_oddCore_of_normal inferInstance hZ
  rcases hcase with ⟨-, hQRO⟩ | ⟨-, p, hp, -, hp8, ⟨eQ⟩⟩
  ·
    have hcen : ∀ c ∈ oddCoreSub Q, ∀ x ∈ Q, c * x = x * c := by
      rintro _ ⟨u, hu, rfl⟩ x hx
      have h := Subgroup.mem_center_iff.mp (hOZ hu) ⟨x, hx⟩
      exact (congrArg Subtype.val h).symm
    have hCQ : oddCoreSub Q ≤ Q := by
      rintro _ ⟨u, -, rfl⟩
      exact u.2
    have hRN : R ≤ Subgroup.normalizer (oddCoreSub Q : Set A) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro c
      have hrQ : r ∈ Q := hst.R_le hr
      constructor
      · intro hc
        have e1 : r * c * r⁻¹ = c := by rw [← hcen c hc r hrQ]; group
        rw [e1]
        exact hc
      · intro hc
        have h1 := hcen _ hc r⁻¹ (Q.inv_mem hrQ)
        have e1 : c = r * c * r⁻¹ := by
          calc c = r⁻¹ * (r * c * r⁻¹) * r := by group
            _ = r * c * r⁻¹ * r⁻¹ * r := by rw [← h1]
            _ = r * c * r⁻¹ := by group
        rw [e1]
        exact hc
    have hQR : Q ≤ R := by
      have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hQq.1
      rw [← hperf]
      refine commutator_le_of_forall_eq_mul (C := oddCoreSub Q) (fun x hx => ?_)
        (fun c hc r hr => hcen c hc r (hst.R_le hr)) (fun c hc c' hc' => hcen c hc c' (hCQ hc'))
      have hx' : x ∈ ((R ⊔ oddCoreSub Q : Subgroup A) : Set A) := by
        rw [← hQRO]
        exact hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right R (oddCoreSub Q) hRN] at hx'
      obtain ⟨r, hr, c, hc, rfl⟩ := hx'
      exact ⟨r, hr, c, hc, rfl⟩
    have heq : Q = R := le_antisymm hQR hst.R_le
    exact hnot (heq ▸ hst.D_le_Q)
  ·
    have hOeq : CFSG.oddCore ↥Q = Subgroup.center ↥Q := le_antisymm hOZ hZO
    have : IsSimpleGroup (↥Q ⧸ Subgroup.center ↥Q) := hQq.2.1
    have hs : IsSimpleGroup (↥Q ⧸ CFSG.oddCore ↥Q) :=
      (QuotientGroup.quotientMulEquivOfEq hOeq).isSimpleGroup
    have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
      eQ.symm.isSimpleGroup
    have : Fact p.Prime := ⟨hp⟩
    exact not_isSimpleGroup_sl2_of_ringChar (k := ZMod p) (by rw [ZMod.ringChar_zmod_n]; omega) hsl

theorem false_of_case34 (hst : Star513 Q R S B D) (hnot : ¬ D ≤ Subgroup.normalizer (R : Set A))
    (hTc : FactType513Aut) (h34 : A36Case3 ↥Q ∨ A36Case4 ↥Q) (hE : A36Extra ↥Q)
    (hFO : CFSG.fittingSubgroup ↥Q = CFSG.oddCore ↥Q) (hOR : CFSG.oddCore ↥R = ⊥) {z : A}
    (hzR : z ∈ R) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ r ∈ R, r * z = z * r)
    (hSz : S ≤ Subgroup.centralizer ({z} : Set A)) (hzP : z ∈ ⁅S ⊓ R, S ⊓ R⁆) {a b : A}
    (ha : a ∈ R) (hb : b ∈ R) (hab : a * b ≠ b * a)
    (hcase : (IsSL2 5 (↥R ⧸ CFSG.oddCore ↥R) ∧ Q = R ⊔ oddCoreSub Q) ∨
      (IsSL2 5 (↥R ⧸ CFSG.oddCore ↥R) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥Q ⧸ CFSG.oddCore ↥Q))) : False := by
  have hzQ : z ∈ Q := hst.R_le hzR
  set w : ↥Q := ⟨z, hzQ⟩ with hwdef
  have hw2 : w * w = 1 := Subtype.ext hz2
  have hw1 : w ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hwF : w ∉ CFSG.fittingSubgroup ↥Q := by
    rw [hFO]
    exact fun h => hw1 (eq_one_of_mul_self_of_odd CFSG.ABGLocalTools.odd_card_oddCore h hw2)
  set FA := (CFSG.fittingSubgroup ↥Q).map Q.subtype with hFA
  have hFAo : Odd (Nat.card FA) := by
    rw [hFA, Subgroup.card_map_of_injective Q.subtype_injective, hFO]
    exact CFSG.ABGLocalTools.odd_card_oddCore
  have hNF : Subgroup.normalizer (Q : Set A) ≤ Subgroup.normalizer (FA : Set A) :=
    SteinbergBS.normalizer_le_normalizer_map_characteristic Q _
  have hDF : D ≤ Subgroup.normalizer (FA : Set A) := hst.D_le_Q.trans hNF
  have hSF : S ≤ Subgroup.normalizer (FA : Set A) := hst.S_le_Q.trans hNF
  have hRF : R ≤ Subgroup.normalizer (FA : Set A) :=
    hst.R_le.trans (Subgroup.le_normalizer.trans hNF)
  obtain ⟨r, hr, hr5, χ, -, hχk⟩ := exists_sl2_surjection_of_case34 h34
  have : Fact r.Prime := ⟨hr⟩
  have hkr : ringChar (ZMod r) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hχinv : ∀ y : ↥Q, y * y = 1 → y ∉ CFSG.fittingSubgroup ↥Q → χ y = -1 := by
    intro y hy hyF
    have h1 : χ y ^ 2 = 1 := by rw [sq, ← map_mul, hy, map_one]
    rcases (LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hkr _).mp h1 with h | h
    · exact absurd (hχk ▸ MonoidHom.mem_ker.mpr h) hyF
    · exact h
  have hdz : ∀ d ∈ D, d * z * d⁻¹ * z⁻¹ ∈ FA := by
    intro d hd
    have hdzQ : d * z * d⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hst.D_le_Q hd) z).mp hzQ
    set y : ↥Q := ⟨d * z * d⁻¹, hdzQ⟩ with hydef
    have hy2 : y * y = 1 := by
      apply Subtype.ext
      show d * z * d⁻¹ * (d * z * d⁻¹) = 1
      calc d * z * d⁻¹ * (d * z * d⁻¹) = d * (z * z) * d⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    have hyF : y ∉ CFSG.fittingSubgroup ↥Q := by
      intro hy
      have h1 : d * z * d⁻¹ ∈ FA := ⟨y, hy, rfl⟩
      have h2 : d⁻¹ * (d * z * d⁻¹) * d⁻¹⁻¹ ∈ FA :=
        (Subgroup.mem_normalizer_iff.mp (hDF (D.inv_mem hd)) _).mp h1
      have h3 : d⁻¹ * (d * z * d⁻¹) * d⁻¹⁻¹ = z := by group
      rw [h3] at h2
      obtain ⟨u, hu, hu'⟩ := h2
      apply hwF
      have hu2 : u = w := Subtype.ext hu'
      rw [← hu2]
      exact hu
    have hyw : χ y = χ w := by rw [hχinv y hy2 hyF, hχinv w hw2 hwF]
    have hmem : y * w⁻¹ ∈ CFSG.fittingSubgroup ↥Q := by
      rw [← hχk, MonoidHom.mem_ker, map_mul, map_inv, hyw, mul_inv_cancel]
    exact ⟨y * w⁻¹, hmem, rfl⟩
  have hDz : D ≤ Subgroup.centralizer ({z} : Set A) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_commutator_mem hst.D_cyclic hst.D_odd hst.S_two hst.perm_D hFAo hDF hSF
        inf_le_left hzP hz2 hd (hdz d hd))
  set W := Q ⊓ Subgroup.centralizer ({z} : Set A) with hWdef
  have hRz : R ≤ Subgroup.centralizer ({z} : Set A) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc x hx)
  have hRW : R ≤ W := le_inf hst.R_le hRz
  have hDW : D ≤ Subgroup.normalizer (W : Set A) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hst.D_le_Q hd, Subgroup.le_normalizer (hDz hd)⟩
  rcases hcase with ⟨-, hQRO⟩ | ⟨-, p, hp, hp5, hp8, hQp⟩
  ·
    have hC : oddCoreSub Q = FA := by
      show (CFSG.oddCore ↥Q).map Q.subtype = _
      rw [hFA, hFO]
    rw [hC] at hQRO
    have hKF : R.subgroupOf Q ⊓ CFSG.fittingSubgroup ↥Q = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxR', hxF⟩ := Subgroup.mem_inf.mp hx
      have hxR : (x : A) ∈ R := Subgroup.mem_subgroupOf.mp hxR'
      have hN : ((FA ⊓ R).subgroupOf R).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
        intro t ht
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hRF ht, Subgroup.le_normalizer ht⟩
      have hNo : Odd (Nat.card ((FA ⊓ R).subgroupOf R)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
        exact hFAo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
      have hle := CFSG.ABGLocalTools.le_oddCore_of_normal hN hNo
      rw [hOR] at hle
      have hxm : (⟨(x : A), hxR⟩ : ↥R) ∈ (FA ⊓ R).subgroupOf R :=
        Subgroup.mem_subgroupOf.mpr ⟨⟨x, hxF, rfl⟩, hxR⟩
      have h1 := hle hxm
      rw [Subgroup.mem_bot] at h1
      have h2 : (x : A) = 1 := congrArg Subtype.val h1
      exact Subgroup.mem_bot.mpr (Subtype.ext h2)
    have hKp : ⁅R.subgroupOf Q, R.subgroupOf Q⁆ = R.subgroupOf Q := by
      apply Subgroup.map_injective Q.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hst.R_le]
      exact hst.R_perfect
    have hwK : ∀ k ∈ R.subgroupOf Q, k * w = w * k := fun k hk =>
      Subtype.ext (hzc _ (Subgroup.mem_subgroupOf.mp hk))
    have hk : (⟨a, hst.R_le ha⟩ : ↥Q) * ⟨b, hst.R_le hb⟩ ≠ ⟨b, hst.R_le hb⟩ * ⟨a, hst.R_le ha⟩ :=
      fun h => hab (congrArg Subtype.val h)
    have hcp : ∀ c ∈ FA ⊓ Subgroup.centralizer ({z} : Set A),
        (∀ x ∈ R, c * x = x * c) ∧
          ∀ c' ∈ FA ⊓ Subgroup.centralizer ({z} : Set A), c * c' = c' * c := by
      rintro c ⟨⟨u, hu, rfl⟩, hcz⟩
      have hwu : w * u = u * w :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hcz).symm
      obtain ⟨h1, h2⟩ := Vol2.Ch10.SecB.SL2Inv.commute_props h34 hE hKF hKp
        (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hb) hk hw2 hwF hwK hu hwu
      refine ⟨fun x hx =>
        congrArg Subtype.val (h1 ⟨x, hst.R_le hx⟩ (Subgroup.mem_subgroupOf.mpr hx)), ?_⟩
      rintro _ ⟨⟨u', hu', rfl⟩, hcz'⟩
      have hwu' : w * u' = u' * w :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hcz').symm
      exact congrArg Subtype.val (h2 u' hu' hwu')
    have hWR : ⁅W, W⁆ ≤ R := by
      refine commutator_le_of_forall_eq_mul (C := FA ⊓ Subgroup.centralizer ({z} : Set A))
        (fun x hx => ?_) (fun c hc x hx => (hcp c hc).1 x hx)
        (fun c hc c' hc' => (hcp c hc).2 c' hc')
      have hx' : x ∈ ((R ⊔ FA : Subgroup A) : Set A) := by
        rw [← hQRO]
        exact hx.1
      rw [Subgroup.coe_mul_of_left_le_normalizer_right R FA hRF] at hx'
      obtain ⟨t, ht, c, hc, rfl⟩ := hx'
      refine ⟨t, ht, c, ⟨hc, ?_⟩, rfl⟩
      have h1 : t⁻¹ * (t * c) ∈ Subgroup.centralizer ({z} : Set A) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hRz ht)) hx.2
      rwa [inv_mul_cancel_left] at h1
    exact hnot fun d hd => mem_normalizer_of_commutator_le hRW hWR hst.R_perfect (hDW hd)
  ·
    rcases h34 with h3 | h4
    ·
      have hFo : Odd (Nat.card (CFSG.fittingSubgroup ↥Q)) := by
        rw [hFO]
        exact CFSG.ABGLocalTools.odd_card_oddCore
      have hbij := centralizer_bijective_of_case_three h3 hFo hw2 hwF
      have hcent : Subgroup.centralizer ({w} : Set ↥Q) =
          (Subgroup.centralizer ({z} : Set A)).subgroupOf Q := by
        ext x
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
          Subgroup.mem_centralizer_singleton_iff]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      have hWSL : IsSL2 p ↥W := by
        obtain ⟨e4⟩ := hQp
        have e1 : ↥W ≃* ↥(Subgroup.centralizer ({w} : Set ↥Q)) :=
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ Q)).symm.trans
            (MulEquiv.subgroupCongr (by rw [Subgroup.inf_subgroupOf_left, ← hcent]))
        exact ⟨((e1.trans (MulEquiv.ofBijective _ hbij)).trans
          (QuotientGroup.quotientMulEquivOfEq hFO)).trans e4⟩
      have hSW : S ⊓ W = S ⊓ Q := by
        apply le_antisymm (inf_le_inf_left _ inf_le_left)
        exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hSz))
      have hst' : Star513 W R S B D :=
        { R_le := hRW
          R_perfect := hst.R_perfect
          R_type := hst.R_type
          S_two := hst.S_two
          S_le_Q := fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
            ⟨hst.S_le_Q hs, Subgroup.le_normalizer (hSz hs)⟩
          S_le_R := hst.S_le_R
          sylow_Q := by
            rw [hSW]
            exact F7.isSylowTwoOf_mono_right hst.sylow_Q
              (le_inf inf_le_right (inf_le_left.trans hSz)) inf_le_left
          sylow_R := hst.sylow_R
          hall_B := hst.hall_B
          perm_B := hst.perm_B
          D_cyclic := hst.D_cyclic
          D_odd := hst.D_odd
          D_le_Q := hDW
          B_le_D := hst.B_le_D
          perm_D := hst.perm_D }
      exact hnot (hTc A W R S B D hst' (Or.inl ⟨p, hp, hp5, hp8, Or.inr hWSL⟩))
    ·
      obtain ⟨-, -, ⟨e5⟩, -⟩ := h4
      obtain ⟨ep⟩ := hQp
      have : Fact p.Prime := ⟨hp⟩
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) =
          Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
        (Nat.card_congr e5.toEquiv).symm.trans
          ((Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hFO).toEquiv).trans
            (Nat.card_congr ep.toEquiv))
      rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod, Nat.card_zmod] at hc
      have h5 := Vol2.Ch11.SecA.eq_of_mul_sq_sub_one (by norm_num) hp.one_lt.le hc
      subst h5
      norm_num at hp5

theorem false_of_nq (hst : Star513 Q R S B D) (hnot : ¬ D ≤ Subgroup.normalizer (R : Set A))
    (hTc : FactType513Aut) (h36 : Vol2Native.A36StrongCat Q)
    (hcase : (IsSL2 5 (↥R ⧸ CFSG.oddCore ↥R) ∧ Q = R ⊔ oddCoreSub Q) ∨
      (IsSL2 5 (↥R ⧸ CFSG.oddCore ↥R) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥Q ⧸ CFSG.oddCore ↥Q))) : False := by
  have hR5 : IsSL2 5 (↥R ⧸ CFSG.oddCore ↥R) := by rcases hcase with h | h <;> exact h.1
  have hOR := oddCore_eq_bot_of_lieModel hst.R_type hR5
  obtain ⟨z, hzR, hz2, hz1, hzc, huniq, hzP, a, ha, b, hb, hab⟩ :=
    exists_central_involution_sl25 (isSL2_of_oddCore_eq_bot hOR hR5) hst.sylow_R
  have hSz : S ≤ Subgroup.centralizer ({z} : Set A) := by
    intro s hs
    have hszR : s * z * s⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hst.S_le_R hs) z).mp hzR
    have h2 : s * z * s⁻¹ * (s * z * s⁻¹) = 1 := by
      calc s * z * s⁻¹ * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    rcases huniq _ hszR h2 with h | h
    · exfalso
      apply hz1
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc s * z = s * z * s⁻¹ * s := by group
        _ = z * s := by rw [h]
  obtain ⟨hconc, hcom, hextra⟩ := h36
  rcases hconc with ⟨hc, hs, -⟩ | ⟨hc, hZ3, -⟩ | h3 | h4
  ·
    refine false_of_quasisimple hst hnot hc.1 ?_ (hst.R_le hzR) hz2 hz1 hcase
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Q) with h | h
    · rw [h, Subgroup.card_bot]
      exact odd_one
    · exfalso
      obtain ⟨u, v, huv⟩ := hc.1.2.2
      apply huv
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
      have hx : (x : ↥Q ⧸ Subgroup.center ↥Q) = 1 :=
        (QuotientGroup.eq_one_iff x).mpr (by rw [h]; exact Subgroup.mem_top x)
      have hy : (y : ↥Q ⧸ Subgroup.center ↥Q) = 1 :=
        (QuotientGroup.eq_one_iff y).mpr (by rw [h]; exact Subgroup.mem_top y)
      rw [hx, hy]
  ·
    exact false_of_quasisimple hst hnot hc.1 (by rw [hZ3]; decide) (hst.R_le hzR) hz2 hz1 hcase
  · exact false_of_case34 hst hnot hTc (Or.inl h3) (hextra (Or.inl h3)) hcom.1 hOR hzR hz2 hz1
      hzc hSz hzP ha hb hab hcase
  · exact false_of_case34 hst hnot hTc (Or.inr h4) (hextra (Or.inr h4)) hcom.1 hOR hzR hz2 hz1
      hzc hSz hzP ha hb hab hcase

end Star513

theorem stmt5_1_13_type_nq_of (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h36 : Vol2Native.A36ForSQTKCat) (h510 : Stmt5_1_10) (hTc : FactType513Aut) :
    Stmt5_1_13_type_nq := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl hcase
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  obtain ⟨hst, hnot⟩ := m.star513 h37 h38 h510 heq hcl hL24
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have h36Q := Vol2Native.lemma_1_2_1_four_strong hloc h36 m.inH.2 m.hat.1
  exact Star513.false_of_nq hst hnot hTc h36Q hcase

end CFSG.Quasithin.H13
