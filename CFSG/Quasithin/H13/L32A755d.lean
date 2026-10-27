module

public import CFSG.Quasithin.H13.L32A753j
public import CFSG.Quasithin.H13.L32A755c
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330H2

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit

namespace M755

variable {V : Type} [CommGroup V] [Finite V]

theorem mem_map_of_inner
    {e : V ≃* ModQ}
    {X K Tb : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hKe : K.map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)))
    (hX : ∀ x ∈ X, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range)
    (hTbS : Tb.map (MulAut.congr e).toMonoidHom ≤ sSubG.map (g2QAct (ZMod 2)))
    (hsyl : IsSylowTwoOf Tb X) {i : ℕ} (hi : i ∈ innerS) :
    g2QAct (ZMod 2) (sEltG i) ∈ Tb.map (MulAut.congr e).toMonoidHom := by
  set ρ := g2QAct (ZMod 2) with hρ
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hρinj : Function.Injective ρ := g2QAct_injective
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  set X' := (X.map φ).comap ρ with hX'
  set P := (Tb.map φ).comap ρ with hP
  have hXR : X.map φ ≤ ρ.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hX x hx
  have hTR : Tb.map φ ≤ ρ.range := (Subgroup.map_mono hsyl.1).trans hXR
  have hX'map : X'.map ρ = X.map φ := Subgroup.map_comap_eq_self hXR
  have hPmap : P.map ρ = Tb.map φ := Subgroup.map_comap_eq_self hTR
  have hcardX : Nat.card X = Nat.card X' := by
    rw [← Subgroup.card_map_of_injective hφinj, ← hX'map, Subgroup.card_map_of_injective hρinj]
  have hcardT : Nat.card Tb = Nat.card P := by
    rw [← Subgroup.card_map_of_injective hφinj, ← hPmap, Subgroup.card_map_of_injective hρinj]
  have hDX' : g2Derived (ZMod 2) ≤ X' := by
    intro g hg
    show ρ g ∈ X.map φ
    have : ρ g ∈ K.map φ := by rw [hKe]; exact ⟨g, hg, rfl⟩
    exact Subgroup.map_mono hKX this
  have hPS : P ≤ sSubG := fun x hx => by
    have : ρ x ∈ sSubG.map ρ := hTbS hx
    obtain ⟨s, hs, hse⟩ := this
    rw [hρinj hse] at hs
    exact hs
  have hD6 : Nat.card (g2Derived (ZMod 2)) = 6048 := by
    have h1 := (g2Derived (ZMod 2)).card_mul_index
    rw [B45U33.index_g2Derived, card_g2Two] at h1
    omega
  have hX'card : Nat.card X' = 6048 ∨ Nat.card X' = 12096 := by
    have hdvd : Nat.card (g2Derived (ZMod 2)) ∣ Nat.card X' := Subgroup.card_dvd_of_le hDX'
    have hdvd2 : Nat.card X' ∣ 12096 := by
      rw [← card_g2Two]
      exact Subgroup.card_subgroup_dvd_card X'
    rw [hD6] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨m, hm⟩ := hdvd2
    rw [hk] at hm
    have hk2 : k * m = 2 := by
      have : 6048 * (k * m) = 6048 * 2 := by rw [← mul_assoc, ← hm]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro m hk2) with h | h
    · left; rw [hk, h]
    · right; rw [hk, h]
  have hP2 : ∃ n, Nat.card P = 2 ^ n ∧ ¬ 2 ∣ Nat.card X' / Nat.card P ∧
      Nat.card P ∣ Nat.card X' := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hsyl.2.1
    have hmul := Subgroup.card_mul_index (Tb.subgroupOf X)
    have hTbc : Nat.card (Tb.subgroupOf X) = Nat.card Tb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsyl.1).toEquiv
    rw [hTbc] at hmul
    refine ⟨n, by rw [← hcardT, hn], ?_, ?_⟩
    · rw [← hcardT, ← hcardX, ← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
      exact hsyl.2.2
    · rw [← hcardT, ← hcardX, ← hmul]
      exact Dvd.intro _ rfl
  obtain ⟨n, hn, hodd, hdvdP⟩ := hP2
  have hS0 : ∀ j ∈ innerS, sEltG j ∈ P := by
    have hi64 : ∀ j ∈ innerS, j < 64 := innerS_lt
    set S₀ := sSubG ⊓ g2Derived (ZMod 2) with hS₀
    have hS₀mem : ∀ x ∈ S₀, ∃ j ∈ innerS, sEltG j = x := by
      rintro x ⟨hxS, hxD⟩
      obtain ⟨j, hj, rfl⟩ := mem_sSubG.1 hxS
      exact ⟨j, (mem_g2Derived_iff hj).1 hxD, rfl⟩
    have hS₀card : Nat.card S₀ ≤ 32 := by
      have hsurj : ∀ x : S₀, ∃ j : {j // j ∈ innerS}, sEltG j.1 = x := fun x => by
        obtain ⟨j, hj, hjx⟩ := hS₀mem x.1 x.2
        exact ⟨⟨j, hj⟩, hjx⟩
      have h1 := Nat.card_le_card_of_surjective (fun j : {j // j ∈ innerS} =>
        (⟨sEltG j.1, mem_sSubG.2 ⟨j.1, innerS_lt j.1 j.2, rfl⟩,
          (mem_g2Derived_iff (innerS_lt j.1 j.2)).2 j.2⟩ : S₀))
        (fun x => by
          obtain ⟨j, hj⟩ := hsurj x
          exact ⟨j, Subtype.ext hj⟩)
      have h2 : Nat.card {j // j ∈ innerS} = 32 := by
        have e : {j // j ∈ innerS} ≃ {j // j ∈ innerS.toFinset} :=
          Equiv.subtypeEquivRight fun j => by simp
        rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
        decide
      omega
    have hPD : Nat.card ↥(P ⊓ g2Derived (ZMod 2)) = 32 := by
      rcases hX'card with h6 | h12
      ·
        have hX'D : X' = g2Derived (ZMod 2) :=
          (Subgroup.eq_of_le_of_card_ge hDX' (by rw [h6, hD6])).symm
        have hPX' : P ≤ X' := fun x hx => by
          show ρ x ∈ X.map φ
          exact Subgroup.map_mono hsyl.1 hx
        rw [inf_eq_left.2 (hX'D ▸ hPX'), hn]
        rw [h6, hn] at hodd hdvdP
        have hn5 : n = 5 := by
          have h5 : n < 6 := by
            by_contra hlt
            push Not at hlt
            have : 2 ^ 6 ∣ 6048 := (Nat.pow_dvd_pow 2 hlt).trans hdvdP
            norm_num at this
          have key : ∀ n < 6, ¬ 2 ∣ 6048 / 2 ^ n → n = 5 := by decide
          exact key n h5 hodd
        rw [hn5]
        norm_num
      ·
        have hn6 : n = 6 := by
          rw [h12, hn] at hodd hdvdP
          have h6 : n < 7 := by
            by_contra hlt
            push Not at hlt
            have : 2 ^ 7 ∣ 12096 := (Nat.pow_dvd_pow 2 hlt).trans hdvdP
            norm_num at this
          have key : ∀ n < 7, ¬ 2 ∣ 12096 / 2 ^ n → n = 6 := by decide
          exact key n h6 hodd
        have hPeq : P = sSubG :=
          Subgroup.eq_of_le_of_card_ge hPS (by rw [hn, hn6, card_sSubG]; norm_num)
        rw [hPeq]
        have hle2 : (g2Derived (ZMod 2)).relIndex sSubG ≤ 2 := by
          calc (g2Derived (ZMod 2)).relIndex sSubG ≤ (g2Derived (ZMod 2)).relIndex ⊤ :=
                Subgroup.relIndex_le_of_le_right le_top
                  (by rw [Subgroup.relIndex_top_right, B45U33.index_g2Derived]; norm_num)
            _ = 2 := by rw [Subgroup.relIndex_top_right, B45U33.index_g2Derived]
        have hmul := Subgroup.relIndex_mul_card (g2Derived (ZMod 2)) sSubG
        rw [card_sSubG, inf_comm] at hmul
        obtain ⟨r, hr⟩ : ∃ r, r = (g2Derived (ZMod 2)).relIndex sSubG := ⟨_, rfl⟩
        rw [← hr] at hmul hle2
        have hle32 : Nat.card ↥(sSubG ⊓ g2Derived (ZMod 2)) ≤ 32 := hS₀card
        interval_cases r <;> omega
    intro j hj
    have hle : P ⊓ g2Derived (ZMod 2) ≤ S₀ := inf_le_inf_right _ hPS
    have heq : P ⊓ g2Derived (ZMod 2) = S₀ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hPD]; exact hS₀card)
    have : sEltG j ∈ S₀ := ⟨mem_sSubG.2 ⟨j, hi64 j hj, rfl⟩, (mem_g2Derived_iff (hi64 j hj)).2 hj⟩
    rw [← heq] at this
    exact this.1
  have h1 := hS0 i hi
  rw [← hPmap]
  exact ⟨_, h1, rfl⟩

omit [Finite V] in
theorem autSec_le_normalizer {X K : Subgroup (MulAut V)} {J C : Subgroup V} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V))) (hXJ : X ≤ stabSub J)
    (hXC : X ≤ stabSub C) :
    autSec X J C ≤ Subgroup.normalizer (autSec K J C : Set (MulAut (Sec J C))) := by
  rw [← M753.range_secHom hXJ hXC]
  rintro _ ⟨ξ, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [← M753.range_secHom (hKX.trans hXJ) (hKX.trans hXC)]
  constructor
  · rintro ⟨κ, rfl⟩
    have hc : (ξ : MulAut V) * κ * (ξ : MulAut V)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hXN ξ.2) κ).mp κ.2
    refine ⟨⟨_, hc⟩, ?_⟩
    rw [M753.secHom_mono hKX hXJ hXC, M753.secHom_mono hKX hXJ hXC]
    have e1 : (⟨(ξ : MulAut V) * κ * (ξ : MulAut V)⁻¹, hKX hc⟩ : ↥X) =
        ξ * ⟨κ, hKX κ.2⟩ * ξ⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
  · rintro ⟨κ, hκ⟩
    have hc : (ξ : MulAut V)⁻¹ * κ * (ξ : MulAut V) ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hXN (X.inv_mem ξ.2)) κ).mp κ.2
      simpa using this
    refine ⟨⟨_, hc⟩, ?_⟩
    rw [M753.secHom_mono hKX hXJ hXC]
    have e1 : (⟨(ξ : MulAut V)⁻¹ * κ * (ξ : MulAut V), hKX hc⟩ : ↥X) =
        ξ⁻¹ * ⟨κ, hKX κ.2⟩ * ξ := by
      apply Subtype.ext
      simp
    rw [e1, map_mul, map_mul, map_inv, ← M753.secHom_mono hKX hXJ hXC, hκ]
    group

theorem isSylowTwoOf_map {G' K' : Type*} [Group G'] [Group K'] {H S : Subgroup G'}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K') :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

omit [Finite V] in
theorem isSylowTwoOf_autSec {X Tb : Subgroup (MulAut V)} {J C : Subgroup V}
    (hsyl : IsSylowTwoOf Tb X) (hXJ : X ≤ stabSub J) (hXC : X ≤ stabSub C) :
    IsSylowTwoOf (autSec Tb J C) (autSec X J C) := by
  have h := isSylowTwoOf_map hsyl (M753.secHom hXJ hXC)
  rw [M753.range_secHom] at h
  have e : (Tb.subgroupOf X).map (M753.secHom hXJ hXC) = autSec Tb J C := by
    rw [← M753.range_secHom (hsyl.1.trans hXJ) (hsyl.1.trans hXC)]
    ext φ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, Subgroup.mem_subgroupOf.1 ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨⟨t, hsyl.1 t.2⟩, Subgroup.mem_subgroupOf.2 t.2, rfl⟩
  rwa [e] at h

end M755

namespace Ctx753

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

theorem isSylowTwoOf_autT (C : Ctx753 T L V K) :
    IsSylowTwoOf (autIH (fsuV1 T V) V (hz T V) T) (autIH (fsuV1 T V) V (hz T V) (hz T V)) := by
  have hV₁T : fsuV1 T V ≤ T :=
    inf_le_right.trans ((B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left)
  exact CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn
    (isSylowTwoOf_secImg C.hF98.toHypF91.sylow_H C.f918.H_le_normalizer_V₁ hV₁T)
    (HypF91.tilde_le_normalizer (V₁ := fsuV1 T V) (Vp := V) le_rfl)

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem natural_sec
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38) :
    M753.IrrBetween (autIH (fsuV1 T V) V (hz T V) K) (fixV (autIH (fsuV1 T V) V (hz T V) K)) ⊤ ∧
      Nat.card (Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))) = 2 ^ 6 ∧
      G2NaturalDerived (autSec (autIH (fsuV1 T V) V (hz T V) K) ⊤
        (fixV (autIH (fsuV1 T V) V (hz T V) K))) ⊤ ⊥ 1 ∧
      ∃ k ∈ autIH (fsuV1 T V) V (hz T V) K,
        ∃ v ∈ (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))),
          k v * v⁻¹ ∉ fixV (autIH (fsuV1 T V) V (hz T V) K) := by
  have hsq : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))), v ^ 2 = 1 := fun v => by
    have h := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V)))).2
      v.1 v.2
    exact Subtype.ext (by simpa using h)
  have hP := C.b42TypeU33_autK
  rcases M753.structure_fixV hsq hP C.commV_autK C.index_fixV_autK_le with
    ⟨hirr, h64, hnat⟩ | ⟨J, hKJ, hC₀J, -, hirr₁, -, hnt₁, hnt₂, h64₁, hnat₁, h64₂, hnat₂⟩
  · refine ⟨hirr, h64, hnat, ?_⟩
    by_contra h
    push Not at h
    have htop := M753.trivial_of_le hP h
    apply absurd (B42U33.card_of_b42TypeU33 hP)
    have hK1 : autIH (fsuV1 T V) V (hz T V) K = ⊥ := by
      rw [eq_bot_iff]
      intro k' hk'
      rw [Subgroup.mem_bot]
      exact MulEquiv.ext fun v => htop (Subgroup.mem_top v) k' hk'
    rw [hK1, Subgroup.card_bot]
    norm_num
  · exact (C.not_two_factor h38 hKJ hC₀J.le hirr₁ hnt₁ hnt₂ h64₁ hnat₁ h64₂ hnat₂).elim

theorem exists_coord755
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38) :
    ∃ e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ,
      (autSec (autIH (fsuV1 T V) V (hz T V) K) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
          (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ∧
        (∀ x ∈ autSec (autIH (fsuV1 T V) V (hz T V) (hz T V)) ⊤
            (fixV (autIH (fsuV1 T V) V (hz T V) K)),
          MulAut.congr e x ∈ (g2QAct (ZMod 2)).range) ∧
        (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
            (MulAut.congr e).toMonoidHom ≤ sSubG.map (g2QAct (ZMod 2)) ∧
        ∀ i ∈ M755.innerS, g2QAct (ZMod 2) (sEltG i) ∈
          (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
            (MulAut.congr e).toMonoidHom := by
  obtain ⟨-, -, hnat, -⟩ := C.natural_sec h38
  have hXJ : autIH (fsuV1 T V) V (hz T V) (hz T V) ≤ stabSub ⊤ := fun x _ v => by simp
  have hXC : autIH (fsuV1 T V) V (hz T V) (hz T V) ≤
      stabSub (fixV (autIH (fsuV1 T V) V (hz T V) K)) := M753.le_stabSub_fixV C.autH_le_normalizer
  have hKX := autSec_mono C.autK_le_autH ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))
  have hXN := M755.autSec_le_normalizer C.autK_le_autH C.autH_le_normalizer hXJ hXC
  have hsyl := M755.isSylowTwoOf_autSec C.isSylowTwoOf_autT hXJ hXC
  obtain ⟨e, hKe, hXe, hTbS⟩ := M3330.exists_coordT hXN hnat hsyl.1 hsyl.2.1
  exact ⟨e, hKe, hXe, hTbS, fun i hi => M755.mem_map_of_inner hKX hKe hXe hTbS hsyl hi⟩

end Ctx753

end CFSG.Quasithin.H13.L32A
