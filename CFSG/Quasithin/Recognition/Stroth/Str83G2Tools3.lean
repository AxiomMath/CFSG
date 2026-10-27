module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.Background.RonanE611Block
public import CFSG.Quasithin.Recognition.Stroth.Str83G2Tools

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem normalizer_inf_eq_borel_sup_q2
    (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (H : Subgroup G) (hH : H = L2 ⊔ S) :
    H ⊓ Subgroup.normalizer (S : Set G) = borelOf L2 S ⊔ Q2 L1 L2 S := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hH' : H = L2 ⊔ Q2 L1 L2 S := hH.trans hsup2
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hQ2_le_p2 : Q2 L1 L2 S ≤ P2 L1 L2 S := pCoreOf_le 2 (P2 L1 L2 S)
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hP2_le_NL2 : P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    rw [P2]
    exact sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).2
  have hQ2_le_NL2 : Q2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    hQ2_le_p2.trans hP2_le_NL2
  have hB2_le_N_S2 : borelOf L2 S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    inf_le_right
  have hB2_le_P2 : borelOf L2 S ≤ P2 L1 L2 S := (F1.borelOf_le L2 S).trans le_sup_left
  have hB2_le_N_Q2 : borelOf L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hB2_le_P2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hB2_le_N_S2' : borelOf L2 (S ⊓ L2 ⊔ Q2 L1 L2 S) ≤
      Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
    rwa [← hS2]
  have hB2_le_N_Q2' : borelOf L2 (S ⊓ L2 ⊔ Q2 L1 L2 S) ≤
      Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
    rwa [← hS2]
  have hB2_le_N_S : borelOf L2 S ≤ Subgroup.normalizer (S : Set G) := by
    rw [hS2]
    exact F1.le_normalizer_sup hB2_le_N_S2' hB2_le_N_Q2'
  have hQ2_le_N_S : Q2 L1 L2 S ≤ Subgroup.normalizer (S : Set G) :=
    hQ2S.trans Subgroup.le_normalizer
  apply le_antisymm
  · intro g hg
    obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.mp hg
    rw [hH'] at hgH
    obtain ⟨l, hl, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQ2_le_NL2).mp hgH
    have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
      have hl_eq : l = (l * q) * q⁻¹ := by group
      rw [hl_eq]
      exact (Subgroup.normalizer (S : Set G)).mul_mem hgN
        (Subgroup.inv_mem _ (hQ2_le_N_S hq))
    have hlB : l ∈ borelOf L2 S := by
      refine Subgroup.mem_inf.mpr ⟨hl, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact ⟨(Subgroup.mem_normalizer_iff.mp hlN x).mp hx.1,
          L2.mul_mem (L2.mul_mem hl hx.2) (L2.inv_mem hl)⟩
      · intro hx
        have hxS : x ∈ S := by
          have h1 : l * x * l⁻¹ ∈ S := hx.1
          have h2 := (Subgroup.mem_normalizer_iff.mp
            (Subgroup.inv_mem _ hlN) (l * x * l⁻¹)).mp h1
          have h2' : l⁻¹ * (l * x * l⁻¹) * l = x := by group
          rw [inv_inv] at h2
          rwa [h2'] at h2
        have hxL2 : x ∈ L2 := by
          have h2 : l⁻¹ * (l * x * l⁻¹) * l = x := by group
          rw [← h2]
          exact L2.mul_mem (L2.mul_mem (L2.inv_mem hl) hx.2) hl
        exact ⟨hxS, hxL2⟩
    exact (borelOf L2 S ⊔ Q2 L1 L2 S).mul_mem
      (Subgroup.mem_sup_left hlB) (Subgroup.mem_sup_right hq)
  · refine sup_le ?_ ?_
    · exact le_inf (hH.symm ▸ ((F1.borelOf_le L2 S).trans le_sup_left)) hB2_le_N_S
    · exact le_inf (hH'.symm ▸ le_sup_right) hQ2_le_N_S


theorem frameT1 (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    {D : Subgroup G} (hDleB : D ≤ borelOf L2 S)
    (hDodd : Odd (Nat.card D))
    (hDsup : (S ⊓ L2) ⊔ D = borelOf L2 S) :
    ∃ w : G, w ∈ L2 ⊔ S ∧ w ∈ Subgroup.normalizer (D : Set G) ∧
      (∀ d ∈ D, w * d * w⁻¹ = d⁻¹) ∧
      w ∉ Subgroup.normalizer (S : Set G) ∧
      S ⊔ conjugate S w = L2 ⊔ S := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  let H : Subgroup G := u3H L1 L2 S
  have hH_eq : H = L2 ⊔ S := by
    rw [show H = L2 ⊔ Q2 L1 L2 S from rfl, hsup2]
  have hS_le_H : S ≤ H := by rw [hH_eq]; exact le_sup_right
  have hD_le_L2 : D ≤ L2 := hDleB.trans (F1.borelOf_le L2 S)
  have hD_le_H : D ≤ H := hD_le_L2.trans (hH_eq ▸ le_sup_left)
  have hQ2_le_H : Q2 L1 L2 S ≤ H := by
    rw [show H = L2 ⊔ Q2 L1 L2 S from rfl]; exact le_sup_right
  have hpCoreH : pCoreOf 2 H = Q2 L1 L2 S := by
    rw [show H = u3H L1 L2 S from rfl]
    exact str86_pCoreOf_u3H hF
  have hSH : IsSylowTwoOf S H := by
    rw [hH_eq]
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    simpa [Q1, Q2, P1, P2, bigB_comm, hsup2] using h
  let K : Type := oTwoQuot ↥H
  let π : ↥H →* K := QuotientGroup.mk' (pCore 2 ↥H)
  have hπ_surj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = (Q2 L1 L2 S).subgroupOf H := by
    rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 H, hpCoreH]
  have hBT : BenderType K (2 * a + 1) 1 1 := by
    have hBT_L2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
      BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
    exact BenderType.of_mulEquiv hBT_L2 (str86_oTwoQuot_u3H_equiv hF).symm
  have hSHp : IsPGroup 2 (S.subgroupOf H) :=
    hSH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH.1).symm
  let SH : Sylow 2 ↥H := hSHp.toSylow hSH.2.2
  let Q : Sylow 2 K := SH.mapSurjective hπ_surj
  let Qimg : Subgroup K := (S.subgroupOf H).map π
  have hQcoe : (Q : Subgroup K) = Qimg := by
    rw [Sylow.coe_mapSurjective hπ_surj SH, IsPGroup.toSylow_coe]
  let Dbar : Subgroup K := (D.subgroupOf H).map π
  have hQ2_map_bot : ((Q2 L1 L2 S).subgroupOf H).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker]
  have hS2leH : S ⊓ L2 ≤ H := inf_le_right.trans (hH_eq ▸ le_sup_left)
  have hS_map : Qimg = ((S ⊓ L2).subgroupOf H).map π := by
    change (S.subgroupOf H).map π = ((S ⊓ L2).subgroupOf H).map π
    conv_lhs => rw [hS2]
    rw [Subgroup.subgroupOf_sup hS2leH hQ2_le_H, Subgroup.map_sup, hQ2_map_bot, sup_bot_eq]
  have hB2_map : ((borelOf L2 S).subgroupOf H).map π =
      ((S ⊓ L2).subgroupOf H).map π ⊔ Dbar := by
    rw [← hDsup, Subgroup.subgroupOf_sup hS2leH hD_le_H, Subgroup.map_sup]
  have hC5 : H ⊓ Subgroup.normalizer (S : Set G) =
      borelOf L2 S ⊔ Q2 L1 L2 S :=
    normalizer_inf_eq_borel_sup_q2 hF hB ha hSz hL2 H hH_eq
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hcomapQ : Subgroup.comap π Qimg = S.subgroupOf H := by
    change Subgroup.comap π ((S.subgroupOf H).map π) = S.subgroupOf H
    rw [Subgroup.comap_map_eq, hker]
    exact sup_eq_left.mpr (Subgroup.subgroupOf_mono H hQ2S)
  have hB2_le_H : borelOf L2 S ≤ H :=
    (F1.borelOf_le L2 S).trans (hH_eq ▸ le_sup_left)
  have hborel_comap : Subgroup.comap π (CFSG.GH74.Uniqueness.Bender.borel Q) =
      (H ⊓ Subgroup.normalizer (S : Set G)).subgroupOf H := by
    rw [CFSG.GH74.Uniqueness.Bender.borel,
      Subgroup.comap_normalizer_eq_of_surjective (H := (Q : Subgroup K)) hπ_surj]
    rw [hQcoe, hcomapQ, ← CFSG.Quasithin.RonanE611.subgroupOf_normalizer_eq hS_le_H]
  have hborel_comap' : (borelOf L2 S ⊔ Q2 L1 L2 S).subgroupOf H =
      Subgroup.comap π (CFSG.GH74.Uniqueness.Bender.borel Q) := by
    rw [← hC5, ← hborel_comap]
  have hborel_eq : CFSG.GH74.Uniqueness.Bender.borel Q =
      ((borelOf L2 S ⊔ Q2 L1 L2 S).subgroupOf H).map π := by
    rw [hborel_comap']
    exact (Subgroup.map_comap_eq_self_of_surjective hπ_surj
      (CFSG.GH74.Uniqueness.Bender.borel Q)).symm
  have hQ_sup_Dbar : (Q : Subgroup K) ⊔ Dbar =
      CFSG.GH74.Uniqueness.Bender.borel Q := by
    rw [hborel_eq, Subgroup.subgroupOf_sup hB2_le_H hQ2_le_H,
      Subgroup.map_sup, hB2_map, hQ2_map_bot, sup_bot_eq, hQcoe, hS_map]
  have hS2p : IsPGroup 2 ↥(S ⊓ L2) := hF.1.h2.sylow.2.1
  have hDinfS2 : D ⊓ (S ⊓ L2) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2p) (⟨x, hx.2⟩ : ↥(S ⊓ L2))
    have hk' : orderOf x = 2 ^ k :=
      (Subgroup.orderOf_coe (⟨x, hx.2⟩ : ↥(S ⊓ L2))).trans hk
    have hx2 : orderOf x ∣ 2 ^ k := by
      rw [hk']
    have hxodd : Odd (orderOf x) :=
      hDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hx.1)
    have hcop : Nat.Coprime (2 ^ k) (Nat.card D) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hDodd)
    have hx1 : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hx2 hcop)
        (Subgroup.orderOf_dvd_natCard D hx.1)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hx1)
  have hDinfQ2 : D ⊓ Q2 L1 L2 S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ S := hQ2S hx.2
    have hxL2 : x ∈ L2 := hD_le_L2 hx.1
    have hxbot : x ∈ D ⊓ (S ⊓ L2) := ⟨hx.1, ⟨hxS, hxL2⟩⟩
    rw [hDinfS2] at hxbot
    exact hxbot
  have hDbar_odd : Odd (Nat.card Dbar) := by
    have hcard : Nat.card Dbar = Nat.card D := by
      change Nat.card ↥((D.subgroupOf H).map π) = Nat.card ↥D
      let φ : ↥D → ↥((D.subgroupOf H).map π) := fun d =>
        ⟨π ⟨d, hD_le_H d.2⟩, Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr d.2)⟩
      have hφ_inj : Function.Injective φ := by
        intro d1 d2 h
        have hπ : π ⟨d1, hD_le_H d1.2⟩ = π ⟨d2, hD_le_H d2.2⟩ := congrArg Subtype.val h
        have h1 : π (⟨(d1 : G), hD_le_H d1.2⟩⁻¹ * ⟨(d2 : G), hD_le_H d2.2⟩) = 1 := by
          rw [map_mul, map_inv, hπ, inv_mul_cancel]
        have h2 : (⟨(d1 : G), hD_le_H d1.2⟩⁻¹ * ⟨(d2 : G), hD_le_H d2.2⟩ : ↥H) ∈
            (Q2 L1 L2 S).subgroupOf H := by
          rw [← hker]; exact MonoidHom.mem_ker.mpr h1
        have h2G : ((⟨(d1 : G), hD_le_H d1.2⟩⁻¹ *
            ⟨(d2 : G), hD_le_H d2.2⟩ : ↥H) : G) ∈ Q2 L1 L2 S := h2
        have h3 : (d1 : G)⁻¹ * (d2 : G) ∈ D ⊓ Q2 L1 L2 S := by
          refine ⟨D.mul_mem (D.inv_mem d1.2) d2.2, ?_⟩
          simpa using h2G
        rw [hDinfQ2] at h3
        have h4 : (d1 : G)⁻¹ * (d2 : G) = 1 := Subgroup.mem_bot.mp h3
        exact Subtype.ext (inv_mul_eq_one.mp h4)
      have hφ_surj : Function.Surjective φ := by
        intro x
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
        exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext hyx⟩
      exact Nat.card_congr (Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).symm
    rw [hcard]
    exact hDodd
  have hDbar_le_borel : Dbar ≤ CFSG.GH74.Uniqueness.Bender.borel Q := by
    rw [← hQ_sup_Dbar]
    exact le_sup_right
  obtain ⟨t, ht2, htB, htInv, htTop⟩ :=
    exists_inverting_involution_of_cartan_linear hBT Q hDbar_le_borel hDbar_odd hQ_sup_Dbar
  have htN : t ∈ Subgroup.normalizer (Dbar : Set K) := by
    have hle : Dbar.map (MulAut.conj t).toMonoidHom ≤ Dbar := by
      rintro x ⟨d, hd, rfl⟩
      change t * d * t⁻¹ ∈ Dbar
      rw [htInv d hd]
      exact Dbar.inv_mem hd
    have hcard : Nat.card ↥(Dbar.map (MulAut.conj t).toMonoidHom) = Nat.card ↥Dbar :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have hmap : Dbar.map (MulAut.conj t).toMonoidHom = Dbar :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  obtain ⟨g, hgπ⟩ := hπ_surj t
  have hDbar_eq : Dbar = (D.subgroupOf H).map π := rfl
  have hpreimage : Subgroup.comap π Dbar = D.subgroupOf H ⊔ (Q2 L1 L2 S).subgroupOf H := by
    change Subgroup.comap π ((D.subgroupOf H).map π) =
      D.subgroupOf H ⊔ (Q2 L1 L2 S).subgroupOf H
    rw [Subgroup.comap_map_eq, hker]
  have hgN : g ∈ Subgroup.normalizer
      (((D.subgroupOf H ⊔ (Q2 L1 L2 S).subgroupOf H : Subgroup ↥H)) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : π x ∈ Dbar := by
        have h1 : x ∈ Subgroup.comap π Dbar := by rw [hpreimage]; exact hx
        exact h1
      have hmem : π (g * x * g⁻¹) ∈ Dbar := by
        have h1 : π (g * x * g⁻¹) = t * π x * t⁻¹ := by
          rw [map_mul, map_mul, map_inv, hgπ]
        rw [h1]
        exact (Subgroup.mem_normalizer_iff.mp htN (π x)).mp hx'
      have h2 : g * x * g⁻¹ ∈ Subgroup.comap π Dbar := hmem
      rwa [hpreimage] at h2
    · intro hx
      have hx' : π (g * x * g⁻¹) ∈ Dbar := by
        have h1 : g * x * g⁻¹ ∈ Subgroup.comap π Dbar := by rw [hpreimage]; exact hx
        exact h1
      have htx : t * π x * t⁻¹ ∈ Dbar := by
        have h1 : π (g * x * g⁻¹) = t * π x * t⁻¹ := by
          rw [map_mul, map_mul, map_inv, hgπ]
        rw [← h1]
        exact hx'
      have hxbar : π x ∈ Dbar := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN)
          (t * π x * t⁻¹)).mp htx
        have h' : t⁻¹ * (t * π x * t⁻¹) * (t⁻¹)⁻¹ = π x := by group
        rwa [h'] at h
      rw [← hpreimage]
      exact hxbar
  let QH : Subgroup ↥H := (Q2 L1 L2 S).subgroupOf H
  let DH : Subgroup ↥H := D.subgroupOf H
  have hH_le_P2 : H ≤ P2 L1 L2 S := by
    rw [show H = u3H L1 L2 S from rfl]
    exact u3H_le_p2 L1 L2 S
  haveI hQHn : QH.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ2_le_H).mpr
      (hH_le_P2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
  have hQHp : IsPGroup 2 QH :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P2 L1 L2 S)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQ2_le_H).symm
  have hDoddH : Odd (Nat.card ↥(D.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_H).toEquiv]
    exact hDodd
  have hQH_inf : QH ⊓ DH = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxG : (x : G) ∈ D ⊓ Q2 L1 L2 S := ⟨hx.2, hx.1⟩
    rw [hDinfQ2] at hxG
    exact Subgroup.mem_bot.mpr (Subtype.ext hxG)
  have hgN' : g ∈ Subgroup.normalizer ((DH ⊔ QH : Subgroup ↥H) : Set ↥H) := by
    change g ∈ Subgroup.normalizer
      ((D.subgroupOf H ⊔ (Q2 L1 L2 S).subgroupOf H : Subgroup ↥H) : Set ↥H)
    exact hgN
  have hQH_inf' : DH ⊓ QH = ⊥ := by rw [inf_comm]; exact hQH_inf
  obtain ⟨n, hnN, hnq⟩ := exists_mem_normalizer_of_mem_normalizer_sup
    (Q := QH) (D := DH) (H := DH ⊔ QH) (sup_comm QH DH).symm hQHp hDoddH
    hQH_inf hgN'
  have hnN' : n ∈ (H ⊓ Subgroup.normalizer (D : Set G)).subgroupOf H := by
    rwa [CFSG.Quasithin.RonanE611.subgroupOf_normalizer_eq hD_le_H]
  have hnD : (n : G) ∈ Subgroup.normalizer (D : Set G) :=
    (Subgroup.mem_subgroupOf.mp hnN').2
  have hnH : (n : G) ∈ H := n.2
  have hnqker : n⁻¹ * g ∈ π.ker := by
    rw [hker]; exact hnq
  have hnq1 : π (n⁻¹ * g) = 1 := MonoidHom.mem_ker.mp hnqker
  have hnπ : π n = t := by
    have hn_eq : n = g * (n⁻¹ * g)⁻¹ := by group
    rw [hn_eq, map_mul, map_inv, hnq1, inv_one, mul_one, hgπ]
  have hwInv : ∀ d ∈ D, (n : G) * d * (n : G)⁻¹ = d⁻¹ := by
    intro d hd
    let dH : ↥H := ⟨d, hD_le_H hd⟩
    have hdDH : dH ∈ DH := Subgroup.mem_subgroupOf.mpr hd
    have hnd : n * dH * n⁻¹ ∈ DH :=
      (Subgroup.mem_normalizer_iff.mp hnN dH).mp hdDH
    have hdbar : π dH ∈ Dbar :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hd)
    have hmemker : n * dH * n⁻¹ * dH ∈ QH := by
      change n * dH * n⁻¹ * dH ∈ (Q2 L1 L2 S).subgroupOf H
      rw [← hker]
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_mul, map_mul, map_inv, hnπ]
      have h := htInv (π dH) hdbar
      rw [h]
      group
    have hbot : n * dH * n⁻¹ * dH ∈ DH ⊓ QH :=
      ⟨DH.mul_mem hnd hdDH, hmemker⟩
    rw [show DH ⊓ QH = ⊥ by rw [inf_comm]; exact hQH_inf, Subgroup.mem_bot] at hbot
    have hnd_eq : n * dH * n⁻¹ = dH⁻¹ := eq_inv_of_mul_eq_one_left hbot
    have hcoe : ((n * dH * n⁻¹ : ↥H) : G) = (dH : G)⁻¹ := by
      rw [hnd_eq]; rfl
    have hcoe' : (n : G) * d * (n : G)⁻¹ = d⁻¹ := by
      simpa [dH] using hcoe
    exact hcoe'
  have hwNotN : (n : G) ∉ Subgroup.normalizer (S : Set G) := by
    intro hnS
    have hn_mem : n ∈ (H ⊓ Subgroup.normalizer (S : Set G)).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr ⟨n.2, hnS⟩
    have ht_in : t ∈ ((H ⊓ Subgroup.normalizer (S : Set G)).subgroupOf H).map π := by
      rw [← hnπ]
      exact Subgroup.mem_map_of_mem π hn_mem
    rw [← hborel_comap] at ht_in
    rw [Subgroup.map_comap_eq_self_of_surjective hπ_surj
      (CFSG.GH74.Uniqueness.Bender.borel Q)] at ht_in
    exact htB ht_in
  let XH : Subgroup ↥H := S.subgroupOf H ⊔ conjugate (S.subgroupOf H) ⟨n, n.2⟩
  have hmapX : XH.map π = ⊤ := by
    rw [show XH = S.subgroupOf H ⊔ conjugate (S.subgroupOf H) ⟨n, n.2⟩ from rfl,
      Subgroup.map_sup]
    rw [CFSG.map_conjugate π (S.subgroupOf H) ⟨n, n.2⟩]
    rw [show (S.subgroupOf H).map π = Qimg from rfl]
    rw [hnπ, ← hQcoe, htTop]
  have hXtop : XH = ⊤ := by
    have hcomap : Subgroup.comap π (XH.map π) = ⊤ := by rw [hmapX, Subgroup.comap_top]
    rw [Subgroup.comap_map_eq] at hcomap
    have hker_le : π.ker ≤ XH := by
      rw [hker]
      exact (Subgroup.subgroupOf_mono H hQ2S).trans le_sup_left
    rwa [sup_eq_left.mpr hker_le] at hcomap
  have hXG : S ⊔ conjugate S (n : G) = H := by
    calc S ⊔ conjugate S (n : G)
        = XH.map H.subtype := by
          rw [show XH = S.subgroupOf H ⊔ conjugate (S.subgroupOf H) ⟨n, n.2⟩ from rfl,
            Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hS_le_H]
          congr 1
          rw [CFSG.map_conjugate H.subtype (S.subgroupOf H) ⟨n, n.2⟩,
            Subgroup.map_subgroupOf_eq_of_le hS_le_H]
          rfl
      _ = (⊤ : Subgroup ↥H).map H.subtype := by rw [hXtop]
      _ = H := by rw [Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨(n : G), hH_eq ▸ hnH, hnD, hwInv, hwNotN, hXG.trans hH_eq⟩

end CFSG.Quasithin.Stroth

end
