module

public import CFSG.Quasithin.H13.L32A721Ma
public import CFSG.Quasithin.H13.L32A721Mb
public import CFSG.Quasithin.Vol2.Ch12Sec6L11b
public import CFSG.Quasithin.H13.L32A721b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (E : Ctx7153 G T L V (hz T V))
include E

theorem inf_hz_le_of_normal {N : Subgroup G} (hKN : mK T V ≤ Subgroup.normalizer (N : Set G))
    (h3 : ¬ 3 ∣ Nat.card ↥N) : N ⊓ hz T V ≤ pCoreOf 2 (hz T V) := by
  have hHN : hz T V ≤ Subgroup.normalizer ((N ⊓ hz T V : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKN (E.hz_le_mK hg), Subgroup.le_normalizer hg⟩
  have hnorm := modO2Image_normal hHN
  have hcard : ¬ 3 ∣ Nat.card ↥(modO2Image (hz T V) (N ⊓ hz T V)) := by
    intro h3'
    rw [card_modO2Image' inf_le_right] at h3'
    exact h3 (h3'.trans ((Subgroup.relIndex_dvd_card _ _).trans
      (Subgroup.card_dvd_of_le inf_le_left)))
  have hbot := (CFSG.pPrimeCore_eq_bot_iff.mp E.pPrimeCore_eq_bot) _ hnorm
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcard)
  intro x hx
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) ⟨x, hx.2⟩ ∈
      modO2Image (hz T V) (N ⊓ hz T V) := mem_modO2Image_iff.mpr ⟨⟨x, hx.2⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, mk_eq_one_iff_hz] at hmem
  exact hmem

theorem v1_le_omegaOneCenter_r1 :
    fsuV1 T V ≤ quasithinOmegaOneCenter (pCoreOf 2 (l1 T L V ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQR, hRT⟩ := E.qh_le_r1
  have hV1 := E.card_v1
  have hV1c : ∀ a ∈ fsuV1 T V, ∀ b ∈ fsuV1 T V, a * b = b * a := by
    intro a ha b hb
    have hbN : b ∈ Subgroup.normalizer (fsuV1 T V : Set G) := Subgroup.le_normalizer hb
    rw [normalizer_eq_centralizer_of_card_eq_two hV1] at hbN
    exact Subgroup.mem_centralizer_iff.mp hbN a ha
  have hV1H : fsuV1 T V ≤ hz T V := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hV1c b hb a ha
  have hV1Q : fsuV1 T V ≤ pCoreOf 2 (hz T V) := by
    refine le_pCoreOf_of_le_normalizer 2 hV1H (Subgroup.centralizer_le_normalizer _) ?_
    exact IsPGroup.of_card (n := 1) (by rw [hV1, pow_one])
  intro v hv
  refine Subgroup.subset_closure ⟨⟨hQR (hV1Q hv), ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (Subgroup.mem_centralizer_iff.mp (E.t_le_hz (hRT hr)) v hv).symm
  · have h2 : Nat.card ↥(Subgroup.zpowers v) ∣ 2 := hV1 ▸ Subgroup.card_dvd_of_le
      (Subgroup.zpowers_le.mpr hv)
    rw [Nat.card_zpowers] at h2
    exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem sup_inf_hz_le {N : Subgroup G} (hKN : mK T V ≤ Subgroup.normalizer (N : Set G))
    (h3 : ¬ 3 ∣ Nat.card ↥N) :
    (N ⊔ pCoreOf 2 (l1 T L V ⊔ T)) ⊓ hz T V ≤ pCoreOf 2 (l1 T L V ⊔ T) := by
  obtain ⟨hQR, hRT⟩ := E.qh_le_r1
  have hRhz : pCoreOf 2 (l1 T L V ⊔ T) ≤ hz T V := hRT.trans E.t_le_hz
  have hRN : pCoreOf 2 (l1 T L V ⊔ T) ≤ Subgroup.normalizer (N : Set G) :=
    hRhz.trans (E.hz_le_mK.trans hKN)
  have hNH := E.inf_hz_le_of_normal hKN h3
  intro x hx
  obtain ⟨hxX, hxH⟩ := Subgroup.mem_inf.mp hx
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN] at hxX
  obtain ⟨r, hr, n, hn, hrn⟩ := Set.mem_mul.mp hxX
  subst hrn
  have hrH : r ∈ hz T V := hRhz hr
  have hnH : n ∈ hz T V := by
    rw [show n = r⁻¹ * (r * n) by group]
    exact mul_mem (inv_mem hrH) hxH
  exact mul_mem hr (hQR (hNH ⟨hn, hnH⟩))

theorem isPGroup_of_normal (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8) {N : Subgroup G}
    (hNK : N ≤ mK T V) (hKN : mK T V ≤ Subgroup.normalizer (N : Set G))
    (h3 : ¬ 3 ∣ Nat.card ↥N) : IsPGroup 2 ↥N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := E.S.hyp
  set R := pCoreOf 2 (l1 T L V ⊔ T) with hR
  obtain ⟨hQR, hRT⟩ := E.qh_le_r1
  have hRhz : R ≤ hz T V := hRT.trans E.t_le_hz
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := hRhz.trans (E.hz_le_mK.trans hKN)
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := E.t_le_mK.trans hKN
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  set X := N ⊔ R with hX
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    mem_normalizer_sup_of_mem (hTN ht) (hTR ht)
  have hXH : X ⊓ hz T V ≤ R := E.sup_inf_hz_le hKN h3
  have hTXR : T ⊓ X = R :=
    le_antisymm (fun t ht => hXH ⟨ht.2, E.t_le_hz ht.1⟩) (le_inf hRT le_sup_right)
  have hsyl : IsSylowTwoOf R X := by
    have h1 := A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_le h (le_sup_right : T ≤ X ⊔ T))
      le_sup_left (sup_le Subgroup.le_normalizer hTX)
    rwa [hTXR] at h1
  have hXK : X ≤ mK T V := sup_le hNK (hRhz.trans E.hz_le_mK)
  have hXT : X ⊔ T ≤ mK T V := sup_le hXK E.t_le_mK
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hOT : pCoreOf 2 (mK T V) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf E.isSylowTwoOf_mK
  have hO : pCoreOf 2 (mK T V) ≤ pCoreOf 2 (X ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      (hXT.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hC : CharTwo (X ⊔ T) := charTwo_of_inH h.fsu.qtke.2.1 S
    ⟨by rw [hS]; exact le_sup_right, fun h0 => E.pCoreOf_mK_ne_bot (le_bot_iff.mp (h0 ▸ hO))⟩
  have hCX : CharTwo X := A4.charTwo_of_normal le_sup_left (sup_le Subgroup.le_normalizer hTX) hC
  set W := conjClosure (quasithinOmegaOneCenter R) X with hW
  obtain ⟨hWO, hWe, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hCX (le_refl _)
  have : IsMulCommutative ↥W := hWe.1
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  have hWX : W ≤ X := hred.1
  have hV1W : fsuV1 T V ≤ W := E.v1_le_omegaOneCenter_r1.trans (le_conjClosure _ _)
  have hCXR : X ⊓ Subgroup.centralizer (W : Set G) ≤ R := fun x hx =>
    hXH ⟨hx.1, Subgroup.centralizer_le hV1W hx.2⟩
  have hCXO : X ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hXW))
      ((pCoreOf_isPGroup 2 (l1 T L V ⊔ T)).to_le hCXR)
  have hOR : pCoreOf 2 X ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsyl
  have hOC : pCoreOf 2 X ≤ Subgroup.centralizer (W : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hWO hw)).2 o ho).symm
  have hROX : R ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 X :=
    le_antisymm (fun r hr => hCXO ⟨hsyl.1 hr.1, hr.2⟩) (le_inf hOR hOC)
  have h3X : ¬ 3 ∣ Nat.card ↥X := by
    intro h3X
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3X
    have hx3 : (x : G) ^ 3 ^ 1 = 1 := by
      rw [pow_one, ← Subgroup.orderOf_coe] at *
      rw [← hx]
      exact pow_orderOf_eq_one _
    have hxN : (x : G) ∈ N :=
      mem_of_mem_sup_of_pow_three hRN ((pCoreOf_isPGroup 2 _)) (by rw [sup_comm]; exact x.2) hx3
    apply h3
    rw [← hx, ← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard N hxN
  have hSQ : SQTKGroup ↥X := InternalSec.sqtkGroup_mono E.sqtk_mK hXK
  have hO2 : pCoreOf 2 (autOn X W) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hJX : thompsonJ X ≤ Subgroup.centralizer (W : Set G) := by
    rcases B2_7 hWe hWX hXW hsyl with ⟨hJ, -⟩ | ⟨-, hFF, -⟩
    · exact hJ
    · exact absurd hFF (S126T2.not_isFFModule_of_three h56 hWe.2 hXW hSQ hO2 h3X)
  have hJR : thompsonJ R ≤ R ⊓ Subgroup.centralizer (W : Set G) :=
    le_inf (thompsonJ_le_self R) ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hsyl).trans hJX)
  have hb : baum R = baum (pCoreOf 2 X) := by
    rw [← hROX]
    exact baum_eq_baum_centralizer hWe ((hWO.trans inf_le_left).trans hOR) hJR
  have hXb : X ≤ Subgroup.normalizer (baum R : Set G) := by
    rw [hb]
    exact (le_normalizer_pCoreOf 2 X).trans
      (normalizer_le_normalizer_of_characteristic inf_le_left (C1GN.characteristic_baum _))
  have hXM : X ≤ Subgroup.normalizer (L : Set G) := hXb.trans (E.normalizer_baum_le hF hC137)
  set Y := oTwoUpper N with hY
  have hYN : Y ≤ N := oTwoUpper_le N
  have hInH : InH T (mK T V) := ⟨E.t_le_mK, E.pCoreOf_mK_ne_bot⟩
  have hnot : ¬ mK T V ≤ Subgroup.normalizer (L : Set G) := fun hle =>
    E.S.hz.2.2 (E.hz_le_mK.trans hle)
  obtain ⟨-, h23⟩ := h1338 G T L L (mK T V) Y h.hyp.h13 h.hyp.h13.faithful hInH hnot
    (by rw [oTwoRes_eq_oTwoUpper, hY, oTwoUpper_oTwoUpper]) (hYN.trans hNK)
    (hKN.trans (normalizer_le_normalizer_oTwoUpper N)) (hYN.trans (le_sup_left.trans hXM))
  have hodd : ∀ n ∈ N, Odd (orderOf n) → n = 1 := by
    intro n hn hno
    by_contra hn1
    have hnY : n ∈ Y := mem_oTwoUpper_of_odd hn hno
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (fun h1 => hn1 (orderOf_eq_one_iff.mp h1))
    have hpY : p ∣ Nat.card ↥Y := hpd.trans (Subgroup.orderOf_dvd_natCard Y hnY)
    rcases h23 p hp hpY with rfl | rfl
    · exact (Nat.not_even_iff_odd.mpr hno) (even_iff_two_dvd.mpr hpd)
    · exact h3 (hpY.trans (Subgroup.card_dvd_of_le hYN))
  intro n
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  refine ⟨k, Subtype.ext ?_⟩
  have hn' : orderOf ((n : G) ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero), Subgroup.orderOf_coe, hnm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    rw [Subgroup.orderOf_coe, hnm]
    exact Dvd.intro m rfl
  have h1 := hodd _ (N.pow_mem n.2 _) (hn' ▸ hm)
  simpa using h1

end Ctx7153

end CFSG.Quasithin.H13.L32A
