module

public import CFSG.Quasithin.H13.A6S13821j
public import CFSG.Quasithin.H13.A6S13821g
public import CFSG.Quasithin.H13.A6S13821e
public import CFSG.Quasithin.H13.A6S1372L76Od1
public import CFSG.Quasithin.Background.H16TwoM22
public import CFSG.Quasithin.H13.A6S1372L19b
public import CFSG.Quasithin.H13.L32AC36b
public import CFSG.Quasithin.H13.L32AC50h

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace A6M22

section Lattice

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat PermLat
open L32A.C.M22Hex

theorem relIndex_eq_three_of_pow_model {P : Subgroup ↥Mgrp}
    (hUP : Ugrp ≤ P) {j : ℕ} (hj : 1 ≤ j) (h3 : Ugrp.relIndex P = 3 ^ j) :
    Ugrp.relIndex P = 3 := by
  obtain ⟨i, hi, hLM, hPL, hcardi⟩ := cert.overgroup_cases_idx (rawIsEnc 22) cert_check P hUP
  set t := 3 ^ j with ht
  have hP : Nat.card P = 128 * t := by
    have h1 := Subgroup.card_mul_index (Ugrp.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv, card_U] at h1
    have h2 : (Ugrp.subgroupOf P).index = t := h3
    rw [h2] at h1
    omega
  have hPj : Nat.card P = cert.sizes.getD i 0 := by
    rw [hPL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardi]
  rw [hP] at hPj
  rw [len_eq] at hi
  have h5 : ¬ (5 : ℕ) ∣ t := fun h =>
    absurd (Nat.prime_five.dvd_of_dvd_pow h) (by norm_num)
  have h3t : 3 ≤ t := by
    rw [ht]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  interval_cases i
  · have hs : cert.sizes.getD 0 0 = 128 := by decide
    omega
  · have hs : cert.sizes.getD 1 0 = 384 := by decide
    rw [h3]
    omega
  · have hs : cert.sizes.getD 2 0 = 1920 := by decide
    exact absurd (by omega : (5 : ℕ) ∣ t) h5
  · have hs : cert.sizes.getD 3 0 = 5760 := by decide
    exact absurd (by omega : (5 : ℕ) ∣ t) h5
  · have hs : cert.sizes.getD 4 0 = 443520 := by decide
    exact absurd (by omega : (5 : ℕ) ∣ t) h5
  · have hs : cert.sizes.getD 5 0 = 384 := by decide
    rw [h3]
    omega

theorem relIndex_eq_three_of_pow {Y : Type} [Group Y] [Finite Y]
    (hY : IsSporadic .M22 Y) {S P : Subgroup Y} (hS : IsSylowTwoOf S ⊤) (hSP : S ≤ P) {j : ℕ}
    (hj : 1 ≤ j) (hP : S.relIndex P = 3 ^ j) : S.relIndex P = 3 := by
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* ↥Mgrp :=
    (e₀ : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M22).trans (MulEquiv.subgroupCongr mGens_closure).symm
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) cert_check (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map _, ?_⟩
    have h : ¬ 2 ∣ S.relIndex ⊤ := hS.2.2
    change ¬ 2 ∣ (S.map e.toMonoidHom).relIndex ⊤
    rw [Subgroup.relIndex_top_right] at h ⊢
    rwa [show (S.map e.toMonoidHom).index = S.index from Subgroup.index_map_equiv (H := S) e]
  obtain ⟨c, hc⟩ := exists_conj_of_isSylowTwoOf hS' hU
  let φ : Y ≃* ↥Mgrp := e.trans (MulAut.conj c)
  have hSφ : S.map φ.toMonoidHom = Ugrp := by
    rw [← hc, Subgroup.map_map]
    rfl
  have hrel : Ugrp.relIndex (P.map φ.toMonoidHom) = S.relIndex P := by
    rw [← hSφ, Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
  rw [← hrel]
  exact relIndex_eq_three_of_pow_model (hSφ ▸ Subgroup.map_mono hSP) hj (hrel.trans hP)

end Lattice

end A6M22

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem comm_V3_mem_of_R1 (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {r : G}
    (hr : r ∈ pCoreOf 2 (S.L1 ⊔ T)) {v : G} (hv : v ∈ S.V3) :
    r * v * r⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have hF := (hS.hF H hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ := hF.H_normalizes_V₁
  have hIH := le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hrH : r ∈ H := hF.L₁T_le_H (pCoreOf_le 2 _ hr)
  have hvU : v ∈ conjClosure S.V3 H := le_conjClosure S.V3 H hv
  have hw := (modMk_mem_subM_iff hIHN hF.V₁_le_Vp hvU).2 hv
  have h1 := S.R1_fix_tilde_V3 hS hH hV₁ hIH (r := ⟨r, hrH⟩) hr hw
  rw [actH_modMk hV₁ hIHN hIH ⟨r, hrH⟩ hvU] at h1
  exact (A6Tv.modMk_conj_eq_iff' hIHN hvU _).1 h1

theorem relIndex_L1_inf_T :
    ∃ j, 1 ≤ j ∧ (S.L1 ⊓ T).relIndex S.L1 = 3 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := pCoreOf 2 S.L1 with hP
  have hPT : P ≤ T := S.O2L1_le_T
  have hPL : P ≤ S.L1 := pCoreOf_le 2 _
  have hPLT : P ≤ S.L1 ⊓ T := le_inf hPL hPT
  have hn : (P.subgroupOf S.L1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).mpr (le_normalizer_pCoreOf 2 S.L1)
  have h3 : IsPGroup 3 (↥S.L1 ⧸ P.subgroupOf S.L1) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using S.cube_mem_pCoreOf_L1' x.2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h3
  have hidx : P.relIndex S.L1 = 3 ^ k := by
    rw [Subgroup.relIndex, Subgroup.index, hk]
  have hdvd : (S.L1 ⊓ T).relIndex S.L1 ∣ 3 ^ k := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_of_le_left S.L1 hPLT
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  refine ⟨j, Nat.pos_of_ne_zero fun h0 => ?_, hj⟩
  rw [h0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact S.not_isPGroup_two_L1 (S.h13.sylow.1.to_le (hj.trans inf_le_right))

attribute [local instance] commGroupOfFact in
theorem false_of_m22_core
    (hIrr : MathieuSmallIrr22) (hA21 : AsA21SQTKSection)
    (h56 : AsB56) (h16 : CFSG.Quasithin.H.Mathieu.StmtH16_2_1M22) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hF : HypF918 T V L (fsuV1 T V) S.V3 H K)
    (hKnH : H ≤ Subgroup.normalizer (K : Set G)) (hHeq : H = K ⊔ T) (hL1K : S.L1 ≤ K)
    (hM : IsSporadic .M22 (L32A.cStar K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKc : K ∈ cComp H := hF.K_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hF.T_le_H
  have hTKn : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKnH
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hTKn ht) k).mp hk) (le_conjClosure K T)
  have hHeq' : H = conjClosure K T ⊔ T := by rw [hK₀]; exact hHeq
  have hSQ : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  obtain ⟨I, hV₁I, hIU, hirrT, hHI, h7⟩ :=
    A6M22.exists_I h56 hD310 hD391 hI4 hSQ hF hK₀ hHeq' hM
  have := factElem hF hIU
  have hcode := A6M22.code_m22 hIrr hA21 hSQ hF hK₀ hM hV₁I hIU hirrT hHI
  set Ψ := A6M22.psiI hF hIU hV₁I hHI with hΨ
  have hker : (pCoreOf 2 K).subgroupOf K ≤ (Ψ.comp (Subgroup.inclusion hKH)).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact A6M22.psiI_eq_one_of_mem_pCoreOf hF hIU hV₁I hHI
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp)
        (Subgroup.mem_subgroupOf.mp hk))
  set ψb : L32A.cStar K →* MulAut ↥(subM (fsuV1 T V) (conjClosure I H) I) :=
    QuotientGroup.lift _ (Ψ.comp (Subgroup.inclusion hKH)) hker with hψb
  have hψmk : ∀ k : ↥K, ψb (QuotientGroup.mk k) = Ψ (Subgroup.inclusion hKH k) := fun k => rfl
  have hrange : ψb.range =
      autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I) := by
    rw [← A6M22.map_psiI hF hIU hV₁I hHI hKH]
    ext φ
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨Subgroup.inclusion hKH k, k.2, (hψmk k).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientGroup.mk ⟨(x : G), hx⟩, hψmk _⟩
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have e2 := autSubEquivOfFaithful (A6M22.autIH_le_stabSub hF hIU hV₁I hHI hKH)
    (A6M22.autIH_inf_centSub hHI K)
  have hSs := L32A.C.isSimpleGroup_of_m22 hM
  have hψinj : Function.Injective ψb := by
    refine injective_of_isSimpleGroup ψb ?_
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hφ : ((e2 ⟨g, hg⟩ : ↥(autSub (autIH (fsuV1 T V) I H K)
        (subM (fsuV1 T V) (conjClosure I H) I))) :
          MulAut ↥(subM (fsuV1 T V) (conjClosure I H) I)) ∈ ψb.range := by
      rw [hrange]
      exact (e2 ⟨g, hg⟩).2
    obtain ⟨s, hs⟩ := hφ
    refine ⟨s, fun h1 => hg1 ?_⟩
    have h2 : e2 ⟨g, hg⟩ = 1 := Subtype.ext (hs.symm.trans h1)
    exact e2.injective (h2.trans (map_one e2).symm)
  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hF.sylow_H hKH hKnH
  set φK : ↥K →* L32A.cStar K := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) with hφK
  have hφs : Function.Surjective φK := QuotientGroup.mk'_surjective _
  have hSst : IsSylowTwoOf (((T ⊓ K).subgroupOf K).map φK) ⊤ := by
    have h1 : IsSylowTwoOf ((T ⊓ K).subgroupOf K) (⊤ : Subgroup ↥K) :=
      (A312.isSylowTwoOf_top_iff_map K ((T ⊓ K).subgroupOf K)).mpr
        (by rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right])
    exact A312.isSylowTwoOf_top_map φK hφs h1
  set X := S.L1 ⊔ (T ⊓ K) with hX
  have hXK : X ≤ K := sup_le hL1K inf_le_right
  have hO2TK : pCoreOf 2 K ≤ T ⊓ K := pCoreOf_le_of_isSylowTwoOf hTK
  have hSP : ((T ⊓ K).subgroupOf K).map φK ≤ (X.subgroupOf K).map φK :=
    Subgroup.map_mono fun _ hk => Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : T ⊓ K ≤ X) (Subgroup.mem_subgroupOf.mp hk))
  have hTN : T ≤ Subgroup.normalizer (S.L1 : Set G) := S.T_le_normalizer_L1
  have hTKN : T ⊓ K ≤ Subgroup.normalizer (S.L1 : Set G) := inf_le_left.trans hTN
  have hXidx : (T ⊓ K).relIndex X = (S.L1 ⊓ T).relIndex S.L1 := by
    have hXc := L32A.C.card_sup_eq hTKN
    rw [sup_comm] at hXc
    have h1 := Subgroup.relIndex_mul_card S.L1 (T ⊓ K)
    have hinf : S.L1 ⊓ (T ⊓ K) = S.L1 ⊓ T := by
      rw [← inf_assoc, inf_right_comm, inf_eq_left.mpr hL1K]
    rw [hinf] at h1
    have h2 := Subgroup.relIndex_mul_card (S.L1 ⊓ T) S.L1
    rw [inf_eq_left.mpr inf_le_left] at h2
    have h4 := Subgroup.relIndex_mul_card (T ⊓ K) X
    rw [inf_eq_left.mpr (le_sup_right : T ⊓ K ≤ X)] at h4
    have hpos : 0 < Nat.card ↥(T ⊓ K) := Nat.card_pos
    have key : (T ⊓ K).relIndex X * Nat.card ↥(T ⊓ K) =
        (S.L1 ⊓ T).relIndex S.L1 * Nat.card ↥(T ⊓ K) := by
      calc (T ⊓ K).relIndex X * Nat.card ↥(T ⊓ K) = Nat.card ↥X := h4
        _ = S.L1.relIndex (T ⊓ K) * Nat.card ↥S.L1 := hXc
        _ = S.L1.relIndex (T ⊓ K) * ((S.L1 ⊓ T).relIndex S.L1 * Nat.card ↥(S.L1 ⊓ T)) := by
            rw [h2]
        _ = (S.L1 ⊓ T).relIndex S.L1 * (S.L1.relIndex (T ⊓ K) * Nat.card ↥(S.L1 ⊓ T)) := by
            ring
        _ = (S.L1 ⊓ T).relIndex S.L1 * Nat.card ↥(T ⊓ K) := by rw [h1]
    exact Nat.eq_of_mul_eq_mul_right hpos key
  obtain ⟨j, hj1, hj⟩ := S.relIndex_L1_inf_T
  have hidx0 : (((T ⊓ K).subgroupOf K).map φK).relIndex ((X.subgroupOf K).map φK) =
      (T ⊓ K).relIndex X := by
    rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk']
    have h1 : (T ⊓ K).subgroupOf K ⊔ (pCoreOf 2 K).subgroupOf K = (T ⊓ K).subgroupOf K :=
      sup_eq_left.mpr fun _ hk =>
        Subgroup.mem_subgroupOf.mpr (hO2TK (Subgroup.mem_subgroupOf.mp hk))
    have h2 : X.subgroupOf K ⊔ (pCoreOf 2 K).subgroupOf K = X.subgroupOf K :=
      sup_eq_left.mpr fun _ hk => Subgroup.mem_subgroupOf.mpr
        ((le_sup_right : T ⊓ K ≤ X) (hO2TK (Subgroup.mem_subgroupOf.mp hk)))
    rw [h1, h2, Subgroup.relIndex_subgroupOf hXK]
  have hidx : (((T ⊓ K).subgroupOf K).map φK).relIndex ((X.subgroupOf K).map φK) = 3 :=
    A6M22.relIndex_eq_three_of_pow hM hSst hSP hj1 (by rw [hidx0, hXidx, hj])
  obtain ⟨Nst, hPN, hNcard, -⟩ := L32A.C.M22Hex.exists_hexad hM hSst hSP hidx
  set NK : Subgroup G := (Nst.comap φK).map K.subtype with hNK
  have hXNK : X ≤ NK := fun g hg =>
    ⟨⟨g, hXK hg⟩, hPN ⟨⟨g, hXK hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩, rfl⟩
  have hNKK : NK ≤ K := Subgroup.map_subtype_le _
  have hTKNK : IsSylowTwoOf (T ⊓ K) NK := by
    refine ⟨le_sup_right.trans hXNK, hTK.2.1, fun h2 => hTK.2.2 ?_⟩
    have hm := Subgroup.relIndex_mul_relIndex (T ⊓ K) NK K (le_sup_right.trans hXNK) hNKK
    exact h2.trans (Dvd.intro _ hm)
  have hXN : S.L1 ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer) fun t ht =>
      L32A.C.mem_normalizer_sup'' (hTN ht)
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTKn ht⟩)
  set R₁ := pCoreOf 2 (S.L1 ⊔ T) with hR₁
  have hO2NK : pCoreOf 2 NK ≤ R₁ := by
    have h1 : pCoreOf 2 NK ≤ T ⊓ K := pCoreOf_le_of_isSylowTwoOf hTKNK
    have h2 : pCoreOf 2 NK ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        (hXNK.trans (le_normalizer_pCoreOf 2 NK)) (pCoreOf_isPGroup 2 NK)
    exact h2.trans (le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 X).trans (sup_le le_sup_left (inf_le_left.trans le_sup_right)))
      (hXN.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X))
  set Nc := Nst.map ψb with hNc
  have hNcL : Nc ≤ autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I) :=
    hrange ▸ Subgroup.map_le_range ψb Nst
  have hNcard' : Nat.card Nc = 5760 := by rw [Subgroup.card_map_of_injective hψinj, hNcard]
  have hO2R : pCoreOf 2 Nc ≤ (R₁.subgroupOf H).map Ψ := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := pCoreOf_le 2 Nc hy
    set P₀ := (pCoreOf 2 Nc).comap ψb ⊓ Nst with hP₀
    have hP₀2 : IsPGroup 2 P₀ :=
      ((pCoreOf_isPGroup 2 Nc).comap_of_injective ψb hψinj).to_le inf_le_left
    have hP₀N : Nst ≤ Subgroup.normalizer (P₀ : Set (L32A.cStar K)) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro p
      have hgN : ψb g ∈ Subgroup.normalizer (pCoreOf 2 Nc : Set _) :=
        le_normalizer_pCoreOf 2 Nc ⟨g, hg, rfl⟩
      constructor
      · rintro ⟨hp1, hp2⟩
        refine ⟨?_, Nst.mul_mem (Nst.mul_mem hg hp2) (Nst.inv_mem hg)⟩
        show ψb (g * p * g⁻¹) ∈ pCoreOf 2 Nc
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hp1
      · rintro ⟨hp1, hp2⟩
        refine ⟨?_, ?_⟩
        · have h1 : ψb (g * p * g⁻¹) ∈ pCoreOf 2 Nc := hp1
          rw [map_mul, map_mul, map_inv] at h1
          exact (Subgroup.mem_normalizer_iff.mp hgN _).mpr h1
        · have := Nst.mul_mem (Nst.mul_mem (Nst.inv_mem hg) hp2) hg
          simpa [mul_assoc] using this
    have hnP : n ∈ pCoreOf 2 Nst :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right hP₀N hP₀2 ⟨hy, hn⟩
    obtain ⟨k, rfl⟩ := hφs n
    set Pk : Subgroup G := ((pCoreOf 2 Nst).comap φK).map K.subtype with hPk
    have hker2 : IsPGroup 2 φK.ker := by
      rw [QuotientGroup.ker_mk']
      exact (pCoreOf_isPGroup 2 K).comap_of_injective K.subtype K.subtype_injective
    have hPk2 : IsPGroup 2 Pk :=
      (((pCoreOf_isPGroup 2 Nst).comap_of_ker_isPGroup φK hker2)).map K.subtype
    have hPkNK : Pk ≤ NK := fun g ⟨k', hk', hk'g⟩ => ⟨k', pCoreOf_le 2 Nst hk', hk'g⟩
    have hNKPk : NK ≤ Subgroup.normalizer (Pk : Set G) := by
      rintro _ ⟨g', hg', rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      have hgN : φK g' ∈ Subgroup.normalizer (pCoreOf 2 Nst : Set (L32A.cStar K)) :=
        le_normalizer_pCoreOf 2 Nst hg'
      intro p
      constructor
      · rintro ⟨p', hp', rfl⟩
        refine ⟨g' * p' * g'⁻¹, ?_, by simp⟩
        show φK (g' * p' * g'⁻¹) ∈ pCoreOf 2 Nst
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hp'
      · rintro ⟨q', hq', hq'e⟩
        have hq'e' : (q' : G) = (g' : G) * p * (g' : G)⁻¹ := hq'e
        have hpK : p ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem g'.2) q'.2) g'.2
          rw [hq'e'] at this
          simpa [mul_assoc] using this
        refine ⟨⟨p, hpK⟩, ?_, rfl⟩
        have hq'' : g' * ⟨p, hpK⟩ * g'⁻¹ = q' := Subtype.ext (by rw [hq'e']; rfl)
        show φK ⟨p, hpK⟩ ∈ pCoreOf 2 Nst
        have h1 : φK q' ∈ pCoreOf 2 Nst := hq'
        rw [← hq'', map_mul, map_mul, map_inv] at h1
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mpr h1
    have hkR : (k : G) ∈ R₁ :=
      hO2NK (le_pCoreOf_of_le_normalizer 2 hPkNK hNKPk hPk2 ⟨k, hnP, rfl⟩)
    exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr hkR, (hψmk k).symm⟩
  have hup := CFSG.Quasithin.H.Mathieu.card_fixMod_le_of_pCoreOf_le h16 hcode hNcL hNcard' hO2R
  have hF91 := (hS.hF H hH).toHypF91
  have hV₁V3 : fsuV1 T V ≤ S.V3 := hF91.V₁_le_Vp
  have hV3c : S.V3 ≤ ⁅conjClosure S.V3 H, conjClosure K T⁆ := by
    have hV3L1 : S.V3 ≤ ⁅S.V3, S.L1⁆ := by
      by_cases hhat : IsHatA6 L
      · exact (V3_le_commutator_of_plus (S14.plusData_l1plus S (S.hatL1Plus hhat))).trans
          (Subgroup.commutator_mono le_rfl (S14.plusData_l1plus S (S.hatL1Plus hhat)).le_L1)
      · exact V3_le_commutator_of_plus (S14.plusData_L1 S hhat)
    exact hV3L1.trans (Subgroup.commutator_mono (le_conjClosure S.V3 H)
      (hL1K.trans (le_conjClosure K T)))
  have hIHN : conjClosure I H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ hIU
  have hV3N : S.V3 ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (le_conjClosure S.V3 H).trans (hF.conjClosure_le_normalizer_V₁ (le_conjClosure S.V3 H))
  have hV3I : S.V3 ≤ I := by
    intro v hv
    have h1 : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨v, hV3N hv⟩ ∈
        tildeOf (fsuV1 T V) I := by
      rw [h7]
      exact secMk_mem_secImg (hV3c hv)
    exact (secMk_mem_tildeOf_iff hV₁I).mp h1
  have hR1V3 : R₁ ≤ Subgroup.normalizer (S.V3 : Set G) := (pCoreOf_le 2 _).trans S.L1T_le_NV3
  have hY4 : (fsuV1 T V).relIndex S.V3 = 4 := by
    have hIHN' : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
      hF.conjClosure_le_normalizer_V₁ (le_conjClosure S.V3 H)
    rw [← card_subM hIHN' hV₁V3 (le_conjClosure S.V3 H)]
    exact S.card_tilde_V3 hS hH
  have hYc : ∀ a ∈ S.V3, ∀ b ∈ S.V3, a * b = b * a := fun a ha b hb => by
    have h := S.frame.ψ.injective (a₁ := ⟨a, S.V3_le_V ha⟩ * ⟨b, S.V3_le_V hb⟩)
      (a₂ := ⟨b, S.V3_le_V hb⟩ * ⟨a, S.V3_le_V ha⟩) (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  obtain ⟨c0, hc0L1, hc0ρ, -⟩ := S.exists_c0
  have hc0K : (c0 : G) ∈ K := hL1K hc0L1
  have hfpf : ∀ v ∈ S.V3, (c0 : G) * v * (c0 : G)⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V :=
    fun v hv hc => S.mem_V1_of_c012 hc0ρ hv hc
  have hlow := A6M22.four_mul_card_le_fixMod hF hIU hV₁I hHI hV₁V3 hV3I hK₀
    (fun r hr v hv => S.comm_V3_mem_of_R1 hS hH hr hv) hR1V3 hc0K hfpf hY4 hYc
  have hCpos : 0 < Nat.card ↥((subM (fsuV1 T V) (conjClosure I H) I ⊓
      fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
        (subM (fsuV1 T V) (conjClosure I H) I)) := Nat.card_pos
  have h42 := hlow.trans hup
  omega

theorem not_isM22
    (hIrr : MathieuSmallIrr22) (hA21 : AsA21SQTKSection)
    (h56 : AsB56) (h16M : CFSG.Quasithin.H.Mathieu.StmtH16_2_1M22) (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ IsSporadic .M22 (↥K ⧸ CFSG.pCore 2 ↥K) := by
  intro hM
  obtain ⟨-, hH₀, -, hKc, hKN₀, hF⟩ := S.reduce13821 h16 h36c h37 h38 h139 h1334 h13 hS hH hK
  have hL1K := S.L1_le_of_quotEquiv hF318 h36 h38 hH₀ hKc (MulEquiv.refl _)
    (a318Exclusion_m22 hM)
  have hHeq : K ⊔ (S.L1 ⊔ T) = K ⊔ T := by
    rw [← sup_assoc, sup_eq_left.mpr hL1K]
  have hM' : IsSporadic .M22 (L32A.cStar K) :=
    IsSporadic.of_mulEquiv (L32A.C.cStarEquiv K).symm hM
  exact S.false_of_m22_core hIrr hA21 h56 h16M hD310 hD391 hI4 hS hH₀ hF hKN₀ hHeq hL1K hM'

end Setting4

theorem case13821M22_holds
    (hIrr : MathieuSmallIrr22) (hA21 : AsA21SQTKSection)
    (h56 : AsB56) (h16M : CFSG.Quasithin.H.Mathieu.StmtH16_2_1M22) (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) : Case13821M22 :=
  fun _ _ _ _ _ _ S hS _ hH _ hK =>
    S.not_isM22 hIrr hA21 h56 h16M h16 h36c h36 h37 h38 hF318 h139 h1334 h13 hD310 hD391 hI4 hS
      hH hK

end CFSG.Quasithin.H13.A6
