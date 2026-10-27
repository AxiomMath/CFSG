module

public import CFSG.Quasithin.H13.A6S13824h
public import CFSG.Quasithin.H13.A6S13822c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace HatEnd

variable {G : Type} [Group G]

theorem relIndex_sup_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

variable {T V L V₁ Vp H : Subgroup G}

theorem centralizerMod_sup_pCoreOf [Finite G] (hF : HypF91 T V L V₁ Vp H) {X : Subgroup G}
    (hXH : X ≤ H) :
    centralizerMod V₁ (conjClosure Vp H) (X ⊔ pCoreOf 2 H) =
      centralizerMod V₁ (conjClosure Vp H) X := by
  apply le_antisymm
  · exact fun u hu => ⟨hu.1, hu.2.1, fun y hy => hu.2.2 y (Subgroup.mem_sup_left hy)⟩
  · rintro u ⟨huU, huN, hu⟩
    refine ⟨huU, huN, fun y hy => ?_⟩
    have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      hXH.trans (le_normalizer_pCoreOf 2 H)
    have hy' : y ∈ ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXQ] at hy'
    obtain ⟨x, hx, q, hq, rfl⟩ := hy'
    have hq' : q ∈ centralizerMod V₁ H (conjClosure Vp H) := by
      rw [← hF.pCoreOf_eq_centralizerMod]
      exact hq
    have h1 : u * q * u⁻¹ * q⁻¹ ∈ V₁ := by
      have h2 := V₁.inv_mem (hq'.2.2 u huU)
      have e : (q * u * q⁻¹ * u⁻¹)⁻¹ = u * q * u⁻¹ * q⁻¹ := by group
      rwa [e] at h2
    have h2 : x * (u * q * u⁻¹ * q⁻¹) * x⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ (hXH hx)) _).mp h1
    have e : u * (x * q) * u⁻¹ * (x * q)⁻¹ =
        (u * x * u⁻¹ * x⁻¹) * (x * (u * q * u⁻¹ * q⁻¹) * x⁻¹) := by group
    rw [e]
    exact V₁.mul_mem (hu x hx) h2

theorem centralizerMod_conjSub (hF : HypF91 T V L V₁ Vp H) {c : G} (hc : c ∈ H)
    (X : Subgroup G) :
    centralizerMod V₁ (conjClosure Vp H) (conjSub c X) =
      conjSub c (centralizerMod V₁ (conjClosure Vp H) X) := by
  rw [conjSub_centralizerMod, F7.conjSub_eq_of_mem_normalizer (hF.H_normalizes_V₁ hc),
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H hc)]

end HatEnd

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_R_four
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T))
    (hnt : ∀ x ∈ pCoreOf 2 (S.L1 ⊔ T),
      ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V))
    (hR4 : (pCoreOf 2 H).relIndex (pCoreOf 2 (S.L1 ⊔ T)) ≤ 4)
    (hRC : 4 ≤ mIdx (conjClosure S.V3 H)
      (centralizerMod (fsuV1 T V) (conjClosure S.V3 H) (pCoreOf 2 (S.L1 ⊔ T)))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  obtain ⟨γ, γ', g, s, hDγ, hDH, hpos, hle⟩ := S.case2_of_no_transv_loc hF hnt
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hS H hH K hK hKn hHK γ γ' g s
    (conjClosure S.V3 H) le_rfl hDH.not_ge
  have hm := S.lem13818Four_loc hS.hNS h13315 h1356two hH hF h13314 hnt s hDγ hDH hle hgen
  obtain ⟨c, hcH, hcR⟩ := exists_conj_Vγ_le hF s
  set U := conjClosure S.V3 H with hUdef
  set V₁ := fsuV1 T V with hV₁def
  set Q := pCoreOf 2 H with hQdef
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  set Vγ := F8.Uγ V H (g : G) with hVγdef
  set Uγ := F8.Uγ S.V3 H (g : G) with hUγdef
  set Dγ := F8.Dγ S.V3 V₁ H (g : G) with hDγdef
  set DH := F8.DH S.V3 V₁ H (g : G) with hDHdef
  set A₁ := F8.A₁ V₁ (g : G) with hA₁def
  have hLTH : S.L1 ⊔ T ≤ H := hF1.L₁T_le_H
  have hQR : Q ≤ R := le_pCoreOf_of_le_normalizer 2
    ((F7.isSylowTwoOf_pCoreOf_le hF1.sylow_H).trans le_sup_right)
    (hLTH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hRH : R ≤ H := (pCoreOf_le 2 _).trans hLTH
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 H).to_le hF1.conjClosure_Vp_le_pCoreOf
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF1.H_normalizes_V₁
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure S.V3 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hUH : U ≤ H := hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hVγH : Vγ ≤ H := hF.Vγ_le_H s
  have hUγVγ : Uγ ≤ Vγ := hF.Uγ_le_Vγ
  have hUγH : Uγ ≤ H := hF.Uγ_le_H s
  have hVγ2 : IsPGroup 2 Vγ := isPGroup_of_isElemAbelian hF.isElemAbelian_Vγ
  have hUγ2 : IsPGroup 2 Uγ := isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hDQ : Dγ = Uγ ⊓ Q := hF.Dγ_eq_inf_pCoreOf s
  have hQeq : Q = centralizerMod V₁ H U := hF1.pCoreOf_eq_centralizerMod
  have hfill : ∀ Z : Subgroup G, Z ≤ R → IsPGroup 2 Z → 2 ≤ mIdx Z (Z ⊓ Q) →
      mIdx Z (Z ⊓ Q) = 2 ∧ Z ⊔ Q = R := by
    intro Z hZR hZ2 hZm
    have hZH : Z ≤ H := hZR.trans hRH
    have hidx : Q.relIndex (Z ⊔ Q) = 2 ^ mIdx Z (Z ⊓ Q) := by
      rw [HatEnd.relIndex_sup_of_le_normalizer (hZH.trans hHQ), ← Subgroup.inf_relIndex_left Z Q,
        HypF98.relIndex_eq_two_pow_mIdx hZ2]
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : Q ≤ Z ⊔ Q) (sup_le hZR hQR)
    have hj : 0 < (Z ⊔ Q).relIndex R := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
    have h4 : 2 ^ mIdx Z (Z ⊓ Q) * (Z ⊔ Q).relIndex R ≤ 4 := by
      rw [← hidx, hmul]
      exact hR4
    have h4' : 2 ^ mIdx Z (Z ⊓ Q) ≤ 2 ^ 2 :=
      (Nat.le_mul_of_pos_right _ hj).trans (h4.trans (by norm_num))
    have hm' : mIdx Z (Z ⊓ Q) = 2 :=
      le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp h4') hZm
    refine ⟨hm', le_antisymm (sup_le hZR hQR) ?_⟩
    rw [hm'] at h4
    have h1 : (Z ⊔ Q).relIndex R = 1 := by
      norm_num at h4
      omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hcQ : conjSub c Q = Q := F7.conjSub_eq_of_mem_normalizer (hHQ hcH)
  have hY2 : IsPGroup 2 (conjSub c Vγ) := isPGroup_conjSub hVγ2
  have hmY : mIdx (conjSub c Vγ) (conjSub c Vγ ⊓ Q) = mIdx Vγ (Vγ ⊓ Q) := by
    have h1 := F9.mIdx_conjSub c Vγ (Vγ ⊓ Q)
    rwa [conjSub_inf, hcQ] at h1
  obtain ⟨hmY2, hYQ⟩ := hfill (conjSub c Vγ) hcR hY2 (by omega)
  have hm2 : mIdx Vγ (Vγ ⊓ Q) = 2 := hmY ▸ hmY2
  have hRCV : 4 ≤ mIdx U (centralizerMod V₁ U Vγ) := by
    have h1 : centralizerMod V₁ U R = conjSub c (centralizerMod V₁ U Vγ) := by
      rw [← hYQ, HatEnd.centralizerMod_sup_pCoreOf hF1 (hcR.trans hRH),
        HatEnd.centralizerMod_conjSub hF1 hcH]
    have h2 := F9.mIdx_conjSub c U (centralizerMod V₁ U Vγ)
    rw [F7.conjSub_eq_of_mem_normalizer (hHU hcH), ← h1] at h2
    rw [← h2]
    exact hRC
  have hmono : mIdx Uγ Dγ ≤ 2 := by
    rw [hDQ]
    have h1 := Subgroup.relIndex_le_of_le_right hUγVγ (relIndex_ne_zero' Q Vγ)
    rw [← Subgroup.inf_relIndex_left Uγ Q, ← Subgroup.inf_relIndex_left Vγ Q,
      HypF98.relIndex_eq_two_pow_mIdx hUγ2, HypF98.relIndex_eq_two_pow_mIdx hVγ2, hm2] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hUst : U ≤ conjSub (g : G) H := by
    rw [← hstab]
    exact (conjClosure_mono S.V3_le_V le_rfl).trans
      ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans inf_le_right))
  have hUA : U ≤ Subgroup.normalizer (A₁ : Set G) :=
    hUst.trans (conjSub_le_normalizer hF1.H_normalizes_V₁)
  have hUUγ : U ≤ Subgroup.normalizer (Uγ : Set G) :=
    hUst.trans (conjSub_le_normalizer (le_normalizer_conjClosure S.V3 H))
  have hUγQ : Uγ ≤ Subgroup.normalizer (Q : Set G) := hUγH.trans hHQ
  have hVγQ : Vγ ≤ Subgroup.normalizer (Q : Set G) := hVγH.trans hHQ
  have hiV : Q.relIndex (Vγ ⊔ Q) = 4 := by
    rw [HatEnd.relIndex_sup_of_le_normalizer hVγQ, ← Subgroup.inf_relIndex_left Vγ Q,
      HypF98.relIndex_eq_two_pow_mIdx hVγ2, hm2]
    norm_num
  rcases (show mIdx Uγ Dγ = 1 ∨ mIdx Uγ Dγ = 2 by omega) with hm1 | hm2'
  ·
    obtain ⟨x, hxU, hxD⟩ := IsConcreteLE.exists_of_lt hDγ
    have hCH := S.relIndex_CH_le hS hH s hm1 hxU hxD
    set CH := U ⊓ Subgroup.centralizer (Uγ : Set G) with hCHdef
    have hDHU : DH.relIndex U ≤ 2 := by
      rw [HypF98.relIndex_eq_two_pow_mIdx hU2]
      calc 2 ^ mIdx U DH ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (hm1 ▸ hle)
        _ = 2 := by norm_num
    have hCHU : CH.relIndex U ≤ 4 := by
      have h1 : CH.relIndex U ≤ (CH ⊓ DH).relIndex U :=
        Subgroup.relIndex_le_of_le_left inf_le_left (relIndex_ne_zero' _ _)
      have h2 : (CH ⊓ DH).relIndex DH * DH.relIndex U = (CH ⊓ DH).relIndex U :=
        Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right (centralizerMod_le_left _ _ _)
      rw [Subgroup.inf_relIndex_right] at h2
      calc CH.relIndex U ≤ (CH ⊓ DH).relIndex U := h1
        _ = CH.relIndex DH * DH.relIndex U := h2.symm
        _ ≤ 2 * 2 := Nat.mul_le_mul hCH hDHU
    have hiU : Q.relIndex (Uγ ⊔ Q) = 2 := by
      rw [HatEnd.relIndex_sup_of_le_normalizer hUγQ, ← Subgroup.inf_relIndex_left Uγ Q,
        HypF98.relIndex_eq_two_pow_mIdx hUγ2, ← hDQ, hm1, pow_one]
    have hUVQ : Uγ ⊔ Q ≤ Vγ ⊔ Q := sup_le_sup_right hUγVγ Q
    have hi2 : (Uγ ⊔ Q).relIndex (Vγ ⊔ Q) = 2 := by
      have h1 := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : Q ≤ Uγ ⊔ Q) hUVQ
      rw [hiU, hiV] at h1
      omega
    obtain ⟨v₀, hv₀V, hv₀N⟩ : ∃ v₀ ∈ Vγ, v₀ ∉ Uγ ⊔ Q := by
      by_contra hcon
      push Not at hcon
      have h1 : Vγ ⊔ Q ≤ Uγ ⊔ Q := sup_le (fun y hy => hcon y hy) le_sup_right
      have h2 := Subgroup.relIndex_eq_one.mpr h1
      rw [hi2] at h2
      exact absurd h2 (by norm_num)
    have hmod : ∀ y ∈ Vγ, y ∉ Uγ ⊔ Q → y * v₀⁻¹ ∈ Uγ ⊔ Q := by
      intro y hy hyN
      have hidx : ((Uγ ⊔ Q).subgroupOf (Vγ ⊔ Q)).index = 2 := hi2
      have hy' : (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Vγ ⊔ Q)) ∉ (Uγ ⊔ Q).subgroupOf (Vγ ⊔ Q) :=
        fun h => hyN (Subgroup.mem_subgroupOf.mp h)
      have hv' : (⟨v₀, Subgroup.mem_sup_left hv₀V⟩ : ↥(Vγ ⊔ Q))⁻¹ ∉
          (Uγ ⊔ Q).subgroupOf (Vγ ⊔ Q) := by
        intro h
        apply hv₀N
        have h' := (Uγ ⊔ Q).inv_mem (Subgroup.mem_subgroupOf.mp h)
        simpa using h'
      have h1 := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hy' hv')
      simpa using Subgroup.mem_subgroupOf.mp h1
    have hQcomm : ∀ c' ∈ CH, ∀ q ∈ Vγ ⊓ Q, q * c' = c' * q := by
      intro c' hc' q hq
      have h1 : q * c' * q⁻¹ * c'⁻¹ ∈ A₁ :=
        S.comm_mem_A₁_of_cent hS h13315 h1356two hH s hc'.1
          (fun u hu => Subgroup.mem_centralizer_iff.mp hc'.2 u hu) hq.1
      have h2 : q * c' * q⁻¹ * c'⁻¹ ∈ V₁ := by
        have hq' : q ∈ centralizerMod V₁ H U := hQeq ▸ hq.2
        exact hq'.2.2 c' hc'.1
      have h3 : q * c' * q⁻¹ * c'⁻¹ ∈ V₁ ⊓ A₁ := ⟨h2, h1⟩
      rw [hF.F913_5b s, Subgroup.mem_bot] at h3
      calc q * c' = (q * c' * q⁻¹ * c'⁻¹) * (c' * q) := by group
        _ = c' * q := by rw [h3, one_mul]
    have hcentV : ∀ c' ∈ CH, v₀ * c' = c' * v₀ → ∀ y ∈ Vγ, y * c' = c' * y := by
      intro c' hc' hv₀c
      have key : ∀ y ∈ Vγ, y ∈ Uγ ⊔ Q → y * c' = c' * y := by
        intro y hy hyN
        have hy' : y ∈ ((Uγ ⊔ Q : Subgroup G) : Set G) := hyN
        rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUγQ] at hy'
        obtain ⟨u, hu, q, hq, rfl⟩ := hy'
        have hqV : q ∈ Vγ := by
          have h1 : u⁻¹ * (u * q) ∈ Vγ := Vγ.mul_mem (Vγ.inv_mem (hUγVγ hu)) hy
          simpa using h1
        have h1 := Subgroup.mem_centralizer_iff.mp hc'.2 u hu
        have h2 := hQcomm c' hc' q ⟨hqV, hq⟩
        calc u * q * c' = u * (q * c') := by group
          _ = u * (c' * q) := by rw [h2]
          _ = (u * c') * q := by group
          _ = c' * u * q := by rw [h1]
          _ = c' * (u * q) := by group
      intro y hy
      by_cases hyN : y ∈ Uγ ⊔ Q
      · exact key y hy hyN
      · have h1 := key (y * v₀⁻¹) (Vγ.mul_mem hy (Vγ.inv_mem hv₀V)) (hmod y hy hyN)
        calc y * c' = (y * v₀⁻¹) * (v₀ * c') := by group
          _ = (y * v₀⁻¹) * (c' * v₀) := by rw [hv₀c]
          _ = ((y * v₀⁻¹) * c') * v₀ := by group
          _ = (c' * (y * v₀⁻¹)) * v₀ := by rw [h1]
          _ = c' * y := by group
    have hcA : Nat.card ↥A₁ = 2 := hF.card_A₁
    have hδmem : ∀ c' ∈ CH, v₀ * c' * v₀⁻¹ * c'⁻¹ ∈ A₁ := fun c' hc' =>
      S.comm_mem_A₁_of_cent hS h13315 h1356two hH s hc'.1
        (fun u hu => Subgroup.mem_centralizer_iff.mp hc'.2 u hu) hv₀V
    have hA₁N : A₁ ≤ Subgroup.normalizer (A₁ : Set G) := Subgroup.le_normalizer
    let δ : ↥CH →* ↥A₁ :=
      { toFun := fun d => ⟨v₀ * (d : G) * v₀⁻¹ * (d : G)⁻¹, hδmem d d.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => by
          apply Subtype.ext
          show v₀ * ((a * b : ↥CH) : G) * v₀⁻¹ * ((a * b : ↥CH) : G)⁻¹ =
            (v₀ * (a : G) * v₀⁻¹ * (a : G)⁻¹) * (v₀ * (b : G) * v₀⁻¹ * (b : G)⁻¹)
          have h1 := A6Gen.conj_eq_of_card_two hcA (hUA a.2.1) (hδmem b b.2)
          have e : v₀ * ((a * b : ↥CH) : G) * v₀⁻¹ * ((a * b : ↥CH) : G)⁻¹ =
              (v₀ * (a : G) * v₀⁻¹ * (a : G)⁻¹) *
                ((a : G) * (v₀ * (b : G) * v₀⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
            simp only [Subgroup.coe_mul]
            group
          rw [e, h1] }
    set CV := U ⊓ Subgroup.centralizer (Vγ : Set G) with hCVdef
    have hker : δ.ker ≤ CV.subgroupOf CH := by
      intro d hd
      have hd1 : v₀ * (d : G) * v₀⁻¹ * (d : G)⁻¹ = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
      have hdv : v₀ * (d : G) = (d : G) * v₀ := by
        calc v₀ * (d : G) = (v₀ * (d : G) * v₀⁻¹ * (d : G)⁻¹) * ((d : G) * v₀) := by group
          _ = (d : G) * v₀ := by rw [hd1, one_mul]
      rw [Subgroup.mem_subgroupOf]
      exact ⟨d.2.1, Subgroup.mem_centralizer_iff.2 fun y hy => hcentV d d.2 hdv y hy⟩
    have hCVCH : CV.relIndex CH ≤ 2 := by
      have h1 := Subgroup.index_dvd_of_le hker
      have h2 := Subgroup.index_ker δ
      have h3 : Nat.card ↥δ.range ≤ 2 := hcA ▸ Subgroup.card_le_card_group δ.range
      have h4 : δ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h5 := Nat.le_of_dvd (Nat.pos_of_ne_zero h4) h1
      show (CV.subgroupOf CH).index ≤ 2
      omega
    have hCVle : CV ≤ CH :=
      inf_le_inf_left U (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUγVγ))
    have hCVU : CV.relIndex U ≤ 8 := by
      have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hCVle (inf_le_left : CH ≤ U)
      calc CV.relIndex U = CV.relIndex CH * CH.relIndex U := h1.symm
        _ ≤ 2 * 4 := Nat.mul_le_mul hCVCH hCHU
    have hCVC : CV ≤ centralizerMod V₁ U Vγ := fun u hu =>
      ⟨hu.1, hHV₁ (hUH hu.1), fun y hy => by
        rw [← Subgroup.mem_centralizer_iff.mp hu.2 y hy, mul_inv_cancel_right, mul_inv_cancel]
        exact V₁.one_mem⟩
    have h3 : mIdx U (centralizerMod V₁ U Vγ) ≤ 3 := by
      have h1 := A6Gen.mIdx_le_of_le hU2 hCVC
      have h2 : 2 ^ mIdx U CV ≤ 2 ^ 3 := by
        rw [← HypF98.relIndex_eq_two_pow_mIdx hU2]
        exact hCVU.trans (by norm_num)
      exact h1.trans ((Nat.pow_le_pow_iff_right (by norm_num)).mp h2)
    omega
  ·
    have hiU : Q.relIndex (Uγ ⊔ Q) = 4 := by
      rw [HatEnd.relIndex_sup_of_le_normalizer hUγQ, ← Subgroup.inf_relIndex_left Uγ Q,
        HypF98.relIndex_eq_two_pow_mIdx hUγ2, ← hDQ, hm2']
      norm_num
    have hUQ : Uγ ⊔ Q = Vγ ⊔ Q := by
      have hUVQ : Uγ ⊔ Q ≤ Vγ ⊔ Q := sup_le_sup_right hUγVγ Q
      refine le_antisymm hUVQ ?_
      have h1 := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : Q ≤ Uγ ⊔ Q) hUVQ
      rw [hiU, hiV] at h1
      have h2 : (Uγ ⊔ Q).relIndex (Vγ ⊔ Q) = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp h2
    have hCUV : centralizerMod V₁ U Uγ = centralizerMod V₁ U Vγ := by
      rw [← HatEnd.centralizerMod_sup_pCoreOf hF1 hUγH, hUQ,
        HatEnd.centralizerMod_sup_pCoreOf hF1 hVγH]
    obtain ⟨hq, hr⟩ := hF.F916_2_aux s hpos hle
    have hq4 : mIdx U (centralizerMod V₁ U Uγ) ≤ 4 := by
      have h1 := hq.2.2.2.2
      rw [HypF98.relIndex_eq_two_pow_mIdx hU2, HypF98.relIndex_eq_two_pow_mIdx hUγ2, ← hDQ,
        hm2'] at h1
      have h2 : 2 ^ mIdx U (centralizerMod V₁ U Uγ) ≤ 2 ^ 4 := h1.trans (by norm_num)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    have heq : 2 * mIdx Uγ Dγ = mIdx U (centralizerMod V₁ U Uγ) := by
      have h1 : 4 ≤ mIdx U (centralizerMod V₁ U Uγ) := by
        rw [hCUV]
        exact hRCV
      omega
    have hmeq := (hr heq).1
    have hDHQ : DH = U ⊓ conjSub (g : G) Q := by
      have h1 : conjSub (g : G) Q = centralizerMod A₁ (conjSub (g : G) H) Uγ := by
        rw [hQeq, conjSub_centralizerMod]
        rfl
      rw [h1]
      ext u
      constructor
      · intro hu
        exact ⟨hu.1, hUst hu.1, hu.2.1, hu.2.2⟩
      · rintro ⟨hu, -, hN, hc⟩
        exact ⟨hu, hN, hc⟩
    have hV₁Uγ : V₁ ≤ Uγ := by
      by_contra hV₁U
      have hcomm : ∀ d ∈ Dγ, ∀ u ∈ U, d * u * d⁻¹ * u⁻¹ = 1 := by
        intro d hd u hu
        have h1 : d * u * d⁻¹ * u⁻¹ ∈ V₁ := hd.2.2 u hu
        have hdU : d ∈ Uγ := centralizerMod_le_left _ _ _ hd
        have h2 : d * u * d⁻¹ * u⁻¹ ∈ Uγ := by
          have h3 : u * d⁻¹ * u⁻¹ ∈ Uγ :=
            (Subgroup.mem_normalizer_iff.mp (hUUγ hu) _).mp (Uγ.inv_mem hdU)
          have e : d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) := by group
          rw [e]
          exact Uγ.mul_mem hdU h3
        rcases S.mem_V1_iff.1 h1 with h | h
        · exact h
        · exfalso
          apply hV₁U
          intro v hv
          rcases S.mem_V1_iff.1 hv with h' | h'
          · rw [h']
            exact Uγ.one_mem
          · rw [h', ← h]
            exact h2
      have hY'R : conjSub (g : G)⁻¹ U ≤ R :=
        (conjSub_mono _ (conjClosure_mono S.V3_le_V le_rfl)).trans (S.conjSub_VH_le_R hF s)
      have hY'2 : IsPGroup 2 (conjSub (g : G)⁻¹ U) := isPGroup_conjSub hU2
      have hmY' : mIdx (conjSub (g : G)⁻¹ U) (conjSub (g : G)⁻¹ U ⊓ Q) = 2 := by
        have h1 := F9.mIdx_conjSub (g : G)⁻¹ U (U ⊓ conjSub (g : G) Q)
        rw [conjSub_inf, conjSub_conjSub_inv, ← hDHQ, ← hmeq, hm2'] at h1
        exact h1
      obtain ⟨-, hY'Q⟩ := hfill _ hY'R hY'2 hmY'.ge
      have hUγU : conjSub (g : G)⁻¹ Uγ = U := conjSub_conjSub_inv _ _
      have hD'U : conjSub (g : G)⁻¹ Dγ ≤ U := by
        have h1 := conjSub_mono (g : G)⁻¹ (centralizerMod_le_left V₁ Uγ U)
        rwa [hUγU] at h1
      have hD'C : conjSub (g : G)⁻¹ Dγ ≤ centralizerMod V₁ U R := by
        rw [← hY'Q, HatEnd.centralizerMod_sup_pCoreOf hF1 (hY'R.trans hRH)]
        intro d hd
        refine ⟨hD'U hd, hHV₁ (hUH (hD'U hd)), fun y hy => ?_⟩
        have hd' := mem_conjSub.mp hd
        have hy' := mem_conjSub.mp hy
        have h1 := hcomm _ hd' _ hy'
        have e : d * y * d⁻¹ * y⁻¹ = (g : G)⁻¹ * (((g : G)⁻¹⁻¹ * d * (g : G)⁻¹) *
            ((g : G)⁻¹⁻¹ * y * (g : G)⁻¹) * ((g : G)⁻¹⁻¹ * d * (g : G)⁻¹)⁻¹ *
            ((g : G)⁻¹⁻¹ * y * (g : G)⁻¹)⁻¹) * (g : G) := by group
        rw [e, h1, mul_one, inv_mul_cancel]
        exact V₁.one_mem
      have h1 : mIdx U (centralizerMod V₁ U R) ≤ mIdx U (conjSub (g : G)⁻¹ Dγ) :=
        A6Gen.mIdx_le_of_le hU2 hD'C
      have h2 : mIdx U (conjSub (g : G)⁻¹ Dγ) = 2 := by
        have h3 := F9.mIdx_conjSub (g : G)⁻¹ Uγ Dγ
        rw [hUγU, hm2'] at h3
        exact h3
      omega
    exact S.lemma13_8_11_one hS.hNS h13315 h1356two hH hF h13314 s hgen (Or.inl hV₁Uγ)
      (le_sup_left.trans hUQ.ge)

end Setting4

end CFSG.Quasithin.H13.A6
