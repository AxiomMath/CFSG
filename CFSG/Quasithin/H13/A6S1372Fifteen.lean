module

public import CFSG.Quasithin.H13.A6S1372Fourteen
public import CFSG.Quasithin.Background.B53FFJImage
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.Background.C129NativeLight

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6Mod

variable {G : Type} [Group G] {U C Y : Subgroup G} [IsMulCommutative ↥U]

theorem autSec_map_conj (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hYC : Y ≤ Subgroup.normalizer ((U ⊓ C : Subgroup G) : Set G)) {F : Subgroup G}
    (hFY : F ≤ Y) (y : ↥Y) :
    autSec (autOn (F.map (MulAut.conj (y : G)).toMonoidHom) U) ⊤ (C.subgroupOf U) =
      (autSec (autOn F U) ⊤ (C.subgroupOf U)).map
        (MulAut.conj (secAct hYU hYC y)).toMonoidHom := by
  have hFyY : F.map (MulAut.conj (y : G)).toMonoidHom ≤ Y := by
    rintro _ ⟨f, hf, rfl⟩
    exact Y.mul_mem (Y.mul_mem y.2 (hFY hf)) (Y.inv_mem y.2)
  ext ψ
  rw [mem_autSec_iff hYU hYC hFyY, Subgroup.mem_map]
  constructor
  · rintro ⟨f, ⟨f', hf', hff'⟩, rfl⟩
    refine ⟨secAct hYU hYC ⟨f', hFY hf'⟩,
      (mem_autSec_iff hYU hYC hFY).2 ⟨⟨f', hFY hf'⟩, hf', rfl⟩, ?_⟩
    have e : f = y * ⟨f', hFY hf'⟩ * y⁻¹ := Subtype.ext (by rw [← hff']; rfl)
    rw [e, map_mul, map_mul, map_inv]
    rfl
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨f', hf', rfl⟩ := (mem_autSec_iff hYU hYC hFY).1 hφ
    refine ⟨y * f' * y⁻¹, ⟨f', hf', rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl

end A6Mod

namespace A6Fifteen

variable {G : Type} [Group G]

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]


theorem sqtkGroup_of_mulEquiv {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q]
    (e : X ≃* Q) (hS : SQTKGroup X) : SQTKGroup Q := by
  refine InternalSec.sqtkGroup_of_surjective e.toMonoidHom e.surjective ?_ hS
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
  exact IsPGroup.of_bot

end A6Fifteen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Orbit

theorem orbit_cComp
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) :
    (∀ c ∈ H, c ^ 3 = 1 → c ∈ Subgroup.normalizer (K : Set G)) ∧
      ∃ t ∈ T, ∀ h ∈ H, K.map (MulAut.conj h).toMonoidHom = K ∨
        K.map (MulAut.conj h).toMonoidHom = K.map (MulAut.conj t).toMonoidHom := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hO2 : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  rcases QuasithinUnique.Vol2Native.lemma_1_2_1_three hloc
      QuasithinUnique.Vol2Native.a37ForSQTKCat_proved C129Native.a38ForSQTKCat_proved hO2 hK
    with hn | ⟨h2, -⟩
  · have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK)).mp hn
    exact ⟨fun c hc _ => hHN hc, 1, T.one_mem, fun h hh =>
      Or.inl (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHN hh))⟩
  · have hidx : ((Subgroup.normalizer (K : Set G)).subgroupOf H).index = 2 := by
      rw [← A5.ncard_conjSubgroupsBy_eq_index]
      exact h2
    refine ⟨fun c hc hc3 => ?_, ?_⟩
    · have h := Subgroup.mul_self_mem_of_index_two hidx (⟨c, hc⟩ * ⟨c, hc⟩)
      rw [Subgroup.mem_subgroupOf] at h
      have e : ((⟨c, hc⟩ * ⟨c, hc⟩ * (⟨c, hc⟩ * ⟨c, hc⟩) : ↥H) : G) = c := by
        simp only [Subgroup.coe_mul]
        calc c * c * (c * c) = (c * c * c) * c := by simp only [mul_assoc]
          _ = c := by rw [← pow_three', hc3, one_mul]
      rwa [e] at h
    · obtain ⟨t, htT, htN⟩ := A5.exists_not_mem_normalizer_of_ncard_two hTsyl h2
      set K₁ := K.map (MulAut.conj t).toMonoidHom with hK₁
      have hne : K ≠ K₁ := fun h =>
        htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
      have hsub : ({K, K₁} : Set (Subgroup G)) ⊆ conjSubgroupsBy H K := by
        intro X' hX'
        rcases hX' with rfl | rfl
        · exact ⟨1, H.one_mem, by ext x; simp⟩
        · exact ⟨t, hTsyl.1 htT, rfl⟩
      have hfin : (conjSubgroupsBy H K).Finite := Set.finite_of_ncard_ne_zero (by omega)
      have heq : ({K, K₁} : Set (Subgroup G)) = conjSubgroupsBy H K :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [h2, Set.ncard_pair hne]) hfin
      refine ⟨t, htT, fun h hh => ?_⟩
      have hmem : K.map (MulAut.conj h).toMonoidHom ∈ conjSubgroupsBy H K := ⟨h, hh, rfl⟩
      rw [← heq] at hmem
      exact hmem

end Orbit

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hNS h13315 h1356two hH hab in
theorem eq_top_of_conj_V3 [IsMulCommutative ↥(conjClosure S.V3 H)]
    {M : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))}
    (hM : ∀ h : ↥H, ∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
        (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
          (conjClosure S.V3 H))),
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H)) h w ∈ M) :
    M = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ x
  have hle : conjClosure S.V3 H ≤ (M.comap (InternalSec.secMk
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))).map
        (conjClosure S.V3 H).subtype := conjClosure_le fun h hh z hz => by
    refine ⟨⟨h * z * h⁻¹, mem_conjClosure hh hz⟩, ?_, rfl⟩
    have h1 := hM ⟨h, hh⟩ _ ⟨⟨z, le_conjClosure _ _ hz⟩, hz, rfl⟩
    rw [A6Mod.secAct_secMk] at h1
    have e : (⟨h * z * h⁻¹, mem_conjClosure hh hz⟩ : ↥(conjClosure S.V3 H)) =
        Setup.rho (conjClosure S.V3 H) H (le_normalizer_conjClosure S.V3 H) ⟨h, hh⟩
          ⟨z, le_conjClosure _ _ hz⟩ := Subtype.ext (by rw [Setup.rho_apply_coe])
    rw [SetLike.mem_coe, Subgroup.mem_comap, e]
    exact h1
  obtain ⟨u', hu', hu'u⟩ := hle u.2
  have e : u' = u := Subtype.ext hu'u
  rw [← e]
  exact hu'

omit hNS h13315 h1356two hH hab in
theorem secAct_mem_V3_plus [IsMulCommutative ↥(conjClosure S.V3 H)] {g : G} (hg : g ∈ H)
    (hgV : g ∈ Subgroup.normalizer (S.V3 : Set G))
    {w : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))}
    (hw : w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
      (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
        (conjClosure S.V3 H)))) :
    A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H)) ⟨g, hg⟩ w ∈
      (S.V3.subgroupOf (conjClosure S.V3 H)).map
        (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
          (conjClosure S.V3 H))) := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [A6Mod.secAct_secMk]
  refine ⟨_, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Setup.rho_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp hgV (u : G)).mp hu

omit hab in
theorem card_V3_plus (h13314 : Stmt13_3_14)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    Nat.card ↥((S.V3.subgroupOf (conjClosure S.V3 H)).map
      (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
        (conjClosure S.V3 H)))) = 4 := by
  have hVU : S.V3 ≤ (conjClosure S.V3 H) := le_conjClosure _ _
  set ψ : ↥S.V3 →* Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :=
    (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
      (conjClosure S.V3 H))).comp (Subgroup.inclusion hVU) with hψ
  have hrange : ψ.range = (S.V3.subgroupOf (conjClosure S.V3 H)).map (InternalSec.secMk
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨Subgroup.inclusion hVU v, v.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hker : Nat.card ψ.ker = 2 := by
    have e : ψ.ker.map S.V3.subtype = fsuV1 T V := by
      rw [← S.V3_inf_U0 hNS h13315 h1356two hH h13314]
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply,
          A6Mod.secMk_eq_one_iff] at hv
        exact ⟨v.2, hVU v.2, hv⟩
      · rintro ⟨hx3, -, hxC⟩
        refine ⟨⟨x, hx3⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply,
          A6Mod.secMk_eq_one_iff]
        exact hxC
    have h1 : Nat.card ψ.ker = Nat.card ↥(fsuV1 T V) := by
      rw [← e, Subgroup.card_map_of_injective S.V3.subtype_injective]
    rw [h1, S.card_V1]
  have h := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hker, S.card_V3, hrange] at h
  omega

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

include C in
theorem exists_c1_mem [IsMulCommutative ↥(conjClosure S.V3 H)]
    (h13314 : Stmt13_3_14) :
    ∃ (c₁ : G) (hc₁ : c₁ ∈ H), c₁ ^ 3 = 1 ∧ c₁ ∈ Subgroup.normalizer (S.V3 : Set G) ∧
      ∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H))),
        A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H))
          ⟨c₁, hc₁⟩ w = w → w = 1 := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  obtain ⟨c₁, hc₁L, hc₁3, hρ, -⟩ := C.exists_c1 hNS h13315 h1356two hH hab hhat
  have hc₁H : (c₁ : G) ∈ H := S.L1_le_of_mem_Hz hNS h13315 h1356two hH hc₁L
  have hcV3 : (c₁ : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    S.L1T_le_NV3 (le_sup_left (a := S.L1) hc₁L)
  refine ⟨c₁, hc₁H, hc₁3, hcV3, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ hfix
  rw [A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
    A6Mod.secMk_eq_one_iff] at hfix
  rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at hfix
  have hu' : (u : G) ∈ S.V3 := hu
  have hcu : (c₁ : G) * u * (c₁ : G)⁻¹ ∈ S.V3 :=
    (Subgroup.mem_normalizer_iff.mp hcV3 (u : G)).mp hu'
  have h1 : (c₁ : G) * u * (c₁ : G)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
    rw [← S.V3_inf_U0 hNS h13315 h1356two hH h13314]
    refine ⟨S.V3.mul_mem hcu (S.V3.inv_mem hu'), ?_, hfix⟩
    exact (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (hHU hc₁H) (u : G)).mp u.2) ((conjClosure S.V3 H).inv_mem u.2)
  have h2 := S.mem_V1_of_c012 hρ hu' h1
  exact (A6Mod.secMk_eq_one_iff _).2 (S.V1_le_centralizer_QH hNS h13315 h1356two hH h2)

theorem exists_K_normal
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hLem : Lem1374One) (h56 : AsB56)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
      B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
      ∃ K ∈ cComp H, CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
          (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
        B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ≤
          Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
              Subgroup _) : Set _) ∧
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊤ ∧
        quasithinGenFitting (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) =
          autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) := by
  obtain ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot⟩ :=
    C.exists_K hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem
  refine ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, ?_⟩
  set X := autSec (autOn H (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hX
  set Kp := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hKp
  set W := (S.V3.subgroupOf (conjClosure S.V3 H)).map (InternalSec.secMk
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) with hW
  have hHU : H ≤ Subgroup.normalizer ((conjClosure S.V3 H) : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  set ρ := A6Mod.secAct hHU hHC with hρ
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hV' : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hV : ∀ v : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)), v ^ 2 = 1 :=
    Bridge.sec_sq_eq_one hV' _ _
  have hKq : CFSG.IsQuasisimple ↥Kp := B1Red.isQuasisimple_of_open hKcomp.2.2
  have hKB : ⁅Kp, B⁆ = Kp := FFJImage.commutator_eq_of_not_le_centralizer hKq hBN hBnot
  have hKX : Kp ≤ X := hKcomp.1
  have hrange : ρ.range = X := S.range_secAct_plus
  have hconj : ∀ (F : Subgroup G), F ≤ H → ∀ h : ↥H,
      autSec (autOn (F.map (MulAut.conj (h : G)).toMonoidHom) (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) =
        (autSec (autOn F (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))).map
            (MulAut.conj (ρ h)).toMonoidHom :=
    fun F hF h => A6Mod.autSec_map_conj hHU hHC hF h
  obtain ⟨hc3N, t, htT, hT⟩ := S.orbit_cComp hH hKc
  have htH : t ∈ H := hTH htT
  obtain ⟨c₁, hc₁H, hc₁3, hcV3, hcfix⟩ := C.exists_c1_mem hNS h13315 h1356two hH hab hhat h13314
  have hcK : ρ ⟨c₁, hc₁H⟩ ∈ Subgroup.normalizer (Kp : Set (MulAut (Sec (⊤ : Subgroup
      ↥(conjClosure S.V3 H)) ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
        (conjClosure S.V3 H))))) := by
    refine B19.mem_normalizer_of_map_conj_eq ?_
    rw [hKp, ← hconj K hKH ⟨c₁, hc₁H⟩]
    show autSec (autOn (K.map (MulAut.conj c₁).toMonoidHom) (conjClosure S.V3 H)) ⊤ _ = _
    rw [B19.map_conj_eq_of_mem_normalizer (hc3N c₁ hc₁H hc₁3)]
  have hAH := C.A_le_H hNS h13315 h1356two hH hab hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hUH : (conjClosure S.V3 H) ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hmono : commV B ≤ commV (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
    unfold commV
    refine Subgroup.closure_mono fun w hw => ?_
    obtain ⟨x, hx, v, hv⟩ := hw
    exact ⟨x, hBA hx, v, hv⟩
  have hBW : commV B ≤ W := hmono.trans (C.commV_A_plus_le hUH hAH fun u hu a ha =>
    C.comm_UH_A_mem hNS h13315 h1356two hH hab hhat hna h13314 hu ha)
  have hne := FFJImage.commSub_commV_ne_bot hKq hKB
  have hMW : commV Kp ⊓ W ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff, ← hbot]
    exact le_inf (commSub_le_of_invariant fun b hb u hu =>
        FFJImage.apply_mem_commV (hBN hb) hu)
      ((commSub_mono le_top le_rfl).trans (by rw [← commV_eq_commSub]; exact hBW))
  have hWK : W ≤ commV Kp := FFJImage.le_of_fpf (S.card_V3_plus hNS h13315 h1356two hH h13314)
    (fun w hw => S.secAct_mem_V3_plus hc₁H hcV3 hw) (hcfix)
    (fun m hm => FFJImage.apply_mem_commV hcK hm) hMW
  set K₁ := K.map (MulAut.conj t).toMonoidHom with hK₁
  set Kp₁ := autSec (autOn K₁ (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hKp₁
  have hK₁H : K₁ ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    exact H.mul_mem (H.mul_mem htH (hKH hk)) (H.inv_mem htH)
  have hKp₁e : Kp₁ = Kp.map (MulAut.conj (ρ ⟨t, htH⟩)).toMonoidHom := hconj K hKH ⟨t, htH⟩
  have htV3 : t ∈ Subgroup.normalizer (S.V3 : Set G) := S.T_le_normalizer_V3 htT
  have htV3' : t⁻¹ ∈ Subgroup.normalizer (S.V3 : Set G) := Subgroup.inv_mem _ htV3
  have hWK₁ : W ≤ commV Kp₁ := by
    rw [hKp₁e, B19.commV_map_conj]
    intro w hw
    have hw' : ρ ⟨t⁻¹, H.inv_mem htH⟩ w ∈ W := S.secAct_mem_V3_plus (H.inv_mem htH) htV3' hw
    refine ⟨ρ ⟨t⁻¹, H.inv_mem htH⟩ w, hWK hw', ?_⟩
    show ρ ⟨t, htH⟩ (ρ ⟨t⁻¹, H.inv_mem htH⟩ w) = w
    rw [← MulAut.mul_apply, ← map_mul]
    have e : (⟨t, htH⟩ * ⟨t⁻¹, H.inv_mem htH⟩ : ↥H) = 1 := Subtype.ext (mul_inv_cancel t)
    rw [e, map_one, MulAut.one_apply]
  have hperm : ∀ h : ↥H, Kp.map (MulAut.conj (ρ h)).toMonoidHom = Kp ∨
      Kp.map (MulAut.conj (ρ h)).toMonoidHom = Kp₁ := by
    intro h
    rw [hKp, ← hconj K hKH h, hKp₁]
    rcases hT h h.2 with e | e
    · left; rw [e]
    · right; rw [e]
  have hperm₁ : ∀ h : ↥H, Kp₁.map (MulAut.conj (ρ h)).toMonoidHom = Kp ∨
      Kp₁.map (MulAut.conj (ρ h)).toMonoidHom = Kp₁ := by
    intro h
    rw [hKp₁, ← hconj K₁ hK₁H h, hK₁, A6Fifteen.map_conj_map_conj, hKp]
    rcases hT _ (H.mul_mem h.2 htH) with e | e
    · left; rw [e]
    · right; rw [e]
  have hsup : commV Kp ⊔ commV Kp₁ = ⊤ := by
    rw [← B19.commV_sup]
    apply S.eq_top_of_conj_V3
    intro h w hw
    have hle : (Kp ⊔ Kp₁).map (MulAut.conj (ρ h)).toMonoidHom ≤ Kp ⊔ Kp₁ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rcases hperm h with e | e <;> rw [e]
        · exact le_sup_left
        · exact le_sup_right
      · rcases hperm₁ h with e | e <;> rw [e]
        · exact le_sup_left
        · exact le_sup_right
    have h1 : ρ h w ∈ commV ((Kp ⊔ Kp₁).map (MulAut.conj (ρ h)).toMonoidHom) := by
      rw [B19.commV_map_conj]
      exact ⟨w, B19.commV_mono le_sup_left (hWK hw), rfl⟩
    exact B19.commV_mono hle h1
  set J := ffJ X with hJ
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple
    S.h13.nonabelian hH.1.2
  have hO2 := S.pCoreOf_plus_eq_bot hNS h13315 h1356two hH hab hNU hhat hLem
  have hb53 : B53Hyp J := by
    rw [hJ, ← hrange]
    exact FFJImage.b53Hyp_ffJ_range hSQ ρ (by rw [hrange]; exact hO2)
  have hBJ : B ≤ J := B6.le_ffJ hB.1
  have hJne : J ≠ ⊥ := fun h => hB.1.2.1 (le_bot_iff.1 (h ▸ hBJ))
  have hcases := h56 _ hV J hJne hb53
  have hKJ : Kp ≤ J := B1Red.K_le_ffJ hKX hB.1 hKB
  have hJN : J ≤ Subgroup.normalizer (Kp : Set (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))) :=
    iSup₂_le fun A hA => B15P4.asB15Part4 _ hV _ A hA Kp hKcomp
  have hρtX : ρ ⟨t, htH⟩ ∈ X := hrange ▸ ⟨_, rfl⟩
  have hK₁J : Kp₁ ≤ J := by
    rw [hKp₁e]
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hρtX) k).mp (hKJ hk)
  have hJN₁ : ∀ x ∈ J, ∀ k ∈ Kp₁, x * k * x⁻¹ ∈ Kp₁ := by
    intro x hx k hk
    rw [hKp₁e] at hk ⊢
    obtain ⟨k', hk', rfl⟩ := hk
    set g := ρ ⟨t, htH⟩ with hg
    have hy : g⁻¹ * x * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X (X.inv_mem hρtX)) x).mp hx
      simpa [mul_assoc] using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hJN hy) k').mp hk'
    refine ⟨g⁻¹ * x * g * k' * (g⁻¹ * x * g)⁻¹, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hK₁q : CFSG.IsQuasisimple ↥Kp₁ := by
    rw [hKp₁e]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Kp.equivMapOfInjective _ (MulAut.conj (ρ ⟨t, htH⟩)).injective) hKq
  rcases FFJImage.b56Cases_two hKJ hK₁J (fun x hx k hk => (Subgroup.mem_normalizer_iff.mp
      (hJN hx) k).mp hk) hJN₁ hKq hK₁q hsup hcases with ⟨hFJ, heq⟩ | hfix
  · refine ⟨?_, ?_, hFJ⟩
    · intro ψ hψ
      rw [← hrange] at hψ
      obtain ⟨h, rfl⟩ := hψ
      refine B19.mem_normalizer_of_map_conj_eq ?_
      rcases hperm h with e | e
      · exact e
      · rw [e, heq]
    · rw [← hsup, heq, sup_idem]
  · exfalso
    refine FFJImage.not_commV_le_fixV hKq hKB (hBW.trans ?_)
    refine (le_inf hWK hWK₁).trans (hfix.trans ?_)
    intro v hv k hk
    exact hv k (hKJ hk)


theorem exists_K_b51
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hLem : Lem1374One) (h56 : AsB56) (h51 : AsB51)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
      B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
      ∃ K ∈ cComp H, CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
          (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
        B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ≤
          Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
              Subgroup _) : Set _) ∧
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊤ ∧
        quasithinGenFitting (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) =
          autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
        (B51Case1i (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
            (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∨
          (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
              ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) =
            autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
            ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
              DirectSumOfCopies (autSec (autOn K (conjClosure S.V3 H)) ⊤
                ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
                (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
                  ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
                    (conjClosure S.V3 H)))) ⊥
                (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) 1)) := by
  obtain ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ⟩ :=
    C.exists_K_normal hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem h56
  refine ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, ?_⟩
  have hHU : H ≤ Subgroup.normalizer ((conjClosure S.V3 H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  set ρ := A6Mod.secAct hHU hHC with hρ
  set X := autSec (autOn H (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hX
  set Kp := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hKp
  set W := (S.V3.subgroupOf (conjClosure S.V3 H)).map (InternalSec.secMk
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) with hW
  set J := ffJ X with hJ
  have hV' : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hV := Bridge.sec_sq_eq_one hV' (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
  have hrange : ρ.range = X := S.range_secAct_plus
  have hKq : CFSG.IsQuasisimple ↥Kp := B1Red.isQuasisimple_of_open hKcomp.2.2
  have hKB : ⁅Kp, B⁆ = Kp := FFJImage.commutator_eq_of_not_le_centralizer hKq hBN hBnot
  have hKX : Kp ≤ X := hKcomp.1
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple
    S.h13.nonabelian hH.1.2
  have hSQX : SQTKGroup ↥X := by
    have h1 := InternalSec.sqtkGroup_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      (by
        rw [MonoidHom.ker_rangeRestrict, S.ker_secAct_plus hNS h13315 h1356two hH hab hNU hhat
          hLem]
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)) hSQ
    exact hrange ▸ h1
  have hSQK : SQTKGroup ↥Kp :=
    A6Fifteen.sqtkGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX)
      (InternalSec.sqtkGroup_subgroup hSQX (Kp.subgroupOf X))
  have hO2 := S.pCoreOf_plus_eq_bot hNS h13315 h1356two hH hab hNU hhat hLem
  have hb53 : B53Hyp J := by
    rw [hJ, ← hrange]
    exact FFJImage.b53Hyp_ffJ_range hSQ ρ (by rw [hrange]; exact hO2)
  have hKJ : Kp ≤ J := B1Red.K_le_ffJ hKX hB.1 hKB
  have hZ : centerOf J ≤ Kp := hFJ ▸ InternalSec.centerOf_le_quasithinGenFitting J
  have hb51 : B51Hyp J Kp :=
    ⟨by rw [hFJ, sup_eq_left.2 hZ], hKq, hSQK, hKJ, hb53.1, hb53.2.1⟩
  obtain ⟨⟨-, hcases⟩, -⟩ := h51 _ hV J Kp hb51
  have hAH := C.A_le_H hNS h13315 h1356two hH hab hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hmono : commV B ≤ commV (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
    unfold commV
    refine Subgroup.closure_mono fun w hw => ?_
    obtain ⟨x, hx, v, hv⟩ := hw
    exact ⟨x, hBA hx, v, hv⟩
  have hBW : commV B ≤ W := hmono.trans (C.commV_A_plus_le hUH hAH fun u hu a ha =>
    C.comm_UH_A_mem hNS h13315 h1356two hH hab hhat hna h13314 hu ha)
  have hB4 : Nat.card (commV B) ≤ 4 :=
    (Subgroup.card_le_of_le hBW).trans (S.card_V3_plus hNS h13315 h1356two hH h13314).le
  have hBJ : IsFFStarOffender J B :=
    ⟨B6.le_ffJ hB.1, hB.1.2.1, hB.1.2.2.1, hB.1.2.2.2⟩
  rcases hcases with h1 | h2 | ⟨n, h3⟩ | h4
  · exact Or.inl h1
  · exact absurd hB4 (not_le.2 (B51Sum.four_lt_card_commV_of_case1ii h2 hBJ))
  · exact absurd hB4 (not_le.2 (B51Sum.four_lt_card_commV_of_case1iii h3 hBJ))
  · exact Or.inr ⟨h4.1, B51Sum.copies_eq_one_of_case1iv h4 hBJ hB4⟩

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
