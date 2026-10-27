module

public import CFSG.Quasithin.H13.A6S13826l
public import CFSG.Quasithin.H13.A6S13825v
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.Background.C124BlkAlt

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

namespace A6Gen

theorem toAdd_coreEvenEquiv_permAct (σ : Perm (Fin 6)) (m : ↥(G6.coreMod 6))
    (hm : G6.permAct 6 σ (m : G6.PermMod 6) ∈ G6.coreMod 6) :
    Multiplicative.toAdd (C124.coreEvenEquiv 6 ⟨G6.permAct 6 σ (m : G6.PermMod 6), hm⟩) =
      permWeight 6 σ (Multiplicative.toAdd (C124.coreEvenEquiv 6 m)) :=
  Subtype.ext (funext fun _ => rfl)

end A6Gen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace D826

variable {H K : Subgroup G} (hd : S.D826 H K)
include hd

theorem sigmaH_secMk [IsMulCommutative ↥(conjClosure S.V3 H)] (k : ↥K)
    (u v : ↥(conjClosure S.V3 H)) (huv : (v : G) = k * u * k⁻¹) :
    L13825.sigmaH hd.hH ⟨(k : G), hd.hKH k.2⟩
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) v := by
  rw [A6Mod.secAct_secMk]
  congr 1
  apply Subtype.ext
  rw [Setup.rho_apply_coe, huv]
  rfl

theorem exists_heart [IsMulCommutative ↥(conjClosure S.V3 H)]
    {α : ↥K →* alternatingGroup (Fin 6)}
    {π : alternatingGroup (Fin 6) →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hπα : ∀ k : ↥K, ((π (α k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :
        MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) =
      L13825.sigmaH hd.hH ⟨(k : G), hd.hKH k.2⟩)
    (hreal : (FFModel.altDn 6).RealizesVia (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ π) :
    ∃ β : ↥(conjClosure S.V3 H) →* Multiplicative (AltHeart 6),
      Function.Surjective β ∧
      (∀ u : ↥(conjClosure S.V3 H), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
      ∀ (k : ↥K) (u v : ↥(conjClosure S.V3 H)), (v : G) = k * u * k⁻¹ →
        ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) =
          Multiplicative.toAdd (β u) →
          (QuotientAddGroup.mk (permWeight 6 (α k : Perm (Fin 6)) x) : AltHeart 6) =
            Multiplicative.toAdd (β v) := by
  obtain ⟨-, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := hreal
  let sU : ↥(conjClosure S.V3 H) →* ↥(⊤ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
    Subgroup.topEquiv.symm.toMonoidHom.comp
      (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
  have hsU : ∀ u : ↥(conjClosure S.V3 H), ((sU u : ↥(⊤ : Subgroup _)) :
      Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) _) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u := fun _ => rfl
  let e := C124.altQuotEquiv 6 (by norm_num)
  refine ⟨e.toMonoidHom.comp (β₀.comp sU), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨⟨x, hx'⟩, hx⟩ := hβs q
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) x
    refine ⟨u, ?_⟩
    show e (β₀ (sU u)) = e q
    rw [← hx]
    rfl
  · intro u
    have h1 : (e.toMonoidHom.comp (β₀.comp sU)) u = 1 ↔ β₀ (sU u) = 1 := e.map_eq_one_iff
    rw [h1, hβk, Subgroup.mem_bot, hsU]
    exact A6Mod.secMk_eq_one_iff u
  · intro k u v huv x hx
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ (sU u))
    have hpm : (FFModel.altDn 6).act (α k) (m : (FFModel.altDn 6).Amb) ∈
        (FFModel.altDn 6).sec := G6.permAct_mem_coreMod _ m.2
    have h1 := hβe (α k) (sU u) m trivial hpm hm.symm
    have hv : (⟨((π (α k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
          ((sU u : ↥(⊤ : Subgroup _)) : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) _), trivial⟩ :
          ↥(⊤ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = sU v := by
      apply Subtype.ext
      rw [hsU, hsU, hπα]
      exact hd.sigmaH_secMk k u v huv
    have h2 : β₀ (sU v) = QuotientGroup.mk
        ⟨(FFModel.altDn 6).act (α k) (m : (FFModel.altDn 6).Amb), hpm⟩ := by
      rw [← hv]
      exact h1
    have hβv : Multiplicative.toAdd (e (β₀ (sU v))) = (QuotientAddGroup.mk
        (permWeight 6 (α k : Perm (Fin 6)) (Multiplicative.toAdd (C124.coreEvenEquiv 6 m))) :
          AltHeart 6) := by
      rw [h2]
      exact congrArg (QuotientAddGroup.mk (s := constWeight 6))
        (A6Gen.toAdd_coreEvenEquiv_permAct _ m hpm)
    have hβu : Multiplicative.toAdd (e (β₀ (sU u))) = (QuotientAddGroup.mk
        (Multiplicative.toAdd (C124.coreEvenEquiv 6 m)) : AltHeart 6) := by
      rw [← hm]
      rfl
    show _ = Multiplicative.toAdd (e (β₀ (sU v)))
    rw [hβv]
    have hx' : (QuotientAddGroup.mk x : AltHeart 6) =
        QuotientAddGroup.mk (Multiplicative.toAdd (C124.coreEvenEquiv 6 m)) := hx.trans hβu
    rw [QuotientAddGroup.eq] at hx' ⊢
    exact C124.permWeight_sub_mem _ hx'

theorem exists_even [IsMulCommutative ↥(conjClosure S.V3 H)]
    {α₀ : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α₀)
    (hαk : ∀ k : ↥K, α₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {π : alternatingGroup (Fin 6) →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hreal : (altCoreModel 6).RealizesVia (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ π) :
    ∃ α : ↥K →* alternatingGroup (Fin 6), Function.Surjective α ∧
      (∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) ∧
      ∃ β : ↥(conjClosure S.V3 H) →* Multiplicative ↥(evenWeight 6),
        Function.Surjective β ∧
        (∀ u : ↥(conjClosure S.V3 H), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
        ∀ (k : ↥K) (u v : ↥(conjClosure S.V3 H)), (v : G) = k * u * k⁻¹ →
          Multiplicative.toAdd (β v) =
            permWeight 6 (α k : Perm (Fin 6)) (Multiplicative.toAdd (β u)) := by
  obtain ⟨hπs, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := hreal
  have hF1 := hd.hF.toHypF91
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH) hαs hαk
  obtain ⟨ι⟩ := (hsV.ctx hαs hαk).iso
  have hπi : Function.Injective π :=
    (Finite.injective_iff_surjective_of_equiv ι.symm.toEquiv).2 hπs
  let e₂ : alternatingGroup (Fin 6) ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let rV : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    (hsV.act.comp (Subgroup.inclusion hd.hKH)).codRestrict _ fun k =>
      (hsV.mem_autSec_iff hd.hKH).2 ⟨_, k.2, rfl⟩
  have hrVs : Function.Surjective rV := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hf, rfl⟩ := (hsV.mem_autSec_iff hd.hKH).1 hψ
    exact ⟨⟨f, hf⟩, rfl⟩
  have hrVk : ∀ k : ↥K, rV k = 1 ↔ (k : G) ∈ pCoreOf 2 H := fun k => by
    rw [← Subtype.coe_inj]
    exact hsV.act_eq_one_iff _
  let α : ↥K →* alternatingGroup (Fin 6) := e₂.symm.toMonoidHom.comp rV
  have hπα : ∀ k : ↥K, π (α k) = rV k := fun k => e₂.apply_symm_apply (rV k)
  refine ⟨α, e₂.symm.surjective.comp hrVs, fun k => ?_, ?_⟩
  · rw [← hrVk]
    exact e₂.symm.map_eq_one_iff
  let sU : ↥(conjClosure S.V3 H) →* ↥(⊤ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
    Subgroup.topEquiv.symm.toMonoidHom.comp
      (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
  have hsU : ∀ u : ↥(conjClosure S.V3 H), ((sU u : ↥(⊤ : Subgroup _)) :
      Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) _) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u := fun _ => rfl
  let q := C124.quotBotEquiv (altCoreModel 6).sec (altCoreModel 6).ker rfl
  refine ⟨(C124.coreEvenEquiv 6).toMonoidHom.comp (q.toMonoidHom.comp (β₀.comp sU)), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨m, rfl⟩ := (C124.coreEvenEquiv 6).surjective y
    obtain ⟨w, hw⟩ := q.surjective m
    obtain ⟨⟨x, hx'⟩, hx⟩ := hβs w
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) x
    refine ⟨u, ?_⟩
    show C124.coreEvenEquiv 6 (q (β₀ (sU u))) = C124.coreEvenEquiv 6 m
    rw [← hw, ← hx]
    rfl
  · intro u
    have h1 : ((C124.coreEvenEquiv 6).toMonoidHom.comp (q.toMonoidHom.comp (β₀.comp sU))) u = 1 ↔
        β₀ (sU u) = 1 :=
      (C124.coreEvenEquiv 6).map_eq_one_iff.trans q.map_eq_one_iff
    rw [h1, hβk, Subgroup.mem_bot, hsU]
    exact A6Mod.secMk_eq_one_iff u
  · intro k u v huv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ (sU u))
    have hpm : (altCoreModel 6).act (α k) (m : (altCoreModel 6).Amb) ∈ (altCoreModel 6).sec :=
      G6.permAct_mem_coreMod _ m.2
    have h1 := hβe (α k) (sU u) m trivial hpm hm.symm
    have hv : (⟨((π (α k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
          ((sU u : ↥(⊤ : Subgroup _)) : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) _), trivial⟩ :
          ↥(⊤ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = sU v := by
      apply Subtype.ext
      rw [hsU, hsU, hπα]
      exact hd.sigmaH_secMk k u v huv
    have h2 : β₀ (sU v) = QuotientGroup.mk
        ⟨(altCoreModel 6).act (α k) (m : (altCoreModel 6).Amb), hpm⟩ := by
      rw [← hv]
      exact h1
    show Multiplicative.toAdd (C124.coreEvenEquiv 6 (q (β₀ (sU v)))) =
      permWeight 6 _ (Multiplicative.toAdd (C124.coreEvenEquiv 6 (q (β₀ (sU u)))))
    rw [h2, ← hm]
    exact A6Gen.toAdd_coreEvenEquiv_permAct _ m hpm

end D826

end Setting4

theorem lem13826_of
    (h1376 : Lem1376Full) (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) : Lem13826 := by
  intro G _ _ T L V S hS H hH K hK h6
  obtain ⟨hL1K, -, ⟨hKT, -⟩, hUK⟩ := h21 G T L V S hS H hH K hK
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hd : S.D826 H K := ⟨hS, hH, hK, hKn, hKT.symm, hL1K, hUK, h6⟩
  have hab := L13825.isElemAbelian_UH hS hH
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hab.1
  obtain ⟨α, hαs, hαk⟩ := S.exists_alpha hS hH hd.hKH h6
  obtain ⟨W, hV1W, hWU, hHW, hmax⟩ := hd.exists_max
  have hW : ∀ u ∈ conjClosure S.V3 H, u ∈ W ↔ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V :=
    fun u hu => hd.mem_max_iff h21 h16 h36 h139 h1334 h13 h13314 h13315 h1356two hαs hαk hV1W
      hWU hHW hmax hu
  have h16W := hd.relIndex_max hαs hαk hV1W hWU hHW hmax
  obtain ⟨α', π, hα's, hα'k, hπα, hreal⟩ :=
    hd.exists_realizesVia_alt hαs hαk hV1W hWU hHW hmax hW h16W
  have hcomm : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ := by
    rw [L13825.autSec_eq_map hH hd.hKH]
    exact L13825.commV_eq_top_of_commutator hH hd.hKH hUK
  have hAN : AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 6 := ⟨π, hreal⟩
  obtain ⟨-, -, h3, -⟩ := h1376 G T L V S hS.hNS hS.hNU H hH hab K hK
  obtain ⟨-, -, -, hcases⟩ := h3 6 (by rw [hcomm, inf_top_eq]; exact hAN)
  have hcprop : ∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
      (∀ k ∈ K, k * (c * u * c⁻¹ * u⁻¹) * k⁻¹ * (c * u * c⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V) →
      ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    rcases hcases with ⟨-, -, hc, -⟩ | ⟨h7, -⟩
    · exact hc
    · exact absurd h7 (by norm_num)
  have hU2 : ∀ w : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)), w ^ 2 = 1 :=
    L13825.sec_sq_eq_one hab.2
  rcases VolI.altNaturalCoverSix_holds _ hU2 _ _ le_rfl hcomm hAN with hZ | ⟨-, -, π₂, hreal₂⟩
  · rw [hZ] at hreal
    obtain ⟨β, hβs, hβk, hβe⟩ := hd.exists_heart hπα hreal
    exact ⟨α', hα's, hα'k, hcprop, Or.inl ⟨β, hβs, hβk, hβe⟩⟩
  · obtain ⟨α₂, hα₂s, hα₂k, β, hβs, hβk, hβe⟩ := hd.exists_even hαs hαk hreal₂
    exact ⟨α₂, hα₂s, hα₂k, hcprop, Or.inr ⟨β, hβs, hβk, hβe⟩⟩

end CFSG.Quasithin.H13.A6
