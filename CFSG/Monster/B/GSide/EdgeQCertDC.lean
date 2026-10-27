module

public import CFSG.Monster.B.GSide.EdgeQCertOrbits
public import CFSG.Monster.B.GSide.EdgeQCertP2
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import CFSG.Monster.B.GSide.MuFourOmega
public import CFSG.Monster.B.GSide.EdgeQCertDCInputs
public import Certificates.Certificate3133
public import Certificates.Certificate3043
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate16042
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.Visible CFSG.Monster.VisQuot
open CFSG.Monster.B.Co2 (v0 decW)

@[expose] def edgeJ :
    cEdgeStab →* Jhat where
  toFun b := ⟨((b : Shat) : Dfull), mem_Jhat_of_mem_cEdgeStab b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def edgeRho :
    cEdgeStab →* Kstab v0 :=
    jhatToKv0.comp edgeJ

theorem edgeRho_eq_one_iff
    {b : cEdgeStab} : edgeRho b = 1
    ↔ b ∈ edgeQ := by
  show edgeJ b ∈ jhatToKv0.ker ↔ _
  rw [ker_jhatToKv0, Subgroup.mem_subgroupOf]
  rfl

theorem ker_edgeRho :
    edgeRho.ker = edgeQ := by
  ext b
  exact edgeRho_eq_one_iff

theorem psiW_conj_edge
    (b : cEdgeStab) {e : Dfull}
    (he : e ∈ Ehat) :
    psiW ⟨((b : Shat) : Dfull)⁻¹ * e * b, conj_mem_Ehat (mem_Jhat_of_mem_cEdgeStab b.2) he⟩ =
      wAct v0 (edgeRho b) (psiW ⟨e, he⟩) :=
  psiW_conj (mem_Jhat_of_mem_cEdgeStab b.2) he

theorem psiW_cQ_xhat :
    psiW ⟨cQ * xhat, Ehat.mul_mem cQ_mem_Ehat xhat_mem_Ehat⟩ =
    sigmaW := by
  have e : (⟨cQ * xhat, Ehat.mul_mem cQ_mem_Ehat xhat_mem_Ehat⟩ : Ehat) = cE * xhatE := rfl
  rw [e, psiW_mul, psiW_cE, psiW_xhatE, add_zero]

theorem edgeRho_mem_Usig
    (b : cEdgeStab) : edgeRho b ∈
    Usig := by
  rw [mem_Usig]
  have h := psiW_conj_edge b cQ_mem_Ehat
  rw [show psiW ⟨cQ, cQ_mem_Ehat⟩ = sigmaW from psiW_cE] at h
  rw [← h]
  rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 b.2 with ⟨h0, -⟩ | ⟨h0, -⟩
  · have e := clabel_cvMul cv0 (b : Shat)
    rw [h0, clabel_cv0] at e
    have e' : (⟨((b : Shat) : Dfull)⁻¹ * cQ * b, conj_mem_Ehat (mem_Jhat_of_mem_cEdgeStab b.2)
        cQ_mem_Ehat⟩ : Ehat) = cE := Subtype.ext e.symm
    rw [e', psiW_cE]
  · have e := clabel_cvMul cv0 (b : Shat)
    rw [h0, clabel_cv0, clabel_cw0] at e
    have e' : (⟨((b : Shat) : Dfull)⁻¹ * cQ * b, conj_mem_Ehat (mem_Jhat_of_mem_cEdgeStab b.2)
        cQ_mem_Ehat⟩ : Ehat) = ⟨cQ * xhat, Ehat.mul_mem cQ_mem_Ehat xhat_mem_Ehat⟩ :=
      Subtype.ext e.symm
    rw [e', psiW_cQ_xhat]

theorem edgeU0_mem_Ehat :
    (((cEdgeIncl edgeU0 : cEdgeStab) : Shat) : Dfull) ∈ Ehat := u0_mem_Ehat

theorem val_conj_inv
    (b x : cEdgeStab) :
    (((b⁻¹ * x * b⁻¹⁻¹ : cEdgeStab) : Shat) : Dfull) =
      ((b : Shat) : Dfull)⁻¹ * ((x : Shat) : Dfull) * ((b : Shat) : Dfull) := by
  rw [inv_inv]
  rfl

theorem conj_u0_cases
    {b : cEdgeStab} (hb : b ∈ edgeMB edgeU0) :
    ((b : Shat) : Dfull)⁻¹ * (cQ * yhat) * b = cQ * yhat ∨
      ((b : Shat) : Dfull)⁻¹ * (cQ * yhat) * b = cQ * yhat * xhat := by
  have hconj : b⁻¹ ∈ edgeMB edgeU0 := (edgeMB edgeU0).inv_mem hb
  rcases hconj with e | e
  · left
    have h := congrArg (fun y : cEdgeStab => ((y : Shat) : Dfull)) e
    rw [val_conj_inv] at h
    exact h
  · right
    have h := congrArg (fun y : cEdgeStab => ((y : Shat) : Dfull)) e
    rw [val_conj_inv, val_mul, coe_edgeXhat] at h
    exact h

theorem edgeRho_mem_UsigW
    {b : cEdgeStab} (hb : b ∈ edgeMB edgeU0) : edgeRho b ∈
    UsigW := by
  have hU := edgeRho_mem_Usig b
  refine Subgroup.mem_inf.2 ⟨hU, mem_wStab.2 ?_⟩
  have hu : psiW ⟨cQ * yhat, u0_mem_Ehat⟩ = sigmaW + wFr := psiW_edgeU0
  have h := psiW_conj_edge b u0_mem_Ehat
  rw [hu] at h
  have hpsi : wAct v0 (edgeRho b) (sigmaW + wFr) = sigmaW + wFr := by
    rw [← h]
    rcases conj_u0_cases hb with e | e
    · have e' : (⟨((b : Shat) : Dfull)⁻¹ * (cQ * yhat) * b, conj_mem_Ehat
          (mem_Jhat_of_mem_cEdgeStab b.2) u0_mem_Ehat⟩ : Ehat) = ⟨cQ * yhat, u0_mem_Ehat⟩ :=
        Subtype.ext e
      rw [e', hu]
    · have e' : (⟨((b : Shat) : Dfull)⁻¹ * (cQ * yhat) * b, conj_mem_Ehat
          (mem_Jhat_of_mem_cEdgeStab b.2) u0_mem_Ehat⟩ : Ehat) = ⟨cQ * yhat, u0_mem_Ehat⟩ *
          xhatE := Subtype.ext e
      rw [e', psiW_mul, psiW_xhatE, add_zero, hu]
  rw [map_add, show wAct v0 (edgeRho b) sigmaW = sigmaW from hU] at hpsi
  exact add_left_cancel hpsi

theorem mem_edgeMB_of_fix
    {b : cEdgeStab}
    (h : wAct v0 (edgeRho b⁻¹) (sigmaW + wFr) = sigmaW + wFr) : b ∈ edgeMB edgeU0 := by
  have hu : psiW ⟨cQ * yhat, u0_mem_Ehat⟩ = sigmaW + wFr := psiW_edgeU0
  have hc := psiW_conj_edge b⁻¹ u0_mem_Ehat
  have hval : (((b⁻¹ : cEdgeStab) : Shat) : Dfull)⁻¹ * (cQ * yhat) *
      (((b⁻¹ : cEdgeStab) : Shat) : Dfull) =
      (((b * cEdgeIncl edgeU0 * b⁻¹ : cEdgeStab) : Shat) : Dfull) := by
    show ((((b : Shat) : Dfull))⁻¹)⁻¹ * (cQ * yhat) * ((b : Shat) : Dfull)⁻¹ =
      ((b : Shat) : Dfull) * (cQ * yhat) * ((b : Shat) : Dfull)⁻¹
    rw [inv_inv]
  generalize hE : (⟨_, conj_mem_Ehat (mem_Jhat_of_mem_cEdgeStab (b⁻¹).2) u0_mem_Ehat⟩ : Ehat) =
    e₁ at hc
  have hpe : psiW e₁ = sigmaW + wFr := by rw [hc, hu, h]
  have h0 : psiW (⟨cQ * yhat, u0_mem_Ehat⟩⁻¹ * e₁) = 0 := by
    rw [psiW_mul, psiW_inv, hpe, hu, neg_add_cancel]
  have hv1 : (e₁ : Dfull) = (((b * cEdgeIncl edgeU0 * b⁻¹ : cEdgeStab) : Shat) : Dfull) := by
    rw [← hE]
    exact hval
  have hU0 : (((cEdgeIncl edgeU0 : cEdgeStab) : Shat) : Dfull) = cQ * yhat := rfl
  rcases (psiW_eq_zero_iff _).1 h0 with e | e
  · left
    apply cEdgeStab_val_injective
    have e2 : (e₁ : Dfull) = cQ * yhat := (congrArg Subtype.val (inv_mul_eq_one.1 e)).symm
    exact hv1.symm.trans (e2.trans hU0.symm)
  · right
    apply cEdgeStab_val_injective
    have e2 : (e₁ : Dfull) = cQ * yhat * xhat := congrArg Subtype.val (inv_mul_eq_iff_eq_mul.1 e)
    have e3 : (((cEdgeIncl edgeU0 * edgeXhat : cEdgeStab) : Shat) : Dfull) = cQ * yhat * xhat :=
      (val_mul (cEdgeIncl edgeU0) edgeXhat).trans (by rw [hU0, coe_edgeXhat])
    exact hv1.symm.trans (e2.trans e3.symm)

@[expose] def cEdgeOfP1
    (p : P1) : cEdgeStab :=
  cEdgeIncl ⟨⟨p, Jhat_le_Shat (P1_le_Jhat p.2)⟩, mem_cEdgeFix_iff.2 p.2⟩

theorem edgeRho_cEdgeOfP1
    (p : P1) : edgeRho (cEdgeOfP1 p) = (p1Proj p : Kstab v0) := rfl

theorem exists_edgeRho_eq
    {k : Kstab v0} (hk : k ∈ UsigW) :
    ∃ b ∈ edgeMB edgeU0, edgeRho b = k := by
  obtain ⟨p, hp⟩ := p1Proj_surjective ⟨k, (Subgroup.mem_inf.1 hk).1⟩
  have hrho : edgeRho (cEdgeOfP1 p) = k := by rw [edgeRho_cEdgeOfP1, hp]
  refine ⟨cEdgeOfP1 p, mem_edgeMB_of_fix ?_, hrho⟩
  have hkinv : k⁻¹ ∈ UsigW := UsigW.inv_mem hk
  rw [map_inv, hrho, map_add, show wAct v0 k⁻¹ sigmaW = sigmaW from (Subgroup.mem_inf.1 hkinv).1,
    show wAct v0 k⁻¹ wFr = wFr from mem_wStab.1 (Subgroup.mem_inf.1 hkinv).2]

theorem UsigWEquiv_inl_signMask
    (i : Fin 10) :
    (UsigWEquiv (SemidirectProduct.inl (nOf (signMask i) (signMask_mem i))) : Kstab v0) =
      genK ⟨6 + i, by omega⟩ := by
  apply Subtype.ext
  rw [coe_UsigWEquiv]
  show monoD c012Hyp ⟨_, 1⟩ = n6Elt ⟨6 + i, by omega⟩
  rw [nOf, monoD_mk, n6Elt_sign, OneMemClass.coe_one, inv_one, VisQuot.PO_one, mul_one]
  congr 2
  apply Subtype.ext
  show bvec 24 (signMask i) = (wordSignCode n6WordArr[(i : ℕ)]! : Fin 24 → ZMod 2)
  rw [← signVec_eq]
  rfl

theorem card_eq_card_ker_mul_card_map {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (K : Subgroup G) : Nat.card K = Nat.card (f.ker.subgroupOf K) * Nat.card (K.map f) := by
  have h1 := Subgroup.card_mul_index (f.comp K.subtype).ker
  rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.comap_ker]
    at h1
  exact h1.symm

theorem comm_mem_of_normal {G : Type*} [Group G] {K M : Subgroup G}
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) {k q : G} (hk : k ∈ K) (hq : q ∈ M) :
    k⁻¹ * q * k * q⁻¹ ∈ K := by
  have h := K.mul_mem (K.inv_mem hk) (hKn q hq k hk)
  have e : k⁻¹ * (q * k * q⁻¹) = k⁻¹ * q * k * q⁻¹ := by group
  rw [e] at h
  exact h

theorem comm_mem_of_normal' {G : Type*} [Group G] {Q : Subgroup G} (hQ : Q.Normal) (k : G) {q : G}
    (hq : q ∈ Q) : k⁻¹ * q * k * q⁻¹ ∈ Q := by
  have h := hQ.conj_mem q hq k⁻¹
  rw [inv_inv] at h
  exact Q.mul_mem h (Q.inv_mem hq)

theorem exists_comm_mem
    {K : Subgroup cEdgeStab}
    (hKn : ∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) {k : cEdgeStab} (hk : k ∈ K)
    (q : Ehat) : ∃ c : cEdgeStab, c ∈ K ∧ ∃ hc : c ∈ edgeQ,
      psiW ⟨((c : Shat) : Dfull), hc⟩ = wAct v0 (edgeRho k) (psiW q) + psiW q := by
  have hq'Q : edgeQOf q.2 ∈ edgeQ := edgeQOf_mem q.2
  have hq'M : edgeQOf q.2 ∈ edgeMB edgeU0 := edgeQ_le_edgeMB edgeU0_mem_edgeL hq'Q
  have hcQ := comm_mem_of_normal' edgeQ_normal k hq'Q
  refine ⟨_, comm_mem_of_normal hKn hk hq'M, hcQ, ?_⟩
  have hc := psiW_conj_edge k q.2
  have e : (⟨((((k⁻¹ * edgeQOf q.2 * k * (edgeQOf q.2)⁻¹ : cEdgeStab)) : Shat) : Dfull),
      hcQ⟩ : Ehat) =
      ⟨((k : Shat) : Dfull)⁻¹ * q * k, conj_mem_Ehat (mem_Jhat_of_mem_cEdgeStab k.2) q.2⟩ *
        q⁻¹ := rfl
  rw [e, psiW_mul, psiW_inv, ZModModule.neg_eq_self, hc]

theorem commChecks :
    ∀ i l : Fin 15, bWcode (commCode i) (commY l) = if i = l then 1 else 0 :=
  Certificates.certificate3133

theorem commK_range : ∀ i : Fin 15, 6 ≤ commK i ∧ commK i < 16 := by decide

@[expose] def commVec (i : Fin 15) : Wv v0 := decW (commCode i)

theorem linearIndependent_commVec : LinearIndependent (ZMod 2)
    commVec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h := congrArg (fun x => bV x (decW (commY l))) hg
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply, commVec, bV_decW, commChecks, smul_eq_mul] at h
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

theorem map_edgeRho_le
    {K : Subgroup cEdgeStab} (hKM : K ≤ edgeMB edgeU0) :
    K.map edgeRho ≤ UsigW := by
  rintro _ ⟨k, hk, rfl⟩
  exact edgeRho_mem_UsigW (hKM hk)

theorem map_edgeRho_conj
    {K : Subgroup cEdgeStab}
    (hKn : ∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) {m : Kstab v0} (hm : m ∈ UsigW)
    {x : Kstab v0} (hx : x ∈ K.map edgeRho) : m * x * m⁻¹ ∈ K.map edgeRho := by
  obtain ⟨b, hb, rfl⟩ := exists_edgeRho_eq hm
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨b * k * b⁻¹, hKn b hb k hk, ?_⟩
  simp only [map_mul, map_inv]

@[expose] def sddOf
    (Kb : Subgroup (Kstab v0)) : Subgroup (SDD c012Hyp) :=
  Kb.comap (UsigW.subtype.comp UsigWEquiv.toMonoidHom)

theorem mem_sddOf
    {Kb : Subgroup (Kstab v0)} {x : SDD c012Hyp} :
    x ∈ sddOf Kb ↔ ((UsigWEquiv x : UsigW) : Kstab v0) ∈ Kb := Iff.rfl

theorem sddOf_normal
    {Kb : Subgroup (Kstab v0)}
    (h : ∀ m ∈ UsigW, ∀ x ∈ Kb, m * x * m⁻¹ ∈ Kb) : (sddOf Kb).Normal where
  conj_mem x hx y := by
    rw [mem_sddOf, map_mul, map_mul, map_inv]
    exact h _ (UsigWEquiv y).2 _ hx

theorem isPGroup_sddOf
    {Kb : Subgroup (Kstab v0)} (h2 : IsPGroup 2 Kb) :
    IsPGroup 2 (sddOf Kb) :=
  h2.comap_of_injective _ (UsigW.subtype_injective.comp UsigWEquiv.injective)

theorem eq_bot_of_sddOf
    {Kb : Subgroup (Kstab v0)} (hle : Kb ≤ UsigW) (h : sddOf Kb = ⊥)
    :
    Kb = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall Kb).2 fun y hy => ?_
  have hx : UsigWEquiv.symm ⟨y, hle hy⟩ ∈ sddOf Kb := by
    rw [mem_sddOf, MulEquiv.apply_symm_apply]
    exact hy
  rw [h, Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at hx
  exact congrArg Subtype.val hx

theorem le_range_inl {X : Subgroup (SDD c012Hyp)} (hn : X.Normal) (h2 : IsPGroup 2 X) :
    X ≤ SemidirectProduct.inl.range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, ← Subgroup.map_eq_bot_iff]
  exact P2_normal_isPGroup_eq_bot (hn.map _ SemidirectProduct.rightHom_surjective) (h2.map _)

theorem comap_inl_invariant {X : Subgroup (SDD c012Hyp)} (hn : X.Normal) (p : P2) (n : NQ)
    (h : n ∈ X.comap SemidirectProduct.inl) :
    permActD c012Hyp p n ∈ X.comap SemidirectProduct.inl := by
  have h' := hn.conj_mem _ (Subgroup.mem_comap.1 h) (SemidirectProduct.inr p)
  have e : (SemidirectProduct.inl (permActD c012Hyp p n) : SDD c012Hyp) =
      SemidirectProduct.inr p * SemidirectProduct.inl n * (SemidirectProduct.inr p)⁻¹ :=
    (SemidirectProduct.inl_aut p n).trans (congrArg
      (fun z => SemidirectProduct.inr p * SemidirectProduct.inl n * z)
      (map_inv SemidirectProduct.inr p))
  show SemidirectProduct.inl (permActD c012Hyp p n) ∈ X
  rw [e]
  exact h'

theorem eq_bot_of_comap_inl {X : Subgroup (SDD c012Hyp)} (hle : X ≤ SemidirectProduct.inl.range)
    (h : X.comap SemidirectProduct.inl = ⊥) : X = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall X).2 fun x hx => ?_
  obtain ⟨n, rfl⟩ := hle hx
  have hn : n ∈ X.comap SemidirectProduct.inl := hx
  rw [h, Subgroup.mem_bot] at hn
  rw [hn, map_one]

@[expose] def psiKQ
    (K : Subgroup cEdgeStab)
    (x : edgeQ.subgroupOf K) : Wv v0 :=
  psiW ⟨((((x : K) : cEdgeStab) : Shat) : Dfull), x.2⟩

theorem psiKQ_one
    (K : Subgroup cEdgeStab) : psiKQ
    K 1 = 0 := psiW_one

theorem psiKQ_mul
    (K : Subgroup cEdgeStab)
    (x y : edgeQ.subgroupOf K) :
    psiKQ K (x * y) = psiKQ K x + psiKQ K y :=
  psiW_mul ⟨((((x : K) : cEdgeStab) : Shat) : Dfull), x.2⟩
    ⟨((((y : K) : cEdgeStab) : Shat) : Dfull), y.2⟩

theorem commVec_mem
    {K : Subgroup cEdgeStab}
    (hKn : ∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hgen : ∀ i : Fin 10, genK ⟨6 + i, by omega⟩ ∈ K.map edgeRho) (i : Fin 15) :
    commVec i ∈ Set.range (psiKQ K) := by
  have hr := commK_range i
  have hi : commK i - 6 < 10 := by omega
  have hg := hgen ⟨commK i - 6, hi⟩
  obtain ⟨k, hk, hke⟩ := hg
  obtain ⟨q, hq⟩ := psiW_surjective (decW (2 ^ commJ i))
  have hcm := exists_comm_mem hKn hk q
  obtain ⟨c, hcK, hcm'⟩ := hcm
  obtain ⟨hc, hpsi⟩ := hcm'
  have e : genRows ⟨6 + (commK i - 6), by omega⟩ = n6RowArr[commK i]! := by
    show n6RowArr[6 + (commK i - 6)]! = n6RowArr[commK i]!
    rw [show 6 + (commK i - 6) = commK i by omega]
  refine ⟨⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 hc⟩, ?_⟩
  show psiW ⟨((c : Shat) : Dfull), hc⟩ = commVec i
  rw [hpsi, hke, hq, wAct_genK_decW, e, ← Co2.decW_xor]
  rfl

theorem span_commVec_subset
    {K : Subgroup cEdgeStab}
    (hKn : ∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hgen : ∀ i : Fin 10, genK ⟨6 + i, by omega⟩ ∈ K.map edgeRho) {v : Wv v0}
    (hv : v ∈ Submodule.span (ZMod 2) (Set.range commVec)) : v ∈ Set.range (psiKQ K) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact commVec_mem hKn hgen i
  | zero => exact ⟨1, psiKQ_one K⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, psiKQ_mul K a b⟩
  | smul a x _ hx =>
    rcases Fischer.zmod2_cases a with rfl | rfl
    · exact ⟨1, (psiKQ_one K).trans (zero_smul _ x).symm⟩
    · rw [one_smul]
      exact hx

theorem natCard_span_commVec :
    Nat.card (Submodule.span (ZMod 2) (Set.range commVec)) = 2 ^ 15 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_span_eq_card linearIndependent_commVec,
    Nat.card_zmod, Fintype.card_fin]

theorem card_inter_ge
    {K : Subgroup cEdgeStab}
    (hKn : ∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hgen : ∀ i : Fin 10, genK ⟨6 + i, by omega⟩ ∈ K.map edgeRho) :
    2 ^ 15 ≤ Nat.card (edgeQ.subgroupOf K) := by
  rw [← natCard_span_commVec]
  calc Nat.card (Submodule.span (ZMod 2) (Set.range commVec)) ≤ Nat.card (Set.range (psiKQ K)) :=
        Nat.card_le_card_of_injective (fun v => ⟨v.1, span_commVec_subset hKn hgen v.2⟩)
          (fun a b e => Subtype.ext (Subtype.mk.inj e))
    _ ≤ Nat.card (edgeQ.subgroupOf K) := Finite.card_range_le _


theorem card_edgeQ_inter_mul
    (K : Subgroup cEdgeStab) :
    Nat.card K = Nat.card (edgeQ.subgroupOf K) * Nat.card (K.map edgeRho) := by
  have h := card_eq_card_ker_mul_card_map edgeRho K
  rwa [ker_edgeRho] at h

theorem edgeQ_unique
    {K : Subgroup cEdgeStab}
    (hKM : K ≤ edgeMB edgeU0)
    (hKn : ∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hK : Nat.card K = 2 ^ 23) :
    K = edgeQ := by
  have hKbU : K.map edgeRho ≤ UsigW := map_edgeRho_le hKM
  have hX := sddOf_normal (Kb := K.map edgeRho) fun m hm x hx => map_edgeRho_conj hKn hm hx
  have h2 : IsPGroup 2 (sddOf (K.map edgeRho)) :=
    isPGroup_sddOf ((IsPGroup.of_card hK).map edgeRho)
  have hle := le_range_inl hX h2
  by_cases hN : (sddOf (K.map edgeRho)).comap SemidirectProduct.inl = ⊥
  · have hbot := eq_bot_of_sddOf hKbU (eq_bot_of_comap_inl hle hN)
    have hKQ : K ≤ edgeQ := fun k hk => by
      rw [← edgeRho_eq_one_iff, ← Subgroup.mem_bot, ← hbot]
      exact ⟨k, hk, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hKQ (natCard_edgeQ.trans hK.symm).le
  · exfalso
    have htop := eq_top_of_invariant (comap_inl_invariant hX) hN
    have hmem : ∀ n : NQ,
        ((UsigWEquiv (SemidirectProduct.inl n) : UsigW) : Kstab v0) ∈ K.map edgeRho := fun n => by
      have h : n ∈ (sddOf (K.map edgeRho)).comap SemidirectProduct.inl := by
        rw [htop]
        exact Subgroup.mem_top n
      exact mem_sddOf.1 (Subgroup.mem_comap.1 h)
    have hgen : ∀ i : Fin 10, genK ⟨6 + i, by omega⟩ ∈ K.map edgeRho := fun i =>
      UsigWEquiv_inl_signMask i ▸ hmem _
    have hKb : 2 ^ 9 ≤ Nat.card (K.map edgeRho) := by
      rw [← natCard_NQ]
      refine Nat.card_le_card_of_injective (fun n : NQ => (⟨_, hmem n⟩ : K.map edgeRho))
        fun a b e => SemidirectProduct.inl_injective (UsigWEquiv.injective (Subtype.ext ?_))
      exact congrArg (fun z : K.map edgeRho => (z : Kstab v0)) e
    have hc : 2 ^ 23 = Nat.card (edgeQ.subgroupOf K) * Nat.card (K.map edgeRho) :=
      hK.symm.trans (card_edgeQ_inter_mul K)
    have hQK : Nat.card (edgeQ.subgroupOf K) * 2 ^ 9 ≤ 2 ^ 14 * 2 ^ 9 :=
      calc Nat.card (edgeQ.subgroupOf K) * 2 ^ 9
          ≤ Nat.card (edgeQ.subgroupOf K) * Nat.card (K.map edgeRho) := Nat.mul_le_mul_left _ hKb
        _ = 2 ^ 14 * 2 ^ 9 := hc.symm.trans (by norm_num)
    have h14 := Nat.le_of_mul_le_mul_right hQK (by norm_num)
    have h15 := card_inter_ge hKn hgen
    omega

theorem edgeQ_unique_center :
    ∀ K :
    Subgroup cEdgeStab, K ≤ edgeMB
    edgeU0 →
    (∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
    Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
      k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = edgeQ :=
  fun _ hKM hKn hK _ => edgeQ_unique hKM hKn hK

end CFSG.Monster.B.GSide
