module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotRouteB
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotO2
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotOuterFusion
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectW

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le)


section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def leviX (σ : K →+* K) :
    Fin 2 → Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  ![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
    ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom]

@[expose] noncomputable def leviY (σ : K →+* K) :
    Fin 2 → Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  ![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ relWordTY)).toMonoidHom,
    ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ relWordUY)).toMonoidHom]

variable (k : Type) [Field k] [Algebra k K]

@[expose] noncomputable def thetaJ (σ : K →+* K) : Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  (E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)

@[expose] noncomputable def shortJ (σ : K →+* K) : Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  (shortRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)

@[expose] noncomputable def w1C (σ : K →+* K) : Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  (shortRootTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)

@[expose] def TorusConjY (σ : K →+* K) : Prop :=
  ∀ X'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ), X'' ≤ shortJ k σ →
    Nat.card X'' = Nat.card (w1C k σ) →
      ∃ c : graphFixedRootGroup TwistTag.E6 K σ, X'' = (w1C k σ).map (MulAut.conj c).toMonoidHom

end Defs

section F3

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_isCoreLeviDecomp_repXC [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    ∃ Q : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      IsCoreLeviDecomp (centralizer ({repXC (apply_apply_eq hK hσ) κ} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) Q (leviX σ κ) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  match κ with
  | 0 =>
    have hd := (isCoreLeviDecomp_stdRepC_zero (k := k) hf hk hK hσ).map
      (MulAut.conj (relWeylC σ relWordTX))
    rw [← centralizer_conj_eq_map] at hd
    rw [repXC_eq_conj (apply_apply_eq hK hσ) 0]
    exact ⟨_, hd⟩
  | 1 =>
    have hd := (isCoreLeviDecomp_stdRepC_one (k := k) hf hk hK hσ).map
      (MulAut.conj (relWeylC σ relWordUX))
    rw [← centralizer_conj_eq_map] at hd
    rw [repXC_eq_conj (apply_apply_eq hK hσ) 1]
    exact ⟨_, hd⟩

theorem exists_isCoreLeviDecomp_repYC [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    ∃ Q : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      IsCoreLeviDecomp (centralizer ({repYC (apply_apply_eq hK hσ) κ} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) Q (leviY σ κ) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  match κ with
  | 0 =>
    have hd := (isCoreLeviDecomp_stdRepC_zero (k := k) hf hk hK hσ).map
      (MulAut.conj (relWeylC σ relWordTY))
    rw [← centralizer_conj_eq_map] at hd
    rw [repYC_eq_conj (apply_apply_eq hK hσ) 0]
    exact ⟨_, hd⟩
  | 1 =>
    have hd := (isCoreLeviDecomp_stdRepC_one (k := k) hf hk hK hσ).map
      (MulAut.conj (relWeylC σ relWordUY))
    rw [← centralizer_conj_eq_map] at hd
    rw [repYC_eq_conj (apply_apply_eq hK hσ) 1]
    exact ⟨_, hd⟩

theorem thetaJ_le_leviX [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    thetaJ k σ ≤ leviX σ κ := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  match κ with
  | 0 =>
    refine subgroupOf_le_map_conj (relWeylC σ relWordTX) fun x hx => ?_
    refine mem_inf.2 ⟨mem_map_conj_iff.1 (thetaRankOneGroup_le_map_relWordTX _ hx), ?_⟩
    exact mul_mem (mul_mem (inv_mem (relWeylC σ relWordTX).2)
      (thetaRankOneGroup_le_C0 hf hk hK hσ hx)) (relWeylC σ relWordTX).2
  | 1 =>
    refine subgroupOf_le_map_conj (relWeylC σ relWordUX) fun x hx => ?_
    have hC : ((relWeylC σ relWordUX : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)⁻¹ * x * (relWeylC σ relWordUX) ∈
          graphFixedRootGroup TwistTag.E6 K σ :=
      mul_mem (mul_mem (inv_mem (relWeylC σ relWordUX).2)
        (thetaRankOneGroup_le_C0 hf hk hK hσ hx)) (relWeylC σ relWordUX).2
    have hL : ((relWeylC σ relWordUX : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)⁻¹ * x * (relWeylC σ relWordUX) ∈ E6Pilot.yLeviF4 K :=
      mem_map_conj_iff.1 (thetaRankOneGroup_le_map_relWordUX _ hx)
    exact ⟨hL, hC⟩

theorem shortJ_le_leviY [CharP K 2] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    shortJ k σ ≤ leviY σ κ := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
    (sigma_eq_self_iff hk hσ _).2 ⟨c, rfl⟩
  match κ with
  | 0 =>
    refine subgroupOf_le_map_conj (relWeylC σ relWordTY) fun x hx => ?_
    refine mem_inf.2 ⟨mem_map_conj_iff.1 (shortRankOneGroup_le_map_relWordTY _ hx), ?_⟩
    exact mul_mem (mul_mem (inv_mem (relWeylC σ relWordTY).2)
      (shortRankOneGroup_le_C0 (apply_apply_eq hK hσ) hσι hx)) (relWeylC σ relWordTY).2
  | 1 =>
    refine subgroupOf_le_map_conj (relWeylC σ relWordUY) fun x hx => ?_
    have hC : ((relWeylC σ relWordUY : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)⁻¹ * x * (relWeylC σ relWordUY) ∈
          graphFixedRootGroup TwistTag.E6 K σ :=
      mul_mem (mul_mem (inv_mem (relWeylC σ relWordUY).2)
        (shortRankOneGroup_le_C0 (apply_apply_eq hK hσ) hσι hx)) (relWeylC σ relWordUY).2
    have hL : ((relWeylC σ relWordUY : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)⁻¹ * x * (relWeylC σ relWordUY) ∈ E6Pilot.yLeviF4 K :=
      mem_map_conj_iff.1 (shortRankOneGroup_le_map_relWordUY _ hx)
    exact ⟨hL, hC⟩

theorem w1C_le_shortJ [CharP K 2] (σ : K →+* K) : w1C k σ ≤ shortJ k σ := fun _ hx =>
  mem_subgroupOf.2 (shortRootTorus_le_shortRankOneGroup _ (mem_subgroupOf.1 hx))

end F3

section Models

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem lieModel_leviX_zero (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel (leviX σ 0) .PSU 6 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (((su6Levi σ).subgroupOf _).equivMapOfInjective (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom
      (MulAut.conj _).injective) (lieModel_su6Levi_subgroupOf hf hk hK hσ)

theorem lieModel_leviX_one (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel (leviX σ 1) .PSp 3 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (((uLevi σ).subgroupOf _).equivMapOfInjective (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom
      (MulAut.conj _).injective) (lieModel_uLevi_subgroupOf hf hk hK hσ)

theorem lieModel_leviY_zero (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel (leviY σ 0) .PSU 6 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (((su6Levi σ).subgroupOf _).equivMapOfInjective (MulAut.conj (relWeylC σ relWordTY)).toMonoidHom
      (MulAut.conj _).injective) (lieModel_su6Levi_subgroupOf hf hk hK hσ)

theorem lieModel_leviY_one (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel (leviY σ 1) .PSp 3 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (((uLevi σ).subgroupOf _).equivMapOfInjective (MulAut.conj (relWeylC σ relWordUY)).toMonoidHom
      (MulAut.conj _).injective) (lieModel_uLevi_subgroupOf hf hk hK hσ)

theorem two_pow_dvd_card_leviX (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    2 ^ (8 * f + 1) ∣ Nat.card (leviX σ κ) := by
  match κ with
  | 0 => exact two_pow_dvd_card_of_lieModel_PSU_six hf (lieModel_leviX_zero hf hk hK hσ)
  | 1 => exact two_pow_dvd_card_of_lieModel_PSp_three hf (lieModel_leviX_one hf hk hK hσ)

theorem two_pow_dvd_card_leviY (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    2 ^ (8 * f + 1) ∣ Nat.card (leviY σ κ) := by
  match κ with
  | 0 => exact two_pow_dvd_card_of_lieModel_PSU_six hf (lieModel_leviY_zero hf hk hK hσ)
  | 1 => exact two_pow_dvd_card_of_lieModel_PSp_three hf (lieModel_leviY_one hf hk hK hσ)

theorem eq_of_nonempty_leviX_mulEquiv (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {κ κ' : Fin 2}
    (ι : leviX σ κ ≃* leviX σ κ') : κ = κ' := by
  match κ, κ', ι with
  | 0, 0, _ => rfl
  | 1, 1, _ => rfl
  | 0, 1, ι => exact ((isEmpty_mulEquiv_of_lieModel_PSU_six_PSp_three hf
      (lieModel_leviX_zero hf hk hK hσ) (lieModel_leviX_one hf hk hK hσ)).false ι).elim
  | 1, 0, ι => exact ((isEmpty_mulEquiv_of_lieModel_PSU_six_PSp_three hf
      (lieModel_leviX_zero hf hk hK hσ) (lieModel_leviX_one hf hk hK hσ)).false ι.symm).elim

theorem eq_of_nonempty_leviY_mulEquiv (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {κ κ' : Fin 2}
    (ι : leviY σ κ ≃* leviY σ κ') : κ = κ' := by
  match κ, κ', ι with
  | 0, 0, _ => rfl
  | 1, 1, _ => rfl
  | 0, 1, ι => exact ((isEmpty_mulEquiv_of_lieModel_PSU_six_PSp_three hf
      (lieModel_leviY_zero hf hk hK hσ) (lieModel_leviY_one hf hk hK hσ)).false ι).elim
  | 1, 0, ι => exact ((isEmpty_mulEquiv_of_lieModel_PSU_six_PSp_three hf
      (lieModel_leviY_zero hf hk hK hσ) (lieModel_leviY_one hf hk hK hσ)).false ι.symm).elim

theorem classPredicate_repXC [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {Q : Fin 2 → Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hQ : ∀ κ, IsCoreLeviDecomp (centralizer ({repXC (apply_apply_eq hK hσ) κ} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) (Q κ) (leviX σ κ)) (κ : Fin 2)
    (x : graphFixedRootGroup TwistTag.E6 K σ) (hx : orderOf x = 2)
    (hψ : Nonempty (perfectCore (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) ≃*
      (Q κ ⊔ leviX σ κ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)))) :
    ∃ (κ' : Fin 2) (c : graphFixedRootGroup TwistTag.E6 K σ),
      c * x * c⁻¹ = repXC (apply_apply_eq hK hσ) κ' := by
  have eM : (leviX σ κ).subgroupOf (Q κ ⊔ leviX σ κ) ≃* leviX σ κ := subgroupOfEquivOfLe le_sup_right
  refine exists_conj_repXC_of_nonempty_mulEquiv hf hK hσ hx
    (M := (leviX σ κ).subgroupOf (Q κ ⊔ leviX σ κ))
    (EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv eM.symm (hQ κ).2.2.2.2) ?_ hψ
  rw [Nat.card_congr eM.toEquiv]
  exact two_pow_dvd_card_leviX hf hk hK hσ κ

theorem classPredicate_repYC [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {Q : Fin 2 → Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hQ : ∀ κ, IsCoreLeviDecomp (centralizer ({repYC (apply_apply_eq hK hσ) κ} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) (Q κ) (leviY σ κ)) (κ : Fin 2)
    (x : graphFixedRootGroup TwistTag.E6 K σ) (hx : orderOf x = 2)
    (hψ : Nonempty (perfectCore (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) ≃*
      (Q κ ⊔ leviY σ κ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)))) :
    ∃ (κ' : Fin 2) (c : graphFixedRootGroup TwistTag.E6 K σ),
      c * x * c⁻¹ = repYC (apply_apply_eq hK hσ) κ' := by
  have eM : (leviY σ κ).subgroupOf (Q κ ⊔ leviY σ κ) ≃* leviY σ κ := subgroupOfEquivOfLe le_sup_right
  refine exists_conj_repYC_of_nonempty_mulEquiv hf hK hσ hx
    (M := (leviY σ κ).subgroupOf (Q κ ⊔ leviY σ κ))
    (EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv eM.symm (hQ κ).2.2.2.2) ?_ hψ
  rw [Nat.card_congr eM.toEquiv]
  exact two_pow_dvd_card_leviY hf hk hK hσ κ

end Models

section Step7

@[expose] def LeviAutConj {C : Type*} [Group C] (M : Fin 2 → Subgroup C) (J : Subgroup C) : Prop :=
  ∀ (κ : Fin 2) (ι : M κ ≃* M κ), ∃ c : C,
    ((J.subgroupOf (M κ)).map ι.toMonoidHom).map (M κ).subtype = J.map (MulAut.conj c).toMonoidHom

theorem leviAutConj_of_isAutConjIn {C : Type*} [Group C] {M : Fin 2 → Subgroup C}
    {J : Subgroup C} (h : ∀ κ, E6Pilot.IsAutConjIn (M κ) J) : LeviAutConj M J := fun κ ι => by
  obtain ⟨m, -, hm⟩ := h κ ι
  exact ⟨m, hm⟩

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_thetaJ (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (thetaJ k σ : Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  rw [thetaJ, centralizer_subgroupOf (thetaRankOneGroup_le_C0 (by omega) hk hK hσ),
    ← inf_subgroupOf_right, centralizer_thetaRankOneGroup_inf_eq hf2 hk hK hσ]

theorem step7_X (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hF5 : LeviAutConj (leviX σ) (thetaJ k σ))
    (κ κ' : Fin 2) (ι : leviX σ κ ≃* leviX σ κ')
    (X'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ))
    (hX'' : X'' ≤ (((thetaJ k σ).subgroupOf (leviX σ κ)).map ι.toMonoidHom).map
      (leviX σ κ').subtype) :
    ∃ P'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      P'' ≤ centralizer (X'' : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
        Nonempty (P'' ≃* (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  obtain rfl := eq_of_nonempty_leviX_mulEquiv (by omega) hk hK hσ ι
  obtain ⟨c, hc⟩ := hF5 κ ι
  rw [hc] at hX''
  refine ⟨centralizer (((thetaJ k σ).map (MulAut.conj c).toMonoidHom :
    Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) : Set (graphFixedRootGroup TwistTag.E6 K σ)),
    centralizer_le hX'', ?_⟩
  obtain ⟨e⟩ := E6Pilot.nonempty_centralizer_map_conj_mulEquiv (thetaJ k σ) c
  rw [centralizer_thetaJ hf2 hk hK hσ] at e
  exact ⟨e⟩

theorem step7_Y (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hF5 : LeviAutConj (leviY σ) (shortJ k σ))
    (hT : TorusConjY k σ) (κ κ' : Fin 2) (ι : leviY σ κ ≃* leviY σ κ')
    (X'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ))
    (hX'' : X'' ≤ (((shortJ k σ).subgroupOf (leviY σ κ)).map ι.toMonoidHom).map
      (leviY σ κ').subtype)
    (hcard : Nat.card X'' = Nat.card (w1C k σ)) :
    ∃ P'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      P'' ≤ centralizer (X'' : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
        Nonempty (P'' ≃* (omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  obtain rfl := eq_of_nonempty_leviY_mulEquiv (by omega) hk hK hσ ι
  obtain ⟨c, hc⟩ := hF5 κ ι
  rw [hc] at hX''
  set X₀ := X''.map (MulAut.conj c⁻¹).toMonoidHom with hX₀
  have hX₀J : X₀ ≤ shortJ k σ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hjx⟩ := hX'' hx
    rw [← hjx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e : c⁻¹ * (c * j * c⁻¹) * c = j := by group
    rw [e]
    exact hj
  have hX₀c : Nat.card X₀ = Nat.card (w1C k σ) := by
    rw [hX₀, card_map_of_injective (MulAut.conj c⁻¹).injective, hcard]
  obtain ⟨d, hd⟩ := hT X₀ hX₀J hX₀c
  have hLW : (omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer (w1C k σ : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    rw [w1C, centralizer_shortRootTorus_subgroupOf hf2 hk hK hσ]
    exact le_sup_right
  set L₁ := (omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) with hL₁
  have hX''eq : X'' = (w1C k σ).map (MulAut.conj (c * d)).toMonoidHom := by
    have h1 : X'' = X₀.map (MulAut.conj c).toMonoidHom := by
      rw [hX₀, E6Pilot.map_conj_map_conj_eq_conj_mul, mul_inv_cancel]
      ext x
      simp
    rw [h1, hd, E6Pilot.map_conj_map_conj_eq_conj_mul]
  refine ⟨L₁.map (MulAut.conj (c * d)).toMonoidHom, ?_,
    ⟨(L₁.equivMapOfInjective _ (MulAut.conj (c * d)).injective).symm⟩⟩
  rw [hX''eq]
  exact map_conj_le_centralizer_map_conj hLW (c * d)

end Step7

section LemmaC

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem conj_eq_mul_of_conj {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (htC : t ∈ centralizer (L : Set G)) {h : G} {x y c : C}
    (hh : h⁻¹ * t * h = t * (e.symm x : G)) (hc : c * x * c⁻¹ = y) :
    (h * (e.symm c : G)⁻¹)⁻¹ * t * (h * (e.symm c : G)⁻¹) = t * (e.symm y : G) := by
  have htc : (e.symm c : G) * t = t * (e.symm c : G) := mem_centralizer_iff.1 htC _ (e.symm c).2
  have e1 : (h * (e.symm c : G)⁻¹)⁻¹ * t * (h * (e.symm c : G)⁻¹) =
      (e.symm c : G) * (h⁻¹ * t * h) * (e.symm c : G)⁻¹ := by group
  rw [e1, hh, ← hc]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← mul_assoc, htc]
  group

theorem exists_conj_eq_mul_repYC_twistedE6 (hset : StandardSetting G L) [CharP K 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (κ : Fin 2) (h : G), h⁻¹ * t * h = t * (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) := by
  have htC := EPilot.mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  obtain ⟨κ, h, hh⟩ := exists_conj_eq_mul_repXC_twistedE6 hset hf hk hK σ hσ e hperf hξ ht hKt
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_repXC_repYC (apply_apply_eq hK hσ) κ)
  exact ⟨κ, _, conj_eq_mul_of_conj e htC hh hc⟩

end LemmaC

end CFSG.SeitzReduction.TwistedE6Pilot
