module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.NQRigidCoreQuot

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G]

theorem mem_normalizer_subgroupOf_of {X K : Subgroup G} {h : G} (hhK : h ∈ K)
    (hhN : h ∈ normalizer (X : Set G)) :
    (⟨h, hhK⟩ : K) ∈ normalizer ((X.subgroupOf K : Subgroup K) : Set K) := by
  rw [mem_normalizer_iff]
  intro y
  simp only [mem_subgroupOf, coe_mul, coe_inv]
  exact mem_normalizer_iff.mp hhN y

theorem subgroupOfEquivOfLe_normalizerMonoidHom {X K : Subgroup G} (hXK : X ≤ K) {h : G}
    (hhK : h ∈ K) (hhN : h ∈ normalizer (X : Set G))
    (hh' : (⟨h, hhK⟩ : K) ∈ normalizer ((X.subgroupOf K : Subgroup K) : Set K))
    (x : X.subgroupOf K) :
    subgroupOfEquivOfLe hXK ((X.subgroupOf K).normalizerMonoidHom ⟨⟨h, hhK⟩, hh'⟩ x) =
      X.normalizerMonoidHom ⟨h, hhN⟩ (subgroupOfEquivOfLe hXK x) := by
  apply Subtype.ext
  rfl

theorem frattiniEquivSubgroupOf_conj {X K : Subgroup G} (hXK : X ≤ K) {h : G} (hhK : h ∈ K)
    (hhN : h ∈ normalizer (X : Set G))
    (w : (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K)) ⧸
      frattini (X.subgroupOf K ⧸ CFSG.pCore 2 (X.subgroupOf K))) :
    frattiniEquivSubgroupOf hXK (normalizerFrattiniConj (X.subgroupOf K)
        ⟨⟨h, hhK⟩, mem_normalizer_subgroupOf_of hhK hhN⟩ w) =
      normalizerFrattiniConj X ⟨h, hhN⟩ (frattiniEquivSubgroupOf hXK w) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  rw [normalizerFrattiniConj_mk_mk, frattiniEquivSubgroupOf_mk, frattiniEquivSubgroupOf_mk,
    normalizerFrattiniConj_mk_mk, subgroupOfEquivOfLe_normalizerMonoidHom hXK hhK hhN]

theorem congr_normalizerFrattiniConj {X K : Subgroup G} (hXK : X ≤ K) {h : G} (hhK : h ∈ K)
    (hhN : h ∈ normalizer (X : Set G)) :
    MulAut.congr (frattiniEquivSubgroupOf hXK) (normalizerFrattiniConj (X.subgroupOf K)
        ⟨⟨h, hhK⟩, mem_normalizer_subgroupOf_of hhK hhN⟩) =
      normalizerFrattiniConj X ⟨h, hhN⟩ := by
  ext w
  change frattiniEquivSubgroupOf hXK (normalizerFrattiniConj (X.subgroupOf K)
    ⟨⟨h, hhK⟩, mem_normalizer_subgroupOf_of hhK hhN⟩ ((frattiniEquivSubgroupOf hXK).symm w)) = _
  rw [frattiniEquivSubgroupOf_conj, MulEquiv.apply_symm_apply]

theorem map_congr_image_subgroupOf {X K Q : Subgroup G} (hXK : X ≤ K) (hQK : Q ≤ K)
    (hQN : Q ≤ normalizer (X : Set G)) :
    (((Q.subgroupOf K).subgroupOf (normalizer ((X.subgroupOf K : Subgroup K) : Set K))).map
        (normalizerFrattiniConj (X.subgroupOf K))).map
        (MulAut.congr (frattiniEquivSubgroupOf hXK)).toMonoidHom =
      (Q.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X) := by
  ext γ
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    have hhQ : ((n : K) : G) ∈ Q := mem_subgroupOf.mp (mem_subgroupOf.mp hn)
    refine ⟨⟨((n : K) : G), hQN hhQ⟩, mem_subgroupOf.mpr hhQ, ?_⟩
    rw [MulEquiv.coe_toMonoidHom]
    exact (congr_normalizerFrattiniConj hXK (n : K).2 (hQN hhQ)).symm
  · rintro ⟨n, hn, rfl⟩
    have hhQ : (n : G) ∈ Q := mem_subgroupOf.mp hn
    refine ⟨normalizerFrattiniConj (X.subgroupOf K)
      ⟨⟨(n : G), hQK hhQ⟩, mem_normalizer_subgroupOf_of (hQK hhQ) n.2⟩, ⟨_, ?_, rfl⟩, ?_⟩
    · exact mem_subgroupOf.mpr (mem_subgroupOf.mpr hhQ)
    · rw [MulEquiv.coe_toMonoidHom, congr_normalizerFrattiniConj]

@[expose] noncomputable def imageEquivSubgroupOf {X K Q : Subgroup G} (hXK : X ≤ K) (hQK : Q ≤ K)
    (hQN : Q ≤ normalizer (X : Set G)) :
    (((Q.subgroupOf K).subgroupOf (normalizer ((X.subgroupOf K : Subgroup K) : Set K))).map
        (normalizerFrattiniConj (X.subgroupOf K))) ≃*
      (Q.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X) :=
  ((((Q.subgroupOf K).subgroupOf (normalizer ((X.subgroupOf K : Subgroup K) : Set K))).map
    (normalizerFrattiniConj (X.subgroupOf K))).equivMapOfInjective _
    (MulAut.congr (frattiniEquivSubgroupOf hXK)).injective).trans
    (MulEquiv.subgroupCongr (map_congr_image_subgroupOf hXK hQK hQN))

theorem isCyclic_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    IsCyclic A ↔ IsCyclic B :=
  ⟨fun _ => isCyclic_of_surjective e.toMonoidHom e.surjective,
    fun _ => isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective⟩

theorem nonscalar_image_subgroupOf {p : ℕ} {X K Q : Subgroup G} (hXK : X ≤ K) (hQK : Q ≤ K)
    (hQN : Q ≤ normalizer (X : Set G)) {Q' : Subgroup K} (hQ' : Q' = Q.subgroupOf K)
    {γ : MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))}
    (hγ : γ ∈ (Q.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X))
    (hns : ¬ ∃ c : ZMod p, ∀ w, γ w = w ^ c.val) :
    ∃ γ' ∈ (Q'.subgroupOf (normalizer ((X.subgroupOf K : Subgroup K) : Set K))).map
        (normalizerFrattiniConj (X.subgroupOf K)), ¬ ∃ c : ZMod p, ∀ w, γ' w = w ^ c.val := by
  rw [← map_congr_image_subgroupOf hXK hQK hQN] at hγ
  obtain ⟨γ', hγ', rfl⟩ := hγ
  refine ⟨γ', by rw [hQ']; exact hγ', ?_⟩
  rintro ⟨c, hc⟩
  apply hns
  refine ⟨c, fun w => ?_⟩
  change frattiniEquivSubgroupOf hXK (γ' ((frattiniEquivSubgroupOf hXK).symm w)) = w ^ c.val
  rw [hc, map_pow, MulEquiv.apply_symm_apply]

theorem map_center_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hz
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hz]
  · intro z hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rw [mem_center_iff] at hz
    rw [SetLike.mem_coe, mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]

@[expose] noncomputable def coreQuotEquiv {K₁ K₂ : Type*} [Group K₁] [Group K₂] [Finite K₁]
    [Finite K₂] (e : K₁ ≃* K₂) : (K₁ ⧸ CFSG.pCore 2 K₁) ≃* (K₂ ⧸ CFSG.pCore 2 K₂) :=
  QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)

@[expose] noncomputable def centerQuotEquiv {K₁ K₂ : Type*} [Group K₁] [Group K₂] [Finite K₁]
    [Finite K₂] (e : K₁ ≃* K₂) :
    ((K₁ ⧸ CFSG.pCore 2 K₁) ⧸ center (K₁ ⧸ CFSG.pCore 2 K₁)) ≃*
      ((K₂ ⧸ CFSG.pCore 2 K₂) ⧸ center (K₂ ⧸ CFSG.pCore 2 K₂)) :=
  QuotientGroup.congr _ _ (coreQuotEquiv e) (map_center_mulEquiv (coreQuotEquiv e))

theorem card_center_coreQuot_congr {K₁ K₂ : Type*} [Group K₁] [Group K₂] [Finite K₁]
    [Finite K₂] (e : K₁ ≃* K₂) :
    Nat.card (center (K₁ ⧸ CFSG.pCore 2 K₁)) = Nat.card (center (K₂ ⧸ CFSG.pCore 2 K₂)) := by
  rw [← map_center_mulEquiv (coreQuotEquiv e),
    card_map_of_injective (f := (coreQuotEquiv e).toMonoidHom) (coreQuotEquiv e).injective]

end CFSG.Quasithin.H13.NQRigid
