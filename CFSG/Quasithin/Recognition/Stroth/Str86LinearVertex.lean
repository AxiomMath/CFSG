module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCount
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyModule
public import CFSG.CGT.Timmesfeld75.L2Basic
public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.Timmesfeld.Bridge.SL2FactsCoord
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.EmptyFaithful.S152He3Chief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {H U L N : Subgroup G} {m : ℕ}

@[expose, instance_reducible] noncomputable def l2ChiefSectionCommGroup {L N : Subgroup G}
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) : CommGroup (Ch3z.chiefMod L N) :=
  commGroupOfElemAbelian hE

@[expose, instance_reducible] noncomputable def l2ChiefSectionModule {L N : Subgroup G}
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) :
    @Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) _
      (@Additive.addCommGroup (Ch3z.chiefMod L N)
        (l2ChiefSectionCommGroup hE)).toAddCommMonoid := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : AddCommGroup (Additive (Ch3z.chiefMod L N)) :=
    @Additive.addCommGroup (Ch3z.chiefMod L N) (l2ChiefSectionCommGroup hE)
  have hsq : ∀ e : Ch3z.chiefMod L N, e ^ 2 = 1 := by
    intro e
    refine Subtype.ext ?_
    simpa using hE.2 (e : SecQuot (Subgroup.normalizer (L : Set G)) L) e.2
  exact CFSG.RankThree.FFModules.moduleOfSq hsq

@[expose] noncomputable def l2ChiefSectionAction (hstep : IsChiefStep H U L N)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) :
    ↥H →* MulAut (Ch3z.chiefMod L N) :=
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  (Ch3z.chiefAut H L N).subtype.comp (Ch3z.chiefHom hHL hHN)

theorem l2ChiefSectionAction_apply (hstep : IsChiefStep H U L N)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (h : ↥H) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    l2ChiefSectionAction hstep hE h =
      ((Ch3z.chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) h : Ch3z.chiefAut H L N) :
        MulAut (Ch3z.chiefMod L N)) := by
  simp [l2ChiefSectionAction]

@[expose] noncomputable def l2ChiefSectionQuotAction (hstep : IsChiefStep H U L N)
    (hUH : U ≤ H) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) :
    oTwoQuot ↥H →* MulAut (Ch3z.chiefMod L N) :=
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hπker : pCore 2 ↥H ≤ (l2ChiefSectionAction hstep hE).ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    have hrO : (r : G) ∈ pCoreOf 2 H := Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
    have hcent : (r : G) ∈ centralizerMod L H N :=
      Ch3z.pCoreOf_le_centralizerMod hUH hstep hE hrO
    have h1 := (Ch3z.chiefHom_eq_one_iff hHL hHN hNL ⟨(r : G), r.2⟩).2 hcent
    change (l2ChiefSectionAction hstep hE r : MulAut (Ch3z.chiefMod L N)) = 1
    rw [l2ChiefSectionAction_apply]
    simpa using congrArg Subtype.val h1
  QuotientGroup.lift (pCore 2 ↥H) (l2ChiefSectionAction hstep hE) hπker

theorem l2ChiefSectionQuotAction_mk (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (h : ↥H) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    l2ChiefSectionQuotAction hstep hUH hE (QuotientGroup.mk h) =
      l2ChiefSectionAction hstep hE h := by
  unfold l2ChiefSectionQuotAction
  exact QuotientGroup.lift_mk' (N := pCore 2 ↥H) (φ := l2ChiefSectionAction hstep hE) _ h

@[expose] noncomputable def l2ChiefSectionSL2Action (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m)) :
    SL(2, GaloisField 2 m) →* MulAut (Ch3z.chiefMod L N) :=
  (l2ChiefSectionQuotAction hstep hUH hE).comp e.symm.toMonoidHom

theorem l2ChiefSectionSL2Action_apply (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (g : SL(2, GaloisField 2 m)) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    l2ChiefSectionSL2Action hstep hUH hE e g =
      l2ChiefSectionQuotAction hstep hUH hE (e.symm g) := by
  unfold l2ChiefSectionSL2Action
  rfl

@[expose] noncomputable def l2ChiefSectionRep (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m)) :
    @Representation (ZMod 2) (SL(2, GaloisField 2 m)) (Additive (Ch3z.chiefMod L N))
      _ _ (@Additive.addCommGroup (Ch3z.chiefMod L N) (l2ChiefSectionCommGroup hE)).toAddCommMonoid
      (l2ChiefSectionModule hE) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  exact (CFSG.RankThree.FFModules.autRep (Ch3z.chiefMod L N)).comp
    (l2ChiefSectionSL2Action hstep hUH hE e)

theorem l2ChiefSectionAction_eq_chiefPsi (hstep : IsChiefStep H U L N)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (h : ↥H) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    l2ChiefSectionAction hstep hE h =
      Ch3z.chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) h := by
  rw [l2ChiefSectionAction_apply]
  rfl

theorem l2ChiefSectionRep_apply (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (g : SL(2, GaloisField 2 m)) (w : Ch3z.chiefMod L N) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    l2ChiefSectionRep hstep hUH hE e g (Additive.ofMul w) =
      Additive.ofMul (l2ChiefSectionSL2Action hstep hUH hE e g w) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  change (CFSG.RankThree.FFModules.autRep (Ch3z.chiefMod L N))
      (l2ChiefSectionSL2Action hstep hUH hE e g) (Additive.ofMul w) = _
  exact CFSG.RankThree.FFModules.autRep_apply (E := Ch3z.chiefMod L N)
    (l2ChiefSectionSL2Action hstep hUH hE e g) (Additive.ofMul w)

theorem l2ChiefSectionRep_apply_mk (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (h : ↥H) (w : Ch3z.chiefMod L N) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    l2ChiefSectionRep hstep hUH hE e (e (QuotientGroup.mk h)) (Additive.ofMul w) =
      Additive.ofMul (l2ChiefSectionAction hstep hE h w) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  rw [l2ChiefSectionRep_apply, l2ChiefSectionSL2Action_apply, MulEquiv.symm_apply_apply,
    l2ChiefSectionQuotAction_mk]

theorem l2ChiefSectionRep_irreducible (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m)) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    (l2ChiefSectionRep hstep hUH hE e).IsIrreducible := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨?_, ?_⟩
  · have hntE : Nontrivial (Ch3z.chiefMod L N) := by
      obtain ⟨n, hnN, hnL⟩ := Set.exists_of_ssubset (SetLike.coe_ssubset_coe.mpr hstep.2.2.1)
      exact ⟨⟨Ch3z.chiefIota hNL ⟨n, hnN⟩, 1, fun h =>
        hnL ((Ch3z.chiefIota_eq_one_iff hNL ⟨n, hnN⟩).1 h)⟩⟩
    infer_instance
  · intro U hU
    let K : Subgroup (Ch3z.chiefMod L N) :=
      { carrier := {e | Additive.ofMul e ∈ U}
        mul_mem' := by
          intro a b ha hb
          change Additive.ofMul a + Additive.ofMul b ∈ U
          exact U.add_mem ha hb
        one_mem' := by
          change (0 : Additive (Ch3z.chiefMod L N)) ∈ U
          exact U.zero_mem
        inv_mem' := by
          intro a ha
          change -Additive.ofMul a ∈ U
          exact U.neg_mem ha }
    have hKinv : ∀ x ∈ Ch3z.chiefAut H L N, ∀ w ∈ K, x w ∈ K := by
      intro x hx w hw
      obtain ⟨h, hh⟩ := Ch3z.chiefHom_surjective hHL hHN ⟨x, hx⟩
      have hxeq : ((Ch3z.chiefHom hHL hHN h : Ch3z.chiefAut H L N) :
          MulAut (Ch3z.chiefMod L N)) = x := congrArg Subtype.val hh
      have h1 := hU (e (QuotientGroup.mk h)) (Additive.ofMul w) hw
      rw [l2ChiefSectionRep_apply_mk] at h1
      rw [l2ChiefSectionAction_apply] at h1
      rwa [hxeq] at h1
    rcases Ch3z.chiefMod_irr hstep hUH K hKinv with hK | hK
    · left
      ext x
      constructor
      · intro hx
        have hxK : x.toMul ∈ K := hx
        rw [hK, Subgroup.mem_bot] at hxK
        rw [Submodule.mem_bot]
        change x.toMul = 1
        exact hxK
      · intro hx
        rw [Submodule.mem_bot] at hx
        rw [hx]
        exact U.zero_mem
    · right
      rw [eq_top_iff]
      intro x _
      have hxK : x.toMul ∈ K := by rw [hK]; exact Subgroup.mem_top _
      change Additive.ofMul x.toMul ∈ U
      exact hxK

theorem l2ChiefSectionRep_nontrivial (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (hnc : ¬ IsCentralStep H L N) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    ∃ g, l2ChiefSectionRep hstep hUH hE e g ≠ 1 := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  by_contra hcon
  push Not at hcon
  apply hnc
  intro h hh n hn
  by_contra hne
  have hσ : l2ChiefSectionAction hstep hE ⟨h, hh⟩ = 1 := by
    have hg := hcon (e (QuotientGroup.mk ⟨h, hh⟩))
    have hσ' : l2ChiefSectionSL2Action hstep hUH hE e (e (QuotientGroup.mk ⟨h, hh⟩)) = 1 := by
      apply CFSG.RankThree.FFModules.autRep_injective
      change (l2ChiefSectionRep hstep hUH hE e) (e (QuotientGroup.mk ⟨h, hh⟩)) = 1
      exact hg
    rw [l2ChiefSectionSL2Action_apply, MulEquiv.symm_apply_apply,
      l2ChiefSectionQuotAction_mk] at hσ'
    exact hσ'
  have hσc : (Ch3z.chiefHom hHL hHN) ⟨h, hh⟩ = 1 := by
    apply Subtype.ext
    have h := hσ
    rwa [l2ChiefSectionAction_apply] at h
  have hcent : h ∈ centralizerMod L H N :=
    (Ch3z.chiefHom_eq_one_iff hHL hHN hNL ⟨h, hh⟩).1 hσc
  exact hne (hcent.2.2 n hn)

theorem exists_l2ChiefSectionRep (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    letI _cg : CommGroup (Ch3z.chiefMod L N) :=
      l2ChiefSectionCommGroup (isElemAbelian_chiefMod hstep hUH hU)
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) :=
      l2ChiefSectionModule (isElemAbelian_chiefMod hstep hUH hU)
    ∃ (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
      (ρ : Representation (ZMod 2) (SL(2, GaloisField 2 m))
        (Additive (Ch3z.chiefMod L N))),
      Fact ρ.IsIrreducible ∧ (∃ g, ρ g ≠ 1) ∧
        (∀ (h : ↥H) (w : Ch3z.chiefMod L N),
          ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
            Additive.ofMul
              (l2ChiefSectionAction hstep (isElemAbelian_chiefMod hstep hUH hU) h w)) := by
  let hE := isElemAbelian_chiefMod hstep hUH hU
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  obtain ⟨e₀⟩ := hL2
  let e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 m))
  refine ⟨e, l2ChiefSectionRep hstep hUH hE e, ?_, ?_, ?_⟩
  · exact ⟨l2ChiefSectionRep_irreducible hstep hUH hE e⟩
  · exact l2ChiefSectionRep_nontrivial hstep hUH hE e hnc
  · intro h w
    exact l2ChiefSectionRep_apply_mk hstep hUH hE e h w

theorem l2ChiefSectionRep_sq_card_fixSub (hm2 : 2 ≤ m) (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (hnc : ¬ IsCentralStep H L N) {t : G} (htH : t ∈ H)
    (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    letI : Fact (l2ChiefSectionRep hstep hUH hE e).IsIrreducible :=
      ⟨l2ChiefSectionRep_irreducible hstep hUH hE e⟩
    Nat.card (CFSG.RankThree.FFModules.fixSub (l2ChiefSectionRep hstep hUH hE e)
      (Subgroup.zpowers (e (QuotientGroup.mk ⟨t, htH⟩)))) ^ 2 =
      Nat.card (Additive (Ch3z.chiefMod L N)) := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  haveI : Fact (l2ChiefSectionRep hstep hUH hE e).IsIrreducible :=
    ⟨l2ChiefSectionRep_irreducible hstep hUH hE e⟩
  set W := Additive (Ch3z.chiefMod L N)
  set ρ := l2ChiefSectionRep hstep hUH hE e
  set a : SL(2, GaloisField 2 m) := e (QuotientGroup.mk ⟨t, htH⟩)
  have hF : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 m (by omega)]
  have hm : 1 ≤ m := by omega
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstep hUH hE e hnc
  have htH2 : (⟨t, htH⟩ : ↥H) * ⟨t, htH⟩ ∈ pCore 2 ↥H := by
    obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp ht
    have hx' : (x : ↥H) = ⟨t, htH⟩ * ⟨t, htH⟩ := Subtype.ext (by simpa using hxt)
    rw [← hx']
    exact hx
  have ha2 : a * a = 1 := by
    have hmk : (QuotientGroup.mk (⟨t, htH⟩ * ⟨t, htH⟩) : oTwoQuot ↥H) = 1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 ↥H) _).2 htH2
    rw [show a * a = e (QuotientGroup.mk (⟨t, htH⟩ * ⟨t, htH⟩)) by
      simp [a, ← map_mul, ← QuotientGroup.mk_mul], hmk, map_one]
  have ha1 : a ≠ 1 := by
    intro h1
    apply htO
    have hmk : (QuotientGroup.mk ⟨t, htH⟩ : oTwoQuot ↥H) = 1 := by
      apply e.injective
      rw [map_one]
      exact h1
    have hmem : ⟨t, htH⟩ ∈ pCore 2 ↥H :=
      (QuotientGroup.eq_one_iff (N := pCore 2 ↥H) _).1 hmk
    exact Subgroup.mem_map.mpr ⟨⟨t, htH⟩, hmem, rfl⟩
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.binary_SL2_irreducible_Frobenius_descent
      hm hF ρ hnt
  have hfin : Module.Finite (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) W :=
    Module.Finite.of_finite
  let b := Module.finBasis (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) W
  obtain ⟨E', _, _, _, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  have hfix := CFSG.QuasithinUnique.Setup.SL2Modules.natCard_fixW_involution
    ρ b ιF ιD J hJne Φ a ha1 ha2
  have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hW : Nat.card W =
      Nat.card (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) ^ 2 ^ J.card := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.natCard_eq_pow_finrank (ρ := ρ), hdim]
  have h2 : 2 ^ J.card = 2 * 2 ^ (J.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsq : Nat.card {w : W // ρ a w = w} ^ 2 = Nat.card W := by
    rw [hfix, hW, ← pow_mul, mul_comm, ← h2]
  have hord : orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha1
  have hfixeq : Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers a)) =
      Nat.card {w : W // ρ a w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro w
    constructor
    · intro hw
      exact hw a (Subgroup.mem_zpowers a)
    · intro hw h hh
      rw [mem_zpowers_iff_mem_range_orderOf, hord] at hh
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
      have hk2 : k = 0 ∨ k = 1 := by
        have := Finset.mem_range.mp hk
        omega
      rcases hk2 with rfl | rfl
      · simp
      · rw [pow_one]
        exact hw
  rw [hfixeq, hsq]

theorem l2ChiefSectionRep_sq_le_card (hm2 : 2 ≤ m)
    (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (hnc : ¬ IsCentralStep H L N) :
    (2 ^ m) ^ 2 ≤ Nat.card (Additive (Ch3z.chiefMod L N)) := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  haveI : Fact (l2ChiefSectionRep hstep hUH hE e).IsIrreducible :=
    ⟨l2ChiefSectionRep_irreducible hstep hUH hE e⟩
  have hnt : ∃ g, l2ChiefSectionRep hstep hUH hE e g ≠ 1 :=
    l2ChiefSectionRep_nontrivial hstep hUH hE e hnc
  have hm : 1 ≤ m := by omega
  have hF : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 m (by omega)]
  exact CFSG.Timmesfeld.Bridge.RootMany.sq_le_card_of_irreducible hm hF
    (l2ChiefSectionRep hstep hUH hE e) hnt

theorem l2Sylow_sq_mem (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (T : Sylow 2 (oTwoQuot ↥H)) :
    (∀ x ∈ (T : Subgroup (oTwoQuot ↥H)), x * x = 1) ∧
      Nat.card (T : Subgroup (oTwoQuot ↥H)) = 2 ^ m := by
  classical
  obtain ⟨φ, hφ⟩ := CFSG.Timmesfeld.Bridge.RootClosure.psl2SylowCoordStmt
    m hm2 (oTwoQuot ↥H) hL2 T
  have hcard : Nat.card (T : Subgroup (oTwoQuot ↥H)) =
      Nat.card (CFSG.Timmesfeld.upperUnipotent (GaloisField 2 m)) := by
    rw [← hφ]
    exact (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).symm
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxφ : φ x ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 m) := by
      rw [← hφ]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
    obtain ⟨t, ht⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff _).1 hxφ
    apply φ.injective
    rw [map_mul, map_one, ht, CFSG.Timmesfeld.RankOne.upperElt_mul, CharTwo.add_self_eq_zero,
      CFSG.Timmesfeld.RankOne.upperElt_zero]
  · rw [hcard, CFSG.Timmesfeld.RankOne.card_upperUnipotent, GaloisField.card 2 m (by omega)]

end CFSG.Quasithin.Stroth
