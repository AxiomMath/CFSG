module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Vocab
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch6Remark612

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def L2FFModuleFact : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X K : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n →
      K ≤ X → X ≤ Subgroup.normalizer (K : Set (MulAut V)) →
      (∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K) → pCoreOf 2 X = ⊥ →
      Nonempty (↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) →
      Nat.card ↥K = 2 ^ n * ((2 ^ n) ^ 2 - 1) → CFSG.IsQuasisimple ↥K →
      SQTKGroup ↥K → IsFFModule X →
        BinaryNaturalSL K ⊤ (fixV K) 2 n ∨
        (n = 2 ∧ IsIntDirect (commV K) (fixV X) ⊤ ∧ Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧
          SymmetricNatural X (commV K) ⊥ 5)

section Restrict

variable {G : Type} [Group G] {Y V W : Subgroup G} [IsMulCommutative ↥V] [IsMulCommutative ↥W]

theorem FFModel.Realizes.restrict {D : FFModel} (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hWV : W ≤ V)
    (h : D.Realizes (autOn Y V) (W.subgroupOf V) ⊥) : D.Realizes (autOn Y W) ⊤ ⊥ := by
  obtain ⟨π, hsurj, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  obtain ⟨r, hrs, hr⟩ := exists_autOn_restrict hYV hYW hWV
  let φ : ↥(⊤ : Subgroup ↥W) →* ↥(W.subgroupOf V) :=
    { toFun := fun w => ⟨⟨(w : ↥W), hWV (w : ↥W).2⟩, (w : ↥W).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφs : Function.Surjective φ := by
    rintro ⟨⟨v, hv⟩, hvW⟩
    exact ⟨⟨⟨v, hvW⟩, Subgroup.mem_top _⟩, rfl⟩
  refine ⟨r.comp π, hrs.comp hsurj, bot_le, hks, fun _ _ _ => Subgroup.mem_top _, ?_, hsec, hker,
    β.comp φ, hβs.comp hφs, ?_, ?_⟩
  · intro a z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro w
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h1
      apply Subtype.ext
      exact congrArg (fun x : ↥V => (x : G)) h1
    · intro h1
      apply Subtype.ext
      exact congrArg (fun x : ↥W => (x : G)) h1
  · intro γ w m hu hm hw
    have hmem : (((π γ : ↥(autOn Y V)) : MulAut ↥V) ⟨((w : ↥W) : G), hWV (w : ↥W).2⟩ : G) ∈ W := by
      rw [← hr (π γ) (w : ↥W)]
      exact (((r (π γ) : ↥(autOn Y W)) : MulAut ↥W) (w : ↥W)).2
    have h1 : φ ⟨(((r.comp π) γ : ↥(autOn Y W)) : MulAut ↥W) (w : ↥W), hu⟩ =
        ⟨((π γ : ↥(autOn Y V)) : MulAut ↥V) ⟨((w : ↥W) : G), hWV (w : ↥W).2⟩, hmem⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact hr (π γ) (w : ↥W)
    show β (φ ⟨(((r.comp π) γ : ↥(autOn Y W)) : MulAut ↥W) (w : ↥W), hu⟩) = _
    rw [h1]
    exact hβe γ (φ w) m hmem hm hw

end Restrict

theorem stmt5_1_2_FF_of (hF : L2FFModuleFact) : Stmt5_1_2_FF := by
  intro G _ _ T M L V n h hV hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred : IsTwoReducedIn (L ⊔ T) V := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hYV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hYV
  have hYL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := h.sup_le_normalizer
  let hVc : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (by
    have := hVel.1
    exact setLike_mul_comm a.2 b.2)⟩⟩
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hVel.2 v v.2)
  set X := autOn (L ⊔ T) V with hXdef
  set K := autOn L V with hKdef
  have hKX : K ≤ X := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hn := InternalSec.autOn_normal_of (U := V) hYL
  have hXK : X ≤ Subgroup.normalizer (K : Set (MulAut ↥V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hn x hx k
    · intro hk
      have := hn x⁻¹ (X.inv_mem hx) _ hk
      simpa [mul_assoc] using this
  have h2X : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K := by
    refine InternalSec.autOn_two_of hLV fun y hy => ?_
    obtain ⟨e, he⟩ := InternalSec.two_of_sup h.sylow.1 h.T_le_normalizer y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩
  have hO2 : pCoreOf 2 X = ⊥ :=
    InternalSec.pCoreOf_autOn_eq_bot_of_isPrimeReduced hV.1 hV.2.1
  have hOK : pCoreOf 2 K = ⊥ := le_bot_iff.mp (hO2 ▸
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K X hKX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK))
  have hLnc : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hL
    apply hV.2.2
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hL)
  have hker2 : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
    InternalSec.isPGroup_ker_of_simple hLV h.isSimple hOK hLnc
  have hkerEq : (InternalSec.autOnHom hLV).ker = CFSG.pCore 2 ↥L := by
    apply le_antisymm
    · have hkp : IsPGroup 2 ↥(InternalSec.autOnHom hLV).ker := by
        let f : ↥(InternalSec.autOnHom hLV).ker →* ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
          { toFun := fun x => ⟨((x : ↥L) : G), (x : ↥L).2,
              (InternalSec.mem_ker_autOnHom hLV _).mp x.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        have hf : Function.Injective f := fun a b hab =>
          Subtype.ext (Subtype.ext (congrArg (fun y : ↥(L ⊓ Subgroup.centralizer (V : Set G)) =>
            (y : G)) hab))
        exact hker2.of_injective f hf
      exact le_sSup ⟨inferInstance, hkp⟩
    · exact InternalSec.pCore_le_ker_autOnHom hLV hOK
  obtain ⟨eL⟩ := nonempty_equiv_psl_of_lieModel (by have := h.two_le; omega) h.lie
  have eK : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (((QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (InternalSec.autOnHom_surjective hLV))).symm).trans eL
  have hSY : SQTKGroup ↥(L ⊔ T) :=
    sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian h.maximal.1.2.2.2
  have hSL : SQTKGroup ↥L := by
    have h1 := InternalSec.sqtkGroup_subgroup hSY (L.subgroupOf (L ⊔ T))
    refine InternalSec.sqtkGroup_of_surjective
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ T)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ T)).surjective ?_ h1
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subgroupOfEquivOfLe _).injective]
    exact IsPGroup.of_bot
  have hSK : SQTKGroup ↥K := InternalSec.sqtkGroup_autOn hLV hSL hker2
  have hqK : CFSG.IsQuasisimple ↥K := InternalSec.isQuasisimple_autOn hLV h.isQuasisimple hOK hLnc
  have hcardK : Nat.card ↥K = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← h.card_quot]
    exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (InternalSec.autOnHom_surjective hLV))).toEquiv).symm
  have hJT : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hJ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
  have hJY : ¬ thompsonJ (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hJT ((thompsonJ_le_thompsonJ_of_isSylowTwoOf (h.isSylowTwoOf le_sup_right)).trans hle)
  have hFF : IsFFModule (V := ↥V) X := (B2_7_of_not_le hVel hV.1 hYV hJY).1
  rcases hF ↥V hV2 X K n h.two_le hKX hXK h2X hO2 ⟨eK⟩ hcardK hqK hSK hFF with
    hnat | ⟨hn2, hdir, heX, hsym⟩
  · left
    refine ⟨hLV, hVc, ?_⟩
    rw [← fixV_autOn hLV]
    exact hnat
  · right
    have hcomm : (commV K).map V.subtype = ⁅V, L⁆ := map_commV_autOn hLV
    have hfix : (fixV X).map V.subtype =
        V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) := by
      rw [fixV_autOn hYV, Subgroup.subgroupOf_map_subtype, inf_comm]
    have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
    refine ⟨hn2, ⟨?_, ?_⟩, heX, ?_⟩
    · rw [← hcomm, ← hfix, ← Subgroup.map_inf_eq _ _ _ V.subtype_injective, hdir.2,
        Subgroup.map_bot]
    · rw [← hcomm, ← hfix, ← Subgroup.map_sup, hdir.1, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    · have hYW : L ⊔ T ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
        le_normalizer_commutator_of hYV hYL
      let hWc : IsMulCommutative ↥⁅V, L⁆ := ⟨⟨fun a b => Subtype.ext (by
        have := hVel.1
        exact setLike_mul_comm (hWV a.2) (hWV b.2))⟩⟩
      refine ⟨hYW, hWc, ?_⟩
      have hU : commV K = ⁅V, L⁆.subgroupOf V := by
        apply Subgroup.map_injective V.subtype_injective
        rw [hcomm, Subgroup.map_subgroupOf_eq_of_le hWV]
      rw [hU] at hsym
      exact FFModel.Realizes.restrict hYV hYW hWV hsym

end CFSG.Quasithin.H13
