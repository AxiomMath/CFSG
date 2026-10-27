module

public import CFSG.Quasithin.Recognition.Stroth.Str83G3Main2
public import CFSG.Quasithin.Recognition.Stroth.Str83EightL2
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality
public import CFSG.Quasithin.MS93.S38EAZ
public import CFSG.GroupTheory.CardSupInf
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefModBot

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem card_fixSub_eq_card_fixedSub {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {G' : Type*} [Group G'] (ρ : Representation (ZMod 2) G' W) (A : Subgroup G') :
    Nat.card (CFSG.RankThree.FFModules.fixSub ρ A) =
      Nat.card (CFSG.QuasithinUnique.Setup.X7.fixedSub ρ A) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

private theorem le_relIndex_of_mul_card_le {Y C : Subgroup G} {m : ℕ}
    (h : m * Nat.card ↥C ≤ Nat.card ↥Y)
    (hrel : C.relIndex Y * Nat.card ↥C = Nat.card ↥Y) :
    m ≤ C.relIndex Y := by
  refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥C) ?_ (Nat.card_pos (α := ↥C))
  rw [hrel]
  exact h

private theorem eq_relIndex_of_mul_card_eq {Y C : Subgroup G} {m : ℕ}
    (h : Nat.card ↥Y = m * Nat.card ↥C)
    (hrel : C.relIndex Y * Nat.card ↥C = Nat.card ↥Y) :
    C.relIndex Y = m := by
  refine Nat.mul_right_cancel (Nat.card_pos (α := ↥C)) ?_
  rw [hrel, h]

theorem str83_bottom_st8_false
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha1 : a = 1)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ1 : ¬ thompsonJ S ≤ Q1 L1 L2 S)
    {Y : Subgroup G} (hYZ : Y ≤ Z2 L1 L2 S) (hYH : Y ≤ L2 ⊔ S) (hV : IsElemAbelian 2 Y)
    (hstep : IsChiefStep (L2 ⊔ S) Y ⊥ Y) :
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
    Nat.card (Additive (Ch3z.chiefMod ⊥ Y)) = 2 ^ 8 → False := by
  subst ha1
  dsimp only
  intro hW
  have hL2' : IsL2Quot 3 (oTwoQuot ↥L2) := by
    have h3 : 2 * 1 + 1 = 3 := by norm_num
    rwa [h3] at hL2
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨3, by norm_num, hL2'⟩))
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S :=
    str86_pCoreOf_sup_eq_q2 hF hB (by norm_num) hL2'
  have hL2sup : IsL2Quot 3 (oTwoQuot ↥(L2 ⊔ S)) :=
    str86_isL2Quot_sup_of_caseII hF hB (by norm_num) hL2'
  have hSQ2 : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S :=
    (str83_caseI_basics hF hB (by norm_num) hSz hL2' hZI).2.2.2.1
  have hQ2S : Q2 L1 L2 S ≤ S := str86_q2_le_s hF hB (by norm_num) hL2'
  have hQ2Z : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZ2S : Z2 L1 L2 S ≤ S := (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hVz2 : IsElemAbelian 2 (Z2 L1 L2 S) :=
    isElemAbelian_z2 (L1 := L1) (L2 := L2) (S := S)
  have hSP2 : S ≤ P2 L1 L2 S := by
    conv_lhs => rw [hS2]
    exact sup_le (inf_le_right.trans le_sup_left) (pCoreOf_le 2 (P2 L1 L2 S))
  have hHP2 : L2 ⊔ S ≤ P2 L1 L2 S := sup_le le_sup_left hSP2
  have hG1Z : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    hHP2.trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hSyl : IsSylowTwoOf S (L2 ⊔ S) := isSylowTwoOf_sup_Q2 hF.1 hS2
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨1, by norm_num, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hnc : ¬ IsCentralStep (L2 ⊔ S) ⊥ Y := by
    intro hcent
    have hZ2bot :=
      z2_inf_centralizer_sup_eq_bot_of_caseI hF hB (by norm_num) hSz hL2' hZI
    have hYleC : Y ≤ Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 : g * x * g⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := hcent g hg x hx
      have h2 : g * x * g⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h1
      have h3 : g * x * g⁻¹ = x := by
        have := congrArg (fun y => y * x) h2
        simpa [mul_assoc] using this
      have h4 : g * x = x * g := by
        have := congrArg (fun y => y * g) h3
        simpa [mul_assoc] using this
      exact h4
    have hYle : Y ≤ Z2 L1 L2 S ⊓
        Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) := le_inf hYZ hYleC
    have hYbot : Y = ⊥ := le_bot_iff.mp (hYle.trans (le_of_eq hZ2bot))
    exact (ne_of_gt hstep.2.2.1) hYbot
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
  letI : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  obtain ⟨e₀⟩ := hL2sup
  let e : oTwoQuot ↥(L2 ⊔ S) ≃* SL(2, GaloisField 2 3) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 3))
  let ρ : Representation (ZMod 2) SL(2, GaloisField 2 3)
      (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionRep hstep hYH hE e
  haveI : Fact ρ.IsIrreducible := ⟨l2ChiefSectionRep_irreducible hstep hYH hE e⟩
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstep hYH hE e hnc
  have hFcard : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 3 (by norm_num)]
  have hWY : Nat.card ↥Y = 2 ^ 8 := by
    rw [Nat.card_congr (chiefModBotMulEquiv Y).toEquiv]
    change Nat.card (Additive (Ch3z.chiefMod ⊥ Y)) = 2 ^ 8
    exact hW
  have hWYeq : Nat.card (Additive (Ch3z.chiefMod ⊥ Y)) = Nat.card ↥Y :=
    hW.trans hWY.symm
  have hnum := eightL_l_one_numerics (F := GaloisField 2 3) hFcard ρ hnt hW
  obtain ⟨hnum1, hnum4, hnum8⟩ := hnum
  let p : ↥(L2 ⊔ S) →* oTwoQuot ↥(L2 ⊔ S) :=
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L2 ⊔ S))
  let φ : ↥(L2 ⊔ S) →* SL(2, GaloisField 2 3) := e.toMonoidHom.comp p
  have hkerφ : φ.ker = CFSG.Open.pCore 2 ↥(L2 ⊔ S) := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : p x = 1 := by
        apply e.injective
        rw [map_one]
        simpa [φ] using hx
      exact (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥(L2 ⊔ S)) x).mp h1
    · intro hx
      have hq : p x = 1 :=
        (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥(L2 ⊔ S)) x).mpr hx
      simp only [φ, MonoidHom.comp_apply, hq, map_one]
  have hdispInv : ∀ t ∈ S, t * t ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) →
      t ∉ Subgroup.centralizer (Z2 L1 L2 S : Set G) →
      (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y = 16 := by
    intro t htS httC htC
    have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) htS
    have httQ2 : t * t ∈ Q2 L1 L2 S := by
      rw [← hSQ2]
      exact Subgroup.mem_inf.mpr ⟨S.mul_mem htS htS, httC⟩
    have htQ2 : t ∉ Q2 L1 L2 S := fun h => htC (hQ2Z h)
    let ā : SL(2, GaloisField 2 3) := φ ⟨t, htH⟩
    have hā2 : ā * ā = 1 := by
      have hmem : (⟨t, htH⟩ * ⟨t, htH⟩ : ↥(L2 ⊔ S)) ∈ φ.ker := by
        rw [hkerφ]
        exact (CFSG.mem_openPCoreOf_iff (⟨t, htH⟩ * ⟨t, htH⟩)).mp
          (by rw [hpCore2]; simpa using httQ2)
      have h1 : φ (⟨t, htH⟩ * ⟨t, htH⟩) = 1 := by
        have := hmem
        rwa [MonoidHom.mem_ker] at this
      have hmul : φ (⟨t, htH⟩ * ⟨t, htH⟩) = φ ⟨t, htH⟩ * φ ⟨t, htH⟩ := map_mul φ _ _
      rw [hmul] at h1
      exact h1
    have hā1 : ā ≠ 1 := by
      intro h1
      apply htQ2
      have h2 : p ⟨t, htH⟩ = 1 := by
        apply e.injective
        rw [map_one]
        exact h1
      have h3 : (⟨t, htH⟩ : ↥(L2 ⊔ S)) ∈ CFSG.Open.pCore 2 ↥(L2 ⊔ S) :=
        (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥(L2 ⊔ S)) _).mp h2
      have h4 : t ∈ pCoreOf 2 (L2 ⊔ S) := (CFSG.mem_openPCoreOf_iff ⟨t, htH⟩).mpr h3
      rwa [hpCore2] at h4
    have hnum1' := hnum1 ā hā1 hā2
    have hfixT : Nat.card
        (CFSG.QuasithinUnique.Setup.X7.fixedSub ρ (Subgroup.zpowers ā)) =
        Nat.card ↥(Y ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) := by
      have h := fixSub_chiefMod_bot_card (H := L2 ⊔ S) (U := Y) (W := Y) (m := 3)
        hstep hYH hE e (Subgroup.zpowers (⟨t, htH⟩ : ↥(L2 ⊔ S)))
      simp only [MonoidHom.map_zpowers] at h
      rw [← card_fixSub_eq_card_fixedSub ρ (Subgroup.zpowers ā)]
      simpa [ρ, ā, φ, p] using h
    have hcentT : Subgroup.centralizer (Subgroup.zpowers t : Set G) =
        Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hY16 : Nat.card ↥Y =
        16 * Nat.card ↥(Y ⊓ Subgroup.centralizer ({t} : Set G)) := by
      rw [← hWYeq, hnum1', hfixT, hcentT]
    have hrelmul : (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y *
        Nat.card ↥(Y ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card ↥Y := by
      have h := Subgroup.relIndex_mul_card
        (H := Y ⊓ Subgroup.centralizer ({t} : Set G)) (K := Y)
      rwa [inf_of_le_left (inf_le_left)] at h
    exact eq_relIndex_of_mul_card_eq hY16 hrelmul
  have hrelA8 : ∀ A : Subgroup G, A ≤ S →
      (A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex A ≤ 8 := by
    intro A hAS
    have hinf : A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = A ⊓ Q2 L1 L2 S := by
      rw [← hSQ2, ← inf_assoc, inf_eq_left.mpr hAS]
    rw [hinf]
    have hEN : A ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      hAS.trans (hSP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
    have h := CFSG.GroupTheory.relIndex_inf_le_relIndex_of_card_sup_le
      (A := S) (B := Q2 L1 L2 S) (C := A) hQ2S hEN
      (Subgroup.card_le_of_le (sup_le hQ2S hAS))
    rw [str86_relIndex_q2_s hF hB (by norm_num) hL2'] at h
    rwa [inf_comm] at h
  have hmonoZ : ∀ t : G, (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y ≤
      (Z2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z2 L1 L2 S) := by
    intro t
    have h1 : (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y =
        (Subgroup.centralizer ({t} : Set G)).relIndex Y := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    have h2 : (Z2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
        (Z2 L1 L2 S) = (Subgroup.centralizer ({t} : Set G)).relIndex (Z2 L1 L2 S) := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h1, h2]
    exact Subgroup.relIndex_le_of_le_right hYZ (D15Proof.relIndex_ne_zero _ _)
  have hnff : ¬ IsFFInt (L2 ⊔ S) (Z2 L1 L2 S) hVz2 := by
    apply not_isFFInt_of_disp_sub (hV := hVz2) (hG₁V := hG1Z) (hT := hSyl)
    intro A hAS hquad hAnc
    obtain ⟨t, htA, htC⟩ : ∃ t ∈ A, t ∉ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
      by_contra h
      push Not at h
      exact hAnc fun x hx => h x hx
    have htS : t ∈ S := hAS htA
    have httC : t * t ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) := (hquad t htA t htA).2
    have h16 := hdispInv t htS httC htC
    have hA8 := hrelA8 A hAS
    have hZ : (8 : ℕ) <
        (Z2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z2 L1 L2 S) := by
      calc (8 : ℕ) < 16 := by norm_num
        _ = (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y := h16.symm
        _ ≤ (Z2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z2 L1 L2 S) :=
            hmonoZ t
    exact ⟨t, htA, htC, lt_of_le_of_lt hA8 hZ⟩
  have hndual : ¬ IsDualFFInt (L2 ⊔ S) (Z2 L1 L2 S) hVz2 := by
    apply not_isDualFFInt_of_disp_sub (hV := hVz2) (hG₁V := hG1Z) (hT := hSyl)
    intro A hAS hquad hAnc
    obtain ⟨t, htA, htC⟩ : ∃ t ∈ A, t ∉ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
      by_contra h
      push Not at h
      exact hAnc fun x hx => h x hx
    have htS : t ∈ S := hAS htA
    have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) htS
    have httC : t * t ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) := (hquad t htA t htA).2
    have htNY : t ∈ Subgroup.normalizer (Y : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hstep.1.2 t htH x hx
      · intro hx
        have h1 : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ ∈ Y :=
          hstep.1.2 t⁻¹ ((L2 ⊔ S).inv_mem htH) _ hx
        have h2 : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
        rwa [h2] at h1
    have h16 := hdispInv t htS httC htC
    have hA8 := hrelA8 A hAS
    have hcomm0 := CFSG.Quasithin.MS93.S38EA.relIndex_le_card_commutator
      (U := Y) (t := t) (fun a ha b hb => CFSG.Open.IsElemAbelian.comm hV ha hb) htNY
    have hcentT : Subgroup.centralizer (Subgroup.zpowers t : Set G) =
        Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hcomm : (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y ≤
        Nat.card (⁅Z2 L1 L2 S, A⁆ : Subgroup G) := by
      have h1 : (Subgroup.centralizer (Subgroup.zpowers t : Set G)).relIndex Y =
          (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y := by
        rw [hcentT, inf_comm, Subgroup.inf_relIndex_right]
      rw [← h1]
      exact hcomm0.trans (Subgroup.card_le_of_le
        (Subgroup.commutator_mono hYZ (Subgroup.zpowers_le.mpr htA)))
    calc (A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex A
        ≤ 8 := hA8
      _ < 16 := by norm_num
      _ = (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y := h16.symm
      _ ≤ Nat.card (⁅Z2 L1 L2 S, A⁆ : Subgroup G) := hcomm
  have hQrc : QrcHV L1 L2 S := by
    intro E hEQ1 hEe hEnc
    rw [hpCore1] at hEQ1
    have hES : E ≤ S := hEQ1.trans hQ1S
    have hEH : E ≤ L2 ⊔ S := hES.trans le_sup_right
    have hESN : E ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      hES.trans (hSP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
    let Ē : Subgroup SL(2, GaloisField 2 3) := (E.subgroupOf (L2 ⊔ S)).map φ
    have hĒ2 : ∀ a ∈ Ē, a * a = 1 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_mul]
      have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
      have hsq : (x : G) * (x : G) ∈ Q2 L1 L2 S := by
        rw [← hSQ2]
        exact Subgroup.mem_inf.mpr ⟨S.mul_mem (hES hxE) (hES hxE), by
          rw [show (x : G) * (x : G) = 1 from by
            rw [← pow_two]; exact hEe.2 (x : G) hxE]
          exact Subgroup.one_mem _⟩
      have hker : x * x ∈ φ.ker := by
        rw [hkerφ]
        exact (CFSG.mem_openPCoreOf_iff (x * x)).mp (by rw [hpCore2]; simpa using hsq)
      have h1 : φ (x * x) = 1 := by
        have := hker
        rwa [MonoidHom.mem_ker] at this
      exact h1
    have hĒne : Ē ≠ ⊥ := by
      intro hbot
      apply hEnc
      intro x hx
      have hxE : x ∈ E := hx
      have hxH : x ∈ L2 ⊔ S := hEH hx
      have hxker : (⟨x, hxH⟩ : ↥(L2 ⊔ S)) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        have himg : φ ⟨x, hxH⟩ ∈ Ē :=
          Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hxE)
        rw [hbot] at himg
        exact Subgroup.mem_bot.mp himg
      rw [hkerφ] at hxker
      have hxQ2 : x ∈ Q2 L1 L2 S := by
        have := (CFSG.mem_openPCoreOf_iff ⟨x, hxH⟩).mpr hxker
        rwa [hpCore2] at this
      exact hQ2Z hxQ2
    have hcardĒ : Nat.card Ē = (E ⊓ Q2 L1 L2 S).relIndex E := by
      have h1 := CFSG.Quasithin.Ch3E215M.card_map_eq_relIndex_ker φ (E.subgroupOf (L2 ⊔ S))
      rw [hkerφ] at h1
      have h2 : (CFSG.Open.pCore 2 ↥(L2 ⊔ S)).relIndex (E.subgroupOf (L2 ⊔ S)) =
          (E ⊓ pCoreOf 2 (L2 ⊔ S)).relIndex E := by
        have hsub : (pCoreOf 2 (L2 ⊔ S)).subgroupOf (L2 ⊔ S) =
            CFSG.Open.pCore 2 ↥(L2 ⊔ S) := by
          unfold pCoreOf Subgroup.subgroupOf
          exact Subgroup.comap_map_eq_self_of_injective (L2 ⊔ S).subtype_injective _
        rw [← hsub, Subgroup.relIndex_subgroupOf hEH,
          ← Subgroup.inf_relIndex_right (pCoreOf 2 (L2 ⊔ S)) E, inf_comm]
      rw [h2, hpCore2] at h1
      simpa [Ē, φ, Subgroup.map_map] using h1.symm
    have hk8 : (E ⊓ Q2 L1 L2 S).relIndex E ≤ 8 := by
      have h := CFSG.GroupTheory.relIndex_inf_le_relIndex_of_card_sup_le
        (A := S) (B := Q2 L1 L2 S) (C := E) hQ2S hESN
        (Subgroup.card_le_of_le (sup_le hQ2S hES))
      rw [str86_relIndex_q2_s hF hB (by norm_num) hL2'] at h
      rwa [inf_comm] at h
    have hkne : (E ⊓ Q2 L1 L2 S).relIndex E ≠ 1 := by
      intro h1
      apply hEnc
      have hle : E ≤ E ⊓ Q2 L1 L2 S := (Subgroup.relIndex_eq_one).mp h1
      intro x hx
      exact hQ2Z (Subgroup.mem_inf.mp (hle hx)).2
    have hcases : (E ⊓ Q2 L1 L2 S).relIndex E = 2 ∨
        (E ⊓ Q2 L1 L2 S).relIndex E = 4 ∨ (E ⊓ Q2 L1 L2 S).relIndex E = 8 := by
      have hpg : IsPGroup 2 ↥Ē := fun a => ⟨1, by
        have h2 : (2 : ℕ) ^ 1 = 2 := rfl
        rw [h2, pow_two]
        exact Subtype.ext (hĒ2 a a.2)⟩
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hpg
      have hk_eq : (E ⊓ Q2 L1 L2 S).relIndex E = 2 ^ j := by rw [← hcardĒ, hj]
      have hgt : 1 < Nat.card Ē := (Subgroup.one_lt_card_iff_ne_bot Ē).mpr hĒne
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · exfalso
          rw [h0] at hj
          have h1 : Nat.card Ē = 1 := by simpa using hj
          omega
        · exact hpos
      have hjle : j ≤ 3 := by
        have h : 2 ^ j ≤ 2 ^ 3 := by
          rw [← hj, hcardĒ]
          norm_num
          exact hk8
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
      interval_cases j
      · left; rw [hk_eq]; norm_num
      · right; left; rw [hk_eq]; norm_num
      · right; right; rw [hk_eq]; norm_num
    have hfixE : Nat.card (CFSG.QuasithinUnique.Setup.X7.fixedSub ρ Ē) =
        Nat.card ↥(Y ⊓ Subgroup.centralizer (E : Set G)) := by
      rw [← card_fixSub_eq_card_fixedSub ρ Ē]
      have h := fixSub_chiefMod_bot_card (H := L2 ⊔ S) (U := Y) (W := Y) (m := 3)
        hstep hYH hE e (E.subgroupOf (L2 ⊔ S))
      rw [Subgroup.map_subgroupOf_eq_of_le hEH] at h
      simpa [Ē, φ, ρ, Subgroup.map_map] using h
    have hrelY : (Y ⊓ Subgroup.centralizer (E : Set G)).relIndex Y *
        Nat.card ↥(Y ⊓ Subgroup.centralizer (E : Set G)) = Nat.card ↥Y := by
      have h := Subgroup.relIndex_mul_card
        (H := Y ⊓ Subgroup.centralizer (E : Set G)) (K := Y)
      rwa [inf_of_le_left (inf_le_left)] at h
    have hmonoE : (Y ⊓ Subgroup.centralizer (E : Set G)).relIndex Y ≤
        (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact Subgroup.relIndex_le_of_le_right hYZ (D15Proof.relIndex_ne_zero _ _)
    have hboundY : (E ⊓ Q2 L1 L2 S).relIndex E ^ 2 ≤
        (Y ⊓ Subgroup.centralizer (E : Set G)).relIndex Y := by
      rcases hcases with hk2 | hk4 | hk8
      ·
        obtain ⟨t, htE, htQ2⟩ : ∃ t ∈ E, t ∉ Q2 L1 L2 S := by
          by_contra h
          push Not at h
          exact hkne ((Subgroup.relIndex_eq_one).mpr fun x hx =>
            Subgroup.mem_inf.mpr ⟨hx, h x hx⟩)
        have htS : t ∈ S := hES htE
        have htC : t ∉ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
          intro h
          exact htQ2 (by rw [← hSQ2]; exact Subgroup.mem_inf.mpr ⟨htS, h⟩)
        have httC : t * t ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
          rw [show t * t = 1 from by rw [← pow_two]; exact hEe.2 t htE]
          exact Subgroup.one_mem _
        have h16 := hdispInv t htS httC htC
        have hle : (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y ≤
            (Y ⊓ Subgroup.centralizer (E : Set G)).relIndex Y :=
          Subgroup.relIndex_le_of_le_left
            (inf_le_inf le_rfl (Subgroup.centralizer_le (by
              intro x hx
              rw [Set.mem_singleton_iff] at hx
              exact hx ▸ htE)))
            (D15Proof.relIndex_ne_zero _ _)
        calc (E ⊓ Q2 L1 L2 S).relIndex E ^ 2 = 4 := by rw [hk2]; norm_num
          _ ≤ 16 := by norm_num
          _ = (Y ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Y := h16.symm
          _ ≤ (Y ⊓ Subgroup.centralizer (E : Set G)).relIndex Y := hle
      ·
        have hA4 : Nat.card Ē = 4 := by rw [hcardĒ, hk4]
        have hb := hnum4 Ē hĒne hĒ2 hA4
        have hb' : 64 * Nat.card ↥(Y ⊓ Subgroup.centralizer (E : Set G)) ≤
            Nat.card ↥Y := by
          rw [← hfixE, ← hWYeq]
          exact hb
        have h64 := le_relIndex_of_mul_card_le hb' hrelY
        calc (E ⊓ Q2 L1 L2 S).relIndex E ^ 2 = 16 := by rw [hk4]; norm_num
          _ ≤ 64 := by norm_num
          _ ≤ (Y ⊓ Subgroup.centralizer (E : Set G)).relIndex Y := h64
      ·
        have hA8 : Nat.card Ē = 8 := by rw [hcardĒ, hk8]
        have hb := hnum8 Ē hĒne hĒ2 hA8
        have hb' : 128 * Nat.card ↥(Y ⊓ Subgroup.centralizer (E : Set G)) ≤
            Nat.card ↥Y := by
          rw [← hfixE, ← hWYeq]
          exact hb
        have h128 := le_relIndex_of_mul_card_le hb' hrelY
        calc (E ⊓ Q2 L1 L2 S).relIndex E ^ 2 = 64 := by rw [hk8]; norm_num
          _ ≤ 128 := by norm_num
          _ ≤ (Y ⊓ Subgroup.centralizer (E : Set G)).relIndex Y := h128
    have hCeq : (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E =
        (E ⊓ Q2 L1 L2 S).relIndex E := by
      have h1 : (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E =
          (E ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E := by
        rw [inf_comm, Subgroup.inf_relIndex_right]
      rw [h1]
      have hinfE : E ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = E ⊓ Q2 L1 L2 S := by
        rw [← hSQ2, ← inf_assoc, inf_eq_left.mpr hES]
      rw [hinfE]
    rw [hCeq]
    exact hboundY.trans hmonoE
  exact str83_st8_false hF hB (by norm_num) hSz hL2 hZI hJ1 hQrc hnff hndual

end CFSG.Quasithin.Stroth

end
