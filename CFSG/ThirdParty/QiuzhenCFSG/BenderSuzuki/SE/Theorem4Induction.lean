module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.lemma_11_1_a

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 4(b), Proposition 6.3 induction boundary

The generic Proposition 6.3 infrastructure lives in `Theorem4`.  The
`[II4; 3.2(b)]` quotient step needs the genuine proper-subgroup induction
hypothesis for Theorem SE, together with the Borel recognition API.  Keeping
this adapter downstream avoids an import cycle through `Interfaces`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

private theorem sq_eq_one_mem_normal_sylow_two
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (hPnormal : (P : Subgroup G).Normal)
    {x : G} (hx : x ^ 2 = 1) : x ∈ (P : Subgroup G) := by
  by_cases hxone : x = 1
  · simpa [hxone] using (P : Subgroup G).one_mem
  · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have horder : orderOf x = 2 := orderOf_eq_prime hx hxone
    have hzp : IsPGroup 2 (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1)
      simpa [Nat.card_zpowers, horder]
    obtain ⟨Q, hzpQ⟩ := hzp.exists_le_sylow
    letI : Unique (Sylow 2 G) := Sylow.unique_of_normal P hPnormal
    have hQP : Q = P := Subsingleton.elim _ _
    rw [hQP] at hzpQ
    exact hzpQ (Subgroup.mem_zpowers x)

/-- The checked `[II4; 3.2(b)]` consequence, using the proper-subgroup
Theorem-SE conclusion supplied by strong induction. -/
public theorem theorem4bProposition63_II4b_image_isPGroup
    {X : Type u} [Group X] [Finite X] {M L : Subgroup X}
    (hConclusion : TheoremSEConclusion (M.comap L.subtype))
    (hLcore : L = (involutionCore L).map L.subtype)
    (hrankML : TwoRankAtLeastTwo (M.comap L.subtype))
    (hcoreL : (involutionCore M).map M.subtype ≤ L) :
    IsPGroup 2 (theorem4bProposition63CoreQuotientMap hcoreL).range := by
  let ML : Subgroup L := M.comap L.subtype
  have hLcoreTop : involutionCore L = ⊤ := by
    apply Subgroup.map_injective (f := L.subtype) Subtype.val_injective
    calc
      (involutionCore L).map L.subtype = L := hLcore.symm
      _ = (⊤ : Subgroup L).map L.subtype := by
        simpa [MonoidHom.range_eq_map] using
          (Subgroup.range_subtype (H := L)).symm
  have hrankL : TwoRankAtLeastTwo L :=
    hrankML.map_of_injective ML.subtype Subtype.val_injective
  let eCore : involutionCore L ≃* L :=
    (MulEquiv.subgroupCongr hLcoreTop).trans Subgroup.topEquiv
  have hrankCore : TwoRankAtLeastTwo (involutionCore L) :=
    hrankL.map_of_injective eCore.symm.toMonoidHom eCore.symm.injective
  have hSE : TheoremSEBenderConclusion ML := by
    change ¬ TwoRankAtLeastTwo (involutionCore L) ∨
      TheoremSEBenderConclusion ML at hConclusion
    exact hConclusion.resolve_left (fun h => h hrankCore)
  let C : Subgroup L := involutionCore L
  let e : C ≃* L := eCore
  have hcoremap :
      (twoPrimeCore C).map e.toMonoidHom = twoPrimeCore L := by
    simpa [twoPrimeCore] using
      (pPrimeCore_map_iso (p := 2) e)
  letI : ((twoPrimeCore C).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (inferInstance : (twoPrimeCore C).Normal)
      e.toMonoidHom e.surjective
  let q0 : (C ⧸ twoPrimeCore C) ≃*
      (L ⧸ (twoPrimeCore C).map e.toMonoidHom) :=
    quotientMulEquivOfMulEquiv e (twoPrimeCore C)
  let qeq : (L ⧸ (twoPrimeCore C).map e.toMonoidHom) ≃*
      (L ⧸ twoPrimeCore L) :=
    QuotientGroup.quotientMulEquivOfEq hcoremap
  let qe : (C ⧸ twoPrimeCore C) ≃* (L ⧸ twoPrimeCore L) :=
    q0.trans qeq
  change TheoremSEBenderConclusion ML at hSE
  dsimp [TheoremSEBenderConclusion] at hSE
  change IsSimpleBenderGroup (C ⧸ twoPrimeCore C) ∧ _ at hSE
  let Q : Type u := L ⧸ twoPrimeCore L
  let q : L →* Q := QuotientGroup.mk' (twoPrimeCore L)
  let B : Subgroup Q := ML.map q
  have hbender : IsSimpleBenderGroup Q := by
    exact hSE.1.map_mulEquiv qe
  let BC : Subgroup C := (ML ⊓ C).subgroupOf C
  let qC : C →* (C ⧸ twoPrimeCore C) :=
    QuotientGroup.mk' (twoPrimeCore C)
  have hBCmap : BC.map e.toMonoidHom = ML := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc.1
    · intro hx
      let c : C := e.symm x
      refine ⟨c, ?_, by simp [c, e]⟩
      have hxe : e c ∈ ML := by
        change x ∈ ML
        exact hx
      exact ⟨by
        change (e c : L) ∈ ML
        exact hxe, c.property⟩
  have hqcomp : qe.toMonoidHom.comp qC =
      q.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro c
    change qe (QuotientGroup.mk c) = QuotientGroup.mk (e c)
    have hq0c : q0 (QuotientGroup.mk c) = QuotientGroup.mk (e c) := by
      exact quotientMulEquivOfMulEquiv_mk e (twoPrimeCore C) c
    have hqeqc : qeq (QuotientGroup.mk (e c)) =
        QuotientGroup.mk (e c) := by
      exact QuotientGroup.quotientMulEquivOfEq_mk hcoremap (e c)
    rw [show qe (QuotientGroup.mk c) =
      qeq (q0 (QuotientGroup.mk c)) by rfl, hq0c, hqeqc]
  let B0 : Subgroup (C ⧸ twoPrimeCore C) := BC.map qC
  have hBmap : B0.map qe.toMonoidHom = B := by
    calc
      B0.map qe.toMonoidHom =
          BC.map (qe.toMonoidHom.comp qC) := by
            simp [B0, Subgroup.map_map]
      _ = BC.map (q.comp e.toMonoidHom) := by rw [hqcomp]
      _ = (BC.map e.toMonoidHom).map q := by
            simp [Subgroup.map_map]
      _ = B := by rw [hBCmap]
  have hBorel : IsBorelSubgroup B := by
    rw [← hBmap]
    exact hSE.2.2.map_mulEquiv qe
  obtain ⟨P, hPnormal, _hPregular⟩ :=
    simpleBender_borel_normalSylow_regular hBorel hbender
  let PB : Subgroup Q := (P : Subgroup B).map B.subtype
  have hPBp : IsPGroup 2 PB := P.isPGroup'.map B.subtype
  apply hPBp.to_le
  rintro y ⟨c, rfl⟩
  let f : involutionCore M →* Q :=
    theorem4bProposition63CoreQuotientMap hcoreL
  have hfB : ∀ c : involutionCore M, f c ∈ B := by
    intro c
    let cL : L :=
      ⟨((c : M) : X), hcoreL
        (Subgroup.mem_map_of_mem M.subtype c.property)⟩
    have hcML : cL ∈ ML := by
      exact (c : M).property
    refine Subgroup.mem_map.mpr ⟨cL, hcML, ?_⟩
    simpa only [f, q, cL] using
      (theorem4bProposition63CoreQuotientMap_apply hcoreL c).symm
  have hgen : involutionCore (involutionCore M) = ⊤ :=
    involutionCore_involutionCore_eq_top M
  have hcCore : c ∈ involutionCore (involutionCore M) := by
    exact (le_of_eq hgen.symm) (Subgroup.mem_top c)
  have hcClosure :
      c ∈ Subgroup.closure (involutionsSet (involutionCore M)) :=
    (le_of_eq (involutionCore_eq_closure (involutionCore M))) hcCore
  refine Subgroup.closure_induction
    (p := fun c _hc => f c ∈ PB) ?_ ?_ ?_ ?_ hcClosure
  · intro x hx
    let xB : B := ⟨f x, hfB x⟩
    have hxSq : xB ^ 2 = 1 := by
      apply Subtype.ext
      simpa [xB] using congrArg f hx.sq_eq_one
    have hxP : xB ∈ (P : Subgroup B) :=
      sq_eq_one_mem_normal_sylow_two P hPnormal hxSq
    exact Subgroup.mem_map.mpr ⟨xB, hxP, rfl⟩
  · simpa [f, PB] using PB.one_mem
  · intro x y _hx _hy hxPB hyPB
    simpa using PB.mul_mem hxPB hyPB
  · intro x _hx hxPB
    simpa using PB.inv_mem hxPB

/-- The residual containment after the checked `[II4; 3.2(b)]` image step. -/
public theorem theorem4bProposition63Residual_map_le_twoPrimeCore
    {X : Type u} [Group X] [Finite X] {M L : Subgroup X}
    (hConclusion : TheoremSEConclusion (M.comap L.subtype))
    (hLcore : L = (involutionCore L).map L.subtype)
    (hrankML : TwoRankAtLeastTwo (M.comap L.subtype))
    (hcoreL : (involutionCore M).map M.subtype ≤ L) :
    (theorem4bProposition63Residual M).map M.subtype ≤
      (twoPrimeCore L).map L.subtype := by
  apply theorem4bProposition63Residual_map_le_twoPrimeCore_of_image_isPGroup
    hcoreL
  exact theorem4bProposition63_II4b_image_isPGroup
    hConclusion hLcore hrankML hcoreL

/-- Proposition 6.3.  The only minimal-counterexample input is the genuine
Theorem-SE conclusion for strongly embedded subgroups of proper subgroups. -/
public theorem IsStronglyEmbedded.theorem4bProposition63
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixA M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    {t : X} (ht : IsInvolution t) (htM : t ∉ M) :
    theorem4bProposition63Subgroup M d.z t = ⊤ := by
  classical
  let L : Subgroup X := theorem4bProposition63Subgroup M d.z t
  by_contra hLproper
  let D : Subgroup X := M ⊓ rightConjugate M t
  let Y : Subgroup X :=
    (theorem4bProposition63Residual M).map M.subtype
  let O : Subgroup D := twoPrimeCore D
  let OX : Subgroup X := O.map D.subtype
  have hcoreL : (involutionCore M).map M.subtype ≤ L :=
    hM.theorem4bProposition63_involutionCore_le
      d.hzM d.hz ht htM
  have hrankML : TwoRankAtLeastTwo (M.comap L.subtype) :=
    theorem4bProposition63_twoRank_comap hrank hcoreL
  have hML : IsStronglyEmbedded (M.comap L.subtype) :=
    hM.theorem4bProposition63_comap d.hzM d.hz ht htM
  have hLcore : L = (involutionCore L).map L.subtype := by
    exact theorem4bProposition63Subgroup_eq_involutionCore d.hz ht
  have hConclusion : TheoremSEConclusion (M.comap L.subtype) :=
    hinduction L hLproper (M.comap L.subtype) hML
  have hYleOddL :
      Y ≤ (twoPrimeCore L).map L.subtype := by
    exact theorem4bProposition63Residual_map_le_twoPrimeCore
      hConclusion hLcore hrankML hcoreL
  have hOddLleD :
      (twoPrimeCore L).map L.subtype ≤ D := by
    exact hM.theorem4bProposition63_twoPrimeCore_le_D
      d.hzM d.hz ht htM hrank
  have hYleD : Y ≤ D := hYleOddL.trans hOddLleD
  have hbetaNe :
      (QuotientGroup.mk t : conjugateCosetSpace M) ≠
        QuotientGroup.mk 1 := by
    intro h
    apply htM
    simpa [ht.inv_eq_self] using QuotientGroup.eq.mp h
  have hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2 :=
    hM.theorem4bProposition63_not_twoTransitive
      hX d ht hbetaNe hYleD
  have hDodd : Odd (Nat.card D) := by
    exact hM.inf_rightConjugate_card_odd htM
  have hOtop : O = ⊤ := by
    apply top_unique
    change (⊤ : Subgroup D) ≤ pPrimeCore 2 D
    exact le_sSup ⟨inferInstance, by simpa using hDodd.coprime_two_left⟩
  have hOXeqD : OX = D := by
    dsimp only [OX]
    rw [hOtop]
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (H := D))
  have hOodd : Odd (Nat.card O) := by
    rw [hOtop]
    simpa using hDodd
  have hOXodd : Odd (Nat.card OX) := by
    rw [hOXeqD]
    exact hDodd
  have hYleOX : Y ≤ OX := by
    rw [hOXeqD]
    exact hYleD
  have hexists : ∀ q : (Nat.card O).primeFactors.attach,
      ∃ P₀ : Sylow q.1 O,
        d.z ∈ Subgroup.normalizer
          (((((P₀ : Subgroup O).map O.subtype).map D.subtype) ⊔ Y :
            Subgroup X) : Set X) := by
    intro q
    have hq : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
    have hqdiv : (q.1 : ℕ) ∣ Nat.card O :=
      Nat.dvd_of_mem_primeFactors q.1.2
    have hqne : (q.1 : ℕ) ≠ 2 := by
      intro hqTwo
      rw [hqTwo] at hqdiv
      rcases hOodd with ⟨k, hk⟩
      omega
    have hqOdd : Odd (q.1 : ℕ) := hq.odd_of_ne_two hqne
    simpa only [D, O, Y] using
      hM.theorem4bProposition63_exists_sylow_normalized
        d.hzM d.hz ht htM hT2 hnot2 q.1 hq hqOdd
  choose P₀ hP₀norm using hexists
  let P : (Nat.card O).primeFactors.attach → Subgroup X :=
    fun q => (((P₀ q : Subgroup O).map O.subtype).map D.subtype)
  let S : Subgroup X := ⨆ q, P q ⊔ Y
  have hselected :
      (⨆ q, ((P₀ q : Sylow q.1 O) : Subgroup O)) = ⊤ :=
    iSup_selected_sylow_eq_top P₀
  have htopMapO : (⊤ : Subgroup O).map O.subtype = O := by
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (H := O))
  have hPiSup : (⨆ q, P q) = OX := by
    calc
      (⨆ q, P q) =
          ((⨆ q, ((P₀ q : Sylow q.1 O) : Subgroup O)).map
            O.subtype).map D.subtype := by
              simp only [P, Subgroup.map_iSup]
      _ = ((⊤ : Subgroup O).map O.subtype).map D.subtype := by
        rw [hselected]
      _ = O.map D.subtype := by rw [htopMapO]
      _ = OX := rfl
  have hSeq : S = OX := by
    apply le_antisymm
    · refine iSup_le ?_
      intro q
      exact sup_le
        ((le_iSup (fun r => P r) q).trans_eq hPiSup) hYleOX
    · rw [← hPiSup]
      refine iSup_mono ?_
      intro q
      exact le_sup_left
  have hzNormS : d.z ∈ Subgroup.normalizer (S : Set X) := by
    have hconj : S.conjBy d.z = S := by
      dsimp only [S]
      rw [Subgroup.conjBy, Subgroup.map_iSup]
      apply iSup_congr
      intro q
      simpa only [Subgroup.conjBy] using
        section11_conjBy_eq_of_mem_normalizer (hP₀norm q)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxconj : d.z * x * d.z⁻¹ ∈ S.conjBy d.z := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨x, hx, by simp⟩
      simpa [hconj] using hxconj
    · intro hx
      have h_inv : S.conjBy d.z⁻¹ = S := by
        simpa [hconj] using (Subgroup.conjBy_inv S d.z)
      have hxpre : x ∈ S.conjBy d.z⁻¹ := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        refine ⟨d.z * x * d.z⁻¹, hx, ?_⟩
        simp [mul_assoc]
      simpa [h_inv] using hxpre
  have hzNormOX : d.z ∈ Subgroup.normalizer (OX : Set X) := by
    rw [← hSeq]
    exact hzNormS
  let H : Subgroup X := OX ⊔ Subgroup.zpowers d.z
  have hinvolutionH : ∀ {y : X}, y ∈ M → IsInvolution y → y ∈ H := by
    intro y hyM hy
    obtain ⟨a, haD, hay⟩ :=
      hM.involutions_conjugate_by_inf_rightConjugate
        ht htM d.hzM d.hz hyM hy
    have haOX : a ∈ OX := by
      rw [hOXeqD]
      exact haD
    rw [← hay]
    change a⁻¹ * d.z * a ∈ H
    exact H.mul_mem
      (H.mul_mem
        (H.inv_mem (Subgroup.mem_sup_left haOX))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d.z)))
      (Subgroup.mem_sup_left haOX)
  have hcoreH : (involutionCore M).map M.subtype ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyCore, rfl⟩
    rw [involutionCore_eq_closure] at hyCore
    refine Subgroup.closure_induction
      (p := fun y : M => fun _hy => (y : X) ∈ H) ?_ ?_ ?_ ?_ hyCore
    · intro y hy
      exact hinvolutionH y.property
        (IsInvolution.map_of_injective hy M.subtype
          Subtype.val_injective)
    · exact H.one_mem
    · intro a b _ha _hb ha hb
      exact H.mul_mem ha hb
    · intro a _ha ha
      exact H.inv_mem ha
  let f : involutionCore M →* H :=
    { toFun := fun x =>
        ⟨((x : M) : X), hcoreH
          (Subgroup.mem_map_of_mem M.subtype x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : H => (q : X)) hxy
  have hrankH : TwoRankAtLeastTwo H :=
    hrank.map_of_injective f hf
  exact (not_twoRankAtLeastTwo_sup_odd_involution
    OX hOXodd d.hz hzNormOX) hrankH

end CFSG.BenderSuzuki
