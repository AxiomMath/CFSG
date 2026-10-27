module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Exponent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2(d--e): Fitting infrastructure

This file contains the source-independent nilpotent core decomposition used
to package the Fitting argument.  The later source-specific centralization
step remains an implication-shaped earlier-book boundary; no conclusion of
Proposition 10.2 is used here.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u

/-- A finite nilpotent group is the internal direct product of its `p`-core
and its `p'`-core. -/
public theorem proposition102_nilpotent_internalDirectProduct_pCore_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q]
    (p : ℕ) (hp : Nat.Prime p) (hnil : Group.IsNilpotent Q) :
    Section2.IsInternalDirectProduct (⊤ : Subgroup Q)
      (pCore p Q) (pPrimeCore p Q) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsup : pCore p Q ⊔ pPrimeCore p Q = (⊤ : Subgroup Q) :=
    top_unique (nilpotent_top_le_pCore_sup_pPrimeCore hnil)
  have hcop : Nat.Coprime (Nat.card (pCore p Q))
      (Nat.card (pPrimeCore p Q)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := Q) (p := p)).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (G := Q) (p := p)).pow_left n
  have hinf : pCore p Q ⊓ pPrimeCore p Q = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime hcop
  refine
    { left_le := le_top
      right_le := le_top
      commute := ?_
      inf_eq_bot := hinf
      mul_surjective := ?_ }
  · intro x hx y hy
    exact (Subgroup.commute_of_normal_of_disjoint
      (pCore p Q) (pPrimeCore p Q)
      (inferInstance : (pCore p Q).Normal)
      (pPrimeCore_normal (G := Q) (p := p))
      (disjoint_iff.mpr hinf) x y hx hy).eq
  · intro q hq
    have hqSup : q ∈ pCore p Q ⊔ pPrimeCore p Q := by
      rw [hsup]
      exact hq
    rcases Subgroup.mem_sup_of_normal_right.mp hqSup with
      ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hxy.symm⟩

/-- A normal nilpotent subgroup is contained in the Fitting subgroup. -/
public theorem proposition102_normal_nilpotent_le_fitting
    {Q : Type u} [Group Q] {N : Subgroup Q}
    (hNnormal : N.Normal) (hNnil : Group.IsNilpotent N) :
    N ≤ fittingSubgroup Q := by
  exact le_sSup ⟨hNnormal, hNnil⟩

/-- Transport an internal direct product from a subgroup to its ambient
subgroup image. -/
public theorem proposition102_internalDirectProduct_map_subtype_top
    {G : Type u} [Group G] {C : Subgroup G} {H K : Subgroup C}
    (h : Section2.IsInternalDirectProduct (⊤ : Subgroup C) H K) :
    Section2.IsInternalDirectProduct C (H.map C.subtype) (K.map C.subtype) := by
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    rcases hx with ⟨h0, _hh0, rfl⟩
    exact h0.property
  · intro x hx
    rcases hx with ⟨k0, _hk0, rfl⟩
    exact k0.property
  · intro x hx y hy
    rcases hx with ⟨h0, hh0, rfl⟩
    rcases hy with ⟨k0, hk0, rfl⟩
    exact congrArg Subtype.val (h.commute h0 hh0 k0 hk0)
  · apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨h0, hh0, hhx⟩
      rcases hx.2 with ⟨k0, hk0, hkx⟩
      have hhk : h0 = k0 := by
        apply Subtype.ext
        exact hhx.trans hkx.symm
      have h0inf : h0 ∈ H ⊓ K := by
        exact ⟨hh0, by simpa [hhk] using hk0⟩
      have h0bot : h0 ∈ (⊥ : Subgroup C) := by
        simpa [h.inf_eq_bot] using h0inf
      have h0one : h0 = 1 := by simpa using h0bot
      have hvalone : (h0 : G) = 1 := congrArg Subtype.val h0one
      exact hhx.symm.trans hvalone
    · exact bot_le
  · intro c hc
    rcases h.mul_surjective (⟨c, hc⟩ : C) trivial with
      ⟨h0, hh0, k0, hk0, hck⟩
    refine ⟨(h0 : G), ⟨h0, hh0, rfl⟩,
      (k0 : G), ⟨k0, hk0, rfl⟩, ?_⟩
    exact congrArg Subtype.val hck

/-- A normal Sylow subgroup is the corresponding prime core. -/
public theorem proposition102_normal_sylow_eq_pCore
    {G : Type u} [Group G] [Finite G]
    {r : ℕ} (hr : r.Prime) (P : Sylow r G)
    (hPnormal : (P : Subgroup G).Normal) :
    pCore r G = (P : Subgroup G) := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : Unique (Sylow r G) := Sylow.unique_of_normal P hPnormal
  apply le_antisymm
  · obtain ⟨Q, hcoreQ⟩ :=
      (pCore_isPGroup (p := r) (G := G)).exists_le_sylow
    simpa [Subsingleton.elim Q P] using hcoreQ
  · exact le_sSup ⟨hPnormal, P.isPGroup'⟩

/-- If `R` is a normal Sylow `r`-subgroup of `V`, the ambient Fitting
subgroup of `V` splits internally as `R` times its `r'`-core. -/
public theorem proposition102_fitting_internalDirectProduct_of_normal_sylow
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} {V R : Subgroup X}
    (hr : r.Prime)
    (hRV : R ≤ V)
    (hRsyl : theorem4bIsSylowSubgroupOf r R V)
    (hRnormal : (R.subgroupOf V).Normal) :
    ∃ Q : Subgroup X,
      Section2.IsInternalDirectProduct (fittingSubgroupOf V) R Q ∧
      Q = (pPrimeCore r (fittingSubgroupOf V)).map
        (fittingSubgroupOf V).subtype := by
  letI : Fact r.Prime := ⟨hr⟩
  let F : Subgroup X := fittingSubgroupOf V
  have hRnil : Group.IsNilpotent R := by
    exact IsPGroup.isNilpotent (by
      rcases hRsyl with ⟨S, hS⟩
      have hSp : IsPGroup r R := by
        rw [hS]
        exact S.isPGroup'.map V.subtype
      exact hSp)
  have hRnilV : Group.IsNilpotent (R.subgroupOf V) := by
    exact nilpotent_of_mulEquiv (_h := hRnil)
      (Subgroup.subgroupOfEquivOfLe hRV).symm
  have hRF : R ≤ F := by
    have hRFsubV : R.subgroupOf V ≤ fittingSubgroup V :=
      le_sSup ⟨hRnormal, hRnilV⟩
    simpa [F, fittingSubgroupOf, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hRV] using
      (Subgroup.map_mono (f := V.subtype) hRFsubV)
  have hRsylF : theorem4bIsSylowSubgroupOf r R F :=
    theorem4bIsSylowSubgroupOf_of_between hr hRsyl hRF
      (fittingSubgroupOf_le V)
  rcases hRsylF with ⟨SF, hSF⟩
  have hRFsub : R.subgroupOf F = (SF : Subgroup F) := by
    rw [hSF]
    exact subgroupOf_map_subtype_eq (SF : Subgroup F)
  have hSFnormal : (SF : Subgroup F).Normal :=
    Group.IsNilpotent.sylow_normal
      (fittingSubgroupOf_isNilpotent V) r SF
  have hpcore : pCore r F = R.subgroupOf F := by
    exact (proposition102_normal_sylow_eq_pCore hr SF hSFnormal).trans
      hRFsub.symm
  have hprod0 :=
    proposition102_nilpotent_internalDirectProduct_pCore_pPrimeCore r hr
      (fittingSubgroupOf_isNilpotent V)
  let QF : Subgroup F := pPrimeCore r F
  let Q : Subgroup X := QF.map F.subtype
  have hprodX := proposition102_internalDirectProduct_map_subtype_top
      (G := X) (C := F) hprod0
  refine ⟨Q, ?_, rfl⟩
  simpa [Q, F, hpcore, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hRF] using hprodX

/-- The A-times-B centralization step in the source Fitting argument is an
implication of the checked nilpotent coprime-action theorem. -/
public theorem proposition102_commutator_eq_bot_of_coprime_centralizer
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} [Fact r.Prime]
    {S R Q : Subgroup X}
    (hSr : IsPGroup r S)
    (hRS : R ≤ S)
    (hQnormS : Q ≤ Subgroup.normalizer (S : Set X))
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card S))
    (hQR : ⁅Q, R⁆ = ⊥)
    (hQCR : Q ≤ Subgroup.centralizer (subgroupCentralizerIn S R : Set X)) :
    ⁅Q, S⁆ = ⊥ := by
  letI : Subgroup.Normalizes Q S := ⟨hQnormS⟩
  have hnil : Group.IsNilpotent S := IsPGroup.isNilpotent hSr
  have hR_le_CQ : R ≤ subgroupCentralizerIn S Q := by
    have hQ_le_CR : Q ≤ Subgroup.centralizer (R : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQR
    have hR_le_CQ' : R ≤ Subgroup.centralizer (Q : Set X) :=
      (Subgroup.le_centralizer_iff (H := Q) (K := R)).mp hQ_le_CR
    intro x hx
    exact ⟨hRS hx, hR_le_CQ' hx⟩
  have hCR_le_CQ : subgroupCentralizerIn S R ≤ subgroupCentralizerIn S Q := by
    have hCR_le_centQ :
        subgroupCentralizerIn S R ≤ Subgroup.centralizer (Q : Set X) :=
      (Subgroup.le_centralizer_iff
        (H := Q) (K := subgroupCentralizerIn S R)).mp hQCR
    intro x hx
    exact ⟨hx.1, hCR_le_centQ hx⟩
  have hfixed :
      fixedPointSubgroup (↥Q) (↥S) =
        (subgroupCentralizerIn S Q).subgroupOf S :=
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn S Q hQnormS
  have hC :
      Subgroup.centralizer (fixedPointSubgroup (↥Q) (↥S) : Set S) ≤
        fixedPointSubgroup (↥Q) (↥S) := by
    rw [hfixed]
    intro x hx
    have hx_cent_R : (x : X) ∈ Subgroup.centralizer (R : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyCQ : y ∈ subgroupCentralizerIn S Q := hR_le_CQ hy
      have hySub : (⟨y, hRS hy⟩ : S) ∈
          (subgroupCentralizerIn S Q).subgroupOf S := hyCQ
      have hxy : (⟨y, hRS hy⟩ : S) * x =
          x * ⟨y, hRS hy⟩ :=
        Subgroup.mem_centralizer_iff.mp hx _ hySub
      exact congrArg Subtype.val hxy
    have hxCR : (x : X) ∈ subgroupCentralizerIn S R :=
      ⟨x.2, hx_cent_R⟩
    exact hCR_le_CQ hxCR
  have htriv : ActsTrivially (A := Q) (G := S) :=
    proposition_1_10 hnil hcop hC
  exact commutator_eq_bot_of_actsTrivially_subgroup_conj S Q hQnormS htriv

end CFSG.BenderSuzuki
