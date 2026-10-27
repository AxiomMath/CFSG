module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.GL42SevenOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Fin
import CFSG.Quasithin.Background.SmithD37Fix
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Offender
import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven

open Subgroup MulAction CFSG.Quasithin

variable {U : Type} [CommGroup U] [Finite U]

omit [Finite U] in
private theorem zpow_apply_mem_of_mem_stabSub {V : Subgroup U} {g : MulAut U}
    (hgV : g ∈ stabSub V) (k : ℤ) {v : U} (hv : v ∈ V) : (g ^ k) v ∈ V :=
  (mem_stabSub.mp (Subgroup.zpow_mem (stabSub V) hgV k) v).mpr hv

omit [Finite U] in
private theorem apply_eq_self_of_card_eq_two {M : Subgroup (MulAut U)} {F : Subgroup U}
    (hMF : StableUnder M F) (hF : Nat.card F = 2) {m : MulAut U} (hm : m ∈ M) {f : U}
    (hf : f ∈ F) : m f = f := by
  by_cases hf1 : f = 1
  · simp [hf1]
  have hmf : m f ∈ F := hMF m hm f hf
  have hmf1 : m f ≠ 1 := by
    intro h
    exact hf1 (by simpa using congrArg m.symm h)
  exact CFSG.Quasithin.EmptyFaithfulMultiple.L15420.eq_of_card_eq_two hF hmf hf hmf1 hf1

private theorem ker_quotHom_comp_inclusion_eq_bot (hU2 : ∀ u : U, u ^ 2 = 1)
    {M : Subgroup (MulAut U)} (hO2 : O2Trivial M) {F : Subgroup U}
    (hMF : StableUnder M F) (hF : Nat.card F = 2) :
    ((quotHom F).comp (Subgroup.inclusion
      (CFSG.Quasithin.SmithD37.le_stabSub_of_isInvBy hMF))).ker = ⊥ := by
  let h1 : M ≤ stabSub F := CFSG.Quasithin.SmithD37.le_stabSub_of_isInvBy hMF
  let φ : ↥M →* MulAut (U ⧸ F) := (quotHom F).comp (Subgroup.inclusion h1)
  have hsq : ∀ y ∈ φ.ker, (y : MulAut U) ^ 2 = 1 := by
    intro y hy
    have hw : ∀ u : U, y.1 u / u ∈ F := by
      intro u
      have h : (QuotientGroup.mk (y.1 u) : U ⧸ F) = QuotientGroup.mk u := by
        have h := congrArg (fun ψ : MulAut (U ⧸ F) => ψ (QuotientGroup.mk u))
          (MonoidHom.mem_ker.mp hy)
        simpa [φ, h1, quotHom_mk, MulAut.one_apply] using h
      simpa [div_eq_mul_inv] using (mk_eq_mk_iff (y.1 u) u).mp h
    have hyy : ∀ u : U, y.1 (y.1 u) = u := by
      intro u
      have hfix := apply_eq_self_of_card_eq_two hMF hF y.2 (hw u)
      calc
        y.1 (y.1 u) = y.1 ((y.1 u / u) * u) := by rw [div_mul_cancel]
        _ = y.1 (y.1 u / u) * y.1 u := map_mul _ _ _
        _ = (y.1 u / u) * ((y.1 u / u) * u) := by rw [hfix, div_mul_cancel]
        _ = u := by rw [← mul_assoc, ← pow_two, hU2, one_mul]
    exact MulEquiv.ext hyy
  let P : Subgroup (MulAut U) := φ.ker.map M.subtype
  have hPle : P ≤ M := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := by
    refine CFSG.Quasithin.isPGroup_two_of_sq_eq_one fun x => ?_
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp x.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxy]
    simpa using hsq y hy
  have hPsub : P.subgroupOf M = φ.ker := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hPle]
  have hPnorm : (P.subgroupOf M).Normal := by
    rw [hPsub]
    infer_instance
  have hPbot : P = ⊥ := hO2 P hPle hPnorm hP2
  rw [← hPsub, hPbot]
  simp

private theorem false_of_card_eq_seven_or_twentyOne (h16 : Nat.card U = 16)
    {M : Subgroup (MulAut U)} {g : MulAut U} (hgM : g ∈ M) (hg : orderOf g = 7)
    {V : Subgroup U} (hV : Nat.card V = 8) (hgV : ∀ v ∈ V, g v ∈ V)
    (hMV : ¬ StableUnder M V) (hcard : Nat.card ↥M = 7 ∨ Nat.card ↥M = 21) : False := by
  let gM : ↥M := ⟨g, hgM⟩
  let Z : Subgroup ↥M := Subgroup.zpowers gM
  have hZcard : Nat.card Z = 7 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hg]
  have hZnormal : Z.Normal := by
    rcases hcard with h7 | h21
    · have htop : Z = ⊤ := Subgroup.eq_top_of_card_eq Z (by rw [hZcard, h7])
      rw [htop]
      exact Subgroup.normal_top
    · have hidx : Z.index = 3 := by
        have h := Z.card_mul_index
        rw [hZcard, h21] at h
        omega
      exact Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, h21]; norm_num)
  have hstabV : g ∈ stabSub V := CFSG.Quasithin.SmithD37.mem_stabSub_of_maps hgV
  have hstable : StableUnder M V := by
    intro m hm v hv
    let mM : ↥M := ⟨m, hm⟩
    have hconj : mM⁻¹ * gM * mM ∈ Z :=
      hZnormal.conj_mem' gM (Subgroup.mem_zpowers gM) mM
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj
    have hk' : g ^ k = m⁻¹ * g * m := by
      have h := congrArg (fun x : ↥M => (x : MulAut U)) hk
      simpa [gM, mM] using h
    let W : Subgroup U := V.map (m : MulAut U).toMonoidHom
    have hWcard : Nat.card W = 8 := by
      rw [Subgroup.card_map_of_injective m.injective, hV]
    have hgW : ∀ w ∈ W, g w ∈ W := by
      intro w hw
      obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hw
      have hmul : (m : MulAut U) * g ^ k = g * m := by
        rw [hk']
        group
      refine Subgroup.mem_map.mpr ⟨(g ^ k) v', zpow_apply_mem_of_mem_stabSub hstabV k hv', ?_⟩
      calc
        (m : MulAut U) ((g ^ k) v') = ((m : MulAut U) * g ^ k) v' := rfl
        _ = (g * m) v' := by rw [hmul]
        _ = g ((m : MulAut U) v') := rfl
    have hW : V = W := eq_of_invariant_card_eight h16 hg hV hWcard hgV hgW
    have hmv : (m : MulAut U) v ∈ W := Subgroup.mem_map_of_mem _ hv
    rw [← hW] at hmv
    exact hmv
  exact hMV hstable

theorem nonempty_mulEquiv_GL32 (hU2 : ∀ u : U, u ^ 2 = 1) (h16 : Nat.card U = 16)
    {M : Subgroup (MulAut U)} (hO2 : O2Trivial M) {g : MulAut U} (hgM : g ∈ M)
    (hg : orderOf g = 7) {F V : Subgroup U} (hF : (F : Set U) = fixedBy U g)
    (hMF : StableUnder M F) (hV : Nat.card V = 8) (hgV : ∀ v ∈ V, g v ∈ V)
    (hMV : ¬ StableUnder M V) : Nonempty (↥M ≃* GL (Fin 3) (ZMod 2)) := by
  have hF2 : Nat.card F = 2 := by
    have h := card_fixedBy_eq_two h16 hg
    rw [← hF] at h
    simpa using h
  let φ : ↥M →* MulAut (U ⧸ F) := (quotHom F).comp (Subgroup.inclusion
    (CFSG.Quasithin.SmithD37.le_stabSub_of_isInvBy hMF))
  have hker : φ.ker = ⊥ := by
    simpa [φ] using ker_quotHom_comp_inclusion_eq_bot hU2 hO2 hMF hF2
  have hφ : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hcardQ : Nat.card (U ⧸ F) = 8 := by
    rw [← Subgroup.index_eq_card]
    have h := F.card_mul_index
    rw [hF2, h16] at h
    omega
  have hU2q : ∀ u : U ⧸ F, u ^ 2 = 1 := by
    intro u
    induction u using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hU2 v, QuotientGroup.mk_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := CFSG.Sporadic.RuSchreier.ru_nonempty_mulEquiv_of_elementary (p := 2)
    (W := U ⧸ F) (fun a b => mul_comm a b) hU2q (n := 3) (by rw [hcardQ]; norm_num)
  let e : MulAut (U ⧸ F) ≃* GL (Fin 3) (ZMod 2) :=
    (MulAut.congr e₀).trans (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 2) 3)
  let H : Subgroup (GL (Fin 3) (ZMod 2)) := φ.range.map e.toMonoidHom
  have hcardHrange : Nat.card ↥(φ.range) = Nat.card ↥M :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have hcardH : Nat.card ↥H = Nat.card ↥M := by
    change Nat.card ↥(φ.range.map e.toMonoidHom) = Nat.card ↥M
    rw [Subgroup.card_map_of_injective e.injective, hcardHrange]
  have h7M : 7 ∣ Nat.card ↥M := by
    simpa [hg] using Subgroup.orderOf_dvd_natCard M (x := g) hgM
  have h7H : 7 ∣ Nat.card ↥H := by
    rw [hcardH]
    exact h7M
  rcases CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_gl3_subgroup_seven_dvd h7H with
    h168 | ⟨hcard, -⟩
  · have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H
      (by rw [h168, CFSG.ComponentClassification.GHarris.card_GL32_gh])
    exact ⟨(MonoidHom.ofInjective hφ).trans
      ((Subgroup.equivMapOfInjective φ.range e.toMonoidHom e.injective).trans
        ((MulEquiv.subgroupCongr hHtop).trans Subgroup.topEquiv))⟩
  · have hMcard : Nat.card ↥M = 7 ∨ Nat.card ↥M = 21 := by
      rw [← hcardH]
      exact hcard
    exact (false_of_card_eq_seven_or_twentyOne h16 hgM hg hV hgV hMV hMcard).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven
