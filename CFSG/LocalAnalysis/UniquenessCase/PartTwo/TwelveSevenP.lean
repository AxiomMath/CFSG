module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixTen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight
import CFSG.LocalAnalysis.WeakClosure81.SevenOne
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveSeven

theorem normalizer_le_of_gamma_le {p : ℕ} (hp : p.Prime) {X Y M : Subgroup G}
    (hexp : ∀ x ∈ X, x ^ p = 1) (hΓ : rankThreeGamma 1 p X ≤ M) (hYX : Y ≤ X) (hY : Y ≠ ⊥) :
    normalizer (Y : Set G) ≤ M := by
  obtain ⟨⟨y, hyY⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hY
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyp : y ^ p = 1 := hexp y (hYX hyY)
  have hE : IsElemAbelian p (zpowers y) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
  have hcard : Nat.card (zpowers y) = p ^ 1 := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hyp hy1'
  have h1 : 1 ≤ CFSG.Open.pRank p Y :=
    CFSG.SectionRank.le_pRank hp.one_lt ((Subgroup.zpowers_le).2 hyY) hE hcard
  exact (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hYX h1).trans hΓ

theorem normalizer_le_of_uniqueMax_le (D : Data G) {E P : Subgroup G} (hE : UniqueMax D.M E)
    (hEP : E ≤ P) (hPM : P ≤ D.M) : normalizer (P : Set G) ≤ D.M := by
  intro x hx
  have hmax : rankThreeIsMaxTwoLocal (D.M.map (MulAut.conj x).toMonoidHom) := by
    have := UC6.isMaxTwoLocal_conj D.maxLocal x⁻¹
    simpa [uniqueFourConj, rankThreeIsMaxTwoLocal] using this
  have hEM' : E ≤ D.M.map (MulAut.conj x).toMonoidHom := by
    intro e he
    refine ⟨x⁻¹ * e * x, ?_, by simp [mul_assoc]⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) e).1 (hEP he)
    exact hPM (by simpa using h1)
  have hmem : D.M.map (MulAut.conj x).toMonoidHom ∈ calMOf E := ⟨hmax, hEM'⟩
  rw [show calMOf E = {D.M} from hE, Set.mem_singleton_iff] at hmem
  exact TwelveEight.mem_of_le_map_conj D (by rw [hmem]; exact D.sylowM.le)

theorem inf_conjSubgroup_eq_bot (D : Data G) (h63 : UC6.R6_3 D) {X : Subgroup G}
    (hX : F11.InP11 D X) {W : Subgroup G} (hW : InCalV D.M W) {g : G} (hg : g ∉ D.M)
    (hWg : W ≤ conjSubgroup D.M g) : X ⊓ conjSubgroup D.M g = ⊥ := by
  obtain ⟨p, hp, hp2, hXM, hXp, hexp, -, -, hΓX, hsp | ⟨Y, hYnc, ⟨P, hPsyl, hYP, hPY⟩, hΓY⟩⟩ := hX
  · by_contra hne
    have hX1p : IsPGroup p ↥(X ⊓ conjSubgroup D.M g) := hXp.to_le inf_le_left
    haveI : Fact p.Prime := ⟨hp⟩
    have hdvd : p ∣ Nat.card ↥(X ⊓ conjSubgroup D.M g) := by
      rcases hX1p.card_eq_or_dvd with h1 | h
      · exact absurd (Subgroup.card_eq_one.1 h1) hne
      · exact h
    have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
    apply hsp.2.2 g⁻¹ hg'
    exact hdvd.trans (Subgroup.card_dvd_of_le (le_inf (inf_le_left.trans hXM) inf_le_right))
  · by_contra hne
    haveI : Fact p.Prime := ⟨hp⟩
    have hPp : IsPGroup p P := hPsyl.isPGroup
    have hPM : P ≤ D.M := hPsyl.le
    obtain ⟨E, hEY, hPE, hEcard, hEexp, hEab⟩ :=
      CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hp hp2 hPp hYP hPY hYnc
    have hEP : E ≤ P := hEY.trans hYP
    have hEM : E ≤ D.M := hEP.trans hPM
    have hEel : IsElemAbelian p E := ⟨⟨⟨fun a b => Subtype.ext (hEab a a.2 b b.2)⟩⟩, hEexp⟩
    have hΓE : rankThreeGamma 1 p E ≤ D.M :=
      (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := p) (k := 1) hEY).trans hΓY
    have hEU : UniqueMax D.M E := h63 p hp hp2 E hEM hEel hEcard hΓE
    have hNP : normalizer (P : Set G) ≤ D.M := normalizer_le_of_uniqueMax_le D hEU hEP hPM
    have hPG : ¬ p ∣ P.index := by
      have h := (CFSG.ABGLocalTools.isSylowOf_iff.1
        (uc22p22q_isSylowOf_top_of_normalizer hPsyl hNP)).2.2
      rwa [Subgroup.relIndex_top_right] at h
    set P' : Sylow p G := hPp.toSylow hPG with hP'
    have hP'P : (P' : Subgroup G) = P := IsPGroup.toSylow_coe _ _
    have hEnorm : (E.subgroupOf (P' : Subgroup G)).Normal := by
      rw [hP'P]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).2 hPE
    have hX1 : X ⊓ conjSubgroup D.M g ≤ X := inf_le_left
    have h610 := PartTwo.r6_10_of_r6_3 D h63 p hp hp2 P' E (hP'P ▸ hEP) hEnorm
      (uc22p22n_not_isCyclic_of_card hp hEel hEcard.ge) hEexp hΓE (X ⊓ conjSubgroup D.M g)
      (hX1.trans hXM) (hXp.to_le hX1) (normalizer_le_of_gamma_le hp hexp hΓX hX1 hne) g hg
      inf_le_right
    exact h610.2 W hW hWg

theorem le_conjSubgroup_of_isTI (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hTI : IsTI V) {g : G} (hg : g ∉ D.M) (hVg : conjSubgroup V g ≤ D.M) :
    V ≤ conjSubgroup D.M g := by
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hne : conjSubgroup V g ⊓ normalizer (V : Set G) ≠ ⊥ := by
    rw [hN, inf_eq_left.2 hVg]
    intro h
    apply hV.1
    have h1 := E3.card_conjSubgroup V g
    rw [h, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.1 h1.symm
  rcases two_conj_eq_or_comm hV.2.2.2 hTI ⟨g, rfl⟩ ⟨1, (conjSubgroup_one V).symm⟩ hne with
    hcomm | ⟨y, hy, hyV⟩
  · intro v hv
    rw [mem_conjSubgroup_iff]
    refine centralizer_le_of_inCalV D hV ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwg : g⁻¹ * w * g ∈ conjSubgroup V g := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hw
    have hc := hcomm _ hwg v hv
    calc w * (g * v * g⁻¹) = g * ((g⁻¹ * w * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc]
      _ = g * v * g⁻¹ * w := by group
  · exfalso
    have hyM : y ∈ D.M := (sup_le hVg hV.2.1) hy
    rw [conjSubgroup_conjSubgroup] at hyV
    have hgy : g * y ∈ normalizer (V : Set G) := conjSubgroup_eq_iff_mem_normalizer.1 hyV.symm
    rw [hN] at hgy
    exact hg (by simpa using D.M.mul_mem hgy (D.M.inv_mem hyM))

theorem mem_calP_of_inP11 (D : Data G) (h63 : UC6.R6_3 D) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : IsTI V) {X : Subgroup G} (hX : F11.InP11 D X) : X ∈ calP V := by
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  obtain ⟨p, hp, hp2, hXM, hXp, -, -, -, hΓX, -⟩ := id hX
  refine ⟨p, hp, hp2, hXp, hN ▸ hXM, hN ▸ hΓX, fun g hg hVg => ?_⟩
  rw [hN] at hg hVg ⊢
  exact inf_conjSubgroup_eq_bot D h63 hX hV hg (le_conjSubgroup_of_isTI D hV hTI hg hVg)

end TwelveSeven

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
