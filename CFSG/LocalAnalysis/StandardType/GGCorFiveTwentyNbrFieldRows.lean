module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyR3Rank
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTablePRow_fieldTwo {p : ℕ} {labJ labK : LargeEvenLabel} (hp : p.Prime)
    (hrow : GGTablePRow p labJ labK) (hK : LargeEvenInLambda2 labK) (hJ : 2 ≤ labJ.n)
    (hnok : ¬ GGLabNbrOk p labK) :
    (p = 3 ∧ labK = ⟨.twE6, 0, 1⟩) ∨ (p = 7 ∧ labK = ⟨.A, 8, 1⟩) := by
  obtain ⟨t, r, n⟩ := labK
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  have hn1 : 1 ≤ n := hK.1
  simp only [GGLabNbrOk, not_or, not_and, not_le] at hnok
  obtain ⟨hn2, hnA⟩ := hnok
  dsimp only at hn1 hn2 hJ hnA
  obtain rfl : n = 1 := by omega
  have e1 : (1 = nJ) = False := eq_false (by omega)
  have e2 : (nJ = 1) = False := eq_false (by omega)
  have e3 : (1 = 3 * nJ) = False := eq_false (by omega)
  simp only [GGTablePRow, LargeEvenLabel.mk.injEq, e1, e2, e3, and_false, false_and, false_or,
    or_false, and_true, true_and, eq_self_iff_true] at hrow
  have hpr3 : p ∣ 3 → p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
  rcases hrow with ⟨-, -, hrJ, ⟨-, rfl, rfl, -, hp1⟩ | ⟨rfl, hr, -, hp3⟩⟩ |
      ⟨⟨-, -, -⟩, rfl, rfl, rfl⟩ | ⟨⟨-, -, -⟩, -, -, -, h12⟩ | ⟨-, hp9, -, rfl, hn3⟩
  · exfalso
    have h1 : p ≤ 1 := by simpa using Nat.le_of_dvd (by norm_num) hp1
    exact absurd hp.two_le (by omega)
  · exfalso
    have h3 : p = 3 := hpr3 (by simpa using hp3)
    have := hnA rfl rfl h3
    omega
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd h12 (by decide)
  · have hr : r = 0 := by simpa [LargeEvenInLambda2] using hK
    subst hr hn3
    have h9 : p ∣ 3 ^ 2 := by norm_num at hp9 ⊢; exact hp9
    exact Or.inl ⟨hpr3 (hp.dvd_of_dvd_pow h9), rfl⟩

private theorem two_le_n_of_ggLabelIso {p : ℕ} {lab labJ labK : LargeEvenLabel}
    (hrow : GGTablePRow p labJ labK) (hiso : GGLabelIso lab labJ) (h2 : 2 ≤ lab.n) :
    2 ≤ labJ.n := by
  rcases hiso with rfl | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h2
  · omega
  all_goals first
    | (rw [h]; exact h2)
    | (rw [h]; dsimp only; omega)
    | (exfalso; rw [h] at hrow; simp [GGTablePRow] at hrow)

theorem ggNbr_label_J_of_tcj_onLabel (hTCJ : GGTCJKnown) {G : Type} [Group G] [Finite G]
    {S : ℕ → LargeEvenLabel → Prop} {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : GGInnerDiagOnLabel S p Bs L) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧
      GGHasLabel lab (L ⧸ Subgroup.center L) ∧ LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSS.2.2.2.1.1
  have hy : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hy
  have hLperf : commutator ↥L = ⊤ := hL.1
  have hM := ggMarking_and_labelAll_dep (fun lab hlab => hTCJ p hp hp2 lab hlab) hL
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨hS, hNL, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNL hyBs
  have hy1 : y ^ p = 1 := hBel.2 y hy
  have hep : L.normalizerMonoidHom ⟨y, hyN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hy1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind y⁻¹ (Bs.inv_mem hyBs)
  let ψ : ↥L →* R := (θ : L ⧸ Subgroup.center L →* R).comp (QuotientGroup.mk' (Subgroup.center L))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥L := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : L ⧸ Subgroup.center L) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (L.normalizerMonoidHom ⟨y, hyN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (L.normalizerMonoidHom ⟨y, hyN⟩ l) ?_⟩
    show ((L.normalizerMonoidHom ⟨y, hyN⟩ l : ↥L) : G) = y⁻¹⁻¹ * (l : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hDy : D = Subgroup.closure {x, y} := hnb.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  rw [hDy, ggInf_centralizer_pair hLx] at hcomp
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hyN hcomp
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥L ψ hψsurj hψker hLperf _ hep hφe (J.subgroupOf L) hJcomp
  refine ⟨lab, labJ, hlab, hS, hhas, hlabJ, hdvd, ?_⟩
  exact ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL)
    (Subgroup.map_center_eq _)) hhasJ

theorem ggNbr_fieldRow_of_not_labelOk (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hH : GGCorFiveTwentyHyp p B Bs x L D J)
    (hq : GGInnerDiagOnLabel GGLabQFour p Bs L) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : ¬ GGInnerDiagOnLabel GGLabNbrOk p Bs K) :
    (p = 3 ∧ GGHasLabel ⟨.twE6, 0, 1⟩ (K ⧸ Subgroup.center K)) ∨
      (p = 7 ∧ GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K)) := by
  have hcfg := hH.1
  have hInn := hH.2.2.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨labK, hKΛ, hhasK, -⟩ := largeEvenMarking_exists_hasLabel (hInn.2 y K hnb)
  obtain ⟨labL, labJ, -, hq4, -, hJΛ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hq hnb
  have hJ2 : 2 ≤ labJ.n := le_trans hq4 (Nat.le_of_dvd (by have := hJΛ.1; omega) hdvd)
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
    hTP G p B Bs x L D J y K hcfg hInn.1 (hInn.2 y K hnb) hnb labJ labK hJΛ hKΛ hhasJ hhasK
  have hj2 : 2 ≤ jlab.n :=
    two_le_n_of_ggLabelIso hrow (hRig labJ jlab _ hJΛ hjΛ hhasJ hhasJ1) hJ2
  have hnok : ¬ GGLabNbrOk p klab := fun hok => hK (largeEvenMarking_mono
    (fun _ _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hok, hP⟩)
    (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hkΛ hhasK1))
  rcases ggTablePRow_fieldTwo hp hrow hkΛ hj2 hnok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, hhasK1⟩
  · exact Or.inr ⟨rfl, hhasK1⟩

@[expose] def GGCorFiveTwentyInputNbrFieldRows : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      ¬ GGNbrLabelsOk p B Bs x D J → ¬ GGSecFiveA11Config p B Bs x L D J →
        GGCorFiveTwentyR3Rank p B Bs x D J →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ¬ GGInnerDiagOnLabel GGLabNbrOk p Bs K →
          (p = 3 ∧ GGHasLabel ⟨.twE6, 0, 1⟩ (K ⧸ Subgroup.center K)) ∨
            (p = 7 ∧ GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K))) →
          Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3.toFieldRows
    (h : GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3) : GGCorFiveTwentyInputNbrFieldRows :=
  fun G _ _ p B Bs x L D J hH hq hN hA hR _ => h G p B Bs x L D J hH hq hN hA hR

theorem GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3.of_fieldRows (hRig : GGLabelRigidInput)
    (hTCJ : GGTCJKnown) (hTP : GGNbrTablePNbrInput) (h : GGCorFiveTwentyInputNbrFieldRows) :
    GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3 :=
  fun G _ _ p B Bs x L D J hH hq hN hA hR => h G p B Bs x L D J hH hq hN hA hR
    fun _ _ hnb hK => ggNbr_fieldRow_of_not_labelOk hRig hTCJ hTP hH hq hnb hK

end CFSG.StandardType

end
