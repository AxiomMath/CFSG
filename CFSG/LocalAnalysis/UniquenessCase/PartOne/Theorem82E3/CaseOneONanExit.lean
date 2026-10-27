module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONanCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ExitsSetup
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONan
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5SmallONan
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
import CFSG.GroupTheory.CharacteristicNormalizer
import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma96C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

variable {G : Type} [Group G] [Finite G] {D : Data G}

private theorem inf_L_subgroupOf_characteristic
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ((P ⊓ c.L).subgroupOf P).Characteristic := by
  have hforward : ∀ (ψ : MulAut ↥P) (y : ↥P),
      y ∈ (P ⊓ c.L).subgroupOf P → ψ y ∈ (P ⊓ c.L).subgroupOf P := by
    intro ψ y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hy3G : (y : G) ^ 3 = 1 :=
      c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP (y : G) hy
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hy3G
    have hψ3 : ((ψ y : ↥P) : G) ^ 3 = 1 := by
      have h : (ψ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
      simpa using congrArg (fun z : ↥P => (z : G)) h
    exact Subgroup.mem_inf.mpr ⟨(ψ y).2,
      c.forall_pow_three_eq_one_mem_L_of_threeCover
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
        hON hP ((ψ y : ↥P) : G) (ψ y).2 hψ3⟩
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hforward φ y hy
  · intro hx
    exact ⟨φ.symm x, hforward φ.symm x hx, by simp⟩

private theorem centralizer_le_of_mem_inf_centralizer (c : Ctx82E3 D) {P : Subgroup G} {x : G}
    (hcardZ : Nat.card ↥((P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) = 3)
    (hNZM : Subgroup.normalizer (((P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ D.M)
    (hord : orderOf x = 3)
    (hxZ : x ∈ (P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) :
    Subgroup.centralizer ({x} : Set G) ≤ D.M := by
  let Z : Subgroup G := (P ⊓ c.L) ⊓
    Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)
  have hzp : Subgroup.zpowers x ≤ Z := Subgroup.zpowers_le.mpr hxZ
  have hcardzp : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hEq : Subgroup.zpowers x = Z :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hcardzp, hcardZ])
  have hCZ : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    rw [← hEq]
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hyx : y * x * y⁻¹ = x := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hy
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [h]
        _ = x := by group
    show Subgroup.zpowers (y * x * y⁻¹) = Subgroup.zpowers x
    rw [hyx]
  exact hCZ.trans hNZM

private theorem centralizer_le_of_mem_sylow_three
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hcardZ : Nat.card ↥((P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) = 3)
    (hNZM : Subgroup.normalizer (((P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ D.M)
    (hstep : ∀ x ∈ P ⊓ c.L, orderOf x = 3 →
      x ∉ (P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) →
      Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    ∀ x ∈ P, orderOf x = 3 → Subgroup.centralizer ({x} : Set G) ≤ D.M := by
  intro x hxP hord
  have hx3 : x ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one x
  have hxQ : x ∈ P ⊓ c.L :=
    Subgroup.mem_inf.mpr ⟨hxP,
      c.forall_pow_three_eq_one_mem_L_of_threeCover
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
        hON hP x hxP hx3⟩
  by_cases hxZ : x ∈ (P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)
  · exact centralizer_le_of_mem_inf_centralizer c hcardZ hNZM hord hxZ
  · exact hstep x hxQ hord hxZ

theorem Ctx82E3.false_of_onan
    (c : Ctx82E3 D)
    (hKF7 : UC22.KF7Use D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h7 : 7 ∈ D.sig)
    (hstep : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M →
      Subgroup.normalizer
        (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
          Set G) ≤ D.M →
      ∀ x ∈ P ⊓ c.L, orderOf x = 3 →
        x ∉ (P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) →
        Subgroup.centralizer ({x} : Set G) ≤ D.M) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  have hQchar : ((P ⊓ c.L).subgroupOf P).Characteristic :=
    inf_L_subgroupOf_characteristic c hON hP
  have hNPM : Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (((P ⊓ c.L) ⊓
        Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    (CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic inf_le_left hQchar).trans
      (CFSG.LocalAnalysis.GLTheoremA.S9.L96.normalizer_le_normalizer_center (P ⊓ c.L))
  have hNZM : Subgroup.normalizer (((P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ D.M :=
    c.normalizer_inf_centralizer_le_of_onan hKF7 hON h7 hP
  have hNS : Subgroup.normalizer (P : Set G) ≤ D.M := hNPM.trans hNZM
  have hcardZ : Nat.card ↥((P ⊓ c.L) ⊓
      Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) = 3 :=
    c.card_inf_centralizer_of_onan hON hP
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hZleP : ((P ⊓ c.L) ⊓
        Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) ≤ P :=
      inf_le_left.trans inf_le_left
    have hZbot : ((P ⊓ c.L) ⊓
        Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) = ⊥ := by
      simpa [hbot] using hZleP
    rw [hZbot, Subgroup.card_bot] at hcardZ
    omega
  have hC : ∀ x ∈ P, orderOf x = 3 → Subgroup.centralizer ({x} : Set G) ≤ D.M :=
    centralizer_le_of_mem_sylow_three c hON hP hcardZ hNZM (hstep P hP hNZM)
  exact c.not_strong
    (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le
      (s := 3) (M := D.M) (S := P) c.M_ne_top hP hPne hNS hC)

@[expose] def ONanCentralizerSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
    AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
      ∀ c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S),
        CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L →
        ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar →
        (PartTwo.Three.dataOfSetup hS S).sig = {7} →
        ∀ P : Subgroup G,
          CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M →
          Subgroup.normalizer
            (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) :
              Subgroup G) : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M →
          ∀ x ∈ P ⊓ c.L, orderOf x = 3 →
            x ∉ (P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) →
            Subgroup.centralizer ({x} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M

theorem onanExcludedSetup_of_inputs
    (hSQ : Section7.StronglyEmbeddedSolvableQ) (hSE5 : Section7.StronglyEmbeddedFive)
    (hSE3 : Section7.StronglyEmbeddedThree) (hstep : ONanCentralizerSetup) :
    ONanExcludedSetup := by
  intro G _ _ hS hUC hC S hSig c h811 hON hsig
  exact c.false_of_onan (UC22.kf7Use_dataOfSetup hSQ hSE5 hSE3 hS S) hON
    (by rw [hsig]; exact Set.mem_singleton 7)
    (hstep G hS hUC hC S hSig c h811 hON hsig)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
