module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoResidualSplit
public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem eq_one_of_centralizes_section (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hP1 : t.UniqueTwoLocalKy) {r : ℕ} {U W : Subgroup G}
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W) (hUO : U ≤ t.Oz)
    (hWM : W ≤ c.S.M) (hUMW : U ⊓ c.S.M ≤ W)
    (hfix : ∀ u ∈ U, (∀ x ∈ t.Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W) {k : G} (hk : k ∈ t.Ky)
    (hkU : ∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ W) : k = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWU : W ≤ U := le_of_lt hUW.1
  have hUnleW : ¬ U ≤ W := hUW.1.2
  have hUnleM : ¬ U ≤ c.S.M := by
    intro hU
    apply hUnleW
    calc U ≤ U ⊓ c.S.M := le_inf le_rfl hU
      _ ≤ W := hUMW
  have hKyU : t.Ky ≤ Subgroup.normalizer (U : Set G) := hUW.2.1
  have hKyW : t.Ky ≤ Subgroup.normalizer (W : Set G) := hUW.2.2.1
  have hUW_norm : U ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hUW.2.2.2.1 x hx y
    · intro hy
      have h := hUW.2.2.2.1 x⁻¹ (U.inv_mem hx) (x * y * x⁻¹) hy
      have heq : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
      rwa [heq] at h
  have hO2W : CFSG.Open.pCoreOf 2 W = ⊥ := by
    by_contra hne
    have hT2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 W) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W
    have hKyT : t.Ky ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 W : Set G) :=
      hKyW.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
    have hUT : U ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 W : Set G) :=
      hUW_norm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
    exact hUnleM (hUT.trans (t.normalizer_le_of_uniqueTwoLocalKy hP1 hT2 hne hKyT))
  have hW3 : ¬ 3 ∣ Nat.card W := by
    have hOz3 : Nat.Coprime 3 (Nat.card t.Oz) := by
      have hcard : Nat.card t.Oz = Nat.card (CFSG.pPrimeCore 3 ↥t.Xz) :=
        Subgroup.card_map_of_injective t.Xz.subtype_injective
      rw [hcard]
      exact CFSG.pPrimeCore_coprime_card
    have hcop : Nat.Coprime 3 (Nat.card W) :=
      Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le (hWU.trans hUO)) hOz3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  have hN2 : IsPGroup 2 ↥t.d.N := SylowThreeData.N_isPGroup t.d
  have hWWM : W ≤ t.d.M := by rwa [t.hdM]
  have hWnormal_inter :
      W ≤ Subgroup.normalizer ((W ⊓ (c.L ⊓ t.d.N) : Subgroup G) : Set G) := by
    have hWself : W ≤ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer
    have hWL : W ≤ Subgroup.normalizer (c.L : Set G) := hWM.trans c.le_normalizer_L
    have hWN : W ≤ Subgroup.normalizer (t.d.N : Set G) :=
      hWWM.trans (SylowThreeData.N_normal t.d)
    have hWLN : W ≤ Subgroup.normalizer ((c.L ⊓ t.d.N : Subgroup G) : Set G) :=
      (le_inf hWL hWN).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hWself hWLN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hW3bot : W ⊓ (c.L ⊓ t.d.N) ≤ CFSG.Open.pCoreOf 2 W := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ ?_
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hWnormal_inter
    · exact hN2.to_le (inf_le_right.trans inf_le_right)
  have hcommWK : ⁅W, t.Ky⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxO2 : x ∈ CFSG.Open.pCoreOf 2 W :=
      hW3bot (t.commutator_Ky_le_inf_N hK32 hGA hSp hWM hKyW hW3 hx)
    rw [hO2W] at hxO2
    exact hxO2
  let N₀ : Subgroup G :=
    { carrier := {n | n ∈ t.Ky ∧ ∀ u ∈ U, n * u * n⁻¹ * u⁻¹ ∈ W}
      one_mem' := ⟨t.Ky.one_mem, by intro u _; simpa using W.one_mem⟩
      mul_mem' := by
        rintro n m ⟨hnK, hnW⟩ ⟨hmK, hmW⟩
        refine ⟨t.Ky.mul_mem hnK hmK, ?_⟩
        intro u hu
        have h1 : n * (m * u * m⁻¹ * u⁻¹) * n⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hKyW hnK) _).mp (hmW u hu)
        have h2 : n * u * n⁻¹ * u⁻¹ ∈ W := hnW u hu
        have heq : (n * m) * u * (n * m)⁻¹ * u⁻¹ =
            n * (m * u * m⁻¹ * u⁻¹) * n⁻¹ * (n * u * n⁻¹ * u⁻¹) := by group
        rw [heq]
        exact W.mul_mem h1 h2
      inv_mem' := by
        rintro n ⟨hnK, hnW⟩
        refine ⟨t.Ky.inv_mem hnK, ?_⟩
        intro u hu
        have hy : n * u * n⁻¹ * u⁻¹ ∈ W := hnW u hu
        have h1 : n⁻¹ * (n * u * n⁻¹ * u⁻¹) * n⁻¹⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hKyW (t.Ky.inv_mem hnK)) _).mp hy
        have heq : n⁻¹ * (n * u * n⁻¹ * u⁻¹) * n⁻¹⁻¹ =
            (n⁻¹ * u * n * u⁻¹)⁻¹ := by group
        have h1' : (n⁻¹ * u * n * u⁻¹)⁻¹ ∈ W := by rwa [heq] at h1
        simpa using W.inv_mem h1' }
  have hN₀_le_Ky : N₀ ≤ t.Ky := fun x hx => hx.1
  have hN₀_conj : ∀ {g x : G}, g ∈ t.Ky → x ∈ N₀ → g * x * g⁻¹ ∈ N₀ := by
    rintro g x hg ⟨hxK, hxW⟩
    refine ⟨t.Ky.mul_mem (t.Ky.mul_mem hg hxK) (t.Ky.inv_mem hg), ?_⟩
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hKyU (t.Ky.inv_mem hg)) u).mp hu
    have h := hxW (g⁻¹ * u * g) hu'
    have hconj := (Subgroup.mem_normalizer_iff.mp (hKyW hg) _).mp h
    have heq : g * (x * (g⁻¹ * u * g) * x⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * u * (g * x * g⁻¹)⁻¹ * u⁻¹ := by group
    rwa [heq] at hconj
  have hN₀_normal : t.Ky ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hN₀_conj hg hx
    · intro hx
      have h := hN₀_conj (t.Ky.inv_mem hg) hx
      have heq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
      rwa [heq] at h
  have hk_mem : k ∈ N₀ := ⟨hk, hkU⟩
  rcases t.le_N_or_eq_Ky hK32 hGA hSp hN₀_le_Ky hN₀_normal with hN₀_le_N | hN₀_eq_Ky
  ·
    have hN0_2 : IsPGroup 2 ↥N₀ := hN2.to_le hN₀_le_N
    have hcommWN₀ : ⁅W, N₀⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hle : ⁅W, N₀⁆ ≤ ⁅W, t.Ky⁆ := Subgroup.commutator_mono le_rfl hN₀_le_Ky
      rw [hcommWK] at hle
      exact hle hx
    have hWnormN₀ : W ≤ Subgroup.normalizer (N₀ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommWN₀).trans
        (Subgroup.centralizer_le_normalizer (N₀ : Set G))
    have hKy_sup : t.Ky ≤ Subgroup.normalizer ((W ⊔ N₀ : Subgroup G) : Set G) :=
      (le_inf hKyW hN₀_normal).trans
        (Subgroup.inf_normalizer_le_normalizer_sup W N₀)
    have hU_sup : U ≤ Subgroup.normalizer ((W ⊔ N₀ : Subgroup G) : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have key : ∀ v : G, v ∈ U →
          (W ⊔ N₀).map (MulAut.conj v).toMonoidHom ≤ W ⊔ N₀ := by
        intro v hv
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · have hWv : W.map (MulAut.conj v).toMonoidHom = W :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUW_norm hv)
          rw [hWv]
          exact le_sup_left
        · intro y hy
          obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
          have h1 : v * n * v⁻¹ * n⁻¹ ∈ W := by
            have h := W.inv_mem (hn.2 v hv)
            simpa [mul_assoc] using h
          have hmem : v * n * v⁻¹ ∈ W ⊔ N₀ := by
            have hdecomp : v * n * v⁻¹ = (v * n * v⁻¹ * n⁻¹) * n := by group
            rw [hdecomp]
            exact (W ⊔ N₀).mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hn)
          simpa [MulAut.conj_apply] using hmem
      have h1 := key u hu
      exact Subgroup.eq_of_le_of_card_ge h1
        (Subgroup.card_map_of_injective (MulAut.conj u).injective).ge
    have hN₀_normal_sup : (N₀.subgroupOf (W ⊔ N₀)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
        (sup_le hWnormN₀ Subgroup.le_normalizer)
    have hN₀_le_O2 : N₀ ≤ CFSG.Open.pCoreOf 2 (W ⊔ N₀) :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 le_sup_right hN₀_normal_sup hN0_2
    have hKyO2 : t.Ky ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (W ⊔ N₀) : Set G) :=
      hKy_sup.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (W ⊔ N₀))
    have hUO2 : U ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (W ⊔ N₀) : Set G) :=
      hU_sup.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (W ⊔ N₀))
    have hN₀_bot : N₀ = ⊥ := by
      by_contra hne
      have hO2_2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 (W ⊔ N₀)) :=
        CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (W ⊔ N₀)
      have hO2_ne : CFSG.Open.pCoreOf 2 (W ⊔ N₀) ≠ ⊥ := by
        intro hbot
        apply hne
        rw [eq_bot_iff]
        intro x hx
        have hxT := hN₀_le_O2 hx
        rw [hbot] at hxT
        exact hxT
      exact hUnleM (hUO2.trans
        (t.normalizer_le_of_uniqueTwoLocalKy hP1 hO2_2 hO2_ne hKyO2))
    rw [hN₀_bot] at hk_mem
    exact Subgroup.mem_bot.mp hk_mem
  ·
    exfalso
    have hZle : t.Z ≤ N₀ :=
      (t.Z_le_Dz.trans t.Dz_le_Ky).trans (le_of_eq hN₀_eq_Ky.symm)
    exact hUnleW (fun u hu => hfix u hu (fun x hx => (hZle hx).2 u hu))

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
