module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.AlmostSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

namespace CoreSetup

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

theorem exists_outer_involution (h : CoreSetup X K L T Y n)
    (hL2 : CFSG.Open.pCoreOf 2 L = ⊥) (hodd : Odd (Nat.card ↥(K ⊓ centralizer (L : Set X)))) :
    K ⊓ T = ⊥ ∧ ∃ z ∈ T, (∀ t ∈ T, t * z = z * t) ∧ orderOf z = 2 ∧
      L ≤ centralizer ({z} : Set X) ∧ T ≤ centralizer ({z} : Set X) ∧
      centralizer ({z} : Set X) ≠ ⊤ ∧
      CFSG.Open.IsComponentOf L (K ⊓ centralizer ({z} : Set X)) ∧
      ∀ k ∈ K, ∃ x ∈ K, z * x * z⁻¹ ≠ k * x * k⁻¹ := by
  classical
  have hCent : F08.CentOverO2 Y L = centralizer (L : Set X) := by
    rw [centOverO2_eq_of_pCoreOf_eq_bot hL2, inf_eq_right.mpr h.centralizer_le_Y]
  have hSylC : IsSylowOf 2 T (centralizer (L : Set X)) := by
    have hs := h.sylow
    rwa [hCent] at hs
  have hTleC : T ≤ centralizer (L : Set X) := hSylC.le
  have hTgroup : IsPGroup 2 T := hSylC.isPGroup
  have hKT : K ⊓ T = ⊥ := by
    have hP2 : IsPGroup 2 ↥(K ⊓ T) := hTgroup.to_le inf_le_right
    have hdvd : Nat.card ↥(K ⊓ T) ∣ Nat.card ↥(K ⊓ centralizer (L : Set X)) :=
      Subgroup.card_dvd_of_le (inf_le_inf_left K hTleC)
    rcases hP2.card_eq_or_dvd with h1 | h2
    · exact (Subgroup.card_eq_one (H := K ⊓ T)).mp h1
    · exact absurd (dvd_trans h2 hdvd) hodd.not_two_dvd_nat
  have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr h.T_ne_bot
  have hZnt : Nontrivial ↥(Subgroup.center ↥T) := hTgroup.center_nontrivial
  have hZne : Subgroup.center ↥T ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hZnt
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥T) := hTgroup.to_subgroup _
  have hZeven : 2 ∣ Nat.card ↥(Subgroup.center ↥T) := by
    rcases hZ2.card_eq_or_dvd with h1 | h2
    · exact absurd ((Subgroup.card_eq_one (H := Subgroup.center ↥T)).mp h1) hZne
    · exact h2
  obtain ⟨u, hu_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥T)) 2 hZeven
  let z : X := ((u : ↥T) : X)
  have hzT : z ∈ T := (u : ↥T).2
  have hz_comm : ∀ t ∈ T, t * z = z * t := by
    intro t ht
    have hc := (Subgroup.mem_center_iff.mp u.2) ⟨t, ht⟩
    exact congrArg Subtype.val hc
  have hz_order : orderOf z = 2 := by
    change orderOf ((u : ↥T) : X) = 2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hu_order
  have hz_ne : z ≠ 1 := by
    intro h1
    rw [h1] at hz_order
    simp at hz_order
  let Cz : Subgroup X := centralizer ({z} : Set X)
  have hzC : z ∈ centralizer (L : Set X) := hTleC hzT
  have hL_Cz : L ≤ Cz := by
    intro l hl
    change l ∈ centralizer ({z} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzC) l hl
  have hT_Cz : T ≤ Cz := by
    intro t ht
    change t ∈ centralizer ({z} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hz_comm t ht
  have hCz_ne_top : Cz ≠ ⊤ := by
    intro htop
    have hzcenter : z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cz := by rw [htop]; exact Subgroup.mem_top g
      change g ∈ centralizer ({z} : Set X) at hg
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hnorm : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem hzcenter)
    have hp2 : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz_order, pow_one])
    have hle : Subgroup.zpowers z ≤ CFSG.pCore 2 X :=
      CFSG.LieType.BorelTits.le_pCore 2 hnorm hp2
    rw [h.pCore_eq_bot, le_bot_iff] at hle
    have hzbot : z ∈ (⊥ : Subgroup X) := by
      rw [← hle]
      exact Subgroup.mem_zpowers z
    exact hz_ne (Subgroup.mem_bot.mp hzbot)
  have hzK : z ∉ K := by
    intro hzK
    have hzKT : z ∈ K ⊓ T := ⟨hzK, hzT⟩
    rw [hKT] at hzKT
    exact hz_ne (Subgroup.mem_bot.mp hzKT)
  have hOuter : ∀ k ∈ K, ∃ x ∈ K, z * x * z⁻¹ ≠ k * x * k⁻¹ := by
    intro k hk
    by_contra hcon
    push Not at hcon
    have hc : k⁻¹ * z ∈ centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have e : z * x * z⁻¹ = k * x * k⁻¹ := hcon x hx
      have e' : z * x = k * x * k⁻¹ * z := by rw [← e]; group
      calc x * (k⁻¹ * z) = k⁻¹ * (k * x * k⁻¹ * z) := by group
        _ = k⁻¹ * (z * x) := by rw [e']
        _ = k⁻¹ * z * x := by group
    have hkz : k⁻¹ * z ∈ K := h.centralizer_le hc
    apply hzK
    have hz_eq : z = k * (k⁻¹ * z) := by group
    rw [hz_eq]
    exact K.mul_mem hk hkz
  have hsubCz : CFSG.Open.IsSubnormal L Cz := h.subnormal_of_le Cz hCz_ne_top hL_Cz hT_Cz
  have hsubKz : CFSG.Open.IsSubnormal L (K ⊓ Cz) :=
    isSubnormal_mono hsubCz (le_inf h.le hL_Cz) inf_le_right
  have hLsimpleBar : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h.sz
  have hLcore : CFSG.pCore 2 ↥L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
      (by simpa [CFSG.Open.pCoreOf] using hL2)
  let eBar : Bar2 L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hLcore).trans QuotientGroup.quotientBot
  have hSimpleL : IsSimpleGroup ↥L := eBar.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h.sz
  have hNonabL : ∃ a b : ↥L, a * b ≠ b * a := by
    refine ⟨eBar a, eBar b, ?_⟩
    intro hba
    apply hab
    have h' : eBar (a * b) = eBar (b * a) := by rw [map_mul, map_mul, hba]
    exact eBar.injective h'
  have hLq : CFSG.IsQuasisimple ↥L :=
    (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ↥L _ hSimpleL hNonabL).1
  have hComp : CFSG.Open.IsComponentOf L (K ⊓ Cz) :=
    ⟨le_inf h.le hL_Cz, hsubKz, ⟨(Group.isPerfect_def (G := ↥L)).1 hLq.1, hLq.2.1⟩⟩
  exact ⟨hKT, z, hzT, hz_comm, hz_order, hL_Cz, hT_Cz, hCz_ne_top, hComp, hOuter⟩

end CoreSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
