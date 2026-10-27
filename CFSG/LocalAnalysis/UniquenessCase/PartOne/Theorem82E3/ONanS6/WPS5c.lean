module

public import CFSG.LocalAnalysis.GLTheoremB.AutL34Bound
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK9bCat
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem sevenSubgroup_le_centralizerOnQuotient
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (haM : a ∈ D.M) (ha3 : orderOf a = 3)
    (hρa : (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L)
      ⟨a, haM⟩ ≠ 1)
    {S : Subgroup G} (hSM : S ≤ D.M)
    (haS : S ≤ Subgroup.centralizer ({a} : Set G)) (hS7 : IsPGroup 7 S) :
    S ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
      (CFSG.Open.pCoreOf 2 c.L) c.L := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let ρ : ↥D.M →* MulAut c.Lbar :=
    CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  obtain ⟨e⟩ := hON.2.2
  let Φ : MulAut c.Lbar →* MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    (MulAut.congr e).toMonoidHom.comp
      (CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut' c.Lbar)
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr e).injective.comp
      (CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut'_injective hON.1.1)
  let Ψ : ↥D.M →* MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan) := Φ.comp ρ
  have hρa3 : orderOf (ρ ⟨a, haM⟩) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ hρa
    rw [← map_pow]
    have ha3' : (⟨a, haM⟩ : ↥D.M) ^ 3 = 1 := by
      apply Subtype.ext
      change a ^ 3 = 1
      simpa [ha3] using pow_orderOf_eq_one a
    rw [ha3', map_one]
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    (CFSG.Sporadic.ON.fam_on_simplicity).1
  have hσ3 : orderOf (Ψ ⟨a, haM⟩) = 3 :=
    (orderOf_injective Φ hΦinj (ρ ⟨a, haM⟩)).trans hρa3
  let Inn : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) :=
    (MulAut.conj :
      CFSG.Blueprint.NativeSporadic.Carrier .ONan →*
        MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan)).range
  let H : Subgroup (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) :=
    Inn ⊔ Ψ.range
  have hK4 : Nat.card ↥(H ⊓ Subgroup.centralizer
      ({Ψ ⟨a, haM⟩} :
        Set (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan)))) ∣ 6480 :=
    K4ord_holds (Y := CFSG.Blueprint.NativeSporadic.Carrier .ONan)
      ⟨MulEquiv.refl _⟩ H le_sup_left (Ψ ⟨a, haM⟩)
      (Subgroup.mem_sup_right ⟨_, rfl⟩) hσ3
  intro s hsS
  have hsM : s ∈ D.M := hSM hsS
  have hsa : s * a = a * s :=
    Subgroup.mem_centralizer_singleton_iff.mp (haS hsS)
  have hρcomm : ρ ⟨s, hsM⟩ * ρ ⟨a, haM⟩ =
      ρ ⟨a, haM⟩ * ρ ⟨s, hsM⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hsa
  have hΨcomm : Ψ ⟨s, hsM⟩ * Ψ ⟨a, haM⟩ =
      Ψ ⟨a, haM⟩ * Ψ ⟨s, hsM⟩ := by
    have h := congrArg Φ hρcomm
    simpa only [Ψ, MonoidHom.comp_apply, map_mul] using h
  have hΨcentral : Ψ ⟨s, hsM⟩ ∈
      Subgroup.centralizer ({Ψ ⟨a, haM⟩} :
        Set (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hΨcomm
  have hdiv6480 : orderOf (Ψ ⟨s, hsM⟩) ∣ 6480 :=
    (Subgroup.orderOf_dvd_natCard
      (s := H ⊓ Subgroup.centralizer
        ({Ψ ⟨a, haM⟩} :
          Set (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .ONan))))
      ⟨Subgroup.mem_sup_right ⟨_, rfl⟩, hΨcentral⟩).trans hK4
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hS7) ⟨s, hsS⟩
  have horder : orderOf (⟨s, hsM⟩ : ↥D.M) = 7 ^ m := by
    calc orderOf (⟨s, hsM⟩ : ↥D.M) = orderOf s :=
        (Subgroup.orderOf_coe (⟨s, hsM⟩ : ↥D.M)).symm
      _ = orderOf (⟨s, hsS⟩ : ↥S) :=
        Subgroup.orderOf_coe (⟨s, hsS⟩ : ↥S)
      _ = 7 ^ m := hm
  have hdiv7 : orderOf (Ψ ⟨s, hsM⟩) ∣ 7 ^ m := by
    simpa [horder] using orderOf_map_dvd Ψ (⟨s, hsM⟩ : ↥D.M)
  have hcop : Nat.Coprime (7 ^ m) 6480 :=
    Nat.Coprime.pow_left m (by norm_num)
  have hdiv1 : orderOf (Ψ ⟨s, hsM⟩) ∣ 1 := by
    have h := Nat.dvd_gcd hdiv7 hdiv6480
    rwa [hcop.gcd_eq_one] at h
  have hΨ1 : Ψ ⟨s, hsM⟩ = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdiv1)
  have hρs1 : ρ ⟨s, hsM⟩ = 1 := by
    apply hΦinj
    simpa only [Ψ, MonoidHom.comp_apply, hΨ1, map_one]
  have hker : s ∈ ρ.ker.map D.M.subtype :=
    Subgroup.mem_map.mpr ⟨⟨s, hsM⟩, MonoidHom.mem_ker.mpr hρs1, rfl⟩
  rw [map_ker_conjModPCore_eq_centralizerOnQuotient c] at hker
  exact hker

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
