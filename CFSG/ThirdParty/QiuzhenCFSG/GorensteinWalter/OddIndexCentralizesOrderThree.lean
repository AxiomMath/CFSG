module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Odd-index centralizers of normal order-three subgroups -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `F` is a normal subgroup of order three in `D`, and an odd-index
subgroup `V ≤ D` centralizes `F`, then all of `D` centralizes `F`. -/
public theorem le_centralizer_of_card_three_normal_and_odd_centralizing_index
    {G : Type u} [Group G] [Finite G]
    (D V F : Subgroup G)
    (hFcard : Nat.card F = 3) (hFnormalD : IsNormalIn F D)
    (_hVleD : V ≤ D)
    (hVcentF : V ≤ Subgroup.centralizer (F : Set G))
    (hVindexOdd : Odd ((V.subgroupOf D).index)) :
    D ≤ Subgroup.centralizer (F : Set G) := by
  classical
  have hDnormF : D ≤ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd f hf
    exact hFnormalD.2 d hd f hf
  let i : D →* Subgroup.normalizer (F : Set G) :=
    Subgroup.inclusion hDnormF
  let rho : D →* MulAut F := F.normalizerMonoidHom.comp i
  have hFcyc : IsCyclic F := isCyclic_of_prime_card hFcard
  let : IsCyclic F := hFcyc
  have hAutcard : Nat.card (MulAut F) = 2 := by
    rw [IsCyclic.card_mulAut, hFcard, Nat.totient_prime Nat.prime_three]
  let VD : Subgroup D := V.subgroupOf D
  have hVDleKer : VD ≤ rho.ker := by
    intro v hv
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    let vN : Subgroup.normalizer (F : Set G) := ⟨v, hDnormF v.2⟩
    have hvker : vN ∈ F.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr (hVcentF hvV)
    rw [MonoidHom.mem_ker]
    exact hvker
  have hrange_dvd_index : Nat.card rho.range ∣ VD.index := by
    rw [← Subgroup.index_ker rho]
    exact Subgroup.index_dvd_of_le hVDleKer
  have hrangeOdd : Odd (Nat.card rho.range) :=
    Odd.of_dvd_nat hVindexOdd hrange_dvd_index
  have hrangeDvdAut : Nat.card rho.range ∣ Nat.card (MulAut F) :=
    Subgroup.card_subgroup_dvd_card rho.range
  have hrangeCard : Nat.card rho.range = 1 := by
    rw [hAutcard] at hrangeDvdAut
    rcases (Nat.dvd_prime Nat.prime_two).mp hrangeDvdAut with h1 | h2
    · exact h1
    · rw [h2] at hrangeOdd
      norm_num at hrangeOdd
  have hrangeBot : rho.range = ⊥ :=
    (Subgroup.eq_bot_iff_card (H := rho.range)).mpr hrangeCard
  intro d hd
  let dD : D := ⟨d, hd⟩
  let dN : Subgroup.normalizer (F : Set G) := ⟨d, hDnormF hd⟩
  have hrho : rho dD = 1 := by
    have hmem : rho dD ∈ rho.range := ⟨dD, rfl⟩
    rw [hrangeBot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hdker : dN ∈ F.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    exact hrho
  rw [Subgroup.normalizerMonoidHom_ker] at hdker
  exact hdker

end CFSG.GorensteinWalter
