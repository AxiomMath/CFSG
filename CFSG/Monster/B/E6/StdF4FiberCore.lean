module

public import CFSG.Monster.B.E6.StdF4FiberProd

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup parStar thetaFirst SUFrob
  thetaFirst_surjective thetaFirst_eq_one_iff eq_one_of_forall_smul_SUFrob SUFrob_smul_one ZSU)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open MulAction

abbrev radStarP :
    Subgroup (parStar firstJ) := radStar.subgroupOf (parStar firstJ)

theorem radStarP_normal :
    radStarP.Normal :=
  ⟨fun _ hn g => conj_mem_radStar g.2 hn⟩

theorem card_radStarP :
    Nat.card radStarP = 2 ^ 21 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe radStar_le_parStar).toEquiv, card_radStar]

theorem card_isoFlag6 :
    Nat.card IsoFlag6 = 93555 := by
  rw [← Nat.card_congr residueFlag, card_parabolicCosets_firstJ]

theorem pCore_parStar :
    CFSG.pCore 2 (parStar firstJ) = radStarP := by
  refine le_antisymm ?_ (le_sSup ⟨radStarP_normal, IsPGroup.of_card card_radStarP⟩)
  set N := CFSG.pCore 2 (parStar firstJ)
  have hN : IsPGroup 2 (N.map thetaFirst) := CFSG.pCore_isPGroup.map thetaFirst
  have hNn : N.Normal := CFSG.pCore_normal
  have hodd : ¬2 ∣ Nat.card IsoFlag6 := by rw [card_isoFlag6]; norm_num
  obtain ⟨F₀, hF₀⟩ := hN.nonempty_fixed_point_of_prime_not_dvd_card IsoFlag6 hodd
  have hfix0 : ∀ m ∈ N, thetaFirst m • F₀ = F₀ := fun m hm => hF₀ ⟨thetaFirst m, ⟨m, hm, rfl⟩⟩
  intro n hn
  have hfix : ∀ F : IsoFlag6, thetaFirst n • F = F := by
    intro F
    obtain ⟨h, hh⟩ := exists_smul_eq F₀ F
    obtain ⟨γ, hγ⟩ := thetaFirst_surjective ⟨(h : SU6 ⧸ ZSU), 1⟩
    have hγF : thetaFirst γ • F₀ = F := by rw [hγ, SUFrob_smul_one, hh]
    have hm : γ⁻¹ * n * γ ∈ N := by
      have := hNn.conj_mem n hn γ⁻¹
      rwa [inv_inv] at this
    rw [← hγF]
    calc thetaFirst n • thetaFirst γ • F₀ = thetaFirst γ • thetaFirst (γ⁻¹ * n * γ) • F₀ := by
          rw [smul_smul, smul_smul, ← map_mul, ← map_mul]
          congr 2
          group
      _ = thetaFirst γ • F₀ := by rw [hfix0 _ hm]
  have h1 := thetaFirst_eq_one_iff n |>.1 (eq_one_of_forall_smul_SUFrob hfix)
  rw [Subgroup.mem_subgroupOf, mem_radStar]
  exact ⟨h1.2, Subtype.ext h1.1⟩

end CFSG.Monster.B.E6.StdF4
