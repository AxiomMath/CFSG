module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat
import CFSG.Adapters.GeneralizedFitting
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Assembly

private theorem ggSpor_center_eq_bot {F : Type*} [Group F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) : Subgroup.center F = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center F := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

private theorem ggSpor_conjNormal_eq_one_centralizes {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] {g : G} (hg : MulAut.conjNormal (H := H) g = 1) :
    g ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h2 := congrArg (fun ψ : MulAut H => ψ ⟨h, hh⟩) hg
  have h3 : g * h * g⁻¹ = h := by
    have := congrArg (fun x : H => (x : G)) h2
    simpa [MulAut.conjNormal_apply] using this
  exact (mul_inv_eq_iff_eq_mul.mp h3).symm

private theorem ggSpor_conjNormal_mem_center {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] {g : G} (hgF : g ∈ H)
    (hg : MulAut.conjNormal (H := H) g = 1) :
    (⟨g, hgF⟩ : H) ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  change (y : G) * g = g * (y : G)
  have h2 := congrArg (fun ψ : MulAut H => ψ y) hg
  have h3 : g * (y : G) * g⁻¹ = (y : G) := by
    have := congrArg (fun x : H => (x : G)) h2
    simpa [MulAut.conjNormal_apply] using this
  exact (mul_inv_eq_iff_eq_mul.mp h3).symm

theorem ggSporK_card_dvd_aut {W K : Type} [Group W] [Finite W] [Group K] {p : ℕ}
    {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat p H E)
    (e : ↥(CFSG.generalizedFitting W) ≃* K) : Nat.card W ∣ Nat.card (MulAut K) := by
  haveI hFnormal : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  obtain ⟨hsimple, hnab, -⟩ := hyp.2.1
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hsimple
  have hcenter : Subgroup.center ↥(CFSG.generalizedFitting W) = ⊥ :=
    ggSpor_center_eq_bot hnab
  have hbender : Subgroup.centralizer
        ((CFSG.generalizedFitting W : Subgroup W) : Set W) ≤
      CFSG.generalizedFitting W := by
    have h := CFSG.Adapters.generalized_fitting_self_centralizing W
    rw [CFSG.Adapters.genFittingFStar_eq_foundations] at h
    exact h
  let φ : W →* MulAut ↥(CFSG.generalizedFitting W) := MulAut.conjNormal
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff φ, Subgroup.eq_bot_iff_forall]
    intro g hg
    have hg1 : φ g = 1 := MonoidHom.mem_ker.mp hg
    have hcent : g ∈ Subgroup.centralizer
        ((CFSG.generalizedFitting W : Subgroup W) : Set W) :=
      ggSpor_conjNormal_eq_one_centralizes (CFSG.generalizedFitting W) hg1
    have hgF : g ∈ CFSG.generalizedFitting W := hbender hcent
    have hgZ : (⟨g, hgF⟩ : ↥(CFSG.generalizedFitting W)) ∈
        Subgroup.center ↥(CFSG.generalizedFitting W) :=
      ggSpor_conjNormal_mem_center (CFSG.generalizedFitting W) hgF hg1
    have hbot : (⟨g, hgF⟩ : ↥(CFSG.generalizedFitting W)) ∈
        (⊥ : Subgroup ↥(CFSG.generalizedFitting W)) := by
      rw [← hcenter]
      exact hgZ
    have h1 : (⟨g, hgF⟩ : ↥(CFSG.generalizedFitting W)) = 1 :=
      Subgroup.mem_bot.mp hbot
    simpa using congrArg Subtype.val h1
  have hdvd : Nat.card W ∣ Nat.card (MulAut ↥(CFSG.generalizedFitting W)) :=
    Subgroup.card_dvd_of_injective φ hinj
  rw [Nat.card_congr (MulAut.congr e).toEquiv] at hdvd
  exact hdvd

end CFSG.StandardType.SporadicShape
