module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcSplit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwelveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace StepTwoToralExc

theorem seven_le_of_not_dvd_weylE6 {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ 51840) : 7 ≤ p := by
  by_contra hlt
  have h2 := hp.two_le
  interval_cases p
  · exact h (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)

end StepTwoToralExc

open StepTwoToralExc

section SplitWeylSix

theorem ggStepTwoExcSplitWeylOn_E6 : GGStepTwoExcSplitWeylOn .E6 := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hW hq
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hp7 : 7 ≤ p := seven_le_of_not_dvd_weylE6 hp hW
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hq
  let ψ₀ : ↥(e6Data_valid.minGroup (GaloisField 2 f)) →* G := ψ
  have hrange : ψ₀.range = ggG0 p B x L D J := hctx.2.2.2.2.1.1
  have hker : ψ₀.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hπs := e6Isogeny_surjective (GaloisField 2 f)
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny hker
  have hC : Subgroup.centralizer (ψ₀.range : Set G) = ⊥ := by rw [hrange]; exact s1.1
  have hZψ₀ : Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 f)) ≤ ψ₀.ker := by
    intro z hz
    have h1 : ψ₀ z ∈ Subgroup.centralizer (ψ₀.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
    rw [hC, Subgroup.mem_bot] at h1
    exact h1
  have hπψ₀ : (e6Isogeny (GaloisField 2 f)).ker ≤ ψ₀.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.le.trans hZψ₀
  set χ : adjointGroup .E6 (GaloisField 2 f) →* G :=
    ((e6Isogeny (GaloisField 2 f)).liftOfRightInverse (Function.surjInv hπs)
      (Function.rightInverse_surjInv hπs)) ⟨ψ₀, hπψ₀⟩ with hχ
  have hχπ : ∀ u, χ (e6Isogeny (GaloisField 2 f) u) = ψ₀ u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply (e6Isogeny (GaloisField 2 f)) (Function.surjInv hπs)
      (Function.rightInverse_surjInv hπs) ⟨ψ₀, hπψ₀⟩ u
  have hχinj : Function.Injective χ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨u, rfl⟩ := hπs y
    have hu : u ∈ ψ₀.ker := by
      rw [MonoidHom.mem_ker, ← hχπ]
      exact hy
    exact hkπ hu
  have hχr : χ.range = ψ₀.range := by
    ext b
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨u, rfl⟩ := hπs y
      exact ⟨u, (hχπ u).symm⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e6Isogeny (GaloisField 2 f) u, hχπ u⟩
  have hBsR : Bs ≤ ψ₀.range := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (ψ₀.range : Set G) := by
      rw [hrange]
      exact hctx.2.2.2.2.2.2.1.1 hb
    have hbp : b ^ p = 1 := hctx.2.1.2.1.2 b hb
    obtain ⟨a, -, hind⟩ := ExcNonsplit.exists_conj_of_innerDiag_E6 ψ₀ hker hbN
      (hctx.2.2.2.2.2.2.1.2 b hb) hp (by omega) hbp
    obtain ⟨u, rfl⟩ := hπs a
    have hc := (LayerSixE.GGInduces.psi hkπ u).inv.mul hbN hind
    rw [inv_mul_cancel] at hc
    have hcN : (ψ₀ u)⁻¹ * b ∈ Subgroup.normalizer (ψ₀.range : Set G) :=
      mul_mem (inv_mem (Subgroup.le_normalizer ⟨u, rfl⟩)) hbN
    have hcC : (ψ₀ u)⁻¹ * b ∈ Subgroup.centralizer (ψ₀.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      obtain ⟨y', hy'⟩ := LayerSixE.exists_conj_eq hcN y
      have h1 := hc y y' hy'
      rw [MulAut.one_apply] at h1
      have h2 : y⁻¹ * y' ∈ ψ₀.ker :=
        hπψ₀ (by rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel])
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
      have hconj : ((ψ₀ u)⁻¹ * b) * ψ₀ y * ((ψ₀ u)⁻¹ * b)⁻¹ = ψ₀ y := hy'.symm.trans h2.symm
      calc ψ₀ y * ((ψ₀ u)⁻¹ * b) = ((ψ₀ u)⁻¹ * b) * ψ₀ y * ((ψ₀ u)⁻¹ * b)⁻¹ * ((ψ₀ u)⁻¹ * b) := by
            rw [hconj]
        _ = ((ψ₀ u)⁻¹ * b) * ψ₀ y := by group
    rw [hC, Subgroup.mem_bot] at hcC
    have hb : b = ψ₀ u := by
      calc b = ψ₀ u * ((ψ₀ u)⁻¹ * b) := by group
        _ = ψ₀ u := by rw [hcC, mul_one]
    exact ⟨u, hb.symm⟩
  have hBsG₀ : Bs ≤ ggG0 p B x L D J := hrange ▸ hBsR
  obtain ⟨hA, hcomp⟩ := StepTwoSplit.splitWeyl_of_adjAt (τ := .E6) (K := GaloisField 2 f) hp
    hχinj (hχr.trans hrange) hctx.2.1 hBsG₀ (TableBExc.not_dvd_index_torusGroup_E6 hp hp7 hpq)
    (ggExcSplitWeylAdjAt_E6 hp hp7 hpq)
  exact ⟨hA, fun b L₁ hpair => hcomp b hpair.1 hpair.2.1 L₁ hpair.2.2.1⟩

end SplitWeylSix

section Bundle

@[expose] def GGStepTwoToralExcRest : Prop :=
  GGStepTwoToralWitnessExcRestOn .F4 ∧ GGStepTwoToralWitnessExcRestOn .E6 ∧
    GGStepTwoToralWitnessExcRestOn .E7 ∧ GGStepTwoToralWitnessExcRestOn .E8 ∧
      GGStepTwoToralWitnessOn .twistedE6

theorem ggStepTwoToralRound12_of_excRest (h : GGStepTwoToralExcRest) : GGStepTwoToralRound12 :=
  ⟨ggStepTwoToralWitnessOn_of_excRest ggStepTwoExcSplitWeylOn_F4 h.1,
    ggStepTwoToralWitnessOn_of_excRest ggStepTwoExcSplitWeylOn_E6 h.2.1,
    ggStepTwoToralWitnessOn_of_excRest ggStepTwoExcSplitWeylOn_E7 h.2.2.1,
    ggStepTwoToralWitnessOn_of_excRest ggStepTwoExcSplitWeylOn_E8 h.2.2.2.1, h.2.2.2.2⟩

end Bundle

end CFSG.StandardType
