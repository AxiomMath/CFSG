module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup

theorem coprime_fitting_centralizer_component_action_injection {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) (hW : W ≤ centralizer (fittingSubgroup G : Set G))
    (hcop : Nat.Coprime (Nat.card W) (Nat.card (fittingSubgroup G)))
    (hnorm : ∀ L : Subgroup G, IsComponent L → W ≤ normalizer (L : Set G)) :
    ∃ φ : W →* ((L : {L : Subgroup G // IsComponent L}) → MulAut (L : Subgroup G)),
      (∀ (w : W) (L : {L : Subgroup G // IsComponent L}) (x : (L : Subgroup G)),
        ((φ w L x : (L : Subgroup G)) : G) = (w : G) * x * (w : G)⁻¹) ∧
      Function.Injective φ ∧
      ((∀ (L : Subgroup G) (hL : IsComponent L),
          Odd (Nat.card (L.normalizerMonoidHom.comp (inclusion (hnorm L hL))).range)) →
        Odd (Nat.card W)) ∧
      ((∀ L : Subgroup G, ¬ IsComponent L) → W = ⊥) := by
  classical
  let φL : ∀ L : {L : Subgroup G // IsComponent L}, W →* MulAut (L : Subgroup G) := fun L =>
    (L : Subgroup G).normalizerMonoidHom.comp (inclusion (hnorm L L.2))
  let φ : W →* ((L : {L : Subgroup G // IsComponent L}) → MulAut (L : Subgroup G)) :=
    MonoidHom.pi φL
  have hφ : ∀ (w : W) (L : {L : Subgroup G // IsComponent L}) (x : (L : Subgroup G)),
      ((φ w L x : (L : Subgroup G)) : G) = (w : G) * x * (w : G)⁻¹ := fun _ _ _ => rfl
  have hGF : (generalizedFitting G).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hker : ∀ w : W, φ w = 1 → w = 1 := by
    intro w hw
    have hcomp : ∀ L : Subgroup G, IsComponent L → L ≤ centralizer {(w : G)} := by
      intro L hL x hx
      have h1 : (w : G) * x * (w : G)⁻¹ = x := by
        have := congrArg (fun σ : MulAut L => ((σ ⟨x, hx⟩ : L) : G)) (congrFun hw ⟨L, hL⟩)
        exact this
      rw [mem_centralizer_singleton_iff]
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    have hfit : fittingSubgroup G ≤ centralizer {(w : G)} := by
      intro x hx
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp (hW w.2) x hx
    have hgf : generalizedFitting G ≤ centralizer {(w : G)} :=
      sup_le hfit (sSup_le fun L hL => hcomp L hL)
    have hwC : (w : G) ∈ centralizer (generalizedFitting G : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.mp (hgf hh)
    have hwF : (w : G) ∈ generalizedFitting G := CFSG.centralizer_generalizedFitting_le G hwC
    set A := generalizedFitting G ⊓ centralizer (generalizedFitting G : Set G) with hAdef
    have hAcomm : IsMulCommutative A :=
      ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.mp b.2.2 a a.2.1)⟩⟩
    have hAF : A ≤ fittingSubgroup G :=
      CFSG.LocalCores.fitting_characteristic.2.2 A inferInstance inferInstance
    have hwFit : (w : G) ∈ fittingSubgroup G := hAF ⟨hwF, hwC⟩
    exact Subtype.ext ((Subgroup.disjoint_def.mp (Subgroup.disjoint_of_coprime_natCard hcop))
      w.2 hwFit)
  have hinj : Function.Injective φ := (injective_iff_map_eq_one φ).mpr hker
  refine ⟨φ, hφ, hinj, fun hodd => ?_, fun hno => ?_⟩
  · have : Fintype {L : Subgroup G // IsComponent L} := Fintype.ofFinite _
    let ψ : W →* ((L : {L : Subgroup G // IsComponent L}) → (φL L).range) :=
      MonoidHom.pi fun L => (φL L).rangeRestrict
    have hψ : Function.Injective ψ := by
      intro a b hab
      apply hinj
      funext L
      exact congrArg Subtype.val (congrFun hab L)
    have hdvd := Subgroup.card_dvd_of_injective ψ hψ
    rw [Nat.card_pi] at hdvd
    refine Odd.of_dvd_nat (Nat.not_even_iff_odd.mp fun he => ?_) hdvd
    obtain ⟨L, -, hL⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp (even_iff_two_dvd.mp he)
    exact (hodd L L.2).not_two_dvd_nat hL
  · rw [eq_bot_iff]
    intro w hw
    have h1 : φ ⟨w, hw⟩ = φ 1 := funext fun L => absurd L.2 (hno L)
    exact congrArg Subtype.val (hinj h1)

end CFSG.RankThree.GroupTheory
