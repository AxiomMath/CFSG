module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Timmesfeld.Orders.Bang
import CFSG.RankThree.Literature.Stroth80Artin
import CFSG.GF2Type.Smith1979.W4AsSurvNine
import CFSG.GroupTheory.RegularRepGF2
import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open CFSG.Timmesfeld Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (dMinDeg)

theorem nontrivial_of_isQuasisimple {X : Type*} [Group X] (hX : CFSG.Open.IsQuasisimple X) :
    Nontrivial X :=
  haveI := hX.2.toNontrivial
  (QuotientGroup.mk_surjective (s := Subgroup.center X)).nontrivial

theorem center_quotient_center_eq_bot {X : Type*} [Group X] (hX : CFSG.Open.IsQuasisimple X) :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
  CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hX)

theorem ker_le_center_of_isQuasisimple {X H : Type*} [Group X] [Group H]
    (hX : CFSG.Open.IsQuasisimple X) (f : X →* H) (hf : f ≠ 1) : f.ker ≤ Subgroup.center X :=
  CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hX) (by
      by_contra h
      exact hf (MonoidHom.ext fun k => by
        by_contra hk
        exact h ⟨k, hk⟩))

theorem orderOf_dvd_orderOf_of_ker_le_center {X H S : Type*} [Group X] [Group H] [Group S]
    (f : X →* H) (hf : f.ker ≤ Subgroup.center X) (ψ : X →* S) (hψ : Function.Surjective ψ)
    (hS : Subgroup.center S = ⊥) (x : X) : orderOf (ψ x) ∣ orderOf (f x) := by
  have hker : Subgroup.center X ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hz' : ψ z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hS] at hz'
    exact hz'
  have hx : x ^ orderOf (f x) ∈ ψ.ker :=
    hker (hf (by rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]))
  rw [MonoidHom.mem_ker, map_pow] at hx
  exact orderOf_dvd_of_pow_eq_one hx

theorem exists_orderOf_eq_of_quotient {X S : Type*} [Group X] [Finite X] [Group S]
    (hX : CFSG.Open.IsQuasisimple X) (ψ : X →* S) (hψ : Function.Surjective ψ)
    (hS : Subgroup.center S = ⊥) {d : ℕ} (f : X →* GL (Fin d) (ZMod 2)) (hf : f ≠ 1) (s : S) :
    ∃ g : GL (Fin d) (ZMod 2), orderOf g = orderOf s := by
  obtain ⟨x, rfl⟩ := hψ s
  haveI : Finite (GL (Fin d) (ZMod 2)) := inferInstance
  have hdvd : orderOf (ψ x) ∣ orderOf (f x) :=
    orderOf_dvd_orderOf_of_ker_le_center f (ker_le_center_of_isQuasisimple hX f hf) ψ hψ hS x
  exact ⟨f x ^ (orderOf (f x) / orderOf (ψ x)),
    orderOf_pow_orderOf_div (orderOf_pos (f x)).ne' hdvd⟩

theorem le_of_orderOf_eq_ppd {d k p : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (g : GL (Fin d) (ZMod 2)) (hg : orderOf g = p) : k ≤ d := by
  by_contra h
  have hd : d < k := Nat.lt_of_not_le h
  have hord : orderOf (2 : ZMod p) = k :=
    CFSG.RankThree.GF2n.Stroth80.orderOf_two_zmod_eq_of_primitive hp.prime hk hp.dvd hp.2.2
  have hdvd : p ∣ Nat.card (GL (Fin d) (ZMod 2)) := hg ▸ orderOf_dvd_natCard g
  exact CFSG.RankThree.GF2n.stroth37_artin_primitive_prime_not_dvd_card_gl hk hd hp.prime hord
    hdvd

theorem six_le_of_orderOf_eq_nine {d : ℕ} (g : GL (Fin d) (ZMod 2)) (hg : orderOf g = 9) :
    6 ≤ d := by
  letI : AddCommGroup (Fin d → ZMod 2) :=
    { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }
  letI : Module (ZMod 2) (Fin d → ZMod 2) := Pi.Function.module (Fin d) (ZMod 2) (ZMod 2)
  haveI : FiniteDimensional (ZMod 2) (Fin d → ZMod 2) := inferInstance
  let σ : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin d → ZMod 2)
      (Matrix.GeneralLinearGroup.toLin g)
  have hσ : orderOf σ = 9 := by
    have h2 : orderOf σ = orderOf (Matrix.GeneralLinearGroup.toLin g) :=
      MulEquiv.orderOf_eq _ _
    have h1 : orderOf (Matrix.GeneralLinearGroup.toLin g) = orderOf g :=
      MulEquiv.orderOf_eq _ _
    rw [h2, h1, hg]
  have h := CFSG.GF2Type.Smith1979.W4As.Surv.six_le_finrank_of_orderOf_eq_nine (σ := σ) hσ
  rwa [Module.finrank_fin_fun] at h

theorem le_dMinDeg {X : Type} [Group X] [Finite X] [Nontrivial X] {D : ℕ}
    (h : ∀ (d : ℕ) (f : X →* GL (Fin d) (ZMod 2)), f ≠ 1 → D ≤ d) : D ≤ dMinDeg X := by
  obtain ⟨n, f, hf⟩ := CFSG.GroupTheory.exists_nontrivial_repr_card X
  have hne : {m : ℕ | ∃ f : X →* GL (Fin m) (ZMod 2), f ≠ 1}.Nonempty := ⟨n, f, hf⟩
  obtain ⟨f', hf'⟩ := Nat.sInf_mem hne
  exact h _ f' hf'

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
