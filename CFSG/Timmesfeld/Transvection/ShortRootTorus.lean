module

public import CFSG.Timmesfeld.Transvection.ShortRoot
public import CFSG.Timmesfeld.Transvection.ShortRootField
import CFSG.Timmesfeld.Transvection.RankTwoRelMain
import CFSG.GroupTheory.Commutator.ScalingInvariant
import CFSG.Timmesfeld.RankOne.SL2Diag

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace SL2Coords

theorem exists_mat_eq_diagElt_of_conjSub_eq {A E : Subgroup G} {k : ℕ}
    (φ : SL2Coords A E k) {t : G} (ht : t ∈ A ⊔ E) (htA : conjSub A t = A)
    (htE : conjSub E t = E) : ∃ μ : (GaloisField 2 k)ˣ, φ.mat t = diagElt μ := by
  have hU : φ.mat t * upperElt (GaloisField 2 k) 1 * (φ.mat t)⁻¹ ∈
      upperUnipotent (GaloisField 2 k) := by
    have he : φ.elt (upperElt (GaloisField 2 k) 1) ∈ E := φ.elt_upperElt_mem 1
    have hmem : t * φ.elt (upperElt (GaloisField 2 k) 1) * t⁻¹ ∈ E := by
      have h := conj_mem_conjSub t he
      rwa [htE] at h
    have hmat : φ.mat (t * φ.elt (upperElt (GaloisField 2 k) 1) * t⁻¹) =
        φ.mat t * upperElt (GaloisField 2 k) 1 * (φ.mat t)⁻¹ := by
      rw [φ.mat_mul (Subgroup.mul_mem _ ht (φ.elt_mem _)) (Subgroup.inv_mem _ ht),
        φ.mat_mul ht (φ.elt_mem _), φ.mat_inv ht, φ.mat_elt]
    rw [← hmat]
    exact (φ.mem_E_iff (Subgroup.mem_sup_right hmem)).1 hmem
  have hL : φ.mat t * lowerElt (GaloisField 2 k) 1 * (φ.mat t)⁻¹ ∈
      lowerUnipotent (GaloisField 2 k) := by
    have he : φ.elt (lowerElt (GaloisField 2 k) 1) ∈ A := φ.elt_lowerElt_mem 1
    have hmem : t * φ.elt (lowerElt (GaloisField 2 k) 1) * t⁻¹ ∈ A := by
      have h := conj_mem_conjSub t he
      rwa [htA] at h
    have hmat : φ.mat (t * φ.elt (lowerElt (GaloisField 2 k) 1) * t⁻¹) =
        φ.mat t * lowerElt (GaloisField 2 k) 1 * (φ.mat t)⁻¹ := by
      rw [φ.mat_mul (Subgroup.mul_mem _ ht (φ.elt_mem _)) (Subgroup.inv_mem _ ht),
        φ.mat_mul ht (φ.elt_mem _), φ.mat_inv ht, φ.mat_elt]
    rw [← hmat]
    exact (φ.mem_A_iff (Subgroup.mem_sup_left hmem)).1 hmem
  exact CFSG.Timmesfeld.RankOne.exists_eq_diagElt_of_conj_mem_unipotent (φ.mat t) hU hL

theorem exists_eq_torusElt_of_conjSub_eq {A E : Subgroup G} {k : ℕ}
    (φ : SL2Coords A E k) {t : G} (ht : t ∈ A ⊔ E) (htA : conjSub A t = A)
    (htE : conjSub E t = E) : ∃ μ : (GaloisField 2 k)ˣ, t = φ.torusElt μ := by
  obtain ⟨μ, hμ⟩ := φ.exists_mat_eq_diagElt_of_conjSub_eq ht htA htE
  exact ⟨μ, φ.mat_injOn ht (φ.torusElt_mem μ) (by rw [hμ, φ.mat_torusElt])⟩

end SL2Coords

namespace PairFrame

theorem exists_mul_commute_shortRootGroup [Finite G] {A E D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hthick : ThickLines Δ) (hq : 4 ≤ Nat.card A) {t : G}
    (ht : t ∈ A ⊔ E) (htA : conjSub A t = A) (htE : conjSub E t = E) :
    ∃ t₁ ∈ D ⊔ E', ∀ x ∈ shortRootGroup Δ A E D E', Commute (t * t₁) x := by
  have hqE : 4 ≤ Nat.card E := by rw [hΔ.root.card_eq P.memE P.memA]; exact hq
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_opposite hΔ.root P.memE P.memA P.oppA.symm
  obtain ⟨φ₀⟩ := nonempty_sl2Coords hΔ.root P.memE P.memA P.oppA.symm hk
  have hk' : Nat.card D = 2 ^ k := (hΔ.root.card_eq P.memD P.memE).trans hk
  obtain ⟨φ₁⟩ := nonempty_sl2Coords hΔ.root P.memD P.memE' P.oppD hk'
  obtain ⟨τ, hτ⟩ := P.flip.exists_aligned_of_meetsLines hΔ hpts hml hthick hqE φ₀ φ₁
  obtain ⟨μ, rfl⟩ := φ₀.exists_eq_torusElt_of_conjSub_eq (by rwa [sup_comm] at ht) htE htA
  exact ⟨(φ₁.map τ).torusElt μ, (φ₁.map τ).torusElt_mem μ, hτ μ⟩

theorem shortRootGroup_eq_inf_commSub [Finite G] {A E D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) (hq : 4 ≤ Nat.card A) {k₁ : ℕ} (φ₁ : SL2Coords D E' k₁)
    {h₁ : G} (hh₁ : h₁ ∈ D ⊔ E') {ν : (GaloisField 2 k₁)ˣ} (hν : φ₁.mat h₁ = diagElt ν)
    (hν1 : ν ≠ 1) :
    shortRootGroup Δ A E D E' =
      lineGroup Δ A D ⊓ lineStab Δ A E' ⊓ commSub (lineGroup Δ A D) h₁ := by
  have hiso : NoIsolated Δ :=
    hΔ.noIsolated hpts ⟨A, P.memA, D, P.memD, P.ne_AD, P.commuting_AD⟩
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq P.memD P.memA]
  obtain ⟨k₀, φ₀, h₀, μ, hh₀, hμ, hμ1⟩ :=
    exists_sl2Coords_torus hΔ.root P.memA P.memE P.oppA hq
  have hsub : shortRootGroup Δ A E D E' ≤
      lineGroup Δ A D ⊓ lineStab Δ A E' ⊓ commSub (lineGroup Δ A D) h₁ := by
    intro x hx
    have hX := P.shortRootGroup_eq_inf hΔ hiso hpts hlines hq φ₀ hh₀ hμ hμ1 φ₁ hh₁ hν hν1
    refine ⟨⟨hx.1.1, hx.2⟩, ?_⟩
    rw [hX] at hx
    exact hx.2
  refine le_antisymm hsub ?_
  intro w hw
  obtain ⟨hwU, hwC⟩ := hw
  have hsw : lineGroup Δ A D ⊓ lineStab Δ A E' = shortRootGroup Δ A E D E' ⊔ A := by
    have hsr : shortRootGroup Δ D E' A E = shortRootGroup Δ A E D E' := by
      rw [shortRootGroup, shortRootGroup, lineGroup_comm D A, lineStab_comm E' A,
        lineStab_comm D E, inf_right_comm]
    have h := P.swap.lineGroup_inf_lineStab hΔ hiso hpts hlines hqD
    rw [lineGroup_comm D A, lineStab_comm E' A, hsr] at h
    exact h
  rw [hsw] at hwU
  have hc : Commuting (shortRootGroup Δ A E D E') A := fun x hx a ha =>
    commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD hx.1.1
      (le_lineGroup (left_mem_lineOf P.memA) ha)
  obtain ⟨x, hx, a, ha, rfl⟩ := mem_sup_of_commuting hc hwU
  have hxcomm : x ∈ commSub (lineGroup Δ A D) h₁ := (hsub hx).2
  have haC : a ∈ commSub (lineGroup Δ A D) h₁ := by
    have h1 : x⁻¹ * (x * a) ∈ commSub (lineGroup Δ A D) h₁ :=
      (commSub _ _).mul_mem ((commSub _ _).inv_mem hxcomm) hwC
    simpa using h1
  have ha1 : a = 1 := by
    have hbot := inf_commSub_lineGroup (E := E') φ₁ hh₁ hν hΔ P.memD P.memA
      P.commuting_AD.symm P.commuting_AE'.symm
    rw [lineGroup_comm D A] at hbot
    have haX : a ∈ A ⊓ commSub (lineGroup Δ A D) h₁ := ⟨ha, haC⟩
    rwa [hbot, Subgroup.mem_bot] at haX
  rw [ha1, mul_one]
  exact hx

theorem shortRootGroup_eq_of_pairFrame [Finite G] {A E E₂ D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (P₂ : PairFrame Δ A E₂ D E') (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ) (hq : 4 ≤ Nat.card A) :
    shortRootGroup Δ A E₂ D E' = shortRootGroup Δ A E D E' := by
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq P.memD P.memA]
  obtain ⟨k₁, φ₁, h₁, ν, hh₁, hν, hν1⟩ :=
    exists_sl2Coords_torus hΔ.root P.memD P.memE' P.oppD hqD
  rw [P₂.shortRootGroup_eq_inf_commSub hΔ hpts hlines hq φ₁ hh₁ hν hν1,
    P.shortRootGroup_eq_inf_commSub hΔ hpts hlines hq φ₁ hh₁ hν hν1]

theorem conjSub_shortRootGroup_of_conjSub_eq [Finite G] {A E D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) (hq : 4 ≤ Nat.card A) {y : G} (hyA : conjSub A y = A)
    (hyD : conjSub D y = D) (hyE' : conjSub E' y = E') :
    conjSub (shortRootGroup Δ A E D E') y = shortRootGroup Δ A E D E' := by
  have P₂ := P.conj hΔ.root y
  rw [hyA, hyD, hyE'] at P₂
  rw [← shortRootGroup_conjSub hΔ.root A E D E' y, hyA, hyD, hyE']
  exact P.shortRootGroup_eq_of_pairFrame P₂ hΔ hpts hlines hq

theorem commuting_shortRootGroup_of_forall_eq_commutatorElement [Finite G]
    {A E D E' : Subgroup G} (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) (hthick : ThickLines Δ)
    (hq : 4 ≤ Nat.card A) {t : G} (ht : t ∈ A ⊔ E) (htA : conjSub A t = A)
    (htE : conjSub E t = E) {K : Subgroup G} (hKA : ∀ y ∈ K, conjSub A y = A)
    (hKD : Commuting K (D ⊔ E')) (hK : ∀ x ∈ K, ∃ y ∈ K, x = ⁅y, t⁆) :
    Commuting K (shortRootGroup Δ A E D E') := by
  obtain ⟨t₁, ht₁, hc⟩ :=
    P.exists_mul_commute_shortRootGroup hΔ hpts hml hthick hq ht htA htE
  have hg : t * t₁ ∈ Subgroup.centralizer (shortRootGroup Δ A E D E' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun x hx => (hc x hx).eq.symm
  have hK' : ∀ y ∈ K, ⁅y, t * t₁⁆ = ⁅y, t⁆ := by
    intro y hy
    rw [commutatorElement_mul_right_eq_mul_conj, (hKD y hy t₁ ht₁).commutator_eq, mul_one,
      mul_inv_cancel_right]
  have hKg : ∀ y ∈ K, y * (t * t₁) * y⁻¹ ∈
      Subgroup.centralizer (shortRootGroup Δ A E D E' : Set G) := by
    intro y hy
    have hyD : conjSub D y = D := conjSub_of_forall_commute fun d hd =>
      hKD y hy d (Subgroup.mem_sup_left hd)
    have hyE' : conjSub E' y = E' := conjSub_of_forall_commute fun e he =>
      hKD y hy e (Subgroup.mem_sup_right he)
    have hXy := P.conjSub_shortRootGroup_of_conjSub_eq hΔ hpts hml hq (hKA y hy) hyD hyE'
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hx' : y⁻¹ * x * y ∈ shortRootGroup Δ A E D E' := by
      rw [← hXy] at hx
      exact mem_conjSub.1 hx
    have hcomm : (y⁻¹ * x * y) * (t * t₁) = (t * t₁) * (y⁻¹ * x * y) :=
      Subgroup.mem_centralizer_iff.1 hg _ hx'
    calc x * (y * (t * t₁) * y⁻¹)
        = y * ((y⁻¹ * x * y) * (t * t₁)) * y⁻¹ := by group
      _ = y * ((t * t₁) * (y⁻¹ * x * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * (t * t₁) * y⁻¹) * x := by group
  have hK'' : ∀ x ∈ K, ∃ y ∈ K, x = ⁅y, t * t₁⁆ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hK x hx
    exact ⟨y, hy, by rw [hK' y hy]; exact hxy⟩
  exact (commuting_iff_le_centralizer.2
    (CFSG.GroupTheory.le_of_forall_eq_commutatorElement hg hKg hK'')).symm

end PairFrame

end CFSG.Timmesfeld.Transvection
