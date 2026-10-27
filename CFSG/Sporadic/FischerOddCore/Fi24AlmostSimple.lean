module

public import CFSG.Sporadic.FischerOddCore.Fi24Cent
public import CFSG.Sporadic.Fi24.Fischer
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Sporadic.Fi23.Tr.Facts
public import CFSG.Sporadic.Fi22.InvCent
public import CFSG.Sporadic.Fi22.LH.Facts

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.Sporadic.Fi24 (R J JR jR)
open CFSG.Fischer (polarFacts hyperovalFacts)

section Generic

theorem almost_simple_of_aut {Q A : Type*} [Group Q] [Group A] [Finite A] (ψ : A ≃* MulAut Q)
    (B : Subgroup A) (hB : ∀ a : A, a ∈ B ↔ ∃ g : Q, ψ a = MulAut.conj g) (hidx : B.index = 2)
    (hA : ∀ t : A, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set A)) = ⊥)
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* Q))
    (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    (S.index = 1 ∨ S.index = 2) ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  set θ := hS.some
  set f : X →* A := ψ.symm.toMonoidHom.comp (conjTransport θ)
  have hf : Function.Injective f := ψ.symm.injective.comp (conjTransport_injective θ hC)
  have hfS : ∀ s : S, f s = ψ.symm (MulAut.conj (θ s)) := fun s => by
    show ψ.symm (conjTransport θ s) = _
    rw [conjTransport_of_mem]
  have hmap : S.map f = B := by
    ext a
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hB]
      refine ⟨θ ⟨x, hx⟩, ?_⟩
      rw [show f x = f ((⟨x, hx⟩ : S) : X) from rfl, hfS, MulEquiv.apply_symm_apply]
    · intro ha
      obtain ⟨g, hg⟩ := (hB a).1 ha
      refine ⟨θ.symm g, (θ.symm g).2, ?_⟩
      rw [hfS, MulEquiv.apply_symm_apply, ← hg, MulEquiv.symm_apply_apply]
  have hBf : B ≤ f.range := by
    rw [← hmap]
    exact Subgroup.map_le_range _ _
  have hXcard : Nat.card X = Nat.card f.range := Nat.card_congr (Equiv.ofInjective f hf)
  have hScard : Nat.card S = Nat.card B := by
    rw [← hmap]
    exact Nat.card_congr (S.equivMapOfInjective f hf).toEquiv
  have hAcard : Nat.card A = Nat.card B * 2 := by
    rw [← hidx, B.card_mul_index]
  have hpos : 0 < Nat.card B := Nat.card_pos
  obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le hBf
  have hdvd : Nat.card f.range ∣ Nat.card A := Subgroup.card_subgroup_dvd_card _
  have hq2 : q ∣ 2 := by
    rw [hq, hAcard] at hdvd
    exact (Nat.mul_dvd_mul_iff_left hpos).1 hdvd
  have hidxS : S.index = q := by
    have h := S.card_mul_index
    rw [hScard, hXcard, hq] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have hnorm : f.range.Normal := by
    have h := f.range.card_mul_index
    rw [hq, hAcard] at h
    rcases (Nat.dvd_prime Nat.prime_two).1 hq2 with h1 | h1
    · subst h1
      apply Subgroup.normal_of_index_eq_two
      rw [mul_one] at h
      exact Nat.eq_of_mul_eq_mul_left hpos h
    · subst h1
      have h' : Nat.card B * 2 * f.range.index = Nat.card B * 2 * 1 := by rw [h, mul_one]
      rw [Subgroup.index_eq_one.1 (Nat.eq_of_mul_eq_mul_left (by positivity) h')]
      exact Subgroup.normal_top
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hidxS]
    exact (Nat.dvd_prime Nat.prime_two).1 hq2
  · have hτ : orderOf (f t) = 2 := by rw [orderOf_injective f hf t, ht]
    have hmap' : (Subgroup.centralizer ({t} : Set X)).map f =
        f.range ⊓ Subgroup.centralizer {f t} := by
      ext p
      rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hx
        exact ⟨⟨x, rfl⟩, by rw [← map_mul, hx, map_mul]⟩
      · rintro ⟨⟨x, rfl⟩, hxt⟩
        refine ⟨x, Subgroup.mem_centralizer_singleton_iff.2 (hf ?_), rfl⟩
        rw [map_mul, map_mul, hxt]
    have hK : ((f.range ⊓ Subgroup.centralizer {f t}).subgroupOf
        (Subgroup.centralizer {f t})).Normal := by
      refine ⟨fun n hn c => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnR, hnc⟩ := Subgroup.mem_inf.1 hn
      exact Subgroup.mem_inf.2 ⟨hnorm.conj_mem _ hnR _,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hnc) (Subgroup.inv_mem _ c.2)⟩
    have hodd := oddCore_eq_bot_of_normal_le inf_le_right hK (hA (f t) hτ)
    have e : ↥(Subgroup.centralizer ({t} : Set X)) ≃* ↥(f.range ⊓ Subgroup.centralizer {f t}) :=
      ((Subgroup.centralizer ({t} : Set X)).equivMapOfInjective f hf).trans
        (MulEquiv.subgroupCongr hmap')
    exact oddCore_eq_bot_of_mulEquiv e.symm hodd

theorem generalized_fitting_of_aut {Q A : Type*} [Group Q] [Group A] [Finite A]
    (hZ : Subgroup.center Q = ⊥) (ψ : A ≃* MulAut Q) (B : Subgroup A)
    (hB : ∀ a : A, a ∈ B ↔ ∃ g : Q, ψ a = MulAut.conj g) (hidx : B.index = 2)
    (hA : ∀ t : A, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set A)) = ⊥)
    {X : Type*} [Group X] [Finite X] (hJ : Nonempty (CFSG.generalizedFitting X ≃* Q)) :
    ((CFSG.generalizedFitting X).index = 1 ∨ (CFSG.generalizedFitting X).index = 2) ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  exact almost_simple_of_aut ψ B hB hidx hA _ hJ
    (centralizer_generalizedFitting_eq_bot_of_center (center_eq_bot_of_mulEquiv hJ.some hZ))

end Generic

@[expose] def fi24AutEquiv :
    R ≃* MulAut Blueprint.NativeSporadic.Fi24prime :=
  Fi24.rEquivAut polarFacts hyperovalFacts (Fi22.fi22Facts polarFacts hyperovalFacts)
    (Fi23.fi23Facts (Fi22.fi22Facts polarFacts hyperovalFacts)) Fi22.card_fixed_involution_D
    Fi22.eq_of_commute_centralizer Fi24.edgeSwap_a Fi23.d1_mem_localClass Fi23.involution_cover

theorem fi24AutEquiv_jR
    (g : J) :
    fi24AutEquiv (jR g) = MulAut.conj (Fi24.fi24EquivJ.symm g) := by
  refine MulEquiv.ext fun x => ?_
  simp only [fi24AutEquiv, Fi24.rEquivAut, MulEquiv.trans_apply, Fi24.mulAutEquivR,
    MulAut.congr_apply]
  change Fi24.fi24EquivJ.symm (Fi24.conjJ (jR g) (Fi24.fi24EquivJ.symm.symm x)) = _
  rw [Fi24.conjJ_jR, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

theorem fi24_mem_JR_iff
    (a : R) :
    a ∈ JR ↔ ∃ g : Blueprint.NativeSporadic.Fi24prime, fi24AutEquiv a = MulAut.conj g := by
  constructor
  · intro ha
    obtain ⟨j, rfl⟩ : a ∈ jR.range := by
      rw [Fi24.range_jR]
      exact ha
    exact ⟨_, fi24AutEquiv_jR j⟩
  · rintro ⟨g, hg⟩
    have h : a = jR (Fi24.fi24EquivJ g) := by
      apply fi24AutEquiv.injective
      rw [hg, fi24AutEquiv_jR, MulEquiv.symm_apply_apply]
    rw [h]
    exact Fi24.jR_mem_JR _

theorem center_fi24prime :
    Subgroup.center Blueprint.NativeSporadic.Fi24prime = ⊥ :=
  @center_eq_bot_of_mulEquiv Blueprint.NativeSporadic.Fi24prime J Units.instGroup inferInstance
    Fi24.fi24EquivJ Fi24.center_J

theorem fi24_hA :
    ∀ t : R, orderOf t = 2 →
    CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set R)) = ⊥ := fun t ht =>
  (CTUC_Fi24_all_extension_involution_centralizers_odd_core_trivial t ht).1

theorem CTUC_Fi24prime_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (S : Subgroup X) [S.Normal]
    (hS : Nonempty (S ≃* Blueprint.NativeSporadic.Fi24prime))
    (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    (S.index = 1 ∨ S.index = 2) ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ :=
  @almost_simple_of_aut Blueprint.NativeSporadic.Fi24prime R Units.instGroup inferInstance
    inferInstance fi24AutEquiv JR fi24_mem_JR_iff Fi24.index_JR fi24_hA X _ _ S _ hS hC

theorem CTUC_Fi24prime_generalized_Fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (_hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.Fi24prime)) :
    ((CFSG.generalizedFitting X).index = 1 ∨ (CFSG.generalizedFitting X).index = 2) ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ :=
  @generalized_fitting_of_aut Blueprint.NativeSporadic.Fi24prime R Units.instGroup inferInstance
    inferInstance center_fi24prime fi24AutEquiv JR fi24_mem_JR_iff Fi24.index_JR fi24_hA X _ _ hJ

end CFSG.Sporadic.FischerOddCore
