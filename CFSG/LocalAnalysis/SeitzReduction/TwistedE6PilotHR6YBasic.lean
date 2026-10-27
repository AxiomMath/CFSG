module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYMinus
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotRoots
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToral
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LieType.Chevalley.C2E6StandardLeviFactors
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

local instance twistedE6PilotHR6YNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def d4CentralDiag (μ ν : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  Pi.mulSingle 0 μ * Pi.mulSingle 5 ν

variable (K) in
@[expose] def d4CentralHom : Kˣ × Kˣ →* (Fin Tag.E6.rank → Kˣ) :=
  (MonoidHom.mulSingle (fun _ => Kˣ) 0).comp (MonoidHom.fst Kˣ Kˣ) *
    (MonoidHom.mulSingle (fun _ => Kˣ) 5).comp (MonoidHom.snd Kˣ Kˣ)

theorem d4CentralHom_apply (p : Kˣ × Kˣ) : d4CentralHom K p = d4CentralDiag p.1 p.2 :=
  rfl

section Defs


variable (K) in
@[expose] noncomputable def d4CentralTorus : Subgroup (ModGL Tag.E6 K) :=
  ((rootDiagUnitHom Tag.E6 K).comp (d4CentralHom K)).range

@[expose] noncomputable def w1Torus {k : Type} [Field k] (ι : k →+* K) :
    Subgroup (ModGL Tag.E6 K) :=
  ((((rootDiagUnitHom Tag.E6 K).comp (d4CentralHom K)).comp
    ((MonoidHom.id Kˣ).prod (MonoidHom.id Kˣ))).comp (Units.map ι.toMonoidHom)).range

theorem mem_d4CentralTorus {g : ModGL Tag.E6 K} :
    g ∈ d4CentralTorus K ↔ ∃ μ ν : Kˣ, rootDiagUnit Tag.E6 (d4CentralDiag μ ν) = g :=
  ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩, fun ⟨μ, ν, h⟩ => ⟨(μ, ν), h⟩⟩

theorem mem_w1Torus {k : Type} [Field k] {ι : k →+* K} {g : ModGL Tag.E6 K} :
    g ∈ w1Torus ι ↔ ∃ l : kˣ, rootDiagUnit Tag.E6
      (d4CentralDiag (Units.map ι.toMonoidHom l) (Units.map ι.toMonoidHom l)) = g :=
  Iff.rfl

theorem w1Torus_le_d4CentralTorus {k : Type} [Field k] (ι : k →+* K) :
    w1Torus ι ≤ d4CentralTorus K := by
  rintro _ ⟨l, rfl⟩
  exact ⟨_, rfl⟩

end Defs

theorem rootChar_d4CentralDiag (μ ν : Kˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (d4CentralDiag μ ν) v = μ ^ v 0 * ν ^ v 5 := by
  rw [rootChar, d4CentralDiag]
  change ∏ i : Fin 6, ((Pi.mulSingle (0 : Fin 6) μ * Pi.mulSingle (5 : Fin 6) ν :
    Fin 6 → Kˣ) i) ^ v i = _
  simp [Fin.prod_univ_succ, Pi.mulSingle_apply]
  rfl

theorem coeff_check : ∀ δ ∈ rootFinset .E6,
    (δ 0 = -1 ∨ δ 0 = 0 ∨ δ 0 = 1) ∧ (δ 5 = -1 ∨ δ 5 = 0 ∨ δ 5 = 1) ∧
      (δ 0 + δ 5 = 0 → δ 0 = 0 ∧ δ 5 = 0) := by
  decide +kernel

section Roots

variable {δ : Fin Tag.E6.rank → ℤ}

theorem coeff_zero_bound (hδ : IsRoot .E6 δ) : -1 ≤ δ 0 ∧ δ 0 ≤ 1 := by
  rcases (coeff_check δ (mem_rootFinset.2 hδ)).1 with h | h | h <;> omega

theorem coeff_five_bound (hδ : IsRoot .E6 δ) : -1 ≤ δ 5 ∧ δ 5 ≤ 1 := by
  rcases (coeff_check δ (mem_rootFinset.2 hδ)).2.1 with h | h | h <;> omega

theorem coeff_zero_five_eq_zero (hδ : IsRoot .E6 δ) (h : δ 0 + δ 5 = 0) :
    δ 0 = 0 ∧ δ 5 = 0 :=
  (coeff_check δ (mem_rootFinset.2 hδ)).2.2 h

theorem mem_parabolicRoots_setD_iff :
    δ ∈ parabolicRoots .E6 setD ↔ IsRoot .E6 δ ∧ δ 0 = 0 ∧ δ 5 = 0 := by
  have hD : ∀ i : Fin 6, i ∉ setD ↔ i = 0 ∨ i = 5 := by
    intro i
    fin_cases i <;> simp [setD]
  refine ⟨fun h => ⟨h.1, h.2 0 ((hD 0).2 (Or.inl rfl)), h.2 5 ((hD 5).2 (Or.inr rfl))⟩,
    fun h => ⟨h.1, fun i hi => ?_⟩⟩
  rcases (hD i).1 hi with rfl | rfl
  exacts [h.2.1, h.2.2]

end Roots

theorem eq_zero_of_zpow_eq_one_of_three_le {G : Type*} [Group G] {μ : G} (hμ : 3 ≤ orderOf μ)
    {z : ℤ} (hz : -2 ≤ z ∧ z ≤ 2) (h : μ ^ z = 1) : z = 0 := by
  obtain ⟨h1, h2⟩ := F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf hμ
  exact F4Pilot.eq_zero_of_zpow_eq_one_of_abs_le_two h1 h2 (abs_le.2 hz) h

theorem rootCharKernel_w1Diag {μ : Kˣ} (hμ : 3 ≤ orderOf μ) :
    rootCharKernel (d4CentralDiag μ μ) = parabolicRoots .E6 setD := by
  ext δ
  change (IsRoot Tag.E6 δ ∧ rootChar (d4CentralDiag μ μ) δ = 1) ↔ _
  rw [mem_parabolicRoots_setD_iff, rootChar_d4CentralDiag, ← zpow_add]
  refine and_congr_right fun hδ => ⟨fun h => ?_, fun h => by rw [h.1, h.2, zero_add, zpow_zero]⟩
  have b0 := coeff_zero_bound hδ
  have b5 := coeff_five_bound hδ
  exact coeff_zero_five_eq_zero hδ
    (eq_zero_of_zpow_eq_one_of_three_le hμ ⟨by omega, by omega⟩ h)

theorem parabolicRoots_setD_subset_rootCharKernel (μ ν : Kˣ) :
    parabolicRoots .E6 setD ⊆ rootCharKernel (d4CentralDiag μ ν) := by
  intro δ hδ
  rw [mem_parabolicRoots_setD_iff] at hδ
  refine ⟨hδ.1, ?_⟩
  rw [rootChar_d4CentralDiag, hδ.2.1, hδ.2.2, zpow_zero, zpow_zero, mul_one]

section Central


theorem d4Levi_le_centralizer_d4CentralDiag
    (μ ν : Kˣ) :
    subsystemGroup Tag.E6 K setD ≤
      centralizer {rootDiagUnit Tag.E6 (d4CentralDiag μ ν)} :=
  (subsystemGroup_eq_rootSpan (τ := Tag.E6) (K := K) setD).le.trans
    (rootSpan_le_centralizer _ (parabolicRoots_setD_subset_rootCharKernel μ ν))

theorem d4CentralTorus_le_centralizer :
    d4CentralTorus K ≤
      centralizer (subsystemGroup Tag.E6 K setD : Set (ModGL Tag.E6 K)) := by
  intro z hz
  obtain ⟨μ, ν, rfl⟩ := mem_d4CentralTorus.1 hz
  rw [mem_centralizer_iff]
  intro l hl
  exact mem_centralizer_singleton_iff.1 (d4Levi_le_centralizer_d4CentralDiag μ ν hl)

theorem center_eq_bot_of_isSimpleGroup_of_isPerfect {T : Type*} [Group T] [IsSimpleGroup T]
    [Group.IsPerfect T] : center T = ⊥ := by
  have hnc : ¬ IsMulCommutative T := Group.IsPerfect.not_isMulCommutative T
  rcases (center T).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc

theorem d4CentralTorus_inf_d4Levi
    [IsSimpleGroup (subsystemGroup Tag.E6 K setD)]
    [Group.IsPerfect (subsystemGroup Tag.E6 K setD)] :
    d4CentralTorus K ⊓ subsystemGroup Tag.E6 K setD = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzZ, hzD⟩ := mem_inf.1 hz
  have hc : (⟨z, hzD⟩ : subsystemGroup Tag.E6 K setD) ∈
      center (subsystemGroup Tag.E6 K setD) := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.1 (d4CentralTorus_le_centralizer hzZ) l l.2)
  rw [center_eq_bot_of_isSimpleGroup_of_isPerfect, mem_bot] at hc
  exact mem_bot.2 (congrArg Subtype.val hc)

theorem twistHom_rootDiagUnit_d4CentralDiag (σ : K →+* K) (μ ν : Kˣ) :
    twistHom TwistTag.E6 K σ (rootDiagUnit Tag.E6 (d4CentralDiag μ ν)) =
      rootDiagUnit Tag.E6
        (d4CentralDiag (Units.map σ.toMonoidHom ν) (Units.map σ.toMonoidHom μ)) := by
  refine (twistHom_rootDiagUnit_eq (t := TwistTag.E6) (σ := σ) (d4CentralDiag μ ν)).trans ?_
  congr 1
  funext i
  have hs : ∀ i : Fin 6, (Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i =
      ![5, 1, 4, 3, 2, 0] i := by decide
  revert i
  change ∀ i : Fin 6, Units.map σ.toMonoidHom ((Pi.mulSingle (0 : Fin 6) μ *
    Pi.mulSingle (5 : Fin 6) ν : Fin 6 → Kˣ) ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i)) =
      (Pi.mulSingle (0 : Fin 6) (Units.map σ.toMonoidHom ν) *
        Pi.mulSingle (5 : Fin 6) (Units.map σ.toMonoidHom μ) : Fin 6 → Kˣ) i
  intro i
  rw [hs]
  fin_cases i <;> simp

theorem twistHom_mem_d4CentralTorus (σ : K →+* K) {z : ModGL Tag.E6 K}
    (hz : z ∈ d4CentralTorus K) : twistHom TwistTag.E6 K σ z ∈ d4CentralTorus K := by
  obtain ⟨μ, ν, rfl⟩ := mem_d4CentralTorus.1 hz
  rw [twistHom_rootDiagUnit_d4CentralDiag]
  exact mem_d4CentralTorus.2 ⟨_, _, rfl⟩

end Central

section Torus


theorem cartanChar_zpow' {τ : Tag} (v : Kˣ) (n : Fin τ.rank → ℤ) :
    cartanChar (fun j => v ^ n j) = fun l => v ^ (∑ j, n j * τ.cartan j l) := by
  funext l
  simp only [cartanChar, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]

@[expose] def centralExp (a b : ℤ) : Fin Tag.E6.rank → ℤ :=
  (![a, 0, 0, 0, 0, b] : Fin 6 → ℤ)

@[expose] def torusZeroExp : Fin Tag.E6.rank → ℤ :=
  (![0, -1, -2, -2, -1, 0] : Fin 6 → ℤ)

@[expose] def torusFiveExp : Fin Tag.E6.rank → ℤ :=
  (![0, -1, -1, -2, -2, 0] : Fin 6 → ℤ)

theorem d4CentralDiag_zpow (c : Kˣ) (a b : ℤ) :
    d4CentralDiag (c ^ a) (c ^ b) = fun l => c ^ centralExp a b l := by
  funext l
  revert l
  change ∀ l : Fin 6, (Pi.mulSingle (0 : Fin 6) (c ^ a) * Pi.mulSingle (5 : Fin 6) (c ^ b) :
    Fin 6 → Kˣ) l = c ^ (![a, 0, 0, 0, 0, b] : Fin 6 → ℤ) l
  intro l
  fin_cases l <;> simp

theorem torusZero_exps : ∀ l : Fin Tag.E6.rank,
    2 * Tag.E6.cartan 0 l = centralExp 2 (-1) l +
      ∑ j, torusZeroExp j * Tag.E6.cartan j l := by
  decide

theorem torusFive_exps : ∀ l : Fin Tag.E6.rank,
    2 * Tag.E6.cartan 5 l = centralExp (-1) 2 l +
      ∑ j, torusFiveExp j * Tag.E6.cartan j l := by
  decide

theorem torusElt_zero_sq_eq (c : Kˣ) :
    torusElt Tag.E6 K 0 (c ^ 2) =
      rootDiagUnit Tag.E6 (d4CentralDiag (c ^ (2 : ℤ)) (c ^ (-1 : ℤ))) *
        ((List.finRange Tag.E6.rank).map fun j => torusElt Tag.E6 K j (c ^ torusZeroExp j)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_zpow', torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, d4CentralDiag_zpow]
  congr 1
  funext l
  rw [Pi.mul_apply, ← zpow_add, ← torusZero_exps l, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem torusElt_five_sq_eq (c : Kˣ) :
    torusElt Tag.E6 K 5 (c ^ 2) =
      rootDiagUnit Tag.E6 (d4CentralDiag (c ^ (-1 : ℤ)) (c ^ (2 : ℤ))) *
        ((List.finRange Tag.E6.rank).map fun j => torusElt Tag.E6 K j (c ^ torusFiveExp j)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_zpow', torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, d4CentralDiag_zpow]
  congr 1
  funext l
  rw [Pi.mul_apply, ← zpow_add, ← torusFive_exps l, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem prod_torusElt_mem_d4Levi (c : Kˣ) {e : Fin Tag.E6.rank → ℤ} (h0 : e 0 = 0)
    (h5 : e 5 = 0) :
    ((List.finRange Tag.E6.rank).map fun j => torusElt Tag.E6 K j (c ^ e j)).prod ∈
      subsystemGroup Tag.E6 K setD := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  by_cases hj : j = 0 ∨ j = 5
  · have he : e j = 0 := by rcases hj with rfl | rfl <;> assumption
    rw [he, zpow_zero, torusElt_eq_rootDiagUnit]
    simp only [one_zpow]
    rw [show (fun _ : Fin Tag.E6.rank => (1 : Kˣ)) = 1 from rfl, rootDiagUnit_one]
    exact one_mem _
  · have hjD : j ∈ setD := by
      have : ∀ j : Fin 6, ¬ (j = 0 ∨ j = 5) → j ∈ setD := by
        intro j; fin_cases j <;> simp [setD]
      exact this j hj
    exact subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hjD _)

theorem torusGroup_le_d4CentralTorus_sup (hsq : ∀ u : Kˣ, ∃ c : Kˣ, c ^ 2 = u) :
    torusGroup Tag.E6 K ≤ d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨j, u⟩, rfl⟩
  change torusElt Tag.E6 K j u ∈ d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD
  by_cases h0 : j = 0
  · subst h0
    obtain ⟨c, rfl⟩ := hsq u
    rw [torusElt_zero_sq_eq]
    exact mul_mem (mem_sup_left (mem_d4CentralTorus.2 ⟨_, _, rfl⟩))
      (mem_sup_right (prod_torusElt_mem_d4Levi c rfl rfl))
  by_cases h5 : j = 5
  · subst h5
    obtain ⟨c, rfl⟩ := hsq u
    rw [torusElt_five_sq_eq]
    exact mul_mem (mem_sup_left (mem_d4CentralTorus.2 ⟨_, _, rfl⟩))
      (mem_sup_right (prod_torusElt_mem_d4Levi c rfl rfl))
  · have hjD : j ∈ setD := by
      have : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → j ∈ setD := by
        intro j; fin_cases j <;> simp [setD]
      exact this j h0 h5
    exact mem_sup_right (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hjD _))

end Torus

end CFSG.SeitzReduction.TwistedE6Pilot
