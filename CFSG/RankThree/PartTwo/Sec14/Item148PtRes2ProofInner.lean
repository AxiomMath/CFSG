module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofInndiag
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

namespace Item148PtRes2

variable {K : Type} [Field K]

theorem commutator_projImage_glPi_le {π : Bool} {p f : ℕ}
    (hπ : π = false → UnitaryFieldData p f K) :
    ⁅projImage (glPi π 3 (p ^ f) K), projImage (glPi π 3 (p ^ f) K)⁆ ≤
      projImage (slPi π 3 (p ^ f) K) := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
  refine ⟨⁅g, h⁆, (mem_slPi_iff hπ).mpr ⟨?_, ?_⟩, by rw [map_commutatorElement]⟩
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  · rw [← GeneralLinearGroup.val_det_apply, map_commutatorElement, commutatorElement_def,
      mul_right_comm (GeneralLinearGroup.det g), mul_inv_cancel, one_mul, mul_inv_cancel,
      Units.val_one]

theorem solvable_or_simple {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) :
    Group.IsSolvable (projImage (slPi π 3 (p ^ f) K)) ∨
      (2 < p ^ f ∧ IsSimpleGroup (projImage (slPi π 3 (p ^ f) K))) := by
  have hp := hK.prime
  have hf := hK.one_le
  have hq2' : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
  by_cases hq2 : 2 < p ^ f
  · refine Or.inr ⟨hq2, ?_⟩
    cases π
    · have := hK.finite
      have : Fact p.Prime := ⟨hp⟩
      have hcard : Nat.card K = (p ^ f) ^ 2 := hK.card
      have hs : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ f) K)) :=
        CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hcard 3 le_rfl
          (fun h => by
            have := (Prod.mk.inj h).2
            omega)
      have hs' : IsSimpleGroup (StatedProj (slPi false 3 (p ^ f) K)) := hs
      exact (Census.statedProjEquivProjImage (slPi false 3 (p ^ f) K)).symm.isSimpleGroup
    · rw [← projSL_eq_projImage]
      exact Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field K
  · have h2 : p ^ f = 2 := by omega
    cases π
    · exact Or.inl (Sec13.isSolvable_projImage_slPi_two hK h2)
    · exfalso
      change p ^ f % 3 = 1 at hq
      omega

theorem eq_one_of_isPerfect {X C : Type*} [Group X] [Group.IsPerfect X] [CommGroup C]
    (φ : X →* C) (x : X) : φ x = 1 := by
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := X)]
    exact Abelianization.commutator_subset_ker φ
  exact (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top x)

end Item148PtRes2

open Item148PtRes2 Proof142Res

theorem kf148PGLInnerV : KF148PGLInnerV := by
  intro Γ _ _ J E V p f _ hX hJp _ hEJ hVJ hEV hV3 hVE
  classical
  by_cases hJt : ∀ j ∈ J, j = 1
  · intro v _
    refine Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.mpr fun j hj => ?_)
    rw [hJt j hj, one_mul, mul_one]
  push Not at hJt
  obtain ⟨j₀, hj₀, hj₀1⟩ := hJt
  have hJnt : Nontrivial ↥J := ⟨⟨⟨j₀, hj₀⟩, 1, fun h => hj₀1 (congrArg Subtype.val h)⟩⟩
  have := hJp
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := hX
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hJX : J ≤ J ⊔ E := le_sup_left
  have hXN : J ⊔ E ≤ Subgroup.normalizer (J : Set Γ) := sup_le Subgroup.le_normalizer hEJ
  have hSP : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (slPi_le_glPi hπ)
  set φ₀ : ↥J →* Multiplicative (ZMod 3) × ↥(projImage (glPi π 3 (p ^ f) K)) :=
    φ.toMonoidHom.comp (Subgroup.inclusion hJX) with hφ₀
  set τ : ↥J →* ProjGenLinGroup (Fin 3) K :=
    (projImage (glPi π 3 (p ^ f) K)).subtype.comp ((MonoidHom.snd _ _).comp φ₀) with hτ
  have hτapp : ∀ j : ↥J, τ j = ((φ₀ j).2 : ProjGenLinGroup (Fin 3) K) := fun j => rfl
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h1 : (φ₀ j).1 = 1 := eq_one_of_isPerfect ((MonoidHom.fst _ _).comp φ₀) j
    have h2 : (φ₀ j).2 = 1 := Subtype.ext (by rw [← hτapp]; exact hj)
    have h12 : φ (Subgroup.inclusion hJX j) = 1 := Prod.ext h1 h2
    have h3 : Subgroup.inclusion hJX j = 1 := φ.injective (h12.trans (map_one φ).symm)
    exact Subgroup.inclusion_injective hJX (h3.trans (map_one _).symm)
  have hrangeP : τ.range ≤ projImage (glPi π 3 (p ^ f) K) := by
    rintro _ ⟨j, rfl⟩
    exact (φ₀ j).2.2
  have hrangeS : τ.range ≤ projImage (slPi π 3 (p ^ f) K) := by
    have : Group.IsPerfect τ.range := Group.IsPerfect.range τ
    rw [← Subgroup.commutator_eq_self (H := τ.range)]
    exact (Subgroup.commutator_mono hrangeP hrangeP).trans (commutator_projImage_glPi_le hπ)
  have hconj : ∀ (x : ↥(J ⊔ E)) (j : ↥J) (hj : (x : Γ) * (j : Γ) * (x : Γ)⁻¹ ∈ J),
      τ ⟨_, hj⟩ = ((φ x).2 : ProjGenLinGroup (Fin 3) K) * τ j *
        ((φ x).2 : ProjGenLinGroup (Fin 3) K)⁻¹ := by
    intro x j hj
    have e1 : Subgroup.inclusion hJX ⟨_, hj⟩ = x * Subgroup.inclusion hJX j * x⁻¹ :=
      Subtype.ext rfl
    rw [hτapp, hτapp, hφ₀, MonoidHom.comp_apply, e1]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, Prod.snd_mul, Subgroup.coe_mul,
      MonoidHom.comp_apply]
    rw [map_inv φ x]
    rfl
  have hnorm : ∀ s ∈ projImage (slPi π 3 (p ^ f) K), ∀ t ∈ τ.range, s * t * s⁻¹ ∈ τ.range := by
    rintro s hs _ ⟨j, rfl⟩
    set x : ↥(J ⊔ E) := φ.symm (1, ⟨s, hSP hs⟩) with hx
    have hxs : ((φ x).2 : ProjGenLinGroup (Fin 3) K) = s := by
      rw [hx, MulEquiv.apply_symm_apply]
    have hj' : (x : Γ) * (j : Γ) * (x : Γ)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hXN x.2) j).mp j.2
    exact ⟨⟨_, hj'⟩, by rw [hconj x j hj', hxs]⟩
  rcases solvable_or_simple hK hq with hsol | ⟨hq2, hsimp⟩
  · exfalso
    have hJs : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective
        (f := τ.codRestrict (projImage (slPi π 3 (p ^ f) K)) fun j => hrangeS ⟨j, rfl⟩)
        (fun a b hab => hτinj (by simpa using congrArg Subtype.val hab))
    exact Group.IsPerfect.not_isSolvable ↥J hJs
  have hrange : τ.range = projImage (slPi π 3 (p ^ f) K) := by
    have hN : (τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K))).Normal :=
      ⟨fun t ht s => by
        rw [Subgroup.mem_subgroupOf] at ht ⊢
        exact hnorm s s.2 t ht⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K))) with hb | ht
    · exfalso
      have hj₀ : τ ⟨j₀, hj₀⟩ = 1 := by
        have h1 : (⟨τ ⟨j₀, hj₀⟩, hrangeS ⟨_, rfl⟩⟩ : ↥(projImage (slPi π 3 (p ^ f) K))) ∈
            τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K)) :=
          Subgroup.mem_subgroupOf.mpr ⟨_, rfl⟩
        rw [hb, Subgroup.mem_bot] at h1
        exact congrArg Subtype.val h1
      have := hτinj (hj₀.trans (map_one τ).symm)
      exact hj₀1 (congrArg Subtype.val this)
    · refine le_antisymm hrangeS fun s hs => ?_
      have h1 : (⟨s, hs⟩ : ↥(projImage (slPi π 3 (p ^ f) K))) ∈
          τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K)) := by
        rw [ht]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
  set ψ : ↥J ≃* ↥(projImage (slPi π 3 (p ^ f) K)) :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hrange) with hψ
  have hψapp : ∀ j : ↥J, ((ψ j : ↥(projImage (slPi π 3 (p ^ f) K))) :
      ProjGenLinGroup (Fin 3) K) = τ j := fun j => rfl
  set ρ : Subgroup.normalizer (J : Set Γ) →* MulAut ↥(projImage (slPi π 3 (p ^ f) K)) :=
    (MulAut.congr ψ).toMonoidHom.comp J.normalizerMonoidHom with hρ
  have hρapp : ∀ (n : Subgroup.normalizer (J : Set Γ)) (j : ↥J),
      ρ n (ψ j) = ψ (J.normalizerMonoidHom n j) := by
    intro n j
    change ψ (J.normalizerMonoidHom n (ψ.symm (ψ j))) = _
    rw [MulEquiv.symm_apply_apply]
  have hρX : ∀ (x : ↥(J ⊔ E)), ρ ⟨x, hXN x.2⟩ ∈ inndiagPi π (p ^ f) K := by
    intro x
    obtain ⟨g, hg, hgx⟩ := (φ x).2.2
    refine ⟨g, hg, fun s => ?_⟩
    obtain ⟨j, rfl⟩ := ψ.surjective s
    have hj' : (x : Γ) * (j : Γ) * (x : Γ)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hXN x.2) j).mp j.2
    have e1 : J.normalizerMonoidHom ⟨x, hXN x.2⟩ j = ⟨_, hj'⟩ := Subtype.ext rfl
    rw [hρapp, e1, hψapp, hψapp, hconj x j hj', hgx]
  have hNorm := ks142InndiagNormal π p f K hK hq hq2
  set T : Subgroup Γ := ((inndiagPi π (p ^ f) K).comap ρ).map
    (Subgroup.normalizer (J : Set Γ)).subtype with hT
  have hmemT : ∀ g : Γ, g ∈ T ↔ ∃ hg : g ∈ Subgroup.normalizer (J : Set Γ),
      ρ ⟨g, hg⟩ ∈ inndiagPi π (p ^ f) K := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, hg'⟩
    · rintro ⟨hg, hgI⟩
      exact ⟨⟨g, hg⟩, hgI, rfl⟩
  have hVT : V ≤ T := by
    rw [hVE, Subgroup.commutator_le]
    intro v hv e he
    have hvN := hVJ hv
    have heN := hEJ he
    have heI : ρ ⟨e, heN⟩ ∈ inndiagPi π (p ^ f) K := hρX ⟨e, Subgroup.mem_sup_right he⟩
    have hm : ⁅v, e⁆ ∈ Subgroup.normalizer (J : Set Γ) :=
      mul_mem (mul_mem (mul_mem hvN heN) (inv_mem hvN)) (inv_mem heN)
    refine (hmemT _).mpr ⟨hm, ?_⟩
    have e : (⟨⁅v, e⁆, hm⟩ : Subgroup.normalizer (J : Set Γ)) =
        ⟨v, hvN⟩ * ⟨e, heN⟩ * (⟨v, hvN⟩ : Subgroup.normalizer (J : Set Γ))⁻¹ *
          (⟨e, heN⟩ : Subgroup.normalizer (J : Set Γ))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (hNorm.conj_mem _ heI _) (inv_mem heI)
  intro v hv
  obtain ⟨hvN, hvI⟩ := (hmemT v).mp (hVT hv)
  have hcop : Nat.Coprime 3 (orderOf (ρ ⟨v, hvN⟩)) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hV3 ?_
    refine h3.trans ((orderOf_map_dvd ρ _).trans ?_)
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard V hv
  obtain ⟨u, hu⟩ := exists_eq_conj_of_mem_inndiagPi hK hvI hcop
  set j := ψ.symm u with hj
  have hact : ∀ j' : ↥J, (v : Γ) * (j' : Γ) * v⁻¹ = (j : Γ) * (j' : Γ) * (j : Γ)⁻¹ := by
    intro j'
    have h1 : ψ (J.normalizerMonoidHom ⟨v, hvN⟩ j') = ψ (j * j' * j⁻¹) := by
      rw [← hρapp, hu, MulAut.conj_apply, map_mul, map_mul, map_inv, hj,
        MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (ψ.injective h1)
  have hc : (j : Γ)⁻¹ * v ∈ Subgroup.centralizer (J : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hact ⟨y, hy⟩
    calc y * ((j : Γ)⁻¹ * v) = (j : Γ)⁻¹ * ((j : Γ) * y * (j : Γ)⁻¹) * v := by group
      _ = (j : Γ)⁻¹ * (v * y * v⁻¹) * v := by rw [← h1]
      _ = (j : Γ)⁻¹ * v * y := by group
  have hv' : v = (j : Γ) * ((j : Γ)⁻¹ * v) := by group
  rw [hv']
  exact mul_mem (Subgroup.mem_sup_left j.2) (Subgroup.mem_sup_right hc)

end CFSG.RankThree.PartTwo.Sec14
