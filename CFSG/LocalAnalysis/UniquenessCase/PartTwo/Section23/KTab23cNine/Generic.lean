module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Fixed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Concl

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Least

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine

open CFSG.Open CFSG.Quasithin Matrix CFSG.LocalAnalysis.RankThreeUC
  CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE PartTwo Subgroup
open scoped Pointwise commutatorElement

@[expose] def KTab23cNineAt (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) : Prop :=
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  ∀ S : Sylow 2 ↥H,
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    let ℓ : Subgroup W := fixedPointSubgroup ↥S W
    let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
    ∀ Tstar : Subgroup (MulAut W),
      Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
      IsPGroup 2 ↥Tstar →
      (S : Subgroup ↥H).map H.subtype ≤ Tstar →
      let Good : Subgroup ↥H → Prop := fun Pstar =>
        IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ Tstar,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ Pℓ
      ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
        ∀ B : Subgroup ↥H, B ≤ Hinf Pstar → Odd (Nat.card ↥B) →
          B ⊓ fixingSubgroupOf ↥H W (ℓ : Set W) = ⊥

private theorem exists_coord_fixed_of_sylow_le_lineStab {W : Type} [CommGroup W] [Finite W]
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K} (he0 : e₀ ≠ 0)
    (hline : KTabC.SylowFixedLine Γ e₀) (U : Sylow 2 ↥Γ)
    (hU : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀) (S : Sylow 2 ↥H) :
    ∃ (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K)),
      (∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w)) ∧
      (U : Subgroup ↥Γ).map π.toMonoidHom = (S : Subgroup ↥H) ∧
      ∀ v : ι → K,
        (∀ s ∈ (S : Subgroup ↥H),
          (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
          ∃ c : K, v = c • e₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Sbar : Subgroup (MulAut W) := (S : Subgroup ↥H).map H.subtype
  have hSbar : IsSylowIn 2 Sbar H := by
    refine ⟨Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_⟩
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact S.not_dvd_index
  obtain ⟨π, e, he, hπU⟩ := NatBorelIrr.exists_adjusted_natEquiv hreal hSbar U
  have hUS : (U : Subgroup ↥Γ).map π.toMonoidHom = (S : Subgroup ↥H) := by
    rw [hπU, CFSG.subgroupOf_map_subtype_eq]
  have hSU : (S : Subgroup ↥H).map π.symm.toMonoidHom = (U : Subgroup ↥Γ) := by
    have hcomp : π.symm.toMonoidHom.comp π.toMonoidHom = MonoidHom.id ↥Γ := by
      ext g
      simp
    rw [← hUS, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hlineU : ∀ v : ι → K,
      (∀ u ∈ (U : Subgroup ↥Γ), ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • e₀ :=
    fun v => NatBorelIrr.fixed_iff_of_sylow_le_lineStab he0 hline U hU v
  refine ⟨π, e, he, hUS, ?_⟩
  intro v
  rw [KTabC.fixed_iff_fixed_sylowMap π S v]
  have hcoe : ((S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective : Sylow 2 ↥Γ) :
      Subgroup ↥Γ) = (S : Subgroup ↥H).map π.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective S
  rw [hcoe, hSU]
  exact hlineU v

private theorem fixSub_eq_map_vecStab {W : Type} [CommGroup W]
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (S : Sylow 2 ↥H) {e₀ : ι → K}
    (hSfix : ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥H),
        (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • e₀) :
    KSUE.fixSub H S = (KTabC.vecStab Γ.subtype e₀).map π.toMonoidHom := by
  let ρ : ↥H →* GL ι K := Γ.subtype.comp π.symm.toMonoidHom
  have he' : ∀ (h : ↥H) (w : W), Multiplicative.toAdd (e ((h : MulAut W) w)) =
      ((ρ h : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w) := by
    intro h w
    simpa [ρ] using he (π.symm h) w
  refine (KTabC.fixingSubgroupOf_fixedPointSubgroup_eq_vecStab he' S hSfix).trans ?_
  ext g
  rw [Subgroup.mem_map_equiv, KTabC.mem_vecStab, KTabC.mem_vecStab]
  rfl

private theorem eq_one_of_mem_of_odd_card {G Γ : Type} [Group G] [Group Γ]
    {B : Subgroup G} {X : Subgroup Γ} (φ : Γ ≃* G) (hBodd : Odd (Nat.card ↥B))
    {x : G} (hxB : x ∈ B) (hx : φ.symm x ∈ X)
    (htriv : ∀ t ∈ X, Odd (orderOf t) → t = 1) : x = 1 := by
  have hoddx : Odd (orderOf x) :=
    Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hxB)
  have hodd0 : Odd (orderOf (φ.symm x)) := by
    rw [← MulEquiv.orderOf_eq φ (φ.symm x), MulEquiv.apply_symm_apply]
    exact hoddx
  simpa using congrArg (fun y => φ y) (htriv (φ.symm x) hx hodd0)

theorem exists_mulEquiv_pointStab_fixSub_eq_map_sylow {W : Type} [CommGroup W] [Finite W]
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K} (he0 : e₀ ≠ 0)
    (hline : KTabC.SylowFixedLine Γ e₀) (U : Sylow 2 ↥Γ)
    (hU : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀) (S : Sylow 2 ↥H) :
    ∃ φ : ↥Γ ≃* ↥H, (U : Subgroup ↥Γ).map φ.toMonoidHom = S ∧
      KTabD.pointStab H S = (KTabD.lineStab Γ e₀).map φ.toMonoidHom ∧
      KSUE.fixSub H S = (KTabC.vecStab Γ.subtype e₀).map φ.toMonoidHom := by
  obtain ⟨π, e, he, hUS, hSfix⟩ :=
    exists_coord_fixed_of_sylow_le_lineStab hreal he0 hline U hU S
  exact ⟨π, hUS, KTabD.pointStab_eq_map_lineStab π e he S hSfix,
    fixSub_eq_map_vecStab π e he S hSfix⟩

theorem kTab23cNineAt_of_model {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    {Γ : Type} [Group Γ] [Finite Γ] (U Qα Q₀ C₀ : Subgroup Γ)
    (hmodel : ∀ S : Sylow 2 ↥H, ∃ φ : Γ ≃* ↥H, U.map φ.toMonoidHom = (S : Subgroup ↥H) ∧
      KTabD.pointStab H S = Q₀.map φ.toMonoidHom ∧ KSUE.fixSub H S = C₀.map φ.toMonoidHom)
    (hpar : IsParabolicTwo Γ Qα) (hUQ : U ≤ Qα) (hnot : ¬ Qα ≤ Q₀)
    (hleast : ∀ P : Subgroup Γ, IsParabolicTwo Γ P → U ≤ P → ¬ P ≤ Q₀ → Qα ≤ P)
    (htriv : ∀ t ∈ Hinf Qα ⊓ C₀, Odd (orderOf t) → t = 1) :
    KTab23cNineAt W H := by
  unfold KTab23cNineAt
  intro S
  obtain ⟨φ, hφU, hφP, hφF⟩ := hmodel S
  intro ℓ Pℓ Tstar hTH hT hST Good Pstar hmin B hB hBodd
  have hPℓ_eq : Pℓ = Q₀.map φ.toMonoidHom := by
    rw [show Pℓ = KTabD.pointStab H S from rfl, hφP]
  have hPℓ_fix : ∀ t ∈ Tstar,
      (Pℓ.map H.subtype).map (MulAut.conj t).toMonoidHom = Pℓ.map H.subtype :=
    map_conj_stabilizer_fixedPoint_eq H S Tstar hTH hT hST
  obtain ⟨hpar', hSP', hnot', hleast'⟩ := leastParabolic_map φ hφU hpar hUQ hnot hleast
  have hnotPα : ¬ Qα.map φ.toMonoidHom ≤ Pℓ := by rwa [hPℓ_eq]
  have hle : ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P → (S : Subgroup ↥H) ≤ P →
      ¬ P ≤ Pℓ → Qα.map φ.toMonoidHom ≤ P := by
    intro P hparP hSP hnotP
    exact hleast' P hparP hSP (by rwa [hPℓ_eq] at hnotP)
  have hPeq : Pstar = Qα.map φ.toMonoidHom :=
    minimal_good_eq_of_least_parabolic H S Pℓ Tstar hTH hT hST hPℓ_fix hpar' hSP'
      hnotPα hle hmin
  refine (Subgroup.eq_bot_iff_forall
    (B ⊓ fixingSubgroupOf ↥H W (ℓ : Set W))).mpr ?_
  intro x hx
  obtain ⟨hxB, hxF⟩ := Subgroup.mem_inf.mp hx
  have hxFix : x ∈ KSUE.fixSub H S := hxF
  have hxFix' : x ∈ C₀.map φ.toMonoidHom := by
    rwa [hφF] at hxFix
  have hxH : x ∈ Hinf (Qα.map φ.toMonoidHom) := hPeq ▸ hB hxB
  have hx0 : φ.symm x ∈ Hinf Qα ⊓ C₀ :=
    symm_mem_Hinf_inf_of_mem_map (A := Qα) (B := C₀) φ ⟨hxH, hxFix'⟩
  exact eq_one_of_mem_of_odd_card φ hBodd hxB hx0 htriv

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine
