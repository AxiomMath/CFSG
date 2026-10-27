module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionDefining
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteen
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Layer

variable {X : Type} [Group X]

theorem ggExists_derivedSeries_le_of_isSolvable (N : Subgroup X) [N.Normal]
    (hsolv : Group.IsSolvable (X ⧸ N)) : ∃ k : ℕ, derivedSeries X k ≤ N := by
  obtain ⟨k, hk⟩ := (Group.isSolvable_def (X ⧸ N)).mp hsolv
  refine ⟨k, ?_⟩
  have h := map_derivedSeries_eq (QuotientGroup.mk'_surjective N) k
  rw [hk, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  exact h

theorem ggLe_derivedSeries_of_perfect {Y : Type} [Group Y] {C : Subgroup Y} (hC : ⁅C, C⁆ = C)
    (k : ℕ) : C ≤ derivedSeries Y k := by
  induction k with
  | zero => exact le_top
  | succ k ih =>
    rw [derivedSeries_succ, ← hC]
    exact Subgroup.commutator_mono ih ih

theorem ggLayer_quot_pCore_two_eq_bot [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup X)
    [N.Normal] (hsolv : Group.IsSolvable (X ⧸ N)) (hchar : IsCharacteristicP p ↥N) :
    LargeEvenLayer (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) = ⊥ := by
  classical
  have hpf : Fact p.Prime := ⟨hp⟩
  have h2f : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  set Q : Subgroup X := CFSG.pCore 2 X with hQdef
  set π : X →* X ⧸ Q := QuotientGroup.mk' Q with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  refine sSup_eq_bot.mpr fun C hC => ?_
  exfalso
  set P : Subgroup X := (CFSG.pCore p ↥N).map N.subtype with hPdef
  have hPp : IsPGroup p P := (CFSG.pCore_isPGroup (p := p) (G := ↥N)).map N.subtype
  have hPn : P.Normal := ConjAct.normal_of_characteristic_of_normal
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hPQ : Disjoint P Q := IsPGroup.disjoint_of_ne p 2 hp2 P Q hPp hQp
  obtain ⟨k, hk⟩ := ggExists_derivedSeries_le_of_isSolvable N hsolv
  have hCN : C ≤ N.map π := by
    have h1 := ggLe_derivedSeries_of_perfect (ggComponent_perfect hC) k
    rw [← map_derivedSeries_eq hπs k] at h1
    exact h1.trans (Subgroup.map_mono hk)
  have hPbar : Group.IsSolvable ↥(P.map π) := by
    have : Group.IsNilpotent ↥(P.map π) := (hPp.map π).isNilpotent
    infer_instance
  have hCP : ¬ C ≤ P.map π := ggComponent_not_le_of_isSolvable hC hPbar
  have hPbarn : (P.map π).Normal := hPn.map π hπs
  have hsub : ((P.map π).subgroupOf ⊤).IsSubnormal := (hPbarn.subgroupOf ⊤).isSubnormal
  have hcomm := (ggComponent_le_or_commute hC hsub).resolve_left hCP
  apply hCP
  intro c hc
  obtain ⟨n, hnN, rfl⟩ := hCN hc
  have hnP : ∀ y ∈ P, y * n = n * y := by
    intro y hy
    have h1 := hcomm (π n) hc (π y) ⟨Subgroup.mem_top _, Subgroup.mem_map_of_mem π hy⟩
    have hq : n * y * n⁻¹ * y⁻¹ ∈ Q := by
      rw [← QuotientGroup.ker_mk' Q, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      change π n * π y * (π n)⁻¹ * (π y)⁻¹ = 1
      rw [h1]
      group
    have hpm : n * y * n⁻¹ * y⁻¹ ∈ P :=
      P.mul_mem (hPn.conj_mem y hy n) (P.inv_mem hy)
    have h1' : n * y * n⁻¹ * y⁻¹ = 1 :=
      (Subgroup.disjoint_def.mp hPQ) hpm hq
    calc y * n = (n * y * n⁻¹ * y⁻¹)⁻¹ * (n * y) := by group
      _ = n * y := by rw [h1', inv_one, one_mul]
  have hmem : (⟨n, hnN⟩ : ↥N) ∈ CFSG.pCore p ↥N := by
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (hnP y ⟨y, hy, rfl⟩)
  exact Subgroup.mem_map_of_mem π ⟨⟨n, hnN⟩, hmem, rfl⟩

end Layer

section Hyp

variable {W : Type} [Group W]

theorem ggMem_ker_mk_comp_subtype {H K : Subgroup W} [K.Normal] (x : ↥H) :
    x ∈ ((QuotientGroup.mk' K).comp H.subtype).ker ↔ (x : W) ∈ K := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  rfl

theorem ggIsSolvable_quot_inf_generalizedFitting [Finite W]
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) {p : ℕ}
    {H E : Subgroup W} (hyp : GGHypThreeSixteen p H E) :
    have : (CFSG.generalizedFitting W).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
    Group.IsSolvable (↥H ⧸ ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker) := by
  intro hKn
  obtain ⟨-, ⟨hsimple, hnab, hcat⟩, -⟩ := hyp
  have : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hsimple
  have hout := hSch _ hnab hcat
  have hWK := ggIsSolvable_quot_generalizedFitting hsimple hnab hout
  exact Group.isSolvable_of_isSolvable_injective
    (QuotientGroup.kerLift_injective ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype))

end Hyp

end CFSG.StandardType
