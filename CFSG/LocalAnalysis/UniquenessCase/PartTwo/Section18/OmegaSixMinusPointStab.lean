module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedInf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem map_conj_pointStabilizer (g : Gom Q) (u : V) :
    (pointStabilizer Q u).map (MulAut.conj g).toMonoidHom = pointStabilizer Q (g.app u) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    change (g * x * g⁻¹).app (g.app u) = c • (g.app u)
    simp only [Gom.app_mul, Gom.app_inv_app, hc, Gom.map_smul]
  · intro hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨g⁻¹ * y * g, ⟨c, ?_⟩, ?_⟩
    · change (g⁻¹ * y * g).app u = c • u
      simp only [Gom.app_mul, hc, Gom.map_smul, Gom.app_inv_app]
    · change (MulAut.conj g) (g⁻¹ * y * g) = y
      rw [MulAut.conj_apply]
      group

private theorem polar_eq_zero_of_forall_app_eq_smul_T2J3 {u v : V} (hu : u ≠ 0)
    (hQu : Q u = 0) (hb : polar Q v u = 0) (hvmem : v ∉ Submodule.span K ({u} : Set V))
    (hv : ∀ g ∈ Lom Q u, ∃ c : K, g.app v = c • v) :
    ∀ w, polar Q u w = 0 → polar Q v w = 0 := by
  intro w hw
  obtain ⟨c, hc⟩ := hv (Eom Q u w) (Eom_mem_Lom hw)
  have hmain : v - polar Q v w • u = c • v := by
    have h := Eom_app hQu hw v
    rw [hb] at h
    simpa using h.symm.trans hc
  have hrel : (1 - c) • v = polar Q v w • u := by
    rw [sub_smul, one_smul, ← hmain]
    abel
  by_cases h1c : 1 - c = 0
  · rw [h1c, zero_smul] at hrel
    exact (smul_eq_zero.mp hrel.symm).resolve_right hu
  · exfalso
    apply hvmem
    refine Submodule.mem_span_singleton.mpr ⟨(1 - c)⁻¹ * polar Q v w, ?_⟩
    calc ((1 - c)⁻¹ * polar Q v w) • u = (1 - c)⁻¹ • (polar Q v w • u) := by rw [smul_smul]
      _ = (1 - c)⁻¹ • ((1 - c) • v) := by rw [hrel]
      _ = v := by rw [smul_smul, inv_mul_cancel₀ h1c, one_smul]

theorem eq_smul_of_forall_app_eq_smul_Lom (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0) (hQu : Q u = 0) {v : V}
    (hv : ∀ g ∈ Lom Q u, ∃ c : K, g.app v = c • v) : ∃ c : K, v = c • u := by
  haveI : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  by_contra hnot
  push Not at hnot
  have hvN : v ∉ Submodule.span K ({u} : Set V) := by
    intro hvmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvmem
    exact hnot c hc.symm
  set N : Submodule K V := Submodule.span K ({u, v} : Set V) with hNdef
  have huN : u ∈ N := Submodule.subset_span (by simp)
  have hvN' : v ∈ N := Submodule.subset_span (by simp)
  by_cases hb : polar Q v u = 0
  · have hzero := polar_eq_zero_of_forall_app_eq_smul_T2J3 hu hQu hb hvN hv
    obtain ⟨z, hz, hzv⟩ := exists_polar_ne_zero_of_not_mem hQ hvN
    exact hzv (hzero z (mem_orth_span_single_iff.mp hz))
  · have key : ∀ w, polar Q u w = 0 → w ∈ N := by
      intro w hw
      obtain ⟨c, hc⟩ := hv (Eom Q u w) (Eom_mem_Lom hw)
      have hmain : v + polar Q v u • w - (polar Q v w + Q w * polar Q v u) • u = c • v :=
        (Eom_app hQu hw v).symm.trans hc
      have hbw : polar Q v u • w ∈ N := by
        have h1 : polar Q v u • w =
            c • v + (polar Q v w + Q w * polar Q v u) • u - v := by
          rw [← hmain]
          abel
        rw [h1]
        exact Submodule.sub_mem _
          (Submodule.add_mem _ (Submodule.smul_mem _ _ hvN') (Submodule.smul_mem _ _ huN))
          hvN'
      have hwN := N.smul_mem (polar Q v u)⁻¹ hbw
      rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at hwN
    have horth : LinearMap.BilinForm.orthogonal (polarBilin Q)
        (Submodule.span K ({u} : Set V)) ≤ N :=
      fun z hz => key z (mem_orth_span_single_iff.mp hz)
    have hdim : Module.finrank K (LinearMap.BilinForm.orthogonal (polarBilin Q)
        (Submodule.span K ({u} : Set V))) = Module.finrank K V - 1 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hu]
    have hmono := Submodule.finrank_mono horth
    have hNle : Module.finrank K N ≤ 2 := by
      rw [hNdef]
      exact finrank_span_pair_le u v
    omega

private theorem normalizer_le_pointStabilizer_T2J3 (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0) (hQu : Q u = 0)
    {T : Subgroup (Gom Q)} (hT : T ≤ pointStabilizer Q u) (hUT : Lom Q u ≤ T) :
    Subgroup.normalizer (T : Set (Gom Q)) ≤ pointStabilizer Q u := by
  intro g hg
  rw [mem_pointStabilizer]
  refine eq_smul_of_forall_app_eq_smul_Lom hQ h4 hu hQu ?_
  intro h hh
  have hhT : h ∈ T := hUT hh
  have hconj : g⁻¹ * h * g ∈ T := (Subgroup.mem_normalizer_iff''.mp hg h).mp hhT
  obtain ⟨c, hc⟩ := mem_pointStabilizer.mp (hT hconj)
  refine ⟨c, ?_⟩
  calc h.app (g.app u) = (h * g).app u := (Gom.app_mul h g u).symm
    _ = (g * (g⁻¹ * h * g)).app u := by rw [show h * g = g * (g⁻¹ * h * g) by group]
    _ = g.app ((g⁻¹ * h * g).app u) := Gom.app_mul g _ u
    _ = g.app (c • u) := by rw [hc]
    _ = c • g.app u := Gom.map_smul g c u

private theorem mem_normalizer_of_mem_normalizer_subgroupOf_T2J3 {T : Subgroup (Gom Q)}
    {S' : Sylow 2 (Gom Q)} (hTS' : T ≤ (S' : Subgroup (Gom Q))) {x : ↥S'}
    (hx : x ∈ Subgroup.normalizer
      ((T.subgroupOf (S' : Subgroup (Gom Q))) : Set ↥S')) :
    (x : Gom Q) ∈ Subgroup.normalizer (T : Set (Gom Q)) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro t
  constructor
  · intro ht
    have htS' : t ∈ (S' : Subgroup (Gom Q)) := hTS' ht
    have hmem := (Subgroup.mem_normalizer_iff''.mp hx (⟨t, htS'⟩ : ↥S')).mp
      (Subgroup.mem_subgroupOf.mpr ht)
    simpa using Subgroup.mem_subgroupOf.mp hmem
  · intro hconj
    have htS' : t ∈ (S' : Subgroup (Gom Q)) := by
      have h1 : (x : Gom Q)⁻¹ * t * (x : Gom Q) ∈ (S' : Subgroup (Gom Q)) := hTS' hconj
      have h2 : (x : Gom Q) * ((x : Gom Q)⁻¹ * t * (x : Gom Q)) * (x : Gom Q)⁻¹ ∈
          (S' : Subgroup (Gom Q)) :=
        (S' : Subgroup (Gom Q)).mul_mem
          ((S' : Subgroup (Gom Q)).mul_mem x.2 h1) (inv_mem x.2)
      have h3 : (x : Gom Q) * ((x : Gom Q)⁻¹ * t * (x : Gom Q)) * (x : Gom Q)⁻¹ = t := by
        group
      rwa [h3] at h2
    have hmem : x⁻¹ * (⟨t, htS'⟩ : ↥S') * x ∈ T.subgroupOf (S' : Subgroup (Gom Q)) :=
      Subgroup.mem_subgroupOf.mpr (by simpa using hconj)
    simpa using Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff''.mp hx (⟨t, htS'⟩ : ↥S')).mpr hmem)

private theorem sylow_inf_eq_of_le_T2J3 {P T : Subgroup (Gom Q)} (T₀ : Sylow 2 ↥P)
    (hT : T = (T₀ : Subgroup ↥P).map P.subtype) (S' : Sylow 2 (Gom Q)) (hTS' : T ≤ S') :
    (S' : Subgroup (Gom Q)) ⊓ P = T := by
  have hT₀le : (T₀ : Subgroup ↥P) ≤ (((S' : Subgroup (Gom Q)) ⊓ P).subgroupOf P) := by
    intro t ht
    rw [Subgroup.mem_subgroupOf]
    have htT : (t : Gom Q) ∈ T := by
      rw [hT]
      exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    exact ⟨hTS' htT, t.2⟩
  have hPinf : IsPGroup 2 (((S' : Subgroup (Gom Q)) ⊓ P).subgroupOf P) :=
    (S'.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hmax := T₀.is_maximal' hPinf hT₀le
  have h := congrArg (Subgroup.map P.subtype) hmax
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
  exact h.trans hT.symm

private theorem coe_eq_of_inf_eq_of_normalizer_le_T2J3 [Finite (Gom Q)] [Fact (Nat.Prime 2)]
    {P T : Subgroup (Gom Q)} {S' : Sylow 2 (Gom Q)}
    (hS'inf : (S' : Subgroup (Gom Q)) ⊓ P = T)
    (hnorm : Subgroup.normalizer (T : Set (Gom Q)) ≤ P) (hTS' : T ≤ S') :
    T = (S' : Subgroup (Gom Q)) := by
  by_contra hne
  let H : Subgroup ↥S' := T.subgroupOf (S' : Subgroup (Gom Q))
  have hlt : H < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    exact hne (le_antisymm hTS' (Subgroup.subgroupOf_eq_top.mp htop))
  haveI : Finite ↥S' := Subtype.finite
  haveI : Group.IsNilpotent ↥S' := IsPGroup.isNilpotent S'.isPGroup'
  have hNC : NormalizerCondition ↥S' := Group.normalizerCondition_of_isNilpotent
  have hlt' : H < Subgroup.normalizer (H : Set ↥S') := hNC H hlt
  have hle : H ≤ Subgroup.normalizer (H : Set ↥S') := le_of_lt hlt'
  have hne' : H ≠ Subgroup.normalizer (H : Set ↥S') := ne_of_lt hlt'
  obtain ⟨x, hxnorm, hxnotin⟩ : ∃ x ∈ Subgroup.normalizer (H : Set ↥S'), x ∉ H := by
    by_contra hcon
    refine hne' (le_antisymm hle ?_)
    intro x hx
    by_contra hxH
    exact hcon ⟨x, hx, hxH⟩
  have hxP : (x : Gom Q) ∈ P :=
    hnorm (mem_normalizer_of_mem_normalizer_subgroupOf_T2J3 hTS' hxnorm)
  have hxT : (x : Gom Q) ∈ T := by
    rw [← hS'inf]
    exact ⟨x.2, hxP⟩
  exact hxnotin (Subgroup.mem_subgroupOf.mpr hxT)

private theorem sylow_coe_eq_of_le_T2J3 [Finite (Gom Q)] [Fact (Nat.Prime 2)]
    {P T : Subgroup (Gom Q)} (T₀ : Sylow 2 ↥P)
    (hT : T = (T₀ : Subgroup ↥P).map P.subtype)
    (hnorm : Subgroup.normalizer (T : Set (Gom Q)) ≤ P)
    (S' : Sylow 2 (Gom Q)) (hTS' : T ≤ S') :
    T = (S' : Subgroup (Gom Q)) :=
  coe_eq_of_inf_eq_of_normalizer_le_T2J3 (sylow_inf_eq_of_le_T2J3 T₀ hT S' hTS') hnorm hTS'

end Generic

section Parabolic

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V] [Finite V]
  {Q : QuadraticForm K V}

theorem isParabolicTwo_pointStabilizer (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0) (hQu : Q u = 0) :
    IsParabolicTwo (Gom Q) (pointStabilizer Q u) := by
  haveI : FiniteDimensional K V := Module.Finite.of_finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ h => LinearEquiv.ext fun v => congrFun h v
  haveI : Finite (Gom Q) := Subtype.finite
  let P : Subgroup (Gom Q) := pointStabilizer Q u
  let T₀ : Sylow 2 ↥P := default
  let T : Subgroup (Gom Q) := (T₀ : Subgroup ↥P).map P.subtype
  have hTP : T ≤ P := Subgroup.map_subtype_le _
  have hUT : Lom Q u ≤ T := by
    rw [Lom_eq_pCoreOf_pointStabilizer_of_four_le hQ h4 hu hQu]
    show pCoreOf 2 P ≤ T
    exact Subgroup.map_mono (IsPGroup.le_sylow_of_normal
      (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥P)) T₀)
  have hnormT : Subgroup.normalizer (T : Set (Gom Q)) ≤ P :=
    normalizer_le_pointStabilizer_T2J3 hQ h4 hu hQu hTP hUT
  obtain ⟨S', hTS'⟩ := IsPGroup.exists_le_sylow (T₀.isPGroup'.map P.subtype)
  have hEq : T = (S' : Subgroup (Gom Q)) := sylow_coe_eq_of_le_T2J3 T₀ rfl hnormT S' hTS'
  refine ⟨S', ?_⟩
  have hcoe : (S' : Set (Gom Q)) = (T : Set (Gom Q)) :=
    congrArg (fun H : Subgroup (Gom Q) => (H : Set (Gom Q))) hEq.symm
  rw [hcoe]
  exact hnormT

end Parabolic

section PCoreBot

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V] [Finite V]
  {Q : QuadraticForm K V}

theorem pCoreOf_pointStabilizer_ne_bot (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0) (hQu : Q u = 0) :
    pCoreOf 2 (pointStabilizer Q u) ≠ ⊥ := by
  haveI : FiniteDimensional K V := Module.Finite.of_finite
  rw [← Lom_eq_pCoreOf_pointStabilizer_of_four_le hQ h4 hu hQu]
  exact Lom_ne_bot hQ (by omega) hQu hu

end PCoreBot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
