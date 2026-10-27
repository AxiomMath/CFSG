module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.StandardType.FrameRoute

theorem p13a7_two_subgroup_trivial {K : Type*} [Group K] {C E U : Subgroup K} {r : ℕ}
    (hEC : E ≤ C) (hE : Nat.card E = 3 ^ r) (hnorm : (E.subgroupOf C).Normal)
    (hcent : C ⊓ Subgroup.centralizer (E : Set K) = E)
    (hUC : U ≤ C) (hU : IsPGroup 2 U) (hEU : E ≤ Subgroup.normalizer (U : Set K)) :
    U = ⊥ := by
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hE
  have hEU' : E ⊓ U = ⊥ := by
    have h3 : IsPGroup 3 (E ⊓ U : Subgroup K) := IsPGroup.to_inf_left hE3
    have h2 : IsPGroup 2 (E ⊓ U : Subgroup K) := IsPGroup.to_inf_right hU
    exact disjoint_self.mp (IsPGroup.disjoint_of_coprime h3 h2 (by norm_num))
  refine le_bot_iff.mp ?_
  intro u hu
  have huC : u ∈ C := hUC hu
  have huCent : u ∈ Subgroup.centralizer (E : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hconjU : e * u * e⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hEU he) u).mp hu
    have heC : (⟨e, hEC he⟩ : C) ∈ E.subgroupOf C := Subgroup.mem_subgroupOf.mpr he
    have hconjE : u * e * u⁻¹ ∈ E := by
      have hmem := hnorm.conj_mem ⟨e, hEC he⟩ heC ⟨u, huC⟩
      exact Subgroup.mem_subgroupOf.mp hmem
    have hcomm : e * u * e⁻¹ * u⁻¹ ∈ E := by
      have hinv : (u * e * u⁻¹)⁻¹ ∈ E := E.inv_mem hconjE
      have heq : (u * e * u⁻¹)⁻¹ = u * e⁻¹ * u⁻¹ := by group
      rw [heq] at hinv
      simpa only [mul_assoc] using E.mul_mem he hinv
    have hcommU : e * u * e⁻¹ * u⁻¹ ∈ U := U.mul_mem hconjU (U.inv_mem hu)
    have hone : e * u * e⁻¹ * u⁻¹ = 1 := by
      have hbot : e * u * e⁻¹ * u⁻¹ ∈ (⊥ : Subgroup K) := by
        rw [← hEU']
        exact Subgroup.mem_inf.mpr ⟨hcomm, hcommU⟩
      simpa using hbot
    have hconj : e * u * e⁻¹ = u := mul_inv_eq_one.mp hone
    calc e * u = e * u * e⁻¹ * e := by group
      _ = u * e := by rw [hconj]
  have huE : u ∈ E := by
    have hmem : u ∈ C ⊓ Subgroup.centralizer (E : Set K) := Subgroup.mem_inf.mpr ⟨huC, huCent⟩
    rwa [hcent] at hmem
  have hbot : u ∈ (⊥ : Subgroup K) := by
    rw [← hEU']
    exact Subgroup.mem_inf.mpr ⟨huE, hu⟩
  exact hbot

@[expose] def P13aConclusion (K : Type) [Group K] (E : Subgroup K) (r : ℕ) : Prop :=
  Nat.card E = 3 ^ r ∧ Subgroup.centralizer (E : Set K) = E ∧
    ∀ F : Subgroup K, F ≤ E → F.relIndex E = 3 →
      Nat.card F = 3 ^ (r - 1) ∧
      (Subgroup.centralizer (F : Set K) = E ∨
        ∃ R : Subgroup K, Nonempty (R ≃* Equiv.Perm (Fin 3)) ∧
          F ≤ Subgroup.centralizer (R : Set K) ∧ F ⊓ R = ⊥ ∧
          Subgroup.centralizer (F : Set K) = F ⊔ R ∧ E = F ⊔ E ⊓ R ∧ Nat.card ↥(E ⊓ R) = 3) ∧
      (E.subgroupOf (Subgroup.centralizer (F : Set K))).Normal ∧
      Subgroup.centralizer (F : Set K) ⊓ Subgroup.centralizer (E : Set K) = E

theorem p13a7_of_conclusion {K : Type} [Group K] {E : Subgroup K} {r : ℕ}
    (h : P13aConclusion K E r) {F : Subgroup K} (hFE : F ≤ E) (hidx : F.relIndex E = 3)
    {U : Subgroup K} (hUC : U ≤ Subgroup.centralizer (F : Set K)) (hU : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  obtain ⟨hE, hCE, hF⟩ := h
  obtain ⟨-, -, hnorm, hcent⟩ := hF F hFE hidx
  have hEC : E ≤ Subgroup.centralizer (F : Set K) := by
    intro x hx
    have hx' : x ∈ Subgroup.centralizer (E : Set K) := by
      rw [hCE]
      exact hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hx' y (hFE hy)
  exact p13a7_two_subgroup_trivial hEC hE hnorm hcent hUC hU hEU

@[expose] def P13aCase (K : Type) [Group K] (E F : Subgroup K) : Prop :=
  Subgroup.centralizer (F : Set K) = E ∨
    ∃ R : Subgroup K, Nonempty (R ≃* Equiv.Perm (Fin 3)) ∧
      F ≤ Subgroup.centralizer (R : Set K) ∧ F ⊓ R = ⊥ ∧
      Subgroup.centralizer (F : Set K) = F ⊔ R ∧ E = F ⊔ E ⊓ R ∧ Nat.card ↥(E ⊓ R) = 3

theorem p13aConclusion_of_cases {K : Type} [Group K] {E : Subgroup K} {r : ℕ}
    (hE : Nat.card E = 3 ^ r) (hCE : Subgroup.centralizer (E : Set K) = E)
    (hF : ∀ F : Subgroup K, F ≤ E → F.relIndex E = 3 → P13aCase K E F) :
    P13aConclusion K E r := by
  refine ⟨hE, hCE, fun F hFE hidx => ?_⟩
  have hEC : E ≤ Subgroup.centralizer (F : Set K) := by
    intro x hx
    have hx' : x ∈ Subgroup.centralizer (E : Set K) := by
      rw [hCE]
      exact hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hx' y (hFE hy)
  have hcardF : Nat.card F = 3 ^ (r - 1) := by
    have h1 := Subgroup.relIndex_mul_card F E
    rw [hidx, inf_of_le_left hFE, hE] at h1
    rcases r with _ | r
    · omega
    · rw [Nat.add_sub_cancel]
      rw [pow_succ'] at h1
      omega
  have hcases := hF F hFE hidx
  refine ⟨hcardF, hcases, ?_, by rw [hCE]; exact inf_eq_right.mpr hEC⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEC]
  rw [P13aCase] at hcases
  rcases hcases with hC | ⟨R, ⟨eR⟩, hFR, -, hC, hER, hcardER⟩
  · rw [hC]
    exact Subgroup.le_normalizer
  have hnR : ((E ⊓ R).subgroupOf R).Normal := by
    refine Subgroup.normal_of_index_eq_two ?_
    have h1 := Subgroup.relIndex_mul_card (E ⊓ R) R
    rw [inf_of_le_left inf_le_right, hcardER, Nat.card_congr eR.toEquiv, Nat.card_perm,
      Nat.card_fin] at h1
    have h2 : (E ⊓ R).relIndex R = 2 := by
      norm_num [Nat.factorial] at h1
      omega
    exact h2
  have hconj : ∀ x ∈ R, ∀ y ∈ E, x * y * x⁻¹ ∈ E := by
    intro x hx y hy
    have hle : F ⊔ E ⊓ R ≤ E.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun f hf => ?_) (fun z hz => ?_)
      · have hcomm := Subgroup.mem_centralizer_iff.mp (hFR hf) x hx
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcomm,
          mul_inv_cancel_right]
        exact hFE hf
      · have hz' : (⟨z, hz.2⟩ : R) ∈ (E ⊓ R).subgroupOf R := Subgroup.mem_subgroupOf.mpr hz
        have hmem := hnR.conj_mem _ hz' ⟨x, hx⟩
        rw [Subgroup.mem_subgroupOf] at hmem
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact (Subgroup.mem_inf.mp hmem).1
    rw [hER] at hy
    exact hle hy
  rw [hC]
  refine sup_le (hFE.trans Subgroup.le_normalizer) fun x hx => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj x hx y, fun h => ?_⟩
  have h2 := hconj x⁻¹ (R.inv_mem hx) _ h
  rwa [inv_inv, show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h2

private theorem p13cAux_centralizer_map {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (S : Subgroup K) :
    Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup K') : Set K') =
      (Subgroup.centralizer (S : Set K)).map e.toMonoidHom := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hy s hs
    apply e.injective
    rw [map_mul, map_mul]
    exact hy (e s) ⟨s, hs, rfl⟩
  · rintro hy _ ⟨s, hs, rfl⟩
    change e s * e y = e y * e s
    rw [← map_mul, ← map_mul, hy s hs]

theorem p13aCase_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {E F : Subgroup K} (h : P13aCase K' (E.map e.toMonoidHom) (F.map e.toMonoidHom)) :
    P13aCase K E F := by
  have hinj : Function.Injective (Subgroup.map e.toMonoidHom) :=
    Subgroup.map_injective e.injective
  have hcard : ∀ S : Subgroup K, Nat.card (S.map e.toMonoidHom) = Nat.card S := fun S =>
    Subgroup.card_map_of_injective e.injective
  have hinf : ∀ S T : Subgroup K,
      (S ⊓ T).map e.toMonoidHom = S.map e.toMonoidHom ⊓ T.map e.toMonoidHom := fun S T =>
    Subgroup.map_inf_eq S T e.toMonoidHom e.injective
  rw [P13aCase, p13cAux_centralizer_map] at h
  rcases h with hCF | ⟨R', ⟨eR'⟩, hFR', hFR'0, hCF, hER', hcardER'⟩
  · exact Or.inl (hinj hCF)
  set R := R'.comap e.toMonoidHom with hRdef
  have hR : R.map e.toMonoidHom = R' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective R'
  rw [← hR] at hFR' hFR'0 hCF hER' hcardER'
  rw [p13cAux_centralizer_map, Subgroup.map_le_map_iff_of_injective e.injective] at hFR'
  rw [← hinf, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hFR'0
  rw [← Subgroup.map_sup] at hCF
  rw [← hinf, ← Subgroup.map_sup] at hER'
  rw [← hinf, hcard] at hcardER'
  exact Or.inr ⟨R, ⟨((e.subgroupMap R).trans (MulEquiv.subgroupCongr hR)).trans eR'⟩, hFR',
    hFR'0, hinj hCF, hinj hER', hcardER'⟩

theorem p13aConclusion_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {E : Subgroup K} {r : ℕ} (h : P13aConclusion K' (E.map e.toMonoidHom) r) :
    P13aConclusion K E r := by
  obtain ⟨hE, hCE, hF⟩ := h
  rw [Subgroup.card_map_of_injective e.injective] at hE
  rw [p13cAux_centralizer_map] at hCE
  refine p13aConclusion_of_cases hE (Subgroup.map_injective e.injective hCE)
    fun F hFE hidx => p13aCase_of_mulEquiv e ?_
  exact (hF (F.map e.toMonoidHom) (Subgroup.map_mono hFE)
    (by rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]; exact hidx)).2.1

end CFSG.StandardType.FrameRoute
