module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs
public import CFSG.GroupTheory.CyclicModAbelianCommutators
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private noncomputable def ggEbar {K : Type*} {R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) : Subgroup (MulAut R) := E.map (ggInducedAut θ)

private noncomputable def ggC {K : Type*} {R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) : Subgroup (MulAut R) :=
  Subgroup.centralizer (ggEbar θ E : Set (MulAut R))

private noncomputable def ggS0 {K : Type*} {R : Type} [Group K] [Group R] (S : Subgroup (MulAut R))
    (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K)) : Subgroup (MulAut R) :=
  S ⊓ ggC θ E

private noncomputable def ggN0 {K : Type*} {R : Type} [Group K] [Group R] (J : Subgroup (MulAut R))
    (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K)) : Subgroup (MulAut R) :=
  J ⊓ ggC θ E

private noncomputable def ggV {K : Type*} {R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R)
    (P : Subgroup (MulAut K)) : Subgroup (MulAut R) := P.map (ggInducedAut θ)

private theorem ggN0_le_ggS0 {K : Type*} {R : Type} [Group K] [Group R] {J S : Subgroup (MulAut R)}
    (hJS : J ≤ S) (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K)) :
    ggN0 J θ E ≤ ggS0 S θ E := fun _ hx => ⟨hJS hx.1, hx.2⟩

private theorem ggN0_normal {K : Type*} {R : Type} [Group K] [Group R] {J S : Subgroup (MulAut R)}
    (hJS : J ≤ S) (hJnorm : (J.subgroupOf S).Normal)
    (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K)) :
    ∀ s ∈ ggS0 S θ E, ∀ u ∈ ggN0 J θ E, s * u * s⁻¹ ∈ ggN0 J θ E := by
  intro s hs u hu
  rw [ggS0] at hs
  rw [ggN0] at hu
  refine ⟨?_, ?_⟩
  · have hconj := hJnorm.conj_mem (⟨u, hJS hu.1⟩ : ↥S)
      (Subgroup.mem_subgroupOf.mpr hu.1) (⟨s, hs.1⟩ : ↥S)
    exact Subgroup.mem_subgroupOf.mp hconj
  · exact (ggC θ E).mul_mem ((ggC θ E).mul_mem hs.2 hu.2) ((ggC θ E).inv_mem hs.2)

private theorem ggN0_commutative {K : Type*} {R : Type} [Group K] [Group R]
    {J : Subgroup (MulAut R)} {I : Set (MulAut R)}
    (hJI : (J : Set (MulAut R)) = I) (θ : K ⧸ Subgroup.center K ≃* R)
    {E : Subgroup (MulAut K)}
    (hcomm : ∀ x ∈ I, ∀ y ∈ I,
      (∀ e ∈ E, x * ggInducedAut (R := R) θ e = ggInducedAut (R := R) θ e * x) →
      (∀ e ∈ E, y * ggInducedAut (R := R) θ e = ggInducedAut (R := R) θ e * y) → x * y = y * x) :
    ∀ x ∈ ggN0 J θ E, ∀ y ∈ ggN0 J θ E, x * y = y * x := by
  intro x hx y hy
  rw [ggN0] at hx hy
  have hxI : x ∈ I := by rw [← hJI]; exact hx.1
  have hyI : y ∈ I := by rw [← hJI]; exact hy.1
  exact hcomm x hxI y hyI
    (fun e he => (Subgroup.mem_centralizer_iff.mp hx.2 _ (Subgroup.mem_map_of_mem _ he)).symm)
    (fun e he => (Subgroup.mem_centralizer_iff.mp hy.2 _ (Subgroup.mem_map_of_mem _ he)).symm)

private theorem ggN0_mem {K : Type*} {R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K)) {J S : Subgroup (MulAut R)} :
    ∀ s ∈ ggS0 S θ E, s ∈ J → s ∈ ggN0 J θ E := by
  intro s hs hJ
  change s ∈ S ⊓ ggC θ E at hs
  change s ∈ J ⊓ ggC θ E
  exact ⟨hJ, hs.2⟩

private theorem ggEbar_le_ggN0 {K : Type*} {R : Type} [Group K] [Group R] {J : Subgroup (MulAut R)}
    {I : Set (MulAut R)} (hJI : (J : Set (MulAut R)) = I) (θ : K ⧸ Subgroup.center K ≃* R)
    {E : Subgroup (MulAut K)} (p : ℕ) (hEelem : IsElemAbelian p E)
    (hInd : ∀ e ∈ E, GGL45InducesIn (R := R) θ I e) :
    ggEbar θ E ≤ ggN0 J θ E := by
  intro u hu
  rw [ggEbar] at hu
  rw [ggN0]
  constructor
  · obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hu
    change ggInducedAut θ e ∈ (J : Set (MulAut R))
    rw [hJI]
    exact (ggL45_inducesIn_iff (R := R) θ I e).mp (hInd e he)
  · haveI : IsMulCommutative ↥(ggEbar θ E) :=
      (CFSG.Open.IsElemAbelian.map hEelem (ggInducedAut θ)).1
    intro v hv
    exact Subgroup.mul_comm_of_mem_isMulCommutative (ggEbar θ E) hv hu

private theorem ggEbar_central {K : Type*} {R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) {S : Subgroup (MulAut R)} :
    ∀ z ∈ ggEbar θ E, ∀ s ∈ ggS0 S θ E, z * s = s * z := by
  intro z hz s hs
  rw [ggS0] at hs
  exact Subgroup.mem_centralizer_iff.mp hs.2 z hz

private theorem ggV_exponent {K : Type*} {R : Type} [Group K] [Group R] {p : ℕ}
    (θ : K ⧸ Subgroup.center K ≃* R) {P E : Subgroup (MulAut K)}
    (hPE : P ≤ E) (hEelem : IsElemAbelian p E) :
    ∀ v ∈ ggV θ P, v ^ p = 1 := by
  intro v hv
  rw [ggV] at hv
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hv
  rw [← map_pow, hEelem.2 e (hPE he), map_one]

private theorem ggV_commutators {K : Type*} {R : Type} [Group K] [Group R] {p : ℕ}
    (θ : K ⧸ Subgroup.center K ≃* R) {S : Subgroup (MulAut R)}
    {ψ : MulAut K} {E P : Subgroup (MulAut K)}
    (hψp : ψ ^ p = 1) (hψE : ∀ e ∈ E, e * ψ = ψ * e)
    (hSp : ∀ α : MulAut R, (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hPforall : ∀ e ∈ P, ∃ γ : MulAut K, GGL45IsPElt p γ ∧
      (∀ e' ∈ E, γ * e' = e' * γ) ∧
      IsPGroup p ↥(Subgroup.closure (insert γ (insert ψ (E : Set (MulAut K))))) ∧
      e = γ * ψ⁻¹ * γ⁻¹ * ψ) :
    ∀ v ∈ ggV θ P, ∃ x ∈ ggS0 S θ E, ∃ y ∈ ggS0 S θ E,
      v = x * y⁻¹ * x⁻¹ * y := by
  intro v hv
  rw [ggV] at hv
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨γ, hγp, hγE, _hγgrp, heq⟩ := hPforall e he
  have hγpelt : GGL45IsPElt p (ggInducedAut θ γ) := by
    obtain ⟨k, hk⟩ := hγp
    exact ⟨k, by simp only [← map_pow, hk, map_one]⟩
  have hψpelt : GGL45IsPElt p (ggInducedAut θ ψ) :=
    ⟨1, by rw [pow_one, ← map_pow, hψp, map_one]⟩
  have hγS : ggInducedAut θ γ ∈ S := hSp _ hγpelt
  have hψS : ggInducedAut θ ψ ∈ S := hSp _ hψpelt
  have hγC : ggInducedAut θ γ ∈ ggC θ E := by
    rw [ggC, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp hh
    rw [← map_mul, ← hγE e' he', map_mul]
  have hψC : ggInducedAut θ ψ ∈ ggC θ E := by
    rw [ggC, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp hh
    rw [← map_mul, hψE e' he', map_mul]
  refine ⟨ggInducedAut θ γ, ?_, ggInducedAut θ ψ, ?_, ?_⟩
  · rw [ggS0]; exact ⟨hγS, hγC⟩
  · rw [ggS0]; exact ⟨hψS, hψC⟩
  · rw [heq]
    simp only [map_mul, map_inv]

private def ggPi0 {R : Type} [Group R] {J S S0 : Subgroup (MulAut R)}
    (hS0S : S0 ≤ S) [(J.subgroupOf S).Normal] :
    ↥S0 →* ↥S ⧸ J.subgroupOf S :=
  (QuotientGroup.mk' (J.subgroupOf S)).comp (Subgroup.inclusion hS0S)

private def ggPsi0 {R : Type} [Group R] {J S S0 N0 : Subgroup (MulAut R)}
    (hS0S : S0 ≤ S) [(J.subgroupOf S).Normal] [(N0.subgroupOf S0).Normal]
    (hker : N0.subgroupOf S0 ≤ (ggPi0 (J := J) (S := S) (S0 := S0) hS0S).ker) :
    ↥S0 ⧸ (N0.subgroupOf S0) →* ↥S ⧸ J.subgroupOf S :=
  QuotientGroup.lift (N0.subgroupOf S0)
    (ggPi0 (J := J) (S := S) (S0 := S0) hS0S) hker

private theorem ggSJ_cyclic {R : Type} [Group R] {J S : Subgroup (MulAut R)}
    [(J.subgroupOf S).Normal] (g0 : MulAut R) (hg0S : g0 ∈ S)
    (hg0cyc : ∀ s ∈ S, ∃ k : ℤ, g0 ^ k * s ∈ J) :
    IsCyclic (↥S ⧸ J.subgroupOf S) := by
  let gS : ↥S := ⟨g0, hg0S⟩
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨QuotientGroup.mk' (J.subgroupOf S) gS, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (J.subgroupOf S) x
  obtain ⟨k, hk⟩ := hg0cyc s s.2
  have h1 : QuotientGroup.mk' (J.subgroupOf S)
      (⟨g0 ^ k * s, S.mul_mem (S.zpow_mem hg0S k) s.2⟩ : ↥S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hk)
  have h2 : QuotientGroup.mk' (J.subgroupOf S)
      (⟨g0 ^ k * s, S.mul_mem (S.zpow_mem hg0S k) s.2⟩ : ↥S) =
      (QuotientGroup.mk' (J.subgroupOf S) gS) ^ k *
        QuotientGroup.mk' (J.subgroupOf S) s := by
    rw [← map_zpow, ← map_mul]
    congr 1
  have h3 : (QuotientGroup.mk' (J.subgroupOf S) gS) ^ k *
      QuotientGroup.mk' (J.subgroupOf S) s = 1 := by
    rwa [h2] at h1
  have h4 : QuotientGroup.mk' (J.subgroupOf S) s =
      (QuotientGroup.mk' (J.subgroupOf S) gS) ^ (-k) := by
    calc
      QuotientGroup.mk' (J.subgroupOf S) s =
          ((QuotientGroup.mk' (J.subgroupOf S) gS) ^ k)⁻¹ *
            ((QuotientGroup.mk' (J.subgroupOf S) gS) ^ k *
              QuotientGroup.mk' (J.subgroupOf S) s) := by group
      _ = ((QuotientGroup.mk' (J.subgroupOf S) gS) ^ k)⁻¹ * 1 := by rw [h3]
      _ = (QuotientGroup.mk' (J.subgroupOf S) gS) ^ (-k) := by group
  exact Subgroup.mem_zpowers_iff.mpr ⟨-k, h4.symm⟩

private theorem ggN0_subgroupOf_normal {R : Type} [Group R]
    {S0 N0 : Subgroup (MulAut R)}
    (hNn : ∀ s ∈ S0, ∀ u ∈ N0, s * u * s⁻¹ ∈ N0) :
    (N0.subgroupOf S0).Normal := by
  refine Subgroup.Normal.mk (fun n hn s => ?_)
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact hNn (s : MulAut R) s.2 (n : MulAut R) hn

private theorem ggPi0_kernel {R : Type} [Group R] {J S S0 N0 : Subgroup (MulAut R)}
    [(J.subgroupOf S).Normal] (hS0S : S0 ≤ S) (hN0J : N0 ≤ J) :
    N0.subgroupOf S0 ≤ (ggPi0 (J := J) (S := S) (S0 := S0) hS0S).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hxJ : (x : MulAut R) ∈ J := hN0J (Subgroup.mem_subgroupOf.mp hx)
  rw [ggPi0]
  change QuotientGroup.mk' (J.subgroupOf S) (Subgroup.inclusion hS0S x) = 1
  exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hS0S x)).mpr
    (Subgroup.mem_subgroupOf.mpr hxJ)

private theorem ggPsi0_injective {R : Type} [Group R] {J S S0 N0 : Subgroup (MulAut R)}
    [(J.subgroupOf S).Normal] [(N0.subgroupOf S0).Normal]
    (hS0S : S0 ≤ S)
    (hN0_mem : ∀ s ∈ S0, s ∈ J → s ∈ N0)
    (hker : N0.subgroupOf S0 ≤ (ggPi0 (J := J) (S := S) (S0 := S0) hS0S).ker) :
    Function.Injective (ggPsi0 (J := J) (S := S) (S0 := S0) (N0 := N0) hS0S hker) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (N0.subgroupOf S0) q
  have hq' : ggPi0 (J := J) (S := S) (S0 := S0) hS0S s = 1 := by
    rw [ggPsi0, QuotientGroup.mk'_apply, QuotientGroup.lift_mk'] at hq
    exact hq
  have hsJ : Subgroup.inclusion hS0S s ∈ J.subgroupOf S :=
    (QuotientGroup.eq_one_iff (Subgroup.inclusion hS0S s)).mp hq'
  have hsJ' : (s : MulAut R) ∈ J := Subgroup.mem_subgroupOf.mp hsJ
  have hsN : s ∈ N0.subgroupOf S0 := by
    rw [Subgroup.mem_subgroupOf]
    exact hN0_mem s s.2 hsJ'
  rw [QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff s).mpr hsN

private theorem ggS0N0_cyclic {R : Type} [Group R] {J S S0 N0 : Subgroup (MulAut R)}
    [(J.subgroupOf S).Normal] [(N0.subgroupOf S0).Normal]
    (hS0S : S0 ≤ S)
    (hker : N0.subgroupOf S0 ≤ (ggPi0 (J := J) (S := S) (S0 := S0) hS0S).ker)
    (hpsi_inj : Function.Injective
      (ggPsi0 (J := J) (S := S) (S0 := S0) (N0 := N0) hS0S hker))
    (hSJcyc : IsCyclic (↥S ⧸ J.subgroupOf S)) :
    ∃ g ∈ S0, ∀ s ∈ S0, ∃ k : ℤ, g ^ k * s ∈ N0 := by
  haveI : IsCyclic (↥S0 ⧸ (N0.subgroupOf S0)) :=
    isCyclic_of_injective _ hpsi_inj
  obtain ⟨q, hqgen⟩ := IsCyclic.exists_generator (α := ↥S0 ⧸ (N0.subgroupOf S0))
  obtain ⟨g1, hg1⟩ := QuotientGroup.mk'_surjective (N0.subgroupOf S0) q
  refine ⟨(g1 : MulAut R), g1.2, ?_⟩
  intro s hs
  have hmem : QuotientGroup.mk' (N0.subgroupOf S0) (⟨s, hs⟩ : ↥S0) ∈
      Subgroup.zpowers (QuotientGroup.mk' (N0.subgroupOf S0) g1) := by
    have h := hqgen (QuotientGroup.mk' (N0.subgroupOf S0) (⟨s, hs⟩ : ↥S0))
    rwa [← hg1] at h
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  refine ⟨-k, ?_⟩
  have h1 : QuotientGroup.mk' (N0.subgroupOf S0) ((g1 ^ (-k)) * ⟨s, hs⟩ : ↥S0) = 1 := by
    rw [map_mul, map_zpow, ← hk]
    group
  have hmemN : ((g1 ^ (-k)) * ⟨s, hs⟩ : ↥S0) ∈ N0.subgroupOf S0 :=
    (QuotientGroup.eq_one_iff _).mp h1
  simpa using Subgroup.mem_subgroupOf.mp hmemN

private theorem ggS0N0_cyclic_main {K : Type*} {R : Type} [Group K] [Group R]
    {J S : Subgroup (MulAut R)} [(J.subgroupOf S).Normal]
    (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K))
    (g0 : MulAut R) (hg0S : g0 ∈ S)
    (hg0cyc : ∀ s ∈ S, ∃ k : ℤ, g0 ^ k * s ∈ J)
    (hNn : ∀ s ∈ ggS0 S θ E, ∀ u ∈ ggN0 J θ E, s * u * s⁻¹ ∈ ggN0 J θ E) :
    ∃ g ∈ ggS0 S θ E, ∀ s ∈ ggS0 S θ E, ∃ k : ℤ, g ^ k * s ∈ ggN0 J θ E := by
  have hS0S : ggS0 S θ E ≤ S := inf_le_left
  have hN0normal : ((ggN0 J θ E).subgroupOf (ggS0 S θ E)).Normal :=
    ggN0_subgroupOf_normal (S0 := ggS0 S θ E) (N0 := ggN0 J θ E) hNn
  haveI : ((ggN0 J θ E).subgroupOf (ggS0 S θ E)).Normal := hN0normal
  have hker : (ggN0 J θ E).subgroupOf (ggS0 S θ E) ≤
      (ggPi0 (J := J) (S := S) (S0 := ggS0 S θ E) hS0S).ker :=
    ggPi0_kernel (J := J) (S := S) (S0 := ggS0 S θ E) (N0 := ggN0 J θ E)
      hS0S (inf_le_left : ggN0 J θ E ≤ J)
  have hpsi_inj : Function.Injective
      (ggPsi0 (J := J) (S := S) (S0 := ggS0 S θ E) (N0 := ggN0 J θ E) hS0S hker) :=
    ggPsi0_injective (J := J) (S := S) (S0 := ggS0 S θ E) (N0 := ggN0 J θ E)
      hS0S (ggN0_mem θ E) hker
  have hSJcyc : IsCyclic (↥S ⧸ J.subgroupOf S) := ggSJ_cyclic g0 hg0S hg0cyc
  exact ggS0N0_cyclic (J := J) (S := S) (S0 := ggS0 S θ E) (N0 := ggN0 J θ E)
    hS0S hker hpsi_inj hSJcyc

private theorem ggV_card {K : Type*} {R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {P : Subgroup (MulAut K)}
    (hK : commutator K = ⊤) :
    Nat.card (ggV θ P) = Nat.card P := by
  change Nat.card (P.map (ggInducedAut θ)) = Nat.card P
  exact Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hK θ)

private theorem ggEbar_card {K : Type*} {R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)}
    (hK : commutator K = ⊤) :
    Nat.card (ggEbar θ E) = Nat.card E := by
  change Nat.card (E.map (ggInducedAut θ)) = Nat.card E
  exact Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hK θ)

private theorem ggTarget_card {K : Type*} {R : Type} [Group K] [Group R] {p : ℕ}
    {I : Set (MulAut R)} {J : Subgroup (MulAut R)} (hJI : (J : Set (MulAut R)) = I)
    (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)} :
    Nat.card {u : MulAut R // u ∈ ggN0 J θ E ∧ u ^ p ∈ ggEbar θ E} =
      Nat.card {t : MulAut R // t ∈ I ∧
        (∀ e ∈ E, t * ggInducedAut θ e = ggInducedAut θ e * t) ∧
        t ^ p ∈ E.map (ggInducedAut θ)} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro u
  constructor
  · rintro ⟨⟨huJ, huC⟩, hup⟩
    refine ⟨hJI ▸ huJ, ?_, hup⟩
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp huC (ggInducedAut θ e)
      (Subgroup.mem_map_of_mem _ he)).symm
  · rintro ⟨huI, hucomm, hup⟩
    refine ⟨⟨hJI.symm ▸ huI, ?_⟩, hup⟩
    change u ∈ Subgroup.centralizer (ggEbar θ E : Set (MulAut R))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hh
    exact (hucomm e he).symm

private theorem ggFinal_bound {K : Type*} {R : Type} [Group K] [Group R] {p : ℕ}
    {I : Set (MulAut R)} {J : Subgroup (MulAut R)} (hJI : (J : Set (MulAut R)) = I)
    (θ : K ⧸ Subgroup.center K ≃* R) {E P : Subgroup (MulAut K)}
    (hEcardP : Nat.card E ≤ p * Nat.card P)
    (hcard : Nat.card (ggV θ P) * Nat.card (ggEbar θ E) ≤
      Nat.card {u : MulAut R // u ∈ ggN0 J θ E ∧ u ^ p ∈ ggEbar θ E})
    (hK : commutator K = ⊤) :
    Nat.card E * Nat.card E ≤ p * Nat.card {t : MulAut R // t ∈ I ∧
      (∀ e ∈ E, t * ggInducedAut θ e = ggInducedAut θ e * t) ∧
      t ^ p ∈ E.map (ggInducedAut θ)} := by
  have hVcard := ggV_card (P := P) θ hK
  have hEbar_card := ggEbar_card (E := E) θ hK
  have hset := ggTarget_card (J := J) hJI θ (p := p) (E := E)
  have hbound : Nat.card P * Nat.card E ≤
      Nat.card {t : MulAut R // t ∈ I ∧
        (∀ e ∈ E, t * ggInducedAut θ e = ggInducedAut θ e * t) ∧
        t ^ p ∈ E.map (ggInducedAut θ)} := by
    rw [← hVcard, ← hEbar_card, ← hset]
    exact hcard
  calc
    Nat.card E * Nat.card E ≤ (p * Nat.card P) * Nat.card E :=
      Nat.mul_le_mul_right _ hEcardP
    _ = p * (Nat.card P * Nat.card E) := by ring
    _ ≤ p * Nat.card {t : MulAut R // t ∈ I ∧
        (∀ e ∈ E, t * ggInducedAut θ e = ggInducedAut θ e * t) ∧
        t ^ p ∈ E.map (ggInducedAut θ)} := Nat.mul_le_mul_left p hbound

theorem ggL45TorusKGHyp_card_mul_card_le {p : ℕ} {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)}
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hH : GGL45TorusKGHyp p lab I F θ ψ E)
    (hcomm : ∀ x ∈ I, ∀ y ∈ I, (∀ e ∈ E, x * ggInducedAut θ e = ggInducedAut θ e * x) →
      (∀ e ∈ E, y * ggInducedAut θ e = ggInducedAut θ e * y) → x * y = y * x) :
    Nat.card E * Nat.card E ≤ p * Nat.card {t : MulAut R // t ∈ I ∧
      (∀ e ∈ E, t * ggInducedAut θ e = ggInducedAut θ e * t) ∧ t ^ p ∈ E.map (ggInducedAut θ)} := by
  classical
  haveI : Finite (K ⧸ Subgroup.center K) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  haveI : Finite R := Finite.of_equiv _ θ.toEquiv
  haveI : Finite (MulAut R) := TableBSymp.finite_mulAut (R := R)
  obtain ⟨hψp, hFA, hEelem, hEcard2, hD4, hInd, hψE, hSat, hRk, hP⟩ := hH
  obtain ⟨P, hPE, hEcardP, hPforall⟩ := hP
  obtain ⟨J, S, hJI, hJS, hJnorm, ⟨g0, hg0S, hg0cyc⟩, hSp⟩ := hcyc
  haveI : (J.subgroupOf S).Normal := hJnorm
  let Ebar : Subgroup (MulAut R) := ggEbar θ E
  let S0 : Subgroup (MulAut R) := ggS0 S θ E
  let N0 : Subgroup (MulAut R) := ggN0 J θ E
  let V : Subgroup (MulAut R) := ggV θ P
  have hS0S : S0 ≤ S := inf_le_left
  have hNS0 : N0 ≤ S0 := ggN0_le_ggS0 (J := J) (S := S) hJS θ E
  have hNn : ∀ s ∈ S0, ∀ u ∈ N0, s * u * s⁻¹ ∈ N0 := ggN0_normal (J := J) (S := S) hJS hJnorm θ E
  have hNcomm : ∀ x ∈ N0, ∀ y ∈ N0, x * y = y * x :=
    ggN0_commutative (J := J) hJI θ (E := E) hcomm
  have hEbarN : Ebar ≤ N0 := ggEbar_le_ggN0 (J := J) hJI θ (E := E) p hEelem hInd
  have hZ : ∀ z ∈ Ebar, ∀ s ∈ S0, z * s = s * z := ggEbar_central θ E (S := S)
  have hVexp : ∀ v ∈ V, v ^ p = 1 := ggV_exponent θ (P := P) (E := E) hPE hEelem
  have hVc : ∀ v ∈ V, ∃ x ∈ S0, ∃ y ∈ S0, v = x * y⁻¹ * x⁻¹ * y :=
    ggV_commutators θ (S := S) (E := E) (P := P) hψp hψE hSp hPforall
  have hcycS0 : ∃ g ∈ S0, ∀ s ∈ S0, ∃ k : ℤ, g ^ k * s ∈ N0 :=
    ggS0N0_cyclic_main (J := J) (S := S) θ E g0 hg0S hg0cyc hNn
  have hcard := CFSG.GroupTheory.card_mul_card_le_of_commutator_of_cyclic (G := MulAut R)
    (S := S0) (N := N0) (Z := Ebar) (V := V) hNS0 hNn hNcomm hcycS0 hEbarN hZ hVexp hVc
  exact ggFinal_bound (J := J) (E := E) (P := P) hJI θ hEcardP hcard hK

end CFSG.StandardType
