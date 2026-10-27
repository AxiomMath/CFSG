module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ComplementCore

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec715Torus

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalGroups.F2Fixed
open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem eichlerG_nonA2 {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (P : HypPair Q) {b : V} (hbe : polar Q P.e b = 0) (hQb : Q b ≠ 0) :
    (eichlerG Q P.e b).NonA2 := by
  refine ⟨P.f, ?_⟩
  show polar Q P.f (eichler Q P.e b P.f) ≠ 0
  rw [polar_apply_eichler_self P.Q_e hbe, P.Q_f, P.polar_fe]
  simpa using hQb

section ExtData

variable {M₀ M : Type} [AddCommGroup M₀] [Finite M₀] [DistribMulAction (Gom (quadPlus n K)) M₀]
  [AddCommGroup M] [Finite M] [DistribMulAction (Gom (quadPlus n K)) M]
  {V₀ : AddSubgroup M} {π : M →+ M₀} {P : HypPair (quadPlus n K)}

theorem ExtData.range_comm_nonA2 (hn : 4 ≤ n) (H : ExtData K n M₀ M V₀ π P)
    {x : Gom (quadPlus n K)} (hx : x ∈ Lom (quadPlus n K) P.e) (hxn : x.NonA2) :
    (comm M₀ x).range = fixedSub M₀ (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) := by
  obtain ⟨w, hwe, hwf⟩ := exists_gom_swap (by omega) P
  exact (stroth_2_1_ii_omega_fixed (nondegenerate_polarBilin_quadPlus n K) H.two₀ P.Q_f P.Q_e
    (by rw [P.polar_fe]; exact one_ne_zero) hwf H.dec.symm hx hxn).2.1

theorem ExtData.comm_mem_fixedSub (hK : 2 < Nat.card K) (hn : 4 ≤ n)
    (H : ExtData K n M₀ M V₀ π P) {l : Gom (quadPlus n K)}
    (hl : l ∈ Lom (quadPlus n K) P.e) (m : M₀) :
    l • m - m ∈ fixedSub M₀ (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hef : polar (quadPlus n K) P.f P.e ≠ 0 := by
    rw [P.polar_fe]
    exact one_ne_zero
  have hcl := Lom_le_closure_eichlerNonA2Set hQ P.Q_f P.Q_e hef hK hl
  have key : ∀ g ∈ Subgroup.closure (eichlerNonA2Set (quadPlus n K) P.f P.e),
      ∀ m : M₀, g • m - m ∈ fixedSub M₀ (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨w, hfw, hew, hQw, rfl⟩ := ha
      intro m
      have hmem : eichlerG (quadPlus n K) P.e w ∈ Lom (quadPlus n K) P.e := eichlerG_mem_Lom hew
      have hr := H.range_comm_nonA2 hn hmem (eichlerG_nonA2 P hew hQw)
      rw [← hr]
      exact ⟨m, rfl⟩
    | one => intro m; simp
    | mul a b _ _ iha ihb =>
      intro m
      have e : (a * b) • m - m = (a • (b • m) - b • m) + (b • m - m) := by
        rw [mul_smul]
        abel
      rw [e]
      exact AddSubgroup.add_mem _ (iha _) (ihb m)
    | inv a _ iha =>
      intro m
      have e : a⁻¹ • m - m = -(a • (a⁻¹ • m) - a⁻¹ • m) := by
        rw [smul_inv_smul]
        abel
      rw [e]
      exact AddSubgroup.neg_mem _ (iha _)
  exact key l hcl m

theorem ExtData.range_comm_le_of_nonA2 (hK : 2 < Nat.card K) (hn : 4 ≤ n)
    (H : ExtData K n M₀ M V₀ π P) {x : Gom (quadPlus n K)}
    (hx : x ∈ Lom (quadPlus n K) P.e) (hxn : x.NonA2) {l : Gom (quadPlus n K)}
    (hl : l ∈ Lom (quadPlus n K) P.e) : (comm M l).range ≤ (comm M x).range := by
  obtain ⟨Y, hY, hinv⟩ := H.exists_complement hK hn
  have hC₀ := H.range_comm_nonA2 hn hx hxn
  have hrY : ∀ g ∈ Lom (quadPlus n K) P.e, (comm M g).range ≤ Y := by
    intro g hg
    rintro _ ⟨m, rfl⟩
    have hm : m ∈ Y ⊔ V₀ := by rw [hY.sup_eq_top]; trivial
    obtain ⟨y, hy, v, hv, rfl⟩ := AddSubgroup.mem_sup.mp hm
    have e : comm M g (y + v) = g • y - y := by
      rw [map_add, comm_apply, comm_apply, H.fixed g v hv, sub_self, add_zero]
    rw [e]
    exact Y.sub_mem (hinv g hg y hy) hy
  have hrC : ∀ g ∈ Lom (quadPlus n K) P.e, ∀ m : M,
      π (comm M g m) ∈ fixedSub M₀ (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) := by
    intro g hg m
    rw [comm_apply, map_sub, H.equiv]
    exact H.comm_mem_fixedSub hK hn hg (π m)
  rintro _ ⟨m, rfl⟩
  have h1 := hrY l hl ⟨m, rfl⟩
  have h2 := hrC l hl m
  rw [← hC₀] at h2
  obtain ⟨m₀, hm₀⟩ := h2
  obtain ⟨m₁, rfl⟩ := H.surj m₀
  have hdiff : π (comm M l m - comm M x m₁) = 0 := by
    rw [map_sub, ← hm₀, comm_apply (M := M₀), comm_apply (M := M), map_sub, H.equiv]
    simp
  have hv : comm M l m - comm M x m₁ ∈ V₀ := (H.ker _).mp hdiff
  have hx1 : comm M x m₁ ∈ Y := hrY x hx ⟨m₁, rfl⟩
  have hv' : comm M l m - comm M x m₁ ∈ Y := Y.sub_mem h1 hx1
  have h0 : comm M l m - comm M x m₁ ∈ Y ⊓ V₀ := ⟨hv', hv⟩
  rw [hY.inf_eq_bot, AddSubgroup.mem_bot, sub_eq_zero] at h0
  rw [h0]
  exact ⟨m₁, rfl⟩

end ExtData

end CFSG.RankThree.GF2n.Stroth80.Sec715Torus
