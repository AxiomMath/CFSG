module

public import CFSG.RankThree.GF2n.Smith81.S81E7Frame

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


theorem neg_mem_Perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) : -β ∈ Perp := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  show IsRoot .E7 (-β) ∧ MinData.toWeight (-β) ⬝ᵥ theta = 0
  refine ⟨isRoot_neg hβ'.1, ?_⟩
  rw [MinData.toWeight_neg, neg_dotProduct, hβ'.2, neg_zero]

theorem pr_theta_shift_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) {b : Fin e7Data.d}
    (h : pr b β = -1) : pr (shift β b) theta = pr b theta := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  rw [pr_shift hβ'.1 h theta, hβ'.2, add_zero]

variable {K : Type} [Field K]

@[expose] def Lam (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ :=
  Subgroup.closure {g | ∃ β ∈ Perp, ∃ c : K, g = e7Data_valid.xu K β c}

theorem xu_mem_Lam {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (c : K) :
    e7Data_valid.xu K β c ∈ Lam K :=
  Subgroup.subset_closure ⟨β, hβ, c, rfl⟩

theorem Lam_le_E : Lam K ≤ EGrp K := by
  rw [Lam, Subgroup.closure_le]
  rintro g ⟨β, _, c, rfl⟩
  exact e7Data_valid.xu_mem K β c

theorem theta_dot_perp_zero {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    MinData.toWeight theta ⬝ᵥ β = 0 := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  exact (form_comm posDef_cartan_E7 β theta).symm.trans hβ'.2

theorem negtheta_dot_perp_zero {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    MinData.toWeight (-theta) ⬝ᵥ β = 0 := by
  rw [MinData.toWeight_neg, neg_dotProduct, theta_dot_perp_zero hβ, neg_zero]

theorem pr_shift_theta_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) {b : Fin e7Data.d}
    (h : pr b theta = -1) : pr (shift theta b) β = pr b β := by
  rw [pr_shift isRoot_theta h β, theta_dot_perp_zero hβ, add_zero]

theorem pr_shift_negtheta_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) {b : Fin e7Data.d}
    (h : pr b theta = 1) : pr (shift (-theta) b) β = pr b β := by
  have h' : pr b (-theta) = -1 := by rw [pr_neg, h]
  rw [pr_shift (isRoot_neg isRoot_theta) h' β, negtheta_dot_perp_zero hβ, add_zero]

theorem shift_comm_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) (hδβ : MinData.toWeight δ ⬝ᵥ β = 0)
    {b : Fin e7Data.d} (hb : pr b β = 1) (hbδ : pr b δ = -1) :
    shift δ (shift (-β) b) = shift (-β) (shift δ b) := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  have hβδ : MinData.toWeight β ⬝ᵥ δ = 0 := (form_comm posDef_cartan_E7 β δ).trans hδβ
  have hb' : pr b (-β) = -1 := by rw [pr_neg, hb]
  have hw1 : e7Data.wt (shift (-β) b) = e7Data.wt b + MinData.toWeight (-β) :=
    wt_shift (isRoot_neg hβ'.1) hb'
  have hp1 : pr (shift (-β) b) δ = -1 := by
    rw [pr_shift (isRoot_neg hβ'.1) hb' δ, MinData.toWeight_neg, neg_dotProduct, hβδ, neg_zero,
      add_zero, hbδ]
  have hw2 : e7Data.wt (shift δ (shift (-β) b)) = e7Data.wt (shift (-β) b) + MinData.toWeight δ :=
    wt_shift hδ hp1
  have hw3 : e7Data.wt (shift δ b) = e7Data.wt b + MinData.toWeight δ := wt_shift hδ hbδ
  have hp2 : pr (shift δ b) β = 1 := by
    rw [pr_shift hδ hbδ β, hδβ, add_zero, hb]
  have hw4 : e7Data.wt (shift (-β) (shift δ b)) = e7Data.wt (shift δ b) + MinData.toWeight (-β) :=
    wt_shift (isRoot_neg hβ'.1) (by rw [pr_neg, hp2])
  apply wt_injective
  rw [hw2, hw1, hw4, hw3]
  abel

theorem xu_perp_comm_jOp [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (c : K)
    (m : Matrix (Fin 2) (Fin 2) K) :
    (e7Data_valid.xu K β c : Module.End K (V K)) * jOp m =
      jOp m * (e7Data_valid.xu K β c : Module.End K (V K)) := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  rw [Module.End.mul_apply, Module.End.mul_apply, xu_apply_coord hβ'.1 c (jOp m v) b]
  simp only [jOp_apply]
  by_cases hb1 : pr b β = 1
  · have hb' : pr b (-β) = -1 := by rw [pr_neg, hb1]
    have hbs : pr (shift (-β) b) theta = pr b theta :=
      pr_theta_shift_perp (neg_mem_Perp hβ) hb'
    rcases pr_mem isRoot_theta b with h | h | h
    · have hs : pr (shift (-β) b) theta = -1 := hbs.trans h
      have hsθ : pr (shift theta b) β = 1 := (pr_shift_theta_perp hβ h).trans hb1
      have hcomm : shift theta (shift (-β) b) = shift (-β) (shift theta b) :=
        shift_comm_perp hβ isRoot_theta (theta_dot_perp_zero hβ) hb1 h
      simp only [jFun_of_neg h, jFun_of_neg hs, xu_apply_coord hβ'.1, hb1, hsθ, hcomm,
        ↓reduceIte] <;> ring
    · have hs : pr (shift (-β) b) theta = 0 := hbs.trans h
      simp only [jFun_of_zero h, jFun_of_zero hs, xu_apply_coord hβ'.1, hb1, ↓reduceIte] <;> ring
    · have hs : pr (shift (-β) b) theta = 1 := hbs.trans h
      have hsθ : pr (shift (-theta) b) β = 1 := (pr_shift_negtheta_perp hβ h).trans hb1
      have hcomm : shift (-theta) (shift (-β) b) = shift (-β) (shift (-theta) b) :=
        shift_comm_perp hβ (isRoot_neg isRoot_theta) (negtheta_dot_perp_zero hβ) hb1
          (by rw [pr_neg, h])
      simp only [jFun_of_pos h, jFun_of_pos hs, xu_apply_coord hβ'.1, hb1, hsθ, hcomm,
        ↓reduceIte] <;> ring
  · rcases pr_mem isRoot_theta b with h | h | h
    · have hsθ : ¬ pr (shift theta b) β = 1 := by
        rw [pr_shift_theta_perp hβ h]
        exact hb1
      simp only [jFun_of_neg h, xu_apply_coord hβ'.1, hb1, hsθ, ↓reduceIte] <;> ring
    · simp only [jFun_of_zero h, xu_apply_coord hβ'.1, hb1, ↓reduceIte] <;> ring
    · have hsβ : ¬ pr (shift (-theta) b) β = 1 := by
        rw [pr_shift_negtheta_perp hβ h]
        exact hb1
      simp only [jFun_of_pos h, xu_apply_coord hβ'.1, hb1, hsβ, ↓reduceIte] <;> ring

theorem Lam_commute_J [CharP K 2] {l j : (Module.End K (V K))ˣ} (hl : l ∈ Lam K)
    (hj : j ∈ Jgrp K) : l * j = j * l := by
  have hgen : Lam K ≤ Subgroup.centralizer (Jgrp K : Set (Module.End K (V K))ˣ) := by
    rw [Lam, Subgroup.closure_le]
    rintro g ⟨β, hβ, c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro j' hj'
    rw [SetLike.mem_coe, Jgrp_eq_range] at hj'
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hj'
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, jHom_val]
    exact (xu_perp_comm_jOp hβ c m).symm
  exact (Subgroup.mem_centralizer_iff.mp (hgen hl) j hj).symm

theorem Lam_stabilizes_V0 [CharP K 2] {l : (Module.End K (V K))ˣ} (hl : l ∈ Lam K) {v : V K}
    (hv : v ∈ V0 K) : (l : Module.End K (V K)) v ∈ V0 K := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (Module.End K (V K))ˣ, ∀ g : (Module.End K (V K))ˣ, g ∈ H ↔
      ((∀ w ∈ V0 K, (g : Module.End K (V K)) w ∈ V0 K) ∧
        (∀ w ∈ V0 K, ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) w ∈ V0 K)) := by
    refine ⟨{
        carrier := {g | (∀ w ∈ V0 K, (g : Module.End K (V K)) w ∈ V0 K) ∧
          (∀ w ∈ V0 K, ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) w ∈ V0 K)},
        mul_mem' := ?_,
        one_mem' := ?_,
        inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rw [Units.val_mul, Module.End.mul_apply]
        exact ha1 _ (hb1 w hw)
      · rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]
        exact hb2 _ (ha2 w hw)
    · refine ⟨fun w hw => ?_, fun w hw => ?_⟩ <;> simpa using hw
    · rintro x ⟨hx1, hx2⟩
      refine ⟨hx2, fun w hw => ?_⟩
      rw [inv_inv]
      exact hx1 w hw
  have hgen : ∀ β : Fin (Tag.rank .E7) → ℤ, β ∈ Perp → ∀ c : K, ∀ w ∈ V0 K,
      ((e7Data_valid.xu K β c : (Module.End K (V K))ˣ) : Module.End K (V K)) w ∈ V0 K := by
    intro β hβ c w hw
    have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
    rw [mem_V0]
    intro b hb
    have hb' : pr b theta ≠ 0 := fun h => hb (mem_idx0.2 h)
    have hwb : w b = 0 := (mem_V0.1 hw) b hb
    rw [xu_apply_coord hβ'.1 c w b]
    by_cases hp : pr b β = 1
    · have hb2 : pr b (-β) = -1 := by rw [pr_neg, hp]
      have hsh : pr (shift (-β) b) theta = pr b theta :=
        pr_theta_shift_perp (neg_mem_Perp hβ) hb2
      have hsh0 : shift (-β) b ∉ idx0 := by
        rw [mem_idx0, hsh]
        exact hb'
      rw [if_pos hp, (mem_V0.1 hw) _ hsh0, hwb, mul_zero, add_zero]
    · rw [if_neg hp, mul_zero, add_zero, hwb]
  have hinv : ∀ β : Fin (Tag.rank .E7) → ℤ, ∀ c : K,
      ((e7Data_valid.xu K β c)⁻¹ : (Module.End K (V K))ˣ) = e7Data_valid.xu K β (-c) := by
    intro β c
    apply inv_eq_of_mul_eq_one_right
    rw [← e7Data_valid.xu_add, add_neg_cancel, e7Data_valid.xu_zero]
  have hLam : Lam K ≤ H := by
    rw [Lam, Subgroup.closure_le]
    rintro g ⟨β, hβ, c, rfl⟩
    rw [SetLike.mem_coe, hH]
    exact ⟨hgen β hβ c, fun w hw => by rw [hinv β c]; exact hgen β hβ (-c) w hw⟩
  exact ((hH l).1 (hLam hl)).1 v hv

theorem idx0_separated_aux : ∀ a a' : Fin e7Data.d, pr a theta = 0 → pr a' theta = 0 → a ≠ a' →
    ∃ k : Fin 126, (MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0) ∧
      ¬ (pr a ((Tag.rootCertificate .E7).root k) = -1 ↔
        pr a' ((Tag.rootCertificate .E7).root k) = -1) := by
  unfold pr
  decide +kernel

theorem idx0_separated {a a' : Fin e7Data.d} (ha : a ∈ idx0) (ha' : a' ∈ idx0) (hne : a ≠ a') :
    ∃ β ∈ Perp, ¬ (pr a β = -1 ↔ pr a' β = -1) := by
  obtain ⟨k, hk1, hk2⟩ := idx0_separated_aux a a' (mem_idx0.1 ha) (mem_idx0.1 ha') hne
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  refine ⟨(Tag.rootCertificate .E7).root k, ?_, hk2⟩
  show IsRoot .E7 ((Tag.rootCertificate .E7).root k) ∧
    MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0
  exact ⟨RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega), hk1⟩

@[expose] def adjD (a b : Fin e7Data.d) : Prop :=
  ∃ k : Fin 126, (MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0) ∧
    pr a ((Tag.rootCertificate .E7).root k) = -1 ∧
    e7Data.wt b = e7Data.wt a + MinData.toWeight ((Tag.rootCertificate .E7).root k)

instance (a b : Fin e7Data.d) : Decidable (adjD a b) := by unfold adjD; infer_instance

theorem adjD_iff {a b : Fin e7Data.d} :
    adjD a b ↔ ∃ β ∈ Perp, pr a β = -1 ∧ shift β a = b := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  constructor
  · intro h
    unfold adjD at h
    obtain ⟨k, hk1, hk2, hk3⟩ := h
    refine ⟨(Tag.rootCertificate .E7).root k, ?_, hk2, shift_eq hk3⟩
    show IsRoot .E7 ((Tag.rootCertificate .E7).root k) ∧
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0
    exact ⟨RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega), hk1⟩
  · rintro ⟨β, hβ, hpa, hsh⟩
    have hβP : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
    obtain ⟨k, hk, hkβ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hβP.1
    unfold adjD
    refine ⟨⟨k, by omega⟩, ?_, ?_, ?_⟩
    · show MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0
      rw [hkβ]
      exact hβP.2
    · show pr a ((Tag.rootCertificate .E7).root k) = -1
      rw [hkβ]
      exact hpa
    · show e7Data.wt b = e7Data.wt a + MinData.toWeight ((Tag.rootCertificate .E7).root k)
      rw [hkβ, ← hsh]
      exact wt_shift hβP.1 hpa

@[expose] def stepSet (S : Finset (Fin e7Data.d)) : Finset (Fin e7Data.d) :=
  S ∪ idx0.filter fun b => ∃ a ∈ S, adjD a b

theorem bfs_idx0 : ∀ a ∈ idx0, stepSet^[3] {a} = idx0 := by
  unfold stepSet adjD idx0 pr
  decide +kernel

theorem reach_of_mem_iterate (a : Fin e7Data.d) :
    ∀ n b, b ∈ stepSet^[n] {a} → Relation.ReflTransGen adjD a b := by
  intro n
  induction n with
  | zero =>
    intro b hb
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at hb
    subst hb
    exact .refl
  | succ n ih =>
    intro b hb
    rw [Function.iterate_succ_apply'] at hb
    simp only [stepSet, Finset.mem_union, Finset.mem_filter] at hb
    rcases hb with hb | ⟨_, a', ha', hadj⟩
    · exact ih b hb
    · exact (ih a' ha').tail hadj

theorem connected_idx0 {a b : Fin e7Data.d} (ha : a ∈ idx0) (hb : b ∈ idx0) :
    Relation.ReflTransGen adjD a b :=
  reach_of_mem_iterate a 3 b (by rw [bfs_idx0 a ha]; exact hb)

theorem exists_adjD : ∀ a : Fin e7Data.d, pr a theta = 0 → ∃ b, adjD a b := by
  unfold adjD pr
  decide +kernel

theorem Lam_swap [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) {a : Fin e7Data.d}
    (h : pr a β = -1) :
    ∃ l ∈ Lam K, (l : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single (shift β a) 1 := by
  have hβP : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  have hβR : IsRoot .E7 β := hβP.1
  have hmβ : -β ∈ Perp := by
    show IsRoot .E7 (-β) ∧ MinData.toWeight (-β) ⬝ᵥ theta = 0
    refine ⟨isRoot_neg hβR, ?_⟩
    rw [MinData.toWeight_neg, neg_dotProduct, hβP.2, neg_zero]
  have hx : e7Data_valid.xu K β 1 ∈ Lam K := xu_mem_Lam hβ 1
  have hy : e7Data_valid.xu K (-β) 1 ∈ Lam K := xu_mem_Lam hmβ 1
  refine ⟨e7Data_valid.xu K β 1 * e7Data_valid.xu K (-β) 1 * e7Data_valid.xu K β 1,
    mul_mem (mul_mem hx hy) hx, ?_⟩
  have hs1 : pr (shift β a) β = 1 := pr_shift_self hβR h
  have hne1 : ¬ pr (shift β a) β = -1 := by omega
  have hne2 : ¬ pr a (-β) = -1 := by rw [pr_neg]; omega
  have hpb : pr (shift β a) (-β) = -1 := by rw [pr_neg]; omega
  have A1 : (e7Data_valid.xu K β 1 : Module.End K (V K)) (Finsupp.single a 1) =
      Finsupp.single a 1 + Finsupp.single (shift β a) 1 := by
    rw [e7Data_valid.xu_apply, rootOp_single (K := K) hβR a, if_pos h, one_smul]
  have A2 : (e7Data_valid.xu K β 1 : Module.End K (V K)) (Finsupp.single (shift β a) 1) =
      Finsupp.single (shift β a) 1 := by
    rw [e7Data_valid.xu_apply, rootOp_single (K := K) hβR (shift β a), if_neg hne1, smul_zero,
      add_zero]
  have B1 : (e7Data_valid.xu K (-β) 1 : Module.End K (V K)) (Finsupp.single a 1) =
      Finsupp.single a 1 := by
    rw [e7Data_valid.xu_apply, rootOp_single (K := K) (isRoot_neg hβR) a, if_neg hne2, smul_zero,
      add_zero]
  have B2 : (e7Data_valid.xu K (-β) 1 : Module.End K (V K)) (Finsupp.single (shift β a) 1) =
      Finsupp.single (shift β a) 1 + Finsupp.single a 1 := by
    rw [e7Data_valid.xu_apply, rootOp_single (K := K) (isRoot_neg hβR) (shift β a), if_pos hpb,
      shift_neg_shift hβR h, one_smul]
  have hvv : ∀ v : V K, v + v = 0 := by
    intro v
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 := congrArg (fun c : K => c • v) h2
    simpa [two_smul] using h3
  have gen : ∀ x y : V K, x + y + (y + (x + y)) = y := by
    intro x y
    calc x + y + (y + (x + y)) = (x + x) + (y + y) + y := by abel
      _ = y := by simp [hvv]
  simp only [Units.val_mul, Module.End.mul_apply, map_add, A1, A2, B1, B2]
  exact gen _ _

theorem Lam_transitive_wt [CharP K 2] {a b : Fin e7Data.d} (ha : a ∈ idx0) (hb : b ∈ idx0) :
    ∃ l ∈ Lam K, (l : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single b 1 := by
  have key : ∀ c : Fin e7Data.d, Relation.ReflTransGen adjD a c →
      ∃ l ∈ Lam K, (l : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single c 1 := by
    intro c hc
    induction hc with
    | refl => exact ⟨1, (Lam K).one_mem, by simp⟩
    | tail _ hcd ih =>
      obtain ⟨l, hl, hl_eq⟩ := ih
      obtain ⟨β, hβ, hpa, hsh⟩ := adjD_iff.1 hcd
      obtain ⟨m, hm, hm_eq⟩ := Lam_swap (K := K) hβ hpa
      refine ⟨m * l, mul_mem hm hl, ?_⟩
      rw [Units.val_mul, Module.End.mul_apply, hl_eq, hm_eq, hsh]
  exact key b (connected_idx0 ha hb)

section Irred

variable [CharP K 2] (S : AddSubgroup (V K))

theorem scalar_closure (hΛ : ∀ l ∈ Lam K, ∀ s ∈ S, (l : Module.End K (V K)) s ∈ S)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (c : K) {s : V K} (hs : s ∈ S) :
    c • e7Data.rootOp K β s ∈ S := by
  have h1 : (e7Data_valid.xu K β c : Module.End K (V K)) s ∈ S :=
    hΛ _ (xu_mem_Lam hβ c) s hs
  have h2 : (e7Data_valid.xu K β c : Module.End K (V K)) s = s + c • e7Data.rootOp K β s := by
    rw [e7Data_valid.xu_apply]
  have h3 : c • e7Data.rootOp K β s = (e7Data_valid.xu K β c : Module.End K (V K)) s - s := by
    rw [h2]
    abel
  rw [h3]
  exact S.sub_mem h1 hs

set_option linter.constructorNameAsVariable false in
theorem exists_single_of_ne_bot (hS : ∀ s ∈ S, s ∈ V0 K)
    (hΛ : ∀ l ∈ Lam K, ∀ s ∈ S, (l : Module.End K (V K)) s ∈ S) (hne : S ≠ ⊥) :
    ∃ a ∈ idx0, ∃ c : K, c ≠ 0 ∧ c • Finsupp.single a (1 : K) ∈ S := by
  classical
  obtain ⟨s₀, hs₀, hs₀0⟩ : ∃ t : V K, t ∈ S ∧ t ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    rw [AddSubgroup.mem_bot]
    exact h x hx
  have hex : ∃ n : ℕ, ∃ t : V K, t ∈ S ∧ t ≠ 0 ∧ t.support.card = n :=
    ⟨s₀.support.card, s₀, hs₀, hs₀0, rfl⟩
  obtain ⟨s, hs, hs0, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ t ∈ S, t ≠ 0 → s.support.card ≤ t.support.card := by
    intro t ht ht0
    rw [hcard]
    exact Nat.find_min' hex ⟨t, ht, ht0, rfl⟩
  have hsV : ∀ b, b ∉ idx0 → s b = 0 := mem_V0.1 (hS s hs)
  have hsupp0 : ∀ x ∈ s.support, x ∈ idx0 := by
    intro x hx
    by_contra h
    exact (Finsupp.mem_support_iff.mp hx) (hsV x h)
  have key : ∀ x y : Fin e7Data.d, x ∈ s.support → y ∈ s.support →
      ∀ β ∈ Perp, pr x β = -1 → pr y β ≠ -1 → False := by
    intro x y hx hy β hβ hx1 hy1
    have hβP : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
    have hs' : e7Data.rootOp K β s ∈ S := by
      have h := scalar_closure S hΛ hβ 1 hs
      rwa [one_smul] at h
    have hval : (e7Data.rootOp K β s) (shift β x) = s x := by
      rw [rootOp_apply (K := K) hβP.1 s (shift β x), if_pos (pr_shift_self hβP.1 hx1),
        shift_neg_shift hβP.1 hx1]
    have hs'0 : e7Data.rootOp K β s ≠ 0 := by
      intro h0
      apply Finsupp.mem_support_iff.mp hx
      rw [← hval, h0, Finsupp.zero_apply]
    have hsub : (e7Data.rootOp K β s).support ⊆ (s.support.erase y).image (shift β) := by
      intro b hb
      rw [Finsupp.mem_support_iff, rootOp_apply (K := K) hβP.1 s b] at hb
      by_cases hb1 : pr b β = 1
      · rw [if_pos hb1] at hb
        rw [Finset.mem_image]
        refine ⟨shift (-β) b, ?_, shift_shift_neg hβP.1 hb1⟩
        rw [Finset.mem_erase, Finsupp.mem_support_iff]
        refine ⟨?_, hb⟩
        intro h
        have hpa : pr (shift (-β) b) β = -1 := pr_shift_neg hβP.1 hb1
        rw [h] at hpa
        exact hy1 hpa
      · rw [if_neg hb1] at hb
        exact absurd rfl hb
    have hcard1 : (e7Data.rootOp K β s).support.card ≤ (s.support.erase y).card :=
      (Finset.card_le_card hsub).trans Finset.card_image_le
    have hcard2 : (s.support.erase y).card < s.support.card :=
      Finset.card_erase_lt_of_mem hy
    have hmin' := hmin _ hs' hs'0
    omega
  have hone : s.support.card = 1 := by
    by_contra hne1
    have hpos : 0 < s.support.card := by
      obtain ⟨x, hx⟩ : ∃ x, s x ≠ 0 := by
        by_contra h
        push Not at h
        exact hs0 (Finsupp.ext fun x => by simpa using h x)
      exact Finset.card_pos.mpr ⟨x, Finsupp.mem_support_iff.mpr hx⟩
    have hgt : 1 < s.support.card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hgt
    obtain ⟨β, hβ, hiff⟩ := idx0_separated (hsupp0 x hx) (hsupp0 y hy) hxy
    by_cases h1 : pr x β = -1
    · exact key x y hx hy β hβ h1 (fun h2 => hiff ⟨fun _ => h2, fun _ => h1⟩)
    · have h2 : pr y β = -1 := by
        by_contra h2
        exact hiff ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      exact key y x hy hx β hβ h2 h1
  obtain ⟨a, hsupp⟩ := Finset.card_eq_one.mp hone
  have ha : a ∈ s.support := by
    rw [hsupp]
    exact Finset.mem_singleton_self a
  have hsa : s a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hseq : s = s a • Finsupp.single a (1 : K) := by
    ext b
    by_cases hb : b = a
    · subst hb
      simp
    · have hb0 : s b = 0 := by
        by_contra hne2
        have hbm : b ∈ s.support := Finsupp.mem_support_iff.mpr hne2
        rw [hsupp, Finset.mem_singleton] at hbm
        exact hb hbm
      rw [hb0, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hb), smul_zero]
  refine ⟨a, hsupp0 a ha, s a, hsa, ?_⟩
  rw [← hseq]
  exact hs

theorem line_step (hΛ : ∀ l ∈ Lam K, ∀ s ∈ S, (l : Module.End K (V K)) s ∈ S)
    {a b : Fin e7Data.d} (hab : adjD a b) (h : ∀ c : K, c • Finsupp.single a (1 : K) ∈ S) :
    ∀ c : K, c • Finsupp.single b (1 : K) ∈ S := by
  intro c
  obtain ⟨β, hβ, hpa, hsh⟩ := adjD_iff.1 hab
  have hβP : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  have h1 := scalar_closure S hΛ hβ c (h 1)
  have h2 : e7Data.rootOp K β ((1 : K) • Finsupp.single a (1 : K)) = Finsupp.single b (1 : K) := by
    rw [one_smul, rootOp_single (K := K) hβP.1 a, if_pos hpa, hsh]
  rw [h2] at h1
  exact h1

theorem Lam_irreducible_V0 (hS : ∀ s ∈ S, s ∈ V0 K)
    (hΛ : ∀ l ∈ Lam K, ∀ s ∈ S, (l : Module.End K (V K)) s ∈ S) :
    S = ⊥ ∨ S = (V0 K).toAddSubgroup := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨a, ha, c, hc0, hca⟩ := exists_single_of_ne_bot S hS hΛ hbot
  have ha' : pr a theta = 0 := mem_idx0.1 ha
  obtain ⟨b, hab⟩ := exists_adjD a ha'
  obtain ⟨β, hβ, hpa, hsh⟩ := adjD_iff.1 hab
  have hβP : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  have hb : b ∈ idx0 := by
    rw [mem_idx0, ← hsh, pr_theta_shift_perp hβ hpa]
    exact ha'
  have hlineb : ∀ c'' : K, c'' • Finsupp.single b (1 : K) ∈ S := by
    intro c''
    have h1 := scalar_closure S hΛ hβ (c'' / c) hca
    have h2 : e7Data.rootOp K β (c • Finsupp.single a (1 : K)) = c • Finsupp.single b (1 : K) := by
      rw [map_smul, rootOp_single (K := K) hβP.1 a, if_pos hpa, hsh]
    have hcc : c'' / c * c = c'' := by field_simp
    rw [h2, smul_smul, hcc] at h1
    exact h1
  have hall : ∀ d : Fin e7Data.d, Relation.ReflTransGen adjD b d →
      ∀ c'' : K, c'' • Finsupp.single d (1 : K) ∈ S := by
    intro d hd
    induction hd with
    | refl => exact hlineb
    | tail _ hde ih => exact line_step S hΛ hde ih
  have hfull : ∀ d ∈ idx0, ∀ c'' : K, c'' • Finsupp.single d (1 : K) ∈ S :=
    fun d hd => hall d (connected_idx0 hb hd)
  apply le_antisymm
  · intro s hs
    exact (Submodule.mem_toAddSubgroup _).2 (hS s hs)
  · intro v hv
    have hv' : v ∈ V0 K := (Submodule.mem_toAddSubgroup _).1 hv
    have hsum : v = ∑ d ∈ v.support, v d • Finsupp.single d (1 : K) := by
      have h := Finsupp.sum_single v
      rw [Finsupp.sum] at h
      conv_lhs => rw [← h]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finsupp.smul_single_one]
    have hmem : ∑ d ∈ v.support, v d • Finsupp.single d (1 : K) ∈ S := by
      apply AddSubgroup.sum_mem
      intro d hd
      have hdI : d ∈ idx0 := by
        by_contra h
        exact (Finsupp.mem_support_iff.mp hd) ((mem_V0.1 hv') d h)
      exact hfull d hdI (v d)
    rw [← hsum] at hmem
    exact hmem

end Irred

end CFSG.RankThree.GF2n.Smith81.E7Model
