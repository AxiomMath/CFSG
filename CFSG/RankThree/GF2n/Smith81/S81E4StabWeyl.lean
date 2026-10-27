module

public import CFSG.RankThree.GF2n.Smith81.S81E7Roots

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.LieType.RootSystem


variable {K : Type} [Field K]

theorem forall_endo_single_iff [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ)
    (a : Fin e7Data.d) :
    (∀ x ∈ e7Data_valid.rootGroup K δ, endoE x (Finsupp.single a 1) = Finsupp.single a 1) ↔
      pr a δ ≠ -1 := by
  constructor
  · intro h hδa
    have h1 := h _ (e7Data_valid.xm_mem_rootGroup K δ 1)
    have h2 : endoE (e7Data_valid.xm K δ 1) (Finsupp.single a 1) =
        Finsupp.single a 1 + Finsupp.single (shift δ a) 1 := by
      change ((e7Data_valid.xu K δ 1 : (Module.End K (V K))ˣ) : Module.End K (V K))
        (Finsupp.single a 1) = _
      rw [e7Data_valid.xu_apply, rootOp_single hδ a, if_pos hδa, one_smul]
    rw [h2, add_eq_left] at h1
    exact one_ne_zero (Finsupp.single_eq_zero.1 h1)
  · intro hδa x hx
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hx
    change ((e7Data_valid.xu K δ c : (Module.End K (V K))ˣ) : Module.End K (V K))
      (Finsupp.single a 1) = Finsupp.single a 1
    rw [e7Data_valid.xu_apply, rootOp_single hδ a, if_neg hδa, smul_zero, add_zero]

theorem endo_inv_single {n : e7Data_valid.minGroup K} {a : Fin e7Data.d} {c : K}
    (hc : endoE n (Finsupp.single a 1) = c • Finsupp.single a 1) :
    c ≠ 0 ∧ endoE n⁻¹ (Finsupp.single a 1) = c⁻¹ • Finsupp.single a 1 := by
  have hinv : ∀ v, endoE n⁻¹ (endoE n v) = v := fun v => by
    change e7Data_valid.endo K n⁻¹ (e7Data_valid.endo K n v) = v
    rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have h := hinv (Finsupp.single a 1)
    rw [hc, map_zero] at h
    exact one_ne_zero (Finsupp.single_eq_zero.1 h.symm)
  refine ⟨hc0, ?_⟩
  have h := hinv (Finsupp.single a 1)
  rw [hc, map_smul] at h
  calc endoE n⁻¹ (Finsupp.single a 1)
      = c⁻¹ • (c • endoE n⁻¹ (Finsupp.single a 1)) := by
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • Finsupp.single a 1 := by rw [h]

theorem pr_weylAction_of_actsAs [CharP K 2] {n : e7Data_valid.minGroup K} {w : W7 K}
    (hn : ActsAs (e7Datum K) n w) {a : Fin e7Data.d} {c : K}
    (hc : endoE n (Finsupp.single a 1) = c • Finsupp.single a 1)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) :
    pr a (weylAction (e7Datum K).isFiniteType w δ) = pr a δ := by
  obtain ⟨hc0, hci⟩ := endo_inv_single hc
  have hinv : ∀ v, endoE n⁻¹ (endoE n v) = v := fun v => by
    change e7Data_valid.endo K n⁻¹ (e7Data_valid.endo K n v) = v
    rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]
  have hroot : ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ →
      IsRoot .E7 (weylAction (e7Datum K).isFiniteType w δ) := fun δ hδ =>
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1
      (weylAction_mem_roots _ w ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hδ))
  have key : ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ →
      (pr a δ ≠ -1 ↔ pr a (weylAction (e7Datum K).isFiniteType w δ) ≠ -1) := by
    intro δ hδ
    have hδR : δ ∈ (e7Datum K).roots :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hδ
    rw [← forall_endo_single_iff (K := K) hδ, ← forall_endo_single_iff (K := K) (hroot δ hδ)]
    have hmap : (e7Data_valid.rootGroup K δ).map (MulAut.conj n).toMonoidHom =
        e7Data_valid.rootGroup K (weylAction (e7Datum K).isFiniteType w δ) := hn δ hδR
    constructor
    · intro h y hy
      rw [← hmap] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx0 := h x hx
      change e7Data_valid.endo K (n * x * n⁻¹) (Finsupp.single a 1) = Finsupp.single a 1
      rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, Module.End.mul_apply,
        Module.End.mul_apply]
      change endoE n (endoE x (endoE n⁻¹ (Finsupp.single a 1))) = Finsupp.single a 1
      rw [hci, map_smul, hx0, map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · intro h x hx
      have hy : n * x * n⁻¹ ∈ e7Data_valid.rootGroup K
          (weylAction (e7Datum K).isFiniteType w δ) := by
        rw [← hmap]
        exact ⟨x, hx, rfl⟩
      have h1 := h _ hy
      change e7Data_valid.endo K (n * x * n⁻¹) (Finsupp.single a 1) = Finsupp.single a 1 at h1
      rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, Module.End.mul_apply,
        Module.End.mul_apply] at h1
      change endoE n (endoE x (endoE n⁻¹ (Finsupp.single a 1))) = Finsupp.single a 1 at h1
      rw [hci, map_smul] at h1
      have h2 := congrArg (endoE n⁻¹) h1
      rw [hinv, hci] at h2
      exact smul_right_injective _ (inv_ne_zero hc0) h2
  have h1 := key δ hδ
  have h2 := key (-δ) (CFSG.LieType.Chevalley.IsRoot.neg hδ)
  rw [map_neg, pr_neg, pr_neg] at h2
  rcases pr_mem hδ a with h | h | h <;> rcases pr_mem (hroot δ hδ) a with h' | h' | h' <;> omega

private theorem nW_pr_theta_eq [CharP K 2] {w : W7 K}
    (hN : ((nW K w : e7Data_valid.minGroup K) : (Module.End K (V K))ˣ) ∈ GG K)
    {π : Fin e7Data.d → Fin e7Data.d}
    (hπ : ∀ a, endoE (nW K w) (Finsupp.single a 1) = Finsupp.single (π a) 1) :
    ∀ a, pr (π a) theta = pr a theta := by
  intro a
  by_contra hne
  have hmem : endoE (nW K w) (Finsupp.single a 1) ∈ Piece K (pr a theta) :=
    hN.1 (pr a theta) _ (single_mem_Piece (K := K) a)
  rw [hπ a] at hmem
  have h0 := mem_Piece_iff.1 hmem (π a) hne
  rw [Finsupp.single_eq_same] at h0
  exact one_ne_zero h0

private theorem nW_shift_eq [CharP K 2] {w : W7 K}
    {δ δ' : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) (hδ'root : IsRoot .E7 δ')
    (hmap : (e7Data_valid.rootGroup K δ).map (MulAut.conj (nW K w)).toMonoidHom =
      e7Data_valid.rootGroup K δ')
    {π : Fin e7Data.d → Fin e7Data.d}
    (hπ : ∀ a, endoE (nW K w) (Finsupp.single a 1) = Finsupp.single (π a) 1)
    {a : Fin e7Data.d} (ha : pr a δ = -1) :
    pr (π a) δ' = -1 ∧ π (shift δ a) = shift δ' (π a) := by
  classical
  have hinv : ∀ a, endoE (nW K w)⁻¹ (Finsupp.single (π a) 1) = Finsupp.single a 1 := by
    intro a
    have h : endoE (nW K w)⁻¹ (endoE (nW K w) (Finsupp.single a 1)) =
        (Finsupp.single a 1 : V K) := by
      change e7Data_valid.endo K (nW K w)⁻¹
        (e7Data_valid.endo K (nW K w) (Finsupp.single a 1)) = _
      rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]
    rwa [hπ a] at h
  have hx : endoE (e7Data_valid.xm K δ 1) (Finsupp.single a 1) =
      Finsupp.single a 1 + Finsupp.single (shift δ a) 1 := by
    change ((e7Data_valid.xu K δ 1 : (Module.End K (V K))ˣ) : Module.End K (V K))
      (Finsupp.single a 1) = _
    rw [e7Data_valid.xu_apply, rootOp_single hδ a, if_pos ha, one_smul]
  have h1 : endoE (nW K w * e7Data_valid.xm K δ 1 * (nW K w)⁻¹)
      (Finsupp.single (π a) 1) =
      Finsupp.single (π a) 1 + Finsupp.single (π (shift δ a)) 1 := by
    change e7Data_valid.endo K (nW K w * e7Data_valid.xm K δ 1 * (nW K w)⁻¹)
      (Finsupp.single (π a) 1) = _
    rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, Module.End.mul_apply,
      Module.End.mul_apply]
    change e7Data_valid.endo K (nW K w)
      (e7Data_valid.endo K (e7Data_valid.xm K δ 1)
        (e7Data_valid.endo K (nW K w)⁻¹ (Finsupp.single (π a) 1))) = _
    rw [hinv a, hx, map_add, hπ a, hπ (shift δ a)]
  have hy : nW K w * e7Data_valid.xm K δ 1 * (nW K w)⁻¹ ∈
      e7Data_valid.rootGroup K δ' := by
    rw [← hmap]
    exact ⟨_, e7Data_valid.xm_mem_rootGroup K δ 1, rfl⟩
  obtain ⟨c, hc⟩ := (e7Data_valid.mem_rootGroup K).1 hy
  have h2 : endoE (e7Data_valid.xm K δ' c) (Finsupp.single (π a) 1) =
      Finsupp.single (π a) 1 + c • (if pr (π a) δ' = -1 then
        (Finsupp.single (shift δ' (π a)) 1 : V K) else 0) := by
    change ((e7Data_valid.xu K δ' c : (Module.End K (V K))ˣ) : Module.End K (V K))
      (Finsupp.single (π a) 1) = _
    rw [e7Data_valid.xu_apply, rootOp_single hδ'root (π a)]
  have hsingle : (Finsupp.single (π (shift δ a)) (1 : K) : V K) =
      c • (if pr (π a) δ' = -1 then (Finsupp.single (shift δ' (π a)) 1 : V K) else 0) := by
    have e1 := h1
    rw [← hc] at e1
    rw [e1] at h2
    exact add_left_cancel h2
  have hpr : pr (π a) δ' = -1 := by
    by_contra hpr
    have heval : (1 : K) = 0 := by
      have h := congrArg (fun v : V K => v (π (shift δ a))) hsingle
      simpa [hpr, Finsupp.smul_apply] using h
    exact one_ne_zero heval
  have hidx : π (shift δ a) = shift δ' (π a) := by
    by_contra hne
    have hne' : shift δ' (π a) ≠ π (shift δ a) := fun e => hne e.symm
    have heval : (1 : K) = 0 := by
      have h := congrArg (fun v : V K => v (π (shift δ a))) hsingle
      simpa [hpr, hne', Finsupp.smul_apply] using h
    exact one_ne_zero heval
  exact ⟨hpr, hidx⟩

theorem node1_weylAction_of_mem_GG [CharP K 2] {w : W7 K}
    (hN : ((nW K w : e7Data_valid.minGroup K) : (Module.End K (V K))ˣ) ∈ GG K)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) :
    weylAction (e7Datum K).isFiniteType w δ node1 = δ node1 := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : Fin e7Data.d → Fin e7Data.d, ∀ a,
      endoE (nW K w) (Finsupp.single a 1) = Finsupp.single (π a) 1 :=
    ⟨fun a => (endo_nW_single (K := K) w a).choose,
      fun a => (endo_nW_single (K := K) w a).choose_spec⟩
  have hdeg := nW_pr_theta_eq (π := π) hN hπ
  set δ' : Fin (Tag.rank .E7) → ℤ := weylAction (e7Datum K).isFiniteType w δ with hδ'def
  have hδR : δ ∈ (e7Datum K).roots :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hδ
  have hδ'root : IsRoot .E7 δ' := by
    rw [hδ'def]
    exact (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1
      (weylAction_mem_roots _ w hδR)
  have hmap : (e7Data_valid.rootGroup K δ).map (MulAut.conj (nW K w)).toMonoidHom =
      e7Data_valid.rootGroup K δ' := by
    rw [hδ'def]
    exact actsAs_nrep (e7Datum_isCTGroupDatum K) w δ hδR
  obtain ⟨a, ha⟩ : ∃ a : Fin e7Data.d, pr a δ = -1 := by
    have hcard : 0 < (Finset.univ.filter fun a : Fin e7Data.d => pr a δ = -1).card := by
      rw [(card_pr hδ).2.1]
      norm_num
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hcard
    exact ⟨a, (Finset.mem_filter.1 ha).2⟩
  obtain ⟨hpr, hidx⟩ := nW_shift_eq (π := π) hδ hδ'root hmap hπ ha
  have e1 : pr (shift δ a) theta = pr a theta + δ node1 := by
    rw [pr_shift hδ ha theta, pair_theta]
  have e2 : pr (shift δ' (π a)) theta = pr (π a) theta + δ' node1 := by
    rw [pr_shift hδ'root hpr theta, pair_theta]
  have hfinal : pr a theta + δ node1 = pr a theta + δ' node1 := by
    calc pr a theta + δ node1 = pr (shift δ a) theta := e1.symm
      _ = pr (π (shift δ a)) theta := (hdeg (shift δ a)).symm
      _ = pr (shift δ' (π a)) theta := by rw [hidx]
      _ = pr (π a) theta + δ' node1 := e2
      _ = pr a theta + δ' node1 := by rw [hdeg a]
  omega

theorem nW_mem_closure_of_preserves (J : Set (Fin (Tag.rank .E7))) {w : W7 K}
    (hw : ∀ δ, IsRoot .E7 δ → ∀ j ∈ J, weylAction (e7Datum K).isFiniteType w δ j = δ j) :
    nW K w ∈ Subgroup.closure (e7Data_valid.nm K '' {i | i ∉ J}) := by
  induction hl : (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.length w
    using Nat.strong_induction_on generalizing w with
  | _ m ih =>
  by_cases h1 : w = 1
  · subst h1
    rw [nW, nrep_one]
    exact one_mem _
  obtain ⟨i, hi⟩ :=
    (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.exists_leftDescent_of_ne_one h1
  have hiJ : i ∉ J := by
    intro hiJ
    have hR := (isRightDescent_iff (e7Datum K).isFiniteType w⁻¹ i).1
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.isRightDescent_inv_iff.2 hi)
    have hα : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ (e7Datum K).roots :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 (IsRoot.basis (τ := .E7) i)
    have hroot : IsRoot .E7 (weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single i 1)) :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 (weylAction_mem_roots _ w⁻¹ hα)
    have h : weylAction (e7Datum K).isFiniteType w
        (weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single i 1)) i =
          weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single i 1) i := hw _ hroot i hiJ
    rw [weylAction_apply_inv_apply, Pi.single_eq_same] at h
    have h2 : weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single i 1) i ≤ 0 := hR i
    omega
  have hw' : ∀ δ, IsRoot .E7 δ → ∀ j ∈ J, weylAction (e7Datum K).isFiniteType
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i * w) δ j = δ j := by
    intro δ hδ j hj
    have hji : j ≠ i := fun e => hiJ (e ▸ hj)
    rw [weylAction_mul_apply, weylAction_simple_apply_of_ne _ i _ hji]
    exact hw δ hδ j hj
  have hlen := (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.isLeftDescent_iff.1 hi
  have hmem := ih _ (by omega) hw' rfl
  have hnot : ¬ (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.IsLeftDescent
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i * w) i :=
    (CoxeterSystem.isLeftDescent_iff_not_isLeftDescent_mul _).1 hi
  have e : w = (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i *
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i * w) :=
    ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple_mul_simple_cancel_left i).symm
  rw [e, nW, nrep_simple_mul _ hnot]
  exact mul_mem (Subgroup.subset_closure ⟨i, hiJ, rfl⟩) hmem

end CFSG.RankThree.GF2n.Smith81.E7Model
