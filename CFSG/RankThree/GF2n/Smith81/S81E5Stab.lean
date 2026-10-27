module

public import CFSG.RankThree.GF2n.Smith81.S81E5Rad
public import CFSG.RankThree.GF2n.Smith81.S81ZStab

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

variable {K : Type} [Field K]

private theorem chk_node7 : ∀ l ∈ Tag.E7.artifactRoots,
    l.getD 6 0 = -1 ∨ l.getD 6 0 = 0 ∨ l.getD 6 0 = 1 := by
  decide +kernel

theorem node7_mem {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    γ node7 = -1 ∨ γ node7 = 0 ∨ γ node7 = 1 := by
  have h := chk_node7 _ (isRoot_iff_mem_artifactRoots.1 hγ)
  rwa [getD_ofFn_six] at h

theorem forall_endo_w0_iff [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) :
    (∀ x ∈ e7Data_valid.rootGroup K δ, endoE x w0 = w0) ↔ δ node7 ≠ -1 := by
  have hpr : pr ⟨0, by decide⟩ δ = δ node7 := pr_topIdx δ
  constructor
  · intro h hδ7
    have h1 := h _ (e7Data_valid.xm_mem_rootGroup K δ 1)
    change ((e7Data_valid.xu K δ 1 : (Module.End K (V K))ˣ) : Module.End K (V K)) w0 = w0 at h1
    rw [e7Data_valid.xu_apply, one_smul, add_eq_left] at h1
    exact (e7Data_valid.rootOp_single_ne_zero_iff cartan_symm_E7 hδ ⟨0, by decide⟩).2
      (hpr.trans hδ7) h1
  · intro hδ7 x hx
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hx
    change ((e7Data_valid.xu K δ c : (Module.End K (V K))ˣ) : Module.End K (V K)) w0 = w0
    have h2 := rootOp_single (K := K) hδ ⟨0, by decide⟩
    rw [if_neg (fun h => hδ7 (hpr.symm.trans h))] at h2
    rw [e7Data_valid.xu_apply, h2, smul_zero, add_zero]

theorem endo_inv_w0 {n : e7Data_valid.minGroup K} {c : K} (hc : endoE n w0 = c • w0) :
    c ≠ 0 ∧ endoE n⁻¹ w0 = c⁻¹ • w0 := by
  have hinv : ∀ v, endoE n⁻¹ (endoE n v) = v := fun v => by
    change e7Data_valid.endo K n⁻¹ (e7Data_valid.endo K n v) = v
    rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have h := hinv w0
    rw [hc, map_zero] at h
    exact one_ne_zero (Finsupp.single_eq_zero.1 h.symm)
  refine ⟨hc0, ?_⟩
  have h := hinv w0
  rw [hc, map_smul] at h
  calc endoE n⁻¹ w0 = c⁻¹ • (c • endoE n⁻¹ w0) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • w0 := by rw [h]

theorem node7_weylAction_of_actsAs [CharP K 2] {n : e7Data_valid.minGroup K} {w : W7 K}
    (hn : ActsAs (e7Datum K) n w) {c : K} (hc : endoE n w0 = c • w0)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) :
    weylAction (e7Datum K).isFiniteType w δ node7 = δ node7 := by
  obtain ⟨hc0, hci⟩ := endo_inv_w0 hc
  have key : ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ →
      (δ node7 ≠ -1 ↔ weylAction (e7Datum K).isFiniteType w δ node7 ≠ -1) := by
    intro δ hδ
    have hδR : δ ∈ (e7Datum K).roots :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hδ
    have hδ' : IsRoot .E7 (weylAction (e7Datum K).isFiniteType w δ) :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1
        (weylAction_mem_roots _ w hδR)
    rw [← forall_endo_w0_iff (K := K) hδ, ← forall_endo_w0_iff (K := K) hδ']
    have hmap : (e7Data_valid.rootGroup K δ).map (MulAut.conj n).toMonoidHom =
        e7Data_valid.rootGroup K (weylAction (e7Datum K).isFiniteType w δ) := hn δ hδR
    constructor
    · intro h y hy
      rw [← hmap] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx0 := h x hx
      change e7Data_valid.endo K (n * x * n⁻¹) w0 = w0
      rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, Module.End.mul_apply,
        Module.End.mul_apply]
      change endoE n (endoE x (endoE n⁻¹ w0)) = w0
      rw [hci, map_smul, hx0, map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · intro h x hx
      have hy : n * x * n⁻¹ ∈ e7Data_valid.rootGroup K
          (weylAction (e7Datum K).isFiniteType w δ) := by
        rw [← hmap]
        exact ⟨x, hx, rfl⟩
      have h1 := h _ hy
      change e7Data_valid.endo K (n * x * n⁻¹) w0 = w0 at h1
      rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, Module.End.mul_apply,
        Module.End.mul_apply] at h1
      change endoE n (endoE x (endoE n⁻¹ w0)) = w0 at h1
      rw [hci, map_smul] at h1
      have h2 := congrArg (endoE n⁻¹) h1
      have hinv : ∀ v, endoE n⁻¹ (endoE n v) = v := fun v => by
        change e7Data_valid.endo K n⁻¹ (e7Data_valid.endo K n v) = v
        rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]
      rw [hinv, hci] at h2
      exact smul_right_injective _ (inv_ne_zero hc0) h2
  have h1 := key δ hδ
  have h2 := key (-δ) (CFSG.LieType.Chevalley.IsRoot.neg hδ)
  rw [map_neg, Pi.neg_apply, Pi.neg_apply] at h2
  have hδ' : IsRoot .E7 (weylAction (e7Datum K).isFiniteType w δ) :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1
      (weylAction_mem_roots _ w ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hδ))
  rcases node7_mem hδ with h | h | h <;> rcases node7_mem hδ' with h' | h' | h' <;> omega

theorem endo_nW_w0_of_stab [CharP K 2] {w : W7 K} {b₁ b₂ : e7Data_valid.minGroup K}
    (hb₁ : b₁ ∈ Bor K) (hb₂ : b₂ ∈ Bor K) {c : K} (hg : endoE (b₁ * nW K w * b₂) w0 = c • w0) :
    ∃ c' : K, endoE (nW K w) w0 = c' • w0 := by
  obtain ⟨c₁, hc₁⟩ := endo_bor_w0 (inv_mem hb₁)
  obtain ⟨c₂, hc₂⟩ := endo_bor_w0 (inv_mem hb₂)
  refine ⟨c₁ * (c * c₂), ?_⟩
  have e : nW K w = b₁⁻¹ * (b₁ * nW K w * b₂) * b₂⁻¹ := by group
  rw [e]
  change e7Data_valid.endo K (b₁⁻¹ * (b₁ * nW K w * b₂) * b₂⁻¹) w0 = _
  rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, Module.End.mul_apply, Module.End.mul_apply]
  change endoE b₁⁻¹ (endoE (b₁ * nW K w * b₂) (endoE b₂⁻¹ w0)) = _
  rw [hc₂, map_smul, hg, map_smul, map_smul, hc₁, smul_smul, smul_smul]
  ring_nf

@[expose] def p7Gen (K : Type) [Field K] : Subgroup (e7Data_valid.minGroup K) :=
  (⨆ γ ∈ {γ : Fin (Tag.rank .E7) → ℤ | IsRoot .E7 γ ∧ γ node7 ≠ -1},
    e7Data_valid.rootGroup K γ) ⊔ e7Data_valid.torus K node7

theorem rootGroup_le_p7Gen {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h7 : γ node7 ≠ -1) :
    e7Data_valid.rootGroup K γ ≤ p7Gen K :=
  le_trans (le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin (Tag.rank .E7) → ℤ |
    IsRoot .E7 γ ∧ γ node7 ≠ -1}) => e7Data_valid.rootGroup K γ) γ ⟨hγ, h7⟩ le_rfl) le_sup_left

theorem nt_mem_p7Gen {i : Fin (Tag.rank .E7)} (hi : i ≠ node7) (t : Kˣ) :
    e7Data_valid.nt K i t ∈ p7Gen K := by
  have h0 : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) node7 = 0 := by
    simp [Pi.single_apply, Ne.symm hi]
  have hr : IsRoot .E7 (Pi.single i 1) := IsRoot.basis i
  have h1 : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) node7 ≠ -1 := by rw [h0]; decide
  have h2 : (-Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) node7 ≠ -1 := by
    rw [Pi.neg_apply, h0]; decide
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact rootGroup_le_p7Gen hr h1 (e7Data_valid.xm_mem_rootGroup K _ _)
  · exact rootGroup_le_p7Gen (CFSG.LieType.Chevalley.IsRoot.neg hr) h2
      (e7Data_valid.xm_mem_rootGroup K _ _)
  · exact rootGroup_le_p7Gen hr h1 (e7Data_valid.xm_mem_rootGroup K _ _)

theorem torus_le_p7Gen (i : Fin (Tag.rank .E7)) : e7Data_valid.torus K i ≤ p7Gen K := by
  intro x hx
  obtain ⟨t, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
  by_cases hi : i = node7
  · subst hi
    exact le_sup_right (a := ⨆ γ ∈ {γ : Fin (Tag.rank .E7) → ℤ | IsRoot .E7 γ ∧ γ node7 ≠ -1},
      e7Data_valid.rootGroup K γ) (e7Data_valid.hm_mem_torus K _ t)
  · exact mul_mem (nt_mem_p7Gen hi t) (inv_mem (nt_mem_p7Gen hi 1))

theorem bor_le_p7Gen : Bor K ≤ p7Gen K := by
  refine sup_le (iSup_le fun i => torus_le_p7Gen i) (iSup₂_le fun γ hγ => ?_)
  have hγr : IsRoot .E7 γ := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 hγ.1
  refine rootGroup_le_p7Gen hγr ?_
  rw [← pr_topIdx γ]
  exact pr_zero_ne_neg_one_of_pos hγr hγ.2

theorem nW_mem_p7Gen {w : W7 K}
    (hw : ∀ δ, IsRoot .E7 δ → weylAction (e7Datum K).isFiniteType w δ node7 = δ node7) :
    nW K w ∈ p7Gen K := by
  induction hl : (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.length w
    using Nat.strong_induction_on generalizing w with
  | _ m ih =>
  by_cases h1 : w = 1
  · subst h1
    rw [nW, nrep_one]
    exact one_mem _
  obtain ⟨i, hi⟩ :=
    (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.exists_leftDescent_of_ne_one h1
  have hi7 : i ≠ node7 := by
    rintro rfl
    have hR := (isRightDescent_iff (e7Datum K).isFiniteType w⁻¹ node7).1
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.isRightDescent_inv_iff.2 hi)
    have hα : (Pi.single node7 1 : Fin (Tag.rank .E7) → ℤ) ∈ (e7Datum K).roots :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 (IsRoot.basis node7)
    have hroot : IsRoot .E7 (weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single node7 1)) :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 (weylAction_mem_roots _ w⁻¹ hα)
    have h : weylAction (e7Datum K).isFiniteType w
        (weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single node7 1)) node7 =
          weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single node7 1) node7 := hw _ hroot
    rw [weylAction_apply_inv_apply, Pi.single_eq_same] at h
    have h2 : weylAction (e7Datum K).isFiniteType w⁻¹ (Pi.single node7 1) node7 ≤ 0 := hR node7
    omega
  have hw' : ∀ δ, IsRoot .E7 δ → weylAction (e7Datum K).isFiniteType
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i * w) δ node7 =
        δ node7 := by
    intro δ hδ
    rw [weylAction_mul_apply, weylAction_simple_apply_of_ne _ i _ (Ne.symm hi7)]
    exact hw δ hδ
  have hlen := (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.isLeftDescent_iff.1 hi
  have hmem := ih _ (by omega) hw' rfl
  have hnot : ¬ (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.IsLeftDescent
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i * w) i :=
    (CoxeterSystem.isLeftDescent_iff_not_isLeftDescent_mul _).1 hi
  have e : w = (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i *
      ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple i * w) :=
    ((coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.simple_mul_simple_cancel_left i).symm
  rw [e, nW, nrep_simple_mul _ hnot]
  exact mul_mem (nt_mem_p7Gen hi7 1) hmem

theorem mem_p7Gen_of_stab [CharP K 2] {g : e7Data_valid.minGroup K} {c : K}
    (hg : endoE g w0 = c • w0) : g ∈ p7Gen K := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := bruhat_decomp g
  obtain ⟨c', hn⟩ := endo_nW_w0_of_stab hb₁ hb₂ hg
  exact mul_mem (mul_mem (bor_le_p7Gen hb₁) (nW_mem_p7Gen fun δ hδ =>
    node7_weylAction_of_actsAs (actsAs_nrep (e7Datum_isCTGroupDatum K) w) hn hδ))
    (bor_le_p7Gen hb₂)

end CFSG.RankThree.GF2n.Smith81.E7Model

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.E7Model

theorem charTwo_map_eq_one_of_mul_self {K : Type} [Field K] [CharP K 2] {G : Type} [Group G]
    (χ : G →* Kˣ) {g : G} (hg : g * g = 1) : χ g = 1 := by
  refine Units.ext (CharTwo.sq_inj.1 ?_)
  rw [Units.val_one, one_pow, sq, ← Units.val_mul, ← map_mul, hg, map_one, Units.val_one]

theorem e5StabChar_holds (K : Type) [Field K] [CharP K 2] : E5StabChar K := by
  intro χ hχ
  let H : Subgroup (StabW0 K) :=
    { carrier := {g | ((g : EAut K) : V K ≃ₗ[K] V K) (w0 : V K) = ((χ g : Kˣ) : K) • (w0 : V K)}
      mul_mem' := fun {g h} hg hh => by
        change ((g : EAut K) : V K ≃ₗ[K] V K) (((h : EAut K) : V K ≃ₗ[K] V K) (w0 : V K)) = _
        rw [hh, map_smul, hg, smul_smul, map_mul, Units.val_mul, mul_comm]
      one_mem' := by
        change (w0 : V K) = ((χ 1 : Kˣ) : K) • (w0 : V K)
        rw [map_one, Units.val_one, one_smul]
      inv_mem' := fun {g} hg => by
        change (((g : EAut K) : V K ≃ₗ[K] V K)⁻¹) (w0 : V K) = ((χ g⁻¹ : Kˣ) : K) • (w0 : V K)
        apply ((g : EAut K) : V K ≃ₗ[K] V K).injective
        rw [map_smul, hg, smul_smul, map_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
        exact LinearEquiv.apply_symm_apply _ _ }
  let ι : e7Data_valid.minGroup K →* EAut K := (vAut K).toMonoidHom.subgroupMap (EGrp K)
  have key : p7Gen K ≤ (H.map (StabW0 K).subtype).comap ι := by
    refine sup_le (iSup₂_le fun γ hγ x hx => ?_) (fun x hx => ?_)
    · obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hx
      have hfix : ((ι (e7Data_valid.xm K γ c) : EAut K) : V K ≃ₗ[K] V K) (w0 : V K) = w0 :=
        (forall_endo_w0_iff hγ.1).2 hγ.2 _ (e7Data_valid.xm_mem_rootGroup K γ c)
      have hS : ι (e7Data_valid.xm K γ c) ∈ StabW0 K := ⟨1, one_ne_zero, by rw [hfix, one_smul]⟩
      have hsq : (⟨_, hS⟩ : StabW0 K) * ⟨_, hS⟩ = 1 := by
        apply Subtype.ext
        change ι (e7Data_valid.xm K γ c) * ι (e7Data_valid.xm K γ c) = 1
        rw [← map_mul, ← e7Data_valid.xm_add, CharTwo.add_self_eq_zero, e7Data_valid.xm_zero,
          map_one]
      refine ⟨⟨_, hS⟩, ?_, rfl⟩
      change _ = _
      rw [charTwo_map_eq_one_of_mul_self χ hsq, Units.val_one, one_smul]
      exact hfix
    · obtain ⟨t, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
      refine ⟨d7 K t, ?_, rfl⟩
      change _ = _
      rw [hχ t]
      exact d7_apply_w0 t
  intro g
  obtain ⟨⟨_, g₀, hg₀, rfl⟩, c, hc0, hc⟩ := g
  have hmem := key (mem_p7Gen_of_stab (g := ⟨g₀, hg₀⟩) (c := c) hc)
  obtain ⟨y, hy, hyg⟩ := hmem
  have e : y = ⟨⟨_, g₀, hg₀, rfl⟩, c, hc0, hc⟩ := Subtype.ext hyg
  rw [← e]
  exact hy

end CFSG.RankThree.GF2n.Smith81.S81Z
