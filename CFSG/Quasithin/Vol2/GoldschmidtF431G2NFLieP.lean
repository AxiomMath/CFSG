module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2NFLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentC
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelRad
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Aut
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Cls
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2QOneAct

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.NFLie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.F431.NF
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.GH74.GLS.Stage4.Hex CFSG.Quasithin.H13.F431.BN
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem U_le_Pmin (i : Fin Tag.G2.rank) : U K ≤ Pmin K i := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _
    (Subgroup.mem_sup_right (mem_U_iff.1 hx)))

theorem nrC_mem_Pmin : nrC K ∈ Pmin K ⟨1, by decide⟩ :=
  Subgroup.mem_subgroupOf.2 (weylElt_mem_parabolicSubgroup (Set.mem_singleton _))

theorem naC_mem_Pmin : naC K ∈ Pmin K ⟨0, by decide⟩ :=
  Subgroup.mem_subgroupOf.2 (weylElt_mem_parabolicSubgroup (Set.mem_singleton _))

theorem Pmin_one_le_normalizer_Q1 [Finite K] (hK : 3 ≤ Nat.card K) :
    Pmin K ⟨1, by decide⟩ ≤ Subgroup.normalizer (Q1 K : Set (C K)) := by
  intro g hg
  have h1 : mk K g ∈ BN.P (g2ModelSystem K hK) true := by
    rw [BN.P_true, ← map_Pmin_one hK]
    exact ⟨g, hg, rfl⟩
  have h2 : mk K g ∈ Subgroup.normalizer (BN.Q (g2ModelSystem K hK) true : Set _) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ h1
  rw [Q_true_eq hK] at h2
  rw [Subgroup.mem_normalizer_iff] at h2 ⊢
  intro x
  have h3 := h2 (mk K x)
  have e : mk K g * mk K x * (mk K g)⁻¹ = mk K (g * x * g⁻¹) := by simp
  rw [e] at h3
  have hm : ∀ w : C K, mk K w ∈ (Q1 K).map (mk K).toMonoidHom ↔ w ∈ Q1 K := fun w => by
    rw [Subgroup.mem_map_equiv]
    simp
  rwa [hm, hm] at h3

theorem exists_torus_xc {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ d ∈ Pmin K ⟨1, by decide⟩, d * xc s * d⁻¹ = xc t := by
  have hu : t / s ≠ 0 := div_ne_zero ht hs
  refine ⟨⟨torusElt Tag.G2 K Cls.iA (Units.mk0 (t / s) hu),
    torusElt_mem_adjointGroup Cls.iA (Units.mk0 (t / s) hu)⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (torusGroup_le_parabolicSubgroup _
      (torusElt_mem_torusGroup _ _))
  · refine Subtype.ext ?_
    have h := Cls.torusElt_conj_pinnedX_c (K := K) (Units.mk0 (t / s) hu) s
    rw [Units.val_mk0, div_mul_cancel₀ _ hs] at h
    exact h

theorem aut_mem_of_stab [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {H : Subgroup (C K)} (hP : Pmin K ⟨1, by decide⟩ ≤ Subgroup.normalizer (H : Set (C K)))
    (hσ : ∀ σ : K ≃+* K, fieldAut K σ ∈ autStab H) {φ : MulAut (C K)}
    (hφ : φ ∈ autStab (Pmin K ⟨1, by decide⟩)) {x : C K} (hx : x ∈ H) : φ x ∈ H := by
  obtain ⟨g, hg, σ, rfl⟩ := exists_of_autStab_Pmin hf hK ⟨1, by decide⟩ hφ
  rw [MulAut.mul_apply, MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.1 (hP hg) _).1 ((hσ σ x).1 hx)

theorem aut_mem_Xc [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {φ : MulAut (C K)} (hφ : φ ∈ autStab (Pmin K ⟨1, by decide⟩)) {x : C K} (hx : x ∈ Xc K) :
    φ x ∈ Xc K :=
  aut_mem_of_stab hf hK Cent.Pr_le_normalizer_Xc (fun σ => fieldAut_mem_autStab_Xe σ rC) hφ hx

theorem aut_mem_Q1 [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {φ : MulAut (C K)} (hφ : φ ∈ autStab (Pmin K ⟨1, by decide⟩)) {x : C K} (hx : x ∈ Q1 K) :
    φ x ∈ Q1 K :=
  aut_mem_of_stab hf hK (Pmin_one_le_normalizer_Q1 (three_le_card_of_pow hf hK))
    (fun σ => fieldAut_mem_autStab_Q1 σ) hφ hx

theorem xu_one_ne_one : xu (1 : K) ≠ 1 := fun h => one_ne_zero (xu_eq_one_iff.mp h)

theorem isConj_z_of_mem_V {y : C K} (hV : y ∈ V K) (hy1 : y ≠ 1) : IsConj (xc 1) y := by
  obtain ⟨β, γ, rfl⟩ := mem_V_iff.1 hV
  by_cases hβ : β = 0
  · subst hβ
    have hγ : γ ≠ 0 := fun h => hy1 (by rw [h]; exact nf_one)
    rw [← xc_eq_nf]
    exact Cls.isConj_z_xc hγ
  · exact Cls.isConj_z_nf_V hβ

theorem exists_comm_not_mem_Xc [Finite K] (hK : 4 ≤ Nat.card K)
    (hnc : ¬ IsConj (xc (1 : K)) (xv 1)) {y : C K} (hyQ : y ∈ Q1 K)
    (hy : IsConj (xu (1 : K)) y) : ∃ s ∈ U K, ⁅s, y⁆ ∉ Xc K := by
  by_contra hcon
  push Not at hcon
  have hV : y ∈ V K := (Q1_centralizer_mod_Xc_iff (exists_ne_zero_one hK)).1 ⟨hyQ, hcon⟩
  have hy1 : y ≠ 1 := fun h => xu_one_ne_one (isConj_one_left.1 (h ▸ hy))
  exact hnc ((isConj_z_of_mem_V hV hy1).trans
    (hy.symm.trans (Cls.isConj_t_xu one_ne_zero).symm))

theorem four_le_card_of_pow {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem exists_comm_not_mem_Xc_aut [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hnc : ¬ IsConj (xc (1 : K)) (xv 1)) {φ : MulAut (C K)}
    (hφ : φ ∈ autStab (Pmin K ⟨1, by decide⟩)) : ∃ s ∈ U K, ⁅s, φ (xu 1)⁆ ∉ Xc K := by
  have h4 := four_le_card_of_pow hf hK
  obtain ⟨g, hg, σ, rfl⟩ := exists_of_autStab_Pmin hf hK ⟨1, by decide⟩ hφ
  have e : (MulAut.conj g * fieldAut K σ) (xu 1) = g * xu 1 * g⁻¹ := by
    rw [MulAut.mul_apply, fieldAut_xu_one, MulAut.conj_apply]
  rw [e]
  refine exists_comm_not_mem_Xc h4 hnc ?_ (isConj_iff.2 ⟨g, rfl⟩)
  exact (Subgroup.mem_normalizer_iff.1
    (Pmin_one_le_normalizer_Q1 (three_le_card_of_pow hf hK) hg) _).1 (xu_mem_Q1 1)

end CFSG.Quasithin.H13.F431.G2.NFLie
