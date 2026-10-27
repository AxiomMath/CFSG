module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG.ABGLocalTools
open scoped IsMulCommutative

theorem exists_chiefRep {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {N M : Subgroup X} (hN : N.Normal) (hM : M.Normal) (hNM : N < M)
    (hmin : ∀ K : Subgroup X, K.Normal → N ≤ K → K ≤ M → K = N ∨ K = M)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N) :
    ∃ (F : Type) (_ : AddCommGroup F) (_ : Module (ZMod p) F) (_ : Module.Finite (ZMod p) F)
      (ρ : Representation (ZMod p) X F) (q : X → F),
      ρ.IsIrreducible ∧ (∀ f : F, ∃ m ∈ M, q m = f) ∧
      (∀ m ∈ M, ∀ m' ∈ M, q (m * m') = q m + q m') ∧ (∀ m ∈ M, q m = 0 ↔ m ∈ N) ∧
      ∀ x : X, ∀ m ∈ M, ρ x (q m) = q (x * m * x⁻¹) := by
  classical
  haveI hNnormal : N.Normal := hN
  haveI hMnormal : M.Normal := hM
  have hNMle : N ≤ M := hNM.le
  haveI hNsub : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNMle).mpr Subgroup.le_normalizer_of_normal
  have hchief : IsChiefFactorUnder p ⊤ M N :=
    ⟨hNM, (Subgroup.normalizer_eq_top (H := M)).ge, (Subgroup.normalizer_eq_top (H := N)).ge,
      (fun x _ y hy => hN.conj_mem y hy x),
      (fun x hx y hy => hab x hx y hy), (fun x hx => hexp x hx),
      (fun K hNK hKM hKNorm =>
        hmin K (Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top hKNorm)) hNK hKM)⟩
  haveI hEA : IsElementaryAbelian p (M ⧸ N.subgroupOf M) := hchief.isElementaryAbelian
  let F := Additive (M ⧸ N.subgroupOf M)
  haveI hFin : Finite F := inferInstance
  haveI hModFin : Module.Finite (ZMod p) F := Module.Finite.of_finite
  let ρ₀ := chiefRep (p := p) hchief.2.1 hchief.2.2.1
  let ρ : Representation (ZMod p) X F :=
    (Units.coeHom (Module.End (ZMod p) F)).comp
      (ρ₀.comp (Subgroup.topEquiv.symm : X ≃* (⊤ : Subgroup X)).toMonoidHom)
  let q : X → F := fun y =>
    if hy : y ∈ M then Additive.ofMul ((⟨y, hy⟩ : M) : M ⧸ N.subgroupOf M) else 0
  have hq_mem : ∀ (y : X) (hy : y ∈ M),
      q y = Additive.ofMul ((⟨y, hy⟩ : M) : M ⧸ N.subgroupOf M) := by
    intro y hy
    dsimp only [q]
    rw [dif_pos hy]
  haveI hFnt : Nontrivial F := by
    obtain ⟨m, hmM, hmN⟩ := IsConcreteLE.exists_of_lt hNM
    refine ⟨0, Additive.ofMul ((⟨m, hmM⟩ : M) : M ⧸ N.subgroupOf M), ?_⟩
    intro hzero
    have hzero' : Additive.ofMul ((⟨m, hmM⟩ : M) : M ⧸ N.subgroupOf M) = 0 := hzero.symm
    rw [ofMul_eq_zero] at hzero'
    exact hmN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hzero'))
  have hρtop : ∀ n : (⊤ : Subgroup X),
      ρ (Subgroup.topEquiv n) = (Units.coeHom (Module.End (ZMod p) F)) (ρ₀ n) := by
    intro n
    change (Units.coeHom (Module.End (ZMod p) F))
        (ρ₀ (Subgroup.topEquiv.symm (Subgroup.topEquiv n))) =
      (Units.coeHom (Module.End (ZMod p) F)) (ρ₀ n)
    have h : Subgroup.topEquiv.symm (Subgroup.topEquiv n) = n := by
      apply Subtype.ext
      rw [Subgroup.topEquiv_symm_apply_coe, Subgroup.topEquiv_apply]
    rw [h]
  have hirr : ρ.IsIrreducible := by
    refine { eq_bot_or_eq_top := fun U => ?_ }
    have hU : ∀ n : (⊤ : Subgroup X), ∀ v ∈ U.toSubmodule,
        ((ρ₀ n : LinearMap.GeneralLinearGroup (ZMod p) F) : F →ₗ[ZMod p] F) v ∈
          U.toSubmodule := by
      intro n v hv
      have h1 := U.apply_mem_toSubmodule (Subgroup.topEquiv n) hv
      rwa [hρtop n] at h1
    rcases chiefRep_irreducible hchief U.toSubmodule hU with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  have hq_add : ∀ m ∈ M, ∀ m' ∈ M, q (m * m') = q m + q m' := by
    intro m hm m' hm'
    rw [hq_mem _ (M.mul_mem hm hm'), hq_mem m hm, hq_mem m' hm']
    rfl
  have hq_ker : ∀ m ∈ M, q m = 0 ↔ m ∈ N := by
    intro m hm
    rw [hq_mem m hm, ofMul_eq_zero, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hρapply : ∀ (y : X) (w : M),
      ρ y (Additive.ofMul ((w : M) : M ⧸ N.subgroupOf M)) =
        Additive.ofMul ((⟨y * (w : X) * y⁻¹, hM.conj_mem (w : X) w.2 y⟩ : M) :
          M ⧸ N.subgroupOf M) := by
    intro y w
    change ((chiefRep (p := p) hchief.2.1 hchief.2.2.1 (Subgroup.topEquiv.symm y) :
      LinearMap.GeneralLinearGroup (ZMod p) F) : F →ₗ[ZMod p] F)
        (Additive.ofMul ((w : M) : M ⧸ N.subgroupOf M)) = _
    rw [chiefRep_apply_mk]
    congr 1
  refine ⟨F, inferInstance, inferInstance, hModFin, ρ, q, hirr, ?_, hq_add, hq_ker, ?_⟩
  · intro f
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul f)
    exact ⟨w, w.2, by rw [hq_mem w w.2]; simpa using congrArg Additive.ofMul hw⟩
  · intro y m hm
    rw [hq_mem m hm, hq_mem (y * m * y⁻¹) (hM.conj_mem m hm y)]
    exact hρapply y ⟨m, hm⟩

theorem rho_apply_eq_iff {X : Type} [Group X] {N M : Subgroup X} {p : ℕ}
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] (ρ : Representation (ZMod p) X F)
    (q : X → F) (hq : ∀ m ∈ M, ∀ m' ∈ M, q (m * m') = q m + q m')
    (hq0 : ∀ m ∈ M, q m = 0 ↔ m ∈ N) (hρ : ∀ x : X, ∀ m ∈ M, ρ x (q m) = q (x * m * x⁻¹))
    (hMn : M.Normal) {m : X} (hm : m ∈ M) (x : X) :
    ρ x (q m) = q m ↔ m * x * m⁻¹ * x⁻¹ ∈ N := by
  have hq1 : q 1 = 0 := by
    have h := hq 1 M.one_mem 1 M.one_mem
    rw [mul_one] at h
    have h1 : q 1 + q 1 = 0 + q 1 := by rw [zero_add]; exact h.symm
    exact add_right_cancel h1
  have hqinv : ∀ m ∈ M, q m⁻¹ = -q m := by
    intro m hm
    have h := hq m hm m⁻¹ (M.inv_mem hm)
    rw [mul_inv_cancel, hq1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  constructor
  · intro h
    have hu : x * m * x⁻¹ ∈ M := hMn.conj_mem m hm x
    have h1 : q (x * m * x⁻¹) = q m := by rw [← hρ x m hm]; exact h
    have h2 : q (x * m * x⁻¹ * m⁻¹) = q (x * m * x⁻¹) + q m⁻¹ :=
      hq (x * m * x⁻¹) hu m⁻¹ (M.inv_mem hm)
    rw [h1, hqinv m hm, add_neg_cancel] at h2
    have h3 : x * m * x⁻¹ * m⁻¹ ∈ N :=
      (hq0 (x * m * x⁻¹ * m⁻¹) (M.mul_mem hu (M.inv_mem hm))).mp h2
    have h4 := N.inv_mem h3
    rwa [show (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ by group] at h4
  · intro h
    have hu : x * m * x⁻¹ ∈ M := hMn.conj_mem m hm x
    have h1 : x * m * x⁻¹ * m⁻¹ ∈ N := by
      have h' := N.inv_mem h
      rwa [show (m * x * m⁻¹ * x⁻¹)⁻¹ = x * m * x⁻¹ * m⁻¹ by group] at h'
    have h2 : q (x * m * x⁻¹ * m⁻¹) = 0 :=
      (hq0 (x * m * x⁻¹ * m⁻¹) (M.mul_mem hu (M.inv_mem hm))).mpr h1
    have h3 := hq (x * m * x⁻¹) hu m⁻¹ (M.inv_mem hm)
    rw [h2, hqinv m hm] at h3
    have h4 : q (x * m * x⁻¹) = q m := by
      have h5 : q (x * m * x⁻¹) + (-q m) = q m + (-q m) := by
        rw [h3.symm, add_neg_cancel]
      exact add_right_cancel h5
    rw [hρ x m hm, h4]

end CFSG.RankThree.PartTwo.Sec16.Kcd166