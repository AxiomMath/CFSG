module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Reconstruction

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

universe u

/-! # Peterfalvi, Part II, Chapter IV, Section 1 Lemma, second assertion -/

private theorem generated_by_pointStabilizer_and_mover
    {L X : Type*} [Group L] [MulAction L X]
    (M : Subgroup L) (t : L) {a : X}
    (h2 : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht : t ∉ M) :
    Subgroup.closure ((M : Set L) ∪ ({t} : Set L)) = ⊤ := by
  classical
  let H : Subgroup L := Subgroup.closure ((M : Set L) ∪ ({t} : Set L))
  have hM_le_H : M ≤ H := by
    intro m hm
    exact Subgroup.subset_closure (Or.inl hm)
  have htH : t ∈ H := by
    exact Subgroup.subset_closure (Or.inr rfl)
  have ht_not_stabilizer : t ∉ MulAction.stabilizer L a := by
    intro htst
    exact ht (by
      rw [hM]
      exact htst)
  have hta_ne : t • a ≠ a := by
    intro hta
    exact ht_not_stabilizer ((MulAction.mem_stabilizer_iff).2 hta)
  let : MulAction.IsMultiplyPretransitive L X 2 := h2
  have : MulAction.IsPretransitive L X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hstab_one :
      MulAction.IsMultiplyPretransitive
        (MulAction.stabilizer L a) (SubMulAction.ofStabilizer L a) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := L) (α := X) (a := a) (n := 1)).mp h2
  have hstab_pre :
      MulAction.IsPretransitive
        (MulAction.stabilizer L a) (SubMulAction.ofStabilizer L a) :=
    (MulAction.is_one_pretransitive_iff
      (G := MulAction.stabilizer L a)
      (α := SubMulAction.ofStabilizer L a)).mp hstab_one
  have hH_base : ∀ x : X, ∃ h : H, h • a = x := by
    intro x
    by_cases hx : x = a
    · refine ⟨1, ?_⟩
      simp [hx]
    · obtain ⟨m, hm⟩ := hstab_pre.exists_smul_eq
        (⟨t • a, hta_ne⟩ : SubMulAction.ofStabilizer L a)
        (⟨x, hx⟩ : SubMulAction.ofStabilizer L a)
      have hmX : (m : L) • (t • a) = x := by
        have hm' := congrArg Subtype.val hm
        change (m : L) • (t • a) = x at hm'
        exact hm'
      have hmM : (m : L) ∈ M := by
        rw [hM]
        exact m.property
      refine ⟨⟨(m : L) * t, H.mul_mem (hM_le_H hmM) htH⟩, ?_⟩
      simpa [mul_smul] using hmX
  apply (Subgroup.eq_top_iff' H).2
  intro l
  obtain ⟨h, hh⟩ := hH_base (l • a)
  have hhL : (h : L) • a = l • a := by
    change (h : L) • a = l • a at hh
    exact hh
  have hfix : ((h : L)⁻¹ * l) ∈ MulAction.stabilizer L a := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      ((h : L)⁻¹ * l) • a = (h : L)⁻¹ • (l • a) := by
        rw [mul_smul]
      _ = (h : L)⁻¹ • ((h : L) • a) := by
        rw [← hhL]
      _ = a := by
        simp
  have hfixM : ((h : L)⁻¹ * l) ∈ M := by
    rw [hM]
    exact hfix
  have hprod : (h : L) * ((h : L)⁻¹ * l) ∈ H :=
    H.mul_mem h.property (hM_le_H hfixM)
  have hprod_eq : (h : L) * ((h : L)⁻¹ * l) = l := by
    simp
  rwa [hprod_eq] at hprod

private theorem lemma_b_compatible_copy_group_iso_obligation
    {L : Type u} {X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    [FaithfulSMul L X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hM : Q ≤ M ∧ D ≤ M ∧
      (∀ m q : L, m ∈ M → q ∈ Q → m * q * m⁻¹ ∈ Q) ∧
        Disjoint Q D ∧ Q ⊔ D = M)
    (hgenerated : Subgroup.closure ((M : Set L) ∪ ({t} : Set L)) = ⊤) :
    ∀ {L' : Type u} {X' : Type*}
      [Group L'] [Finite L'] [MulAction L' X'] [Finite X'] [FaithfulSMul L' X']
      (M' Q' D' : Subgroup L') (t' : L') (f' g' h' : L' → L'),
      MulAction.IsMultiplyPretransitive L' X' 2 →
        (∃ x' : X', M' = MulAction.stabilizer L' x') →
          IsInvolution t' → t' ∉ M' →
            D' = M' ⊓ rightConjugate M' t' →
              (Q'.subgroupOf M').Normal →
                Disjoint Q' D' → Q' ⊔ D' = M' →
                  (∀ x' : L', x' ∈ Q' → x' ≠ 1 → f' x' ∈ Q' ∧ f' x' ≠ 1) →
                    (∀ x' : L', x' ∈ Q' → x' ≠ 1 → g' x' ∈ Q' ∧ g' x' ≠ 1) →
                      (∀ x' : L', x' ∈ Q' → x' ≠ 1 → h' x' ∈ D') →
                        (∀ x' : L', x' ∈ Q' → x' ≠ 1 →
                          t' * x' * t' = g' x' * h' x' * t' * f' x') →
                          (hM' : Q' ≤ M' ∧ D' ≤ M' ∧
                            (∀ m q : L', m ∈ M' → q ∈ Q' → m * q * m⁻¹ ∈ Q') ∧
                              Disjoint Q' D' ∧ Q' ⊔ D' = M') →
                            (mIso : M ≃* M') → (qIso : Q ≃* Q') →
                              (∀ x : Q,
                                ((mIso ⟨x, hM.1 x.property⟩ : M') : L') =
                                  ((qIso x : Q') : L')) →
                                (D.subgroupOf M).map mIso.toMonoidHom =
                                    D'.subgroupOf M' →
                                  (∀ x : L, ∀ hx : x ∈ Q, ∀ hx1 : x ≠ 1,
                                    ((qIso ⟨f x, (hf_mem x hx hx1).1⟩ : Q') : L') =
                                      f' ((qIso ⟨x, hx⟩ : Q') : L')) →
                                    Nonempty (L ≃* L') := by
  intro L' X' _ _ _ _ _ M' Q' D' t' f' g' h' htwo_transitive'
    hpoint_stabilizer' ht_involution' ht_not_mem_M' hD_eq' hQ_normal_in_M'
    hQ_disjoint_D' hQ_sup_D' hf_mem' hg_mem' hh_mem' hcanonical_eq' hM' mIso
    qIso hQ_compat hD_compat hf_compat
  obtain ⟨a, hMstab⟩ := hpoint_stabilizer
  obtain ⟨a', hMstab'⟩ := hpoint_stabilizer'
  obtain ⟨e, he_base, he_Q, he_t⟩ :=
    exists_rankOnePointEquiv M Q D t f g h a M' Q' D' t' f' g' h' a'
      htwo_transitive hMstab ht_involution ht_not_mem_M hD_eq hQ_normal_in_M
      hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      htwo_transitive' hMstab' ht_involution' ht_not_mem_M' hD_eq'
      hQ_normal_in_M' hQ_disjoint_D' hQ_sup_D' hf_mem' hg_mem' hh_mem'
      hcanonical_eq' qIso hf_compat
  have he_M : ∀ m : M,
      IsActionTransport e (m : L) ((mIso m : M') : L') :=
    rankOnePointEquiv_transport_M M Q D t a M' Q' D' t' a'
      htwo_transitive hMstab ht_involution ht_not_mem_M hD_eq hQ_normal_in_M
      hQ_disjoint_D hQ_sup_D htwo_transitive' hMstab' ht_involution'
      ht_not_mem_M' hD_eq' hQ_normal_in_M' hQ_disjoint_D' hQ_sup_D'
      mIso qIso hQ_compat hD_compat e he_base he_Q he_t
  obtain ⟨E, _hE_M, _hE_t⟩ :=
    rankOneGeneratedSubgroup_equiv M t M' t' mIso e he_M he_t
  have hgenerated' :
      Subgroup.closure ((M' : Set L') ∪ ({t'} : Set L')) = ⊤ :=
    generated_by_pointStabilizer_and_mover M' t' htwo_transitive' hMstab'
      ht_not_mem_M'
  exact ⟨
    (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).symm |>.trans
      (MulEquiv.subgroupCongr hgenerated.symm) |>.trans E |>.trans
      (MulEquiv.subgroupCongr hgenerated') |>.trans
      (Subgroup.topEquiv : (⊤ : Subgroup L') ≃* L')⟩

public theorem lemma_b
    {L : Type u} {X : Type*}
    [Group L] [Finite L] [MulAction L X] [Finite X] [FaithfulSMul L X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ {L' : Type u} {X' : Type*}
            [Group L'] [Finite L'] [MulAction L' X'] [Finite X'] [FaithfulSMul L' X']
            (M' Q' D' : Subgroup L') (t' : L') (f' g' h' : L' → L'),
            MulAction.IsMultiplyPretransitive L' X' 2 →
              (∃ x' : X', M' = MulAction.stabilizer L' x') →
                IsInvolution t' → t' ∉ M' →
                  D' = M' ⊓ rightConjugate M' t' →
                    (Q'.subgroupOf M').Normal →
                      Disjoint Q' D' → Q' ⊔ D' = M' →
                        (∀ x' : L', x' ∈ Q' → x' ≠ 1 → f' x' ∈ Q' ∧ f' x' ≠ 1) →
                          (∀ x' : L', x' ∈ Q' → x' ≠ 1 → g' x' ∈ Q' ∧ g' x' ≠ 1) →
                            (∀ x' : L', x' ∈ Q' → x' ≠ 1 → h' x' ∈ D') →
                              (∀ x' : L', x' ∈ Q' → x' ≠ 1 →
                                t' * x' * t' = g' x' * h' x' * t' * f' x') →
                                (mIso : M ≃* M') → (qIso : Q ≃* Q') →
                                    (∀ x : Q,
                                      ((mIso ⟨x, (rankOneSplit_Q_le_M hQ_sup_D) x.property⟩ : M') : L') =
                                        ((qIso x : Q') : L')) →
                                      (D.subgroupOf M).map mIso.toMonoidHom =
                                          D'.subgroupOf M' →
                                        (∀ x : L, ∀ hx : x ∈ Q, ∀ hx1 : x ≠ 1,
                                          ((qIso ⟨f x, (hf_mem x hx hx1).1⟩ : Q') : L') =
                                            f' ((qIso ⟨x, hx⟩ : Q') : L')) →
                                          Nonempty (L ≃* L') := by
  have hM : Q ≤ M ∧ D ≤ M ∧
      (∀ m q : L, m ∈ M → q ∈ Q → m * q * m⁻¹ ∈ Q) ∧
        Disjoint Q D ∧ Q ⊔ D = M :=
    rankOneSplit_QD_decomposition hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D
  have hgenerated : Subgroup.closure ((M : Set L) ∪ ({t} : Set L)) = ⊤ := by
    obtain ⟨a, hMstab⟩ := hpoint_stabilizer
    exact generated_by_pointStabilizer_and_mover M t
      htwo_transitive hMstab ht_not_mem_M
  intro L' X' _ _ _ _ _ M' Q' D' t' f' g' h' htwo_transitive'
    hpoint_stabilizer' ht_involution' ht_not_mem_M' hD_eq' hQ_normal_in_M'
    hQ_disjoint_D' hQ_sup_D' hf_mem' hg_mem' hh_mem' hcanonical_eq'
  have hM' : Q' ≤ M' ∧ D' ≤ M' ∧
      (∀ m q : L', m ∈ M' → q ∈ Q' → m * q * m⁻¹ ∈ Q') ∧
        Disjoint Q' D' ∧ Q' ⊔ D' = M' :=
    rankOneSplit_QD_decomposition hD_eq' hQ_normal_in_M' hQ_disjoint_D' hQ_sup_D'
  exact
    lemma_b_compatible_copy_group_iso_obligation M Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq
      hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      hM hgenerated M' Q' D' t' f' g' h' htwo_transitive' hpoint_stabilizer'
      ht_involution' ht_not_mem_M' hD_eq' hQ_normal_in_M' hQ_disjoint_D'
      hQ_sup_D' hf_mem' hg_mem' hh_mem' hcanonical_eq' hM'
end PFchapter4section1
end CFSG.BenderSuzuki
