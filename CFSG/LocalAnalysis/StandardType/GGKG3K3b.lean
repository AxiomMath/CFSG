module

public import CFSG.LocalAnalysis.StandardType.GGKG3Coord
public import CFSG.LocalAnalysis.StandardType.GGKG3Cent
public import CFSG.LocalAnalysis.StandardType.GGKG3ZE
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem kg3_commutator_self_le_self {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem k3b
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup .E6 L 7) (hS : IsK3Setup S)
    (g : S.Γ) (hg : g ∈ Subgroup.normalizer ((S.E.subgroupOf S.Γ : Subgroup S.Γ) : Set S.Γ)) :
    ∃ c : WeylGroup .E6, c * w3 = w3 * c ∧ ∀ x ∈ S.E,
      (g : ModGL .E6 L) * x * (g : ModGL .E6 L)⁻¹ =
        canonicalRep (coxeterSystem .E6) L c * x * (canonicalRep (coxeterSystem .E6) L c)⁻¹ := by
  have h2 : ((2 : ℕ) : L) = 0 := by
    simpa [hS.q_eq] using S.hqpow.2
  obtain ⟨ζ, hζ⟩ := k3_exists_zeta h2
  have h7 : ζ ^ 7 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hVH : (S.E : Set (ModGL .E6 L)) ⊆ torusGroup .E6 L := by
    intro x hx
    exact (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 (S.E_le hx).1).1
  have hTcomm : ∀ a ∈ torusGroup .E6 L, ∀ b ∈ torusGroup .E6 L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
    obtain ⟨b', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hb
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hgN : (g : ModGL .E6 L) ∈ Subgroup.normalizer (S.E : Set (ModGL .E6 L)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxΓ : (⟨x, (S.E_le hx).2⟩ : S.Γ) ∈ S.E.subgroupOf S.Γ :=
        Subgroup.mem_subgroupOf.2 hx
      exact Subgroup.mem_subgroupOf.1
        ((Subgroup.mem_normalizer_iff.1 hg ⟨x, (S.E_le hx).2⟩).1 hxΓ)
    · intro hx
      have hxΓ : x ∈ S.Γ := by
        have h1 : (g : ModGL .E6 L)⁻¹ * ((g : ModGL .E6 L) * x * (g : ModGL .E6 L)⁻¹) *
            (g : ModGL .E6 L) = x := by group
        rw [← h1]
        exact mul_mem (mul_mem (inv_mem g.2) (S.E_le hx).2) g.2
      have hyΓ : g * (⟨x, hxΓ⟩ : S.Γ) * g⁻¹ ∈ S.E.subgroupOf S.Γ := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hx
      exact Subgroup.mem_subgroupOf.1 ((Subgroup.mem_normalizer_iff.1 hg ⟨x, hxΓ⟩).2 hyΓ)
  have hgA : (g : ModGL .E6 L) ∈
      adjointGroup .E6 L ⊓ Subgroup.normalizer (S.E : Set (ModGL .E6 L)) := by
    refine Subgroup.mem_inf.2 ⟨?_, hgN⟩
    have hΓ : S.Γ ≤ S.D.model := kg3_commutator_self_le_self S.D.model
    exact (S.D.mem_model.1 (hΓ g.2)).1
  have hCV : adjointGroup .E6 L ⊓ Subgroup.centralizer (S.E : Set (ModGL .E6 L)) =
      torusGroup .E6 L := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzC, hzE⟩ := Subgroup.mem_inf.1 hz
      exact k3_commute_torus hζ hzC fun y hy =>
        (Subgroup.mem_centralizer_iff.1 hzE (k3Diag ζ y)
          ((k3_E_eq S hS hζ (k3Diag ζ y)).2 ⟨y, hy, rfl⟩)).symm
    · intro z hz
      refine Subgroup.mem_inf.2 ⟨CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' hz, ?_⟩
      exact Subgroup.mem_centralizer_iff.2 fun y hy => hTcomm y (hVH hy) z hz
  obtain ⟨h, hh, c, hgc⟩ :=
    CFSG.RankThree.Chevalley.exists_eq_mul_canonicalRep_of_mem_normalizer hVH hCV hgA
  have hconj : ∀ x ∈ S.E,
      (g : ModGL .E6 L) * x * (g : ModGL .E6 L)⁻¹ =
        canonicalRep (coxeterSystem .E6) L c * x * (canonicalRep (coxeterSystem .E6) L c)⁻¹ := by
    intro x hx
    have hxT : x ∈ torusGroup .E6 L := hVH hx
    have ht : canonicalRep (coxeterSystem .E6) L c * x *
        (canonicalRep (coxeterSystem .E6) L c)⁻¹ ∈ torusGroup .E6 L :=
      (Subgroup.mem_normalizer_iff.1
        (canonicalRep_mem_normalizer (τ := .E6) (R := L) c) x).1 hxT
    calc (g : ModGL .E6 L) * x * (g : ModGL .E6 L)⁻¹
        = h * canonicalRep (coxeterSystem .E6) L c * x *
            (h * canonicalRep (coxeterSystem .E6) L c)⁻¹ := by rw [hgc]
      _ = h * (canonicalRep (coxeterSystem .E6) L c * x *
            (canonicalRep (coxeterSystem .E6) L c)⁻¹) * h⁻¹ := by group
      _ = (canonicalRep (coxeterSystem .E6) L c * x *
            (canonicalRep (coxeterSystem .E6) L c)⁻¹) * h * h⁻¹ := by
            rw [hTcomm h hh
              (canonicalRep (coxeterSystem .E6) L c * x *
                (canonicalRep (coxeterSystem .E6) L c)⁻¹) ht]
      _ = canonicalRep (coxeterSystem .E6) L c * x *
            (canonicalRep (coxeterSystem .E6) L c)⁻¹ := by group
  have hstab : ∀ y ∈ k3Ex, k3Star c y ∈ k3Ex := by
    intro y hy
    have hd : k3Diag ζ y ∈ S.E := (k3_E_eq S hS hζ (k3Diag ζ y)).2 ⟨y, hy, rfl⟩
    have hgd : (g : ModGL .E6 L) * k3Diag ζ y * (g : ModGL .E6 L)⁻¹ ∈ S.E :=
      (Subgroup.mem_set_normalizer_iff.1 hgN (k3Diag ζ y)).1 hd
    have hEq : k3Diag ζ (k3Star c y) ∈ S.E := by
      rw [← k3_conj_diag h7 c y, ← hconj (k3Diag ζ y) hd]
      exact hgd
    obtain ⟨y', hy', heq⟩ := (k3_E_eq S hS hζ (k3Diag ζ (k3Star c y))).1 hEq
    rw [k3Diag_injective hζ heq]
    exact hy'
  exact ⟨c, k3_comm_of_stable c hstab, hconj⟩

end CFSG.StandardType.GGKG3
