module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace TableBOrthL

@[expose] def GGInnerDiagRigid (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eb Eh : Subgroup (MulAut R), (Eb : Set (MulAut R)) ⊆ I → p ^ 3 ≤ Nat.card Eb → Eb ≤ Eh →
    IsElemAbelian p Eh → (Eh : Set (MulAut R)) ⊆ I

section Config

variable {G : Type} [Group G] [Finite G]

theorem bstar_innerDiag_of_rigid {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hrig : GGInnerDiagRigid p R I) :
    Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  have hBsN := hC.bstar_le_normalizer hnc
  obtain ⟨-, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  have hEbI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN h3 b
  have hEhI := hrig _ _ hEbI h3' (range_ggBeta_le θ hC.2.1.1 hBN hBsN)
    (isElemAbelian_range_ggBeta θ hC.2.1.2.1 hBsN)
  refine ⟨hBsN, fun b hb => ⟨_, ?_, largeEvenInduces_ggLAut_inv L θ (hBsN (Bs.inv_mem hb))⟩⟩
  exact hEhI ⟨⟨b⁻¹, Bs.inv_mem hb⟩, rfl⟩

theorem ggInnerDiagOnLab_bstar_of_rigid {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGInnerDiagRigid p R I)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hM : GGInnerDiagOnLab S p B L) : GGInnerDiagOnLab S p Bs L := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  refine ⟨hL, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hSl, hsplit, hBN, h3⟩, hrig⟩
  exact ⟨hs, hna, θ, hSl, hsplit, bstar_innerDiag_of_rigid hC hnc hL θ hBN h3 hrig⟩

end Config

theorem ggBstarInnerDiagLInputOn_of_rigid_pilot {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGInnerDiagRigid p R I) :
    GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  exact ggInnerDiagOnLab_bstar_of_rigid h hC (ggLNoncyclicInputOn_pilot G p B x L hC.1
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2⟩) hM)) hM

section D4

open NbrGraphD4 Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem eq_one_of_mem_fieldImage_two (hK : Nat.card K = 2)
    {φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) :
    φ = 1 := by
  obtain ⟨σ, hσ⟩ := hφ
  have hσ1 : ∀ a : K, σ a = a := by
    intro a
    have : Fintype K := Fintype.ofFinite K
    have h2 := FiniteField.pow_card a
    rw [← Nat.card_eq_fintype_card, hK, sq] at h2
    have h3 : a * (a - 1) = 0 := by rw [mul_sub, mul_one, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · rw [h, map_zero]
    · rw [sub_eq_zero.mp h, map_one]
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [MulAut.one_apply]
  exact hσ h h (by ext i j; simp [hσ1])

omit [CharP K 2] in
theorem eq_one_of_mem_closure_fieldImage_two (hK : Nat.card K = 2)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))}
    (hf : f ∈ Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4))))) :
    f = 1 := by
  have hle : Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) ≤ ⊥ :=
    (Subgroup.closure_le _).mpr fun φ hφ =>
      Subgroup.mem_bot.mpr (eq_one_of_mem_fieldImage_two hK hφ)
  exact Subgroup.mem_bot.mp (hle hf)

theorem ggInnerDiagRigid_d4Two (hK : Nat.card K = 2) :
    GGInnerDiagRigid 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro Eb Eh hEbI h27 hle hEh φ hφ
  by_contra hφI
  set Θ := RecipeFieldOmega.plusEquiv (K := K) one_le_four with hΘ
  set e := MulAut.congr Θ with he
  have hα : e φ ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range := by
    intro h
    obtain ⟨u, hu, f, hf, rfl⟩ := exists_inner_mul_field_of_mem h
    rw [eq_one_of_mem_closure_fieldImage_two hK hf, mul_one] at hφI
    exact hφI hu
  have hA : IsElemAbelian 3 (Eh.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := a
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := b
      apply Subtype.ext
      change e a * e b = e b * e a
      rw [← map_mul, ← map_mul,
        show a * b = b * a from congrArg Subtype.val (hEh.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)]
    · rintro _ ⟨a, ha, rfl⟩
      change e a ^ 3 = 1
      rw [← map_pow, hEh.2 a ha, map_one]
  have h9 := card_inf_inner_le_nine hA ⟨φ, hφ, rfl⟩ hα
  have hsub : Eb.map e.toMonoidHom ≤ Eh.map e.toMonoidHom ⊓ Inn (Om8 K) := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨⟨ψ, hle hψ, rfl⟩, (RecipeFieldOmega.mem_innSet_iff_congr Θ ψ).1 (hEbI hψ)⟩
  have hcard := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_map_of_injective e.injective] at hcard
  have h := le_trans h27 (le_trans hcard h9)
  norm_num at h

end D4

end TableBOrthL

open TableBOrthL

@[expose] def GGOrthLD4TwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1 ∧ p = 3

theorem GGOrthLD4TwoLabel.pilot {p : ℕ} {lab : LargeEvenLabel} (h : GGOrthLD4TwoLabel p lab) :
    GGOutdiagPilotLabel lab :=
  Or.inr (Or.inr (Or.inr (Or.inl h.1)))

theorem GGOrthLD4TwoLabel.orthNs {p : ℕ} {lab : LargeEvenLabel} (h : GGOrthLD4TwoLabel p lab) :
    GGOrthNsLabel p lab := by
  obtain ⟨ht, h4, hn, rfl⟩ := h
  refine ⟨Or.inl ht, h4.ge, ?_⟩
  rw [hn]
  norm_num

theorem largeEvenLabelAll_innerDiagRigid_d4Two {p : ℕ} {lab : LargeEvenLabel}
    (h : GGOrthLD4TwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGInnerDiagRigid p R I := by
  obtain ⟨ht, h4, hn, rfl⟩ := h
  refine largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ hK => ?_
  rw [h4]
  rw [hn, pow_one] at hK
  exact ggInnerDiagRigid_d4Two hK

theorem ggBstarInnerDiagLInputOn_d4Two (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGOrthLD4TwoLabel p lab :=
  ggBstarInnerDiagLInputOn_of_rigid_pilot (fun _ _ h => h.2.pilot) fun _ _ _ _ h =>
    largeEvenLabelAll_innerDiagRigid_d4Two h.2

section TableB

theorem ggTableBCxInputOn_d4Two (T : ℕ → LargeEvenLabel → Prop) :
    GGTableBCxInputOn fun p lab => T p lab ∧ GGOrthLD4TwoLabel p lab :=
  ggTableBCxInputOn_of_orthNs (fun _ _ h => h.2.orthNs) (ggBstarInnerDiagLInputOn_d4Two T)

theorem ggTableBModuleInputOn_d4Two (T : ℕ → LargeEvenLabel → Prop) :
    GGTableBModuleInputOn fun p lab => T p lab ∧ GGOrthLD4TwoLabel p lab :=
  ggTableBModuleInputOn_of_orthNs (fun _ _ h => h.2.orthNs) (ggBstarInnerDiagLInputOn_d4Two T)

theorem ggTableBActionInputOn_d4Two (T : ℕ → LargeEvenLabel → Prop) :
    GGTableBActionInputOn fun p lab => T p lab ∧ GGOrthLD4TwoLabel p lab :=
  ggTableBActionInputOn_of_orthNs (fun _ _ h => h.2.orthNs) (ggBstarInnerDiagLInputOn_d4Two T)

end TableB

end CFSG.StandardType

end
