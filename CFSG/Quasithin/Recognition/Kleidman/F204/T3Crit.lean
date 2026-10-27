module

public import CFSG.Quasithin.Recognition.Kleidman.F204.T3F2a
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOff

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section H3'

variable (F : Frame L1 L2 S D X)

include F

theorem H3' {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    {A : Subgroup G} (hAx : A ≤ stab x) (hA : IsPGroup 2 (A.subgroupOf (stab x)))
    (hAnt : ∃ a ∈ A, ∃ v ∈ Zv x, a * v ≠ v * a)
    (hidx : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) ≤
      (A ⊓ Qv x).relIndex A) :
    Nat.card (Zv x) = 16 * Nat.card (Zv x ⊓ Subgroup.centralizer (stab x : Set G) : Subgroup G) ∧
      (A ⊓ Qv x).relIndex A = 4 ∧
      Nat.card (Zv x ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
        4 * Nat.card (Zv x ⊓ Subgroup.centralizer (stab x : Set G) : Subgroup G) := by
  have hA' := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hx
  have hV2 : ∀ a ∈ Zv x, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact (hA'.isElemAbelian_Zv x).2 a ha
  have hLV : stab x ≤ Subgroup.normalizer (Zv x : Set G) := hA'.stab_le_normalizer_Zv x
  have hker : ∀ l : ↥(stab x), φ l = 1 → (l : G) ∈ Subgroup.centralizer (Zv x : Set G) := by
    intro l hl
    have hlk : l ∈ φ.ker := MonoidHom.mem_ker.mpr hl
    rw [hφk] at hlk
    exact Qv_le_centralizer_Zv F x (Subgroup.mem_subgroupOf.mp hlk)
  have hbridge : (A ⊓ Qv x).relIndex A = Nat.card ((A.subgroupOf (stab x)).map φ) := by
    calc (A ⊓ Qv x).relIndex A = (Qv x).relIndex A := by
          rw [inf_comm]; exact Subgroup.inf_relIndex_right (H := Qv x) (K := A)
      _ = ((Qv x).subgroupOf (stab x)).relIndex (A.subgroupOf (stab x)) :=
          (Subgroup.relIndex_subgroupOf hAx).symm
      _ = φ.ker.relIndex (A.subgroupOf (stab x)) := by rw [hφk]
      _ = Nat.card ((A.subgroupOf (stab x)).map φ) := Subgroup.relIndex_ker _ φ
  have hAmap : ((A.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAx]
  have hAnt' : ∃ a ∈ A.subgroupOf (stab x), ∃ v ∈ Zv x, (a : G) * v ≠ v * (a : G) := by
    obtain ⟨a, haA, v, hv, hne⟩ := hAnt
    exact ⟨⟨a, hAx haA⟩, Subgroup.mem_subgroupOf.mpr haA, v, hv, hne⟩
  have hidx' : (Zv x ⊓ Subgroup.centralizer
      (((A.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) : Set G)).relIndex (Zv x) ≤
      Nat.card ((A.subgroupOf (stab x)).map φ) := by
    rw [hAmap, ← hbridge]
    exact hidx
  obtain ⟨h1, h2, h3, -⟩ := fa5_ff_card' hV2 hLV φ hφs hker hA hAnt' hidx'
  refine ⟨h1, ?_, ?_⟩
  · rw [hbridge]
    exact h2
  · rw [hAmap] at h3
    exact h3

end H3'

section Pair

variable (F : Frame L1 L2 S D X)

include F

theorem T3_pair {x y : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hZx : ZFaithful x) (hZy : ZFaithful y)
    (hsx : Zv y ≤ stab x) (hsy : Zv x ≤ stab y)
    (hnot1 : ¬ Zv x ≤ Qv y) (hnot2 : ¬ Zv y ≤ Qv x)
    (hdis : (Zv x ⊓ Subgroup.centralizer (Zv y : Set G)).relIndex (Zv x) ≤
      (Zv y ⊓ Qv x).relIndex (Zv y)) :
    vtype x = true ∧ vtype y = true ∧
      Nat.card (Zv x) = 16 * Nat.card (Zv x ⊓ Subgroup.centralizer (stab x : Set G) : Subgroup G) ∧
      Nat.card (Zv y) = 16 * Nat.card (Zv y ⊓ Subgroup.centralizer (stab y : Set G) : Subgroup G) ∧
      (Zv x ⊓ Qv y).relIndex (Zv x) = 4 ∧ (Zv y ⊓ Qv x).relIndex (Zv y) = 4 := by
  have hA := Amal.of_frame F
  have hV2x : ∀ a ∈ Zv x, a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv x).2 a ha
  have hV2y : ∀ a ∈ Zv y, a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv y).2 a ha
  have hEx := inf_centralizer_eq_inf_Qv F hZy hsy
  have hEy := inf_centralizer_eq_inf_Qv F hZx hsx
  have hvx : vtype x = true := by
    by_contra hf
    have hf' : vtype x = false := by simpa using hf
    exact H2 F hf' hZx (hA.isElemAbelian_Zv y) hsx hnot2 hdis
  have hAy : IsPGroup 2 ((Zv y).subgroupOf (stab x)) :=
    isPGroup_two_of_sq_gen fun u hu => Subtype.ext (by
      simpa using hV2y _ (Subgroup.mem_subgroupOf.mp hu))
  obtain ⟨hcx, hq, hcZC⟩ := H3' F hvx hsx hAy (exists_noncomm_of_not_le F hEx hnot1) hdis
  have hcZQ : Nat.card (Zv x ⊓ Qv y : Subgroup G) =
      4 * Nat.card (Zv x ⊓ Subgroup.centralizer (stab x : Set G) : Subgroup G) := by
    rw [← hEx]; exact hcZC
  have hp : (Zv x ⊓ Qv y).relIndex (Zv x) = 4 := by
    have h := card_eq_relIndex_mul (V := Zv x) (Z := Qv y)
    rw [hcx, hcZQ] at h
    have hpos : 0 < Nat.card (Zv x ⊓ Subgroup.centralizer (stab x : Set G) : Subgroup G) :=
      Nat.card_pos
    nlinarith
  have hvy : vtype y = true := by
    by_contra hf
    have hf' : vtype y = false := by simpa using hf
    have := relIndex_inf_Qv_le_two F hf' hsy (hA.isElemAbelian_Zv x)
    omega
  have hAx' : IsPGroup 2 ((Zv x).subgroupOf (stab y)) :=
    isPGroup_two_of_sq_gen fun u hu => Subtype.ext (by
      simpa using hV2x _ (Subgroup.mem_subgroupOf.mp hu))
  have hidy : (Zv y ⊓ Subgroup.centralizer (Zv x : Set G)).relIndex (Zv y) ≤
      (Zv x ⊓ Qv y).relIndex (Zv x) := by
    simp only [hEy, hq, hp, le_refl]
  obtain ⟨hcy, -, -⟩ := H3' F hvy hsy hAx' (exists_noncomm_of_not_le F hEy hnot2) hidy
  exact ⟨hvx, hvy, hcx, hcy, hp, hq⟩


theorem T3_H4 (hT3 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ¬ ZCentral δ)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') :
    ¬ Zv α' ≤ Qv α ∧ vtype α = true ∧ vtype α' = true ∧
      Nat.card (Zv α) = 16 * Nat.card (Zv α ⊓ Subgroup.centralizer (stab α : Set G) : Subgroup G) ∧
      Nat.card (Zv α') = 16 *
        Nat.card (Zv α' ⊓ Subgroup.centralizer (stab α' : Set G) : Subgroup G) ∧
      (Zv α ⊓ Qv α').relIndex (Zv α) = 4 ∧ (Zv α' ⊓ Qv α).relIndex (Zv α') = 4 := by
  have hA := Amal.of_frame F
  have hdich : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ∨ ZFaithful δ :=
    fun δ => dichotomy F δ
  have h : ¬ Zv α' ≤ Qv α := by
    intro h
    exact hT3 α' (hA.caseII hdich hc h).1
  obtain ⟨hb, hZα, hZα'⟩ := hA.caseI hdich hc h
  have hsx : Zv α' ≤ stab α := by
    apply hA.Zv_le_stab_of_dist_le
    rw [hb, CosetGeom.dist_comm, hc.dist_eq]
  have hsy : Zv α ≤ stab α' := by
    apply hA.Zv_le_stab_of_dist_le
    rw [hc.dist_eq, hc.bAt_eq]
  rcases hA.offender_or α α' with hdis | hdis
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      T3_pair F hZα hZα' hsx hsy hc.not_le h hdis
    exact ⟨h, h1, h2, h3, h4, h5, h6⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      T3_pair F hZα' hZα hsy hsx h hc.not_le hdis
    exact ⟨h, h2, h1, h4, h3, h6, h5⟩

end Pair

end CFSG.Quasithin.Kleidman.F204
