module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofStar
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.RankThree.Asc83Table.HS
public import CFSG.RankThree.Asc83Table.M24
public import CFSG.RankThree.Asc83Table.He
public import CFSG.RankThree.Asc83Table.Ru
public import CFSG.RankThree.Asc83Table.J4
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofFamilies

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.Asc83Table CFSG.Blueprint

namespace Item22Res4Proof

theorem exists_eight_of_rhoE {L : Type} [Group L] (E : E9Basis L) {R : GL23}
    (hR : R ∈ E.rhoE.range) (h8 : R ^ 8 = 1) (h4 : R ^ 4 ≠ 1) :
    ∃ g : L, (∀ b ∈ E.sub, g * b * g⁻¹ ∈ E.sub) ∧ (∀ b ∈ E.sub, g ^ 8 * b = b * g ^ 8) ∧
      ∃ b ∈ E.sub, g ^ 4 * b ≠ b * g ^ 4 := by
  obtain ⟨n, hn⟩ := hR
  have hmem : ∀ x : L, x ∈ Subgroup.closure (Set.range E.vec) ↔ x ∈ E.sub := fun x => by
    rw [E.closure_range]
  have hker : ∀ k : ℕ, E.rhoE (n ^ k) = 1 → ∀ b ∈ E.sub, (n : L) ^ k * b = b * (n : L) ^ k := by
    intro k hk b hb
    have h1 : n ^ k ∈ E.rhoE.ker := hk
    have h2 : n ^ k ∈ (Subgroup.centralizer (Subgroup.closure (Set.range E.vec) : Set L)).subgroupOf
        (Subgroup.normalizer (Subgroup.closure (Set.range E.vec) : Set L)) := by
      rw [← ker_rho E.equiv]
      exact h1
    have h3 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp h2) b ((hmem b).mpr hb)
    rw [Subgroup.coe_pow] at h3
    exact h3.symm
  refine ⟨n, fun b hb => ?_, hker 8 (by rw [map_pow, hn, h8]), ?_⟩
  · exact (hmem _).mp ((Subgroup.mem_normalizer_iff.mp n.2 b).mp ((hmem b).mpr hb))
  · by_contra hall
    push Not at hall
    apply h4
    have h5 : n ^ 4 ∈ (Subgroup.centralizer (Subgroup.closure (Set.range E.vec) : Set L)).subgroupOf
        (Subgroup.normalizer (Subgroup.closure (Set.range E.vec) : Set L)) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Subgroup.coe_pow]
      exact (hall b ((hmem b).mp hb)).symm
    rw [← ker_rho E.equiv] at h5
    have h6 : E.rhoE (n ^ 4) = 1 := h5
    rwa [map_pow, hn] at h6

theorem autEight228_M23 :
    AutEight228 NativeSporadic.M23 := by
  have h4 : M23.sdR ^ 4 ≠ 1 := fun h => by
    have := M23.sd_ne 4 0 (by simpa using h)
    exact absurd this.1 (by decide)
  obtain ⟨g, hgN, h8, h4'⟩ := exists_eight_of_rhoE M23.E M23.sdR_mem M23.sdR_pow h4
  exact autEight228_of_sylow M23.factorization_card M23.E.card hgN h8 h4'

theorem autEight228_HS :
    AutEight228 NativeSporadic.HS := by
  have h4 : HS.sdR ^ 4 ≠ 1 := fun h => by
    have := HS.sd_ne 4 0 (by simpa using h)
    exact absurd this.1 (by decide)
  obtain ⟨g, hgN, h8, h4'⟩ := exists_eight_of_rhoE HS.E HS.sdR_mem HS.sdR_pow h4
  exact autEight228_of_sylow HS.factorization_card HS.E.card hgN h8 h4'

theorem autThree228_of_automizer {L : Type} [Group L] {N : Type} [Group N] (B₀ : Fin 4 → Subgroup N)
    (htr : ∀ B : Subgroup L, Nat.card B = 9 → ∃ i : Fin 4,
      Nonempty (Automizer B ≃* Automizer (B₀ i)))
    (haut : ∀ i : Fin 4, Nonempty (Automizer (B₀ i) ≃* DihedralGroup 6) ∨
      Nonempty (Automizer (B₀ i) ≃* GL23)) : AutThree228 L := by
  intro B hB
  obtain ⟨i, ⟨f⟩⟩ := htr B hB
  rcases haut i with ⟨⟨q⟩⟩ | ⟨⟨q⟩⟩
  · exact exists_three_of_automizer (f.trans q) (t := DihedralGroup.r 2) (by decide) (by decide)
  · exact exists_three_of_automizer (f.trans q) (t := unip 1) (by decide +kernel)
      (by decide +kernel)

theorem autThree228_M24 :
    AutThree228 NativeSporadic.M24 :=
  autThree228_of_automizer (fun i => (M24.E i).sub)
    (ex27_transport M24.X_cube M24.Y_cube M24.Z_X M24.Z_Y M24.Z_ne M24.factorization_card
      (MulEquiv.refl _)).2.2 M24.automizer_B

theorem autThree228_He :
    AutThree228 NativeSporadic.He :=
  autThree228_of_automizer (fun i => (He.E i).sub)
    (ex27_transport (He.facts.x_cube (CFSG.SectionRank.specP 7 50) He.he_check)
      (He.facts.y_cube (CFSG.SectionRank.specP 7 50) He.he_check)
      (He.facts.z_x (CFSG.SectionRank.specP 7 50) He.he_check)
      (He.facts.z_y (CFSG.SectionRank.specP 7 50) He.he_check)
      (He.facts.z_ne (CFSG.SectionRank.specP 7 50) He.he_check) He.factorization_card
      (MulEquiv.refl _)).2.2 He.automizer_B

theorem autThree228_Ru :
    AutThree228 NativeSporadic.Ru :=
  autThree228_of_automizer (fun i => (Ru.E i).sub)
    (ex27_transport (Ru.facts.x_cube (CFSG.SectionRank.spec2fr 28) Ru.ru_check)
      (Ru.facts.y_cube (CFSG.SectionRank.spec2fr 28) Ru.ru_check)
      (Ru.facts.z_x (CFSG.SectionRank.spec2fr 28) Ru.ru_check)
      (Ru.facts.z_y (CFSG.SectionRank.spec2fr 28) Ru.ru_check)
      (Ru.facts.z_ne (CFSG.SectionRank.spec2fr 28) Ru.ru_check) Ru.factorization_card
      (MulEquiv.refl _)).2.2 fun i => Or.inr (Ru.automizer_B i)

theorem autThree228_J4 :
    AutThree228 NativeSporadic.J4 :=
  autThree228_of_automizer (fun i => (J4.E i).sub)
    (ex27_transport (J4.facts.x_cube (CFSG.SectionRank.spec2fr 112) J4.j4_check)
      (J4.facts.y_cube (CFSG.SectionRank.spec2fr 112) J4.j4_check)
      (J4.facts.z_x (CFSG.SectionRank.spec2fr 112) J4.j4_check)
      (J4.facts.z_y (CFSG.SectionRank.spec2fr 112) J4.j4_check)
      (J4.facts.z_ne (CFSG.SectionRank.spec2fr 112) J4.j4_check) J4.factorization_card
      (MulEquiv.refl _)).2.2 fun i => Or.inr (J4.automizer_B i)

end Item22Res4Proof

open Item22Res4Proof

theorem census228SporStar_holds :
    Census228SporStar := by
  intro G _ _ X A K K₀ m hP hAmax hA27 hAN hAC hin hmono _ ρ _ _ _ _ _ _ _ _ _ _
  obtain ⟨s, hs, ⟨e⟩⟩ := hP
  simp only [sporadicsStar228, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · have : IsSimpleGroup (NativeSporadic.Carrier .M23) :=
      CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    exact false_of_autEight228 hAmax hA27 hAN hAC hin hmono e.isSimpleGroup
      (autEight228_of_mulEquiv e autEight228_M23)
  · have : IsSimpleGroup (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.isSimpleGroup_HS
    exact false_of_autEight228 hAmax hA27 hAN hAC hin hmono e.isSimpleGroup
      (autEight228_of_mulEquiv e autEight228_HS)
  · have : IsSimpleGroup (NativeSporadic.Carrier .M24) :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact false_of_autThree228 hAmax hA27 hAN hAC hin hmono e.isSimpleGroup
      (autThree228_of_mulEquiv e autThree228_M24)
  · have : IsSimpleGroup (NativeSporadic.Carrier .He) := CFSG.Sporadic.He.isSimpleGroup_He
    exact false_of_autThree228 hAmax hA27 hAN hAC hin hmono e.isSimpleGroup
      (autThree228_of_mulEquiv e autThree228_He)
  · have : IsSimpleGroup (NativeSporadic.Carrier .Ru) := CFSG.Sporadic.Ru.isSimpleGroup_Ru
    exact false_of_autThree228 hAmax hA27 hAN hAC hin hmono e.isSimpleGroup
      (autThree228_of_mulEquiv e autThree228_Ru)
  · have : IsSimpleGroup (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.isSimpleGroup_J4
    exact false_of_autThree228 hAmax hA27 hAN hAC hin hmono e.isSimpleGroup
      (autThree228_of_mulEquiv e autThree228_J4)

end CFSG.RankThree.PartTwo.Sec21
