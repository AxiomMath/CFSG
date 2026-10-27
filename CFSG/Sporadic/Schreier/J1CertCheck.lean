module

public import Certificates.Certificate2164

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu

theorem j1Certificate_shape : J1Certificate.shapeOK = true :=
  Certificates.certificate2164

theorem j1Certificate_shapeFacts :
    J1Certificate.schemaVersion = 1 ∧ J1Certificate.group = "J1" ∧
      J1Certificate.prime = 11 ∧ J1Certificate.dimension = 7 ∧
      J1Certificate.vectors.length = 3080 ∧
      (∀ v ∈ J1Certificate.vectors, v.length = 7 ∧ ∀ e ∈ v, e ≤ 10) ∧
      J1Certificate.basisIndices = [0, 1, 2, 3, 4, 5, 6] ∧
      J1Certificate.chain.degree = 3080 ∧ J1Certificate.chain.generators.length = 2 ∧
      (∀ a ∈ J1Certificate.chain.generators ++ J1Certificate.chain.strongGenerators,
        isPermList 3080 a = true) ∧
      J1Certificate.sylows.map (·.prime) = [2, 3, 5, 7, 11, 19] ∧
      ∀ s ∈ J1Certificate.sylows, (∀ g ∈ s.generators, isPermList 3080 g = true) ∧
        ∀ ng ∈ s.normalGeneration,
          isPermList 3080 ng.representative = true ∧ ng.chain.degree = 3080 := by
  have h := j1Certificate_shape
  simp only [J1CertificateFile.shapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem cert_j1_matrix_action_data :
    J1Certificate.schemaVersion = 1 ∧ J1Certificate.group = "J1" ∧
      J1Certificate.prime = 11 ∧ J1Certificate.dimension = 7 ∧
      J1Certificate.vectors.length = 3080 ∧
      (∀ v ∈ J1Certificate.vectors, v.length = 7 ∧ ∀ e ∈ v, e ≤ 10) ∧
      J1Certificate.basisIndices = [0, 1, 2, 3, 4, 5, 6] ∧
      J1Certificate.chain.degree = 3080 ∧ J1Certificate.chain.generators.length = 2 ∧
      (∀ a ∈ J1Certificate.chain.generators ++ J1Certificate.chain.strongGenerators,
        isPermList 3080 a = true) ∧
      J1Certificate.sylows.map (·.prime) = [2, 3, 5, 7, 11, 19] ∧
      ∀ s ∈ J1Certificate.sylows, (∀ g ∈ s.generators, isPermList 3080 g = true) ∧
        ∀ ng ∈ s.normalGeneration,
          isPermList 3080 ng.representative = true ∧ ng.chain.degree = 3080 :=
  j1Certificate_shapeFacts

end CFSG.Sporadic.Schreier
