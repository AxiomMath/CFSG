module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_inv_conj_mem_of_map_conj_eq {X : Type*} [Group X] {L M : Subgroup X}
    {g : X} (h : L.map (MulAut.conj g).toMonoidHom = M) {l : X} (hl : l ∈ M) :
    g⁻¹ * l * g ∈ L := by
  have hlm : l ∈ L.map (MulAut.conj g).toMonoidHom := by rwa [h]
  obtain ⟨l', hl', hl'eq⟩ := hlm
  have heq : g * l' * g⁻¹ = l := hl'eq
  have hconj : g⁻¹ * l * g = l' := by
    rw [← heq]
    group
  rw [hconj]
  exact hl'

private theorem s16h_exists_conj_mem_of_isSylowIn_two {Y : Type*} [Group Y] [Finite Y]
    {C P : Subgroup Y} (hP : IsSylowIn 2 P C) {x : Y} (hxC : x ∈ C) (hx : x * x = 1) :
    ∃ c ∈ C, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPC, hP2, hidx⟩ := hP
  have hP2' : IsPGroup 2 ↥(P.subgroupOf C) :=
    hP2.of_equiv (subgroupOfEquivOfLe hPC).symm
  let S : Sylow 2 ↥C := hP2'.toSylow hidx
  have hX : IsPGroup 2 ↥(zpowers (⟨x, hxC⟩ : ↥C)) := by
    have hdvd : orderOf (⟨x, hxC⟩ : ↥C) ∣ 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥C) S Q
  have hxQ : (⟨x, hxC⟩ : ↥C) ∈ (Q : Subgroup ↥C) := hQ (mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply] at hxQ
  refine ⟨((g⁻¹ : ↥C) : Y), (g⁻¹).2, ?_⟩
  have h1 : ((g⁻¹ * (⟨x, hxC⟩ : ↥C) * g : ↥C) : Y) ∈ P := hxQ
  simpa using h1

theorem s16h_z3_exists_tau_mem_sylow {X : Type*} [Group X] [Finite X]
    {A L L₂ T : Subgroup X} {t : X}
    (hperm : ∀ g ∈ A,
      (L.map (MulAut.conj g).toMonoidHom = L ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂) ∨
      (L.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L))
    (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (htinv : ∀ l ∈ L, t * l * t⁻¹ = l⁻¹) (htc : ∀ l ∈ L₂, t * l = l * t)
    (hT : IsSylowIn 2 T A) :
    ∃ τ ∈ T, ((∀ l ∈ L, τ * l * τ⁻¹ = l⁻¹) ∧ ∀ l ∈ L₂, τ * l = l * τ) ∨
      ((∀ l ∈ L₂, τ * l * τ⁻¹ = l⁻¹) ∧ ∀ l ∈ L, τ * l = l * τ) := by
  obtain ⟨g, hgA, hgT⟩ :=
    s16h_exists_conj_mem_of_isSylowIn_two hT htA (by simpa [pow_two] using ht2)
  refine ⟨g * t * g⁻¹, hgT, ?_⟩
  rcases hperm g hgA with ⟨hL, hL₂⟩ | ⟨hL, hL₂⟩
  · left
    refine ⟨fun l hl => ?_, fun l hl => ?_⟩
    · have hgl : g⁻¹ * l * g ∈ L := s16h_inv_conj_mem_of_map_conj_eq hL hl
      calc
        (g * t * g⁻¹) * l * (g * t * g⁻¹)⁻¹
            = g * (t * (g⁻¹ * l * g) * t⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * l * g)⁻¹ * g⁻¹ := by rw [htinv _ hgl]
        _ = l⁻¹ := by group
    · have hgl : g⁻¹ * l * g ∈ L₂ := s16h_inv_conj_mem_of_map_conj_eq hL₂ hl
      have hcomm : t * (g⁻¹ * l * g) = (g⁻¹ * l * g) * t := htc _ hgl
      calc
        (g * t * g⁻¹) * l = g * (t * (g⁻¹ * l * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * l * g) * t) * g⁻¹ := by rw [hcomm]
        _ = l * (g * t * g⁻¹) := by group
  · right
    refine ⟨fun l hl => ?_, fun l hl => ?_⟩
    · have hgl : g⁻¹ * l * g ∈ L := s16h_inv_conj_mem_of_map_conj_eq hL hl
      calc
        (g * t * g⁻¹) * l * (g * t * g⁻¹)⁻¹
            = g * (t * (g⁻¹ * l * g) * t⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * l * g)⁻¹ * g⁻¹ := by rw [htinv _ hgl]
        _ = l⁻¹ := by group
    · have hgl : g⁻¹ * l * g ∈ L₂ := s16h_inv_conj_mem_of_map_conj_eq hL₂ hl
      have hcomm : t * (g⁻¹ * l * g) = (g⁻¹ * l * g) * t := htc _ hgl
      calc
        (g * t * g⁻¹) * l = g * (t * (g⁻¹ * l * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * l * g) * t) * g⁻¹ := by rw [hcomm]
        _ = l * (g * t * g⁻¹) := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
