module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionClasses
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionSwap

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup Matrix

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

theorem isConj_t_iff_of_isConj_t_tu [Finite G] (htu : IsConj D.t (D.t * D.u)) {x : G}
    (hx : x ∈ D.E) (hx2 : orderOf x = 2) :
    IsConj D.t x ↔
      x = D.t ∨ x = D.t * D.u ∨ x = D.u * D.v ∨ x = D.u * D.w ∨ x = D.u * D.v * D.w :=
  D.isConj_t_iff_of_mem_E (D.not_isConj_t_u_of_isConj_t_tu htu) htu
    (D.isConj_u_v_of_isConj_t_tu htu) hx hx2

private theorem orderOf_eq_two_of_isConj_t {x : G} (h : IsConj D.t x) : orderOf x = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (SemiconjBy.orderOf_eq c (show SemiconjBy c D.t (c * D.t * c⁻¹) from by
    unfold SemiconjBy; group)).symm.trans D.orderOf_t

section Rep

variable {D} {ρ : normalizer (D.E : Set G) →* GL (Fin 4) (ZMod 2)}

theorem IsBasisRep.vecMul_mem_fusionPplus [Finite G] (htu : IsConj D.t (D.t * D.u))
    (hρ : D.IsBasisRep ρ) (g : normalizer (D.E : Set G)) :
    ∀ p ∈ fusionPplus, p ᵥ* (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ fusionPplus := by
  intro p hp
  have hbase : IsConj D.t (D.vecE p) := by
    simp only [fusionPplus, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · simpa [SwapData.vecE, ZMod.val_one] using IsConj.refl D.t
    · simpa [SwapData.vecE, ZMod.val_one] using htu
    · simpa [SwapData.vecE, ZMod.val_one] using htu.trans D.isConj_t_mul_u_u_mul.1
    · simpa [SwapData.vecE, ZMod.val_one] using htu.trans D.isConj_t_mul_u_u_mul.2.1
    · simpa [SwapData.vecE, ZMod.val_one] using htu.trans D.isConj_t_mul_u_u_mul.2.2
  set q : Fin 4 → ZMod 2 := p ᵥ* (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hq
  have h2p : orderOf (D.vecE p) = 2 := orderOf_eq_two_of_isConj_t D hbase
  have hvec : D.vecE q = (g : G)⁻¹ * D.vecE p * g := by
    rw [hq]
    exact (hρ.conj_vecE g p).symm
  have hconjq : IsConj D.t (D.vecE q) := by
    refine hbase.trans (isConj_iff.mpr ⟨(g : G)⁻¹, ?_⟩)
    rw [hvec]
    group
  have h2q : orderOf (D.vecE q) = 2 := orderOf_eq_two_of_isConj_t D hconjq
  have hdisj := (D.isConj_t_iff_of_isConj_t_tu htu (D.vecE_mem_E q) h2q).mp hconjq
  show q ∈ fusionPplus
  rcases hdisj with h | h | h | h | h
  · have hq0 : q = ![1, 0, 0, 0] :=
      D.vecE_injective (by rw [h]; simp [SwapData.vecE, ZMod.val_one])
    rw [hq0]; decide
  · have hq1 : q = ![1, 1, 0, 0] :=
      D.vecE_injective (by rw [h]; simp [SwapData.vecE, ZMod.val_one])
    rw [hq1]; decide
  · have hq2 : q = ![0, 1, 1, 0] :=
      D.vecE_injective (by rw [h]; simp [SwapData.vecE, ZMod.val_one])
    rw [hq2]; decide
  · have hq3 : q = ![0, 1, 0, 1] :=
      D.vecE_injective (by rw [h]; simp [SwapData.vecE, ZMod.val_one])
    rw [hq3]; decide
  · have hq4 : q = ![0, 1, 1, 1] :=
      D.vecE_injective (by rw [h]; simp [SwapData.vecE, ZMod.val_one])
    rw [hq4]; decide

theorem IsBasisRep.card_range [Finite G] (htu : IsConj D.t (D.t * D.u)) (hρ : D.IsBasisRep ρ) :
    Nat.card ρ.range = 60 := by
  refine card_eq_sixty_of_fusionPplus ?_ ?_ ?_ hρ.not_eight_dvd ?_ ?_
  · exact ⟨⟨D.h1, D.h1_mem_normalizer_E⟩, hρ.apply_h1⟩
  · exact ⟨⟨D.c1, D.c1_mem_normalizer_E⟩, hρ.apply_c1⟩
  · exact ⟨⟨D.f12, D.f12_mem_normalizer_E⟩, hρ.apply_f12⟩
  · intro h hh p hp
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hh
    exact hρ.vecMul_mem_fusionPplus htu g p hp
  · obtain ⟨z0, hz0N, hz0ne⟩ := D.exists_mem_normalizer_E_conj_t_ne htu
    refine ⟨ρ ⟨z0, hz0N⟩, ⟨⟨z0, hz0N⟩, rfl⟩, ?_⟩
    intro he
    apply hz0ne
    have h1 : D.vecE (![1, 0, 0, 0] ᵥ* (ρ ⟨z0, hz0N⟩ : Matrix (Fin 4) (Fin 4) (ZMod 2)))
        = D.vecE ![1, 0, 0, 0] := by rw [he]
    rw [← hρ.conj_vecE ⟨z0, hz0N⟩ ![1, 0, 0, 0]] at h1
    simpa [SwapData.vecE, ZMod.val_one] using h1

end Rep

theorem exists_fusion_element [Finite G] (htu : IsConj D.t (D.t * D.u)) :
    ∃ z ∈ normalizer (D.E : Set G), z⁻¹ * D.t * z = D.u * D.v ∧ z⁻¹ * D.u * z = D.t * D.v ∧
      z⁻¹ * D.v * z = D.v ∧ z⁻¹ * D.w * z = D.t * D.u * D.w ∧ z ^ 2 ∈ D.E := by
  obtain ⟨ρ, hρ⟩ := D.exists_isBasisRep
  have h60 : Nat.card ρ.range = 60 := hρ.card_range htu
  have hmem : ∀ h ∈ ρ.range, ∀ p ∈ fusionPplus,
      p ᵥ* (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ fusionPplus := by
    intro h hh p hp
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hh
    exact hρ.vecMul_mem_fusionPplus htu g p hp
  have hZ : fusionUnitZ ∈ ρ.range := fusionUnitZ_mem hmem h60
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hZ
  have h2 : fusionUnitZ ^ 2 = 1 := by
    apply Units.ext
    simp [pow_two, val_fusionUnitZ, fusionZ_mul_self]
  refine ⟨(g : G), g.2, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hρ g 0
    rw [hg] at h
    simpa [SwapData.vecE, SwapData.eb, fusionZ, ZMod.val_one] using h
  · have h := hρ g 1
    rw [hg] at h
    simpa [SwapData.vecE, SwapData.eb, fusionZ, ZMod.val_one] using h
  · have h := hρ g 2
    rw [hg] at h
    simpa [SwapData.vecE, SwapData.eb, fusionZ, ZMod.val_one] using h
  · have h := hρ g 3
    rw [hg] at h
    simpa [SwapData.vecE, SwapData.eb, fusionZ, ZMod.val_one] using h
  · have hρg2 : ρ (g ^ 2) = 1 := by
      rw [map_pow, hg]
      exact h2
    have hker : g ^ 2 ∈ ρ.ker := MonoidHom.mem_ker.mpr hρg2
    rw [hρ.ker_eq, Subgroup.mem_subgroupOf] at hker
    simpa using hker

theorem exists_splitData [Finite G] :
    ∃ D' : SplitData G, D'.i1 = D.i1 ∧ D'.i2 = D.i2 ∧ D'.t = D.t := by
  obtain ⟨D₀, hi1, hi2, ht, htu⟩ := D.exists_isConj_t_tu
  obtain ⟨z, -, hzt, hzu, hzv, -, hzsq⟩ := D₀.exists_fusion_element htu
  refine ⟨{ toSwapData := D₀, z := z,
            not_isConj_t_u := D₀.not_isConj_t_u_of_isConj_t_tu htu
            isConj_t_tu := htu
            isConj_u_v := D₀.isConj_u_v_of_isConj_t_tu htu
            isConj_t_or_u := fun x hx => D₀.isConj_t_or_u_of_isConj_t_tu htu hx
            isSylow := D₀.isSylow_S
            z_t := by simpa [SwapData.v, SwapData.h1, SwapData.h2] using hzt
            z_u := by simpa [SwapData.v, SwapData.h1, SwapData.h2] using hzu
            z_v := by simpa [SwapData.v, SwapData.h1, SwapData.h2] using hzv
            z_sq := by
              simpa [SwapData.S, SwapData.h1, SwapData.c1, SwapData.h2, SwapData.c2]
                using D₀.E_le_S hzsq }, ?_, ?_, ?_⟩
  · exact hi1
  · exact hi2
  · exact ht

end SwapData

theorem WongHyp.exists_splitData {G : Type} [Group G] [Finite G] {t : G} {L₁ L₂ : Subgroup G}
    (h : WongHyp t L₁ L₂) {u : G} (hu : orderOf u = 2) (huK : u ∉ L₁ ⊔ L₂)
    (hL : L₁.map (MulAut.conj u).toMonoidHom = L₂) :
    ∃ D : SplitData G, D.t = t ∧ D.i1.range = L₁ ∧ D.i2.range = L₂ := by
  obtain ⟨D, ht, -, hL1, hL2⟩ := h.exists_swapData hu huK hL
  obtain ⟨D', hi1, hi2, ht'⟩ := D.exists_splitData
  exact ⟨D', ht'.trans ht, by rw [hi1, hL1], by rw [hi2, hL2]⟩

end CFSG.OddTranspositions.PartThree.Wong
