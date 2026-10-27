module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_exists_normalizer_data (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    ∃ (J₀ : Subgroup W) (g : ↥A →* MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀)),
      J₀ ∈ irrSet L ∧
      g.ker = (s1t3KBar A L).subgroupOf A ∧
      g.range ≤ Subgroup.normalizer (((L.subgroupOf A).map g) :
        Set (MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀))) ∧
      (((L.subgroupOf A).map g).subgroupOf
        (Subgroup.normalizer (((L.subgroupOf A).map g) :
          Set (MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀))))).index ≤ 2 := by
  obtain ⟨J₀, g, hJ₀, hker, hg⟩ := s16t3_exists_section_hom h h7
  refine ⟨J₀, g, hJ₀, hker, ?_, s16t3_normalizer_index_le_two h hJ₀ g hg⟩
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have hnorm : ∀ l : ↥A, (l : MulAut W) ∈ L ↔
      (a : MulAut W) * (l : MulAut W) * (a : MulAut W)⁻¹ ∈ L :=
    fun l => Subgroup.mem_normalizer_iff.mp (h.normal a.2) _
  intro x
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨a * l * a⁻¹, ?_, by simp⟩
    exact (hnorm l).mp hl
  · rintro ⟨l, hl, hlx⟩
    refine ⟨a⁻¹ * l * a, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have hl' : (l : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hl
      have e : (a : MulAut W) * ((a⁻¹ * l * a : ↥A) : MulAut W) * (a : MulAut W)⁻¹ =
          (l : MulAut W) := by
        simp [mul_assoc]
      exact (hnorm (a⁻¹ * l * a)).mpr (by rw [e]; exact hl')
    · have h2 : g a * x * (g a)⁻¹ = g l := hlx.symm
      calc g (a⁻¹ * l * a) = (g a)⁻¹ * g l * g a := by simp
        _ = (g a)⁻¹ * (g a * x * (g a)⁻¹) * g a := by rw [h2]
        _ = x := by group

theorem ThreeNat.index_kBar_le_two (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    {a b c : MulAut W} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    a⁻¹ * b ∈ L ⊔ s1t3KBar A L ∨ a⁻¹ * c ∈ L ⊔ s1t3KBar A L ∨
      b⁻¹ * c ∈ L ⊔ s1t3KBar A L := by
  obtain ⟨J₀, g, -, hker, hrange, hidx⟩ := s16t3_exists_normalizer_data h h7
  have hnorm : s16t3_normIdx ((L.subgroupOf A).map g) :=
    s16t3_normIdx_of_index_le_two hidx
  let a' : ↥A := ⟨a, ha⟩
  let b' : ↥A := ⟨b, hb⟩
  let c' : ↥A := ⟨c, hc⟩
  have hmem := hnorm (g a') (g b') (g c')
    (hrange ⟨a', rfl⟩) (hrange ⟨b', rfl⟩) (hrange ⟨c', rfl⟩)
  have hsup : (L ⊔ s1t3KBar A L).subgroupOf A =
      L.subgroupOf A ⊔ (s1t3KBar A L).subgroupOf A :=
    Subgroup.subgroupOf_sup h.le inf_le_left
  rcases hmem with hmem | hmem | hmem
  · left
    have h1 : g (a'⁻¹ * b') ∈ (L.subgroupOf A).map g := by
      rw [map_mul, map_inv]
      exact hmem
    have h2 : a'⁻¹ * b' ∈ (L ⊔ s1t3KBar A L).subgroupOf A := by
      rw [hsup]
      exact s16t3_mem_sup_of_map_mem g hker h1
    simpa using Subgroup.mem_subgroupOf.mp h2
  · right; left
    have h1 : g (a'⁻¹ * c') ∈ (L.subgroupOf A).map g := by
      rw [map_mul, map_inv]
      exact hmem
    have h2 : a'⁻¹ * c' ∈ (L ⊔ s1t3KBar A L).subgroupOf A := by
      rw [hsup]
      exact s16t3_mem_sup_of_map_mem g hker h1
    simpa using Subgroup.mem_subgroupOf.mp h2
  · right; right
    have h1 : g (b'⁻¹ * c') ∈ (L.subgroupOf A).map g := by
      rw [map_mul, map_inv]
      exact hmem
    have h2 : b'⁻¹ * c' ∈ (L ⊔ s1t3KBar A L).subgroupOf A := by
      rw [hsup]
      exact s16t3_mem_sup_of_map_mem g hker h1
    simpa using Subgroup.mem_subgroupOf.mp h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
