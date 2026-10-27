module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Lbl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

variable (F : FanTree Γ G) {α : V} (hα : valence Γ α = 5) {z : G} (hz : IsCentralInvolIn G α z)
include F hα hz

theorem exists_lab_conj {δ l : V} (hδ : valence Γ δ = 5) (hl : valence Γ l = 5) :
    ∃ g : G, g • δ = l ∧ (labZ F hα hz).z l = g * (labZ F hα hz).z δ * g⁻¹ := by
  obtain ⟨g, hg⟩ := exists_smul_of_valence_eq F (u := δ) (w := l) (by rw [hl, hδ])
  exact ⟨g, hg, by rw [← hg]; exact (labZ F hα hz).equivariant g δ hδ⟩

theorem lab_cinv {δ : V} (hδ : valence Γ δ = 5) : (labZ F hα hz).z δ ∈ Cinv G δ :=
  cinv_iff.2 ((labZ F hα hz).isCentral δ hδ)

theorem labHyp_of (h40 : Fan40 F)
    (hprod : ∀ (β : V) (l : List V) (h : V → G), ¬ Equiv3 G α β → l.Nodup →
      (∀ u, u ∈ l ↔ Γ.Adj β u) → (∀ u, Γ.Adj β u → h u • α = u) →
      (l.map fun u => h u * z * (h u)⁻¹).Pairwise Commute ∧
        (l.map fun u => h u * z * (h u)⁻¹).prod = 1)
    (h517a : Fan517a F) (hD : LemmaD F) (h517c : Fan517c F) : LabHyp (labZ F hα hz) := by
  refine ⟨fun β a b c hβ hset hab hac hbc => ?_, fun δ l hδ hl => ?_,
    fun l d hld hl hd hdist e => ?_, fun δ l₁ l₂ l₃ hδ h1 h2 h3 => ?_⟩
  · have hne : ¬ Equiv3 G α β := by
      rintro ⟨g, hg⟩
      have := F.valence_smul_eq g α
      rw [hg, hα] at this
      omega
    have hmem : ∀ u, u ∈ [a, b, c] ↔ Γ.Adj β u := by
      intro u
      have : u ∈ Γ.neighborSet β ↔ u ∈ ({a, b, c} : Set V) := by rw [hset]
      simpa [or_assoc] using this.symm
    have hfun : ∀ u, Γ.Adj β u → pick G α u • α = u := by
      intro u hu
      obtain ⟨g, hg⟩ := exists_smul_of_valence_eq F (u := α) (w := u)
        (by rw [F.val5_of_adj_val3 hu hβ, hα])
      exact pick_smul ⟨g, hg⟩
    obtain ⟨-, hp⟩ := hprod β [a, b, c] (pick G α) hne (by simp [hab, hac, hbc]) hmem hfun
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
    rw [← mul_assoc] at hp
    rw [labZ_z]
    exact hp
  · obtain ⟨ν, hν⟩ := exists_br F hl
    have hvl := (Br.valence F hδ hν).2
    obtain ⟨g, hg, hgl⟩ := exists_lab_conj F hα hz hδ hvl
    have := (h517a h40 δ _ (by omega) (lab_cinv F hα hz hδ)).1
      (Subgroup.subset_closure ⟨g, by rw [hg]; exact hl.le, hgl⟩)
    exact this
  · exact hD h40 l d hld hl hd hdist _ (lab_cinv F hα hz hl) (by rw [e]; exact lab_cinv F hα hz hd)
  · obtain ⟨ν₁, hν₁⟩ := exists_br F h1
    obtain ⟨ν₂, hν₂⟩ := exists_br F h2
    obtain ⟨ν₃, hν₃⟩ := exists_br F h3
    obtain ⟨g₁, hg₁, e₁⟩ := exists_lab_conj F hα hz hδ (Br.valence F hδ hν₁).2
    obtain ⟨g₂, hg₂, e₂⟩ := exists_lab_conj F hα hz hδ (Br.valence F hδ hν₂).2
    obtain ⟨g₃, hg₃, e₃⟩ := exists_lab_conj F hα hz hδ (Br.valence F hδ hν₃).2
    rw [e₁, e₂, e₃]
    exact h517c h40 δ _ (by omega) (lab_cinv F hα hz hδ) g₁ g₂ g₃ (by rw [hg₁]; exact h1)
      (by rw [hg₂]; exact h2) (by rw [hg₃]; exact h3)

omit hα hz in
theorem exists_labHyp (h40 : Fan40 F) (h512b : Fan512b F) (h517a : Fan517a F) (hD : LemmaD F)
    (h517c : Fan517c F) (T : Track Γ G) (hT : InXi T) (a : ℤ) {z : G} (hZ : z ∈ T.line.ZZ)
    (hz1 : z ≠ 1) (hcore : T.line.IsCore z a (a + 2))
    (hα : valence Γ (T.line.vert (a + 1)) = 5) (hz : z ∈ Cinv G (T.line.vert (a + 1))) :
    ∃ L : ZLab Γ G, L.z (T.line.vert (a + 1)) = z ∧ LabHyp L := by
  have hzc := cinv_iff.1 hz
  refine ⟨labZ F hα hzc, ?_, labHyp_of F hα hzc h40 (h512b h40 T z a hT hZ hz1 hcore).2 h517a hD
    h517c⟩
  rw [labZ_z, labOf_eq hzc.2.2.2 (one_smul G _)]
  group

end P62

end CFSG.Quasithin.Fan86
