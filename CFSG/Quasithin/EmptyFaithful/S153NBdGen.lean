module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.S153N.BridgeD

open CFSG.QuasithinUnique CFSG.Quasithin

section General

variable {G H B : Type*} [Group G] [Group H] [Group B]

theorem normal_comap_of_normal_subgroupOf_range (φ : H →* B) {N : Subgroup B}
    (hN : (N.subgroupOf φ.range).Normal) : (N.comap φ).Normal := by
  refine ⟨fun n hn h => ?_⟩
  have h1 : (⟨φ n, φ.mem_range.mpr ⟨n, rfl⟩⟩ : ↥φ.range) ∈ N.subgroupOf φ.range :=
    Subgroup.mem_subgroupOf.mpr hn
  have h2 := hN.conj_mem _ h1 ⟨φ h, φ.mem_range.mpr ⟨h, rfl⟩⟩
  show φ (h * n * h⁻¹) ∈ N
  rw [map_mul, map_mul, map_inv]
  exact h2

theorem isSylowTwoOf_subgroupOf {S X C : Subgroup G} (h : IsSylowTwoOf S X) (hXC : X ≤ C) :
    IsSylowTwoOf (S.subgroupOf C) (X.subgroupOf C) := by
  have hSC : S ≤ C := h.1.trans hXC
  refine ⟨fun x hx => h.1 hx, h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm, fun hd => ?_⟩
  apply h.2.2
  have e : (S.subgroupOf C).relIndex (X.subgroupOf C) = S.relIndex X :=
    Subgroup.relIndex_subgroupOf hXC
  have hd' : 2 ∣ (S.subgroupOf C).relIndex (X.subgroupOf C) := hd
  rw [e] at hd'
  exact hd'

end General

section Transfer

variable {H B : Type*} [Group H] [Group B]

theorem frattini_transfer [Finite H] (φ : H →* B) {N F : Subgroup B} (hNr : N ≤ φ.range)
    (hFr : F ≤ φ.range) (hNn : (N.subgroupOf φ.range).Normal) {P Q : Subgroup H}
    (hP : IsSylowTwoOf P (N.comap φ)) (hQ : ∀ c : H, φ c ∈ F ↔ c ∈ Q)
    (hker : φ.ker ≤ Q) (hPQ : P ≤ Q) (hNP : Subgroup.normalizer (P : Set H) ≤ Q) :
    φ.range = N ⊔ F ∧ IsSylowTwoOf (P.map φ) N ∧
      Subgroup.normalizer ((P.map φ : Subgroup B) : Set B) ⊓ N ≤ F := by
  have hnorm : (N.comap φ).Normal := normal_comap_of_normal_subgroupOf_range φ hNn
  have hkerN : φ.ker ≤ N.comap φ := MonoidHom.ker_le_comap φ N
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm ?_ (sup_le hNr hFr)
    rintro _ ⟨c, rfl⟩
    have hfr := B6.frattini_two (le_top : N.comap φ ≤ ⊤)
      (Subgroup.le_normalizer_of_normal) hP (Subgroup.mem_top c)
    have h2 : ((N.comap φ ⊔ (⊤ ⊓ Subgroup.normalizer (P : Set H))).map φ) ≤ N ⊔ F := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (Subgroup.map_comap_le φ N)
        (Subgroup.map_le_iff_le_comap.2 fun m hm => (hQ m).2 (hNP hm.2))
    exact h2 (Subgroup.mem_map_of_mem φ hfr)
  · refine ⟨?_, hP.2.1.map φ, ?_⟩
    · exact (Subgroup.map_mono hP.1).trans (Subgroup.map_comap_le φ N)
    · have h2 : (P.map φ).relIndex N = (P ⊔ φ.ker).relIndex (N.comap φ) := by
        have := Subgroup.relIndex_map_map φ P (N.comap φ)
        rwa [Subgroup.map_comap_eq_self hNr, sup_of_le_left hkerN] at this
      intro hd
      have hd' : 2 ∣ (P.map φ).relIndex N := hd
      rw [h2] at hd'
      exact hP.2.2 (hd'.trans (Subgroup.relIndex_dvd_of_le_left _ le_sup_left))
  · rintro n ⟨hn1, hn2⟩
    obtain ⟨c, rfl⟩ := hNr hn2
    have hc : c ∈ Subgroup.normalizer ((P ⊔ φ.ker : Subgroup H) : Set H) := by
      have := Subgroup.comap_normalizer_eq_of_le_range (f := φ)
        (Subgroup.map_le_range φ P)
      rw [Subgroup.comap_map_eq] at this
      rw [← this]
      exact hn1
    have hRN : P ⊔ φ.ker ≤ N.comap φ := sup_le hP.1 hkerN
    have hPR : IsSylowTwoOf P (P ⊔ φ.ker) := B6.isSylowTwoOf_mono hP le_sup_left hRN
    have hfr := B6.frattini_two (Subgroup.le_normalizer) (le_refl _) hPR hc
    have hle : P ⊔ φ.ker ⊔ (Subgroup.normalizer ((P ⊔ φ.ker : Subgroup H) : Set H) ⊓
        Subgroup.normalizer (P : Set H)) ≤ Q :=
      sup_le (sup_le hPQ hker) (inf_le_right.trans hNP)
    exact (hQ c).2 (hle hfr)

end Transfer

end CFSG.Quasithin.S153N.BridgeD
