module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {G : Type*} [Group G] {S : Set (Subgroup G)} {K : Subgroup G}

theorem eq_top_of_forall_mem (hK : IsDirectProduct S K) {P : Subgroup ↥K}
    (h : ∀ J (hJ : J ∈ S), ∀ (x : G) (hx : x ∈ J), (⟨x, hK.le hJ hx⟩ : K) ∈ P) : P = ⊤ := by
  have hle : sSup S ≤ P.map K.subtype :=
    sSup_le fun J hJ x hx => ⟨⟨x, hK.le hJ hx⟩, h J hJ x hx, rfl⟩
  rw [hK.sSup_eq] at hle
  refine eq_top_iff.mpr fun m _ => ?_
  obtain ⟨m', hm', hmm'⟩ := hle m.2
  rwa [← Subtype.ext hmm']

theorem hom_mem_of_forall_mem (hK : IsDirectProduct S K) {N : Type*} [Group N] (f : ↥K →* N)
    (P : Subgroup N)
    (h : ∀ J (hJ : J ∈ S), ∀ (x : G) (hx : x ∈ J), f ⟨x, hK.le hJ hx⟩ ∈ P) (m : K) :
    f m ∈ P := by
  have htop := eq_top_of_forall_mem hK (P := P.comap f) h
  have hm : m ∈ P.comap f := htop ▸ Subgroup.mem_top m
  exact hm

theorem hom_ext_of_forall_mem (hK : IsDirectProduct S K) {N : Type*} [Group N] (f g : ↥K →* N)
    (h : ∀ J (hJ : J ∈ S), ∀ (x : G) (hx : x ∈ J),
      f ⟨x, hK.le hJ hx⟩ = g ⟨x, hK.le hJ hx⟩) : f = g := by
  have htop := eq_top_of_forall_mem hK (P := f.eqLocus g) h
  refine MonoidHom.ext fun m => ?_
  have hm : m ∈ f.eqLocus g := htop ▸ Subgroup.mem_top m
  exact hm

theorem hom_mem_of_coord_mem [Finite G] (hK : IsDirectProduct S K) {N : Type*} [Group N]
    (f : ↥K →* N) (P : Subgroup N) (m : K)
    (h : ∀ J (hJ : J ∈ S), f ⟨(hK.coord hJ m : G), hK.le hJ (hK.coord hJ m).2⟩ ∈ P) :
    f m ∈ P := by
  have h1 : (m : G) ∈ (P.comap f).map K.subtype :=
    hK.mem_of_coord_mem m.2 fun J hJ => ⟨⟨_, hK.le hJ (hK.coord hJ m).2⟩, h J hJ, rfl⟩
  obtain ⟨m', hm', hmm'⟩ := h1
  rwa [← Subtype.ext hmm']

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
