
module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.A36B

open CFSG.SectionRank.Ccomm

theorem map_frattini_mulEquiv {P Q : Type*} [Group P] [Group Q] (ι : P ≃* Q) :
    (frattini P).map ι.toMonoidHom = frattini Q := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective ι.surjective
  · intro y hy
    have h : frattini Q ≤ (frattini P).comap ι.symm.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective ι.symm.surjective
    exact ⟨ι.symm y, h hy, by simp⟩

variable {X : Type} [Group X]

theorem frattiniIn_map_subtype (R : Subgroup X) (P : Subgroup R) :
    frattiniIn (P.map R.subtype) = (frattiniIn P).map R.subtype := by
  let e : P ≃* P.map R.subtype := P.equivMapOfInjective R.subtype R.subtype_injective
  have h1 : frattini ↥(P.map R.subtype) = (frattini ↥P).map e.toMonoidHom :=
    (map_frattini_mulEquiv e).symm
  unfold frattiniIn
  rw [h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_ker_frattiniAction_conjNormal (R : Subgroup X) [R.Normal] (P : Subgroup R)
    [P.Characteristic] (x : X) :
    x ∈ ((frattiniAction P).comp (MulAut.conjNormal : X →* MulAut R)).ker ↔
      ActsTriviallyOnFrattiniQuotient (P.map R.subtype) x := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, mem_ker_frattiniAction_iff]
  unfold ActsTriviallyOnFrattiniQuotient
  rw [frattiniIn_map_subtype]
  constructor
  · intro h d hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    refine ⟨_, h d₀ hd₀, ?_⟩
    simp [MulAut.conjNormal_apply]
  · intro h d hd
    obtain ⟨y, hy, hyd⟩ := h (R.subtype d) ⟨d, hd, rfl⟩
    have hy' : y = d⁻¹ * MulAut.conjNormal x d := by
      apply Subtype.ext
      have := hyd
      simpa [MulAut.conjNormal_apply] using this
    rw [← hy']
    exact hy

end CFSG.Quasithin.A36B
