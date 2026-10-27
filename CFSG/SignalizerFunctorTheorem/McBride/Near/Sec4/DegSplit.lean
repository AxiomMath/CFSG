module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.DegBasic

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

variable {Q : Type*} [Group Q]

theorem splitComm (N : Subgroup Q) (n : N) (c : Subgroup.centralizer (N : Set Q)) :
    Commute (N.subtype n) ((Subgroup.centralizer (N : Set Q)).subtype c) :=
  Subgroup.mem_centralizer_iff.mp c.2 n n.2

@[expose] def splitHom (N : Subgroup Q) : N × Subgroup.centralizer (N : Set Q) →* Q :=
  N.subtype.noncommCoprod (Subgroup.centralizer (N : Set Q)).subtype (splitComm N)

theorem splitHom_apply (N : Subgroup Q) (x : N × Subgroup.centralizer (N : Set Q)) :
    splitHom N x = (x.1 : Q) * (x.2 : Q) := rfl

theorem splitHom_bijective (N : Subgroup Q) [N.Normal]
    (h1 : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥)
    (h2 : N ⊔ Subgroup.centralizer (N : Set Q) = ⊤) : Function.Bijective (splitHom N) := by
  refine ⟨?_, ?_⟩
  · rw [splitHom, MonoidHom.noncommCoprod_injective]
    refine ⟨N.subtype_injective, (Subgroup.centralizer (N : Set Q)).subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact h1
  · intro q
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp (h2 ▸ Subgroup.mem_top q)
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hyz⟩

@[expose] noncomputable def splitEquiv (N : Subgroup Q) [N.Normal]
    (h1 : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥)
    (h2 : N ⊔ Subgroup.centralizer (N : Set Q) = ⊤) :
    N × Subgroup.centralizer (N : Set Q) ≃* Q :=
  MulEquiv.ofBijective (splitHom N) (splitHom_bijective N h1 h2)

@[expose] noncomputable def projC (N : Subgroup Q) [N.Normal]
    (h1 : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥)
    (h2 : N ⊔ Subgroup.centralizer (N : Set Q) = ⊤) : Q →* Subgroup.centralizer (N : Set Q) :=
  (MonoidHom.snd _ _).comp (splitEquiv N h1 h2).symm.toMonoidHom

theorem projC_surjective (N : Subgroup Q) [N.Normal]
    (h1 : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥)
    (h2 : N ⊔ Subgroup.centralizer (N : Set Q) = ⊤) :
    Function.Surjective (projC N h1 h2) := by
  intro c
  refine ⟨(splitEquiv N h1 h2) (1, c), ?_⟩
  simp [projC]

theorem ker_projC (N : Subgroup Q) [N.Normal] (h1 : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥)
    (h2 : N ⊔ Subgroup.centralizer (N : Set Q) = ⊤) : (projC N h1 h2).ker = N := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hx' : ((splitEquiv N h1 h2).symm x).2 = 1 := hx
    have h3 : x = (splitEquiv N h1 h2) ((splitEquiv N h1 h2).symm x) := by simp
    have h4 : ((splitEquiv N h1 h2) ((splitEquiv N h1 h2).symm x) : Q) =
        (((splitEquiv N h1 h2).symm x).1 : Q) * (((splitEquiv N h1 h2).symm x).2 : Q) := rfl
    rw [h3, h4, hx']
    simp
  · intro hx
    have h3 : (splitEquiv N h1 h2) (⟨x, hx⟩, 1) = x := by
      show (x : Q) * ((1 : Subgroup.centralizer (N : Set Q)) : Q) = x
      simp
    have h5 : (splitEquiv N h1 h2).symm x = (⟨x, hx⟩, 1) := by
      rw [MulEquiv.symm_apply_eq, h3]
    simp [projC, h5]

theorem permDeg_le_add [Finite Q] (N : Subgroup Q) [N.Normal]
    (h1 : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥)
    (h2 : N ⊔ Subgroup.centralizer (N : Set Q) = ⊤) :
    permDeg Q ≤ permDeg N + permDeg (Subgroup.centralizer (N : Set Q)) :=
  calc permDeg Q = permDeg (N × Subgroup.centralizer (N : Set Q)) :=
        (permDeg_congr (splitEquiv N h1 h2)).symm
    _ ≤ permDeg N + permDeg (Subgroup.centralizer (N : Set Q)) := permDeg_prod_le _ _

end CFSG.SignalizerFunctorTheorem.McBride.Near.Deg
