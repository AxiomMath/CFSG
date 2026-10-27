module

public import CFSG.RankThree.GF2n.Stroth80.DictModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] {Q Z M : Subgroup G} {K : Type} [Field K] {γ : G → K}
  (M₀ : Tim79.QuadModel Q Z K γ)

@[expose] def preSub (S : AddSubgroup M₀.E) : Subgroup G where
  carrier := {x | x ∈ Q ∧ M₀.π x ∈ S}
  mul_mem' := by
    rintro a b ⟨haQ, haS⟩ ⟨hbQ, hbS⟩
    exact ⟨Q.mul_mem haQ hbQ, by rw [M₀.π_mul a haQ b hbQ]; exact S.add_mem haS hbS⟩
  one_mem' := ⟨Q.one_mem, by rw [Tim79.QuadModel.pi_one M₀]; exact S.zero_mem⟩
  inv_mem' := by
    rintro a ⟨haQ, haS⟩
    exact ⟨Q.inv_mem haQ, by rw [Tim79.QuadModel.pi_inv M₀ haQ]; exact S.neg_mem haS⟩

theorem Z_le_preSub (hZQ : Z ≤ Q) (S : AddSubgroup M₀.E) : Z ≤ preSub M₀ S := by
  intro z hz
  refine ⟨hZQ hz, ?_⟩
  rw [(M₀.π_ker z (hZQ hz)).mpr hz]
  exact S.zero_mem

theorem img_preSub (S : AddSubgroup M₀.E) : M₀.img (preSub M₀ S) = S := by
  ext e
  constructor
  · rintro ⟨x, hxS, -, rfl⟩
    exact hxS.2
  · intro he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    exact ⟨x, ⟨hxQ, he⟩, hxQ, rfl⟩

variable {φ : ↥M →* Equiv.Perm M₀.E}

end HS9

end CFSG.RankThree.GF2n.Stroth80
