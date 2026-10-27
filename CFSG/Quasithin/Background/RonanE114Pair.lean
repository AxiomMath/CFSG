module

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IA
public import CFSG.Quasithin.EmptyFaithful.S14620A

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.QuasithinUnique CFSG.Quasithin.B6 CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB
open CFSG.Quasithin.A1b

@[expose] def HasSolvInvPair (Γ : Type) [Group Γ] : Prop :=
  ∃ U P₀ P₁ : Subgroup Γ, IsSylowTwoOf U ⊤ ∧ U ≤ P₀ ∧ U ≤ P₁ ∧ Group.IsSolvable ↥P₀ ∧
    Group.IsSolvable ↥P₁ ∧ P₀ ⊔ P₁ = ⊤ ∧ ∀ α : MulAut Γ, U.map α.toMonoidHom = U →
      P₀.map α.toMonoidHom = P₀ ∧ P₁.map α.toMonoidHom = P₁

theorem hasSolvInvPair_of_unique_orders {Γ : Type} [Group Γ] {U P₀ P₁ : Subgroup Γ}
    (hU : IsSylowTwoOf U ⊤) (hU₀ : U ≤ P₀) (hU₁ : U ≤ P₁) (hs₀ : Group.IsSolvable ↥P₀)
    (hs₁ : Group.IsSolvable ↥P₁) (hgen : P₀ ⊔ P₁ = ⊤)
    (hu₀ : ∀ Y : Subgroup Γ, U ≤ Y → Nat.card Y = Nat.card P₀ → Y = P₀)
    (hu₁ : ∀ Y : Subgroup Γ, U ≤ Y → Nat.card Y = Nat.card P₁ → Y = P₁) : HasSolvInvPair Γ :=
  ⟨U, P₀, P₁, hU, hU₀, hU₁, hs₀, hs₁, hgen, fun α hα =>
    ⟨map_eq_of_unique_card hU₀ hu₀ α hα, map_eq_of_unique_card hU₁ hu₁ α hα⟩⟩

theorem isSolvable_sup_of_normalizes {H : Type} [Group H] [Finite H] {Q T : Subgroup H} (hT : IsPGroup 2 T)
    (hTQ : T ≤ Subgroup.normalizer (Q : Set H)) (hQ : Group.IsSolvable ↥Q) :
    Group.IsSolvable ↥(Q ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : Group.IsSolvable ↥T := by
    have := hT.isNilpotent
    infer_instance
  exact isSolvable_sup_of_le_normalizer_of_isSolvable hTQ hQ hTs

theorem nParam_le_one_of_hasSolvInvPair {Γ : Type} [Group Γ] [Finite Γ] (hP : HasSolvInvPair Γ)
    {H : Type} [Group H] [Finite H] {K T : Subgroup H} (hK : K.Normal) (e₀ : ↥K ≃* Γ)
    (hT : IsSylowTwoOf T ⊤) (hKT : K ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup H) ≤ 1 := by
  obtain ⟨U, P₀, P₁, hU, hU₀, hU₁, hs₀, hs₁, hgen, hinv⟩ := hP
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e₀ hSK hU
  have hα : ∀ t ∈ T, U.map (autK e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (le_normalizer_inf hK ht)
  have hS : ∀ {P : Subgroup Γ}, U ≤ P → T ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype :=
    fun hUP => (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  have hsolv : ∀ {P : Subgroup Γ}, Group.IsSolvable ↥P →
      Group.IsSolvable ↥((P.map e'.symm.toMonoidHom).map K.subtype) := by
    intro P hP
    let f : ↥P ≃* ↥((P.map e'.symm.toMonoidHom).map K.subtype) :=
      (P.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective).trans
        ((P.map e'.symm.toMonoidHom).equivMapOfInjective K.subtype K.subtype_injective)
    exact Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
  have hn₀ : T ≤ Subgroup.normalizer
      (((P₀.map e'.symm.toMonoidHom).map K.subtype : Subgroup H) : Set H) :=
    fun t ht => mem_normalizer_pull e' (hinv _ (hα t ht)).1
  have hn₁ : T ≤ Subgroup.normalizer
      (((P₁.map e'.symm.toMonoidHom).map K.subtype : Subgroup H) : Set H) :=
    fun t ht => mem_normalizer_pull e' (hinv _ (hα t ht)).2
  have hT' : IsSylowIn 2 T ⊤ := ⟨le_top, hT.2.1, hT.2.2⟩
  refine Vol2.Ch11.SecU1.nParam_le_one_of_solvable_pair (D₁ := _ ⊔ T) (D₂ := _ ⊔ T) hT' le_sup_right
    le_sup_right (isSolvable_sup_of_normalizes hT.2.1 hn₀ (hsolv hs₀))
    (isSolvable_sup_of_normalizes hT.2.1 hn₁ (hsolv hs₁)) ?_
  have hQ : (P₀.map e'.symm.toMonoidHom).map K.subtype ⊔
      (P₁.map e'.symm.toMonoidHom).map K.subtype = K := by
    rw [← pull_sup, hgen, pull_top]
  have hKle : K ≤ _ ⊔ T ⊔ (_ ⊔ T) :=
    hQ.symm.le.trans (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
  rw [eq_top_iff, ← hKT]
  exact sup_le hKle (le_sup_of_le_left le_sup_right)

end CFSG.Quasithin.RonanE114
