module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoWeyl
public import CFSG.RankThree.GF2n.Smith81.S81BGeom

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)}

theorem card_eq_card_mul_card_map_of_ker {α β : Type} [Group α] [Group β] {L Q S : Subgroup α}
    (f : L →* β) (hf : ∀ s : L, f s = 1 ↔ (s : α) ∈ Q) (hQL : Q ≤ L) (hQS : Q ≤ S)
    (hSL : S ≤ L) :
    Nat.card S = Nat.card Q * Nat.card ↥((S.subgroupOf L).map f) := by
  let g : ↥(S.subgroupOf L) →* β := f.comp (S.subgroupOf L).subtype
  have hrange : g.range = (S.subgroupOf L).map f := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card g.ker = Nat.card Q := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x.1 : ↥L) : α), (hf (x.1 : ↥L)).1 (MonoidHom.mem_ker.mp x.2)⟩
        invFun := fun q => ⟨⟨⟨q.1, hQL q.2⟩, Subgroup.mem_subgroupOf.mpr (hQS q.2)⟩,
          MonoidHom.mem_ker.mpr ((hf ⟨q.1, hQL q.2⟩).2 q.2)⟩
        left_inv := fun x => rfl
        right_inv := fun q => rfl }
  have h1 := g.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, hker] at h1
  have hHS : Nat.card ↥(S.subgroupOf L) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  exact hHS.symm.trans h1.symm

theorem finite_map_aux {α β : Type} [Group α] [Finite α] [Group β] (f : α →* β) (H : Subgroup α) :
    Finite ↥(H.map f) := by
  refine Finite.of_surjective
    (fun x : ↥H => (⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩ : ↥(H.map f))) ?_
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem le_and_map_eq_of_radical {α β : Type} [Group α] [Finite α] [Group β] {L Q T : Subgroup α}
    {R : Subgroup β} (f : L →* β) (hf : ∀ s : L, f s = 1 ↔ (s : α) ∈ Q) (hQL : Q ≤ L)
    (hQT : Q ≤ T) (hsurj : ∀ u ∈ R, ∃ t : L, (t : α) ∈ T ∧ f t = u)
    (hcard : Nat.card ↥T = Nat.card Q * Nat.card ↥R) :
    T ≤ L ∧ (T.subgroupOf L).map f = R := by
  have hQS : Q ≤ T ⊓ L := le_inf hQT hQL
  have hA := card_eq_card_mul_card_map_of_ker f hf hQL hQS inf_le_right
  have hRle : R ≤ ((T ⊓ L).subgroupOf L).map f := by
    intro u hu
    obtain ⟨t, htT, htf⟩ := hsurj u hu
    exact Subgroup.mem_map.mpr
      ⟨t, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨htT, t.2⟩), htf⟩
  haveI := finite_map_aux f ((T ⊓ L).subgroupOf L)
  have hle1 : Nat.card ↥T ≤ Nat.card ↥(T ⊓ L) := by
    rw [hA, hcard]
    exact Nat.mul_le_mul le_rfl (Subgroup.card_le_of_le hRle)
  have hTL : T ⊓ L = T := Subgroup.eq_of_le_of_card_ge inf_le_left hle1
  have hTL' : T ≤ L := by
    rw [← hTL]
    exact inf_le_right
  rw [hTL] at hA hRle
  haveI := finite_map_aux f (T.subgroupOf L)
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hcardM : Nat.card ↥((T.subgroupOf L).map f) = Nat.card ↥R :=
    Nat.eq_of_mul_eq_mul_left hQpos (hA.symm.trans hcard)
  have hRM : R = (T.subgroupOf L).map f := Subgroup.eq_of_le_of_card_ge hRle hcardM.le
  exact ⟨hTL', hRM.symm⟩

end CFSG.RankThree.GF2n.Smith81
