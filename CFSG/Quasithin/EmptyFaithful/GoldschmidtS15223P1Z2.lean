module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Gen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

@[expose] def z2Of (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {z | z ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ∧ z ^ 2 = 1}

omit [Finite G] in
theorem quasithinV2_eq_commutator (X : Subgroup G) : quasithinV2 X = ⁅z2Of X, X⁆ := rfl

omit [Finite G] in
theorem z2Of_le_inf (X : Subgroup G) :
    z2Of X ≤ pCoreOf 2 X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

omit [Finite G] in
theorem z2Of_le_pCoreOf (X : Subgroup G) : z2Of X ≤ pCoreOf 2 X := (z2Of_le_inf X).trans inf_le_left

omit [Finite G] in
theorem z2Of_le_centralizer (X : Subgroup G) :
    z2Of X ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) := (z2Of_le_inf X).trans inf_le_right

omit [Finite G] in
theorem pCoreOf_le_centralizer_z2Of (X : Subgroup G) :
    pCoreOf 2 X ≤ Subgroup.centralizer (z2Of X : Set G) := by
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (z2Of_le_centralizer X hz) p hp).symm

omit [Finite G] in
theorem z2Of_comm (X : Subgroup G) : ∀ a ∈ z2Of X, ∀ b ∈ z2Of X, a * b = b * a := fun a ha _ hb =>
  Subgroup.mem_centralizer_iff.mp (z2Of_le_centralizer X hb) a (z2Of_le_pCoreOf X ha)

omit [Finite G] in
theorem z2Of_sq (X : Subgroup G) : ∀ z ∈ z2Of X, z ^ 2 = 1 := by
  intro z hz
  unfold z2Of at hz
  induction hz using Subgroup.closure_induction with
  | mem g hg => exact hg.2
  | one => simp
  | mul a b hxa hxb ha hb =>
    have hc : Commute a b := z2Of_comm X a hxa b hxb
    rw [hc.mul_pow, ha, hb, one_mul]
  | inv a _ ha => rw [inv_pow, ha, inv_one]

omit [Finite G] in
theorem isElemAbelian_z2Of (X : Subgroup G) : IsElemAbelian 2 (z2Of X) :=
  ⟨⟨⟨fun a b => Subtype.ext (z2Of_comm X _ a.2 _ b.2)⟩⟩, z2Of_sq X⟩

omit [Finite G] in
theorem isPGroup_z2Of (X : Subgroup G) : IsPGroup 2 (z2Of X) := fun g =>
  ⟨1, Subtype.ext (by simpa using z2Of_sq X g.1 g.2)⟩

theorem normalizer_le_normalizer_z2Of (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (z2Of X : Set G) := by
  intro g hg
  have hgP : g ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 X hg
  have hgiP : g⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) := inv_mem hgP
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  unfold z2Of at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨hzI, hz2⟩ := hz
    obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hzI
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hgP z).mp hzP
    · rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : g⁻¹ * p * g ∈ pCoreOf 2 X := by
        simpa using (Subgroup.mem_normalizer_iff.mp hgiP p).mp hp
      have hc := Subgroup.mem_centralizer_iff.mp hzC _ hp'
      calc p * (g * z * g⁻¹) = g * ((g⁻¹ * p * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * p * g)) * g⁻¹ := by rw [hc]
        _ = g * z * g⁻¹ * p := by group
    · rw [conj_pow, hz2]
      group
  | one => simp
  | mul a b _ _ ha hb => simpa [mul_assoc] using (Subgroup.closure _).mul_mem ha hb
  | inv a _ ha => simpa [mul_assoc] using (Subgroup.closure _).inv_mem ha

end S15223

end CFSG.Quasithin
