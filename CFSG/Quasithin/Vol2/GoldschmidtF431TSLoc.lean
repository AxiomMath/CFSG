module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSLift

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45
  CFSG.LieType.BorelTits

universe u

section MaxLocal

variable {D : Type} [Group D] [Finite D]

theorem normalizer_le_of_isMaximalTwoLocal {P : Subgroup D} (hP : IsMaximalTwoLocal P) :
    Subgroup.normalizer (P : Set D) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨R, hR1, hR2, rfl⟩, hmax⟩ := hP
  set Q : Subgroup D := pCoreOf 2 (Subgroup.normalizer (R : Set D)) with hQ
  have hRQ : R ≤ Q := le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hR2
  have hQ1 : Q ≠ ⊥ := fun h => hR1 (le_bot_iff.mp (h ▸ hRQ))
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have h1 : Subgroup.normalizer (R : Set D) ≤ Subgroup.normalizer (Q : Set D) :=
    le_normalizer_pCoreOf 2 _
  have h2 : Subgroup.normalizer (Q : Set D) = Subgroup.normalizer (R : Set D) :=
    hmax _ ⟨Q, hQ1, hQ2, rfl⟩ h1
  calc Subgroup.normalizer ((Subgroup.normalizer (R : Set D) : Subgroup D) : Set D)
      ≤ Subgroup.normalizer (Q : Set D) := normalizer_le_normalizer_pCoreOf 2 _
    _ = Subgroup.normalizer (R : Set D) := h2

variable (A : LieAmalgamExt D) (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

omit [Finite D] in
theorem P1_maxLocal : IsMaximalTwoLocal A.P1 :=
  ((A.yam.2.2 A.P1).mpr (Or.inl rfl)).1

omit [Finite D] in
theorem P2_maxLocal : IsMaximalTwoLocal A.P2 :=
  ((A.yam.2.2 A.P2).mpr (Or.inr rfl)).1

omit [Finite D] in
theorem mem_normalizer_of_autStab {P : Subgroup D} {d : D} (h : MulAut.conj d ∈ autStab P) :
    d ∈ Subgroup.normalizer (P : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have := h x
  rw [MulAut.conj_apply] at this
  exact this

theorem iK_mem_Mb1_iff (d : D) : iK A hgen d ∈ A.Mb1 ↔ d ∈ A.P1 :=
  ⟨fun h => normalizer_le_of_isMaximalTwoLocal (P1_maxLocal A) (mem_normalizer_of_autStab h.2),
    iK_mem_Mb1 A hgen⟩

theorem iK_mem_Mb2_iff (d : D) : iK A hgen d ∈ A.Mb2 ↔ d ∈ A.P2 :=
  ⟨fun h => normalizer_le_of_isMaximalTwoLocal (P2_maxLocal A) (mem_normalizer_of_autStab h.2),
    iK_mem_Mb2 A hgen⟩

end MaxLocal

section Sylow

variable {D H : Type*} [Group D] [Group H] (Φ : D →* H)

theorem isSylowTwoOf_map_inj (hΦ : Function.Injective Φ) {S X : Subgroup D}
    (h : IsSylowTwoOf S X) : IsSylowTwoOf (S.map Φ) (X.map Φ) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_⟩
  · exact h.2.1.of_equiv (Subgroup.equivMapOfInjective S Φ hΦ)
  · have e : ∀ (A B : Subgroup D), (A.subgroupOf B).index = A.relIndex B := fun _ _ => rfl
    have e' : ∀ (A B : Subgroup H), (A.subgroupOf B).index = A.relIndex B := fun _ _ => rfl
    have := h.2.2
    rw [e] at this
    rw [e', Subgroup.relIndex_map_map_of_injective S X hΦ]
    exact this

theorem isSylowTwoOf_of_odd_inf {Y N S : Subgroup H} [N.Normal] (hodd : ¬ 2 ∣ N.index)
    (h : IsSylowTwoOf S (Y ⊓ N)) : IsSylowTwoOf S Y := by
  have hSY : S ≤ Y := h.1.trans inf_le_left
  refine ⟨hSY, h.2.1, ?_⟩
  have e : ∀ (A B : Subgroup H), (A.subgroupOf B).index = A.relIndex B := fun _ _ => rfl
  rw [e]
  have h1 : S.relIndex Y = S.relIndex (Y ⊓ N) * (Y ⊓ N).relIndex Y :=
    (Subgroup.relIndex_mul_relIndex S (Y ⊓ N) Y h.1 inf_le_left).symm
  have h2 : (Y ⊓ N).relIndex Y ∣ N.index := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_dvd_index_of_normal N Y
  have h3 : ¬ 2 ∣ S.relIndex (Y ⊓ N) := by
    have := h.2.2
    rwa [e] at this
  rw [h1]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h4 | h4
  · exact h3 h4
  · exact hodd (h4.trans h2)

end Sylow

section PerfectCore

variable {D : Type} [Group D] [Finite D] (A : LieAmalgamExt D)
  (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
  (hodd : ¬ 2 ∣ (iK A hgen).range.index)

theorem Mb1_inf_range : A.Mb1 ⊓ (iK A hgen).range = A.P1.map (iK A hgen) := by
  ext x
  constructor
  · rintro ⟨hx1, d, rfl⟩
    exact ⟨d, (iK_mem_Mb1_iff A hgen d).mp hx1, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨iK_mem_Mb1 A hgen hd, d, rfl⟩

theorem Mb2_inf_range : A.Mb2 ⊓ (iK A hgen).range = A.P2.map (iK A hgen) := by
  ext x
  constructor
  · rintro ⟨hx1, d, rfl⟩
    exact ⟨d, (iK_mem_Mb2_iff A hgen d).mp hx1, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨iK_mem_Mb2 A hgen hd, d, rfl⟩

include hcen hodd in
theorem perfectCore_Mb1 : perfectCore A.Mb1 = (perfectCore A.P1).map (iK A hgen) := by
  have := range_normal A hgen
  have hodd' : Odd (iK A hgen).range.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  rw [perfectCore_eq_inf_of_odd (Inn := (iK A hgen).range) A.Mb1 hodd', Mb1_inf_range,
    perfectCore_map_of_injective _ (iK_injective A hgen hcen)]

include hcen hodd in
theorem perfectCore_Mb2 : perfectCore A.Mb2 = (perfectCore A.P2).map (iK A hgen) := by
  have := range_normal A hgen
  have hodd' : Odd (iK A hgen).range.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  rw [perfectCore_eq_inf_of_odd (Inn := (iK A hgen).range) A.Mb2 hodd', Mb2_inf_range,
    perfectCore_map_of_injective _ (iK_injective A hgen hcen)]

include hcen hodd in
theorem iK_mem_centerOf_perfectCore_Mb1 {w : D} (hw : w ∈ centerOf (perfectCore A.P1)) :
    iK A hgen w ∈ centerOf (perfectCore A.Mb1) := by
  rw [perfectCore_Mb1 A hgen hcen hodd, centerOf_map_of_injective _ (iK_injective A hgen hcen)]
  exact Subgroup.mem_map_of_mem _ hw

include hcen hodd in
theorem iK_mem_centerOf_perfectCore_Mb2 {w : D} (hw : w ∈ centerOf (perfectCore A.P2)) :
    iK A hgen w ∈ centerOf (perfectCore A.Mb2) := by
  rw [perfectCore_Mb2 A hgen hcen hodd, centerOf_map_of_injective _ (iK_injective A hgen hcen)]
  exact Subgroup.mem_map_of_mem _ hw

end PerfectCore

end CFSG.Quasithin.H13.F431.Lift
