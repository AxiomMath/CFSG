module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.M24Base

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

variable {A : Type} [Group A] [Finite A]

theorem exists_sylow_le (hA : Nat.card A = 244823040) {X : Subgroup A}
    (hX : 1024 ∣ Nat.card X) : ∃ T : Subgroup A, IsSylowTwoOf T ⊤ ∧ T ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 X))
  refine ⟨(P : Subgroup X).map X.subtype, ?_, ?_⟩
  · rw [K1.isSylowTwoOf_top_iff]
    refine ⟨P.isPGroup'.map X.subtype, ?_⟩
    rw [Subgroup.index_map_subtype]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact P.not_dvd_index h
    · have h1 := X.card_mul_index
      rw [hA] at h1
      obtain ⟨a, ha⟩ := hX
      obtain ⟨b, hb⟩ := h
      rw [ha, hb] at h1
      have h3 : 2048 ∣ 244823040 := ⟨a * b, by rw [← h1]; ring⟩
      norm_num at h3
  · rintro _ ⟨x, -, rfl⟩
    exact x.2

theorem card_normalizer_of_radical
    (hA : Nonempty (A ≃* ↥NativeSporadic.M24)) {R X : Subgroup A}
    (hXN : X ≤ Subgroup.normalizer (R : Set A)) (hX : 1024 ∣ Nat.card X)
    (hrad : pCoreOf 2 (Subgroup.normalizer (R : Set A)) = R)
    (htop : Subgroup.normalizer (R : Set A) ≠ ⊤) :
    (Nat.card (Subgroup.normalizer (R : Set A)) = 322560 ∧ Nat.card R = 16) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 64512 ∧ Nat.card R = 64) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 138240 ∧ Nat.card R = 64) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 21504 ∧ Nat.card R = 128) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 9216 ∧ Nat.card R = 256) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 3072 ∧ Nat.card R = 512) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 1024 ∧ Nat.card R = 1024) := by
  obtain ⟨e⟩ := hA
  have hcA : Nat.card A = 244823040 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.m24_card]
  obtain ⟨T, hT, hTX⟩ := exists_sylow_le hcA hX
  rcases CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_overgroups ⟨e⟩ hT (hTX.trans hXN) with
    h | ⟨m, hm, hord, ho2, -⟩
  · exact absurd h htop
  · rw [hrad] at ho2
    simp only [CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hord, ho2⟩)))))
    · exact Or.inl ⟨hord, ho2⟩
    · exact Or.inr (Or.inl ⟨hord, ho2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hord, ho2⟩))))

omit [Finite A] in
theorem normalizer_ne_top [IsSimpleGroup A] {R : Subgroup A} (hR1 : R ≠ ⊥) (hRt : R ≠ ⊤) :
    Subgroup.normalizer (R : Set A) ≠ ⊤ := by
  intro h
  have hn : R.Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h1 | h1
  · exact hR1 h1
  · exact hRt h1

end CFSG.Quasithin.KGC31.M24

end
