module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fr6
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Tr

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.zpowers_t_inf_J (h : FS79Hyp b t b₁ b₂ J) : Subgroup.zpowers t ⊓ J = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxJ⟩
  rcases h.mem_zpowers_t hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact absurd hxJ h.t_not_mem_J

namespace Std

variable (S : Std b t b₁ b₂ J)

noncomputable def frame (A₁ : Subgroup J6.S6) : Subgroup H := Subgroup.zpowers t ⊔ A₁.map S.ι

include S

theorem comm_zpowers_map (A₁ : Subgroup J6.S6) :
    ∀ a ∈ Subgroup.zpowers t, ∀ c ∈ A₁.map S.ι, Commute a c := by
  intro a ha c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨s, -, rfl⟩ := hc
  exact Commute.zpow_left (show Commute t (S.ι s) from (S.ι_comm_t s).symm) k

theorem mem_frame_iff (A₁ : Subgroup J6.S6) (x : H) :
    x ∈ S.frame A₁ ↔ ∃ s ∈ A₁, x = S.ι s ∨ x = t * S.ι s := by
  constructor
  · intro hx
    obtain ⟨a, ha, c, hc, rfl⟩ := (CFSG.mem_sup_of_commute (S.comm_zpowers_map A₁)).mp hx
    obtain ⟨s, hs, rfl⟩ := hc
    rcases S.hyp.mem_zpowers_t ha with rfl | rfl
    · exact ⟨s, hs, Or.inl (one_mul _)⟩
    · exact ⟨s, hs, Or.inr rfl⟩
  · rintro ⟨s, hs, rfl | rfl⟩
    · exact Subgroup.mem_sup_right ⟨s, hs, rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_right ⟨s, hs, rfl⟩)

theorem ι_mem_frame {A₁ : Subgroup J6.S6} {s : J6.S6} (hs : s ∈ A₁) : S.ι s ∈ S.frame A₁ :=
  Subgroup.mem_sup_right ⟨s, hs, rfl⟩

theorem t_mem_frame (A₁ : Subgroup J6.S6) : t ∈ S.frame A₁ :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers t)

theorem t_ι_mem_frame {A₁ : Subgroup J6.S6} {s : J6.S6} (hs : s ∈ A₁) :
    t * S.ι s ∈ S.frame A₁ :=
  Subgroup.mul_mem _ (S.t_mem_frame A₁) (S.ι_mem_frame hs)

theorem frame_mono {A₁ A₂ : Subgroup J6.S6} (h : A₁ ≤ A₂) : S.frame A₁ ≤ S.frame A₂ :=
  sup_le_sup_left (Subgroup.map_mono h) _

theorem card_frame (A₁ : Subgroup J6.S6) : Nat.card (S.frame A₁) = 2 * Nat.card A₁ := by
  have hdisj : Subgroup.zpowers t ⊓ A₁.map S.ι = ⊥ := by
    rw [eq_bot_iff, ← S.hyp.zpowers_t_inf_J]
    refine inf_le_inf_left _ ?_
    rintro _ ⟨s, -, rfl⟩
    exact S.ι_mem s
  unfold frame
  rw [CFSG.card_sup_eq_mul_of_commute _ _ (S.comm_zpowers_map A₁) hdisj, Nat.card_zpowers,
    S.hyp.ord_t, Subgroup.card_map_of_injective S.ι_injective]

theorem frame_sq {A₁ : Subgroup J6.S6} (hsq : ∀ s ∈ A₁, s * s = 1) :
    ∀ x ∈ S.frame A₁, x * x = 1 := by
  intro x hx
  obtain ⟨s, hs, rfl | rfl⟩ := (S.mem_frame_iff A₁ x).mp hx
  · rw [← map_mul, hsq s hs, map_one]
  · calc t * S.ι s * (t * S.ι s) = (t * t) * (S.ι s * S.ι s) := by
          calc t * S.ι s * (t * S.ι s) = t * (S.ι s * t) * S.ι s := by group
            _ = t * (t * S.ι s) * S.ι s := by rw [S.ι_comm_t s]
            _ = (t * t) * (S.ι s * S.ι s) := by group
      _ = 1 := by rw [S.hyp.t_sq, ← map_mul, hsq s hs, map_one, one_mul]

theorem frame_comm {A₁ : Subgroup J6.S6} (hcomm : ∀ a ∈ A₁, ∀ c ∈ A₁, a * c = c * a) :
    ∀ x ∈ S.frame A₁, ∀ y ∈ S.frame A₁, x * y = y * x := by
  intro x hx y hy
  obtain ⟨s, hs, rfl | rfl⟩ := (S.mem_frame_iff A₁ x).mp hx <;>
  obtain ⟨r, hr, rfl | rfl⟩ := (S.mem_frame_iff A₁ y).mp hy
  · rw [← map_mul, ← map_mul, hcomm s hs r hr]
  · calc S.ι s * (t * S.ι r) = (S.ι s * t) * S.ι r := by group
      _ = (t * S.ι s) * S.ι r := by rw [S.ι_comm_t s]
      _ = t * (S.ι s * S.ι r) := by group
      _ = t * (S.ι r * S.ι s) := by rw [← map_mul, ← map_mul, hcomm s hs r hr]
      _ = (t * S.ι r) * S.ι s := by group
  · calc t * S.ι s * S.ι r = t * (S.ι s * S.ι r) := by group
      _ = t * (S.ι r * S.ι s) := by rw [← map_mul, ← map_mul, hcomm s hs r hr]
      _ = (t * S.ι r) * S.ι s := by group
      _ = S.ι r * (t * S.ι s) := by
        calc (t * S.ι r) * S.ι s = (S.ι r * t) * S.ι s := by rw [S.ι_comm_t r]
          _ = S.ι r * (t * S.ι s) := by group
  · calc t * S.ι s * (t * S.ι r) = t * (S.ι s * t) * S.ι r := by group
      _ = t * (t * S.ι s) * S.ι r := by rw [S.ι_comm_t s]
      _ = (t * t) * (S.ι s * S.ι r) := by group
      _ = (t * t) * (S.ι r * S.ι s) := by rw [← map_mul, ← map_mul, hcomm s hs r hr]
      _ = t * (t * S.ι r) * S.ι s := by group
      _ = t * (S.ι r * t) * S.ι s := by rw [← S.ι_comm_t r]
      _ = t * S.ι r * (t * S.ι s) := by group

theorem tι_mul_self (r : J6.S6) : (t * S.ι r) * (t * S.ι r) = S.ι (r * r) := by
  calc (t * S.ι r) * (t * S.ι r) = t * (S.ι r * t) * S.ι r := by group
    _ = t * (t * S.ι r) * S.ι r := by rw [S.ι_comm_t r]
    _ = (t * t) * (S.ι r * S.ι r) := by group
    _ = S.ι (r * r) := by rw [S.hyp.t_sq, one_mul, map_mul]

theorem comm_of_comm {a c : H} (ha : a = 1 ∨ a = t) (hc : c = 1 ∨ c = t) {r r' : J6.S6}
    (h : (a * S.ι r) * (c * S.ι r') = (c * S.ι r') * (a * S.ι r)) : r * r' = r' * r := by
  have hac : a * c = c * a := by
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> simp
  have ha' : ∀ s : J6.S6, a * S.ι s = S.ι s * a := by
    rcases ha with rfl | rfl
    · intro s
      simp
    · intro s
      exact (S.ι_comm_t s).symm
  have hc' : ∀ s : J6.S6, c * S.ι s = S.ι s * c := by
    rcases hc with rfl | rfl
    · intro s
      simp
    · intro s
      exact (S.ι_comm_t s).symm
  have e1 : (a * S.ι r) * (c * S.ι r') = (a * c) * (S.ι r * S.ι r') := by
    calc (a * S.ι r) * (c * S.ι r') = a * (S.ι r * c) * S.ι r' := by group
      _ = a * (c * S.ι r) * S.ι r' := by rw [← hc' r]
      _ = (a * c) * (S.ι r * S.ι r') := by group
  have e2 : (c * S.ι r') * (a * S.ι r) = (c * a) * (S.ι r' * S.ι r) := by
    calc (c * S.ι r') * (a * S.ι r) = c * (S.ι r' * a) * S.ι r := by group
      _ = c * (a * S.ι r') * S.ι r := by rw [← ha' r']
      _ = (c * a) * (S.ι r' * S.ι r) := by group
  rw [e1, e2, ← hac] at h
  have h3 := mul_left_cancel h
  apply S.ι_injective
  rw [map_mul, map_mul]
  exact h3

theorem E16 (X : Subgroup H) (hXP : X ≤ S.frame J6.R) (hX : Nat.card X = 16)
    (hsq : ∀ x ∈ X, x * x = 1) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    X = S.frame J6.T1 ∨ X = S.frame J6.V1 := by
  have hmem : ∀ x ∈ X, x ∈ S.frame J6.T1 ∨ x ∈ S.frame J6.V1 := by
    intro x hx
    obtain ⟨r, hr, rfl | rfl⟩ := (S.mem_frame_iff J6.R x).mp (hXP hx)
    · have h1 : S.ι (r * r) = 1 := by rw [map_mul]; exact hsq _ hx
      have h2 : r * r = 1 := S.ι_injective (h1.trans (map_one S.ι).symm)
      rcases J6.R_inv_mem r hr h2 with h3 | h3
      · exact Or.inl (S.ι_mem_frame (A₁ := J6.T1) h3)
      · exact Or.inr (S.ι_mem_frame (A₁ := J6.V1) h3)
    · have h1 : S.ι (r * r) = 1 := by rw [← S.tι_mul_self]; exact hsq _ hx
      have h2 : r * r = 1 := S.ι_injective (h1.trans (map_one S.ι).symm)
      rcases J6.R_inv_mem r hr h2 with h3 | h3
      · exact Or.inl (S.t_ι_mem_frame (A₁ := J6.T1) h3)
      · exact Or.inr (S.t_ι_mem_frame (A₁ := J6.V1) h3)
  have hTcard : Nat.card (S.frame J6.T1) = 16 := by rw [S.card_frame, J6.card_T1]
  have hVcard : Nat.card (S.frame J6.V1) = 16 := by rw [S.card_frame, J6.card_V1]
  by_cases hXT : X ≤ S.frame J6.T1
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hXT (by rw [hX, hTcard]))
  by_cases hXV : X ≤ S.frame J6.V1
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hXV (by rw [hX, hVcard]))
  exfalso
  obtain ⟨x, hxX, hxT⟩ := SetLike.not_le_iff_exists.mp hXT
  obtain ⟨y, hyX, hyV⟩ := SetLike.not_le_iff_exists.mp hXV
  have hxV : x ∈ S.frame J6.V1 := (hmem x hxX).resolve_left hxT
  have hyT : y ∈ S.frame J6.T1 := (hmem y hyX).resolve_right hyV
  obtain ⟨r, hr, hxr⟩ := (S.mem_frame_iff J6.V1 x).mp hxV
  obtain ⟨r', hr', hyr⟩ := (S.mem_frame_iff J6.T1 y).mp hyT
  have hrT : r ∉ J6.T1fin := by
    intro hrT
    apply hxT
    rcases hxr with rfl | rfl
    · exact S.ι_mem_frame (A₁ := J6.T1) hrT
    · exact S.t_ι_mem_frame (A₁ := J6.T1) hrT
  have hr'V : r' ∉ J6.V1fin := by
    intro hr'V
    apply hyV
    rcases hyr with rfl | rfl
    · exact S.ι_mem_frame (A₁ := J6.V1) hr'V
    · exact S.t_ι_mem_frame (A₁ := J6.V1) hr'V
  have hxy := hcomm x hxX y hyX
  have hrr : r * r' = r' * r := by
    rcases hxr with rfl | rfl <;> rcases hyr with rfl | rfl
    · exact S.comm_of_comm (Or.inl rfl) (Or.inl rfl) (by simpa using hxy)
    · exact S.comm_of_comm (Or.inl rfl) (Or.inr rfl) (by simpa using hxy)
    · exact S.comm_of_comm (Or.inr rfl) (Or.inl rfl) (by simpa using hxy)
    · exact S.comm_of_comm (Or.inr rfl) (Or.inr rfl) hxy
  exact J6.noncomm_TV r hr hrT r' hr' hr'V hrr

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
