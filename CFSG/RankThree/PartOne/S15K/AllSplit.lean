module

public import CFSG.RankThree.PartOne.S15K.KF158A
public import CFSG.RankThree.PartOne.S15K.CovAt

public section

namespace CFSG.RankThree.PartOne.S15K

open Equiv CFSG CFSG.RankThree.PartOne CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem s4_swap {R : Type*} [Group R] (σ : R ≃* Perm (Fin 4)) (D : Set R)
    (hconj : ∀ x t : R, t ∈ D → x * t * x⁻¹ ∈ D) (hsq : ∀ t ∈ D, t * t = 1) (hne1 : ∀ t ∈ D, t ≠ 1)
    (hF2 : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → x * y = y * x → x * y ∉ D) {t : R} (ht : t ∈ D) :
    ∃ i j : Fin 4, i ≠ j ∧ σ t = swap i j := by
  have hmem : ∀ y : Perm (Fin 4), (∃ g : Perm (Fin 4), g * σ t * g⁻¹ = y) → σ.symm y ∈ D := by
    rintro y ⟨g, rfl⟩
    have := hconj (σ.symm g) t ht
    simpa using this
  have hσt1 : σ t * σ t = 1 := by rw [← map_mul, hsq t ht, map_one]
  have hσt2 : σ t ≠ 1 := fun h => hne1 t ht (σ.injective (by rw [h, map_one]))
  rcases perm4_invol _ hσt1 hσt2 with hdt | hs
  · exfalso
    obtain ⟨x, y, hx, hy, hxy⟩ := perm4_dt_two
    obtain ⟨g₁, hg₁⟩ := perm4_dt_conj _ _ hdt hx
    obtain ⟨g₂, hg₂⟩ := perm4_dt_conj _ _ hdt hy
    obtain ⟨hcomm, hdt'⟩ := perm4_dt_comm x y hx hy hxy
    obtain ⟨g₃, hg₃⟩ := perm4_dt_conj _ _ hdt hdt'
    have hxD : σ.symm x ∈ D := hmem x ⟨g₁, hg₁⟩
    have hyD : σ.symm y ∈ D := hmem y ⟨g₂, hg₂⟩
    have hxyD : σ.symm (x * y) ∈ D := hmem _ ⟨g₃, hg₃⟩
    refine hF2 _ hxD _ hyD (fun h => hxy (σ.symm.injective h)) ?_
      (by have := hxyD; rwa [map_mul] at this)
    rw [← map_mul, ← map_mul, hcomm]
  · exact hs

theorem s4_conj {R : Type*} [Group R] (σ : R ≃* Perm (Fin 4)) (D : Set R)
    (hconj : ∀ x t : R, t ∈ D → x * t * x⁻¹ ∈ D) (hsq : ∀ t ∈ D, t * t = 1) (hne1 : ∀ t ∈ D, t ≠ 1)
    (hF2 : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → x * y = y * x → x * y ∉ D) {s t : R} (hs : s ∈ D)
    (ht : t ∈ D) : ∃ x : R, s = x * t * x⁻¹ := by
  obtain ⟨i, j, hij, hσt⟩ := s4_swap σ D hconj hsq hne1 hF2 ht
  obtain ⟨k, l, hkl, hσs⟩ := s4_swap σ D hconj hsq hne1 hF2 hs
  obtain ⟨g, hg⟩ := perm4_swap_conj i j k l hij hkl
  refine ⟨σ.symm g, σ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hσs, hσt]
  exact hg.symm

variable {G : Type} [Group G] [Finite G]

theorem allSplit_one {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (σ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 4)) {t₀ : MulAut E}
    (ht₀ : t₀ ∈ reflectionSet p E) (hsp : SplitKt p E t₀) :
    ∀ s ∈ reflectionSet p E, SplitKt p E s := by
  intro s hs
  have C := reflCtx_of_hyp h
  obtain ⟨g, hg, hKF⟩ := hsp
  obtain ⟨x, hx⟩ := s4_conj σ (refSetR p E) (refSetR_conj C.prime) (fun t ht => refSetR_sq ht)
    (fun t ht => refSetR_ne_one ht) (fun x hx y hy hne hc => refSetR_F2 C hx hy hne hc)
    (s := ⟨s, Subgroup.subset_closure hs⟩) (t := ⟨t₀, Subgroup.subset_closure ht₀⟩) hs ht₀
  obtain ⟨⟨w, hw⟩, hwx⟩ := reflectionGroup_le_torusWeyl p E x.2
  refine ⟨g, hg, ?_⟩
  have hconj := hKF.conj hw
  have e : s = conjAut E w hw * t₀ * (conjAut E w hw)⁻¹ := by
    have h1 : conjAut E w hw = (x : MulAut E) := hwx
    rw [h1]
    exact congrArg Subtype.val hx
  rw [e]
  exact hconj

@[expose] def KF158AllSplitBC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
    (Outcome152Two p E A (lieGenerated p E) ∨ Outcome152Three p E A (lieGenerated p E)) →
    ∀ s ∈ reflectionSet p E, SplitKt p E s

theorem kf158AllSplit_of_parts (hA : KF158ASplit) (hBC : KF158AllSplitBC) : KF158AllSplit := by
  intro G _ _ p A c L E h15 hF hout s hs
  rcases hout with h1 | h2 | h3
  · obtain ⟨t₀, ht₀, hsp⟩ := hA G p A c L E h15 hF (Or.inl h1)
    obtain ⟨f, -, -, -, ⟨σ⟩, -⟩ := h1
    exact allSplit_one h15.h12 σ ht₀ hsp s hs
  · exact hBC G p A c L E h15 hF (Or.inl h2) s hs
  · exact hBC G p A c L E h15 hF (Or.inr h3) s hs

end CFSG.RankThree.PartOne.S15K
