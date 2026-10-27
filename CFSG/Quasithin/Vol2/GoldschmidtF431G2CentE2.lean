module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentE1
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentMix

public section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem commute_rU_of_mem {δ : Fin Tag.G2.rank → ℤ} (hδ : δ ∈ [rA, rU, rB, rC]) (s : K) :
    Commute (gX δ s) (gX rU (1 : K)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
  rcases hδ with rfl | rfl | rfl | rfl
  · exact comm_au s 1
  · exact gX_comm_self _ _ _
  · exact (comm_ub 1 s).symm
  · exact (comm_uc 1 s).symm

theorem commute_rR_of_mem {δ : Fin Tag.G2.rank → ℤ} (hδ : δ ∈ [rR, rB, rC]) (s : K) :
    Commute (gX δ s) (gX rR (1 : K)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
  rcases hδ with rfl | rfl | rfl
  · exact gX_comm_self _ _ _
  · exact (comm_rb 1 s).symm
  · exact (comm_rc 1 s).symm

theorem commute_of_commute_mul_right {M : Type*} [Group M] {τ a c : M}
    (h : Commute τ (a * c)) (hc : Commute τ c) : Commute τ a := by
  have h1 : τ * a * c = a * τ * c := by
    calc τ * a * c = τ * (a * c) := by rw [mul_assoc]
      _ = (a * c) * τ := h.eq
      _ = a * (c * τ) := by rw [mul_assoc]
      _ = a * (τ * c) := by rw [hc.eq]
      _ = a * τ * c := by rw [mul_assoc]
  exact mul_right_cancel h1

theorem not_commute_rU {ν β γ : K} (hν : ν ≠ 0) :
    ¬ Commute (gX rU (1 : K)) (gX rV ν * gX rB β * gX rC γ) := by
  intro h
  have h1 : Commute (gX rU (1 : K)) (gX rV ν * gX rB β) :=
    commute_of_commute_mul_right h (comm_uc 1 γ)
  have h2 : Commute (gX rU (1 : K)) (gX rV ν) :=
    commute_of_commute_mul_right h1 (comm_ub 1 β)
  have h3 : ⁅gX rU (1 : K), gX rV ν⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h2.eq
  rw [rel_uv, one_mul] at h3
  exact hν (gX_eq_one h3)

theorem not_commute_rR {ν β γ : K} (hν : ν ≠ 0) :
    ¬ Commute (gX rR (1 : K)) (gX rV ν * gX rB β * gX rC γ) := by
  intro h
  have h1 : Commute (gX rR (1 : K)) (gX rV ν * gX rB β) :=
    commute_of_commute_mul_right h (comm_rc 1 γ)
  have h2 : Commute (gX rR (1 : K)) (gX rV ν) :=
    commute_of_commute_mul_right h1 (comm_rb 1 β)
  have h3 : ⁅gX rR (1 : K), gX rV ν⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h2.eq
  rw [rel_rv, one_mul] at h3
  exact hν (gX_eq_one h3)

theorem conj_gX_mem {w : WeylGroup Tag.G2} {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot Tag.G2 δ)
    (s : K) :
    canonicalRep (coxeterSystem Tag.G2) K w * gX δ s *
      (canonicalRep (coxeterSystem Tag.G2) K w)⁻¹ ∈ rootSpan Tag.G2 K {w • δ} :=
  conj_mem_rootSpan_image hδ (pinnedX_mem_rootSpan (Set.mem_singleton _) s)

theorem commute_conj_prod {w : WeylGroup Tag.G2} {τ : ModGL Tag.G2 K}
    {S : List (Fin Tag.G2.rank → ℤ)}
    (hS : ∀ δ ∈ [w • rV, w • rB, w • rC], 0 < height δ → δ ∈ S)
    (hτ : ∀ δ ∈ S, ∀ s : K, Commute (gX δ s) τ) {ν β γ : K}
    (hy : canonicalRep (coxeterSystem Tag.G2) K w * (gX rV ν * gX rB β * gX rC γ) *
      (canonicalRep (coxeterSystem Tag.G2) K w)⁻¹ ∈ borelGroup Tag.G2 K) :
    Commute τ (canonicalRep (coxeterSystem Tag.G2) K w * (gX rV ν * gX rB β * gX rC γ) *
      (canonicalRep (coxeterSystem Tag.G2) K w)⁻¹) := by
  set n := canonicalRep (coxeterSystem Tag.G2) K w with hn
  have hrv : IsRoot Tag.G2 rV := (pos_TVBC rV (Or.inl rfl)).1
  have hrb : IsRoot Tag.G2 rB := (pos_TVBC rB (Or.inr (Or.inl rfl))).1
  have hrc : IsRoot Tag.G2 rC := (pos_TVBC rC (Or.inr (Or.inr rfl))).1
  have hprod : n * (gX rV ν * gX rB β * gX rC γ) * n⁻¹ =
      (n * gX rV ν * n⁻¹) * (n * gX rB β * n⁻¹) * (n * gX rC γ * n⁻¹) := by group
  rw [hprod] at hy ⊢
  have h12 : Commute (n * gX rV ν * n⁻¹) (n * gX rB β * n⁻¹) :=
    (comm_vb ν β).map (MulAut.conj n)
  have h13 : Commute (n * gX rV ν * n⁻¹) (n * gX rC γ * n⁻¹) :=
    (comm_vc ν γ).map (MulAut.conj n)
  have h23 : Commute (n * gX rB β * n⁻¹) (n * gX rC γ * n⁻¹) :=
    (comm_bc β γ).map (MulAut.conj n)
  have hle : posUnipotent Tag.G2 K ≤ borelGroup Tag.G2 K := le_sup_right
  have hpos : ∀ {δ : Fin Tag.G2.rank → ℤ} {s : K}, IsRoot Tag.G2 δ → 0 < height (w • δ) →
      n * gX δ s * n⁻¹ ∈ borelGroup Tag.G2 K := by
    intro δ s hδ hh
    refine hle (rootSpan_le_posUnipotent (S := {w • δ}) (fun α hα => ?_) (conj_gX_mem hδ s))
    rw [Set.mem_singleton_iff] at hα
    subst hα
    exact ⟨IsRoot.smul hδ w, hh⟩
  have hneg : ∀ {δ : Fin Tag.G2.rank → ℤ} {s : K}, IsRoot Tag.G2 δ → ¬ 0 < height (w • δ) →
      n * gX δ s * n⁻¹ ∈ negUnipotent Tag.G2 K := by
    intro δ s hδ hh
    refine rootSpan_le_negUnipotent (S := {w • δ}) (fun α hα => ?_) (conj_gX_mem hδ s)
    rw [Set.mem_singleton_iff] at hα
    subst hα
    refine ⟨IsRoot.smul hδ w, ?_⟩
    rcases IsRoot.height_pos_or_neg (IsRoot.smul hδ w) with h | h
    · exact absurd h hh
    · exact h
  have hform : ∀ {δ : Fin Tag.G2.rank → ℤ} {s : K}, IsRoot Tag.G2 δ →
      ∃ s' : K, n * gX δ s * n⁻¹ = gX (w • δ) s' := fun hδ =>
    mem_rootSpan_singleton_iff.1 (conj_gX_mem hδ _)
  refine commute_mixed_prod (borelGroup Tag.G2 K) (negUnipotent Tag.G2 K)
    borelGroup_inf_negUnipotent h12 h13 h23 (p₁ := 0 < height (w • rV))
    (p₂ := 0 < height (w • rB)) (p₃ := 0 < height (w • rC)) (hpos hrv) (hneg hrv) (hpos hrb)
    (hneg hrb) (hpos hrc) (hneg hrc) hy ?_ ?_ ?_
  · intro hp
    obtain ⟨s', hs'⟩ := hform (s := ν) hrv
    rw [hs']
    exact (hτ _ (hS _ (by simp) hp) _).symm
  · intro hp
    obtain ⟨s', hs'⟩ := hform (s := β) hrb
    rw [hs']
    exact (hτ _ (hS _ (by simp) hp) _).symm
  · intro hp
    obtain ⟨s', hs'⟩ := hform (s := γ) hrc
    rw [hs']
    exact (hτ _ (hS _ (by simp) hp) _).symm

theorem cent_gX_v_le {g : ModGL Tag.G2 K} (hg : g ∈ adjointGroup Tag.G2 K)
    (hgc : g * gX rV (1 : K) = gX rV (1 : K) * g) :
    g ∈ parabolicSubgroup Tag.G2 K {i0} := by
  have hg' : g ∈ ⋃ w, bruhatCell Tag.G2 K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem Tag.G2) K w with hn
  set t : ModGL Tag.G2 K := gX rV 1 with ht
  have htA : t ∈ rootSpan Tag.G2 K TVBC :=
    pinnedX_mem_rootSpan (show rV ∈ TVBC from Or.inl rfl) 1
  have hnormA : ∀ b ∈ borelGroup Tag.G2 K, b * t * b⁻¹ ∈ rootSpan Tag.G2 K TVBC := fun b hb =>
    (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_TVBC hb) t).1 htA
  have hnormV : ∀ b ∈ borelGroup Tag.G2 K, ∀ y ∈ rootSpan Tag.G2 K TBC,
      b * y * b⁻¹ ∈ rootSpan Tag.G2 K TBC := fun b hb y hy =>
    (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_TBC hb) y).1 hy
  have ht₂ : b₂ * t * b₂⁻¹ ∈ rootSpan Tag.G2 K TVBC := hnormA b₂ hb₂
  obtain ⟨ν', β', γ', ht₂eq⟩ := mem_rootSpan_TVBC_iff.1 ht₂
  have hy : n * (b₂ * t * b₂⁻¹) * n⁻¹ = b₁⁻¹ * t * b₁ := by
    have h1 : b₁ * n * b₂ * t * (b₁ * n * b₂)⁻¹ = t := by
      rw [hgc, mul_inv_cancel_right]
    calc n * (b₂ * t * b₂⁻¹) * n⁻¹
        = b₁⁻¹ * (b₁ * n * b₂ * t * (b₁ * n * b₂)⁻¹) * b₁ := by group
      _ = b₁⁻¹ * t * b₁ := by rw [h1]
  have hyA : b₁⁻¹ * t * b₁ ∈ rootSpan Tag.G2 K TVBC := by
    have := hnormA b₁⁻¹ (inv_mem hb₁)
    simpa using this
  obtain ⟨ν'', β'', γ'', hyeq⟩ := mem_rootSpan_TVBC_iff.1 hyA
  have hν'' : ν'' ≠ 0 := by
    intro h0
    have hyV : b₁⁻¹ * t * b₁ ∈ rootSpan Tag.G2 K TBC := by
      rw [hyeq, h0]
      have : gX rV (0 : K) = 1 := gX_zero rV
      rw [this, one_mul]
      exact mem_rootSpan_TBC_iff.2 ⟨β'', γ'', rfl⟩
    have htV : t ∈ rootSpan Tag.G2 K TBC := by
      have := hnormV b₁ hb₁ _ hyV
      simpa [mul_assoc] using this
    exact gX_rV_not_mem_TBC one_ne_zero htV
  have hy₂ : n * (gX rV ν' * gX rB β' * gX rC γ') * n⁻¹ =
      gX rV ν'' * gX rB β'' * gX rC γ'' := by
    rw [← ht₂eq, hy, hyeq]
  have hBy : n * (gX rV ν' * gX rB β' * gX rC γ') * n⁻¹ ∈ borelGroup Tag.G2 K := by
    have hle : posUnipotent Tag.G2 K ≤ borelGroup Tag.G2 K := le_sup_right
    have htU : t ∈ posUnipotent Tag.G2 K := rootSpan_le_posUnipotent (S := TVBC) pos_TVBC htA
    rw [← ht₂eq, hy]
    exact (borelGroup Tag.G2 K).mul_mem ((borelGroup Tag.G2 K).mul_mem (inv_mem hb₁) (hle htU)) hb₁
  rcases weyl_cases_v w with hv | hcase | hcase
  · exact bruhatCell_subset_parabolicSubgroup
      (mem_parabolicWeylGroup_of_coord (A := {i0}) _ w rfl (weyl_fixes_v hv)).1 hw
  · exfalso
    have hc := commute_conj_prod (τ := gX rU (1 : K)) (S := [rA, rU, rB, rC]) hcase
      (fun δ hδ s => commute_rU_of_mem hδ s) hBy
    rw [hy₂] at hc
    exact not_commute_rU hν'' hc
  · exfalso
    have hc := commute_conj_prod (τ := gX rR (1 : K)) (S := [rR, rB, rC]) hcase
      (fun δ hδ s => commute_rR_of_mem hδ s) hBy
    rw [hy₂] at hc
    exact not_commute_rR hν'' hc

end CFSG.Quasithin.H13.F431.G2.Cent
