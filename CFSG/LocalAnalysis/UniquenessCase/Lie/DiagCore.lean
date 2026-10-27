module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {X : Type} [Group X]

@[expose] def uc22pdiag_Inv (U : Subgroup X) (A : Set (MulAut X)) (P : Subgroup X) : Prop :=
  normalizer (U : Set X) ≤ P ∧ P ≠ ⊤ ∧ ∀ α ∈ A, ∀ x : X, x ∈ P ↔ α x ∈ P

@[expose] def uc22pdiag_join (U : Subgroup X) (A : Set (MulAut X)) : Subgroup X :=
  ⨆ (P : Subgroup X) (_ : uc22pdiag_Inv U A P), P

theorem uc22pdiag_le_join {U : Subgroup X} {A : Set (MulAut X)} {P : Subgroup X}
    (h : uc22pdiag_Inv U A P) : P ≤ uc22pdiag_join U A :=
  le_iSup₂ (f := fun (P : Subgroup X) (_ : uc22pdiag_Inv U A P) => P) P h

theorem uc22pdiag_isCoatom_map_aut (α : MulAut X) {Q : Subgroup X} (h : IsCoatom Q) :
    IsCoatom (Q.map α.toMonoidHom) :=
  (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup α) Q).2 h

theorem uc22pdiag_join_eq_top_of_pair {U : Subgroup X} {A : Set (MulAut X)} {Q₁ Q₂ : Subgroup X}
    (hsup : Q₁ ⊔ Q₂ = ⊤) (i₁ : uc22pdiag_Inv U A Q₁) (i₂ : uc22pdiag_Inv U A Q₂) :
    uc22pdiag_join U A = ⊤ := by
  rw [eq_top_iff, ← hsup]
  exact sup_le (uc22pdiag_le_join i₁) (uc22pdiag_le_join i₂)

theorem uc22pdiag_mem_normalizer_iff_of_aut {V : Subgroup X} (β : MulAut X) (hβ : ∀ x, x ∈ V ↔ β x ∈ V)
    (x : X) : β x ∈ normalizer (V : Set X) ↔ x ∈ normalizer (V : Set X) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h w
    have h1 := h (β w)
    have e : β x * β w * (β x)⁻¹ = β (x * w * x⁻¹) := by simp
    rw [e, ← hβ, ← hβ] at h1
    exact h1
  · intro h w
    obtain ⟨w', rfl⟩ := β.surjective w
    have h1 := h w'
    have e : β x * β w' * (β x)⁻¹ = β (x * w' * x⁻¹) := by simp
    rw [e, ← hβ, ← hβ]
    exact h1

theorem uc22pdiag_map_normalizer_eq_of_aut {V : Subgroup X} (β : MulAut X) (hβ : ∀ x, x ∈ V ↔ β x ∈ V) :
    (normalizer (V : Set X)).map β.toMonoidHom = normalizer (V : Set X) := by
  ext y
  obtain ⟨x, rfl⟩ := β.surjective y
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  exact (uc22pdiag_mem_normalizer_iff_of_aut β hβ x).symm

theorem uc22pdiag_map_eq_iff_aut (β : MulAut X) (Q : Subgroup X) :
    Q.map β.toMonoidHom = Q ↔ ∀ x, x ∈ Q ↔ β x ∈ Q := by
  constructor
  · intro h x
    have h1 := Subgroup.mem_map_equiv (f := β) (K := Q) (x := β x)
    rw [MulEquiv.symm_apply_apply, h] at h1
    exact h1.symm
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := β.surjective y
    rw [mem_map_equiv, MulEquiv.symm_apply_apply]
    exact h x

theorem uc22pdiag_map_conj_eq_iff (V : Subgroup X) (g : X) :
    V.map (MulAut.conj g).toMonoidHom = V ↔ g ∈ normalizer (V : Set X) := by
  rw [uc22pdiag_map_eq_iff_aut, mem_normalizer_iff]
  simp [MulAut.conj_apply]

@[expose] def uc22pdiag_InvPair (X : Type) [Group X] (V : Subgroup X) : Prop :=
  ∃ Q₁ Q₂ : Subgroup X, Q₁ ≠ ⊤ ∧ Q₂ ≠ ⊤ ∧ Q₁ ⊔ Q₂ = ⊤ ∧
    ∀ α : MulAut X, V.map α.toMonoidHom = V →
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂

theorem uc22pdiag_join_eq_top_of_invPair [IsSimpleGroup X] {V : Subgroup X} (h : uc22pdiag_InvPair X V)
    (A : Set (MulAut X)) (hA : ∀ α ∈ A, ∀ x, x ∈ V ↔ α x ∈ V) : uc22pdiag_join V A = ⊤ := by
  obtain ⟨Q₁, Q₂, h1, h2, hsup, hinv⟩ := h
  have key : ∀ Q : Subgroup X, Q ≠ ⊤ → Q ≠ ⊥ →
      (∀ α : MulAut X, V.map α.toMonoidHom = V → Q.map α.toMonoidHom = Q) →
      uc22pdiag_Inv V A (Q ⊔ normalizer (V : Set X)) := by
    intro Q hQ hQ0 hinvQ
    have hN : normalizer (V : Set X) ≤ normalizer (Q : Set X) := by
      intro g hg
      have hV := (uc22pdiag_map_conj_eq_iff V g).2 hg
      have hQg := (uc22pdiag_map_eq_iff_aut _ Q).1 (hinvQ (MulAut.conj g) hV)
      rw [mem_normalizer_iff]
      intro x
      simpa [MulAut.conj_apply] using hQg x
    refine ⟨le_sup_right, ?_, fun α hα x => ?_⟩
    · intro htop
      have hle : Q ⊔ normalizer (V : Set X) ≤ normalizer (Q : Set X) :=
        sup_le (le_normalizer) hN
      rw [htop, top_le_iff, normalizer_eq_top_iff] at hle
      haveI : Q.Normal := hle
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with h | h
      exacts [hQ0 h, hQ h]
    · have hV : V.map α.toMonoidHom = V := (uc22pdiag_map_eq_iff_aut α V).2 (hA α hα)
      have hQα := hinvQ α hV
      have hNα := uc22pdiag_map_normalizer_eq_of_aut α (hA α hα)
      refine (uc22pdiag_map_eq_iff_aut α _).1 ?_ x
      rw [Subgroup.map_sup, hQα, hNα]
  have hne : ∀ Q Q' : Subgroup X, Q ⊔ Q' = ⊤ → Q' ≠ ⊤ → Q ≠ ⊥ := by
    intro Q Q' hsup hQ' hQ0
    apply hQ'
    rw [hQ0, bot_sup_eq] at hsup
    exact hsup
  refine uc22pdiag_join_eq_top_of_pair (Q₁ := Q₁ ⊔ normalizer (V : Set X))
    (Q₂ := Q₂ ⊔ normalizer (V : Set X)) ?_
    (key Q₁ h1 (hne Q₁ Q₂ hsup h2) fun α hα => (hinv α hα).1)
    (key Q₂ h2 (hne Q₂ Q₁ (by rwa [sup_comm]) h1) fun α hα => (hinv α hα).2)
  rw [eq_top_iff, ← hsup]
  exact sup_le_sup le_sup_left le_sup_left

@[expose] def uc22pdiag_All (M : Type) [Group M] : Prop :=
  ∀ (V : Sylow 2 M) (B : Set (MulAut M)),
    (∀ β ∈ B, ∀ x, x ∈ (V : Subgroup M) ↔ β x ∈ (V : Subgroup M)) →
      uc22pdiag_join (V : Subgroup M) B = ⊤

theorem uc22pdiag_all_of_invPairs {M : Type} [Group M] [IsSimpleGroup M]
    (h : ∀ V : Sylow 2 M, uc22pdiag_InvPair M V) : uc22pdiag_All M :=
  fun V B hB => uc22pdiag_join_eq_top_of_invPair (h V) B hB

theorem uc22pdiag_map_normalizer_le {Y : Type} [Group Y] (π : X →* Y) (hπ : Function.Surjective π)
    (U : Subgroup X) :
    (normalizer (U : Set X)).map π ≤ normalizer ((U.map π : Subgroup Y) : Set Y) := by
  rintro _ ⟨n, hn, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  constructor
  · rintro ⟨u, hu, hux⟩
    refine ⟨n * u * n⁻¹, (mem_normalizer_iff.1 hn u).1 hu, ?_⟩
    simp [hux]
  · rintro ⟨u, hu, hux⟩
    refine ⟨n⁻¹ * u * n, (mem_normalizer_iff.1 (inv_mem hn) u).1 hu |> fun h => by simpa using h, ?_⟩
    have h1 : π n * π x * (π n)⁻¹ = π u := by simpa using hux.symm
    calc π (n⁻¹ * u * n) = (π n)⁻¹ * π u * π n := by simp
      _ = (π n)⁻¹ * (π n * π x * (π n)⁻¹) * π n := by rw [h1]
      _ = π x := by group

theorem uc22pdiag_join_pullback {Y : Type} [Group Y] [Nontrivial Y] (π : X →* Y)
    (hπ : Function.Surjective π) (U : Subgroup X) (B : Set (MulAut Y)) (A : Set (MulAut X))
    (hAB : ∀ α ∈ A, ∀ x, ∃ β ∈ B, π (α x) = β (π x))
    (h : uc22pdiag_join (U.map π) B = ⊤) : uc22pdiag_join U A = ⊤ := by
  have hex : ∃ Q, uc22pdiag_Inv (U.map π) B Q := by
    by_contra hno
    push Not at hno
    have hbot : uc22pdiag_join (U.map π) B = ⊥ := by
      unfold uc22pdiag_join
      simp [hno]
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    have : y ∈ uc22pdiag_join (U.map π) B := by rw [h]; trivial
    rw [hbot, Subgroup.mem_bot] at this
    exact hy this
  have key : ∀ Q, uc22pdiag_Inv (U.map π) B Q → uc22pdiag_Inv U A (Q.comap π) := by
    rintro Q ⟨h1, h2, h3⟩
    refine ⟨fun n hn => h1 (uc22pdiag_map_normalizer_le π hπ U ⟨n, hn, rfl⟩), ?_, fun α hα x => ?_⟩
    · intro htop
      apply h2
      rw [← map_comap_eq_self_of_surjective hπ Q, htop, map_top_of_surjective _ hπ]
    · obtain ⟨β, hβ, hβx⟩ := hAB α hα x
      simp only [mem_comap, hβx]
      exact h3 β hβ (π x)
  have hle : uc22pdiag_join (U.map π) B ≤ (uc22pdiag_join U A).map π := by
    refine iSup₂_le fun Q hQ => ?_
    rw [← map_comap_eq_self_of_surjective hπ Q]
    exact map_mono (uc22pdiag_le_join (key Q hQ))
  have hker : π.ker ≤ uc22pdiag_join U A := by
    obtain ⟨Q₀, hQ₀⟩ := hex
    exact (MonoidHom.ker_le_comap π Q₀).trans (uc22pdiag_le_join (key Q₀ hQ₀))
  rw [h, top_le_iff] at hle
  rw [eq_top_iff]
  intro g _
  have : π g ∈ (uc22pdiag_join U A).map π := by rw [hle]; trivial
  obtain ⟨g', hg', hgg⟩ := this
  have : g' ⁻¹ * g ∈ π.ker := by simp [MonoidHom.mem_ker, hgg]
  have := hker this
  simpa using mul_mem hg' this

@[expose] noncomputable def uc22pdiag_inducedAut (α : MulAut X) : MulAut (X ⧸ center X) :=
  QuotientGroup.congr (center X) (center X) α (Subgroup.map_center_eq α)

theorem uc22pdiag_inducedAut_mk (α : MulAut X) (x : X) :
    uc22pdiag_inducedAut α (QuotientGroup.mk x) = QuotientGroup.mk (α x) := rfl

theorem uc22pdiag_induced_preserves (α : MulAut X) (U : Subgroup X) (hα : ∀ x, x ∈ U ↔ α x ∈ U)
    (y : X ⧸ center X) :
    y ∈ U.map (QuotientGroup.mk' (center X)) ↔
      uc22pdiag_inducedAut α y ∈ U.map (QuotientGroup.mk' (center X)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [uc22pdiag_inducedAut_mk]
  constructor
  · rintro ⟨u, hu, hux⟩
    refine ⟨α u, (hα u).1 hu, ?_⟩
    have := congrArg (uc22pdiag_inducedAut α) hux
    simpa [uc22pdiag_inducedAut_mk] using this
  · rintro ⟨u, hu, hux⟩
    refine ⟨α.symm u, (hα _).2 (by simpa using hu), ?_⟩
    have h1 : uc22pdiag_inducedAut α (QuotientGroup.mk (α.symm u)) = QuotientGroup.mk u := by
      simp [uc22pdiag_inducedAut_mk]
    have h2 : uc22pdiag_inducedAut α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
      uc22pdiag_inducedAut_mk α x
    have h3 : (QuotientGroup.mk' (center X)) u = QuotientGroup.mk (α x) := hux
    have : uc22pdiag_inducedAut α (QuotientGroup.mk (α.symm u)) =
        uc22pdiag_inducedAut α (QuotientGroup.mk x) := by
      rw [h1, h2, ← h3]; rfl
    exact (uc22pdiag_inducedAut α).injective this

end CFSG.LocalAnalysis.UniquenessCase.UC22
