module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG

@[expose] def modelReflSet {X : Type} [Group X] (S : Set (MulAut X)) : Set (MulAut X) :=
  {u | u ∈ S ∧ u ^ 2 = 1 ∧ Nat.card {x : X // u x = x} * 3 = Nat.card X}

@[expose] noncomputable def modelNonComm {X : Type} [Group X] (S : Set (MulAut X))
    (u : MulAut X) : ℕ :=
  {v | v ∈ modelReflSet S ∧ u * v ≠ v * u}.ncard

@[expose] def ModelNumIs {X : Type} [Group X] (S : Set (MulAut X)) (N : ℕ) (d : Option ℕ) :
    Prop :=
  (modelReflSet S).ncard = N ∧
    match d with
    | some d => ∀ u ∈ modelReflSet S, modelNonComm S u = d
    | none => ¬ ∃ d : ℕ, ∀ u ∈ modelReflSet S, modelNonComm S u = d

@[expose] def ModelConn {X : Type} [Group X] (S : Set (MulAut X)) : Prop :=
  ∀ u ∈ modelReflSet S, ∀ v ∈ modelReflSet S,
    Relation.ReflTransGen
      (fun a b => a ∈ modelReflSet S ∧ b ∈ modelReflSet S ∧ a * b ≠ b * a) u v

variable {G : Type} [Group G] {A : Subgroup G} {X : Type} [Group X]

private lemma frameMN_fixed_card (Θ : X ≃* ↥A) (u : MulAut X) :
    Nat.card {b : ↥A // MulAut.congr Θ u b = b} =
      Nat.card {x : X // u x = x} := by
  refine Nat.card_congr (Equiv.subtypeEquiv Θ.toEquiv.symm ?_)
  intro b
  constructor
  · intro hb
    have h : MulAut.congr Θ u b = Θ (u (Θ.symm b)) := by
      simp [MulAut.congr_apply]
    rw [h] at hb
    have := congrArg (fun y => Θ.symm y) hb
    simpa using this
  · intro hb
    have h : MulAut.congr Θ u b = Θ (u (Θ.symm b)) := by
      simp [MulAut.congr_apply]
    rw [h]
    exact (congrArg Θ hb).trans (MulEquiv.apply_symm_apply Θ b)

theorem ggIsReflection_congr_iff_model (Θ : X ≃* ↥A) (u : MulAut X) :
    GGIsReflection 3 (MulAut.congr Θ u) ↔
      u ^ 2 = 1 ∧ Nat.card {x : X // u x = x} * 3 = Nat.card X := by
  rw [GGIsReflection, frameMN_fixed_card Θ u, Nat.card_congr Θ.toEquiv, ← map_pow]
  constructor
  · rintro ⟨h2, hfix⟩
    exact ⟨(MulEquiv.map_eq_one_iff (MulAut.congr Θ)).mp h2, hfix⟩
  · rintro ⟨h2, hfix⟩
    exact ⟨by rw [h2, map_one], hfix⟩

private lemma frameMN_mem_frame_iff (Θ : X ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    {S : Set (MulAut X)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ (MulAut.congr Θ).symm φ ∈ S) (u : MulAut X) :
    MulAut.congr Θ u ∈ frameReflSet 𝒜 ↔ u ∈ modelReflSet S := by
  constructor
  · rintro ⟨hφ, hrefl⟩
    have hmem : (MulAut.congr Θ).symm (MulAut.congr Θ u) ∈ S := (h𝒜 _).mp hφ
    rw [MulEquiv.symm_apply_apply] at hmem
    exact ⟨hmem, (ggIsReflection_congr_iff_model Θ u).mp hrefl⟩
  · rintro ⟨hmem, hrefl⟩
    refine ⟨(h𝒜 _).mpr ?_, (ggIsReflection_congr_iff_model Θ u).mpr hrefl⟩
    rwa [MulEquiv.symm_apply_apply]

private lemma frameMN_image (Θ : X ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    {S : Set (MulAut X)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ (MulAut.congr Θ).symm φ ∈ S) :
    frameReflSet 𝒜 = MulAut.congr Θ '' modelReflSet S := by
  ext φ
  constructor
  · intro hφ
    refine ⟨(MulAut.congr Θ).symm φ, ?_, MulEquiv.apply_symm_apply _ φ⟩
    have hφ' : MulAut.congr Θ ((MulAut.congr Θ).symm φ) ∈ frameReflSet 𝒜 := by
      rwa [MulEquiv.apply_symm_apply]
    exact (frameMN_mem_frame_iff Θ h𝒜 _).mp hφ'
  · rintro ⟨u, hu, rfl⟩
    exact (frameMN_mem_frame_iff Θ h𝒜 u).mpr hu

private lemma frameMN_nonComm_image (Θ : X ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    {S : Set (MulAut X)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ (MulAut.congr Θ).symm φ ∈ S) {u : MulAut X} :
    MulAut.congr Θ '' {v | v ∈ modelReflSet S ∧ u * v ≠ v * u}
      = {ψ | ψ ∈ frameReflSet 𝒜 ∧
          MulAut.congr Θ u * ψ ≠ ψ * MulAut.congr Θ u} := by
  ext ψ
  constructor
  · rintro ⟨v, ⟨hv, hne⟩, rfl⟩
    refine ⟨(frameMN_mem_frame_iff Θ h𝒜 v).mpr hv, ?_⟩
    intro hcomm
    apply hne
    have h' : MulAut.congr Θ (u * v) = MulAut.congr Θ (v * u) := by
      rw [map_mul, map_mul]
      exact hcomm
    exact (MulAut.congr Θ).injective h'
  · rintro ⟨hψ, hne⟩
    have hS : (MulAut.congr Θ).symm ψ ∈ modelReflSet S := by
      have hψ' : MulAut.congr Θ ((MulAut.congr Θ).symm ψ) ∈ frameReflSet 𝒜 := by
        rwa [MulEquiv.apply_symm_apply]
      exact (frameMN_mem_frame_iff Θ h𝒜 _).mp hψ'
    refine ⟨(MulAut.congr Θ).symm ψ, ⟨hS, ?_⟩, MulEquiv.apply_symm_apply _ ψ⟩
    intro hcomm
    apply hne
    have h' : MulAut.congr Θ (u * (MulAut.congr Θ).symm ψ)
        = MulAut.congr Θ ((MulAut.congr Θ).symm ψ * u) := by
      rw [hcomm]
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'

private lemma frameMN_frameNonComm (Θ : X ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    {S : Set (MulAut X)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ (MulAut.congr Θ).symm φ ∈ S) {u : MulAut X} :
    frameNonComm 𝒜 (MulAut.congr Θ u) = modelNonComm S u := by
  rw [frameNonComm, modelNonComm, ← frameMN_nonComm_image Θ h𝒜,
    Set.ncard_image_of_injective _ (MulAut.congr Θ).injective]

private lemma frameMN_rel_map (Θ : X ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    {S : Set (MulAut X)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ (MulAut.congr Θ).symm φ ∈ S)
    {a b : MulAut X} (ha : a ∈ modelReflSet S) (hb : b ∈ modelReflSet S)
    (hne : a * b ≠ b * a) :
    MulAut.congr Θ a ∈ frameReflSet 𝒜 ∧ MulAut.congr Θ b ∈ frameReflSet 𝒜 ∧
      MulAut.congr Θ a * MulAut.congr Θ b ≠ MulAut.congr Θ b * MulAut.congr Θ a := by
  refine ⟨(frameMN_mem_frame_iff Θ h𝒜 a).mpr ha,
    (frameMN_mem_frame_iff Θ h𝒜 b).mpr hb, ?_⟩
  intro hcomm
  apply hne
  have h' : MulAut.congr Θ (a * b) = MulAut.congr Θ (b * a) := by
    rwa [map_mul, map_mul]
  exact (MulAut.congr Θ).injective h'

theorem frameNumIs_frameConn_of_model (Θ : X ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    {S : Set (MulAut X)} (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ (MulAut.congr Θ).symm φ ∈ S)
    {N : ℕ} {d : Option ℕ} (hN : ModelNumIs S N d) (hC : ModelConn S) :
    FrameNumIs 𝒜 N d ∧ FrameConn 𝒜 := by
  obtain ⟨hNcard, hNd⟩ := hN
  have himage := frameMN_image Θ h𝒜
  have hN' : (frameReflSet 𝒜).ncard = N := by
    rw [himage, Set.ncard_image_of_injective _ (MulAut.congr Θ).injective]
    exact hNcard
  refine ⟨⟨hN', ?_⟩, ?_⟩
  · cases d with
    | some d =>
        intro φ hφ
        rw [himage] at hφ
        obtain ⟨u, hu, rfl⟩ := hφ
        rw [frameMN_frameNonComm Θ h𝒜]
        exact hNd u hu
    | none =>
        intro hcon
        apply hNd
        obtain ⟨d, hd⟩ := hcon
        refine ⟨d, fun u hu => ?_⟩
        have hframe : MulAut.congr Θ u ∈ frameReflSet 𝒜 := by
          rw [himage]
          exact ⟨u, hu, rfl⟩
        rw [← frameMN_frameNonComm Θ h𝒜]
        exact hd _ hframe
  · intro φ hφ ψ hψ
    rw [himage] at hφ hψ
    obtain ⟨u, hu, rfl⟩ := hφ
    obtain ⟨v, hv, rfl⟩ := hψ
    have hchain := hC u hu v hv
    have hle : (fun a b : MulAut X =>
        a ∈ modelReflSet S ∧ b ∈ modelReflSet S ∧ a * b ≠ b * a)
        ≤ Function.onFun (fun a b : MulAut ↥A =>
          a ∈ frameReflSet 𝒜 ∧ b ∈ frameReflSet 𝒜 ∧ a * b ≠ b * a)
          (MulAut.congr Θ) := by
      rintro a b ⟨ha, hb, hne⟩
      exact frameMN_rel_map Θ h𝒜 ha hb hne
    exact Relation.ReflTransGen.lift (MulAut.congr Θ) hle u v hchain

end CFSG.StandardType.FrameRoute

end
