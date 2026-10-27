module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs

public section

namespace CFSG.StandardType.FrameRoute

variable {G G' : Type} [Group G] [Group G'] {A : Subgroup G} {A' : Subgroup G'}
  {𝒜 : Subgroup (MulAut ↥A)} {𝒜' : Subgroup (MulAut ↥A')}

private noncomputable def frameRT_f (e : ↥𝒜 ≃* ↥𝒜') (φ : MulAut ↥A) : MulAut ↥A' := by
  classical
  exact if h : φ ∈ 𝒜 then (e ⟨φ, h⟩ : MulAut ↥A') else 1

private noncomputable def frameRT_g (e : ↥𝒜 ≃* ↥𝒜') (ψ : MulAut ↥A') : MulAut ↥A := by
  classical
  exact if h : ψ ∈ 𝒜' then (e.symm ⟨ψ, h⟩ : MulAut ↥A) else 1

private lemma frameRT_f_of_mem (e : ↥𝒜 ≃* ↥𝒜') {φ : MulAut ↥A} (h : φ ∈ 𝒜) :
    frameRT_f e φ = (e ⟨φ, h⟩ : MulAut ↥A') := by
  classical
  unfold frameRT_f
  exact dif_pos h

private lemma frameRT_g_of_mem (e : ↥𝒜 ≃* ↥𝒜') {ψ : MulAut ↥A'} (h : ψ ∈ 𝒜') :
    frameRT_g e ψ = (e.symm ⟨ψ, h⟩ : MulAut ↥A) := by
  classical
  unfold frameRT_g
  exact dif_pos h

private lemma frameRT_f_mem (e : ↥𝒜 ≃* ↥𝒜') {φ : MulAut ↥A} (hφ : φ ∈ 𝒜) :
    frameRT_f e φ ∈ 𝒜' := by
  rw [frameRT_f_of_mem e hφ]
  exact (e ⟨φ, hφ⟩).2

private lemma frameRT_g_mem (e : ↥𝒜 ≃* ↥𝒜') {ψ : MulAut ↥A'} (hψ : ψ ∈ 𝒜') :
    frameRT_g e ψ ∈ 𝒜 := by
  rw [frameRT_g_of_mem e hψ]
  exact (e.symm ⟨ψ, hψ⟩).2

private lemma frameRT_g_f (e : ↥𝒜 ≃* ↥𝒜') {φ : MulAut ↥A} (hφ : φ ∈ 𝒜) :
    frameRT_g e (frameRT_f e φ) = φ := by
  rw [frameRT_f_of_mem e hφ, frameRT_g_of_mem e (e ⟨φ, hφ⟩).2]
  simpa using congrArg (fun x : ↥𝒜 => (x : MulAut ↥A)) (e.symm_apply_apply ⟨φ, hφ⟩)

private lemma frameRT_f_g (e : ↥𝒜 ≃* ↥𝒜') {ψ : MulAut ↥A'} (hψ : ψ ∈ 𝒜') :
    frameRT_f e (frameRT_g e ψ) = ψ := by
  rw [frameRT_g_of_mem e hψ, frameRT_f_of_mem e (e.symm ⟨ψ, hψ⟩).2]
  simpa using congrArg (fun x : ↥𝒜' => (x : MulAut ↥A')) (e.apply_symm_apply ⟨ψ, hψ⟩)

private lemma frameRT_f_coe_mul (e : ↥𝒜 ≃* ↥𝒜') {φ ψ : MulAut ↥A}
    (hφ : φ ∈ 𝒜) (hψ : ψ ∈ 𝒜) :
    ((e (⟨φ, hφ⟩ * ⟨ψ, hψ⟩) : ↥𝒜') : MulAut ↥A')
      = frameRT_f e φ * frameRT_f e ψ := by
  rw [frameRT_f_of_mem e hφ, frameRT_f_of_mem e hψ, map_mul, Subgroup.coe_mul]

private lemma frameRT_comm_iff (e : ↥𝒜 ≃* ↥𝒜') {φ ψ : MulAut ↥A}
    (hφ : φ ∈ 𝒜) (hψ : ψ ∈ 𝒜) :
    φ * ψ = ψ * φ ↔
      frameRT_f e φ * frameRT_f e ψ = frameRT_f e ψ * frameRT_f e φ := by
  constructor
  · intro h
    have hx : (⟨φ, hφ⟩ : ↥𝒜) * ⟨ψ, hψ⟩ = ⟨ψ, hψ⟩ * ⟨φ, hφ⟩ :=
      Subtype.ext (by simpa using h)
    rw [← frameRT_f_coe_mul e hφ hψ, ← frameRT_f_coe_mul e hψ hφ]
    exact congrArg (fun x : ↥𝒜 => (e x : MulAut ↥A')) hx
  · intro h
    have h' : ((e (⟨φ, hφ⟩ * ⟨ψ, hψ⟩) : ↥𝒜') : MulAut ↥A')
        = ((e (⟨ψ, hψ⟩ * ⟨φ, hφ⟩) : ↥𝒜') : MulAut ↥A') := by
      rw [frameRT_f_coe_mul e hφ hψ, frameRT_f_coe_mul e hψ hφ]
      exact h
    exact congrArg (fun x : ↥𝒜 => (x : MulAut ↥A))
      (e.injective (Subtype.ext h'))

private lemma frameRT_f_frameReflSet (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A'))
    {φ : MulAut ↥A} (hφ : φ ∈ frameReflSet 𝒜) :
    frameRT_f e φ ∈ frameReflSet 𝒜' := by
  refine ⟨frameRT_f_mem e hφ.1, ?_⟩
  rw [frameRT_f_of_mem e hφ.1]
  exact (he ⟨φ, hφ.1⟩).mp hφ.2

private lemma frameRT_g_reflection (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A'))
    {ψ : MulAut ↥A'} (hψ : ψ ∈ frameReflSet 𝒜') :
    GGIsReflection 3 (e.symm ⟨ψ, hψ.1⟩ : MulAut ↥A) := by
  have h : e (e.symm ⟨ψ, hψ.1⟩) = ⟨ψ, hψ.1⟩ := e.apply_symm_apply _
  exact (he (e.symm ⟨ψ, hψ.1⟩)).mpr (by rw [h]; exact hψ.2)

private lemma frameRT_g_frameReflSet (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A'))
    {ψ : MulAut ↥A'} (hψ : ψ ∈ frameReflSet 𝒜') :
    frameRT_g e ψ ∈ frameReflSet 𝒜 := by
  constructor
  · rw [frameRT_g_of_mem e hψ.1]
    exact (e.symm ⟨ψ, hψ.1⟩).2
  · rw [frameRT_g_of_mem e hψ.1]
    exact frameRT_g_reflection e he hψ

private lemma frameRT_frameReflSet_image (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A')) :
    frameRT_f e '' frameReflSet 𝒜 = frameReflSet 𝒜' := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact frameRT_f_frameReflSet e he hφ
  · intro hψ
    exact ⟨frameRT_g e ψ, frameRT_g_frameReflSet e he hψ, frameRT_f_g e hψ.1⟩

private lemma frameRT_f_injOn (e : ↥𝒜 ≃* ↥𝒜') :
    Set.InjOn (frameRT_f e) (frameReflSet 𝒜) := by
  intro φ hφ ψ hψ h
  calc φ = frameRT_g e (frameRT_f e φ) := (frameRT_g_f e hφ.1).symm
    _ = frameRT_g e (frameRT_f e ψ) := by rw [h]
    _ = ψ := frameRT_g_f e hψ.1

private lemma frameRT_ncard (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A')) :
    (frameReflSet 𝒜).ncard = (frameReflSet 𝒜').ncard := by
  rw [← frameRT_frameReflSet_image e he, (frameRT_f_injOn e).ncard_image]

private lemma frameRT_frameNonComm_image (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A'))
    {φ : MulAut ↥A} (hφ : φ ∈ frameReflSet 𝒜) :
    frameRT_f e '' {ψ | ψ ∈ frameReflSet 𝒜 ∧ φ * ψ ≠ ψ * φ}
      = {χ | χ ∈ frameReflSet 𝒜' ∧ frameRT_f e φ * χ ≠ χ * frameRT_f e φ} := by
  ext χ
  constructor
  · rintro ⟨ψ, ⟨hψ, hne⟩, rfl⟩
    exact ⟨frameRT_f_frameReflSet e he hψ, ((frameRT_comm_iff e hφ.1 hψ.1).not.mp hne)⟩
  · rintro ⟨hχ, hne⟩
    refine ⟨frameRT_g e χ, ⟨frameRT_g_frameReflSet e he hχ, ?_⟩, frameRT_f_g e hχ.1⟩
    intro hcomm
    exact hne (by
      have h := (frameRT_comm_iff e hφ.1 (frameRT_g_mem e hχ.1)).mp hcomm
      rwa [frameRT_f_g e hχ.1] at h)

private lemma frameRT_frameNonComm (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A'))
    {φ : MulAut ↥A} (hφ : φ ∈ frameReflSet 𝒜) :
    frameNonComm 𝒜 φ = frameNonComm 𝒜' (frameRT_f e φ) := by
  unfold frameNonComm
  rw [← frameRT_frameNonComm_image e he hφ]
  exact (Set.InjOn.mono (fun x hx => hx.1) (frameRT_f_injOn e)).ncard_image.symm

private lemma frameRT_rel_preimage (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔
      GGIsReflection 3 (e φ : MulAut ↥A'))
    {a b : MulAut ↥A'}
    (h : a ∈ frameReflSet 𝒜' ∧ b ∈ frameReflSet 𝒜' ∧ a * b ≠ b * a) :
    frameRT_g e a ∈ frameReflSet 𝒜 ∧ frameRT_g e b ∈ frameReflSet 𝒜 ∧
      frameRT_g e a * frameRT_g e b ≠ frameRT_g e b * frameRT_g e a := by
  obtain ⟨ha, hb, hne⟩ := h
  have hga := frameRT_g_frameReflSet e he ha
  have hgb := frameRT_g_frameReflSet e he hb
  refine ⟨hga, hgb, ?_⟩
  intro hcomm
  exact hne (by
    have h := (frameRT_comm_iff e hga.1 hgb.1).mp hcomm
    rwa [frameRT_f_g e ha.1, frameRT_f_g e hb.1] at h)

theorem frameNumIs_of_mulEquiv (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔ GGIsReflection 3 (e φ : MulAut ↥A'))
    {N : ℕ} {d : Option ℕ} (h : FrameNumIs 𝒜' N d) : FrameNumIs 𝒜 N d := by
  obtain ⟨hN, hd⟩ := h
  have hN' : (frameReflSet 𝒜).ncard = N := by
    rw [frameRT_ncard e he]
    exact hN
  refine ⟨hN', ?_⟩
  cases d with
  | none =>
      dsimp only at hd
      intro hcon
      obtain ⟨d, hd'⟩ := hcon
      refine hd ⟨d, fun ψ hψ => ?_⟩
      rw [← frameRT_f_g e hψ.1]
      rw [← frameRT_frameNonComm e he (frameRT_g_frameReflSet e he hψ)]
      exact hd' (frameRT_g e ψ) (frameRT_g_frameReflSet e he hψ)
  | some d =>
      dsimp only at hd
      intro φ hφ
      rw [frameRT_frameNonComm e he hφ]
      exact hd (frameRT_f e φ) (frameRT_f_frameReflSet e he hφ)

theorem frameConn_of_mulEquiv (e : ↥𝒜 ≃* ↥𝒜')
    (he : ∀ φ : ↥𝒜, GGIsReflection 3 (φ : MulAut ↥A) ↔ GGIsReflection 3 (e φ : MulAut ↥A'))
    (h : FrameConn 𝒜') : FrameConn 𝒜 := by
  intro φ hφ ψ hψ
  have hchain : Relation.ReflTransGen
      (fun a b : MulAut ↥A' =>
        a ∈ frameReflSet 𝒜' ∧ b ∈ frameReflSet 𝒜' ∧ a * b ≠ b * a)
      (frameRT_f e φ) (frameRT_f e ψ) :=
    h (frameRT_f e φ) (frameRT_f_frameReflSet e he hφ)
      (frameRT_f e ψ) (frameRT_f_frameReflSet e he hψ)
  have hle : (fun a b : MulAut ↥A' =>
        a ∈ frameReflSet 𝒜' ∧ b ∈ frameReflSet 𝒜' ∧ a * b ≠ b * a)
      ≤ Function.onFun (fun a b : MulAut ↥A =>
        a ∈ frameReflSet 𝒜 ∧ b ∈ frameReflSet 𝒜 ∧ a * b ≠ b * a) (frameRT_g e) :=
    fun a b hab => frameRT_rel_preimage e he hab
  have hback : Relation.ReflTransGen
      (fun a b : MulAut ↥A =>
        a ∈ frameReflSet 𝒜 ∧ b ∈ frameReflSet 𝒜 ∧ a * b ≠ b * a)
      (frameRT_g e (frameRT_f e φ)) (frameRT_g e (frameRT_f e ψ)) :=
    Relation.ReflTransGen.lift (frameRT_g e) hle (frameRT_f e φ) (frameRT_f e ψ) hchain
  simpa [frameRT_g_f e hφ.1, frameRT_g_f e hψ.1] using hback

end CFSG.StandardType.FrameRoute

end
