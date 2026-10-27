module

public import CFSG.Milestones.ASVolI.F4N.BId
public import CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F4N.BPerm

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4nB_le_pCoreOf {E : Type} [Group E] {Q P : Subgroup E} (hQP : Q ≤ P)
    (hN : P ≤ Subgroup.normalizer (Q : Set E)) (hQ : IsPGroup 2 Q) : Q ≤ pCoreOf 2 P := by
  have hn : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hN
  have h1 : Q.subgroupOf P ≤ CFSG.pCore 2 ↥P := le_sSup ⟨hn, hQ.comap_subtype⟩
  have h2 := Subgroup.map_mono (f := P.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hQP] at h2

@[expose] def burnsideF4nB_invSet {E : Type} [Group E] (M₁ M₂ : Subgroup E) (b₀ : E) : Set E :=
  {e | e * e = 1 ∧ b₀⁻¹ * e ∈ M₁ ⊓ M₂}

section EFacts

set_option linter.unusedSectionVars false


theorem burnsideF4nB_E_facts {p f : ℕ} {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 GLKind.G2d p f ⊤ M₁ M₂) :
    (M₁ ⊓ M₂).relIndex M₁ = 3 ∧ (M₁ ⊓ M₂).relIndex M₂ = 3 ∧
    ∃ Z : Subgroup E, Z ≤ M₁ ⊓ M₂ ∧ Z ≤ pCoreOf 2 M₂ ∧ (∀ d ∈ Z, ∀ a ∈ M₁, a * d = d * a) ∧
      ∀ b₀ ∈ M₂, b₀ ∉ M₁ ⊓ M₂ →
        (burnsideF4nB_invSet M₁ M₂ b₀).ncard = 4 ∧
        ∀ e ∈ burnsideF4nB_invSet M₁ M₂ b₀, ∀ e' ∈ burnsideF4nB_invSet M₁ M₂ b₀,
          ∃ d ∈ Z, d * e * d⁻¹ = e' := by
  obtain ⟨Φ, hT, hB, hA⟩ := burnsideF4nB_ident hyp
  obtain ⟨hQT, hQp, hAQ, hZQ⟩ := burnsideF4nB_Q_props
  have hset : ∀ u₀ : U33G, burnsideF4nB_invSet M₁ M₂ (Φ u₀) =
      (fun u => Φ u) '' burnsideF4nB_invCoset u₀ := by
    intro u₀
    ext e
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Φ.symm e, ⟨?_, ?_⟩, by simp⟩
      · rw [← map_mul, h1, map_one]
      · rw [← hT, Subgroup.mem_map_equiv] at h2
        simpa using h2
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      refine ⟨by rw [← map_mul, h1, map_one], ?_⟩
      rw [← hT, Subgroup.mem_map_equiv]
      simpa using h2
  refine ⟨?_, ?_, burnsideF4nB_Z.map Φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← hT, ← hB, Subgroup.relIndex_map_map_of_injective _ _ Φ.injective,
      burnsideF4nB_relIndex_B]
  · rw [← hT, ← hA, Subgroup.relIndex_map_map_of_injective _ _ Φ.injective,
      burnsideF4nB_relIndex_A]
  · rw [← hT]
    exact Subgroup.map_mono (hZQ.trans hQT)
  · refine (Subgroup.map_mono hZQ).trans (burnsideF4nB_le_pCoreOf ?_ ?_ (hQp.map _))
    · rw [← hA]
      exact Subgroup.map_mono (hQT.trans u33Data.T_le_A)
    · rw [← hA, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hAQ
  · rintro _ ⟨d, hd, rfl⟩ a ha
    rw [← hB] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    show Φ a' * Φ d = Φ d * Φ a'
    rw [← map_mul, ← map_mul, burnsideF4nB_Z_central hd ha']
  · intro b₀ hb hbT
    have hu : Φ.symm b₀ ∈ u33Data.A := by
      rw [← hA, Subgroup.mem_map_equiv] at hb
      exact hb
    have huT : Φ.symm b₀ ∉ u33Data.T := by
      intro h
      apply hbT
      rw [← hT, Subgroup.mem_map_equiv]
      exact h
    have hb₀ : b₀ = Φ (Φ.symm b₀) := by simp
    rw [hb₀, hset]
    refine ⟨?_, ?_⟩
    · rw [Set.ncard_image_of_injective _ Φ.injective]
      exact burnsideF4nB_ncard_inv hu huT
    · rintro _ ⟨u, hu1, rfl⟩ _ ⟨u', hu1', rfl⟩
      obtain ⟨d, hd, hdu⟩ := burnsideF4nB_trans_inv hu huT hu1 hu1'
      exact ⟨Φ d, ⟨d, hd, rfl⟩, by rw [← map_inv, ← map_mul, ← map_mul, hdu]⟩

end EFacts

section Completion

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

@[expose] def burnsideF4nB_v1 (M₁ M₂ : Subgroup E) : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 →* E :=
  M₁.subtype

@[expose] def burnsideF4nB_v2 (M₁ M₂ : Subgroup E) : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2 →* E :=
  M₂.subtype

@[expose] def burnsideF4nB_mk1 (M₁ M₂ : Subgroup E) (d : E) (hd : d ∈ M₁) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 := (⟨d, hd⟩ : ↥M₁)

@[expose] def burnsideF4nB_mk2 (M₁ M₂ : Subgroup E) (d : E) (hd : d ∈ M₂) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).G2 := (⟨d, hd⟩ : ↥M₂)

@[expose] def burnsideF4nB_mk12 (M₁ M₂ : Subgroup E) (d : E) (hd : d ∈ M₁ ⊓ M₂) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 := (⟨d, hd⟩ : ↥(M₁ ⊓ M₂))

theorem burnsideF4nB_v1_injective : Function.Injective (burnsideF4nB_v1 M₁ M₂) :=
  M₁.subtype_injective

theorem burnsideF4nB_v2_injective : Function.Injective (burnsideF4nB_v2 M₁ M₂) :=
  M₂.subtype_injective

theorem burnsideF4nB_v1_mem (a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) :
    burnsideF4nB_v1 M₁ M₂ a ∈ M₁ := (show ↥M₁ from a).2

theorem burnsideF4nB_v2_mem (b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) :
    burnsideF4nB_v2 M₁ M₂ b ∈ M₂ := (show ↥M₂ from b).2

theorem burnsideF4nB_f1_alpha1 {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z]
    (c : α.Completion Z) (g : α.G12) : f1 (c := c) (α.α1 g) = f2 (c := c) (α.α2 g) := by
  apply Subtype.ext
  show c.φ1 (α.α1 g) = c.φ2 (α.α2 g)
  rw [c.comm1, c.comm2]

theorem burnsideF4nB_f2_smul_xv_iff {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z]
    (c : α.Completion Z) (hc : c.IsFaithful) (b : α.G2) :
    f2 (c := c) b • c.xv = c.xv ↔ b ∈ α.α2.range := by
  constructor
  · intro h
    have h1 : ((f2 (c := c) b : c.G0) : Z) ∈ c.φ1.range :=
      (burnsideF4b_mem_stv_xv c _).mp (MulAction.mem_stabilizer_iff.mpr h)
    have h2 : c.φ2 b ∈ c.φ1.range ⊓ c.φ2.range := ⟨h1, ⟨b, rfl⟩⟩
    rw [c.inter] at h2
    obtain ⟨d, hd⟩ := h2
    exact ⟨d, hc.2.2 (by rw [c.comm2]; exact hd)⟩
  · intro hb
    exact MulAction.mem_stabilizer_iff.mp (burnsideF4b_f2_mem_stv_xv c hb)

theorem burnsideF4nB_stv_lv_eq_range {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z]
    (c : α.Completion Z) : stv c c.lv = (f2 (c := c)).range :=
  le_antisymm (stv_lv_le_range_f2 c) (by
    rintro _ ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a))

theorem burnsideF4nB_mem_alpha2 (m : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) :
    m ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range ↔ burnsideF4nB_v2 M₁ M₂ m ∈ M₁ ⊓ M₂ := by
  rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range = (M₁ ⊓ M₂).subgroupOf M₂ from
    Subgroup.inclusion_range (inf_le_right : M₁ ⊓ M₂ ≤ M₂)]
  exact Subgroup.mem_subgroupOf

@[expose] def burnsideF4nB_N1 (β : Cpl M₁ M₂ Y) (y : β.Γ) : Set β.G0 :=
  {s | s ∈ stv β β.lv ∧ HasCycle β s β.xv y}

theorem burnsideF4nB_N1_eq (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (b₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) {y : β.Γ} (hy : f2 (c := β) b₀ • β.xv = y)
    (hyx : y ≠ β.xv) :
    burnsideF4nB_N1 β y = (f2 (c := β)) ''
      {m | burnsideF4nB_v2 M₁ M₂ m ∈ burnsideF4nB_invSet M₁ M₂ (burnsideF4nB_v2 M₁ M₂ b₀)} := by
  have key : ∀ m : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2,
      f2 (c := β) m • β.xv = y ↔
        (burnsideF4nB_v2 M₁ M₂ b₀)⁻¹ * burnsideF4nB_v2 M₁ M₂ m ∈ M₁ ⊓ M₂ := by
    intro m
    rw [← hy, ← inv_smul_eq_iff, ← mul_smul, ← map_inv, ← map_mul,
      burnsideF4nB_f2_smul_xv_iff β hβ, burnsideF4nB_mem_alpha2, map_mul, map_inv]
  ext s
  constructor
  · rintro ⟨hs, hs2, -, hsx, -⟩
    rw [burnsideF4nB_stv_lv_eq_range] at hs
    obtain ⟨m, rfl⟩ := hs
    refine ⟨m, ⟨?_, (key m).1 hsx⟩, rfl⟩
    have : m * m = 1 := f2_injective β hβ (by rw [map_mul, hs2, map_one])
    rw [← map_mul, this, map_one]
  · rintro ⟨m, ⟨hm2, hm⟩, rfl⟩
    have hm2' : m * m = 1 := burnsideF4nB_v2_injective (by rw [map_mul, hm2, map_one])
    have hx : f2 (c := β) m • β.xv = y := (key m).2 hm
    refine ⟨MulAction.mem_stabilizer_iff.mpr (f2_smul_lv m), ?_, hyx.symm, hx, ?_⟩
    · rw [← map_mul, hm2', map_one]
    · rw [← hx, ← mul_smul, ← map_mul, hm2', map_one, one_smul]

theorem burnsideF4nB_ncard_N1 (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (b₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) {y : β.Γ} (hy : f2 (c := β) b₀ • β.xv = y)
    (hyx : y ≠ β.xv) {n : ℕ}
    (hn : (burnsideF4nB_invSet M₁ M₂ (burnsideF4nB_v2 M₁ M₂ b₀)).ncard = n) :
    (burnsideF4nB_N1 β y).ncard = n := by
  rw [burnsideF4nB_N1_eq β hβ b₀ hy hyx, Set.ncard_image_of_injective _ (f2_injective β hβ), ← hn]
  have hsub : burnsideF4nB_invSet M₁ M₂ (burnsideF4nB_v2 M₁ M₂ b₀) ⊆ M₂ := by
    rintro e ⟨-, he⟩
    have := M₂.mul_mem (burnsideF4nB_v2_mem b₀) he.2
    simpa using this
  have himg : (burnsideF4nB_v2 M₁ M₂) ''
      {m | burnsideF4nB_v2 M₁ M₂ m ∈ burnsideF4nB_invSet M₁ M₂ (burnsideF4nB_v2 M₁ M₂ b₀)} =
      burnsideF4nB_invSet M₁ M₂ (burnsideF4nB_v2 M₁ M₂ b₀) := by
    ext e
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro he
      exact ⟨burnsideF4nB_mk2 M₁ M₂ e (hsub he), he, rfl⟩
  calc {m | burnsideF4nB_v2 M₁ M₂ m ∈ burnsideF4nB_invSet M₁ M₂ (burnsideF4nB_v2 M₁ M₂ b₀)}.ncard
      = ((burnsideF4nB_v2 M₁ M₂) '' {m | burnsideF4nB_v2 M₁ M₂ m ∈
          burnsideF4nB_invSet M₁ M₂ (burnsideF4nB_v2 M₁ M₂ b₀)}).ncard :=
        (Set.ncard_image_of_injective _ burnsideF4nB_v2_injective).symm
    _ = _ := by rw [himg]

theorem burnsideF4nB_exists_b₀ (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {y : β.Γ}
    (hy : y ∈ CosetGeom.nbrs β.lv) (hyx : y ≠ β.xv) :
    ∃ b₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2, f2 (c := β) b₀ • β.xv = y ∧
      burnsideF4nB_v2 M₁ M₂ b₀ ∉ M₁ ⊓ M₂ := by
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq
    (CosetGeom.adj_γ₀_γ₁.symm : β.graph.Adj β.lv β.xv) (hy : β.graph.Adj β.lv y)
  obtain ⟨b₀, rfl⟩ := stv_lv_le_range_f2 β (MulAction.mem_stabilizer_iff.mpr hg1)
  refine ⟨b₀, hg2, fun h => hyx ?_⟩
  rw [← hg2]
  exact (burnsideF4nB_f2_smul_xv_iff β hβ b₀).2 ((burnsideF4nB_mem_alpha2 b₀).2 h)

theorem burnsideF4nB_N2_eq (β : Cpl M₁ M₂ Y) (a₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1)
    (y' : β.Γ) :
    {t : β.G0 | t ∈ stv β (f1 (c := β) a₀ • β.lv) ∧ HasCycle β t β.xv y'} =
      (fun s => f1 (c := β) a₀ * s * (f1 (c := β) a₀)⁻¹) ''
        burnsideF4nB_N1 β ((f1 (c := β) a₀)⁻¹ • y') := by
  set g := f1 (c := β) a₀ with hg
  have hgx : g • β.xv = β.xv := f1_smul_xv a₀
  have hgx' : g⁻¹ • β.xv = β.xv := inv_smul_eq_iff.mpr hgx.symm
  ext t
  constructor
  · rintro ⟨ht, ht2, hne, htx, hty⟩
    refine ⟨g⁻¹ * t * g, ⟨?_, ?_, ?_, ?_, ?_⟩, by group⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp ht,
        inv_smul_smul]
    · rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]
      group
    · intro h
      apply hne
      rw [← hgx, h, smul_inv_smul]
    · rw [mul_smul, mul_smul, hgx, htx]
    · rw [mul_smul, mul_smul, smul_inv_smul, hty, hgx']
  · rintro ⟨s, ⟨hs, hs2, hne, hsx, hsy⟩, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
        MulAction.mem_stabilizer_iff.mp hs]
    · rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group, hs2]
      group
    · intro h
      apply hne
      rw [← h, hgx']
    · rw [mul_smul, mul_smul, hgx', hsx, smul_inv_smul]
    · rw [mul_smul, mul_smul, hsy, hgx]

theorem burnsideF4nB_Qu_lv_cc {p f : ℕ} {Gp : Subgroup E} {κ : GLKind}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (β : Cpl M₁ M₂ Y) (a₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) :
    Qu p Gp β β.lv = Ql p Gp β ∧
      Qu p Gp β (f1 (c := β) a₀ • β.lv) = conjSub (f1 (c := β) a₀) (Ql p Gp β) := by
  have hQ := burnsideF4b_QNormalized p hyp.normal β
  refine ⟨Qvert_baseVert hQ true, ?_⟩
  have hv : CosetGeom.vtype (f1 (c := β) a₀ • β.lv) = true := by
    rw [CosetGeom.vtype_smul]; rfl
  have h := Qvert_eq_conjSub hQ (u := f1 (c := β) a₀ • β.lv) (g := f1 (c := β) a₀) (by
    rw [hv]; rfl)
  rw [hv] at h
  exact h

theorem burnsideF4nB_Z_le_Qu {p f : ℕ} {κ : GLKind} (hyp : HypF_4_4 κ p f ⊤ M₁ M₂)
    (β : Cpl M₁ M₂ Y) (a₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) {d : E} (hd1 : d ∈ M₁)
    (hd2 : d ∈ M₂) (hdQ : d ∈ pCoreOf p M₂) (hdc : ∀ a ∈ M₁, a * d = d * a) :
    f1 (c := β) (burnsideF4nB_mk1 M₁ M₂ d hd1) ∈
      Qu p ⊤ β β.lv ⊓ Qu p ⊤ β (f1 (c := β) a₀ • β.lv) := by
  obtain ⟨h1, h2⟩ := burnsideF4nB_Qu_lv_cc hyp β a₀
  have hd12 : d ∈ M₁ ⊓ M₂ := Subgroup.mem_inf.2 ⟨hd1, hd2⟩
  have hdd : f1 (c := β) (burnsideF4nB_mk1 M₁ M₂ d hd1) =
      f2 (c := β) (burnsideF4nB_mk2 M₁ M₂ d hd2) :=
    burnsideF4nB_f1_alpha1 β (burnsideF4nB_mk12 M₁ M₂ d hd12)
  have hQl : f1 (c := β) (burnsideF4nB_mk1 M₁ M₂ d hd1) ∈ Ql p ⊤ β := by
    rw [hdd]
    refine ⟨burnsideF4nB_mk2 M₁ M₂ d hd2, ?_, rfl⟩
    show d ∈ pCoreOf p (⊤ ⊓ M₂)
    rw [top_inf_eq]
    exact hdQ
  rw [Subgroup.mem_inf, h1, h2]
  refine ⟨hQl, ?_⟩
  rw [mem_conjSub, ← map_inv, ← map_mul, ← map_mul]
  have he : a₀⁻¹ * burnsideF4nB_mk1 M₁ M₂ d hd1 * a₀ = burnsideF4nB_mk1 M₁ M₂ d hd1 := by
    apply burnsideF4nB_v1_injective
    rw [map_mul, map_mul, map_inv]
    show (burnsideF4nB_v1 M₁ M₂ a₀)⁻¹ * d * burnsideF4nB_v1 M₁ M₂ a₀ = d
    rw [mul_assoc, ← hdc _ (burnsideF4nB_v1_mem a₀), ← mul_assoc, inv_mul_cancel, one_mul]
  rw [he]
  exact hQl

end Completion

end CFSG.ASVolI
