module

public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof424
public import CFSG.RankThree.Asc83Table.M24
public import CFSG.RankThree.Asc83Table.He
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projImage projSL)

@[expose] def K424PairingLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46 X → IsQuasisimple X → Subgroup.center X = ⊥ →
    ¬ IsSLThreePiAny X →
    ((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
      ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) →
    ∀ (D : Subgroup X) (c d : X) (K : Subgroup X), InnerConfig424 X D c d K →
      Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6)

@[expose] def K424PairingSpor : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* NativeSporadic.M24) ∨ Nonempty (X ≃* NativeSporadic.He)) →
    ∀ (D : Subgroup X) (c d : X) (K : Subgroup X), InnerConfig424 X D c d K →
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 1))

namespace Res424Two

open Res423Two CFSG.RankThree.Asc83Table CFSG.SectionRank

theorem card_autIn_le_of_config {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X}
    {K : Subgroup X} (h : InnerConfig424 X D c d K) : Nat.card (autIn (⊤ : Subgroup X) D) ≤ 27 := by
  have hDe := h.maximal.prop
  set c' : D := ⟨c, h.c_mem⟩
  set d' : D := ⟨d, h.d_mem⟩
  have hc3 : c' ^ 3 = 1 := Subtype.ext (hDe.2 c h.c_mem)
  have hd3 : d' ^ 3 = 1 := Subtype.ext (hDe.2 d h.d_mem)
  have hcd : Commute c' d' := hDe.1.is_comm.comm c' d'
  have hc1 : c' ≠ 1 := fun h1 => h.c_ne_one (congrArg Subtype.val h1)
  have hdc : d' ∉ Subgroup.zpowers c' := by
    rintro ⟨k, hk⟩
    apply h.d_not_mem
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hgen : Subgroup.closure ({c', d'} : Set D) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [card_closure_pair_eq_nine hc3 hd3 hcd hc1 hdc, h.card_eq]
  have key : ∀ σ ∈ autIn (⊤ : Subgroup X) D, σ d' ∈ Subgroup.zpowers d' := by
    intro σ hσ
    obtain ⟨g, hN, -, rfl⟩ := mem_autIn_iff.mp hσ
    have hgd := h.normalizer_le hN
    have h1 : g * d * g⁻¹ ∈ Subgroup.zpowers d :=
      (Subgroup.mem_normalizer_iff.mp hgd d).mp (Subgroup.mem_zpowers d)
    obtain ⟨k, hk⟩ := h1
    change d ^ k = g * d * g⁻¹ at hk
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_zpow]
    rw [Sec4.normalizerMonoidHom_apply_coe]
    exact hk
  let f : autIn (⊤ : Subgroup X) D → D × Subgroup.zpowers d' :=
    fun σ => ((σ : MulAut D) c', ⟨(σ : MulAut D) d', key σ σ.2⟩)
  have hf : Function.Injective f := by
    intro σ τ hστ
    have h1 : (σ : MulAut D) c' = (τ : MulAut D) c' := congrArg Prod.fst hστ
    have h2 : (σ : MulAut D) d' = (τ : MulAut D) d' := congrArg (fun p => (p.2 : D)) hστ
    apply Subtype.ext
    have hle : Subgroup.closure ({c', d'} : Set D) ≤
        (σ : MulAut D).toMonoidHom.eqLocus (τ : MulAut D).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact h1
      · exact h2
    rw [hgen] at hle
    exact MulEquiv.ext fun x => hle (Subgroup.mem_top x)
  have hd1 : d' ≠ 1 := by
    intro h1
    apply h.d_not_mem
    rw [show d = 1 from congrArg Subtype.val h1]
    exact Subgroup.one_mem _
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, h.card_eq, Nat.card_zpowers, orderOf_eq_prime hd3 hd1] at hcard
  exact hcard

theorem not_nonempty_gl_of_config {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X}
    {K : Subgroup X} (h : InnerConfig424 X D c d K) :
    ¬ Nonempty (Automizer D ≃* GL23) := by
  rintro ⟨f⟩
  have h1 := card_autIn_le_of_config h
  rw [← Nat.card_congr (Sporadic.automizerEquivAutIn D).toEquiv, Nat.card_congr f.toEquiv,
    card_GL23] at h1
  norm_num at h1

theorem automizer_m24
    {L : Type} [Group L] (hL : NativeSporadic.IsSporadic L .M24) {B : Subgroup L}
    (hB : Nat.card B = 9) :
    Nonempty (Automizer B ≃* DihedralGroup 6) ∨ Nonempty (Automizer B ≃* GL23) := by
  obtain ⟨e⟩ := hL
  obtain ⟨-, -, h₃⟩ := ex27_transport M24.X_cube M24.Y_cube M24.Z_X M24.Z_Y M24.Z_ne
    M24.factorization_card (e : L ≃* NativeSporadic.M24)
  obtain ⟨i, ⟨f⟩⟩ := h₃ B hB
  rcases M24.automizer_B i with h | h
  · obtain ⟨q⟩ := h
    exact Or.inl ⟨f.trans q⟩
  · obtain ⟨q⟩ := h
    exact Or.inr ⟨f.trans q⟩

theorem automizer_he {L : Type}
    [Group L] (hL : NativeSporadic.IsSporadic L .He) {B : Subgroup L} (hB : Nat.card B = 9) :
    Nonempty (Automizer B ≃* DihedralGroup 6) ∨ Nonempty (Automizer B ≃* GL23) := by
  obtain ⟨e⟩ := hL
  obtain ⟨-, -, h₃⟩ := ex27_transport (He.facts.x_cube (specP 7 50) He.he_check)
    (He.facts.y_cube (specP 7 50) He.he_check) (He.facts.z_x (specP 7 50) He.he_check)
    (He.facts.z_y (specP 7 50) He.he_check) (He.facts.z_ne (specP 7 50) He.he_check)
    He.factorization_card (e : L ≃* NativeSporadic.He)
  obtain ⟨i, ⟨f⟩⟩ := h₃ B hB
  rcases He.automizer_B i with h | h
  · obtain ⟨q⟩ := h
    exact Or.inl ⟨f.trans q⟩
  · obtain ⟨q⟩ := h
    exact Or.inr ⟨f.trans q⟩

theorem nonempty_autIn_dihedral_spor
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* NativeSporadic.M24) ∨ Nonempty (X ≃* NativeSporadic.He))
    {D : Subgroup X} {c d : X} {K : Subgroup X} (h : InnerConfig424 X D c d K) :
    Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6) := by
  have hcases : Nonempty (Automizer D ≃* DihedralGroup 6) ∨ Nonempty (Automizer D ≃* GL23) := by
    rcases hX with hM | hH
    · exact automizer_m24 hM h.card_eq
    · exact automizer_he hH h.card_eq
  rcases hcases with hq | hgl
  · obtain ⟨q⟩ := hq
    exact ⟨(Sporadic.automizerEquivAutIn D).symm.trans q⟩
  · exact absurd hgl (not_nonempty_gl_of_config h)

theorem not_isPerfect_projImage_glPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hmod : ModThree π (p ^ f)) :
    ¬ Group.IsPerfect (projImage (glPi π 3 (p ^ f) K)) := by
  intro hperf
  obtain ⟨m, hker, -, A₀, hA₀, hA₀m⟩ := Sec14.exists_detPow_data_glPi hK hmod
  obtain ⟨δ, hδ⟩ := Sec14.exists_detPow_projImage (glPi π 3 (p ^ f) K) m hker
  apply hA₀m
  have h1 : commutator (projImage (glPi π 3 (p ^ f) K)) ≤ δ.ker :=
    Abelianization.commutator_subset_ker δ
  rw [hperf.commutator_eq_top] at h1
  have h2 := h1 (Subgroup.mem_top ⟨Matrix.ProjGenLinGroup.mk A₀,
    Subgroup.mem_map.mpr ⟨A₀, hA₀, rfl⟩⟩)
  rw [MonoidHom.mem_ker, hδ A₀ hA₀] at h2
  exact h2

end Res424Two

open Res424Two

theorem k424Pairing_of
    (hL : K424PairingLie) (hS : K424PairingSpor) : K424Pairing := by
  intro X _ _ hX hq hZ hSL h424 D c d K hC
  rcases h424 with hG2 | hD4 | ⟨p, e, hp, he, hπ⟩ | ⟨π, p, f, F, _, hF, hmod, ⟨φ⟩⟩ | hM | hH
  · exact Or.inl ⟨Or.inl hG2, hL X hX hq hZ hSL (Or.inl hG2) D c d K hC⟩
  · exact Or.inl ⟨Or.inr hD4, hL X hX hq hZ hSL (Or.inr hD4) D c d K hC⟩
  · exact absurd (Or.inr ⟨p, e, hp, he, hπ⟩) hSL
  · exfalso
    have : Group.IsPerfect X := hq.1
    exact not_isPerfect_projImage_glPi hF hmod
      (Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective)
  · exact Or.inr ⟨Or.inl hM, hS X (Or.inl hM) D c d K hC,
      nonempty_autIn_dihedral_spor (Or.inl hM) hC⟩
  · exact Or.inr ⟨Or.inr hH, hS X (Or.inr hH) D c d K hC,
      nonempty_autIn_dihedral_spor (Or.inr hH) hC⟩

end CFSG.RankThree.PartTwo.Sec4
