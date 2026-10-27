module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSp

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma rckLiftHom_rho_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {ε : Matrix ι ι F} (hε : IsIdempotentElem ε) {x y : Matrix ι ι F}
    (hx : x * ε = ε * x) (hy : y * ε = ε * y) :
    (x * ε + (1 - ε)) * (y * ε + (1 - ε)) = (x * y) * ε + (1 - ε) := by
  have hε' : ε * ε = ε := hε.eq
  have h1 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε']
    abel
  have hx0 : x * ε * (1 - ε) = 0 := by
    rw [mul_assoc, hε.mul_one_sub_self, mul_zero]
  have hy0 : (1 - ε) * (y * ε) = 0 := by
    rw [hy, ← mul_assoc, hε.one_sub_mul_self, zero_mul]
  calc
    (x * ε + (1 - ε)) * (y * ε + (1 - ε))
        = x * ε * (y * ε) + x * ε * (1 - ε) + (1 - ε) * (y * ε) +
            (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * ε * (y * ε) + (1 - ε) * (1 - ε) := by simp [hx0, hy0]
    _ = x * (ε * y) * ε + (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * (y * ε) * ε + (1 - ε) * (1 - ε) := by rw [hy]
    _ = x * y * ε + (1 - ε) := by
      rw [mul_assoc x (y * ε) ε, mul_assoc y ε ε, hε', ← mul_assoc x y ε, h1]

private lemma rckLiftHom_exists_sb {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center _)
    {s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hBID : ∀ b ∈ B, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hBe : ∀ b ∈ B, Commute b e) :
    ∃ sb : ↥B → ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      (∀ (b : ↥B) (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
        ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹)) ∧
      (∀ b : ↥B, Commute (sb b) s) := by
  let sb : ↥B → ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) := fun b =>
    Classical.choose
      (exists_conj_eq_PSp n (GaloisField 2 f) ψ hker (hBN b.2) (hBID b b.2))
  have hsb_spec : ∀ (b : ↥B) (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹) := fun b u =>
    Classical.choose_spec
      (exists_conj_eq_PSp n (GaloisField 2 f) ψ hker (hBN b.2) (hBID b b.2)) u
  refine ⟨sb, hsb_spec, fun b => ?_⟩
  exact conj_eq_commute_PSp n (GaloisField 2 f) ψ hker (hBe b b.2) (hsb_spec b) hs

private lemma rckLiftHom_sb_inv_mul {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center _)
    {B : Subgroup X} {sb : ↥B → ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hsb_spec : ∀ (b : ↥B) (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹)) :
    ∀ b b' : ↥B,
      ((sb (b * b'))⁻¹ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) =
        (sb b)⁻¹ * (sb b')⁻¹ := by
  intro b b'
  have hanti : sb (b * b') = sb b' * sb b := by
    refine conj_eq_unique_PSp n (GaloisField 2 f) ψ hker ?_
    intro u
    rw [← hsb_spec (b * b') u]
    calc ((b * b' : ↥B) : X)⁻¹ * ψ u * ((b * b' : ↥B) : X)
        = (b' : X)⁻¹ * ((b : X)⁻¹ * ψ u * (b : X)) * (b' : X) := by
          simp only [Subgroup.coe_mul]
          group
      _ = (b' : X)⁻¹ * ψ (sb b * u * (sb b)⁻¹) * (b' : X) := by rw [hsb_spec b u]
      _ = ψ (sb b' * (sb b * u * (sb b)⁻¹) * (sb b')⁻¹) := by
          rw [hsb_spec b' (sb b * u * (sb b)⁻¹)]
      _ = ψ ((sb b' * sb b) * u * (sb b' * sb b)⁻¹) := by
          congr 1
          group
  rw [hanti, mul_inv_rev]

private lemma rckLiftHom_exists_blockRestrict {n f : ℕ}
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hS : ∀ u ∈ S, ∀ v ∈ S, Commute u v)
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (s' : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hs' : s' ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hcomm_s' : ∀ u ∈ S, Commute s' u) :
    ∃ s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      ((s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε =
        ε * (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) ∧
      (s₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε + (1 - ε) ∧
      s₁ ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) ∧
      s₁ ∈ CFSG.Open.StatedSp n (GaloisField 2 f) ∧
      (∀ g ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε),
        s' * g * s'⁻¹ = s₁ * g * s₁⁻¹) := by
  obtain ⟨hεcomm, s₁, hform, hmem, -, hconj⟩ :=
    rckGLBlock_restrict (S := S) hS hε.1 hε.2.1 s' hcomm_s'
  exact ⟨s₁, hεcomm, hform, hmem,
    rckGLBlock_restrict_mem_statedSp hε.2.2.2.1 hε.2.1 hs' hεcomm hform, hconj⟩

private lemma rckLiftHom_s₁_mul {n f : ℕ} {B : Type} [Group B]
    {s' s₁ : B → GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hform : ∀ b : B, (s₁ b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (s' b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε + (1 - ε))
    (hε : IsIdempotentElem ε)
    (hεcomm : ∀ b : B, (s' b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε =
      ε * (s' b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hs'_mul : ∀ b b' : B, s' (b * b') = s' b * s' b') :
    ∀ b b' : B, s₁ (b * b') = s₁ b * s₁ b' := by
  intro b b'
  apply Units.ext
  rw [Units.val_mul, hform (b * b'), hform b, hform b', hs'_mul b b']
  exact (rckLiftHom_rho_mul hε (hεcomm b) (hεcomm b')).symm

private lemma rckLiftHom_conj_lift {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X}
    {B : Subgroup X} {sb : ↥B → ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hsb_spec : ∀ (b : ↥B) (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    (b : ↥B) (y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
    (b : X) * ψ y * (b : X)⁻¹ = ψ ((sb b)⁻¹ * y * (sb b)) := by
  have h := hsb_spec b ((sb b)⁻¹ * y * (sb b))
  have h' : (b : X)⁻¹ * ψ ((sb b)⁻¹ * y * (sb b)) * (b : X) = ψ y := by
    rw [h, show sb b * ((sb b)⁻¹ * y * (sb b)) * (sb b)⁻¹ = y by group]
  calc (b : X) * ψ y * (b : X)⁻¹
      = (b : X) * ((b : X)⁻¹ * ψ ((sb b)⁻¹ * y * (sb b)) * (b : X)) *
          (b : X)⁻¹ := by rw [← h']
    _ = ψ ((sb b)⁻¹ * y * (sb b)) := by group

private lemma rckLiftHom_blockAction {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X}
    {B : Subgroup X} {sb : ↥B → ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hsb_spec : ∀ (b : ↥B) (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {s' s₁ : ↥B → GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hs'def : ∀ b : ↥B,
      s' b = (((sb b)⁻¹ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hconj : ∀ b : ↥B, ∀ g ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε),
      s' b * g * (s' b)⁻¹ = s₁ b * g * (s₁ b)⁻¹)
    (hstated : ∀ b : ↥B, s₁ b ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) :
    ∀ (b : ↥B) (y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
      y ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε →
      (b : X) * ψ y * (b : X)⁻¹ =
        ψ ((⟨s₁ b, hstated b⟩ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) * y *
          (⟨s₁ b, hstated b⟩ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))⁻¹) := by
  intro b y hy
  have hyGL : (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      Subgroup.centralizer S ⊓ glFixing (1 - ε) := by
    have h : y ∈ (Subgroup.centralizer S ⊓ glFixing (1 - ε)).comap
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
      simpa [glBlockCentralizer] using hy
    exact Subgroup.mem_comap.mp h
  have hconj_y := hconj b (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) hyGL
  have hblock : ((sb b)⁻¹ * y * (sb b) : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) =
      (⟨s₁ b, hstated b⟩ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) * y *
        (⟨s₁ b, hstated b⟩ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))⁻¹ := by
    apply Subtype.ext
    simpa [hs'def b, Subgroup.coe_mul] using hconj_y
  have hmain := rckLiftHom_conj_lift hsb_spec b y
  calc (b : X) * ψ y * (b : X)⁻¹ = ψ ((sb b)⁻¹ * y * (sb b)) := hmain
    _ = ψ ((⟨s₁ b, hstated b⟩ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) * y *
          (⟨s₁ b, hstated b⟩ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))⁻¹) := by
        rw [hblock]

theorem exists_rckRestrictLiftHom_PSp {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X} (hker : ψ.ker ≤ Subgroup.center _)
    {s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
          Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε)
    {B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hBID : ∀ b ∈ B, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hBe : ∀ b ∈ B, Commute b e) :
    ∃ β : ↥B →* ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε),
      ∀ (b : ↥B) (y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
        y ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
          {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε →
        (b : X) * ψ y * (b : X)⁻¹ =
          ψ ((β b : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) * y *
            (β b : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))⁻¹) := by
  let S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
  have hS : ∀ u ∈ S, ∀ v ∈ S, Commute u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst u; subst v
    exact Commute.refl _
  obtain ⟨sb, hsb_spec, hcomm_s⟩ := rckLiftHom_exists_sb hker hs hBN hBID hBe
  let s' : ↥B → GL (Fin n ⊕ Fin n) (GaloisField 2 f) := fun b =>
    (((sb b)⁻¹ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f))
  have hs' : ∀ b : ↥B, s' b ∈ CFSG.Open.StatedSp n (GaloisField 2 f) := fun b =>
    ((sb b)⁻¹).2
  have hcomm_s' : ∀ b : ↥B, ∀ u ∈ S, Commute (s' b) u := by
    intro b u hu
    rw [Set.mem_singleton_iff] at hu
    subst u
    have hc : Commute ((sb b : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f))
        ((s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
      (hcomm_s b).map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
    have hci := hc.inv_left
    simpa [s'] using hci
  choose s₁ hεcomm hform hmem hstated hconj using fun b : ↥B =>
    rckLiftHom_exists_blockRestrict (S := S) hS hε (s' b) (hs' b) (hcomm_s' b)
  have hblockMem : ∀ b : ↥B,
      (⟨s₁ b, hstated b⟩ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) ∈
        glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε := fun b =>
    Subgroup.mem_comap.mpr (hmem b)
  let βfun : ↥B → ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε) :=
    fun b => ⟨⟨s₁ b, hstated b⟩, hblockMem b⟩
  have hs'_mul : ∀ b b' : ↥B, s' (b * b') = s' b * s' b' := by
    intro b b'
    change (((sb (b * b'))⁻¹ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (((sb b)⁻¹ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (((sb b')⁻¹ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    rw [rckLiftHom_sb_inv_mul hker hsb_spec b b', Subgroup.coe_mul]
  have hs₁_mul : ∀ b b' : ↥B, s₁ (b * b') = s₁ b * s₁ b' :=
    rckLiftHom_s₁_mul hform hε.2.1 hεcomm hs'_mul
  have hβmul : ∀ b b' : ↥B, βfun (b * b') = βfun b * βfun b' := by
    intro b b'
    apply Subtype.ext
    apply Subtype.ext
    exact hs₁_mul b b'
  refine ⟨MonoidHom.mk' βfun hβmul, ?_⟩
  intro b y hy
  simpa [βfun] using
    rckLiftHom_blockAction (S := S) hsb_spec (s' := s') (s₁ := s₁) (fun _ => rfl) hconj
      hstated b y hy

end CFSG.StandardType.RCKRP
