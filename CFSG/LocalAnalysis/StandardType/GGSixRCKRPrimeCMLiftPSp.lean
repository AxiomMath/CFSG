module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSp

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma rck_lift_choose {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    {s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {b : X} (hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hbID : GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b) (hbe : Commute b e) :
    ∃ s_b : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      (∀ u, b⁻¹ * ψ u * b = ψ (s_b * u * s_b⁻¹)) ∧
        Commute (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
          (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
  obtain ⟨s_b, hs_b⟩ := exists_conj_eq_PSp n (GaloisField 2 f) ψ hker hbN hbID
  have hcommSub : Commute s_b s :=
    conj_eq_commute_PSp n (GaloisField 2 f) ψ hker hbe hs_b hs
  refine ⟨s_b, hs_b, ?_⟩
  change (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) =
    (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
  exact congrArg Subtype.val hcommSub.eq

private lemma rck_lift_block {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X}
    {s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {b : X}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
          Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJ'G : J' ≤ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε)
    {s_b : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hs_b : ∀ u, b⁻¹ * ψ u * b = ψ (s_b * u * s_b⁻¹))
    (hcomm : Commute (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
    ∃ s₁' : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      s₁' ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε ∧
        (∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁' * y * s₁'⁻¹)) := by
  have hS : ∀ a ∈ ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
      Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ b' ∈ ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
        Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute a b' := by
    intro a ha b' hb'
    rw [Set.mem_singleton_iff] at ha hb'
    rw [ha, hb']
  have hs' : ∀ t ∈ ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
      Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      Commute (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) t := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hcomm
  obtain ⟨hs_bε, s₁, hs₁def, hs₁mem, _hs₁ord, hs₁conj⟩ :=
    rckGLBlock_restrict (S := ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
      Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))) hS hε.1 hε.2.1
      (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) hs'
  have hs₁sp : s₁ ∈ CFSG.Open.StatedSp n (GaloisField 2 f) :=
    rckGLBlock_restrict_mem_statedSp (hadj := hε.2.2.2.1) hε.2.1 s_b.2 hs_bε hs₁def
  let s₁' : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) := ⟨s₁, hs₁sp⟩
  have hblock : s₁' ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε := by
    rw [glBlockCentralizer, Subgroup.mem_comap]; exact hs₁mem
  refine ⟨s₁', hblock, ?_⟩
  intro y hy
  have hyblock : (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      Subgroup.centralizer ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
        Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) ⊓ glFixing (1 - ε) :=
    Subgroup.mem_comap.mp (hJ'G hy)
  have hyEq : (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s_b : GL (Fin n ⊕ Fin n) (GaloisField 2 f))⁻¹ =
      (s₁' : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s₁' : GL (Fin n ⊕ Fin n) (GaloisField 2 f))⁻¹ :=
    hs₁conj (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) hyblock
  rw [hs_b y]
  exact congrArg ψ (Subtype.ext hyEq)

private lemma rck_lift_map_eq {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X}
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {b : X}
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X))
    {s₁' : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hact : ∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁' * y * s₁'⁻¹)) :
    (J'.map (MulAut.conj s₁').toMonoidHom).map ψ = J'.map ψ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hact y hy]
    exact (Subgroup.mem_normalizer_iff''.mp hbK (ψ y)).mp
      (Subgroup.mem_map_of_mem ψ hy)
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyK : b * ψ y * b⁻¹ ∈ J'.map ψ :=
      (Subgroup.mem_normalizer_iff.mp hbK (ψ y)).mp (Subgroup.mem_map_of_mem ψ hy)
    rw [Subgroup.mem_map] at hyK
    obtain ⟨y', hy', hy'eq⟩ := hyK
    refine ⟨s₁' * y' * s₁'⁻¹, ?_, ?_⟩
    · change s₁' * y' * s₁'⁻¹ ∈
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj s₁')) J'
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj s₁').toMonoidHom hy'
    · rw [show ψ (s₁' * y' * s₁'⁻¹) = b⁻¹ * ψ y' * b from (hact y' hy').symm,
        hy'eq]
      group

theorem rckLiftToBlock_PSp {n f : ℕ} {X : Type} [Group X]
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X} (hker : ψ.ker ≤ Subgroup.center _)
    {s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
          Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJ'G : J' ≤ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε)
    (hperf : ⁅J', J'⁆ = J') {b : X} (hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hbID : GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b) (hbe : Commute b e)
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X)) :
    ∃ s₁ ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε,
      s₁ ∈ Subgroup.normalizer (J' : Set ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) ∧
        ∀ y ∈ J', b⁻¹ * ψ y * b = ψ (s₁ * y * s₁⁻¹) := by
  obtain ⟨s_b, hs_b, hcomm⟩ := rck_lift_choose hker hs hbN hbID hbe
  obtain ⟨s₁', hblock, hact⟩ := rck_lift_block hε hJ'G hs_b hcomm
  have hmap : (J'.map (MulAut.conj s₁').toMonoidHom).map ψ = J'.map ψ :=
    rck_lift_map_eq hbK hact
  exact ⟨s₁', hblock, rckNormalizes_of_map_eq hker hperf hmap, hact⟩

end CFSG.StandardType.RCKRP
