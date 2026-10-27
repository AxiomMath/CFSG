module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Reconstruction

namespace CFSG
end CFSG
open CFSG

/-!
# Projective-line points as root Sylow subgroups of `PSL₂`

The point stabilizer of infinity and the conjugation stabilizer of the
standard defining-characteristic Sylow subgroup are both the standard Borel.
Transitivity therefore identifies projective-line points equivariantly with
defining-characteristic Sylow subgroups.  Transporting the natural action of
`MulAut (PSL₂ K)` on those Sylow subgroups gives the point permutation used in
Dieudonne's automorphism proof.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped MatrixGroups

universe u

/-- The chosen Sylow structure on the standard upper-unipotent root group. -/
public noncomputable def psl2UpperUnipotentSylow
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) : Sylow p (PSL2 K) :=
  Classical.choose (psl2UpperUnipotent_isSylow K hKcard)

@[simp]
public theorem psl2UpperUnipotentSylow_coe
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    (psl2UpperUnipotentSylow K hKcard : Subgroup (PSL2 K)) =
      psl2UpperUnipotentSubgroup K :=
  Classical.choose_spec (psl2UpperUnipotent_isSylow K hKcard)

/-- The projective line is equivariantly equivalent to the set of
defining-characteristic Sylow subgroups. -/
public theorem exists_psl2ProjectiveLineEquivSylow
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    ∃ e : PSL2ProjectiveLine K ≃ Sylow p (PSL2 K),
      ∀ g : PSL2 K, ∀ x : PSL2ProjectiveLine K,
        e (g • x) = g • e x := by
  apply
    BenderSuzuki.PFchapter4section1.exists_equivariant_equiv_of_stabilizer_map_eq
      (MulEquiv.refl (PSL2 K)) (psl2ProjectiveInfinity K)
      (psl2UpperUnipotentSylow K hKcard)
  have hrefl :
      (MulEquiv.refl (PSL2 K)).toMonoidHom =
        MonoidHom.id (PSL2 K) := rfl
  rw [hrefl, Subgroup.map_id]
  change psl2Borel K =
    MulAction.stabilizer (PSL2 K)
      (psl2UpperUnipotentSylow K hKcard)
  rw [Sylow.stabilizer_eq_normalizer,
    ← psl2UpperUnipotent_normalizer_eq_borel]
  congr 1
  exact congrArg (fun H : Subgroup (PSL2 K) => (H : Set (PSL2 K)))
    (psl2UpperUnipotentSylow_coe K hKcard).symm

/-- The chosen equivariant identification of projective-line points with
defining-characteristic Sylow subgroups. -/
public noncomputable def psl2ProjectiveLineEquivSylow
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    PSL2ProjectiveLine K ≃ Sylow p (PSL2 K) :=
  Classical.choose (exists_psl2ProjectiveLineEquivSylow K hKcard)

public theorem psl2ProjectiveLineEquivSylow_equivariant
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (g : PSL2 K) (x : PSL2ProjectiveLine K) :
    psl2ProjectiveLineEquivSylow K hKcard (g • x) =
      g • psl2ProjectiveLineEquivSylow K hKcard x :=
  Classical.choose_spec (exists_psl2ProjectiveLineEquivSylow K hKcard) g x

/-- Under the projective-line/root-Sylow equivalence, a point stabilizer is
the normalizer of the corresponding Sylow subgroup. -/
public theorem psl2ProjectiveLineEquivSylow_stabilizer
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (x : PSL2ProjectiveLine K) :
    MulAction.stabilizer (PSL2 K) x =
      Subgroup.normalizer
        (psl2ProjectiveLineEquivSylow K hKcard x :
          Subgroup (PSL2 K)) := by
  calc
    MulAction.stabilizer (PSL2 K) x =
        MulAction.stabilizer (PSL2 K)
          (psl2ProjectiveLineEquivSylow K hKcard x) := by
      ext g
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro hg
        calc
          g • psl2ProjectiveLineEquivSylow K hKcard x =
              psl2ProjectiveLineEquivSylow K hKcard (g • x) :=
            (psl2ProjectiveLineEquivSylow_equivariant K hKcard g x).symm
          _ = psl2ProjectiveLineEquivSylow K hKcard x := by rw [hg]
      · intro hg
        apply (psl2ProjectiveLineEquivSylow K hKcard).injective
        calc
          psl2ProjectiveLineEquivSylow K hKcard (g • x) =
              g • psl2ProjectiveLineEquivSylow K hKcard x :=
            psl2ProjectiveLineEquivSylow_equivariant K hKcard g x
          _ = psl2ProjectiveLineEquivSylow K hKcard x := hg
    _ = Subgroup.normalizer
        (psl2ProjectiveLineEquivSylow K hKcard x :
          Subgroup (PSL2 K)) :=
      Sylow.stabilizer_eq_normalizer _

/-- The reconstructed root Sylow attached to infinity is the chosen standard
upper-unipotent Sylow subgroup. -/
public theorem psl2ProjectiveLineEquivSylow_infinity
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    psl2ProjectiveLineEquivSylow K hKcard
        (psl2ProjectiveInfinity K) =
      psl2UpperUnipotentSylow K hKcard := by
  let P : Sylow p (PSL2 K) :=
    psl2ProjectiveLineEquivSylow K hKcard
      (psl2ProjectiveInfinity K)
  let U : Sylow p (PSL2 K) := psl2UpperUnipotentSylow K hKcard
  let B : Subgroup (PSL2 K) := psl2Borel K
  have hBP : B = Subgroup.normalizer (P : Subgroup (PSL2 K)) := by
    exact psl2ProjectiveLineEquivSylow_stabilizer K hKcard
      (psl2ProjectiveInfinity K)
  have hPleB : (P : Subgroup (PSL2 K)) ≤ B := by
    rw [hBP]
    exact Subgroup.le_normalizer
  have hPnormal : (((P : Subgroup (PSL2 K)).subgroupOf B)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPleB).2
    rw [hBP]
  have hUleB : (U : Subgroup (PSL2 K)) ≤ B := by
    rw [psl2UpperUnipotentSylow_coe]
    exact psl2UpperUnipotent_le_borel
  let PSyl : Sylow p B := P.subtype hPleB
  let USyl : Sylow p B := U.subtype hUleB
  have hPSylNormal : (PSyl : Subgroup B).Normal := by
    change (((P : Subgroup (PSL2 K)).subgroupOf B)).Normal
    exact hPnormal
  let : Unique (Sylow p B) := Sylow.unique_of_normal PSyl hPSylNormal
  have hsub : PSyl = USyl := Subsingleton.elim _ _
  exact Sylow.subtype_injective hsub

/-- The permutation of the projective line induced by an arbitrary group
automorphism of `PSL₂`, obtained from its action on defining-characteristic
Sylow subgroups. -/
@[expose]
public def psl2MulAutProjectiveLine
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    MulAut (PSL2 K) →* Equiv.Perm (PSL2ProjectiveLine K) :=
  (psl2ProjectiveLineEquivSylow K hKcard).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (MulAut (PSL2 K)) (Sylow p (PSL2 K)))

@[simp]
public theorem psl2MulAutProjectiveLine_apply
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (x : PSL2ProjectiveLine K) :
    psl2MulAutProjectiveLine K hKcard alpha x =
      (psl2ProjectiveLineEquivSylow K hKcard).symm
      (alpha • psl2ProjectiveLineEquivSylow K hKcard x) :=
  rfl

/-- The projective-line permutation reconstructed from an automorphism
intertwines the original `PSL₂` action with the action twisted by that
automorphism. -/
public theorem psl2MulAutProjectiveLine_smul
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (alpha : MulAut (PSL2 K)) (g : PSL2 K)
    (x : PSL2ProjectiveLine K) :
    psl2MulAutProjectiveLine K hKcard alpha (g • x) =
      alpha g • psl2MulAutProjectiveLine K hKcard alpha x := by
  apply (psl2ProjectiveLineEquivSylow K hKcard).injective
  rw [psl2MulAutProjectiveLine_apply,
    psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply]
  rw [psl2ProjectiveLineEquivSylow_equivariant,
    psl2ProjectiveLineEquivSylow_equivariant]
  rw [Equiv.apply_symm_apply]
  have hconj :
      alpha * MulAut.conj g = MulAut.conj (alpha g) * alpha := by
    ext y
    simp [MulAut.conj_apply]
  rw [Sylow.smul_def, Sylow.smul_def,
    ← mul_smul, ← mul_smul, hconj]

/-- An automorphism of `PSL₂(K)` is determined by its induced permutation of
the reconstructed projective line. -/
public theorem psl2MulAutProjectiveLine_injective
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    Function.Injective (psl2MulAutProjectiveLine K hKcard) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro alpha halpha
  change psl2MulAutProjectiveLine K hKcard alpha = 1 at halpha
  apply MulEquiv.ext
  intro g
  apply FaithfulSMul.eq_of_smul_eq_smul
    (α := PSL2ProjectiveLine K)
  intro x
  have h := psl2MulAutProjectiveLine_smul K hKcard alpha g x
  rw [halpha] at h
  simpa using h.symm

/-- For an inner automorphism, the induced point permutation is the original
projective action. -/
@[simp]
public theorem psl2MulAutProjectiveLine_conj
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (g : PSL2 K) (x : PSL2ProjectiveLine K) :
    psl2MulAutProjectiveLine K hKcard (MulAut.conj g) x = g • x := by
  apply (psl2ProjectiveLineEquivSylow K hKcard).injective
  rw [psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply]
  exact (psl2ProjectiveLineEquivSylow_equivariant K hKcard g x).symm

end CFSG.GorensteinWalter
