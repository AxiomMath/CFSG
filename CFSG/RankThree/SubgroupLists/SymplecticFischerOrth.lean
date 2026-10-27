module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerExcl
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.Fischer.Classification.Symplectic.OrthoGen

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Open CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem eq_one_of_isPerfect {G A : Type*} [Group G] [CommGroup A] (hG : Group.IsPerfect G)
    (φ : G →* A) (g : G) : φ g = 1 := by
  have h := Abelianization.commutator_subset_ker φ
  rw [hG.commutator_eq_top] at h
  exact h (Subgroup.mem_top g)

theorem not_isPerfect_orthogonalGroup {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    ¬ Group.IsPerfect (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  intro hP
  have h2 := relIndex_omegaGroup Q hQ
  have hker : (dicksonHom Q hQ).ker = ⊤ :=
    eq_top_iff.2 fun g _ => (MonoidHom.mem_ker).2 (eq_one_of_isPerfect hP _ g)
  rw [Subgroup.relIndex, ← dicksonHom_ker, hker, Subgroup.index_top] at h2
  exact absurd h2 (by norm_num)

theorem not_isPerfect_isometryMatrixGroup {n : ℕ} (hn : 0 < n)
    (Q : QuadraticForm (ZMod 2) (Fin n → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    ¬ Group.IsPerfect (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) := by
  intro hP
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [QuadraticMap.polar_comm]; simpa using hy x⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hH := CFSG.Fischer.Classification.fischerMatrixGroup_isometry_eq_comap Q
  set H := fischerMatrixGroup fun A : Matrix (Fin n) (Fin n) (ZMod 2) => ∀ x, Q (A *ᵥ x) = Q x
  set e := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) (ZMod 2)
  have hmem : ∀ g, g ∈ H ↔ e g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g => by
    rw [hH]
    rfl
  let φ : H →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    (e.toMonoidHom.comp H.subtype).codRestrict _ fun g => (hmem g).1 g.2
  have hφ : Function.Surjective φ := by
    intro o
    refine ⟨⟨e.symm o, (hmem _).2 (by simp)⟩, Subtype.ext ?_⟩
    simp [φ]
  have := hP
  exact not_isPerfect_orthogonalGroup Q hQ (Group.IsPerfect.ofSurjective hφ)

theorem fischerOrthCard : FischerOrthCard := fun _ hm Q hnd hP =>
  (not_isPerfect_isometryMatrixGroup (by omega) Q hnd hP).elim

theorem fischerOrthClique : FischerOrthClique := fun _ hm Q hnd hP =>
  (not_isPerfect_isometryMatrixGroup (by omega) Q hnd hP).elim

end CFSG.RankThree.SubgroupLists
