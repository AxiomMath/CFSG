module

public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

structure Cfg10Mod (X Fs : Subgroup (MulAut W)) (I₁ I₂ : Subgroup W) : Prop where
  sq : ∀ w : W, w ^ 2 = 1
  le : Fs ≤ X
  el : IsElemAbelianOfRank 3 3 ↥Fs
  norm : ∀ x ∈ X, ∀ f ∈ Fs, x * f * x⁻¹ ∈ Fs
  self : ∀ x ∈ X, (∀ f ∈ Fs, x * f = f * x) → x ∈ Fs
  ne : I₁ ≠ I₂
  orb : conjSubs X I₁ = {I₁, I₂}
  inf : I₁ ⊓ I₂ = ⊥
  sup : I₁ ⊔ I₂ = ⊤
  rk₁ : rk ↥I₁ = 4
  rk₂ : rk ↥I₂ = 4

section FStar

variable [Finite W]

theorem s16c167_cfg10_fstar_facts (X : Subgroup (MulAut W)) :
    Fstar X ≤ X ∧ (∀ x ∈ X, ∀ f ∈ Fstar X, x * f * x⁻¹ ∈ Fstar X) ∧
      (∀ x ∈ X, (∀ f ∈ Fstar X, x * f = f * x) → x ∈ Fstar X) := by
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx f hf
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf
    have hn := CFSG.ClassicalInvolution.Q3.genFittingFStar_isNormal (X := ↥X)
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * f' * ⟨x, hx⟩⁻¹, hn.conj_mem f' hf' ⟨x, hx⟩, rfl⟩
  · intro x hx h
    have hc : (⟨x, hx⟩ : ↥X) ∈
        Subgroup.centralizer (genFittingFStar ↥X : Set ↥X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f' hf'
      exact Subtype.ext (h _ (Subgroup.mem_map_of_mem _ hf')).symm
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hx⟩, CFSG.ClassicalInvolution.Q3.centralizer_genFittingFStar_le hc, rfl⟩

end FStar

section FFacts

variable {Fs : Subgroup (MulAut W)}

theorem s16c167_cfg10_F_comm (hel : IsElemAbelianOfRank 3 3 ↥Fs) :
    ∀ f ∈ Fs, ∀ g ∈ Fs, f * g = g * f := by
  obtain ⟨e⟩ := hel
  intro f hf g hg
  have h : e ⟨f, hf⟩ * e ⟨g, hg⟩ = e ⟨g, hg⟩ * e ⟨f, hf⟩ := mul_comm _ _
  have h2 : (⟨f, hf⟩ * ⟨g, hg⟩ : ↥Fs) = ⟨g, hg⟩ * ⟨f, hf⟩ :=
    e.injective (by rw [map_mul, map_mul]; exact h)
  exact congrArg Subtype.val h2

theorem s16c167_cfg10_F_pow (hel : IsElemAbelianOfRank 3 3 ↥Fs) :
    ∀ f ∈ Fs, f * f * f = 1 := by
  obtain ⟨e⟩ := hel
  intro f hf
  have h : (⟨f, hf⟩ : ↥Fs) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    ext i
    simp
    exact Or.inl (by decide)
  have h3 : (⟨f, hf⟩ : ↥Fs) * ⟨f, hf⟩ * ⟨f, hf⟩ = 1 := (pow_three' _).symm.trans h
  exact congrArg Subtype.val h3

theorem s16c167_cfg10_F_card (hel : IsElemAbelianOfRank 3 3 ↥Fs) : Nat.card ↥Fs = 27 := by
  obtain ⟨e⟩ := hel
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

end FFacts

variable [Finite W]

theorem s16c167_cfg10_mk (hW : ∀ w : W, w ^ 2 = 1) {X Fs : Subgroup (MulAut W)} {J : Subgroup W}
    (hle : Fs ≤ X) (hel : IsElemAbelianOfRank 3 3 ↥Fs)
    (hnorm : ∀ x ∈ X, ∀ f ∈ Fs, x * f * x⁻¹ ∈ Fs)
    (hself : ∀ x ∈ X, (∀ f ∈ Fs, x * f = f * x) → x ∈ Fs)
    (horb : (conjSubs X J).ncard = 2) (hind : sSupIndep (conjSubs X J))
    (hsup : sSup (conjSubs X J) = ⊤) (hrk : ∀ I ∈ conjSubs X J, rk ↥I = 4) :
    ∃ I₂ : Subgroup W, Cfg10Mod X Fs J I₂ := by
  have hJmem : J ∈ conjSubs X J := ⟨1, X.one_mem, (Subgroup.map_id J).symm⟩
  obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.1 horb
  have hJab : J ∈ ({a, b} : Set (Subgroup W)) := hset ▸ hJmem
  obtain ⟨I₂, hne, horb'⟩ : ∃ I₂, J ≠ I₂ ∧ conjSubs X J = {J, I₂} := by
    rcases hJab with h | h
    · subst h
      exact ⟨b, hab, hset⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact ⟨a, hab.symm, by rw [hset, Set.pair_comm]⟩
  refine ⟨I₂, ⟨hW, hle, hel, hnorm, hself, hne, horb', ?_, ?_, ?_, ?_⟩⟩
  · have h := hind
    rw [horb'] at h
    exact disjoint_iff.mp ((sSupIndep_pair hne).mp h)
  · have h : sSup ({J, I₂} : Set (Subgroup W)) = ⊤ := by rw [← horb']; exact hsup
    rwa [sSup_pair] at h
  · exact hrk J hJmem
  · exact hrk I₂ (by rw [horb']; simp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
