module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.S12.ReflField

public section

namespace CFSG.RankThree.PartOne.N143

variable {G : Type} [Group G] {p : ℕ} {A : Subgroup G}

@[expose] def Xsub (A : Subgroup G) (Xs : Subgroup (MulAut A)) : Subgroup G :=
  (Xs.comap A.normalizerMonoidHom).map (Subgroup.normalizer (A : Set G)).subtype

theorem mem_Xsub {Xs : Subgroup (MulAut A)} {x : G} :
    x ∈ Xsub A Xs ↔ ∃ hx : x ∈ Subgroup.normalizer (A : Set G),
      A.normalizerMonoidHom ⟨x, hx⟩ ∈ Xs := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Xsub_le_normalizer (Xs : Subgroup (MulAut A)) :
    Xsub A Xs ≤ Subgroup.normalizer (A : Set G) := fun _ hx => (mem_Xsub.1 hx).1

@[expose] noncomputable def rhoX (Xs : Subgroup (MulAut A)) : ↥(Xsub A Xs) →* ↥Xs :=
  (A.normalizerMonoidHom.comp (Subgroup.inclusion (Xsub_le_normalizer Xs))).codRestrict Xs
    fun x => (mem_Xsub.1 x.2).2

@[expose] noncomputable def piX (Xs : Subgroup (MulAut A)) : ↥(Xsub A Xs) →* MulAut A :=
  A.normalizerMonoidHom.comp (Subgroup.inclusion (Xsub_le_normalizer Xs))

theorem piX_apply (Xs : Subgroup (MulAut A)) (x : ↥(Xsub A Xs)) (a : A) :
    ((piX Xs x a : A) : G) = (x : G) * a * (x : G)⁻¹ := rfl

theorem piX_eq (Xs : Subgroup (MulAut A)) (x : ↥(Xsub A Xs)) :
    piX Xs x = A.normalizerMonoidHom ⟨x, (mem_Xsub.1 x.2).1⟩ := rfl

theorem mem_ker_piX (Xs : Subgroup (MulAut A)) (x : ↥(Xsub A Xs)) :
    x ∈ (piX Xs).ker ↔ ∀ a ∈ A, (x : G) * a * (x : G)⁻¹ = a := by
  constructor
  · intro hx a ha
    have h : piX Xs x = 1 := hx
    have := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h
    simp only [MulAut.one_apply] at this
    rw [← piX_apply Xs x ⟨a, ha⟩]
    exact this
  · intro h
    show piX Xs x = 1
    ext a
    exact h a a.2

theorem range_piX (Xs : Subgroup (MulAut A)) (hXs : Xs ≤ A.normalizerMonoidHom.range) :
    (piX Xs).range = Xs := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact (mem_Xsub.1 x.2).2
  · intro y hy
    obtain ⟨w, hw⟩ := hXs hy
    refine ⟨⟨(w : G), mem_Xsub.2 ⟨w.2, ?_⟩⟩, ?_⟩
    · simpa using (hw ▸ hy : A.normalizerMonoidHom w ∈ Xs)
    · rw [piX_eq]
      simpa using hw

theorem centralizer_le_Xsub (Xs : Subgroup (MulAut A)) :
    Subgroup.centralizer (A : Set G) ≤ Xsub A Xs := by
  intro d hd
  have hdN : d ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hd
  refine mem_Xsub.2 ⟨hdN, ?_⟩
  have : A.normalizerMonoidHom ⟨d, hdN⟩ = 1 := by
    ext a
    show d * (a : G) * d⁻¹ = a
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hd a a.2).symm
  rw [this]
  exact Xs.one_mem

end CFSG.RankThree.PartOne.N143
