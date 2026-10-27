module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleProj

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

lemma w1369_ta_bijective_of_ne_one {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {A B : Subgroup Q} (hA : w1369_ta_IsSimple Λ A) (hB : w1369_ta_IsSimple Λ B)
    {f : A →* B}
    (hf : ∀ g (hg : g ∈ Λ), ∀ x : A,
      (f ⟨g (x : Q), hA.2.1 g hg (x : Q) x.2⟩ : Q) = g (f x : Q))
    (hf0 : f ≠ 1) : Function.Bijective f := by
  have hKstable : StableUnder Λ (f.ker.map A.subtype) := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨g (y : Q), hA.2.1 g hg (y : Q) y.2⟩, ?_, rfl⟩
    have h := hf g hg y
    rw [MonoidHom.mem_ker.mp hy] at h
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (by simpa using h)
  have hKle : (f.ker.map A.subtype) ≤ A := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hKne : (f.ker.map A.subtype) ≠ A := by
    intro htop
    apply hf0
    ext x
    have hx : (x : Q) ∈ f.ker.map A.subtype := by rw [htop]; exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    simpa using hy
  have hker : f.ker = ⊥ := by
    rcases hA.2.2 _ hKstable hKle with h | h
    · rw [← le_bot_iff]
      intro x hx
      have : (A.subtype x) ∈ f.ker.map A.subtype := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [h] at this
      simpa using this
    · exact absurd h hKne
  refine ⟨(MonoidHom.ker_eq_bot_iff f).mp hker, ?_⟩
  have hLstable : StableUnder Λ (f.range.map B.subtype) := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hy
    refine Subgroup.mem_map.mpr ⟨f ⟨g (z : Q), hA.2.1 g hg (z : Q) z.2⟩, ⟨_, rfl⟩, ?_⟩
    change (f ⟨g (z : Q), hA.2.1 g hg (z : Q) z.2⟩ : Q) = g (y : Q)
    exact (hf g hg z).trans (congrArg (fun w : B => g (w : Q)) hz)
  have hLle : (f.range.map B.subtype) ≤ B := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hLne : (f.range.map B.subtype) ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
    have : (f x : Q) ∈ f.range.map B.subtype :=
      Subgroup.mem_map.mpr ⟨f x, ⟨x, rfl⟩, rfl⟩
    rw [hbot] at this
    have h1 : f x = 1 := by simpa using this
    exact hx ((MonoidHom.ker_eq_bot_iff f).mp hker (by rw [h1, map_one]))
  have himg : f.range.map B.subtype = B := by
    rcases hB.2.2 _ hLstable hLle with h | h
    · exact absurd h hLne
    · exact h
  intro y
  have hy : (y : Q) ∈ f.range.map B.subtype := by rw [himg]; exact y.2
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hz
  exact ⟨x, Subtype.ext (by rw [hx]; exact hzy)⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
