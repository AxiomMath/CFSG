module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.ClassHypB
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

variable {Γ : Type*} [Group Γ]

theorem isSolvable_of_le {K H : Subgroup Γ} (hKH : K ≤ H) (hH : Group.IsSolvable H) :
    Group.IsSolvable K :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
    (Subgroup.inclusion_injective hKH)

variable [Finite Γ]

theorem le_nsOf {p : ℕ} {A G Y : Subgroup Γ} (hY : Y ∈ nsSet p A G) : Y ≤ nsOf p A G :=
  le_iSup₂_of_le Y hY le_rfl

theorem nsOf_le (p : ℕ) (A G : Subgroup Γ) : nsOf p A G ≤ G :=
  iSup₂_le fun _ hY => hY.1

theorem isDAInvariant_of_mem_nsSet {p : ℕ} {A G Y : Subgroup Γ} (hY : Y ∈ nsSet p A G) :
    IsDAInvariant A G Y :=
  ⟨hY.1, hY.2.1, hY.2.2.1⟩

theorem mem_nsSet_of_isDAInvariant {p : ℕ} {A G Y : Subgroup Γ} (hA : IsElemAbelian p A)
    (hB : signalizerMcBrideHypothesisB p Y) (hs : IsDAInvariant A G Y)
    (hY : Group.IsSolvable ↥(Y ⊓ Subgroup.centralizer (A : Set Γ))) : Y ∈ nsSet p A G :=
  ⟨hs.1, hs.2.1, hs.2.2, hA, hB, hY⟩

theorem inf_centralizer_le_normalizer_nsOf (p : ℕ) (A G : Subgroup Γ) :
    G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (nsOf p A G : Set Γ) :=
  CFSG.SignalizerFunctor.Helpers.normalizer_biSup_of_le _ (nsSet p A G) (fun Y => Y)
    fun _ hY => hY.2.1

theorem le_normalizer_nsOf (p : ℕ) (A G : Subgroup Γ) :
    A ≤ Subgroup.normalizer (nsOf p A G : Set Γ) :=
  CFSG.SignalizerFunctor.Helpers.normalizer_biSup_of_le _ (nsSet p A G) (fun Y => Y)
    fun _ hY => hY.2.2.1

theorem isDAInvariant_nsOf (p : ℕ) (A G : Subgroup Γ) : IsDAInvariant A G (nsOf p A G) :=
  ⟨nsOf_le p A G, inf_centralizer_le_normalizer_nsOf p A G, le_normalizer_nsOf p A G⟩

theorem nsOf_mem_nsSet_of_isSolvable {p : ℕ} {A G : Subgroup Γ} (h : KSetting p A G)
    (hs : Group.IsSolvable ↥(nsOf p A G ⊓ Subgroup.centralizer (A : Set Γ))) :
    nsOf p A G ∈ nsSet p A G :=
  mem_nsSet_of_isDAInvariant h.elemAbelian
    (CFSG.SignalizerFunctor.Helpers.mcBrideHypothesisB_of_le p (nsOf_le p A G) h.hypB)
    (isDAInvariant_nsOf p A G) hs

theorem mem_nsSet_of_le {p : ℕ} {A G G' Y : Subgroup Γ} (hG' : G' ≤ G) (hY : Y ∈ nsSet p A G)
    (hYG' : Y ≤ G') : Y ∈ nsSet p A G' :=
  ⟨hYG', (inf_le_inf_right _ hG').trans hY.2.1, hY.2.2.1, hY.2.2.2⟩

omit [Finite Γ] in
theorem mem_normalizer_map_conj_iff {Y : Subgroup Γ} {g t : Γ} :
    t ∈ Subgroup.normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ) ↔
      g⁻¹ * t * g ∈ Subgroup.normalizer (Y : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (g * y * g⁻¹)
    rw [L514.mem_map_conj_iff, L514.mem_map_conj_iff] at h1
    have e : g⁻¹ * (t * (g * y * g⁻¹) * t⁻¹) * g = g⁻¹ * t * g * y * (g⁻¹ * t * g)⁻¹ := by group
    rw [e, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
    exact h1
  · intro h x
    rw [L514.mem_map_conj_iff, L514.mem_map_conj_iff]
    have e : g⁻¹ * (t * x * t⁻¹) * g = g⁻¹ * t * g * (g⁻¹ * x * g) * (g⁻¹ * t * g)⁻¹ := by group
    rw [e]
    exact h (g⁻¹ * x * g)

theorem map_conj_mem_nsSet {p : ℕ} {A G T Y : Subgroup Γ} (hT : IsDAInvariant A G T)
    {g : Γ} (hg : g ∈ G ⊓ Subgroup.centralizer (A : Set Γ)) (hY : Y ∈ nsSet p A T) :
    Y.map (MulAut.conj g).toMonoidHom ∈ nsSet p A T := by
  have hgT : g ∈ Subgroup.normalizer (T : Set Γ) := hT.2.1 hg
  have hcomm : ∀ a ∈ A, g⁻¹ * a * g = a := fun a ha => by
    rw [mul_assoc, Subgroup.mem_centralizer_iff.mp hg.2 a ha, inv_mul_cancel_left]
  refine ⟨?_, fun t ht => ?_, fun a ha => ?_, hY.2.2.2.1, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgT y).mp (hY.1 hy)
  · rw [mem_normalizer_map_conj_iff]
    refine hY.2.1 (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgT) t).mp ht.1
      simpa [mul_assoc] using this
    · exact mul_mem (mul_mem (inv_mem hg.2) ht.2) hg.2
  · rw [mem_normalizer_map_conj_iff, hcomm a ha]
    exact hY.2.2.1 ha
  · exact signalizerMcBrideHypothesisB_map_conj g hY.2.2.2.2.1
  · refine isSolvable_of_le (K := (Y.map (MulAut.conj g).toMonoidHom) ⊓
      Subgroup.centralizer (A : Set Γ)) (H := (Y ⊓ Subgroup.centralizer (A : Set Γ)).map
        (MulAut.conj g).toMonoidHom) ?_ (isSolvable_map_mulEquiv _ hY.2.2.2.2.2)
    rintro _ ⟨hx, hxC⟩
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, Subgroup.mem_inf.mpr ⟨hy, ?_⟩, rfl⟩
    have h1 : g⁻¹ * (g * y * g⁻¹) * g ∈ Subgroup.centralizer (A : Set Γ) :=
      mul_mem (mul_mem (inv_mem hg.2) hxC) hg.2
    simpa [mul_assoc] using h1

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516
