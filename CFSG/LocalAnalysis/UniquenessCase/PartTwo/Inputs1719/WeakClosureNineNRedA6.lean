module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6PGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6M10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81

theorem nonempty_mulEquiv_alt6_of_modelFacts {Y : Type} [Group Y] {G L₀ T₀ : Subgroup Y}
    (hM : NFA6.ModelFacts G L₀ T₀) (eL : L₀ ≃* alternatingGroup (Fin 6)) {A : Type} [Group A]
    (e : A ≃* G) {K : Subgroup A} (hKn : K.Normal) (hK1 : K ≠ ⊥) (hKp : ⁅K, K⁆ = K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  set ι : A →* Y := G.subtype.comp e.toMonoidHom with hιdef
  have hι : Function.Injective ι := G.subtype_injective.comp e.injective
  have hr : ι.range = G := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [ι]⟩
  have hmapG : K.map ι ≤ G := hr ▸ map_le_range ι K
  have hL : K.map ι = L₀ := by
    refine le_antisymm ?_ (hM.le_of_normal _ hmapG ?_ ?_)
    · rw [← hKp, map_commutator, commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      exact hM.commutator_mem (hmapG hx) (hmapG hy)
    · intro g' hg' y hy
      rw [← hr] at hg'
      obtain ⟨h, rfl⟩ := hg'
      obtain ⟨l, hl, rfl⟩ := hy
      exact ⟨h * l * h⁻¹, hKn.conj_mem l hl h, by simp⟩
    · rwa [Ne, map_eq_bot_iff_of_injective _ hι]
  exact ⟨((K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hL)).trans eL⟩

theorem nonempty_mulEquiv_alt6 {A : Type} [Group A]
    (hA : CFSG.Quasithin.F6.IsPGL2 9 A ∨ Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨
      Inputs1719.IsM10 A)
    {K : Subgroup A} (hKn : K.Normal) (hK1 : K ≠ ⊥) (hKp : ⁅K, K⁆ = K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨-, eL, -, -⟩ := CFSG.QuasithinUnique.Unc25K1.A6Model.exists_pslEquiv
  rcases hA with h | h | h
  · obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_pgl29_of_isPGL2 h
    exact nonempty_mulEquiv_alt6_of_modelFacts NFA6.PGLModel.modelFacts eL e hKn hK1 hKp
  · obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_autA6_of_isAutOf h
    exact nonempty_mulEquiv_alt6_of_modelFacts NFA6.AutModel.modelFacts eL e hKn hK1 hKp
  · obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_m10_of_isM10 h
    exact nonempty_mulEquiv_alt6_of_modelFacts NFA6.M10Model.modelFacts eL e hKn hK1 hKp

theorem card_center_eq_three {Z : Type} [Group Z] [Finite Z] {Lb : Subgroup Z} [hLbn : Lb.Normal]
    (hq : CFSG.IsQuasisimple Lb) (hLbp : ⁅Lb, Lb⁆ = Lb)
    {A : Type} [Group A] (ρ : Z →* A) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = centralizer (Lb : Set Z))
    (hA : CFSG.Quasithin.F6.IsPGL2 9 A ∨ Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨
      Inputs1719.IsM10 A)
    (hodd : Odd (Nat.card (center Lb))) (hne : center Lb ≠ ⊥) :
    Nat.card (center Lb) = 3 := by
  set K := Lb.map ρ with hK
  have hKn : K.Normal := hLbn.map ρ hρs
  have hmemk : ∀ l : Lb, ρ l = 1 ↔ l ∈ center Lb := by
    intro l
    rw [← MonoidHom.mem_ker, hρk, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h l'
      exact Subtype.ext (h _ l'.2)
    · intro h z hz
      exact congrArg Subtype.val (h ⟨z, hz⟩)
  have hK1 : K ≠ ⊥ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a ∈ center Lb := (hmemk a).mp (by
      have h1 : ρ a ∈ K := mem_map_of_mem ρ a.2
      rwa [hbot, mem_bot] at h1)
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp ha b]
  have hKp : ⁅K, K⁆ = K := by rw [hK, ← map_commutator, hLbp]
  obtain ⟨eK⟩ := nonempty_mulEquiv_alt6 hA hKn hK1 hKp
  let ρL : Lb →* K := (ρ.comp Lb.subtype).codRestrict K fun l => mem_map_of_mem ρ l.2
  have hρLs : Function.Surjective ρL := by
    rintro ⟨k, l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  let q : Lb →* alternatingGroup (Fin 6) := eK.toMonoidHom.comp ρL
  have hqs : Function.Surjective q := eK.surjective.comp hρLs
  have hqk : q.ker = center Lb := by
    ext l
    rw [MonoidHom.mem_ker, ← hmemk]
    change eK (ρL l) = 1 ↔ _
    rw [map_eq_one_iff _ eK.injective]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have : Group.IsPerfect Lb := hq.1
  have h := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 6) (by norm_num)
    (by norm_num) q hqs hqk.le (by rw [hqk]; exact hodd)).2 (Or.inl rfl)
  rw [hqk] at h
  rcases h with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
  · exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914
