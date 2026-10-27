module

public import CFSG.LocalAnalysis.StandardType.ZS.Support
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.HardMathSupport.Kantor79

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem commutatorSpace_mono {H H' : Subgroup (E ≃ₗ[K] E)} (h : H ≤ H') :
    commutatorSpace H ≤ commutatorSpace H' :=
  Submodule.span_mono fun _ ⟨g, hg, v, hv⟩ => ⟨g, h hg, v, hv⟩

end CFSG.HardMathSupport.Kantor79

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

theorem centralizerSpace_le_of_le {H H' : Subgroup (U ≃ₗ[K] U)} (h : H ≤ H') :
    centralizerSpace H' ≤ centralizerSpace H :=
  fun _ hv => mem_centralizerSpace.mpr fun g hg => mem_centralizerSpace.mp hv g (h hg)

theorem commutatorSpace_map_conj {B : Subgroup (U ≃ₗ[K] U)} (g : U ≃ₗ[K] U) :
    HardMathSupport.Kantor79.commutatorSpace (B.map (MulAut.conj g).toMonoidHom) =
      (HardMathSupport.Kantor79.commutatorSpace B).map (g : U →ₗ[K] U) := by
  rw [HardMathSupport.Kantor79.commutatorSpace, HardMathSupport.Kantor79.commutatorSpace,
    Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨h', hh', hv⟩
    obtain ⟨v, rfl⟩ := hv
    obtain ⟨h, hh, hfh⟩ := (Subgroup.mem_map (f := (MulAut.conj g).toMonoidHom)).mp hh'
    refine ⟨h (g⁻¹ v) - g⁻¹ v, ⟨h, hh, ⟨g⁻¹ v, rfl⟩⟩, ?_⟩
    rw [← hfh]
    simp [LinearEquiv.mul_apply]
  · rintro ⟨x, hxS, hxg⟩
    obtain ⟨h, hh, hv⟩ := hxS
    obtain ⟨v, rfl⟩ := hv
    rw [← hxg]
    refine ⟨(MulAut.conj g).toMonoidHom h, Subgroup.mem_map_of_mem _ hh, ⟨g v, ?_⟩⟩
    simp [LinearEquiv.mul_apply]

theorem centralizerSpace_map_conj {B : Subgroup (U ≃ₗ[K] U)} (g : U ≃ₗ[K] U) :
    centralizerSpace (B.map (MulAut.conj g).toMonoidHom) =
      (centralizerSpace B).map (g : U →ₗ[K] U) := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, rfl⟩ := g.surjective v
    refine Submodule.mem_map.mpr ⟨u, ?_, rfl⟩
    refine (mem_centralizerSpace).mpr fun h hh => ?_
    have h' : (MulAut.conj g).toMonoidHom h ∈ B.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hh
    have hv' := hv ((MulAut.conj g).toMonoidHom h) h'
    have : g (h u) = g u := by simpa [LinearEquiv.mul_apply] using hv'
    exact g.injective this
  · rintro ⟨u, hu, rfl⟩
    intro h' hh'
    obtain ⟨h, hh, rfl⟩ := (Subgroup.mem_map (f := (MulAut.conj g).toMonoidHom)).mp hh'
    have hu' : h u = u := (mem_centralizerSpace).mp hu h hh
    simp [LinearEquiv.mul_apply, hu']

theorem irredOnSection_map_conj {B : Subgroup (U ≃ₗ[K] U)} {W₁ W₂ : Submodule K U}
    (g : U ≃ₗ[K] U) (h : IrredOnSection B W₁ W₂) :
    IrredOnSection (B.map (MulAut.conj g).toMonoidHom)
      (W₁.map (g : U →ₗ[K] U)) (W₂.map (g : U →ₗ[K] U)) := by
  intro X hX₁ hX₂ hXinv
  let X' := X.comap (g : U →ₗ[K] U)
  have hXmap : X = X'.map (g : U →ₗ[K] U) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨u, rfl⟩ := g.surjective x
      exact Submodule.mem_map.mpr ⟨u, Submodule.mem_comap.mpr hx, rfl⟩
    · rintro x ⟨u, hu, rfl⟩
      exact Submodule.mem_comap.mp hu
  have hX'₁ : W₁ ≤ X' := (Submodule.map_le_iff_le_comap).mp hX₁
  have hX'₂ : X' ≤ W₂ := by
    intro x hx
    obtain ⟨w, hw, hwg⟩ := Submodule.mem_map.mp (hX₂ (Submodule.mem_comap.mp hx))
    rwa [g.injective hwg] at hw
  have hX'inv : ∀ b ∈ B, ∀ x ∈ X', b x ∈ X' := by
    intro b hb x hx
    change g (b x) ∈ X
    have hconj : g (b x) = (MulAut.conj g).toMonoidHom b (g x) := by
      simp [LinearEquiv.mul_apply]
    rw [hconj]
    exact hXinv _ (Subgroup.mem_map_of_mem _ hb) _ (Submodule.mem_comap.mp hx)
  rcases h X' hX'₁ hX'₂ hX'inv with hbot | htop
  · exact Or.inl (by rw [hXmap, hbot])
  · exact Or.inr (by rw [hXmap, htop])

theorem splitSupport_map_conj {B : Subgroup (U ≃ₗ[K] U)} {l : ℕ} (g : U ≃ₗ[K] U)
    (hB : SplitSupport B l) : SplitSupport (B.map (MulAut.conj g).toMonoidHom) l := by
  rw [SplitSupport] at hB ⊢
  rw [commutatorSpace_map_conj, centralizerSpace_map_conj]
  exact ⟨Submodule.isCompl_map (f := g) hB.1, by rw [LinearEquiv.finrank_map_eq, hB.2.1],
    by simpa using irredOnSection_map_conj g hB.2.2⟩

theorem SplitSupport.finrank_centralizerSpace [Module.Finite K U] {H : Subgroup (U ≃ₗ[K] U)}
    {l : ℕ} (hH : SplitSupport H l) :
    Module.finrank K (centralizerSpace H) = Module.finrank K U - l := by
  have h := Submodule.finrank_add_eq_of_isCompl hH.1
  rw [hH.2.1] at h
  omega

theorem SplitSupport.exists_mem_centralizerSpace_ne_zero [Module.Finite K U]
    {H : Subgroup (U ≃ₗ[K] U)} {l : ℕ} (hH : SplitSupport H l) (hl : l < Module.finrank K U) :
    ∃ e ∈ centralizerSpace H, e ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h0 => ?_
  have h := hH.finrank_centralizerSpace
  rw [h0, finrank_bot] at h
  omega

end Field

variable {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem reflGen_closure_of_forall_isRefl {S : Set (U ≃ₗ[ZMod p] U)} (hS : ∀ g ∈ S, IsRefl p g) :
    ReflGen p (Subgroup.closure S) :=
  le_antisymm
    ((Subgroup.closure_le _).mpr fun g hg =>
      Subgroup.subset_closure ⟨Subgroup.subset_closure hg, hS g hg⟩)
    ((Subgroup.closure_le _).mpr fun _ hg => hg.1)

theorem ReflGen.closure_insert {H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hH : ReflGen p H) (ha : IsRefl p a) :
    ReflGen p (Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))) := by
  have hHF : H ≤ Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) :=
    fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr fun _ ht => ht.1)
  rintro t (rfl | ht)
  · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (Set.mem_insert _ _), ha⟩
  · refine Subgroup.closure_mono ?_ (hH.le ht)
    exact fun s hs => ⟨hHF hs.1, hs.2⟩

theorem ReflGen.sup {A B : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ReflGen p A) (hB : ReflGen p B) :
    ReflGen p (A ⊔ B) := by
  let RA : Set (U ≃ₗ[ZMod p] U) := {t | t ∈ A ∧ IsRefl p t}
  let RB : Set (U ≃ₗ[ZMod p] U) := {t | t ∈ B ∧ IsRefl p t}
  have hsup : A ⊔ B = Subgroup.closure (RA ∪ RB) := by
    rw [hA, hB, Subgroup.closure_union]
  have hS : Subgroup.closure {t | t ∈ A ⊔ B ∧ IsRefl p t} = Subgroup.closure (RA ∪ RB) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro t ht
      rw [hsup] at ht
      exact ht.1
    · apply Subgroup.closure_mono
      rintro t (ht | ht)
      · exact ⟨Subgroup.mem_sup_left ht.1, ht.2⟩
      · exact ⟨Subgroup.mem_sup_right ht.1, ht.2⟩
  exact hsup.trans hS.symm

variable [Fact p.Prime]

theorem reflGen_map_conj (g : U ≃ₗ[ZMod p] U) {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ReflGen p B) : ReflGen p (B.map (MulAut.conj g).toMonoidHom) := by
  unfold ReflGen
  apply le_antisymm
  · rw [hB, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨t, ⟨ht, hrefl⟩, rfl⟩
    have hmem : (MulAut.conj g).toMonoidHom t ∈
        (MulAut.conj g).toMonoidHom '' {t | t ∈ B ∧ IsRefl p t} :=
      Set.mem_image_of_mem _ ⟨ht, hrefl⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hmem, hrefl.conj g⟩
  · rw [Subgroup.closure_le]
    intro x hx
    exact hx.1

end CFSG.StandardType.ZS

end
