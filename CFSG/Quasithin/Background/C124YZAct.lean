module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.B2FactorizationBridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section Embedding

variable {W : Type*} [CommGroup W] {m : ℕ} {Q : Type*} [Group Q]

def restrictU (U : Subgroup W) (g : MulAut W) (hg : ∀ u ∈ U, g u ∈ U) : ↥U →* ↥U where
  toFun u := ⟨g (u : W), hg u u.2⟩
  map_one' := Subtype.ext (map_one g)
  map_mul' u v := Subtype.ext (map_mul g (u : W) (v : W))

theorem exists_embedding_of_normalizer {Xs Ls : Subgroup (MulAut W)} (hLsXs : Ls ≤ Xs)
    (U : Subgroup W) (hU : ∀ g ∈ Xs, ∀ u ∈ U, g u ∈ U)
    {act : Perm (Fin m) →* MulAut Q}
    (hfaith : ∀ ρ : Perm (Fin m), (∀ q, act ρ q = q) → ρ = 1)
    (hnorm : ∀ φ : MulAut Q, (∀ σ ∈ alternatingGroup (Fin m), ∃ τ ∈ alternatingGroup (Fin m),
      ∀ y, act σ (φ y) = φ (act τ y)) → ∃ ρ : Perm (Fin m), ∀ y, φ y = act ρ y)
    (π : ↥(alternatingGroup (Fin m)) →* ↥Ls) (hπs : Function.Surjective π)
    (β : ↥U →* Q) (hβs : Function.Surjective β)
    (hβπ : ∀ (γ : ↥(alternatingGroup (Fin m))) (u : ↥U)
      (hu : (π γ : MulAut W) (u : W) ∈ U),
      β ⟨(π γ : MulAut W) (u : W), hu⟩ = act (γ : Perm (Fin m)) (β u))
    (hkerinv : ∀ g ∈ Xs, ∀ (u : ↥U) (hu : g (u : W) ∈ U), β u = 1 →
      β ⟨g (u : W), hu⟩ = 1)
    (hnormal : ∀ g ∈ Xs, ∀ l ∈ Ls, g * l * g⁻¹ ∈ Ls)
    (hcent : ∀ g ∈ Xs, (∀ l ∈ Ls, g * l = l * g) → g = 1) :
    ∃ ι : ↥Xs →* Perm (Fin m), Function.Injective ι ∧
      (∀ γ : ↥(alternatingGroup (Fin m)), ι (Subgroup.inclusion hLsXs (π γ)) = γ) ∧
      ∀ (g : ↥Xs) (u : ↥U) (hu : (g : MulAut W) (u : W) ∈ U),
        β ⟨(g : MulAut W) (u : W), hu⟩ = act (ι g) (β u) := by
  classical
  have hφ : ∀ g ∈ Xs, ∃ φ : Q →* Q, ∀ (u : ↥U) (hu : g (u : W) ∈ U),
      φ (β u) = β ⟨g (u : W), hu⟩ := by
    intro g hg
    refine ⟨(β.liftOfRightInverse (Function.surjInv hβs) (Function.rightInverse_surjInv hβs))
      ⟨β.comp (restrictU U g (hU g hg)), fun u hu => ?_⟩, fun u hu => ?_⟩
    · exact hkerinv g hg u (hU g hg u u.2) hu
    · exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
  choose! φ hφ using hφ
  have hinv : ∀ (g : ↥Xs) (q : Q),
      φ (((g⁻¹ : ↥Xs)) : MulAut W) (φ (g : MulAut W) q) = q := by
    intro g q
    obtain ⟨u, rfl⟩ := hβs q
    have hgu : (g : MulAut W) (u : W) ∈ U := hU g g.2 u u.2
    have hg'u : ((g⁻¹ : ↥Xs) : MulAut W) ((g : MulAut W) (u : W)) ∈ U :=
      hU _ (g⁻¹).2 _ hgu
    rw [hφ g g.2 u hgu, hφ (g⁻¹ : ↥Xs) (g⁻¹).2 ⟨_, hgu⟩ hg'u]
    exact congrArg β (Subtype.ext (by
      show ((g : MulAut W))⁻¹ ((g : MulAut W) (u : W)) = u
      exact (g : MulAut W).symm_apply_apply (u : W)))
  have hφaut : ∀ g : ↥Xs, ∃ ψ : MulAut Q, ∀ (u : ↥U) (hu : (g : MulAut W) (u : W) ∈ U),
      ψ (β u) = β ⟨(g : MulAut W) (u : W), hu⟩ := by
    intro g
    have hinv' : ∀ q, φ (g : MulAut W) (φ ((g⁻¹ : ↥Xs) : MulAut W) q) = q := by
      intro q
      have := hinv (g⁻¹) q
      rwa [inv_inv] at this
    let ψ : MulAut Q :=
      { toFun := φ (g : MulAut W)
        invFun := φ ((g⁻¹ : ↥Xs) : MulAut W)
        left_inv := fun q => hinv g q
        right_inv := hinv'
        map_mul' := map_mul _ }
    exact ⟨ψ, fun u hu => hφ g g.2 u hu⟩
  choose ψ hψ using hφaut
  have huniq : ∀ ρ₁ ρ₂ : Perm (Fin m), (∀ q, act ρ₁ q = act ρ₂ q) → ρ₁ = ρ₂ := by
    intro ρ₁ ρ₂ h
    have : ρ₂⁻¹ * ρ₁ = 1 := hfaith _ fun q => by
      rw [map_mul, MulAut.mul_apply, h q, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    exact (inv_mul_eq_one.1 this).symm
  have hρ : ∀ g : ↥Xs, ∃ ρ : Perm (Fin m), ∀ (u : ↥U)
      (hu : (g : MulAut W) (u : W) ∈ U), β ⟨(g : MulAut W) (u : W), hu⟩ = act ρ (β u) := by
    intro g
    have hn : ∀ σ ∈ alternatingGroup (Fin m), ∃ τ ∈ alternatingGroup (Fin m),
        ∀ y, act σ (ψ g y) = ψ g (act τ y) := by
      intro σ hσ
      have hl : (π ⟨σ, hσ⟩ : MulAut W) ∈ Ls := (π ⟨σ, hσ⟩).2
      have hl' : (g : MulAut W)⁻¹ * (π ⟨σ, hσ⟩ : MulAut W) * (g : MulAut W) ∈ Ls := by
        have := hnormal ((g⁻¹ : ↥Xs) : MulAut W) (g⁻¹).2 _ hl
        simpa using this
      obtain ⟨γτ, hγτ⟩ := hπs ⟨_, hl'⟩
      refine ⟨(γτ : Perm (Fin m)), γτ.2, fun y => ?_⟩
      obtain ⟨u, rfl⟩ := hβs y
      have hgu : (g : MulAut W) (u : W) ∈ U := hU g g.2 u u.2
      have hlu : (π ⟨σ, hσ⟩ : MulAut W) ((g : MulAut W) (u : W)) ∈ U :=
        hU _ (hLsXs hl) _ hgu
      have hτu : (π γτ : MulAut W) (u : W) ∈ U := hU _ (hLsXs (π γτ).2) _ u.2
      have e1 := hβπ ⟨σ, hσ⟩ ⟨_, hgu⟩ hlu
      have e2 := hβπ γτ u hτu
      have e3 : (g : MulAut W) ((π γτ : MulAut W) (u : W)) ∈ U := hU g g.2 _ hτu
      have e4 := hψ g ⟨_, hτu⟩ e3
      rw [hψ g u hgu, ← e1, ← e2, e4]
      refine congrArg β (Subtype.ext ?_)
      have hc : (π γτ : MulAut W) = (g : MulAut W)⁻¹ * (π ⟨σ, hσ⟩ : MulAut W) * (g : MulAut W) :=
        congrArg Subtype.val hγτ
      show (π ⟨σ, hσ⟩ : MulAut W) ((g : MulAut W) (u : W)) =
        (g : MulAut W) ((π γτ : MulAut W) (u : W))
      rw [hc]
      show _ = (g : MulAut W) ((g : MulAut W)⁻¹ ((π ⟨σ, hσ⟩ : MulAut W) ((g : MulAut W) (u : W))))
      exact ((g : MulAut W).apply_symm_apply _).symm
    obtain ⟨ρ, hρ⟩ := hnorm (ψ g) hn
    exact ⟨ρ, fun u hu => by rw [← hψ g u hu, hρ]⟩
  choose ι₀ hι₀ using hρ
  have hmul : ∀ g h : ↥Xs, ι₀ (g * h) = ι₀ g * ι₀ h := by
    intro g h
    refine huniq _ _ fun q => ?_
    obtain ⟨u, rfl⟩ := hβs q
    have hhu : (h : MulAut W) (u : W) ∈ U := hU h h.2 u u.2
    have hghu : (g : MulAut W) ((h : MulAut W) (u : W)) ∈ U := hU g g.2 _ hhu
    have e1 := hι₀ (g * h) u hghu
    have e2 := hι₀ g ⟨_, hhu⟩ hghu
    have e3 := hι₀ h u hhu
    rw [map_mul, MulAut.mul_apply, ← e3, ← e2, ← e1]
    rfl
  let ι : ↥Xs →* Perm (Fin m) := MonoidHom.mk' ι₀ hmul
  have hιπ : ∀ γ : ↥(alternatingGroup (Fin m)),
      ι (Subgroup.inclusion hLsXs (π γ)) = γ := by
    intro γ
    refine huniq _ _ fun q => ?_
    obtain ⟨u, rfl⟩ := hβs q
    have hu : (π γ : MulAut W) (u : W) ∈ U := hU _ (hLsXs (π γ).2) _ u.2
    have e1 := hι₀ (Subgroup.inclusion hLsXs (π γ)) u hu
    have e2 := hβπ γ u hu
    exact e1.symm.trans e2
  refine ⟨ι, ?_, hιπ, fun g u hu => hι₀ g u hu⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg1 : ι₀ g = 1 := hg
  have hfix : ∀ (v : ↥U) (hv : (g : MulAut W) (v : W) ∈ U),
      β ⟨(g : MulAut W) (v : W), hv⟩ = β v := by
    intro v hv
    rw [hι₀ g v hv, hg1, map_one]
    rfl
  have hfix' : ∀ v : ↥U, β ⟨((g⁻¹ : ↥Xs) : MulAut W) (v : W), hU _ (g⁻¹).2 _ v.2⟩ = β v := by
    intro v
    have := hfix ⟨((g⁻¹ : ↥Xs) : MulAut W) (v : W), hU _ (g⁻¹).2 _ v.2⟩ (by
      rw [show (g : MulAut W) (((g⁻¹ : ↥Xs) : MulAut W) (v : W)) = v from
        (g : MulAut W).apply_symm_apply _]
      exact v.2)
    refine this.symm.trans (congrArg β (Subtype.ext ?_))
    exact (g : MulAut W).apply_symm_apply (v : W)
  apply Subtype.ext
  refine hcent g.1 g.2 fun l hl => ?_
  obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
  have hl' : (g : MulAut W) * l * (g : MulAut W)⁻¹ ∈ Ls := hnormal _ g.2 _ hl
  obtain ⟨γ', hγ'⟩ := hπs ⟨_, hl'⟩
  have hγγ : (γ' : Perm (Fin m)) = γ := by
    refine huniq _ _ fun q => ?_
    obtain ⟨u, rfl⟩ := hβs q
    have hgu : ((g⁻¹ : ↥Xs) : MulAut W) (u : W) ∈ U := hU _ (g⁻¹).2 _ u.2
    have e1 := hβπ γ' u (hU _ (hLsXs (π γ').2) _ u.2)
    have e2 := hβπ γ ⟨_, hgu⟩ (hU _ (hLsXs (π γ).2) _ hgu)
    have hc' : (π γ' : MulAut W) = (g : MulAut W) * l * (g : MulAut W)⁻¹ :=
      congrArg Subtype.val hγ'
    have hc : (π γ : MulAut W) = l := congrArg Subtype.val hγ
    rw [← e1, ← hβπ γ u (hU _ (hLsXs (π γ).2) _ u.2)]
    set gi : MulAut W := ((g⁻¹ : ↥Xs) : MulAut W) with hgi
    have hgu : gi (u : W) ∈ U := hU _ (g⁻¹).2 _ u.2
    have hlgu : l (gi (u : W)) ∈ U := hU _ (hLsXs hl) _ hgu
    have hglgu : (g : MulAut W) (l (gi (u : W))) ∈ U := hU g g.2 _ hlgu
    have hmem' : (π γ' : MulAut W) (u : W) ∈ U := hU _ (hLsXs (π γ').2) _ u.2
    have hmem : (π γ : MulAut W) (u : W) ∈ U := hU _ (hLsXs (π γ).2) _ u.2
    calc β ⟨(π γ' : MulAut W) (u : W), hmem'⟩
        = β ⟨(g : MulAut W) (l (gi (u : W))), hglgu⟩ := congrArg β (Subtype.ext (by
            show (π γ' : MulAut W) (u : W) = (g : MulAut W) (l (gi (u : W)))
            exact congrArg (fun f : MulAut W => f (u : W)) hc'))
      _ = β ⟨l (gi (u : W)), hlgu⟩ := hfix ⟨l (gi (u : W)), hlgu⟩ hglgu
      _ = act (γ : Perm (Fin m)) (β ⟨gi (u : W), hgu⟩) := by
            rw [← hβπ γ ⟨gi (u : W), hgu⟩ (hU _ (hLsXs (π γ).2) _ hgu)]
            refine congrArg β (Subtype.ext ?_)
            show l (gi (u : W)) = (π γ : MulAut W) (gi (u : W))
            exact (congrArg (fun f : MulAut W => f (gi (u : W))) hc).symm
      _ = act (γ : Perm (Fin m)) (β u) := by rw [hfix' u]
      _ = β ⟨(π γ : MulAut W) (u : W), hmem⟩ := (hβπ γ u hmem).symm
  have hγeq : γ' = γ := Subtype.ext hγγ
  have h1 : (g : MulAut W) * l * (g : MulAut W)⁻¹ = l :=
    congrArg Subtype.val (hγ'.symm.trans ((congrArg π hγeq).trans hγ))
  calc (g : MulAut W) * l = ((g : MulAut W) * l * (g : MulAut W)⁻¹) * (g : MulAut W) := by group
    _ = l * (g : MulAut W) := by rw [h1]

end Embedding

section Transport

variable {G : Type} [Group G] [Finite G]

theorem apply_mem_fixV {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) {u : W} (hu : u ∈ fixV L) :
    g u ∈ fixV L :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hg hu

theorem eq_one_of_centralizes {X L V : Subgroup G} {hV : IsElemAbelian 2 V} {m : ℕ}
    (hm : 4 ≤ m) (hF : quasithinGenFitting (autI hV X) = autI hV L)
    {π : ↥(alternatingGroup (Fin m)) →* ↥(autI hV L)} (hπs : Function.Surjective π)
    (hπ : Function.Injective π) {g : MulAut (IntMod V hV)} (hg : g ∈ autI hV X)
    (hc : ∀ l ∈ autI hV L, g * l = l * g) : g = 1 := by
  have hmem : g ∈ autI hV X ⊓ Subgroup.centralizer
      (quasithinGenFitting (autI hV X) : Set (MulAut (IntMod V hV))) :=
    ⟨hg, by
      rw [hF]
      exact Subgroup.mem_centralizer_iff.2 fun h hh => (hc h hh).symm⟩
  have hgL : g ∈ autI hV L := by
    rw [← hF]
    exact centralizer_quasithinGenFitting_le _ hmem
  obtain ⟨γ, hγ⟩ := hπs ⟨g, hgL⟩
  have hγc : γ ∈ Subgroup.center ↥(alternatingGroup (Fin m)) := by
    rw [Subgroup.mem_center_iff]
    intro γ'
    apply hπ
    have := hc (π γ') (π γ').2
    rw [map_mul, map_mul, hγ]
    exact Subtype.ext this.symm
  rw [alternatingGroup.center_eq_bot (α := Fin m) (by simpa using hm), Subgroup.mem_bot] at hγc
  rw [hγc, map_one] at hγ
  exact congrArg Subtype.val hγ.symm

end Transport

end CFSG.Quasithin.C124.YZ
