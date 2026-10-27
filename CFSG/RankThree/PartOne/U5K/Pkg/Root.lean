module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.U5K.Pkg.Fixed
public import CFSG.RankThree.PartOne.U5K.Pkg.Rel

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def rootLattice (p : ℕ) (E : Subgroup G) : Subgroup G :=
  ⨆ (t : MulAut E) (_ : t ∈ reflectionSet p E), autMovedInG E t

omit [Finite G] in
theorem autMovedInG_le_rootLattice {p : ℕ} {E : Subgroup G} {t : MulAut E}
    (ht : t ∈ reflectionSet p E) : autMovedInG E t ≤ rootLattice p E :=
  le_iSup₂ (f := fun (t : MulAut E) (_ : t ∈ reflectionSet p E) => autMovedInG E t) t ht

omit [Finite G] in
theorem rootLattice_le {p : ℕ} (E : Subgroup G) : rootLattice p E ≤ E :=
  iSup₂_le fun _ _ => Subgroup.map_subtype_le _

theorem rootLattice_invariant {p : ℕ} (hp : p.Prime) (E : Subgroup G) :
    torusInvariant E ⊤ (rootLattice p E) := by
  intro w hw b hb
  obtain ⟨-, hwN⟩ := hw
  have hle : conjBy w (rootLattice p E) ≤ rootLattice p E := by
    unfold conjBy
    rw [rootLattice, Subgroup.map_iSup]
    refine iSup_le fun t => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ht => ?_
    have h1 := Equivariance.autMovedInG_conj t hwN
    have hR : conjAut E w hwN * t * (conjAut E w hwN)⁻¹ ∈ reflectionSet p E :=
      conj_mem_reflectionSet hp ht hwN
    calc Subgroup.map (MulAut.conj w).toMonoidHom (autMovedInG E t)
        = autMovedInG E (conjAut E w hwN * t * (conjAut E w hwN)⁻¹) := h1.symm
      _ ≤ rootLattice p E := autMovedInG_le_rootLattice hR
  exact hle (Subgroup.mem_map_of_mem _ hb)

namespace Model

variable {p : ℕ} {E : Subgroup G} {c : E} (M : Model p E c)

include M in
theorem root_line_eq {t t' : MulAut E} (ht : t ∈ reflectionSet p E)
    (ht' : t' ∈ reflectionSet p E) (h : autMoved E t = autMoved E t') : t = t' := by
  have : Fact p.Prime := ⟨M.prime⟩
  have := M.elem
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E M.card
  obtain ⟨a, b, hab, hψ⟩ := M.swap_of_mem ht
  obtain ⟨c', d, hcd, hψ'⟩ := M.swap_of_mem ht'
  by_contra hne
  have hswap : Equiv.swap a b ≠ Equiv.swap c' d := by
    intro h1
    apply hne
    have : M.ψ ⟨t, Subgroup.subset_closure ht⟩ = M.ψ ⟨t', Subgroup.subset_closure ht'⟩ := by
      rw [hψ, hψ', h1]
    exact congrArg Subtype.val (M.ψ.injective this)
  have hne1 : ¬ (a = c' ∧ b = d) := fun ⟨h1, h2⟩ => hswap (by rw [h1, h2])
  have hne2 : ¬ (a = d ∧ b = c') := fun ⟨h1, h2⟩ => hswap (by rw [h1, h2, Equiv.swap_comm])
  have hX : t ∈ reflectionGroup p E := Subgroup.subset_closure ht
  have hX' : t' ∈ reflectionGroup p E := Subgroup.subset_closure ht'
  have hN1 : LinAlg.coordSub f t (M.u f a) = M.u f b - M.u f a := by
    rw [LinAlg.coordSub_apply, M.coordLin_u f t hX a, hψ, Equiv.swap_apply_left]
  have hN2 : LinAlg.coordSub f t' (M.u f c') = M.u f d - M.u f c' := by
    rw [LinAlg.coordSub_apply, M.coordLin_u f t' hX' c', hψ', Equiv.swap_apply_left]
  have hrank : Module.finrank (ZMod p) (LinearMap.range (LinAlg.coordSub f t)) = 1 :=
    ((LinAlg.isAutReflection_iff f t).1 ht.1).2
  have hR : LinearMap.range (LinAlg.coordSub f t') = LinearMap.range (LinAlg.coordSub f t) := by
    rw [← LinAlg.subSpace_autMoved, ← LinAlg.subSpace_autMoved, h]
  have hm1 : M.u f b - M.u f a ∈ LinearMap.range (LinAlg.coordSub f t) :=
    ⟨M.u f a, hN1⟩
  have hm2 : M.u f d - M.u f c' ∈ LinearMap.range (LinAlg.coordSub f t) := by
    rw [← hR]
    exact ⟨M.u f c', hN2⟩
  obtain ⟨α, β, hαβ, hrel⟩ := exists_rel_of_finrank_one _ hrank hm1 hm2
  obtain ⟨hα, hβ⟩ := M.u_indep f hab hcd hne1 hne2 α β hrel
  rcases hαβ with h1 | h1
  · exact h1 hα
  · exact h1 hβ

include M in
theorem rootLattice_irreducible : ∀ B' : Subgroup G, B' ≤ rootLattice p E →
    torusInvariant E ⊤ B' → B' = ⊥ ∨ B' = rootLattice p E := by
  intro B' hle hinv
  by_cases hbot : B' = ⊥
  · exact Or.inl hbot
  right
  have hp := M.prime
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B', b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hbE : b ∈ E := rootLattice_le E (hle hbB)
  have hX : ∀ x ∈ reflectionGroup p E, ∀ m : E, (m : G) ∈ B' → ((x m : E) : G) ∈ B' := by
    intro x hx m hm
    obtain ⟨w, hw, hwx⟩ := WeylIso.exists_lift (WeylIso.closure_le_weyl (E := E) hx)
    rw [← hwx, coe_conjAut_apply hw]
    exact hinv w ⟨Subgroup.mem_top w, hw⟩ m hm
  obtain ⟨t, ht, htb⟩ : ∃ t ∈ reflectionSet p E, t ⟨b, hbE⟩ ≠ ⟨b, hbE⟩ := by
    by_contra hcon
    push Not at hcon
    have := M.key ⟨b, hbE⟩ (fun x hx => fixed_of_closure hcon x hx)
    exact hb1 (congrArg Subtype.val this)
  have hmoved : autMovedInG E t ≤ B' := by
    have hd := RefFacts.ElemData.of_isElementaryAbelian hp (by have := M.five_le; omega) M.elem
    have h1 : autMoved E t ≤ B'.comap E.subtype :=
      RefFacts.autMoved_le_of_move hd ht.1 (B := B'.comap E.subtype) (b := ⟨b, hbE⟩) hbB
        (hX t (Subgroup.subset_closure ht) ⟨b, hbE⟩ hbB) htb
    exact Subgroup.map_le_iff_le_comap.2 h1
  refine le_antisymm hle (iSup₂_le fun s hs => ?_)
  obtain ⟨g, hg, hgts⟩ := WeylIso.exists_conj_eq_of_swaps (n := 4) M.ψ
    (fun t ht => M.swap_of_mem ht) ht hs
  obtain ⟨w, hw, hwg⟩ := WeylIso.exists_lift (WeylIso.closure_le_weyl (E := E) hg)
  rw [← hgts, ← hwg, Equivariance.autMovedInG_conj t hw]
  rintro _ ⟨y, hy, rfl⟩
  exact hinv w ⟨Subgroup.mem_top w, hw⟩ y (hmoved hy)

include M in
theorem rootLattice_faithful : ∀ g ∈ torusWeyl E,
    (∀ b : E, (b : G) ∈ rootLattice p E → g b = b) → g = 1 := by
  intro g hg hfix
  have hp := M.prime
  have hcomm : ∀ t ∈ reflectionSet p E, g * t = t * g := by
    intro t ht
    have ht' : g * t * g⁻¹ ∈ reflectionSet p E :=
      WeylIso.conj_mem_reflectionSet_of_weyl hp hg ht
    have hmov : autMoved E (g * t * g⁻¹) = autMoved E t := by
      rw [Equivariance.autMoved_conj]
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        have h1 : g m = m := hfix m (autMovedInG_le_rootLattice ht ⟨m, hm, rfl⟩)
        change g m ∈ autMoved E t
        rwa [h1]
      · intro hx
        refine ⟨x, hx, ?_⟩
        exact hfix x (autMovedInG_le_rootLattice ht ⟨x, hx, rfl⟩)
    have h2 := M.root_line_eq ht' ht hmov
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [h2]
  have hcommX : ∀ x ∈ reflectionGroup p E, g * x = x * g := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht => exact hcomm t ht
    | one => simp
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
    | inv x _ hx =>
      calc g * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by group
        _ = x⁻¹ * (g * x) * x⁻¹ := by rw [hx]
        _ = x⁻¹ * g := by group
  have hcommE : ∀ a b : E, a * b = b * a := fun a b => M.elem.is_comm.comm a b
  set d : E := g c * c⁻¹ with hd
  have hvd : ∀ i, g (M.v i) = M.v i * d := by
    intro i
    by_cases hik : i = M.k
    · subst hik
      rw [M.v_k, hd]
      exact ((hcommE c (g c * c⁻¹)).trans (inv_mul_cancel_right (g c) c)).symm
    · obtain ⟨t, ht, hψ⟩ := M.surj_swap (σ := Equiv.swap i M.k) ⟨i, M.k, hik, rfl⟩
      have hti : t (M.v M.k) = M.v i := by
        have := M.equivariant ⟨t, Subgroup.subset_closure ht⟩ M.k
        rw [hψ, Equiv.swap_apply_right] at this
        exact this
      have hmem : t (M.v M.k) * (M.v M.k)⁻¹ ∈ autMoved E t :=
        Subgroup.subset_closure ⟨M.v M.k, rfl⟩
      have hR : ((t (M.v M.k) * (M.v M.k)⁻¹ : E) : G) ∈ rootLattice p E :=
        autMovedInG_le_rootLattice ht ⟨_, hmem, rfl⟩
      have h1 := hfix _ hR
      rw [hti, map_mul, map_inv, M.v_k] at h1
      rw [hd]
      calc g (M.v i) = (g (M.v i) * (g c)⁻¹) * g c := (inv_mul_cancel_right _ _).symm
        _ = (M.v i * c⁻¹) * g c := by rw [h1]
        _ = M.v i * (c⁻¹ * g c) := mul_assoc _ _ _
        _ = M.v i * (g c * c⁻¹) := by rw [hcommE c⁻¹ (g c)]
  have hxd : ∀ x ∈ reflectionGroup p E, x d = d := by
    intro x hx
    have h1 : g (x (M.v M.k)) = x (g (M.v M.k)) := by
      have := congrArg (fun z : MulAut E => z (M.v M.k)) (hcommX x hx)
      simpa [MulAut.mul_apply] using this
    have h2 : x (M.v M.k) = M.v (M.ψ ⟨x, hx⟩ M.k) := M.equivariant ⟨x, hx⟩ M.k
    rw [h2, hvd (M.ψ ⟨x, hx⟩ M.k), hvd M.k, map_mul, h2] at h1
    exact (mul_left_cancel h1).symm
  have hd1 : d = 1 := M.key d hxd
  have hgv : ∀ i, g (M.v i) = M.v i := fun i => by rw [hvd, hd1, mul_one]
  have hall : ∀ m ∈ Subgroup.closure (Set.range M.v), g m = m := by
    intro m hm
    induction hm using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hgv i
    | one => exact map_one g
    | mul y z _ _ hy hz => rw [map_mul, hy, hz]
    | inv y _ hy => rw [map_inv, hy]
  refine MulEquiv.ext fun m => ?_
  rw [MulAut.one_apply]
  exact hall m (by rw [M.span_eq_top]; trivial)

end Model

end CFSG.RankThree.PartOne.U5K.Pkg
