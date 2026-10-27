module

public import CFSG.Quasithin.Background.G12Stmts
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace P4InspSp

theorem p4inspsp_commutator_range {G : Type*} [Group G] {n : ℕ} (hn : 5 ≤ n)
    (ι : Equiv.Perm (Fin n) →* G) :
    ⁅ι.range, ι.range⁆ = Subgroup.map ι (alternatingGroup (Fin n)) := by
  have h5 : 5 ≤ Nat.card (Fin n) := by simpa using hn
  let T : Subgroup (Equiv.Perm (Fin n)) := ⊤
  calc ⁅ι.range, ι.range⁆ = ⁅Subgroup.map ι T, Subgroup.map ι T⁆ := by
        rw [MonoidHom.range_eq_map]
    _ = Subgroup.map ι ⁅T, T⁆ := (Subgroup.map_commutator _ _ _).symm
    _ = Subgroup.map ι (alternatingGroup (Fin n)) := by
        rw [show ⁅T, T⁆ = commutator (Equiv.Perm (Fin n)) from rfl,
          alternatingGroup.commutator_perm_eq h5]

theorem p4inspsp_perfect_le_map_alt {G : Type*} [Group G] {n : ℕ} (hn : 5 ≤ n)
    (ι : Equiv.Perm (Fin n) →* G) {K : Subgroup G} (hK : K ≤ ι.range) (hperf : ⁅K, K⁆ = K) :
    K ≤ Subgroup.map ι (alternatingGroup (Fin n)) :=
  calc K = ⁅K, K⁆ := hperf.symm
    _ ≤ ⁅ι.range, ι.range⁆ := Subgroup.commutator_mono hK hK
    _ = Subgroup.map ι (alternatingGroup (Fin n)) := p4inspsp_commutator_range hn ι

theorem p4inspsp_isSimpleGroup_map_alt {G : Type*} [Group G] {n : ℕ} (hn : 5 ≤ n)
    (ι : Equiv.Perm (Fin n) →* G) (hι : Function.Injective ι) :
    IsSimpleGroup ↥(Subgroup.map ι (alternatingGroup (Fin n))) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  exact (Subgroup.equivMapOfInjective _ ι hι).symm.isSimpleGroup

theorem p4inspsp_eq_of_normalized {G : Type*} [Group G] {P K : Subgroup G} [IsSimpleGroup ↥P]
    (hKP : K ≤ P) (hnorm : ∀ p ∈ P, ∀ k ∈ K, p * k * p⁻¹ ∈ K) (hne : K ≠ ⊥) : K = P := by
  have hN : (K.subgroupOf P).Normal := ⟨fun k hk p => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hnorm p p.2 k hk⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf P) with h | h
  · exfalso
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    have : (⟨k, hKP hk⟩ : ↥P) ∈ K.subgroupOf P := hk
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exact le_antisymm hKP (Subgroup.subgroupOf_eq_top.1 h)

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem p4inspsp_ne_bot [Finite U] {K : Subgroup (GLV U)} (hirr : IsIrr K ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) U) : K ≠ ⊥ := by
  intro hK
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  have hnt : Nontrivial U := by
    rw [← Module.finrank_pos_iff (R := ZMod 2)]
    omega
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  have hinv : Invariant K (Submodule.span (ZMod 2) {u}) := by
    intro k hk w hw
    have h1 : k = 1 := by
      rw [hK] at hk
      exact Subgroup.mem_bot.1 hk
    subst h1
    simpa using hw
  rcases hirr.2.2 _ hinv bot_le le_top with h | h
  · apply hu
    have hmem : u ∈ Submodule.span (ZMod 2) {u} := Submodule.mem_span_singleton_self u
    rw [h] at hmem
    simpa using hmem
  · have h2 : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) U) ≤
        Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {u}) := Submodule.finrank_mono h.ge
    rw [finrank_top, finrank_span_singleton hu] at h2
    omega

theorem p4inspsp_nondeg {f : LinearMap.BilinForm (ZMod 2) U} (h : IsSymplectic f) :
    f.Nondegenerate := by
  obtain ⟨halt, hnd⟩ := h
  have hB : f.IsAlt := halt
  refine ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => ?_⟩
  have h := hB.self_eq_zero (x + y)
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right, halt, halt, hy x, zero_add, add_zero, zero_add] at h
  exact h

theorem p4inspsp_spSub_eq (f : LinearMap.BilinForm (ZMod 2) U) :
    spSub f = TauCeti.BilinForm.isometryGroup f := by
  ext g
  exact TauCeti.BilinForm.mem_isometryGroup_iff.symm

theorem p4inspsp_card_spSub_four [Finite U] {f : LinearMap.BilinForm (ZMod 2) U}
    (h : IsSymplectic f) (hd : Module.finrank (ZMod 2) U = 4) : Nat.card ↥(spSub f) = 720 := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  have h1 := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup (K := ZMod 2)
    2 f h.1 (p4inspsp_nondeg h) (by omega)
  rw [← p4inspsp_spSub_eq] at h1
  rw [h1, Nat.card_zmod]
  decide

noncomputable def p4inspsp_projEquiv {m : ℕ} {f : LinearMap.BilinForm (ZMod 2) U}
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) U)
    (hb : LinearMap.BilinForm.toMatrix b f = Matrix.J (Fin m) (ZMod 2)) :
    ↥(spSub f) ≃* StatedProj (StatedSp m (ZMod 2)) :=
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hscal : (StatedScalars (Fin m ⊕ Fin m) (ZMod 2)).subgroupOf (StatedSp m (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, Subsingleton.elim c 1, map_one]
    rfl
  (MulEquiv.subgroupCongr (p4inspsp_spSub_eq f)).trans
    ((CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b f
      hb).trans ((MulEquiv.subgroupCongr
        CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm).trans
          ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm))

theorem p4inspsp_isSimpleGroup_spSub [Finite U] {f : LinearMap.BilinForm (ZMod 2) U}
    (h : IsSymplectic f) (hd : 6 ≤ Module.finrank (ZMod 2) U) : IsSimpleGroup ↥(spSub f) := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis
      f h.1 (p4inspsp_nondeg h)
  have hm3 : 3 ≤ m := by omega
  have : IsSimpleGroup (StatedProj (StatedSp m (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) m (by omega)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, hm3⟩))
  exact (p4inspsp_projEquiv b hb).isSimpleGroup

theorem p4inspsp_finite_glv [Finite U] : Finite (GLV U) :=
  Finite.of_injective (fun g : GLV U => (g : U → U)) fun _ _ h => LinearEquiv.ext (congrFun h)

end P4InspSp

end G11

end CFSG.Quasithin
