module

public import CFSG.LieType.BorelTits.Families
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Complement
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open CFSG.LieType.BorelTits

private theorem mem_perp_of_mem_complement_F08 {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] (Φ : QuadForm K V) {W A : Submodule K V} (hs : W ⊔ A = Φ.polar.perp W)
    {a : V} (ha : a ∈ A) : a ∈ Φ.polar.perp W :=
  ((le_sup_right (a := W) (b := A)).trans hs.le) ha

private theorem map_mem_perp_of_mem_J_F08 {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x)
    {W : Submodule K V} (J : Subgroup H) (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W) {g : H}
    (hg : g ∈ J) {x : V} (hx : x ∈ Φ.polar.perp W) : ρ g x ∈ Φ.polar.perp W :=
  IsIsometric.apply_mem_perp_of_forall (F := Φ.polar) (ρ := ρ)
    (fun h u v => Φ.polar_map_of_Q (hQ h) u v)
    (W := W) (fun w hw => hJW g⁻¹ (J.inv_mem hg) w hw) hx

private theorem sub_projection_mem_W_F08 {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x)
    {W A : Submodule K V} (hs : W ⊔ A = Φ.polar.perp W) (J : Subgroup H)
    (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W) (π : V →ₗ[K] ↥A)
    (hπ : ∀ x ∈ Φ.polar.perp W, (↑(π x) : V) - x ∈ W) (g : H) (hg : g ∈ J) (a : ↥A) :
    ρ g ↑a - ↑(π (ρ g ↑a)) ∈ W := by
  have hxP : ρ g ↑a ∈ Φ.polar.perp W :=
    map_mem_perp_of_mem_J_F08 Φ ρ hQ J hJW hg (mem_perp_of_mem_complement_F08 Φ hs a.2)
  simpa only [neg_sub] using neg_mem (hπ _ hxP)

private theorem Q_projection_sub_F08 {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x)
    {W A : Submodule K V} (hWs : Φ.IsTotallySingular W) (hs : W ⊔ A = Φ.polar.perp W)
    (J : Subgroup H) (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W) (π : V →ₗ[K] ↥A)
    (hπ : ∀ x ∈ Φ.polar.perp W, (↑(π x) : V) - x ∈ W) (g : H) (hg : g ∈ J) (a : ↥A) :
    Φ.Q ↑(π (ρ g ↑a)) = Φ.Q ↑a := by
  have hxP : ρ g ↑a ∈ Φ.polar.perp W :=
    map_mem_perp_of_mem_J_F08 Φ ρ hQ J hJW hg (mem_perp_of_mem_complement_F08 Φ hs a.2)
  have hyW : (↑(π (ρ g ↑a)) : V) - ρ g ↑a ∈ W := hπ _ hxP
  have hQy : Φ.Q ((↑(π (ρ g ↑a)) : V) - ρ g ↑a) = 0 := hWs _ hyW
  have hβ : Φ.polar.β (ρ g ↑a) ((↑(π (ρ g ↑a)) : V) - ρ g ↑a) = 0 := by
    rw [Φ.polar_symm (ρ g ↑a) ((↑(π (ρ g ↑a)) : V) - ρ g ↑a)]
    exact hxP _ hyW
  have hdecomp : (↑(π (ρ g ↑a)) : V) = ρ g ↑a + ((↑(π (ρ g ↑a)) : V) - ρ g ↑a) := by
    abel
  calc Φ.Q ↑(π (ρ g ↑a))
      = Φ.Q (ρ g ↑a + ((↑(π (ρ g ↑a)) : V) - ρ g ↑a)) := by conv_lhs => rw [hdecomp]
    _ = Φ.Q (ρ g ↑a) + Φ.Q ((↑(π (ρ g ↑a)) : V) - ρ g ↑a)
          + Φ.polar.β (ρ g ↑a) ((↑(π (ρ g ↑a)) : V) - ρ g ↑a) := Φ.Q_add _ _
    _ = Φ.Q (ρ g ↑a) := by rw [hQy, hβ, add_zero, add_zero]
    _ = Φ.Q ↑a := hQ g ↑a

theorem exists_tauEnd {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Group H]
    (Φ : QuadForm K V) (ρ : H →* Module.End K V) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x)
    {W A : Submodule K V} (hWs : Φ.IsTotallySingular W) (hd : Disjoint W A)
    (hs : W ⊔ A = Φ.polar.perp W) (J : Subgroup H) (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W) :
    ∃ T : ↥J →* Module.End K ↥A, (∀ (g : ↥J) (a : ↥A), ρ ↑g ↑a - ↑(T g a) ∈ W) ∧
      ∀ (g : ↥J) (a : ↥A), Φ.Q ↑(T g a) = Φ.Q ↑a := by
  obtain ⟨π, hπa, hπw, hπ⟩ := exists_projection_complement Φ hd hs
  let Tfun : ↥J → Module.End K ↥A := fun g => π.comp ((ρ ↑g).comp A.subtype)
  have hTone : Tfun 1 = 1 := by
    ext a
    simp only [Tfun, LinearMap.comp_apply, Module.End.one_apply, Subgroup.coe_one, map_one]
    exact congrArg Subtype.val (hπa a)
  have hTmul : ∀ g h : ↥J, Tfun (g * h) = Tfun g * Tfun h := by
    intro g h
    apply LinearMap.ext
    intro a
    simp only [Tfun, LinearMap.comp_apply, Module.End.mul_apply]
    show π (ρ ↑(g * h) ↑a) = π (ρ ↑g ↑(π (ρ ↑h ↑a)))
    have hh : ρ ↑h ↑a - ↑(π (ρ ↑h ↑a)) ∈ W :=
      sub_projection_mem_W_F08 Φ ρ hQ hs J hJW π hπ ↑h h.2 a
    have hcomp : ρ ↑(g * h) ↑a = ρ ↑g (ρ ↑h ↑a) := by
      rw [Subgroup.coe_mul, map_mul]
      rfl
    have heq : π (ρ ↑g (ρ ↑h ↑a)) =
        π (ρ ↑g ↑(π (ρ ↑h ↑a)) + ρ ↑g (ρ ↑h ↑a - ↑(π (ρ ↑h ↑a)))) := by
      rw [← map_add, add_sub_cancel]
    rw [hcomp, heq, map_add, hπw _ (hJW ↑g g.2 _ hh), add_zero]
  let T : ↥J →* Module.End K ↥A := { toFun := Tfun, map_one' := hTone, map_mul' := hTmul }
  refine ⟨T, fun g a => ?_, fun g a => ?_⟩
  · exact sub_projection_mem_W_F08 Φ ρ hQ hs J hJW π hπ ↑g g.2 a
  · exact Q_projection_sub_F08 Φ ρ hQ hWs hs J hJW π hπ ↑g g.2 a

theorem exists_tau {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Group H]
    (Φ : QuadForm K V) (ρ : H →* Module.End K V) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x)
    {W A : Submodule K V} (hWs : Φ.IsTotallySingular W) (hd : Disjoint W A)
    (hs : W ⊔ A = Φ.polar.perp W) (q : QuadraticForm K ↥A) (hq : ∀ a : ↥A, q a = Φ.Q ↑a)
    (J : Subgroup H) (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W) :
    ∃ τ : ↥J →* ↥(TauCeti.QuadraticMap.orthogonalGroup q), ∀ (g : ↥J) (a : ↥A),
      ρ ↑g ↑a - ↑((↑(τ g) : ↥A ≃ₗ[K] ↥A) a) ∈ W := by
  obtain ⟨T, hTsub, hTQ⟩ := exists_tauEnd Φ ρ hQ hWs hd hs J hJW
  let e : ↥J →* (↥A ≃ₗ[K] ↥A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K ↥A).toMonoidHom.comp
      (MonoidHom.toHomUnits T)
  have he : ∀ (g : ↥J) (a : ↥A), e g a = T g a := fun g a => rfl
  refine ⟨MonoidHom.codRestrict e (TauCeti.QuadraticMap.orthogonalGroup q) fun g => ?_,
    fun g a => ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro a
    calc q (e g a) = Φ.Q ↑(e g a) := hq _
      _ = Φ.Q ↑(T g a) := by rw [he g a]
      _ = Φ.Q ↑a := hTQ g a
      _ = q a := (hq a).symm
  · change ρ ↑g ↑a - ↑(e g a) ∈ W
    rw [he g a]
    exact hTsub g a

theorem sub_mem_of_tau_eq_one {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Group H]
    (Φ : QuadForm K V) (ρ : H →* Module.End K V) {W A : Submodule K V}
    (hs : W ⊔ A = Φ.polar.perp W) {q : QuadraticForm K ↥A} {J : Subgroup H}
    (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W)
    {τ : ↥J →* ↥(TauCeti.QuadraticMap.orthogonalGroup q)}
    (hτ : ∀ (g : ↥J) (a : ↥A), ρ ↑g ↑a - ↑((↑(τ g) : ↥A ≃ₗ[K] ↥A) a) ∈ W) {g : ↥J}
    (hg : τ g = 1) : ∀ x ∈ Φ.polar.perp W, ρ ↑g x - x ∈ W := by
  intro x hx
  obtain ⟨w, hw, a, ha, hax⟩ := Submodule.mem_sup.mp (hs.symm ▸ hx)
  have h1 : ρ ↑g w - w ∈ W := sub_mem (hJW ↑g g.2 w hw) hw
  have h2 : ρ ↑g a - a ∈ W := by
    have hcoe : (↑((↑(τ g) : ↥A ≃ₗ[K] ↥A) ⟨a, ha⟩) : V) = a := by
      rw [hg, Subgroup.coe_one]
      rfl
    have := hτ g ⟨a, ha⟩
    rwa [hcoe] at this
  have hsum : (ρ ↑g w - w) + (ρ ↑g a - a) = ρ ↑g x - x := by
    rw [← hax, map_add]
    abel
  exact hsum ▸ add_mem h1 h2

theorem isSolvable_orthogonalGroup_of_finrank_eq_two {K A : Type} [Field K] [AddCommGroup A]
    [Module K A] [FiniteDimensional K A] (q : QuadraticForm K A)
    (hq : (QuadraticMap.polarBilin q).Nondegenerate) (h2 : Module.finrank K A = 2) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup q) := by
  set δ := CFSG.RankThree.OrthogonalInvolutions.dicksonHom q hq
  have : Group.IsSolvable δ.ker := Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext
    (CFSG.RankThree.PartOne.KCOrthogonal.commute_of_dicksonHom_eq_one hq h2
      a.1.2 b.1.2 a.2 b.2))
  have : Group.IsSolvable (Multiplicative (ZMod 2)) :=
    Group.isSolvable_of_comm fun a b => mul_comm a b
  exact Group.isSolvable_of_ker_le_range δ.ker.subtype δ (by rw [Subgroup.range_subtype])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
