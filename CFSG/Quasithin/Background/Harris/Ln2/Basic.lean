module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd
public import CFSG.Quasithin.Background.SmithCurtisBasic
import CFSG.Adapters.StatedSLTwoField
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SmithCurtis

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem nonempty_mulEquiv_sl_of_model {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl h


@[expose] noncomputable def repL {G : Type} [Group G] (L : Subgroup (GLV V)) (e : ↥L ≃* G) :
    Representation (ZMod 2) G V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom)

theorem repL_apply {G : Type} [Group G] (L : Subgroup (GLV V)) (e : ↥L ≃* G) (g : G) (v : V) :
    repL L e g v = ((e.symm g : ↥L) : GLV V) v := rfl

theorem repL_apply_self {G : Type} [Group G] (L : Subgroup (GLV V)) (e : ↥L ≃* G) (l : ↥L)
    (v : V) : repL L e (e l) v = (l : GLV V) v := by
  rw [repL_apply, MulEquiv.symm_apply_apply]

theorem isSimpleRep_repL {G : Type} [Group G] {L : Subgroup (GLV V)} (e : ↥L ≃* G)
    (hL : IsIrr L ⊤) : IsSimpleRep (repL L e) := by
  obtain ⟨-, hlt, hirr⟩ := hL
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨⟨v, 0, fun h => hv (h ▸ Submodule.zero_mem _)⟩⟩
  · have hinv : Invariant L U := fun l hl u hu => by
      have := hU (e ⟨l, hl⟩) u hu
      rwa [repL_apply_self] at this
    rcases hirr U hinv bot_le le_top with h | h
    · exact Or.inl h
    · exact Or.inr h

@[expose] def ActsAs {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (L : Subgroup (GLV V)) (θ : ↥L ≃* G) (τ : Representation (ZMod 2) G W)
    (β : V ≃ₗ[ZMod 2] W) : Prop :=
  ∀ (l : ↥L) (v : V), β ((l : GLV V) v) = τ (θ l) (β v)


section Scalar

variable {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

theorem eq_top_of_stable {τ : Representation (ZMod 2) G W} (hτ : IsSimpleRep τ)
    (N : Submodule (ZMod 2) W) (hN : ∀ g, ∀ w ∈ N, τ g w ∈ N) {y : W} (hy : y ≠ 0)
    (hyN : y ∈ N) : N = ⊤ :=
  (hτ.2 N hN).resolve_left fun h => hy (by simpa [h] using hyN)

theorem commutes_scalar (τ : Representation (ZMod 2) G W) (hτ : IsSimpleRep τ) (U : Subgroup G)
    (y : W) (hy : y ≠ 0) (hyU : ∀ u ∈ U, τ u y = y)
    (hfix : ∀ x, (∀ u ∈ U, τ u x = x) → x = 0 ∨ x = y)
    (f : Module.End (ZMod 2) W) (hf : ∀ g w, f (τ g w) = τ g (f w)) : f = 0 ∨ f = 1 := by
  have hfy : f y = 0 ∨ f y = y := hfix (f y) fun u hu => by rw [← hf, hyU u hu]
  rcases hfy with h | h
  · left
    have hN : LinearMap.ker f = ⊤ := eq_top_of_stable hτ _ (fun g w hw => by
      simp only [LinearMap.mem_ker] at hw ⊢; rw [hf, hw, map_zero]) hy (by simpa using h)
    exact LinearMap.ext fun w => by
      have : w ∈ LinearMap.ker f := by rw [hN]; trivial
      simpa using this
  · right
    have hN : LinearMap.ker (f - 1) = ⊤ := eq_top_of_stable hτ _ (fun g w hw => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hw ⊢
      rw [hf, sub_eq_zero.mp hw]; exact sub_self _) hy (by simp [h])
    exact LinearMap.ext fun w => by
      have : w ∈ LinearMap.ker (f - 1) := by rw [hN]; trivial
      simpa [sub_eq_zero] using this

end Scalar

section End

open CFSG.Quasithin.Background.Harris.OrdinaryProofs

theorem endIsField_of_natCard' [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) {n : ℕ}
    (hcard : Nat.card (endCommutant L) = 2 ^ n) : EndIsField L n := by
  classical
  have := endCommutant_nontrivial hL
  have := endCommutant_noZeroDivisors hL
  have : IsDomain (endCommutant L) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  let alg : Algebra (ZMod 2) (endCommutant L) := inferInstance
  let _ : Field (endCommutant L) := (Finite.isDomain_to_isField (endCommutant L)).toField
  let _ : Algebra (ZMod 2) (endCommutant L) := alg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField.algEquivGaloisField 2 n hcard⟩

variable {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

theorem endIsField_one_of_actsAs [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    {θ : ↥L ≃* G} {τ : Representation (ZMod 2) G W} {β : V ≃ₗ[ZMod 2] W} (h : ActsAs L θ τ β)
    (hτ : IsSimpleRep τ) (U : Subgroup G) (y : W) (hy : y ≠ 0) (hyU : ∀ u ∈ U, τ u y = y)
    (hfix : ∀ x, (∀ u ∈ U, τ u x = x) → x = 0 ∨ x = y) : EndIsField L 1 := by
  have hsc : ∀ f ∈ endCommutant L, (f : Module.End (ZMod 2) V) = 0 ∨ f = 1 := by
    intro f hf
    have hf' : ∀ g w, (β.toLinearMap ∘ₗ f ∘ₗ β.symm.toLinearMap) (τ g w) =
        τ g ((β.toLinearMap ∘ₗ f ∘ₗ β.symm.toLinearMap) w) := by
      intro g w
      obtain ⟨l, rfl⟩ := θ.surjective g
      obtain ⟨v, rfl⟩ := β.surjective w
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply]
      rw [← h, LinearEquiv.symm_apply_apply, ← h, endCommutant_apply_comm hf l.2 v]
    rcases commutes_scalar τ hτ U y hy hyU hfix _ hf' with h0 | h1
    · left
      ext v
      have := congrArg (fun g : Module.End (ZMod 2) W => β.symm (g (β v))) h0
      simpa using this
    · right
      ext v
      have := congrArg (fun g : Module.End (ZMod 2) W => β.symm (g (β v))) h1
      simpa using this
  have : Nontrivial (endCommutant L) := endCommutant_nontrivial hL
  have hcard : Nat.card (endCommutant L) = 2 ^ 1 := by
    have h2 : Nat.card (endCommutant L) = Nat.card (ZMod 2) := by
      symm
      apply Nat.card_congr
      refine Equiv.ofBijective (algebraMap (ZMod 2) (endCommutant L))
        ⟨(algebraMap (ZMod 2) (endCommutant L)).injective, fun f => ?_⟩
      rcases hsc f f.2 with h0 | h1
      · exact ⟨0, Subtype.ext (by simpa using h0.symm)⟩
      · exact ⟨1, Subtype.ext (by simpa using h1.symm)⟩
    rw [h2, Nat.card_zmod]
    norm_num
  exact endIsField_of_natCard' hL hcard

end End

end CFSG.Quasithin.G11.Harris.Ln2
