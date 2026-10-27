module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2
public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open Matrix
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω]

section Generic

theorem exists_sl3_root_permuting_of_theta₂ {Fr : Ω →+* Ω}
    (hFrs : Function.Surjective Fr) (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (hinj : Function.Injective θ') (π : Equiv.Perm (Fin 3))
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 (π i) (π j)) (e * Fr c)) :
    (∀ g ∈ subsystemGroup Tag.E6 Ω support56, θ' g ∈ subsystemGroup Tag.E6 Ω support56) ∧
    ∃ Φ : SL(3, Ω) ≃* SL(3, Ω),
      (∀ g : subsystemGroup Tag.E6 Ω support56,
        ((Φ (a2Equiv₂ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = a2Mat₂ (θ' g)) ∧
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
          Matrix (Fin 3) (Fin 3) Ω) = 1 + single (π i) (π j) ((b i j : Ω) * Fr t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot56_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) ∈ subsystemGroup Tag.E6 Ω support56 :=
    fun i j hij c => by
      obtain ⟨e, -, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot56_mem (π.injective.ne hij) _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      θ' g ∈ subsystemGroup Tag.E6 Ω support56 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, c, rfl | rfl⟩ := hx
      · rcases (mem_support56 i).1 hi with rfl | rfl
        · rw [← pinnedX_single, ← h01]
          exact hmemθ 0 1 (by decide) c
        · rw [← pinnedX_single, ← h12]
          exact hmemθ 1 2 (by decide) c
      · rcases (mem_support56 i).1 hi with rfl | rfl
        · rw [← pinnedX_neg_single, ← h10]
          exact hmemθ 1 0 (by decide) c
        · rw [← pinnedX_neg_single, ← h21]
          exact hmemθ 2 1 (by decide) c
    | one =>
      rw [map_one]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact inv_mem hx
  choose s hs hρ using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₂_pinnedX_chainRoot56 (Ω := Ω) hij
  choose e he hθe using hθ
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain56 i j) ((s i j hij : Ω) * t),
          pinnedX_chainRoot56_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₂_apply, coe_a2Rep₂, hρ i j hij, ← mul_assoc, hs i j hij,
      one_mul]
    rfl
  let θQ : subsystemGroup Tag.E6 Ω support56 →* subsystemGroup Tag.E6 Ω support56 :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun a b => Subtype.ext (map_mul θ' (a : ModGL Tag.E6 Ω) b) }
  let Φ₀ : SL(3, Ω) →* SL(3, Ω) :=
    (a2Equiv₂ Ω).toMonoidHom.comp (θQ.comp (a2Equiv₂ Ω).symm.toMonoidHom)
  have hΦ₀ : ∀ g : subsystemGroup Tag.E6 Ω support56,
      ((Φ₀ (a2Equiv₂ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = a2Mat₂ (θ' g) := fun g => by
    change ((a2Equiv₂ Ω (θQ ((a2Equiv₂ Ω).symm (a2Equiv₂ Ω g))) : SL(3, Ω)) :
      Matrix (Fin 3) (Fin 3) Ω) = _
    rw [MulEquiv.symm_apply_apply, a2Equiv₂_apply, coe_a2Rep₂]
    rfl
  set b : Fin 3 → Fin 3 → Ωˣ := fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne ((s (π i) (π j) (π.injective.ne hij) : Ω) * e i j hij *
        Fr (s i j hij))
      ((s (π i) (π j) (π.injective.ne hij) : Ω) * e i j hij * Fr (s i j hij)) (by
        have h1 := hs (π i) (π j) (π.injective.ne hij)
        have h2 := he i j hij
        have h3 : Fr (s i j hij) * Fr (s i j hij) = 1 := by
          rw [← map_mul, hs i j hij, map_one]
        linear_combination (e i j hij * e i j hij * (Fr (s i j hij) * Fr (s i j hij))) * h1 +
          (Fr (s i j hij) * Fr (s i j hij)) * h2 + h3) else 1 with hbdef
  have hb : ∀ (i j : Fin 3) (hij : i ≠ j), (b i j : Ω) =
      (s (π i) (π j) (π.injective.ne hij) : Ω) * e i j hij * Fr (s i j hij) := by
    intro i j hij
    simp [hbdef, hij]
  have hΦt : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ₀ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = 1 + single (π i) (π j) ((b i j : Ω) * Fr t) := by
    intro i j hij t
    change ((a2Equiv₂ Ω (θQ ((a2Equiv₂ Ω).symm
      (Matrix.SpecialLinearGroup.transvection hij t))) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = _
    rw [hsymm i j hij t, a2Equiv₂_apply, coe_a2Rep₂]
    change a2Mat₂ (θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) ((s i j hij : Ω) * t))) = _
    rw [hθe i j hij, hρ (π i) (π j) (π.injective.ne hij), hb i j hij, map_mul]
    congr 2
    ring
  have hΦinj : Function.Injective Φ₀ := by
    intro A B hAB
    have h1 := (a2Equiv₂ Ω).injective hAB
    have h2 : θ' ((a2Equiv₂ Ω).symm A) = θ' ((a2Equiv₂ Ω).symm B) := congrArg Subtype.val h1
    exact (a2Equiv₂ Ω).symm.injective (Subtype.ext (hinj h2))
  have hΦsurj : Function.Surjective Φ₀ := by
    rw [← MonoidHom.range_eq_top]
    have hmem : ∀ (k l : Fin 3) (hkl : k ≠ l) (t : Ω),
        Matrix.SpecialLinearGroup.transvection hkl t ∈ Φ₀.range := by
      intro k l hkl t
      have hij : π.symm k ≠ π.symm l := π.symm.injective.ne hkl
      obtain ⟨t', ht'⟩ := hFrs ((b (π.symm k) (π.symm l))⁻¹ * t)
      refine ⟨Matrix.SpecialLinearGroup.transvection hij t', Subtype.ext ?_⟩
      rw [hΦt, ht', Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      rfl
    exact sl3_eq_top_of_adjacent _ (hmem 0 1 (by decide)) (hmem 1 2 (by decide))
      (hmem 1 0 (by decide)) (hmem 2 1 (by decide))
  exact ⟨hQ, MulEquiv.ofBijective Φ₀ ⟨hΦinj, hΦsurj⟩, hΦ₀, b, hΦt⟩




theorem exists_mulEquiv_fixSubgroup_gen₂ {w : WeylGroup Tag.E6}
    {S : Set (Fin Tag.E6.rank → ℤ)} (θ θw : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (hθw : ∀ y, θw (canonicalRep (coxeterSystem Tag.E6) Ω w * y *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) Ω w * θ y * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹)
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support56)
    (hmaps : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      θw g ∈ subsystemGroup Tag.E6 Ω support56)
    (Φ : SL(3, Ω) ≃* SL(3, Ω))
    (hΦ : ∀ g : subsystemGroup Tag.E6 Ω support56,
      ((Φ (a2Equiv₂ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₂ (θw g)) :
    ∃ e : ↥(rootSpan Tag.E6 Ω S ⊓ θ.eqLocus (MonoidHom.id _)) ≃*
        ↥(fixSubgroup Φ),
      ∀ y, ((e y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₂ (canonicalRep (coxeterSystem Tag.E6) Ω w * (y : ModGL Tag.E6 Ω) *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hmemQ₁ : ∀ y ∈ rootSpan Tag.E6 Ω S, n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 :=
    fun y hy => by
      rw [← hQ]
      exact ⟨y, hy, rfl⟩
  have hfix : ∀ y ∈ rootSpan Tag.E6 Ω S ⊓ θ.eqLocus (MonoidHom.id _),
      θw (n * y * n⁻¹) = n * y * n⁻¹ := fun y hy => by
    rw [hθw]
    have : θ y = y := hy.2
    rw [this]
  let f : ↥(rootSpan Tag.E6 Ω S ⊓ θ.eqLocus (MonoidHom.id _)) →* SL(3, Ω) :=
    { toFun := fun y => a2Equiv₂ Ω ⟨n * (y : ModGL Tag.E6 Ω) * n⁻¹, hmemQ₁ y y.2.1⟩
      map_one' := by
        rw [← map_one (a2Equiv₂ Ω)]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun y z => by
        rw [← map_mul]
        congr 1
        exact Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hfmat : ∀ y, ((f y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₂ (n * (y : ModGL Tag.E6 Ω) * n⁻¹) := fun y => by
      change ((a2Equiv₂ Ω ⟨n * (y : ModGL Tag.E6 Ω) * n⁻¹, hmemQ₁ y y.2.1⟩ : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = _
      rw [a2Equiv₂_apply, coe_a2Rep₂]
  have hf_mem : ∀ y, f y ∈ fixSubgroup Φ := fun y => by
    change Φ (f y) = f y
    apply Subtype.ext
    have h := hΦ ⟨n * (y : ModGL Tag.E6 Ω) * n⁻¹, hmemQ₁ y y.2.1⟩
    change ((Φ (f y) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₂ (θw (n * (y : ModGL Tag.E6 Ω) * n⁻¹)) at h
    rw [h, hfmat, hfix y y.2]
  let f' := f.codRestrict (fixSubgroup Φ) hf_mem
  have hinj : Function.Injective f' := by
    intro y z hyz
    have h1 : f y = f z := congrArg Subtype.val hyz
    have h2 := congrArg Subtype.val ((a2Equiv₂ Ω).injective h1)
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  have hsurj : Function.Surjective f' := by
    rintro ⟨X, hX⟩
    obtain ⟨g', rfl⟩ : ∃ g', a2Equiv₂ Ω g' = X := ⟨_, MulEquiv.apply_symm_apply _ _⟩
    have hg'Q : (g' : ModGL Tag.E6 Ω) ∈ (rootSpan Tag.E6 Ω S).map
        (MulAut.conj n).toMonoidHom := by
      rw [hQ]
      exact g'.2
    obtain ⟨y, hyS, hy⟩ := hg'Q
    change n * y * n⁻¹ = (g' : ModGL Tag.E6 Ω) at hy
    have hθg : θw g' = g' := by
      have h1 := hΦ g'
      have hX' : Φ (a2Equiv₂ Ω g') = a2Equiv₂ Ω g' := hX
      rw [hX', a2Equiv₂_apply, coe_a2Rep₂] at h1
      have h2 : a2Rep₂ Ω ⟨θw g', hmaps g' g'.2⟩ = a2Rep₂ Ω g' := by
        apply Subtype.ext
        rw [coe_a2Rep₂, coe_a2Rep₂]
        exact h1.symm
      exact congrArg Subtype.val (a2Rep₂_injective h2)
    have hyR : y ∈ θ.eqLocus (MonoidHom.id _) := by
      rw [← hy, hθw] at hθg
      exact mul_left_cancel (mul_right_cancel hθg)
    refine ⟨⟨y, hyS, hyR⟩, Subtype.ext ?_⟩
    change a2Equiv₂ Ω ⟨n * y * n⁻¹, _⟩ = a2Equiv₂ Ω g'
    congr 1
    exact Subtype.ext hy
  exact ⟨MulEquiv.ofBijective f' ⟨hinj, hsurj⟩, fun y => hfmat y⟩


end Generic

end CFSG.RankThree.PartOne.KE6
