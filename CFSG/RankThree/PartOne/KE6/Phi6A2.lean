module

public import CFSG.RankThree.PartOne.KE6.Phi6Transport
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE6.Phi6Torsion

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

theorem exists_sl3_root_reversing_of_theta {Fr : Ω →+* Ω}
    (hFrs : Function.Surjective Fr) (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (hinj : Function.Injective θ') (π : Equiv.Perm (Fin 3))
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π j) (π i)) (e * Fr c)) :
    (∀ g ∈ subsystemGroup Tag.E6 Ω support13, θ' g ∈ subsystemGroup Tag.E6 Ω support13) ∧
    ∃ Φ : SL(3, Ω) ≃* SL(3, Ω),
      (∀ g : subsystemGroup Tag.E6 Ω support13,
        ((Φ (a2Equiv₁ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = a2Mat₁ (θ' g)) ∧
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
          Matrix (Fin 3) (Fin 3) Ω) = 1 + single (π j) (π i) ((b i j : Ω) * Fr t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot13_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun i j hij c => by
      obtain ⟨e, -, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot13_mem (π.injective.ne hij).symm _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      θ' g ∈ subsystemGroup Tag.E6 Ω support13 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, c, rfl | rfl⟩ := hx
      · rcases (mem_support13 i).1 hi with rfl | rfl
        · rw [← pinnedX_single, ← h01]
          exact hmemθ 0 1 (by decide) c
        · rw [← pinnedX_single, ← h12]
          exact hmemθ 1 2 (by decide) c
      · rcases (mem_support13 i).1 hi with rfl | rfl
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
    a2Mat₁_pinnedX_chainRoot13 (Ω := Ω) hij
  choose e he hθe using hθ
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t),
          pinnedX_chainRoot13_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₁_apply, coe_a2Rep₁, hρ i j hij, ← mul_assoc, CFSG.RankThree.Classical2.sign_mul_self (hs i j hij),
      one_mul]
    rfl
  let θQ : subsystemGroup Tag.E6 Ω support13 →* subsystemGroup Tag.E6 Ω support13 :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun a b => Subtype.ext (map_mul θ' (a : ModGL Tag.E6 Ω) b) }
  let Φ₀ : SL(3, Ω) →* SL(3, Ω) :=
    (a2Equiv₁ Ω).toMonoidHom.comp (θQ.comp (a2Equiv₁ Ω).symm.toMonoidHom)
  have hΦ₀ : ∀ g : subsystemGroup Tag.E6 Ω support13,
      ((Φ₀ (a2Equiv₁ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = a2Mat₁ (θ' g) := fun g => by
    change ((a2Equiv₁ Ω (θQ ((a2Equiv₁ Ω).symm (a2Equiv₁ Ω g))) : SL(3, Ω)) :
      Matrix (Fin 3) (Fin 3) Ω) = _
    rw [MulEquiv.symm_apply_apply, a2Equiv₁_apply, coe_a2Rep₁]
    rfl
  set b : Fin 3 → Fin 3 → Ωˣ := fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne ((s (π j) (π i) (π.injective.ne hij).symm : Ω) * e i j hij *
        Fr (s i j hij))
      ((s (π j) (π i) (π.injective.ne hij).symm : Ω) * e i j hij * Fr (s i j hij)) (by
        have h1 := CFSG.RankThree.Classical2.sign_mul_self (R := Ω) (hs (π j) (π i) (π.injective.ne hij).symm)
        have h2 := he i j hij
        have h3 : Fr (s i j hij) * Fr (s i j hij) = 1 := by
          rw [← map_mul, CFSG.RankThree.Classical2.sign_mul_self (hs i j hij), map_one]
        linear_combination (e i j hij * e i j hij * (Fr (s i j hij) * Fr (s i j hij))) * h1 +
          (Fr (s i j hij) * Fr (s i j hij)) * h2 + h3) else 1 with hbdef
  have hb : ∀ (i j : Fin 3) (hij : i ≠ j), (b i j : Ω) =
      (s (π j) (π i) (π.injective.ne hij).symm : Ω) * e i j hij * Fr (s i j hij) := by
    intro i j hij
    simp [hbdef, hij]
  have hΦt : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ₀ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = 1 + single (π j) (π i) ((b i j : Ω) * Fr t) := by
    intro i j hij t
    change ((a2Equiv₁ Ω (θQ ((a2Equiv₁ Ω).symm
      (Matrix.SpecialLinearGroup.transvection hij t))) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = _
    rw [hsymm i j hij t, a2Equiv₁_apply, coe_a2Rep₁]
    change a2Mat₁ (θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t))) = _
    rw [hθe i j hij, hρ (π j) (π i) (π.injective.ne hij).symm, hb i j hij, map_mul]
    congr 2
    ring
  have hΦinj : Function.Injective Φ₀ := by
    intro A B hAB
    have h1 := (a2Equiv₁ Ω).injective hAB
    have h2 : θ' ((a2Equiv₁ Ω).symm A) = θ' ((a2Equiv₁ Ω).symm B) := congrArg Subtype.val h1
    exact (a2Equiv₁ Ω).symm.injective (Subtype.ext (hinj h2))
  have hΦsurj : Function.Surjective Φ₀ := by
    rw [← MonoidHom.range_eq_top]
    have hmem : ∀ (k l : Fin 3) (hkl : k ≠ l) (t : Ω),
        Matrix.SpecialLinearGroup.transvection hkl t ∈ Φ₀.range := by
      intro k l hkl t
      have hij : π.symm l ≠ π.symm k := π.symm.injective.ne hkl.symm
      obtain ⟨t', ht'⟩ := hFrs ((b (π.symm l) (π.symm k))⁻¹ * t)
      refine ⟨Matrix.SpecialLinearGroup.transvection hij t', Subtype.ext ?_⟩
      rw [hΦt, ht', Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      rfl
    exact sl3_eq_top_of_adjacent _ (hmem 0 1 (by decide)) (hmem 1 2 (by decide))
      (hmem 1 0 (by decide)) (hmem 2 1 (by decide))
  exact ⟨hQ, MulEquiv.ofBijective Φ₀ ⟨hΦinj, hΦsurj⟩, hΦ₀, b, hΦt⟩


section Transport

variable {Fr : Ω →+* Ω}

theorem phi6_A2_transport [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : ((q : ℕ) : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ phi6TorusTorsion Ω Fr p) (hx1 : x ≠ 1)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    ∃ w : WeylGroup Tag.E6,
      (rootSpan Tag.E6 Ω (torusRootKernel x)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        subsystemGroup Tag.E6 Ω support13 ∧
      ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
        phi6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
          pinnedX Tag.E6 Ω (chainRoot chain13 (π j) (π i)) (e * Fr c) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi6TorusTorsion_iff hFr hζ hr x).1 hx
  have hab0 : (a, b) ≠ 0 := fun h => hx1 (by
    rw [← hab, h, ofAdd_zero, map_one])
  have hker0 : torusRootKernel x = rootKernel (eisensteinColumn (q : ZMod p) a b) := by
    rw [← hab]
    exact torusRootKernel_phi3TorsionHom hζ _ a b
  obtain ⟨w₀, hw₀⟩ := hA2
  rw [hker0] at hw₀
  have hne : (rootKernel (eisensteinColumn (q : ZMod p) a b)).Nonempty := by
    have h1 : (parabolicRoots Tag.E6 support13).Nonempty :=
      ⟨_, chainRoot13_mem_parabolicRoots (show (0 : Fin 3) ≠ 1 by decide)⟩
    rw [← hw₀] at h1
    exact Set.image_nonempty.1 h1
  have hcard := ncard_rootKernel_of_image hw₀
  rw [ncard_parabolicRoots_support13] at hcard
  obtain ⟨-, -, -, -, h8⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, hline, -, hA2A2, hA2'⟩ := h8 p hp3 _ hr
  obtain ⟨k, hk⟩ := (hline a b hab0).1 hne
  have hk4 : 4 ≤ k.val := by
    by_contra h
    obtain ⟨w', hw', -⟩ := hA2A2 k (by omega)
    have := (hw' a b hab0 hk).2
    omega
  obtain ⟨w, hw, -, -, ⟨π, hπ⟩⟩ := hA2' k hk4
  have hwker := (hw a b hab0 hk).1
  refine ⟨w, ?_, π, fun i j hij => ?_⟩
  · rw [hker0, (canonical_weyl_root_transport Tag.E6 Ω).1 w _ fun α hα => hα.1, hwker,
      subsystemGroup_eq_rootSpan]
  · have hβ : IsRoot Tag.E6 (chainRoot chain13 i j) := (chainRoot13_mem_parabolicRoots hij).1
    obtain ⟨e, he, hθ⟩ := exists_conj_phi6Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain13 i j =
        chainRoot chain13 (π j) (π i) := hπ i j
    refine ⟨e, he, fun c => ?_⟩
    rw [hθ, hπij]

end Transport

section Transfer

variable {Fr : Ω →+* Ω}

theorem exists_mulEquiv_fixSubgroup6 {w : WeylGroup Tag.E6}
    {S : Set (Fin Tag.E6.rank → ℤ)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13)
    (hmaps : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      phi6ThetaConj Ω Fr w g ∈ subsystemGroup Tag.E6 Ω support13)
    (Φ : SL(3, Ω) ≃* SL(3, Ω))
    (hΦ : ∀ g : subsystemGroup Tag.E6 Ω support13,
      ((Φ (a2Equiv₁ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₁ (phi6ThetaConj Ω Fr w g)) :
    ∃ e : ↥(rootSpan Tag.E6 Ω S ⊓ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _)) ≃*
        ↥(fixSubgroup Φ),
      ∀ y, ((e y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₁ (canonicalRep (coxeterSystem Tag.E6) Ω w * (y : ModGL Tag.E6 Ω) *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hmemQ₁ : ∀ y ∈ rootSpan Tag.E6 Ω S, n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun y hy => by
      rw [← hQ]
      exact ⟨y, hy, rfl⟩
  have hfix : ∀ y ∈ rootSpan Tag.E6 Ω S ⊓ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _),
      phi6ThetaConj Ω Fr w (n * y * n⁻¹) = n * y * n⁻¹ := fun y hy => by
    rw [phi6ThetaConj_conj]
    have : phi6Theta Ω Fr y = y := hy.2
    rw [this]
  let f : ↥(rootSpan Tag.E6 Ω S ⊓ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _)) →* SL(3, Ω) :=
    { toFun := fun y => a2Equiv₁ Ω ⟨n * (y : ModGL Tag.E6 Ω) * n⁻¹, hmemQ₁ y y.2.1⟩
      map_one' := by
        rw [← map_one (a2Equiv₁ Ω)]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun y z => by
        rw [← map_mul]
        congr 1
        exact Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hfmat : ∀ y, ((f y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₁ (n * (y : ModGL Tag.E6 Ω) * n⁻¹) := fun y => by
      change ((a2Equiv₁ Ω ⟨n * (y : ModGL Tag.E6 Ω) * n⁻¹, hmemQ₁ y y.2.1⟩ : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = _
      rw [a2Equiv₁_apply, coe_a2Rep₁]
  have hf_mem : ∀ y, f y ∈ fixSubgroup Φ := fun y => by
    change Φ (f y) = f y
    apply Subtype.ext
    have h := hΦ ⟨n * (y : ModGL Tag.E6 Ω) * n⁻¹, hmemQ₁ y y.2.1⟩
    change ((Φ (f y) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₁ (phi6ThetaConj Ω Fr w (n * (y : ModGL Tag.E6 Ω) * n⁻¹)) at h
    rw [h, hfmat, hfix y y.2]
  let f' := f.codRestrict (fixSubgroup Φ) hf_mem
  have hinj : Function.Injective f' := by
    intro y z hyz
    have h1 : f y = f z := congrArg Subtype.val hyz
    have h2 := congrArg Subtype.val ((a2Equiv₁ Ω).injective h1)
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  have hsurj : Function.Surjective f' := by
    rintro ⟨X, hX⟩
    obtain ⟨g', rfl⟩ : ∃ g', a2Equiv₁ Ω g' = X := ⟨_, MulEquiv.apply_symm_apply _ _⟩
    have hg'Q : (g' : ModGL Tag.E6 Ω) ∈ (rootSpan Tag.E6 Ω S).map
        (MulAut.conj n).toMonoidHom := by
      rw [hQ]
      exact g'.2
    obtain ⟨y, hyS, hy⟩ := hg'Q
    change n * y * n⁻¹ = (g' : ModGL Tag.E6 Ω) at hy
    have hθg : phi6ThetaConj Ω Fr w g' = g' := by
      have h1 := hΦ g'
      have hX' : Φ (a2Equiv₁ Ω g') = a2Equiv₁ Ω g' := hX
      rw [hX', a2Equiv₁_apply, coe_a2Rep₁] at h1
      have h2 : a2Rep₁ Ω ⟨phi6ThetaConj Ω Fr w g', hmaps g' g'.2⟩ = a2Rep₁ Ω g' := by
        apply Subtype.ext
        rw [coe_a2Rep₁, coe_a2Rep₁]
        exact h1.symm
      exact congrArg Subtype.val (a2Rep₁_injective h2)
    have hyR : y ∈ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _) := by
      rw [← hy, phi6ThetaConj_conj] at hθg
      exact mul_left_cancel (mul_right_cancel hθg)
    refine ⟨⟨y, hyS, hyR⟩, Subtype.ext ?_⟩
    change a2Equiv₁ Ω ⟨n * y * n⁻¹, _⟩ = a2Equiv₁ Ω g'
    congr 1
    exact Subtype.ext hy
  exact ⟨MulEquiv.ofBijective f' ⟨hinj, hsurj⟩, fun y => hfmat y⟩

end Transfer


section Centralizer

variable {Fr : Ω →+* Ω}

theorem phi6_A2_key {w : WeylGroup Tag.E6} {S : Set (Fin Tag.E6.rank → ℤ)}
    (hQ₁ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13)
    {Φ : SL(3, Ω) ≃* SL(3, Ω)}
    (e : ↥(rootSpan Tag.E6 Ω S ⊓ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _)) ≃*
      ↥(fixSubgroup Φ))
    (he : ∀ y, ((e y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      a2Mat₁ (canonicalRep (coxeterSystem Tag.E6) Ω w * (y : ModGL Tag.E6 Ω) *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹))
    {q : ℕ} (H' : SL(3, Ω))
    (hH' : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet (Ω := Ω) q 3,
      Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H' * Y *
        (Matrix.SpecialLinearGroup.toGL H')⁻¹)
    (hscal : Subgroup.centralizer (unitarySet (Ω := Ω) q 3) =
      (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)
    {h z : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω) (hz : z ∈ rootSpan Tag.E6 Ω S)
    (hc : ∀ u ∈ rootSpan Tag.E6 Ω S ⊓ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _),
      h * z * u = u * (h * z)) :
    z ∈ torusGroup Tag.E6 Ω ∧ ∀ g ∈ rootSpan Tag.E6 Ω S, h * z * g = g * (h * z) := by
  classical
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hnN := canonicalRep_mem_normalizer (R := Ω) w
  have hh' : n * h * n⁻¹ ∈ torusGroup Tag.E6 Ω := (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
  have hz' : n * z * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
    rw [← hQ₁]
    exact ⟨z, hz, rfl⟩
  obtain ⟨χ, hχ, -⟩ := exists_simple_root_characters hh'
  set s₀ := χ (e6Index 0)
  set t₀ := χ (e6Index 2)
  have hkey : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ →
      diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] * a2Mat₁ (n * z * n⁻¹) *
        (X : Matrix (Fin 3) (Fin 3) Ω) =
      (X : Matrix (Fin 3) (Fin 3) Ω) *
        (diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] * a2Mat₁ (n * z * n⁻¹)) := by
    intro X hX
    set pp := e.symm ⟨X, hX⟩
    have hpp : a2Mat₁ (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) = (X : Matrix (Fin 3) (Fin 3) Ω) := by
      rw [← he pp, MulEquiv.apply_symm_apply]
    have hppQ : n * (pp : ModGL Tag.E6 Ω) * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
      rw [← hQ₁]
      exact ⟨_, pp.2.1, rfl⟩
    have hc0 : h * z * (pp : ModGL Tag.E6 Ω) = pp * (h * z) := hc pp pp.2
    have hc1 : (n * h * n⁻¹) * (n * z * n⁻¹) * (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) =
        (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) * ((n * h * n⁻¹) * (n * z * n⁻¹)) := by
      calc (n * h * n⁻¹) * (n * z * n⁻¹) * (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) =
          n * (h * z * (pp : ModGL Tag.E6 Ω)) * n⁻¹ := by group
        _ = n * ((pp : ModGL Tag.E6 Ω) * (h * z)) * n⁻¹ := by rw [hc0]
        _ = (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) * ((n * h * n⁻¹) * (n * z * n⁻¹)) := by group
    have h2 := diagonal_mul_a2Mat₁_comm hh' (hχ (e6Index 0)) (hχ (e6Index 2)) hz' hppQ hc1
    rwa [hpp] at h2
  have hD₁ : diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] *
      diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)
  have hD₂ : diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] *
      diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)
  let Dg : GL (Fin 3) Ω := ⟨_, _, hD₁, hD₂⟩
  obtain ⟨A, hAdef⟩ : ∃ A : GL (Fin 3) Ω,
      A = Dg * Matrix.SpecialLinearGroup.toGL (a2Rep₁ Ω ⟨_, hz'⟩) := ⟨_, rfl⟩
  have hA : (A : Matrix (Fin 3) (Fin 3) Ω) =
      diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] * a2Mat₁ (n * z * n⁻¹) := by
    rw [hAdef, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₁]
  have hB : (Matrix.SpecialLinearGroup.toGL H')⁻¹ * A * Matrix.SpecialLinearGroup.toGL H' ∈
      Subgroup.centralizer (unitarySet (Ω := Ω) q 3) := by
    rw [Subgroup.mem_centralizer_iff]
    intro Y hY
    let Ys : SL(3, Ω) := ⟨(Y : Matrix (Fin 3) (Fin 3) Ω), hY.2.1⟩
    have hYs : Matrix.SpecialLinearGroup.toGL Ys = Y := Units.ext rfl
    obtain ⟨X, hXY⟩ : ∃ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H' * Y * (Matrix.SpecialLinearGroup.toGL H')⁻¹ :=
      ⟨H' * Ys * H'⁻¹, by rw [map_mul, map_mul, map_inv, hYs]⟩
    have hXf : X ∈ fixSubgroup Φ := (hH' X).2 ⟨Y, hY, hXY⟩
    have hcomm : A * (Matrix.SpecialLinearGroup.toGL H' * Y *
        (Matrix.SpecialLinearGroup.toGL H')⁻¹) =
        (Matrix.SpecialLinearGroup.toGL H' * Y * (Matrix.SpecialLinearGroup.toGL H')⁻¹) * A := by
      rw [← hXY]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA]
      exact (hkey X hXf)
    calc Y * ((Matrix.SpecialLinearGroup.toGL H')⁻¹ * A * Matrix.SpecialLinearGroup.toGL H') =
        (Matrix.SpecialLinearGroup.toGL H')⁻¹ * ((Matrix.SpecialLinearGroup.toGL H' * Y *
          (Matrix.SpecialLinearGroup.toGL H')⁻¹) * A) * Matrix.SpecialLinearGroup.toGL H' := by
          group
      _ = (Matrix.SpecialLinearGroup.toGL H')⁻¹ * (A * (Matrix.SpecialLinearGroup.toGL H' * Y *
          (Matrix.SpecialLinearGroup.toGL H')⁻¹)) * Matrix.SpecialLinearGroup.toGL H' := by
          rw [hcomm]
      _ = (Matrix.SpecialLinearGroup.toGL H')⁻¹ * A * Matrix.SpecialLinearGroup.toGL H' * Y := by
          group
  rw [hscal] at hB
  obtain ⟨c, hc'⟩ := hB
  have hAsc : (A : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) (c : Ω) := by
    have h1 : A = Matrix.SpecialLinearGroup.toGL H' *
        ((Matrix.SpecialLinearGroup.toGL H')⁻¹ * A * Matrix.SpecialLinearGroup.toGL H') *
          (Matrix.SpecialLinearGroup.toGL H')⁻¹ := by group
    rw [h1, ← hc']
    have hcomm : Matrix.SpecialLinearGroup.toGL H' * Matrix.GeneralLinearGroup.scalar (Fin 3) c =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c * Matrix.SpecialLinearGroup.toGL H' :=
      Units.ext (by
        rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
        exact ((Matrix.scalar_commute (c : Ω) (fun r => Commute.all _ r) _).eq).symm)
    rw [hcomm, mul_inv_cancel_right, Matrix.GeneralLinearGroup.coe_scalar]
  rw [hA] at hAsc
  have hzH' : n * z * n⁻¹ ∈ torusGroup Tag.E6 Ω :=
    mem_torusGroup_of_diagonal_mul_eq_scalar hz' s₀ t₀ hAsc
  refine ⟨?_, fun g hg => ?_⟩
  · have h3 := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) (n * z * n⁻¹)).1 hzH'
    rwa [show n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z by group] at h3
  ·
    have hg' : n * g * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
      rw [← hQ₁]
      exact ⟨g, hg, rfl⟩
    set z' := n * z * n⁻¹ with hz'def
    set g' := n * g * n⁻¹ with hg'def
    set h' := n * h * n⁻¹ with hh'def
    have hz'g' : z' * g' * z'⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 :=
      mul_mem (mul_mem hz' hg') (inv_mem hz')
    obtain ⟨hmem, hform⟩ := a2Mat₁_conj_torus hh' (hχ (e6Index 0)) (hχ (e6Index 2)) hz'g'
    rw [a2Mat₁_mul (mul_mem hz' hg') (inv_mem hz'), a2Mat₁_mul hz' hg'] at hform
    set D := diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] with hDdef
    set D' := diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] with hD'def
    have hρρ : a2Mat₁ z' * a2Mat₁ z'⁻¹ = 1 := by
      rw [← a2Mat₁_mul hz' (inv_mem hz'), mul_inv_cancel, a2Mat₁_one]
    have hAM : (D * a2Mat₁ z') * (a2Mat₁ z'⁻¹ * D') = 1 := by
      calc (D * a2Mat₁ z') * (a2Mat₁ z'⁻¹ * D') = D * (a2Mat₁ z' * a2Mat₁ z'⁻¹) * D' := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hρρ, Matrix.mul_one, hD₁]
    have hres : a2Mat₁ (h' * (z' * g' * z'⁻¹) * h'⁻¹) = a2Mat₁ g' := by
      rw [hform]
      calc D * (a2Mat₁ z' * a2Mat₁ g' * a2Mat₁ z'⁻¹) * D' =
          (D * a2Mat₁ z') * a2Mat₁ g' * (a2Mat₁ z'⁻¹ * D') := by simp only [Matrix.mul_assoc]
        _ = scalar (Fin 3) (c : Ω) * a2Mat₁ g' * (a2Mat₁ z'⁻¹ * D') := by rw [hAsc]
        _ = a2Mat₁ g' * (scalar (Fin 3) (c : Ω) * (a2Mat₁ z'⁻¹ * D')) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (scalar (Fin 3) (c : Ω)),
              (Matrix.scalar_commute (c : Ω) (fun r => Commute.all _ r) _).eq,
              Matrix.mul_assoc]
        _ = a2Mat₁ g' := by
            rw [← hAsc, hAM, Matrix.mul_one]
    have hq : h' * (z' * g' * z'⁻¹) * h'⁻¹ = g' := by
      have h1 : a2Rep₁ Ω ⟨_, hmem⟩ = a2Rep₁ Ω ⟨g', hg'⟩ := by
        apply Subtype.ext
        rw [coe_a2Rep₁, coe_a2Rep₁]
        exact hres
      exact congrArg Subtype.val (a2Rep₁_injective h1)
    have : h * z * g * (h * z)⁻¹ = g := by
      have h2 : n⁻¹ * (h' * (z' * g' * z'⁻¹) * h'⁻¹) * n = h * z * g * (h * z)⁻¹ := by
        simp only [h', z', g']
        group
      have h3 : n⁻¹ * g' * n = g := by
        simp only [g']
        group
      rw [← h2, hq, h3]
    calc h * z * g = (h * z * g * (h * z)⁻¹) * (h * z) := by group
      _ = g * (h * z) := by rw [this]

end Centralizer


section A2Case

variable {Fr : Ω →+* Ω}

variable (Ω Fr) in
@[expose] def phi6Qθ
    (S : Set (Fin Tag.E6.rank → ℤ)) : Subgroup (ModGL Tag.E6 Ω) :=
  rootSpan Tag.E6 Ω S ⊓ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _)

theorem phi6_A2_case {K : Type} [Field K] [Finite K] [Algebra K Ω] [IsAlgClosure K Ω]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    Finite ↥(phi6Qθ Ω Fr (torusRootKernel x)) ∧
    CFSG.IsQuasisimple ↥(phi6Qθ Ω Fr (torusRootKernel x)) ∧
    Nat.card (Subgroup.center ↥(phi6Qθ Ω Fr (torusRootKernel x))) = Nat.gcd 3 (ℓ ^ f + 1) ∧
    (torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x)) ⊓
        Subgroup.centralizer (↑(phi6Qθ Ω Fr (torusRootKernel x)) : Set (ModGL Tag.E6 Ω)) ≤
      torusGroup Tag.E6 Ω ∧
    ∀ y ∈ torusGroup Tag.E6 Ω, (∀ u ∈ phi6Qθ Ω Fr (torusRootKernel x), y * u = u * y) →
      ∀ g ∈ rootSpan Tag.E6 Ω (torusRootKernel x), y * g = g * y := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq
  have hq3 : 3 ≤ ℓ ^ f := by
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    by_contra h
    have h2' : ℓ ^ f = 2 := by omega
    rw [h2'] at hpq
    have : (p : ℤ) ∣ 3 := by simpa using hpq
    have := Int.le_of_dvd (by norm_num) this
    omega
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi6TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁, π, hθ⟩ := phi6_A2_transport hp3 hFr hζ hr hxT hx1 hA2
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta hFrs
    (phi6ThetaConj Ω Fr w) (phi6ThetaConj_injective w) π hθ
  obtain ⟨e, he⟩ := exists_mulEquiv_fixSubgroup6 hQ₁ hmaps Φ hΦ₀
  obtain ⟨-, ⟨H', hH'⟩, hfin, hqsΦ, -⟩ := sln_root_permuting_frobenius_fixed_unitary hℓ hf hK
    (le_refl 3) π Φ b (fun i j hij t => by rw [hΦt, hFr])
  obtain ⟨hqsΦ', -, hcardΦ⟩ := hqsΦ (fun h => by
    have := (Prod.mk.inj h).2
    omega)
  have hscal := centralizer_unitary_eq_range_scalar (Ω := Ω) hK (n := 3) (le_refl 3)
  have hfinQ : Finite ↥(phi6Qθ Ω Fr (torusRootKernel x)) := Finite.of_equiv _ e.symm.toEquiv
  have hHN : torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) :=
    CFSG.RankThree.Classical2.torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hkey := fun {h z : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω)
      (hz : z ∈ rootSpan Tag.E6 Ω (torusRootKernel x))
      (hc : ∀ u ∈ phi6Qθ Ω Fr (torusRootKernel x), h * z * u = u * (h * z)) =>
    phi6_A2_key hQ₁ e he H' hH' hscal hh hz hc
  refine ⟨hfinQ, CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hqsΦ',
    (natCard_center_eq_of_mulEquiv e).trans hcardΦ, ?_, ?_⟩
  · rintro y ⟨hyHQ, hyc⟩
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN
    have hy' : y ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
        (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) := by
      rw [← hmul]
      exact hyHQ
    obtain ⟨h, hh, z, hz, rfl⟩ := hy'
    have hc : ∀ u ∈ phi6Qθ Ω Fr (torusRootKernel x), h * z * u = u * (h * z) := fun u hu =>
      ((Subgroup.mem_centralizer_iff.1 hyc) u hu).symm
    exact mul_mem hh (hkey hh hz hc).1
  · intro y hy hc g hg
    have := (hkey (h := y) (z := 1) hy (one_mem _) (fun u hu => by
      rw [mul_one]
      exact (hc u hu))).2 g hg
    simpa using this

end A2Case

end CFSG.RankThree.PartOne.KE6
