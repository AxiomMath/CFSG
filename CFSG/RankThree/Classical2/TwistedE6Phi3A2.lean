module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Lines
public import CFSG.RankThree.Classical2.TwistedE6Phi3Transport
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.E6.NativeTwoA2

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix
open scoped Matrix MatrixGroups

theorem chainRoot134_castSucc : ∀ i j : Fin 3,
    chainRoot chain134 (Fin.castSucc i) (Fin.castSucc j) = chainRoot chain13 i j := by
  decide +kernel

theorem chainRoot13_apply_eq_zero : ∀ i j : Fin 3, ∀ l : Fin Tag.E6.rank, l ∉ support13 →
    chainRoot chain13 i j l = 0 := by
  intro i j l hl
  simp only [chainRoot]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : chain13 k ≠ l := fun h => hl (by
    rw [← h]
    fin_cases k
    · exact (mem_support13 _).2 (Or.inl rfl)
    · exact (mem_support13 _).2 (Or.inr rfl))
  simp [hk]

theorem chainRoot13_mem_parabolicRoots {i j : Fin 3} (hij : i ≠ j) :
    chainRoot chain13 i j ∈ parabolicRoots Tag.E6 support13 := by
  have h := chainRoot134_mem_parabolicRoots (k := Fin.castSucc i) (l := Fin.castSucc j)
    (fun h => hij (Fin.castSucc_injective _ h))
  rw [chainRoot134_castSucc] at h
  exact ⟨h.1, fun l hl => chainRoot13_apply_eq_zero i j l hl⟩

variable {Ω : Type} [Field Ω]

theorem pinnedX_chainRoot13_mem {i j : Fin 3} (hij : i ≠ j) (t : Ω) :
    pinnedX Tag.E6 Ω (chainRoot chain13 i j) t ∈ subsystemGroup Tag.E6 Ω support13 :=
  rootSubgroup_le_subsystemGroup (chainRoot13_mem_parabolicRoots hij)
    (Subgroup.subset_closure ⟨t, rfl⟩)

theorem a2Mat₁_pinnedX_chainRoot13 {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : Ω,
      a2Mat₁ (pinnedX Tag.E6 Ω (chainRoot chain13 i j) t) = 1 + single i j ((ε : Ω) * t) := by
  obtain ⟨ε, hε, h⟩ := a3RootFamily_all (K := Ω) (Fin.castSucc i) (Fin.castSucc j)
    (fun h => hij (Fin.castSucc_injective _ h))
  refine ⟨ε, hε, fun t => ?_⟩
  rw [a2Mat₁, ← chainRoot134_castSucc, h t]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.castSucc_inj]

theorem chainRoot13_simple :
    chainRoot chain13 0 1 = Pi.single (e6Index 0) 1 ∧
      chainRoot chain13 1 2 = Pi.single (e6Index 2) 1 ∧
      chainRoot chain13 1 0 = -Pi.single (e6Index 0) 1 ∧
      chainRoot chain13 2 1 = -Pi.single (e6Index 2) 1 := by
  decide +kernel

theorem sign_mul_self {R : Type*} [Ring R] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    (ε : R) * ε = 1 := by
  rcases hε with rfl | rfl <;> simp

theorem exists_sl3_root_permuting_of_theta {Fr : Ω →+* Ω} (hFrs : Function.Surjective Fr)
    (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω) (hinj : Function.Injective θ')
    (π : Equiv.Perm (Fin 3))
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π i) (π j)) (e * Fr c)) :
    (∀ g ∈ subsystemGroup Tag.E6 Ω support13, θ' g ∈ subsystemGroup Tag.E6 Ω support13) ∧
    ∃ Φ : SL(3, Ω) ≃* SL(3, Ω),
      (∀ g : subsystemGroup Tag.E6 Ω support13,
        ((Φ (a2Equiv₁ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = a2Mat₁ (θ' g)) ∧
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
          Matrix (Fin 3) (Fin 3) Ω) = 1 + single (π i) (π j) ((b i j : Ω) * Fr t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot13_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun i j hij c => by
      obtain ⟨e, -, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot13_mem (π.injective.ne hij) _
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
    rw [a2Equiv₁_apply, coe_a2Rep₁, hρ i j hij, ← mul_assoc, sign_mul_self (hs i j hij),
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
    Units.mkOfMulEqOne ((s (π i) (π j) (π.injective.ne hij) : Ω) * e i j hij * Fr (s i j hij))
      ((s (π i) (π j) (π.injective.ne hij) : Ω) * e i j hij * Fr (s i j hij)) (by
        have h1 := sign_mul_self (R := Ω) (hs (π i) (π j) (π.injective.ne hij))
        have h2 := he i j hij
        have h3 : Fr (s i j hij) * Fr (s i j hij) = 1 := by
          rw [← map_mul, sign_mul_self (hs i j hij), map_one]
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
    change ((a2Equiv₁ Ω (θQ ((a2Equiv₁ Ω).symm
      (Matrix.SpecialLinearGroup.transvection hij t))) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = _
    rw [hsymm i j hij t, a2Equiv₁_apply, coe_a2Rep₁]
    change a2Mat₁ (θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t))) = _
    rw [hθe i j hij, hρ (π i) (π j) (π.injective.ne hij), hb i j hij, map_mul]
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
      have hij : π.symm k ≠ π.symm l := π.symm.injective.ne hkl
      obtain ⟨t', ht'⟩ := hFrs ((b (π.symm k) (π.symm l))⁻¹ * t)
      refine ⟨Matrix.SpecialLinearGroup.transvection hij t', Subtype.ext ?_⟩
      rw [hΦt, ht', Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      rfl
    exact sl3_eq_top_of_adjacent _ (hmem 0 1 (by decide)) (hmem 1 2 (by decide))
      (hmem 1 0 (by decide)) (hmem 2 1 (by decide))
  exact ⟨hQ, MulEquiv.ofBijective Φ₀ ⟨hΦinj, hΦsurj⟩, hΦ₀, b, hΦt⟩

section Transport

variable {Fr : Ω →+* Ω}

theorem phi3_A2_transport [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ phi3TorusTorsion Ω Fr p) (hx1 : x ≠ 1)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    ∃ w : WeylGroup Tag.E6,
      (rootSpan Tag.E6 Ω (torusRootKernel x)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        subsystemGroup Tag.E6 Ω support13 ∧
      ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
        phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
          pinnedX Tag.E6 Ω (chainRoot chain13 (π i) (π j)) (e * Fr c) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi3TorusTorsion_iff hFr hζ hr x).1 hx
  have hab0 : (a, b) ≠ 0 := fun h => hx1 (by
    rw [← hab, h, ofAdd_zero, map_one])
  have hker0 : torusRootKernel x = rootKernel (eisensteinColumn (-(q : ZMod p)) a b) := by
    rw [← hab]
    exact torusRootKernel_phi3TorsionHom hζ _ a b
  obtain ⟨w₀, hw₀⟩ := hA2
  rw [hker0] at hw₀
  have hne : (rootKernel (eisensteinColumn (-(q : ZMod p)) a b)).Nonempty := by
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
    obtain ⟨e, he, hθ⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain13 i j =
        chainRoot chain13 (π j) (π i) := hπ i j
    refine ⟨e, he, fun c => ?_⟩
    rw [phi3ThetaConj_apply, hθ, hπij, chainRoot_swap, neg_neg]

end Transport

section FixedField

variable {K : Type} [Field K] {σ : K →+* K}

theorem natCard_eqLocusField {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (RingHom.eqLocusField σ (RingHom.id K)) = ℓ ^ f := by
  set a : Fin TwistTag.E6.foldedTag.rank := ⟨2, by decide⟩
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6) hℓ hf hK hσ a
  have h1 : (TwistTag.E6.orbit a).card = 1 := by decide
  rw [h1, pow_one] at h
  have e : orbitField TwistTag.E6 K σ a = RingHom.eqLocusField σ (RingHom.id K) := by
    ext c
    rw [mem_orbitField, h1, pow_one, RingHom.mem_eqLocusField, RingHom.id_apply]
  rw [← e]
  exact h

end FixedField

section Transfer

variable {Fr : Ω →+* Ω}

theorem exists_mulEquiv_fixSubgroup {w : WeylGroup Tag.E6} {S : Set (Fin Tag.E6.rank → ℤ)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13)
    (hmaps : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      phi3ThetaConj Ω Fr w g ∈ subsystemGroup Tag.E6 Ω support13)
    (Φ : SL(3, Ω) ≃* SL(3, Ω))
    (hΦ : ∀ g : subsystemGroup Tag.E6 Ω support13,
      ((Φ (a2Equiv₁ Ω g) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₁ (phi3ThetaConj Ω Fr w g)) :
    ∃ e : ↥(rootSpan Tag.E6 Ω S ⊓ phi3FixedGroup Ω Fr) ≃* ↥(fixSubgroup Φ),
      ∀ y, ((e y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₁ (canonicalRep (coxeterSystem Tag.E6) Ω w * (y : ModGL Tag.E6 Ω) *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) := by
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hmemQ₁ : ∀ y ∈ rootSpan Tag.E6 Ω S, n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun y hy => by
      rw [← hQ]
      exact ⟨y, hy, rfl⟩
  have hfix : ∀ y ∈ rootSpan Tag.E6 Ω S ⊓ phi3FixedGroup Ω Fr,
      phi3ThetaConj Ω Fr w (n * y * n⁻¹) = n * y * n⁻¹ := fun y hy => by
    rw [phi3ThetaConj_conj, (mem_phi3FixedGroup_iff.1 hy.2).2]
  let f : ↥(rootSpan Tag.E6 Ω S ⊓ phi3FixedGroup Ω Fr) →* SL(3, Ω) :=
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
      a2Mat₁ (phi3ThetaConj Ω Fr w (n * (y : ModGL Tag.E6 Ω) * n⁻¹)) at h
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
    have hθg : phi3ThetaConj Ω Fr w g' = g' := by
      have h1 := hΦ g'
      have hX' : Φ (a2Equiv₁ Ω g') = a2Equiv₁ Ω g' := hX
      rw [hX', a2Equiv₁_apply, coe_a2Rep₁] at h1
      have h2 : a2Rep₁ Ω ⟨phi3ThetaConj Ω Fr w g', hmaps g' g'.2⟩ = a2Rep₁ Ω g' := by
        apply Subtype.ext
        rw [coe_a2Rep₁, coe_a2Rep₁]
        exact h1.symm
      exact congrArg Subtype.val (a2Rep₁_injective h2)
    have hyR : y ∈ phi3FixedGroup Ω Fr := by
      refine mem_phi3FixedGroup_iff.2 ⟨rootSpan_le_adjointGroup Ω S hyS, ?_⟩
      rw [← hy, phi3ThetaConj_conj] at hθg
      exact mul_left_cancel (mul_right_cancel hθg)
    refine ⟨⟨y, hyS, hyR⟩, Subtype.ext ?_⟩
    change a2Equiv₁ Ω ⟨n * y * n⁻¹, _⟩ = a2Equiv₁ Ω g'
    congr 1
    exact Subtype.ext hy
  exact ⟨MulEquiv.ofBijective f' ⟨hinj, hsurj⟩, fun y => hfmat y⟩

end Transfer

end CFSG.RankThree.Classical2
