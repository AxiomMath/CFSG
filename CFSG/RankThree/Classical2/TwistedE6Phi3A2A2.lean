module

public import CFSG.RankThree.Classical2.NegativeExchangedSL3
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix
open scoped Matrix MatrixGroups Pointwise

theorem permLattice_e6Rho_chainRoot56 : ∀ i j : Fin 3,
    permLattice e6Rho (chainRoot chain56 i j) = chainRoot chain13 (Fin.rev j) (Fin.rev i) := by
  decide +kernel

theorem chainRoot56_apply_eq_zero : ∀ i j : Fin 3, ∀ l : Fin Tag.E6.rank, l ∉ support56 →
    chainRoot chain56 i j l = 0 := by
  intro i j l hl
  simp only [chainRoot]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : chain56 k ≠ l := fun h => hl (by
    rw [← h]
    fin_cases k
    · exact (mem_support56 _).2 (Or.inl rfl)
    · exact (mem_support56 _).2 (Or.inr rfl))
  simp [hk]

theorem isRoot_chainRoot56 {i j : Fin 3} (hij : i ≠ j) : IsRoot Tag.E6 (chainRoot chain56 i j) := by
  have h := (chainRoot13_mem_parabolicRoots (i := Fin.rev j) (j := Fin.rev i)
    (fun h => hij (Fin.rev_injective h).symm)).1
  have h2 : IsRoot Tag.E6 (permLattice e6Rho (chainRoot chain13 (Fin.rev j) (Fin.rev i))) :=
    h.permLattice TwistTag.E6.cartan_perm
  rwa [← permLattice_e6Rho_chainRoot56, permLattice_e6Rho_e6Rho] at h2

theorem chainRoot56_mem_parabolicRoots {i j : Fin 3} (hij : i ≠ j) :
    chainRoot chain56 i j ∈ parabolicRoots Tag.E6 support56 :=
  ⟨isRoot_chainRoot56 hij, fun l hl => chainRoot56_apply_eq_zero i j l hl⟩

variable {Ω : Type} [Field Ω]

theorem pinnedX_chainRoot56_mem {i j : Fin 3} (hij : i ≠ j) (t : Ω) :
    pinnedX Tag.E6 Ω (chainRoot chain56 i j) t ∈ subsystemGroup Tag.E6 Ω support56 :=
  rootSubgroup_le_subsystemGroup (chainRoot56_mem_parabolicRoots hij)
    (Subgroup.subset_closure ⟨t, rfl⟩)

theorem a2Flip_conj_one_add_single : ∀ a b : Fin 3, a ≠ b → ∃ ε : Ω, ε * ε = 1 ∧ ∀ c : Ω,
    a2Flip Ω * (1 + single a b c) * a2Flip Ω = 1 + single (Fin.rev a) (Fin.rev b) (ε * c) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first
    | exact absurd rfl hab
    | refine ⟨1, by ring, fun c => ?_⟩
      rw [a2Flip_conj]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      done
    | refine ⟨-1, by ring, fun c => ?_⟩
      rw [a2Flip_conj]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem a2Mat₂_pinnedX_chainRoot56 {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : Ω, ε * ε = 1 ∧ ∀ t : Ω,
      a2Mat₂ (pinnedX Tag.E6 Ω (chainRoot chain56 i j) t) = 1 + single i j (ε * t) := by
  obtain ⟨ε₁, h₁, hP⟩ := exists_twistHom_pinnedX TwistTag.E6 (RingHom.id Ω)
    (α := chainRoot chain56 i j) (isRoot_chainRoot56 hij)
  have hji : Fin.rev j ≠ Fin.rev i := fun h => hij (Fin.rev_injective h).symm
  obtain ⟨s, hs, hρ⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := Ω) hji
  have hij' : Fin.rev i ≠ Fin.rev j := fun h => hij (Fin.rev_injective h)
  obtain ⟨ε₂, h₂, hflip⟩ := a2Flip_conj_one_add_single (Ω := Ω) (Fin.rev i) (Fin.rev j) hij'
  refine ⟨-(ε₂ * s * ε₁), ?_, fun t => ?_⟩
  · have hs' := sign_mul_self (R := Ω) hs
    linear_combination (ε₂ * ε₂ * (s * s)) * h₁ + (ε₂ * ε₂) * hs' + h₂
  · have hP' : ∀ c : Ω, e6Diagram Ω (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (permLattice e6Rho (chainRoot chain56 i j)) (ε₁ * c) := fun c => hP c
    have hD : e6Diagram Ω (pinnedX Tag.E6 Ω (chainRoot chain56 i j) t) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (Fin.rev j) (Fin.rev i)) (ε₁ * t) := by
      rw [hP', permLattice_e6Rho_chainRoot56]
    rw [a2Mat₂, hD, hρ, adjugate_one_add_single hji, transpose_add, transpose_one,
      transpose_single, hflip, Fin.rev_rev, Fin.rev_rev]
    congr 2
    ring

theorem exists_conj_invTranspose_of_root_reversing [IsAlgClosed Ω] {n : ℕ} (hn : 3 ≤ n)
    (φ : Ω →+* Ω) (π : Equiv.Perm (Fin n)) (Ψ : SL(n, Ω) →* SL(n, Ω)) (b : Fin n → Fin n → Ωˣ)
    (hΨ : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Ψ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω) = 1 + single (π j) (π i) ((b i j : Ω) * φ t)) :
    ∃ a : SL(n, Ω), ∀ X : SL(n, Ω), Ψ X = a * invTransposeMapSL φ n X * a⁻¹ := by
  set Ψ' := Ψ.comp (invTransposeMapSL (RingHom.id Ω) n) with hΨ'
  have hT : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      invTransposeMapSL (RingHom.id Ω) n (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hij) (-t) := by
    intro i j hij t
    apply Subtype.ext
    rw [coe_invTransposeMapSL, RingHom.coe_id, Matrix.map_id]
    change ((1 + single i j t : Matrix (Fin n) (Fin n) Ω)⁻¹)ᵀ = 1 + single j i (-t)
    rw [(CFSG.LinearGroups.elementary_matrix_identities hij).2.2.1 t, transpose_add,
      transpose_one, transpose_single]
  have hΨ'T : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Ψ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω) = 1 + single (π i) (π j) (((-b j i : Ωˣ) : Ω) * φ t) := by
    intro i j hij t
    rw [hΨ', MonoidHom.comp_apply, hT, hΨ, map_neg, Units.val_neg, neg_mul, mul_neg]
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting hn φ π Ψ' (fun i j => -b j i) hΨ'T
  obtain ⟨a, ha⟩ := exists_specialLinear_conj_eq (by omega : 1 ≤ n) A
  refine ⟨a, fun X => Subtype.ext ?_⟩
  have hX : Ψ X = Ψ' (invTransposeMapSL (RingHom.id Ω) n X) := by
    rw [hΨ', MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    rw [coe_invTransposeMapSL_invTransposeMapSL, RingHom.id_comp, RingHom.coe_id, Matrix.map_id]
  rw [hX, hA, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ha,
    coe_invTransposeMapSL, coe_invTransposeMapSL, RingHom.coe_id, Matrix.map_id, transpose_map,
    map_nonsing_inv_of_isUnit φ (by rw [X.2]; exact isUnit_one)]

theorem support_A2A2_cases : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) →
      e6RootVec m i = 0) →
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2) → e6RootVec m i = 0) ∨
      (∀ i, ¬(i = e6Index 4 ∨ i = e6Index 5) → e6RootVec m i = 0) := by
  decide +kernel

theorem parabolicRoots_supportA2A2 :
    parabolicRoots Tag.E6 supportA2A2 =
      parabolicRoots Tag.E6 support13 ∪ parabolicRoots Tag.E6 support56 := by
  ext α
  constructor
  · rintro ⟨hα, hsupp⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    rcases support_A2A2_cases m (fun i hi => hsupp i ((mem_supportA2A2 i).not.2 hi)) with h | h
    · exact Or.inl ⟨hα, fun i hi => h i ((mem_support13 i).not.1 hi)⟩
    · exact Or.inr ⟨hα, fun i hi => h i ((mem_support56 i).not.1 hi)⟩
  · rintro (⟨hα, hsupp⟩ | ⟨hα, hsupp⟩)
    · refine ⟨hα, fun i hi => hsupp i fun hi' => hi ?_⟩
      rcases (mem_support13 i).1 hi' with rfl | rfl
      · exact (mem_supportA2A2 _).2 (Or.inl rfl)
      · exact (mem_supportA2A2 _).2 (Or.inr (Or.inl rfl))
    · refine ⟨hα, fun i hi => hsupp i fun hi' => hi ?_⟩
      rcases (mem_support56 i).1 hi' with rfl | rfl
      · exact (mem_supportA2A2 _).2 (Or.inr (Or.inr (Or.inl rfl)))
      · exact (mem_supportA2A2 _).2 (Or.inr (Or.inr (Or.inr rfl)))

theorem rootSpan_supportA2A2 :
    rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 supportA2A2) =
      subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 := by
  rw [parabolicRoots_supportA2A2, subsystemGroup_eq_rootSpan, subsystemGroup_eq_rootSpan,
    rootSpan, rootSpan, rootSpan, iSup_union]

section Transport

variable {Fr : Ω →+* Ω}

theorem phi3_A2A2_transport [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ phi3TorusTorsion Ω Fr p) (hx1 : x ≠ 1)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ∃ w : WeylGroup Tag.E6,
      (rootSpan Tag.E6 Ω (torusRootKernel x)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ∧
      ∃ π π' : Equiv.Perm (Fin 3),
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain56 (π j) (π i)) (e * Fr c)) ∧
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain13 (π' j) (π' i)) (e * Fr c)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi3TorusTorsion_iff hFr hζ hr x).1 hx
  have hab0 : (a, b) ≠ 0 := fun h => hx1 (by
    rw [← hab, h, ofAdd_zero, map_one])
  have hker0 : torusRootKernel x = rootKernel (eisensteinColumn (-(q : ZMod p)) a b) := by
    rw [← hab]
    exact torusRootKernel_phi3TorsionHom hζ _ a b
  obtain ⟨w₀, hw₀⟩ := hA2A2
  rw [hker0] at hw₀
  have hne : (rootKernel (eisensteinColumn (-(q : ZMod p)) a b)).Nonempty := by
    have h1 : (parabolicRoots Tag.E6 supportA2A2).Nonempty := by
      rw [parabolicRoots_supportA2A2]
      exact ⟨_, Or.inl (chainRoot13_mem_parabolicRoots (show (0 : Fin 3) ≠ 1 by decide))⟩
    rw [← hw₀] at h1
    exact Set.image_nonempty.1 h1
  have hcard := ncard_rootKernel_of_image hw₀
  rw [ncard_parabolicRoots_supportA2A2] at hcard
  obtain ⟨-, -, -, -, h8⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, hline, -, hA2A2', hA2'⟩ := h8 p hp3 _ hr
  obtain ⟨k, hk⟩ := (hline a b hab0).1 hne
  have hk4 : k.val < 4 := by
    by_contra h
    obtain ⟨w', hw', -⟩ := hA2' k (by omega)
    have := (hw' a b hab0 hk).2
    omega
  obtain ⟨w, hw, -, -, ⟨π, hπ⟩, ⟨π', hπ'⟩⟩ := hA2A2' k hk4
  have hwker := (hw a b hab0 hk).1
  refine ⟨w, ?_, π, π', fun i j hij => ?_, fun i j hij => ?_⟩
  · rw [hker0, (canonical_weyl_root_transport Tag.E6 Ω).1 w _ fun α hα => hα.1, hwker,
      rootSpan_supportA2A2]
  · have hβ : IsRoot Tag.E6 (chainRoot chain13 i j) := (chainRoot13_mem_parabolicRoots hij).1
    obtain ⟨e, he, hθ⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain13 i j =
        chainRoot chain56 (π i) (π j) := hπ i j
    refine ⟨e, he, fun c => ?_⟩
    rw [phi3ThetaConj_apply, hθ, hπij, ← chainRoot_swap]
  · have hβ : IsRoot Tag.E6 (chainRoot chain56 i j) := isRoot_chainRoot56 hij
    obtain ⟨e, he, hθ⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain56 i j =
        chainRoot chain13 (π' i) (π' j) := hπ' i j
    refine ⟨e, he, fun c => ?_⟩
    rw [phi3ThetaConj_apply, hθ, hπij, ← chainRoot_swap]

end Transport

theorem chainRoot56_simple :
    chainRoot chain56 0 1 = Pi.single (e6Index 4) 1 ∧
      chainRoot chain56 1 2 = Pi.single (e6Index 5) 1 ∧
      chainRoot chain56 1 0 = -Pi.single (e6Index 4) 1 ∧
      chainRoot chain56 2 1 = -Pi.single (e6Index 5) 1 := by
  decide +kernel

section Exchange

variable {Fr : Ω →+* Ω}

theorem exists_sl3_root_reversing_12 (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (π : Equiv.Perm (Fin 3))
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 (π j) (π i)) (e * Fr c)) :
    ∃ hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13, θ' g ∈ subsystemGroup Tag.E6 Ω support56,
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((a2Equiv₂ Ω ⟨θ' ((a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t)),
          hQ _ ((a2Equiv₁ Ω).symm _).2⟩ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single (π j) (π i) ((b i j : Ω) * Fr t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot13_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) ∈ subsystemGroup Tag.E6 Ω support56 :=
    fun i j hij c => by
      obtain ⟨e, -, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot56_mem (π.injective.ne hij).symm _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      θ' g ∈ subsystemGroup Tag.E6 Ω support56 := by
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
  choose s' hs' hρ' using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₂_pinnedX_chainRoot56 (Ω := Ω) hij
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
  refine ⟨hQ, fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne (s' (π j) (π i) (π.injective.ne hij).symm * e i j hij * Fr (s i j hij))
      (s' (π j) (π i) (π.injective.ne hij).symm * e i j hij * Fr (s i j hij)) (by
        have h1 := hs' (π j) (π i) (π.injective.ne hij).symm
        have h2 := he i j hij
        have h3 : Fr (s i j hij) * Fr (s i j hij) = 1 := by
          rw [← map_mul, sign_mul_self (hs i j hij), map_one]
        linear_combination (e i j hij * e i j hij * (Fr (s i j hij) * Fr (s i j hij))) * h1 +
          (Fr (s i j hij) * Fr (s i j hij)) * h2 + h3) else 1, fun i j hij t => ?_⟩
  simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mkOfMulEqOne]
  rw [a2Equiv₂_apply, coe_a2Rep₂]
  change a2Mat₂ (θ' ((a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t))) = _
  rw [hsymm i j hij t]
  change a2Mat₂ (θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t))) = _
  rw [hθe i j hij, hρ' (π j) (π i) (π.injective.ne hij).symm, map_mul]
  congr 2
  ring

theorem exists_sl3_root_reversing_21 (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (π : Equiv.Perm (Fin 3))
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π j) (π i)) (e * Fr c)) :
    ∃ hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56, θ' g ∈ subsystemGroup Tag.E6 Ω support13,
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((a2Equiv₁ Ω ⟨θ' ((a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t)),
          hQ _ ((a2Equiv₂ Ω).symm _).2⟩ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single (π j) (π i) ((b i j : Ω) * Fr t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot56_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun i j hij c => by
      obtain ⟨e, -, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot13_mem (π.injective.ne hij).symm _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      θ' g ∈ subsystemGroup Tag.E6 Ω support13 := by
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
  choose s' hs' hρ' using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₁_pinnedX_chainRoot13 (Ω := Ω) hij
  choose e he hθe using hθ
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain56 i j) (s i j hij * t),
          pinnedX_chainRoot56_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₂_apply, coe_a2Rep₂, hρ i j hij, ← mul_assoc, hs i j hij, one_mul]
    rfl
  refine ⟨hQ, fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne ((s' (π j) (π i) (π.injective.ne hij).symm : Ω) * e i j hij *
        Fr (s i j hij))
      ((s' (π j) (π i) (π.injective.ne hij).symm : Ω) * e i j hij * Fr (s i j hij)) (by
        have h1 := sign_mul_self (R := Ω) (hs' (π j) (π i) (π.injective.ne hij).symm)
        have h2 := he i j hij
        have h3 : Fr (s i j hij) * Fr (s i j hij) = 1 := by
          rw [← map_mul, hs i j hij, map_one]
        linear_combination (e i j hij * e i j hij * (Fr (s i j hij) * Fr (s i j hij))) * h1 +
          (Fr (s i j hij) * Fr (s i j hij)) * h2 + h3) else 1, fun i j hij t => ?_⟩
  simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mkOfMulEqOne]
  rw [a2Equiv₁_apply, coe_a2Rep₁]
  change a2Mat₁ (θ' ((a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t))) = _
  rw [hsymm i j hij t]
  change a2Mat₁ (θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) (s i j hij * t))) = _
  rw [hθe i j hij, hρ' (π j) (π i) (π.injective.ne hij).symm, map_mul]
  congr 2
  ring

end Exchange

section Layer

variable {Fr : Ω →+* Ω}

theorem subsystemGroup13_le_normalizer :
    subsystemGroup Tag.E6 Ω support13 ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [(commute_Q₁_Q₂ hg hh).eq, mul_inv_cancel_right]
    exact hh
  · intro hh
    have hc := (commute_Q₁_Q₂ (inv_mem hg) hh).eq
    have e : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = (g * h * g⁻¹) * g⁻¹ * g := by rw [hc]
        _ = g * h * g⁻¹ := by group
    rw [e]
    exact hh

theorem coe_sup_subsystemGroup :
    ((subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 :
      Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) *
        (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ subsystemGroup13_le_normalizer

@[expose] def twoA2MulSup :
    SL(3, Ω) × SL(3, Ω) →*
      ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) :=
  (twoA2Mul Ω).codRestrict _ fun AB => by
    rw [twoA2Mul_apply]
    exact mul_mem (Subgroup.mem_sup_left ((a2Equiv₁ Ω).symm AB.1).2)
      (Subgroup.mem_sup_right ((a2Equiv₂ Ω).symm AB.2).2)

theorem coe_twoA2MulSup (A B : SL(3, Ω)) :
    (twoA2MulSup (A, B) : ModGL Tag.E6 Ω) =
      ((a2Equiv₁ Ω).symm A : ModGL Tag.E6 Ω) * ((a2Equiv₂ Ω).symm B : ModGL Tag.E6 Ω) :=
  rfl

theorem twoA2MulSup_surjective : Function.Surjective (twoA2MulSup (Ω := Ω)) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) *
      (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
    rw [← coe_sup_subsystemGroup]
    exact hy
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy'
  refine ⟨(a2Equiv₁ Ω ⟨g₁, hg₁⟩, a2Equiv₂ Ω ⟨g₂, hg₂⟩), Subtype.ext ?_⟩
  rw [coe_twoA2MulSup, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem twoA2MulSup_eq_one_iff (A B : SL(3, Ω)) :
    twoA2MulSup (A, B) = 1 ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c ∧
        (B : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c := by
  rw [← (twoA2Mul_eq_one_iff A B)]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem exists_exchanged_layer [IsAlgClosed Ω] (hFrs : Function.Surjective Fr)
    (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω) (hinj : Function.Injective θ')
    (π π' : Equiv.Perm (Fin 3))
    (h12 : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 (π j) (π i)) (e * Fr c))
    (h21 : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π' j) (π' i)) (e * Fr c)) :
    ∃ θ : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) ≃*
        ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56),
      (∀ g, (θ g : ModGL Tag.E6 Ω) = θ' g) ∧
      ∃ a b : SL(3, Ω), ∀ A B : SL(3, Ω), θ (twoA2MulSup (A, B)) =
        twoA2MulSup (a * invTransposeMapSL Fr 3 B * a⁻¹, b * invTransposeMapSL Fr 3 A * b⁻¹) := by
  obtain ⟨hQ12, b₁₂, hb₁₂⟩ := exists_sl3_root_reversing_12 θ' π h12
  obtain ⟨hQ21, b₂₁, hb₂₁⟩ := exists_sl3_root_reversing_21 θ' π' h21
  let θ12 : subsystemGroup Tag.E6 Ω support13 →* subsystemGroup Tag.E6 Ω support56 :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ12 g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun x y => Subtype.ext (map_mul θ' (x : ModGL Tag.E6 Ω) y) }
  let θ21 : subsystemGroup Tag.E6 Ω support56 →* subsystemGroup Tag.E6 Ω support13 :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ21 g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun x y => Subtype.ext (map_mul θ' (x : ModGL Tag.E6 Ω) y) }
  let N₁₂ : SL(3, Ω) →* SL(3, Ω) :=
    (a2Equiv₂ Ω).toMonoidHom.comp (θ12.comp (a2Equiv₁ Ω).symm.toMonoidHom)
  let N₂₁ : SL(3, Ω) →* SL(3, Ω) :=
    (a2Equiv₁ Ω).toMonoidHom.comp (θ21.comp (a2Equiv₂ Ω).symm.toMonoidHom)
  obtain ⟨b, hb⟩ := exists_conj_invTranspose_of_root_reversing (le_refl 3) Fr π N₁₂ b₁₂ hb₁₂
  obtain ⟨a, ha⟩ := exists_conj_invTranspose_of_root_reversing (le_refl 3) Fr π' N₂₁ b₂₁ hb₂₁
  have hθ12 : ∀ A : SL(3, Ω), θ' ((a2Equiv₁ Ω).symm A) = (a2Equiv₂ Ω).symm (N₁₂ A) := fun A => by
    change θ' _ = ((a2Equiv₂ Ω).symm (a2Equiv₂ Ω (θ12 ((a2Equiv₁ Ω).symm A))) : ModGL Tag.E6 Ω)
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hθ21 : ∀ B : SL(3, Ω), θ' ((a2Equiv₂ Ω).symm B) = (a2Equiv₁ Ω).symm (N₂₁ B) := fun B => by
    change θ' _ = ((a2Equiv₁ Ω).symm (a2Equiv₁ Ω (θ21 ((a2Equiv₂ Ω).symm B))) : ModGL Tag.E6 Ω)
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56,
      θ' g ∈ subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 := by
    have hle : subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ≤
        (subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56).comap θ' :=
      sup_le (fun g hg => Subgroup.mem_sup_right (hQ12 g hg))
        (fun g hg => Subgroup.mem_sup_left (hQ21 g hg))
    exact fun g hg => hle hg
  let θ₀ : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) :=
    { toFun := fun g => ⟨θ' (g : ModGL Tag.E6 Ω), hQ g g.2⟩
      map_one' := Subtype.ext (map_one θ')
      map_mul' := fun x y => Subtype.ext (map_mul θ' (x : ModGL Tag.E6 Ω) y) }
  have hNsurj : ∀ (N : SL(3, Ω) →* SL(3, Ω)) (σ₀ : Equiv.Perm (Fin 3)) (c : Fin 3 → Fin 3 → Ωˣ),
      (∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((N (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
          Matrix (Fin 3) (Fin 3) Ω) = 1 + single (σ₀ j) (σ₀ i) ((c i j : Ω) * Fr t)) →
      Function.Surjective N := by
    intro N σ₀ c hN
    rw [← MonoidHom.range_eq_top]
    have hmem : ∀ (k l : Fin 3) (hkl : k ≠ l) (t : Ω),
        Matrix.SpecialLinearGroup.transvection hkl t ∈ N.range := by
      intro k l hkl t
      have hij : σ₀.symm l ≠ σ₀.symm k := σ₀.symm.injective.ne hkl.symm
      obtain ⟨t', ht'⟩ := hFrs ((c (σ₀.symm l) (σ₀.symm k))⁻¹ * t)
      refine ⟨Matrix.SpecialLinearGroup.transvection hij t', Subtype.ext ?_⟩
      rw [hN, ht', Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      rfl
    exact sl3_eq_top_of_adjacent _ (hmem 0 1 (by decide)) (hmem 1 2 (by decide))
      (hmem 1 0 (by decide)) (hmem 2 1 (by decide))
  have hN₁₂s := hNsurj N₁₂ π b₁₂ hb₁₂
  have hN₂₁s := hNsurj N₂₁ π' b₂₁ hb₂₁
  have hθ₀bij : Function.Bijective θ₀ := by
    refine ⟨fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy)), ?_⟩
    intro y
    obtain ⟨⟨A, B⟩, rfl⟩ := twoA2MulSup_surjective y
    obtain ⟨A', hA'⟩ := hN₂₁s A
    obtain ⟨B', hB'⟩ := hN₁₂s B
    refine ⟨twoA2MulSup (B', A'), Subtype.ext ?_⟩
    change θ' (((a2Equiv₁ Ω).symm B' : ModGL Tag.E6 Ω) * (a2Equiv₂ Ω).symm A') = _
    rw [map_mul, hθ12, hθ21, hA', hB', coe_twoA2MulSup]
    exact (commute_Q₁_Q₂ ((a2Equiv₁ Ω).symm A).2 ((a2Equiv₂ Ω).symm B).2).eq.symm
  refine ⟨MulEquiv.ofBijective θ₀ hθ₀bij, fun g => rfl, a, b, fun A B => Subtype.ext ?_⟩
  change θ' (((a2Equiv₁ Ω).symm A : ModGL Tag.E6 Ω) * (a2Equiv₂ Ω).symm B) = _
  rw [map_mul, hθ12, hθ21, coe_twoA2MulSup, ← ha, ← hb]
  exact (commute_Q₁_Q₂ ((a2Equiv₁ Ω).symm (N₂₁ B)).2 ((a2Equiv₂ Ω).symm (N₁₂ A)).2).eq.symm

end Layer

end CFSG.RankThree.Classical2
