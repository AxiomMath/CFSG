module

public import CFSG.RankThree.PartOne.KE.E6TwThreeShape
public import CFSG.RankThree.PartOne.KE.E6TwThreeRigid
public import CFSG.RankThree.Lattice.SteinbergBIE6TwoA2Graph

public noncomputable section

namespace CFSG.RankThree.PartOne.KETw3

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.E6
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (diagE6 e6_graph_transporter map_conj_rootSpan)
open scoped Matrix MatrixGroups Pointwise

theorem support13_cases_aux : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2) → e6RootVec m i = 0) →
    ∃ a b : Fin 3, a ≠ b ∧ e6RootVec m = chainRoot chain13 a b := by
  decide +kernel

theorem exists_chainRoot13_of_mem {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 support13) :
    ∃ a b : Fin 3, a ≠ b ∧ α = chainRoot chain13 a b := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
  exact support13_cases_aux m (fun i hi => hα.2 i ((mem_support13 i).not.2 hi))

theorem lattice_T_add (w₁ w : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ℤ) :
    w₁ • (w • permLattice e6Rho (w₁⁻¹ • (x + y))) =
      w₁ • (w • permLattice e6Rho (w₁⁻¹ • x)) + w₁ • (w • permLattice e6Rho (w₁⁻¹ • y)) := by
  simp only [← weylMatrix_mulVec, permLattice_eq_mulVec, Matrix.mulVec_add]

theorem twoA2_graph_contra {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 < p) (hpΩ : (p : Ω) ≠ 0) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    {Fr : Ω →+* Ω} (hFr : Function.Bijective Fr) (k₂ : Subfield Ω) (htk : ∃ t ∈ k₂, Fr t ≠ t)
    (h₁ h₂ : SL(3, Ω)) (w₁ : WeylGroup Tag.E6)
    {y : ModGL Tag.E6 Ω} (hyH : y ∈ torusGroup Tag.E6 Ω) (hyp : y ^ p = 1) (hy1 : y ≠ 1)
    (hw₁ : (fun x => w₁ • x) '' torusRootKernel y = parabolicRoots Tag.E6 supportA2A2)
    {G₃ : ModGL Tag.E6 Ω} (hG₃ : G₃ ∈ adjointGroup Tag.E6 Ω)
    (hfix : (G₃ * diagE6 Ω) * y * (G₃ * diagE6 Ω)⁻¹ = y)
    (hP : ∀ A : SL(3, k₂),
      (G₃ * diagE6 Ω) * ((canonicalRep (coxeterSystem Tag.E6) Ω w₁)⁻¹ *
        twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
          h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹) *
          canonicalRep (coxeterSystem Tag.E6) Ω w₁) * (G₃ * diagE6 Ω)⁻¹ =
        (canonicalRep (coxeterSystem Tag.E6) Ω w₁)⁻¹ *
          twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
            h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹) *
            canonicalRep (coxeterSystem Tag.E6) Ω w₁) : False := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set Q : ModGL Tag.E6 Ω := diagE6 Ω with hQ
  set n₁ : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w₁ with hn₁
  obtain ⟨z, hz⟩ := exists_eq_rootDiagUnit_zetaPow hζ hyH hyp
  obtain ⟨b, hbdef⟩ : ∃ b : Fin Tag.E6.rank → Ωˣ, b = fun i => ζ ^ (z i).val := ⟨_, rfl⟩
  rw [← hbdef] at hz
  have hker : torusRootKernel y = rootKernel z := by
    rw [hz, torusRootKernel_rootDiagUnit, hbdef, rootCharKernel_zetaPow hζ z]
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hy1
    rw [hz]
    have : b = 1 := by
      rw [hbdef]
      funext i
      simp
    rw [this, rootDiagUnit_one]
  have hcol : ∀ l l' : Fin Tag.E6.rank → ℤ,
      rootChar b l = rootChar b l' ↔ charVal z l = charVal z l' := fun l l' => by
    rw [hbdef, ← mul_inv_eq_one, ← rootChar_sub, rootChar_zetaPow_eq_one_iff hζ, charVal_sub,
      sub_eq_zero]
  have hv : (fun x => w₁ • x) '' rootKernel z = parabolicRoots Tag.E6 CFSG.RankThree.Lattice.supp1356 := by
    rw [← hker]
    exact hw₁
  have hfix' : (G₃ * Q) * rootDiagUnit Tag.E6 b * (G₃ * Q)⁻¹ = rootDiagUnit Tag.E6 b := by
    rw [← hz]
    exact hfix
  obtain ⟨w, hwd, hwz⟩ := e6_graph_transporter hcol hG₃ hfix'
  obtain ⟨hex1, hex2⟩ :=
    CFSG.RankThree.Lattice.E6_large_prime_two_A2_graph_stabilizers_exchange_components hp5 z hz0 w₁ hv
      w (graph_dual_fixed_iff.2 hwz)
  set nw : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w with hnw
  have hnwA : nw ∈ adjointGroup Tag.E6 Ω :=
    ((exceptional_root_diagonal_conjugacy_Weyl_transporter Tag.E6 Ω b b).2.2.2) w
  set bσ : Fin Tag.E6.rank → Ωˣ := fun i => b (TwistTag.E6.perm.symm i) with hbσ
  have hQb : Q * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 bσ * Q :=
    E6_diagramMap_mul_rootDiagUnit b
  have h1 : G₃ * rootDiagUnit Tag.E6 bσ * G₃⁻¹ = rootDiagUnit Tag.E6 b := by
    have e : rootDiagUnit Tag.E6 bσ = Q * rootDiagUnit Tag.E6 b * Q⁻¹ := by
      rw [hQb, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    simpa [mul_assoc] using hfix'
  have hu : (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹) := by
    have e : nw⁻¹ * rootDiagUnit Tag.E6 b * nw = rootDiagUnit Tag.E6 bσ := by
      rw [hwd]
      group
    have : (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹ = rootDiagUnit Tag.E6 b := by
      calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹
          = G₃ * (nw⁻¹ * rootDiagUnit Tag.E6 b * nw) * G₃⁻¹ := by group
        _ = rootDiagUnit Tag.E6 b := by rw [e, h1]
    calc (G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b
        = ((G₃ * nw⁻¹) * rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹)⁻¹) * (G₃ * nw⁻¹) := by group
      _ = rootDiagUnit Tag.E6 b * (G₃ * nw⁻¹) := by rw [this]
  have hCG := centralizer_eq_sup_of_pow_eq_one hp5 hpΩ hyH hyp
  have hHN : torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω (torusRootKernel y) : Set (ModGL Tag.E6 Ω)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN
  have hu' : G₃ * nw⁻¹ ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel y) := by
    rw [← hCG]
    refine Subgroup.mem_inf.2 ⟨mul_mem hG₃ (inv_mem hnwA),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hz]
    exact hu
  have hu'' : G₃ * nw⁻¹ ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
      (rootSpan Tag.E6 Ω (torusRootKernel y) : Set (ModGL Tag.E6 Ω)) := by
    rw [← hmul]
    exact hu'
  obtain ⟨t₀, ht₀, q₀, hq₀, huq⟩ := hu''
  set q'' : ModGL Tag.E6 Ω := t₀ * q₀ * t₀⁻¹ with hq''
  have hq''mem : q'' ∈ rootSpan Tag.E6 Ω (torusRootKernel y) :=
    (Subgroup.mem_normalizer_iff.1 (hHN ht₀) q₀).1 hq₀
  have hm' : G₃ * Q = q'' * (t₀ * nw * Q) := by
    have : G₃ = t₀ * q₀ * nw := by
      rw [show t₀ * q₀ = G₃ * nw⁻¹ from huq]
      group
    rw [this, hq'']
    group
  have hq₁₂ : n₁ * q'' * n₁⁻¹ ∈
      subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 := by
    have h := map_conj_rootSpan (τ := Tag.E6) (L := Ω) w₁ (S := torusRootKernel y)
      (fun α hα => hα.1)
    rw [hw₁, rootSpan_supportA2A2] at h
    rw [← h]
    exact ⟨q'', hq''mem, rfl⟩
  obtain ⟨⟨g₁, g₂⟩, hg⟩ := twoA2MulSup_surjective (Ω := Ω) ⟨n₁ * q'' * n₁⁻¹, hq₁₂⟩
  have hg' : twoA2Mul Ω (g₁, g₂) = n₁ * q'' * n₁⁻¹ := congrArg Subtype.val hg
  set E : ModGL Tag.E6 Ω := n₁ * (t₀ * nw * Q) * n₁⁻¹ with hE
  have hmE : n₁ * (G₃ * Q) * n₁⁻¹ = (n₁ * q'' * n₁⁻¹) * E := by
    rw [hm', hE]
    group
  set T : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ :=
    fun x => w₁ • (w • permLattice e6Rho (w₁⁻¹ • x)) with hT
  have hTadd : ∀ x y, T (x + y) = T x + T y := fun x y => lattice_T_add w₁ w x y
  have hEroot : ∀ β, IsRoot Tag.E6 β → ∃ μ : Ωˣ, ∀ c : Ω,
      E * pinnedX Tag.E6 Ω β c * E⁻¹ = pinnedX Tag.E6 Ω (T β) ((μ : Ω) * c) :=
    fun β hβ => conj_conj_t0nwP_pinnedX hβ w₁ w ht₀
  have hT56 : ∀ α ∈ parabolicRoots Tag.E6 support56, T α ∈ parabolicRoots Tag.E6 support13 := by
    intro α hα
    have h1 : w • permLattice e6Rho (w₁⁻¹ • α) ∈
        (fun x => w • permLattice e6Rho x) '' ((fun x => w₁⁻¹ • x) ''
          parabolicRoots Tag.E6 CFSG.RankThree.Lattice.supp56) :=
      ⟨w₁⁻¹ • α, ⟨α, hα, rfl⟩, rfl⟩
    rw [hex2] at h1
    obtain ⟨γ, hγ, hγeq⟩ := h1
    show w₁ • (w • permLattice e6Rho (w₁⁻¹ • α)) ∈ _
    rw [← hγeq, smul_inv_smul]
    exact hγ
  have hT13 : ∀ α ∈ parabolicRoots Tag.E6 support13, T α ∈ parabolicRoots Tag.E6 support56 := by
    intro α hα
    have h1 : w • permLattice e6Rho (w₁⁻¹ • α) ∈
        (fun x => w • permLattice e6Rho x) '' ((fun x => w₁⁻¹ • x) ''
          parabolicRoots Tag.E6 CFSG.RankThree.Lattice.supp13) :=
      ⟨w₁⁻¹ • α, ⟨α, hα, rfl⟩, rfl⟩
    rw [hex1] at h1
    obtain ⟨γ, hγ, hγeq⟩ := h1
    show w₁ • (w • permLattice e6Rho (w₁⁻¹ • α)) ∈ _
    rw [← hγeq, smul_inv_smul]
    exact hγ
  have hroots : ∀ i j : Fin 3, i ≠ j → ∃ a b : Fin 3, a ≠ b ∧
      T (chainRoot chain56 i j) = chainRoot chain13 a b := fun i j hij => by
    obtain ⟨a, b, hab, h⟩ := exists_chainRoot13_of_mem
      (hT56 _ (chainRoot56_mem_parabolicRoots hij))
    exact ⟨a, b, hab, h⟩
  have hQ12 : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      E * g * E⁻¹ ∈ subsystemGroup Tag.E6 Ω support56 := by
    intro g hg
    rw [subsystemGroup_eq_rootSpan] at hg ⊢
    exact conj_rootSpan_le T (fun α hα => hEroot α hα.1) hT13 g hg
  have horient : ∃ τ₁ τ₂ : Fin 3 → Fin 3 → Fin 3, (∀ i j, i ≠ j → τ₁ i j ≠ τ₂ i j) ∧
      (∀ i j, i ≠ j → T (chainRoot chain56 i j) = chainRoot chain13 (τ₁ i j) (τ₂ i j)) ∧
      ((∃ π : Equiv.Perm (Fin 3), ∀ i j, τ₁ i j = π i ∧ τ₂ i j = π j) ∨
        (∃ π : Equiv.Perm (Fin 3), ∀ i j, τ₁ i j = π j ∧ τ₂ i j = π i)) := by
    rcases a2_transition_cases hTadd hroots with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact ⟨fun i _ => π i, fun _ j => π j, fun i j hij => π.injective.ne hij,
        fun i j _ => hπ i j, Or.inl ⟨π, fun i j => ⟨rfl, rfl⟩⟩⟩
    · exact ⟨fun _ j => π j, fun i _ => π i, fun i j hij => (π.injective.ne hij).symm,
        fun i j _ => hπ i j, Or.inr ⟨π, fun i j => ⟨rfl, rfl⟩⟩⟩
  obtain ⟨τ₁, τ₂, hne, hTτ, hform⟩ := horient
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ μ : Ωˣ, ∀ c : Ω,
      (MulAut.conj E).toMonoidHom (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (τ₁ i j) (τ₂ i j)) ((μ : Ω) * c) := fun i j hij => by
    obtain ⟨μ, hμ⟩ := hEroot _ (isRoot_chainRoot56 hij)
    exact ⟨μ, fun c => by rw [← hTτ i j hij]; exact hμ c⟩
  obtain ⟨hQ, bb, hshape⟩ := exists_sl3_exchange_21 (MulAut.conj E).toMonoidHom τ₁ τ₂ hne hθ
  let θ21 : subsystemGroup Tag.E6 Ω support56 →* subsystemGroup Tag.E6 Ω support13 :=
    { toFun := fun g => ⟨(MulAut.conj E).toMonoidHom (g : ModGL Tag.E6 Ω), hQ g g.2⟩
      map_one' := Subtype.ext (map_one (MulAut.conj E).toMonoidHom)
      map_mul' := fun x y => Subtype.ext (map_mul (MulAut.conj E).toMonoidHom (x : ModGL Tag.E6 Ω) y) }
  let N : SL(3, Ω) →* SL(3, Ω) :=
    (a2Equiv₁ Ω).toMonoidHom.comp (θ21.comp (a2Equiv₂ Ω).symm.toMonoidHom)
  have hN : ∀ X : SL(3, Ω), ((a2Equiv₁ Ω).symm (N X) : ModGL Tag.E6 Ω) =
      E * ((a2Equiv₂ Ω).symm X : ModGL Tag.E6 Ω) * E⁻¹ := fun X => by
    change (((a2Equiv₁ Ω).symm ((a2Equiv₁ Ω) (θ21 ((a2Equiv₂ Ω).symm X))) : subsystemGroup Tag.E6 Ω support13) : ModGL Tag.E6 Ω) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hdisc : ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
      Ωˣ →* GL (Fin 3) Ω).range,
      Matrix.SpecialLinearGroup.toGL (g₁ * N (h₂ * invTransposeMapSL Fr 3
        (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹) * g₁⁻¹) =
        z * Matrix.SpecialLinearGroup.toGL (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
          h₁⁻¹) := by
    intro A
    obtain ⟨X₁, hX₁⟩ : ∃ X₁ : SL(3, Ω),
        X₁ = h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨X₂, hX₂⟩ : ∃ X₂ : SL(3, Ω), X₂ = h₂ * invTransposeMapSL Fr 3
        (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹ := ⟨_, rfl⟩
    rw [← hX₁, ← hX₂]
    obtain ⟨Y, hY⟩ : ∃ Y : SL(3, Ω), E * ((a2Equiv₁ Ω).symm X₁ : ModGL Tag.E6 Ω) * E⁻¹ =
        ((a2Equiv₂ Ω).symm Y : ModGL Tag.E6 Ω) :=
      ⟨a2Equiv₂ Ω ⟨_, hQ12 _ ((a2Equiv₁ Ω).symm X₁).2⟩, by rw [MulEquiv.symm_apply_apply]⟩
    have hmm := hP A
    rw [← hX₁, ← hX₂] at hmm
    have hfixu : ((n₁ * q'' * n₁⁻¹) * E) * twoA2Mul Ω (X₁, X₂) * ((n₁ * q'' * n₁⁻¹) * E)⁻¹ =
        twoA2Mul Ω (X₁, X₂) := by
      rw [← hmE]
      calc n₁ * (G₃ * Q) * n₁⁻¹ * twoA2Mul Ω (X₁, X₂) * (n₁ * (G₃ * Q) * n₁⁻¹)⁻¹
          = n₁ * ((G₃ * Q) * (n₁⁻¹ * twoA2Mul Ω (X₁, X₂) * n₁) * (G₃ * Q)⁻¹) * n₁⁻¹ := by
            group
        _ = n₁ * (n₁⁻¹ * twoA2Mul Ω (X₁, X₂) * n₁) * n₁⁻¹ := by rw [hmm]
        _ = twoA2Mul Ω (X₁, X₂) := by group
    have hEu : E * twoA2Mul Ω (X₁, X₂) * E⁻¹ = twoA2Mul Ω (N X₂, Y) := by
      have e1 : E * (((a2Equiv₁ Ω).symm X₁ : ModGL Tag.E6 Ω) *
          ((a2Equiv₂ Ω).symm X₂ : ModGL Tag.E6 Ω)) * E⁻¹ =
          (E * ((a2Equiv₁ Ω).symm X₁ : ModGL Tag.E6 Ω) * E⁻¹) *
            (E * ((a2Equiv₂ Ω).symm X₂ : ModGL Tag.E6 Ω) * E⁻¹) := by
        group
      rw [twoA2Mul_apply, twoA2Mul_apply, e1, hY, ← hN]
      exact (commute_Q₁_Q₂ ((a2Equiv₁ Ω).symm (N X₂)).2 ((a2Equiv₂ Ω).symm Y).2).eq.symm
    have hcomb : twoA2Mul Ω (g₁ * N X₂ * g₁⁻¹, g₂ * Y * g₂⁻¹) = twoA2Mul Ω (X₁, X₂) := by
      have e2 : twoA2Mul Ω (g₁ * N X₂ * g₁⁻¹, g₂ * Y * g₂⁻¹) =
          twoA2Mul Ω (g₁, g₂) * twoA2Mul Ω (N X₂, Y) * (twoA2Mul Ω (g₁, g₂))⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e2, ← hEu, hg']
      calc n₁ * q'' * n₁⁻¹ * (E * twoA2Mul Ω (X₁, X₂) * E⁻¹) * (n₁ * q'' * n₁⁻¹)⁻¹
          = ((n₁ * q'' * n₁⁻¹) * E) * twoA2Mul Ω (X₁, X₂) * ((n₁ * q'' * n₁⁻¹) * E)⁻¹ := by
            group
        _ = twoA2Mul Ω (X₁, X₂) := hfixu
    have hone : twoA2Mul Ω (g₁ * N X₂ * g₁⁻¹ * X₁⁻¹, g₂ * Y * g₂⁻¹ * X₂⁻¹) = 1 := by
      have h0 : twoA2Mul Ω (g₁ * N X₂ * g₁⁻¹, g₂ * Y * g₂⁻¹) * (twoA2Mul Ω (X₁, X₂))⁻¹ = 1 := by
        rw [hcomb, mul_inv_cancel]
      rw [← map_inv, ← map_mul] at h0
      exact h0
    obtain ⟨c, hc3, hc1, -⟩ := (twoA2Mul_eq_one_iff _ _).1 hone
    have hc0 : c ≠ 0 := ne_zero_of_pow_three_eq_one hc3
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0), ⟨_, rfl⟩, ?_⟩
    have hz1 : Matrix.SpecialLinearGroup.toGL (g₁ * N X₂ * g₁⁻¹ * X₁⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc1, Matrix.GeneralLinearGroup.coe_scalar]
      rfl
    rw [map_mul Matrix.SpecialLinearGroup.toGL (g₁ * N X₂ * g₁⁻¹) X₁⁻¹, map_inv] at hz1
    exact mul_inv_eq_iff_eq_mul.1 hz1
  rcases hform with ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    obtain ⟨A₀, hA₀⟩ := exists_conj_map_of_root_permuting (n := 3) (le_refl 3) (RingHom.id Ω) π N
      bb (fun i j hij t => by
        have h := hshape i j hij t
        rw [(hπ i j).1, (hπ i j).2] at h
        rw [RingHom.id_apply]
        exact h)
    have hGLN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
        A₀ * Matrix.SpecialLinearGroup.toGL X * A₀⁻¹ := fun X => by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA₀ X, Units.val_mul, Units.val_mul,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      simp
    refine not_twisted_discrepancy_pos Fr hFr k₂ (Matrix.SpecialLinearGroup.toGL g₁ * A₀ *
      Matrix.SpecialLinearGroup.toGL h₂) (Matrix.SpecialLinearGroup.toGL h₁) (fun A => ?_)
    obtain ⟨z, hzZ, hz⟩ := hdisc A
    refine ⟨z, hzZ, ?_⟩
    generalize Matrix.SpecialLinearGroup.map k₂.subtype A = A' at hz ⊢
    generalize invTransposeMapSL Fr 3 A' = τA at hz ⊢
    simp only [map_mul, map_inv, hGLN] at hz
    convert hz using 1
    group
  ·
    obtain ⟨A₀, hA₀⟩ := exists_conj_map_inv_transpose_of_root_permuting (n := 3) (le_refl 3)
      (RingHom.id Ω) π N bb (fun i j hij t => by
        have h := hshape i j hij t
        rw [(hπ i j).1, (hπ i j).2] at h
        rw [RingHom.id_apply]
        exact h)
    have hGLN : ∀ X : SL(3, Ω), Matrix.SpecialLinearGroup.toGL (N X) =
        A₀ * invTransposeHom (Matrix.SpecialLinearGroup.toGL X) * A₀⁻¹ := fun X => by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA₀ X, Units.val_mul, Units.val_mul,
        coe_invTransposeHom]
      simp [Matrix.coe_units_inv]
    refine not_twisted_discrepancy_neg Fr hFr k₂ htk (Matrix.SpecialLinearGroup.toGL g₁ * A₀ *
      invTransposeHom (Matrix.SpecialLinearGroup.toGL h₂)) (Matrix.SpecialLinearGroup.toGL h₁)
      (fun A => ?_)
    obtain ⟨z, hzZ, hz⟩ := hdisc A
    refine ⟨z, hzZ, ?_⟩
    generalize Matrix.SpecialLinearGroup.map k₂.subtype A = A' at hz ⊢
    generalize invTransposeMapSL Fr 3 A' = τA at hz ⊢
    simp only [map_mul, map_inv, hGLN] at hz
    convert hz using 1
    group

end CFSG.RankThree.PartOne.KETw3
