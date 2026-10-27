module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import CFSG.GH74.Filter.Small.Eigenbasis
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open scoped commutatorElement

section CentWeights

variable {X : Type*} [Group X] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

private def cwSpace (ρ : X →* (V →ₗ[F] V)) (U : Subgroup X) (χ : U → F) : Submodule F V :=
  ⨅ u : U, Module.End.eigenspace (ρ u) (χ u)

private lemma mem_cwSpace {ρ : X →* (V →ₗ[F] V)} {U : Subgroup X} {χ : U → F} {v : V} :
    v ∈ cwSpace ρ U χ ↔ ∀ u : U, ρ u v = χ u • v := by
  simp only [cwSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

private lemma iSupIndep_cwSpace (ρ : X →* (V →ₗ[F] V)) (U : Subgroup X) :
    iSupIndep (cwSpace ρ U) :=
  TauCeti.iSupIndep_iInf_eigenspace fun u : U => ρ (u : X)

private lemma cwSpace_char {ρ : X →* (V →ₗ[F] V)} {U : Subgroup X} {χ : U → F}
    (h : cwSpace ρ U χ ≠ ⊥) : χ 1 = 1 ∧ ∀ a b : U, χ (a * b) = χ a * χ b := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hv' : ∀ g : U, v ∈ Module.End.eigenspace ((ρ.comp U.subtype) g) (χ g) :=
    fun g => Module.End.mem_eigenspace_iff.2 (mem_cwSpace.1 hv g)
  exact ⟨(ρ.comp U.subtype).eigenvalue_one_of_jointEigenvector χ v hv0 hv',
    (ρ.comp U.subtype).eigenvalue_mul_of_jointEigenvector χ v hv0 hv'⟩

open scoped _root_.Classical in
private lemma two_mul_ker_ge {G : Type*} [Group G] [Fintype G] (χ : G → F)
    (hmul : ∀ a b, χ (a * b) = χ a * χ b) (hpm : ∀ g, χ g = 1 ∨ χ g = -1) :
    Fintype.card G ≤ 2 * (Finset.univ.filter fun g => χ g = 1).card := by
  have hPN := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
    (fun g => χ g = 1)
  rw [Finset.card_univ] at hPN
  have hle : (Finset.univ.filter fun g => ¬ χ g = 1).card ≤
      (Finset.univ.filter fun g => χ g = 1).card := by
    rcases (Finset.univ.filter fun g => ¬ χ g = 1).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · rw [h]
      exact Nat.zero_le _
    · have ha' : χ a = -1 := (hpm a).resolve_left (Finset.mem_filter.1 ha).2
      refine Finset.card_le_card_of_injOn (fun g => a * g) ?_
        (fun g _ g' _ hh => mul_left_cancel hh)
      intro g hg
      rw [Finset.mem_coe, Finset.mem_filter] at hg
      have hg' : χ g = -1 := (hpm g).resolve_left hg.2
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show χ (a * g) = 1
      rw [hmul, ha', hg']
      ring
  omega

open scoped _root_.Classical in
private lemma card_filter_le_two [FiniteDimensional F V] (ρ : X →* (V →ₗ[F] V))
    {U : Subgroup X}
    (hub : ∀ s ∈ U, s ≠ 1 → Module.finrank F (LinearMap.ker (ρ s - 1)) ≤ 2)
    (T : Finset (U → F)) (hT : ∀ χ ∈ T, cwSpace ρ U χ ≠ ⊥) (s : U) (hs : s ≠ 1) :
    (T.filter fun χ => χ s = 1).card ≤ 2 := by
  choose! v hvm hv0 using fun χ (h : χ ∈ T) =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hT χ h)
  set Ts := T.filter fun χ => χ s = 1
  have hTsT : ∀ χ ∈ Ts, χ ∈ T := fun χ hχ => (Finset.mem_filter.1 hχ).1
  have hli : LinearIndependent F fun χ : Ts => v χ :=
    ((iSupIndep_cwSpace ρ U).comp (Subtype.val_injective (p := fun χ => χ ∈ Ts))).linearIndependent
      _ (fun χ => hvm χ (hTsT χ χ.2)) (fun χ => hv0 χ (hTsT χ χ.2))
  have hker : ∀ χ : Ts, v χ ∈ LinearMap.ker (ρ s - 1) := by
    intro χ
    have h1 : χ.1 s = 1 := (Finset.mem_filter.1 χ.2).2
    have h2 := mem_cwSpace.1 (hvm χ (hTsT χ χ.2)) s
    rw [LinearMap.mem_ker, LinearMap.sub_apply, h2, h1, one_smul]
    simp
  let w : Ts → LinearMap.ker (ρ s - 1) := fun χ => ⟨v χ, hker χ⟩
  have hw : LinearIndependent F w :=
    LinearIndependent.of_comp (LinearMap.ker (ρ s - 1)).subtype hli
  calc Ts.card = Fintype.card Ts := (Fintype.card_coe Ts).symm
    _ ≤ Module.finrank F (LinearMap.ker (ρ s - 1)) := hw.fintype_card_le_finrank
    _ ≤ 2 := hub s s.2 (fun h => hs (Subtype.ext h))

open scoped _root_.Classical in
private lemma card_weights_le_four [Finite X] [FiniteDimensional F V] (ρ : X →* (V →ₗ[F] V))
    {U : Subgroup X} (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU8 : 8 ≤ Nat.card U)
    (hub : ∀ s ∈ U, s ≠ 1 → Module.finrank F (LinearMap.ker (ρ s - 1)) ≤ 2)
    (T : Finset (U → F)) (hT : ∀ χ ∈ T, cwSpace ρ U χ ≠ ⊥) : T.card ≤ 4 := by
  have : Fintype U := Fintype.ofFinite U
  by_contra hcon
  have hm : 5 ≤ T.card := not_le.1 hcon
  have hn : 8 ≤ Fintype.card U := by rwa [← Nat.card_eq_fintype_card]
  set D : Finset U := Finset.univ.erase 1 with hD
  have hDc : D.card + 1 = Fintype.card U := by
    rw [hD, Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ]
  have hdc : ∑ s ∈ D, (T.filter fun χ => χ s = 1).card =
      ∑ χ ∈ T, (D.filter fun s => χ s = 1).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hup : ∑ s ∈ D, (T.filter fun χ => χ s = 1).card ≤ D.card * 2 := by
    have := Finset.sum_le_card_nsmul D (fun s => (T.filter fun χ => χ s = 1).card) 2
      (fun s hs => card_filter_le_two ρ hub T hT s (Finset.ne_of_mem_erase hs))
    rw [smul_eq_mul] at this
    exact this
  have hlow : ∀ χ ∈ T, Fintype.card U ≤ 2 * (D.filter fun s => χ s = 1).card + 2 := by
    intro χ hχ
    obtain ⟨h1, hmul⟩ := cwSpace_char (hT χ hχ)
    have hpm : ∀ g : U, χ g = 1 ∨ χ g = -1 := by
      intro g
      have hg : g * g = 1 := Subtype.ext (by simpa [sq] using hU2 g g.2)
      have : χ g * χ g = 1 := by rw [← hmul, hg, h1]
      exact mul_self_eq_one_iff.1 this
    have h3 := two_mul_ker_ge χ hmul hpm
    have hb : (D.filter fun s => χ s = 1) = (Finset.univ.filter fun g => χ g = 1).erase 1 := by
      rw [hD, Finset.filter_erase]
    have hmem : (1 : U) ∈ Finset.univ.filter fun g => χ g = 1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    have h4 := Finset.card_erase_add_one hmem
    rw [hb]
    omega
  have hsum : T.card * Fintype.card U ≤
      2 * (∑ χ ∈ T, (D.filter fun s => χ s = 1).card) + 2 * T.card := by
    calc T.card * Fintype.card U = ∑ _χ ∈ T, Fintype.card U := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ χ ∈ T, (2 * (D.filter fun s => χ s = 1).card + 2) := Finset.sum_le_sum hlow
      _ = 2 * (∑ χ ∈ T, (D.filter fun s => χ s = 1).card) + 2 * T.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul]
          ring
  rw [← hdc, ← hDc] at hsum
  have hd : 7 ≤ D.card := by omega
  nlinarith

private def cwAct (U : Subgroup X) [U.Normal] (x : X) (χ : U → F) : U → F :=
  fun u => χ ((MulAut.conjNormal x⁻¹ : MulAut U) u)

private lemma rho_mem_cwSpace_act (ρ : X →* (V →ₗ[F] V)) (U : Subgroup X) [U.Normal] (x : X)
    {χ : U → F} {v : V} (hv : v ∈ cwSpace ρ U χ) : ρ x v ∈ cwSpace ρ U (cwAct U x χ) := by
  refine mem_cwSpace.2 fun u => ?_
  have h1 := mem_cwSpace.1 hv ((MulAut.conjNormal x⁻¹ : MulAut U) u)
  have h2 : (((MulAut.conjNormal x⁻¹ : MulAut U) u : U) : X) = x⁻¹ * u * x := by
    simp
  have h3 : (u : X) * x = x * (((MulAut.conjNormal x⁻¹ : MulAut U) u : U) : X) := by
    rw [h2]
    group
  have e0 : ρ u (ρ x v) = ρ ((u : X) * x) v := by
    rw [map_mul, Module.End.mul_apply]
  have e1 : ρ ((u : X) * x) v = ρ x (ρ (((MulAut.conjNormal x⁻¹ : MulAut U) u : U) : X) v) := by
    rw [h3, map_mul, Module.End.mul_apply]
  show ρ u (ρ x v) = χ ((MulAut.conjNormal x⁻¹ : MulAut U) u) • ρ x v
  rw [e0, e1, h1, map_smul]

private lemma cwSpace_conj_invariant [Finite X] (ρ : X →* (V →ₗ[F] V)) {U : Subgroup X}
    [U.Normal] (hA : ∀ T : Finset (U → F), (∀ χ ∈ T, cwSpace ρ U χ ≠ ⊥) → T.card ≤ 4)
    (hidx : ∀ H : Subgroup X, Subgroup.centralizer (U : Set X) ≤ H → H.index < 5 → H = ⊤)
    {χ : U → F} (hχ : cwSpace ρ U χ ≠ ⊥) (x : X) (u : U) :
    χ ((MulAut.conjNormal x : MulAut U) u) = χ u := by
  let _ : MulAction X (U → F) :=
    { smul := cwAct U
      one_smul := fun χ => by
        show cwAct U 1 χ = χ
        funext u
        simp [cwAct]
      mul_smul := fun x y χ => by
        show cwAct U (x * y) χ = cwAct U x (cwAct U y χ)
        funext u
        simp [cwAct, mul_inv_rev] }
  have horb : ∀ χ' ∈ MulAction.orbit X χ, cwSpace ρ U χ' ≠ ⊥ := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    refine (Submodule.ne_bot_iff _).2 ⟨ρ y v, rho_mem_cwSpace_act ρ U y hv, fun h0 => hv0 ?_⟩
    have h1 : ρ y⁻¹ (ρ y v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, h0, map_zero]
  have hS : (MulAction.stabilizer X χ).index < 5 := by
    rw [MulAction.index_stabilizer]
    have hO : (MulAction.orbit X χ).Finite := Set.finite_range _
    rw [Set.ncard_eq_toFinset_card _ hO]
    have := hA hO.toFinset fun χ' hχ' => horb χ' (hO.mem_toFinset.1 hχ')
    omega
  have hle : Subgroup.centralizer (U : Set X) ≤ MulAction.stabilizer X χ := by
    intro y hy
    rw [MulAction.mem_stabilizer_iff]
    show cwAct U y χ = χ
    funext u
    have hyu := (Subgroup.mem_centralizer_iff.1 hy) (u : X) u.2
    have hcu : (MulAut.conjNormal y⁻¹ : MulAut U) u = u := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, inv_inv]
      calc y⁻¹ * (u : X) * y = y⁻¹ * ((u : X) * y) := mul_assoc _ _ _
        _ = y⁻¹ * (y * (u : X)) := by rw [hyu]
        _ = u := inv_mul_cancel_left _ _
    show χ ((MulAut.conjNormal y⁻¹ : MulAut U) u) = χ u
    rw [hcu]
  have htop := hidx _ hle hS
  have hx : x⁻¹ ∈ MulAction.stabilizer X χ := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [MulAction.mem_stabilizer_iff] at hx
  have h := congrFun hx u
  change χ ((MulAut.conjNormal x⁻¹⁻¹ : MulAut U) u) = χ u at h
  rwa [inv_inv] at h

private lemma commutator_mem_of_normal {U : Subgroup X} [U.Normal] {u : X} (hu : u ∈ U)
    (x : X) : ⁅u, x⁆ ∈ U := by
  have h := U.mul_mem hu (Subgroup.Normal.conj_mem inferInstance u⁻¹ (U.inv_mem hu) x)
  have e : u * (x * u⁻¹ * x⁻¹) = ⁅u, x⁆ := by
    rw [commutatorElement_def]
    group
  rwa [e] at h

end CentWeights

theorem res1Cent_rho_commutator_eq_one {X : Type*} [Group X] [Finite X] {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : X →* (V →ₗ[F] V)) {U : Subgroup X} [U.Normal] (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hU8 : 8 ≤ Nat.card U)
    (hidx : ∀ H : Subgroup X, Subgroup.centralizer (U : Set X) ≤ H → H.index < 5 → H = ⊤)
    (hub : ∀ s ∈ U, s ≠ 1 → Module.finrank F (LinearMap.ker (ρ s - 1)) ≤ 2) :
    ∀ u ∈ U, ∀ x : X, ρ ⁅u, x⁆ = 1 := by
  intro u hu x
  have hsq1 : ∀ c : U, c * c = 1 := fun c => Subtype.ext (by simpa [sq] using hU2 c c.2)
  have hUc : ∀ a b : U, a * b = b * a := by
    intro a b
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq1 (a * b))).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right (hsq1 a), inv_eq_of_mul_eq_one_right (hsq1 b)]
  have hcomm : ∀ i j : U, Commute (ρ (i : X)) (ρ (j : X)) := by
    intro i j
    show ρ (i : X) * ρ (j : X) = ρ (j : X) * ρ (i : X)
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (congrArg Subtype.val (hUc i j))
  have hsq : ∀ i : U, ρ (i : X) ^ 2 = 1 := fun i => by
    rw [← map_pow, hU2 i i.2, map_one]
  obtain ⟨b, μ, hb⟩ := CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one h2
    (fun i : U => ρ (i : X)) hcomm hsq
  have hA := card_weights_le_four ρ hU2 hU8 hub
  have hne : ∀ j, cwSpace ρ U (fun i => μ i j) ≠ ⊥ := fun j =>
    (Submodule.ne_bot_iff _).2 ⟨b j, mem_cwSpace.2 fun i => hb i j, b.ne_zero j⟩
  have hinv : ∀ j (y : X) (w : U), μ ((MulAut.conjNormal y : MulAut U) w) j = μ w j :=
    fun j y w => cwSpace_conj_invariant ρ hA hidx (hne j) y w
  set a : U := ⟨u, hu⟩ with ha
  let g : U := ⟨⁅u, x⁆, commutator_mem_of_normal hu x⟩
  have hg : g = a * ((MulAut.conjNormal x : MulAut U) a)⁻¹ := by
    apply Subtype.ext
    simp only [g, ha, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
      commutatorElement_def]
    group
  have hμg : ∀ j, μ g j = 1 := by
    intro j
    obtain ⟨h1, hmul⟩ := cwSpace_char (hne j)
    have e1 : μ ((MulAut.conjNormal x : MulAut U) a⁻¹) j = μ a⁻¹ j := hinv j x a⁻¹
    calc μ g j = μ (a * ((MulAut.conjNormal x : MulAut U) a)⁻¹) j := by rw [hg]
      _ = μ a j * μ (((MulAut.conjNormal x : MulAut U) a)⁻¹) j := hmul a _
      _ = μ a j * μ a⁻¹ j := by rw [← map_inv, e1]
      _ = μ (a * a⁻¹) j := (hmul a a⁻¹).symm
      _ = 1 := by rw [mul_inv_cancel]; exact h1
  refine b.ext fun j => ?_
  have h := hb g j
  rw [hμg j, one_smul] at h
  rw [Module.End.one_apply]
  exact h

theorem res1Cent_finrank_le_two {X : Type*} [Group X] [Finite X] {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : X →* (V →ₗ[F] V)) {U : Subgroup X} [U.Normal] (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hU8 : 8 ≤ Nat.card U)
    (hidx : ∀ H : Subgroup X, Subgroup.centralizer (U : Set X) ≤ H → H.index < 5 → H = ⊤)
    (hub : ∀ s ∈ U, s ≠ 1 → Module.finrank F (LinearMap.ker (ρ s - 1)) ≤ 2)
    (hne : ∃ u ∈ U, ∃ x : X, ⁅u, x⁆ ≠ 1) :
    Module.finrank F V ≤ 2 := by
  obtain ⟨u, hu, x, hx⟩ := hne
  have h1 := res1Cent_rho_commutator_eq_one h2 ρ hU2 hU8 hidx hub u hu x
  have h3 := hub ⁅u, x⁆ (commutator_mem_of_normal hu x) hx
  rw [h1, sub_self, LinearMap.ker_zero, finrank_top] at h3
  exact h3

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
