module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Act
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3SmNineZ
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.Quasithin
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
  (outer_solvable_of_nonempty_equiv)

theorem perfectCore_map_eq_one {G : Type*} [Group G] [Finite G] {Q : Type*} [Group Q]
    [Group.IsSolvable Q] (M : Subgroup G) (π : ↥M →* Q) (g : ↥(perfectCore M)) :
    π (Subgroup.inclusion (perfectCore_le M) g) = 1 := by
  have hperf : Group.IsPerfect ↥(perfectCore M) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect M)
  let ψ : ↥(perfectCore M) →* Q := π.comp (Subgroup.inclusion (perfectCore_le M))
  have hperfr : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hsub : Subsingleton ↥ψ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥ψ.range inferInstance
  have := Subsingleton.elim (⟨ψ g, g, rfl⟩ : ↥ψ.range) 1
  exact congrArg Subtype.val this

variable {p : ℕ} {K : Type} [Field K] {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)}
  {H : Subgroup (GL (Fin 3) K)}

theorem H_le_X (h : QCtx p K M H) : H ≤ StatedSU 3 (p ^ 1) K := by
  intro x hx
  obtain ⟨m, -, rfl⟩ := h.le hx
  exact m.2

theorem subgroupOf_le_M (h : QCtx p K M H) :
    H.subgroupOf (StatedSU 3 (p ^ 1) K) ≤ M := by
  intro y hy
  obtain ⟨m, hm, hmy⟩ := h.le hy
  have : m = y := Subtype.ext hmy
  rwa [← this]

theorem exists_mul_central [Finite K] (h : QCtx p K M H)
    (hsolv : Group.IsSolvable (Outer (H ⧸ Subgroup.center H))) {a : ↥(StatedSU 3 (p ^ 1) K)}
    (ha : a ∈ perfectCore M) :
    ∃ x ∈ H.subgroupOf (StatedSU 3 (p ^ 1) K), ∃ g : ↥(StatedSU 3 (p ^ 1) K),
      (∀ y : ↥(StatedSU 3 (p ^ 1) K), y * g = g * y) ∧ a = x * g := by
  let π : ↥M →* Outer (H ⧸ Subgroup.center H) :=
    (QuotientGroup.mk' (inner (H ⧸ Subgroup.center H))).comp (qAct h)
  have h1 : π ⟨a, perfectCore_le M ha⟩ = 1 := perfectCore_map_eq_one M π ⟨a, ha⟩
  have h2 : qAct h ⟨a, perfectCore_le M ha⟩ ∈ inner (H ⧸ Subgroup.center H) :=
    (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨s, hs⟩ := h2
  obtain ⟨xs, rfl⟩ := QuotientGroup.mk_surjective s
  let xX : ↥(StatedSU 3 (p ^ 1) K) := ⟨(xs : GL (Fin 3) K), H_le_X h xs.2⟩
  have hxX : xX ∈ H.subgroupOf (StatedSU 3 (p ^ 1) K) := xs.2
  let xM : ↥M := ⟨xX, subgroupOf_le_M h hxX⟩
  have hact : qAct h xM = MulAut.conj (QuotientGroup.mk xs : H ⧸ Subgroup.center H) := by
    refine MulEquiv.ext fun q => QuotientGroup.induction_on q fun y => ?_
    rw [qAct_apply_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  set g' : ↥M := xM⁻¹ * ⟨a, perfectCore_le M ha⟩ with hg'
  have hg'1 : qAct h g' = 1 := by
    rw [hg', map_mul, map_inv, hact]
    rw [← hs]
    exact inv_mul_cancel _
  have hc := qAct_ker_mem_center h hg'1
  refine ⟨xX, hxX, (g' : ↥(StatedSU 3 (p ^ 1) K)), fun y => ?_, ?_⟩
  · apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hc (y : GL (Fin 3) K))
  · have : (⟨a, perfectCore_le M ha⟩ : ↥M) = xM * g' := by rw [hg']; group
    exact congrArg Subtype.val this

theorem perfectCore_eq_subgroupOf [Finite K] (h : QCtx p K M H)
    (hsolv : Group.IsSolvable (Outer (H ⧸ Subgroup.center H))) :
    perfectCore M = H.subgroupOf (StatedSU 3 (p ^ 1) K) := by
  apply le_antisymm
  · calc perfectCore M = ⁅perfectCore M, perfectCore M⁆ := (perfectCore_perfect M).symm
      _ ≤ H.subgroupOf (StatedSU 3 (p ^ 1) K) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        obtain ⟨x₁, hx₁, g₁, hg₁, rfl⟩ := exists_mul_central h hsolv ha
        obtain ⟨x₂, hx₂, g₂, hg₂, rfl⟩ := exists_mul_central h hsolv hb
        rw [commutatorElement_mul_mul_of_central hg₁ hg₂]
        simp only [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx₁ hx₂)
          (Subgroup.inv_mem _ hx₁)) (Subgroup.inv_mem _ hx₂)
  · have hperf : Group.IsPerfect ↥(H.subgroupOf (StatedSU 3 (p ^ 1) K)) :=
      have : Group.IsPerfect ↥H := h.quasi.1
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe (H_le_X h)).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (H_le_X h)).symm.surjective
    exact le_perfectCore_of_perfect (subgroupOf_le_M h) (Subgroup.isPerfect_iff.mp hperf)

theorem su3_nine_row [Finite K] (h3 : (3 : K) ≠ 0) (h : QCtx p K M H) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 9) (e : H ⧸ Subgroup.center H ≃* StatedProj (StatedSL 2 F)) :
    IsHat ↥(perfectCore M) (alternatingGroup (Fin 6)) ∧
      ∀ z ∈ Subgroup.center ↥(perfectCore M),
        (((z : ↥(perfectCore M)) : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) ∈
          StatedScalars (Fin 3) K := by
  have hF9 : Nat.card F = 3 ^ 2 := by rw [hF]; norm_num
  obtain ⟨-, hZ3⟩ := linear_two_three_K h3 h.scalar h.det h.center (f := 2) (by norm_num)
    (by norm_num) hF9 e
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ψ⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism F
    (by rw [← Nat.card_eq_fintype_card, hF])
  let e6 : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6) := (toPSL2 e).trans ψ
  have hsolv := outer_solvable_of_nonempty_equiv ⟨e6⟩
  have hpc := perfectCore_eq_subgroupOf h hsolv
  have hHat : IsHat ↥H (alternatingGroup (Fin 6)) := ⟨h.quasi, hZ3, ⟨e6⟩⟩
  let ε : ↥(perfectCore M) ≃* ↥H :=
    (MulEquiv.subgroupCongr hpc).trans (Subgroup.subgroupOfEquivOfLe (H_le_X h))
  refine ⟨IsHat.of_mulEquiv ε.symm hHat, fun z hz => ?_⟩
  have hcomm : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) *
      (((z : ↥(perfectCore M)) : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) =
      (((z : ↥(perfectCore M)) : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) *
        (x : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx
    have hxX : (⟨x, H_le_X h hx⟩ : ↥(StatedSU 3 (p ^ 1) K)) ∈
        H.subgroupOf (StatedSU 3 (p ^ 1) K) := hx
    have hxpc : (⟨x, H_le_X h hx⟩ : ↥(StatedSU 3 (p ^ 1) K)) ∈ perfectCore M := hpc ▸ hxX
    have := Subgroup.mem_center_iff.mp hz ⟨_, hxpc⟩
    have h' := congrArg (fun w : ↥(perfectCore M) =>
      (((w : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) this
    simpa [Units.val_mul] using h'
  obtain ⟨c, hc⟩ := h.scalar _ hcomm
  have hcen : Subgroup.center (GL (Fin 3) K) = StatedScalars (Fin 3) K :=
    Matrix.GeneralLinearGroup.center_eq_range_scalar
  rw [← hcen]
  exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, hc.symm⟩

end CFSG.Quasithin.A312U3
