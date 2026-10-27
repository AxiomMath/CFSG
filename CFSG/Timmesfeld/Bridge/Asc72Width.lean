module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

theorem isSolvable_closure_isConj_of_isolated {K : Type} [Group K] [Finite K] {d : K}
    (hd1 : d ≠ 1) (hd2 : d * d = 1)
    (hiso : ∀ g : K, Commute (g * d * g⁻¹) d → g * d * g⁻¹ = d) :
    Group.IsSolvable (Subgroup.closure {x | IsConj d x}) := by
  classical
  let := Fintype.ofFinite K
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar K d hd1 hd2 (fun g h => hiso g h)
  set C := Subgroup.closure {x | IsConj d x} with hC
  set g : C →* K ⧸ N := (QuotientGroup.mk' N).comp C.subtype with hg
  have hrange : g.range ≤ Subgroup.zpowers (QuotientGroup.mk' N d) := by
    rintro _ ⟨c, rfl⟩
    have hle : C ≤ (Subgroup.zpowers (QuotientGroup.mk' N d)).comap (QuotientGroup.mk' N) := by
      rw [hC, Subgroup.closure_le]
      intro x hx
      obtain ⟨h, rfl⟩ := isConj_iff.mp hx
      have hmem : h * d * h⁻¹ * d⁻¹ ∈ N := hN h
      have heq : QuotientGroup.mk' N (h * d * h⁻¹) = QuotientGroup.mk' N d := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        have key : (h * d * h⁻¹)⁻¹ * d = d⁻¹ * (h * d * h⁻¹ * d⁻¹)⁻¹ * d⁻¹⁻¹ := by group
        rw [key]
        exact hNn.conj_mem _ (N.inv_mem hmem) d⁻¹
      show QuotientGroup.mk' N (h * d * h⁻¹) ∈ Subgroup.zpowers (QuotientGroup.mk' N d)
      rw [heq]
      exact Subgroup.mem_zpowers _
    exact hle c.2
  have hcomm : ∀ a b : g.range, a * b = b * a := by
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hrange a.2)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hrange b.2)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hsol2 : Group.IsSolvable g.range := Group.isSolvable_of_comm hcomm
  have hNsol : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hker : Group.IsSolvable g.ker := by
    let e : g.ker →* N :=
      { toFun := fun x => ⟨(x : C), by
          have := x.2
          rw [MonoidHom.mem_ker] at this
          simpa [hg, QuotientGroup.eq_one_iff] using this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := e) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g.rangeRestrict (by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

namespace Setup

variable {G : Type} [Group G] {D : Set G} (hS : Setup G D)
include hS

theorem isSolvable_of_forall_commute [Finite G]
    (h : ∀ u ∈ D, ∀ v ∈ D, Commute u v → u = v) : Group.IsSolvable G := by
  obtain ⟨d, hd⟩ := hS.nonempty
  have hiso : ∀ g : G, Commute (g * d * g⁻¹) d → g * d * g⁻¹ = d :=
    fun g hc => h _ (hS.conj_mem g hd) d hd hc
  have hsol := isSolvable_closure_isConj_of_isolated (hS.oddT.ne_one hd)
    (hS.oddT.mul_self_eq_one hd) hiso
  rw [← hS.eq_setOf_isConj hd, hS.gen] at hsol
  exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup G).subtype)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)

theorem exists_commute_of_not_isSolvable [Finite G] (h : ¬ Group.IsSolvable G) :
    ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v := by
  by_contra hcon
  push Not at hcon
  exact h (hS.isSolvable_of_forall_commute fun u hu v hv huv =>
    by_contra fun hne => hcon u hu v hv hne huv)

omit hS in
theorem exists_commute_ne_of_not_isSolvable [Finite G] (hS : Setup G D)
    (h : ¬ Group.IsSolvable G) {x : G} (hx : x ∈ D) : ∃ y ∈ D, x ≠ y ∧ Commute x y := by
  obtain ⟨u, hu, v, hv, huv, hc⟩ := hS.exists_commute_of_not_isSolvable h
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hu hx)
  exact ⟨g * v * g⁻¹, hS.conj_mem g hv, fun h' => huv (by simpa using h'),
    (Commute.conj_iff g).mpr hc⟩

theorem mul_not_mem_of_isSolvable [Finite G] (hsol : Group.IsSolvable G) {u v : G}
    (hu : u ∈ D) (hv : v ∈ D) : u * v ∉ D := by
  intro huv
  have hntriv : Nontrivial G := ⟨⟨u, 1, hS.oddT.ne_one hu⟩⟩
  have hne : commutator G ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn⟩ := (Group.isSolvable_def G).mp hsol
    have hall : ∀ m, derivedSeries G m = ⊤ := fun m => by
      induction m with
      | zero => rfl
      | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
    rw [hall n] at hn
    exact top_ne_bot hn
  have hdisj : ∀ x ∈ D, x ∉ commutator G := by
    rcases hS.subset_or_disjoint (commutator G) with h | h
    · exact absurd (hS.eq_top_of_subset _ h) hne
    · exact h
  apply hdisj _ huv
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, hS.abelianization_eq hv hu,
    ← map_mul, hS.oddT.mul_self_eq_one hu, map_one]

end Setup

theorem widthOne_of_forall_not_commute {Q : Type*} [Group Q] [Finite Q] {X : Set Q}
    (hX : IsOddTransp X) (hN : IsNormalSet X) (hne : X.Nonempty)
    (h : ∀ u ∈ X, ∀ v ∈ X, Commute u v → u = v) : WidthOne X := by
  intro S
  obtain ⟨x, hx⟩ := hne
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hX.orderOf_eq_two hx, pow_one]
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P S
  have hgx : g * x * g⁻¹ ∈ (S : Subgroup Q) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr (by
      simpa [MulAut.smul_def, mul_assoc] using hP (Subgroup.mem_zpowers x))
  rw [Set.ncard_eq_one]
  refine ⟨g * x * g⁻¹, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hyX, hyS⟩
    exact h _ hyX _ (hN g x hx) (hX.commute_of_isPGroup S.isPGroup' hyX (hN g x hx) hyS hgx)
  · rintro rfl
    exact ⟨hN g x hx, hgx⟩

end CFSG.Timmesfeld.Bridge.Asc72
