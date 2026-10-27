module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClGraph

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

@[expose] def McLBridge (K V : Type) [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (F : LinearMap.BilinForm K V) : Prop :=
  F.Nondegenerate → F.IsAlt → 4 ≤ Nat.card K → 4 ≤ Module.finrank K V →
  ∀ (X : Subgroup (V ≃ₗ[K] V)), X ≤ sympSubgroup F → ∀ (Y : Set V), (∀ y ∈ Y, y ≠ 0) →
    (∀ y ∈ Y, ∀ c : K, ∃ g ∈ X, ∀ v, g v = v + (c * F v y) • y) →
    X = Subgroup.closure {g : V ≃ₗ[K] V | ∃ y ∈ Y, ∃ c : K, ∀ v, g v = v + (c * F v y) • y} →
    (∀ U : Submodule K V, (∀ g ∈ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      X = sympSubgroup F

theorem eq_symp_of_transvection_point (hbr : McLBridge K V F) (hnd : F.Nondegenerate)
    (halt : F.IsAlt) (hq : 4 ≤ Nat.card K) (hdim : 4 ≤ Module.finrank K V)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ sympSubgroup F) {P : Set V} (hP0 : ∀ e ∈ P, e ≠ 0)
    (hfull : ∀ e ∈ P, ElationFull F ((H : Set _) ∩ pointRad F e) e)
    (hspan : Submodule.span K P = ⊤) {e : V} (heP : e ∈ P)
    (hT : ∀ c : K, ∃ g ∈ H, ∀ v, g v = v + (c * F v e) • e) : H = sympSubgroup F := by
  obtain ⟨Y, hYmem⟩ : ∃ Y : Set V, ∀ y, y ∈ Y ↔
      (y ≠ 0 ∧ ∀ c : K, ∃ g ∈ H, ∀ v, g v = v + (c * F v y) • y) :=
    ⟨{y | y ≠ 0 ∧ ∀ c : K, ∃ g ∈ H, ∀ v, g v = v + (c * F v y) • y}, fun y => Iff.rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup (V ≃ₗ[K] V),
      X = Subgroup.closure
        {g : V ≃ₗ[K] V | ∃ y ∈ Y, ∃ c : K, ∀ v, g v = v + (c * F v y) • y} :=
    ⟨_, rfl⟩
  have heY : e ∈ Y := (hYmem e).mpr ⟨hP0 e heP, hT⟩
  have hYinv : ∀ g ∈ H, ∀ y ∈ Y, g y ∈ Y := by
    intro g hg y hy
    obtain ⟨hy0, hyT⟩ := (hYmem y).mp hy
    have hgI : IsIsom F g := hH hg
    rw [hYmem]
    refine ⟨fun h => hy0 ?_, fun c => ?_⟩
    · exact (map_eq_zero_iff g g.injective).mp h
    · obtain ⟨h, hhH, hh⟩ := hyT c
      refine ⟨g * h * g⁻¹, H.mul_mem (H.mul_mem hg hhH) (H.inv_mem hg), fun w => ?_⟩
      have hgw : g (g⁻¹ w) = w := by simp
      have hF : F (g⁻¹ w) y = F w (g y) := by
        have := hgI (g⁻¹ w) y
        rw [hgw] at this
        exact this.symm
      simp only [LinearEquiv.mul_apply]
      rw [hh (g⁻¹ w), map_add, map_smul, hgw, hF]
  have hXH : X ≤ H := by
    rw [hXdef]
    refine (Subgroup.closure_le H).mpr fun g hg => ?_
    obtain ⟨y, hy, c, hgy⟩ := hg
    obtain ⟨h, hhH, hh⟩ := ((hYmem y).mp hy).2 c
    have hgh : g = h := LinearEquiv.ext fun v => (hgy v).trans (hh v).symm
    rw [hgh]
    exact hhH
  have hXsymp : X ≤ sympSubgroup F := hXH.trans hH
  have hYtr : ∀ y ∈ Y, ∀ c : K, ∃ g ∈ X, ∀ v, g v = v + (c * F v y) • y := by
    intro y hy c
    obtain ⟨h, _, hh⟩ := ((hYmem y).mp hy).2 c
    refine ⟨h, ?_, hh⟩
    rw [hXdef]
    apply Subgroup.subset_closure
    exact ⟨y, hy, c, hh⟩
  have hY0 : ∀ y ∈ Y, y ≠ 0 := fun y hy => ((hYmem y).mp hy).1
  have hspanY : Submodule.span K Y = ⊤ := by
    have hUinv : ∀ g ∈ H, ∀ u ∈ Submodule.span K Y, g u ∈ Submodule.span K Y := by
      intro g hg u hu
      induction hu using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hYinv g hg y hy)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
    have hne : Submodule.span K Y ≠ ⊥ := by
      intro h0
      have hmem : e ∈ Submodule.span K Y := Submodule.subset_span heY
      rw [h0, Submodule.mem_bot] at hmem
      exact hP0 e heP hmem
    exact eq_top_of_invariant hnd halt (by omega) hH hP0 hfull hspan _ hUinv hne
  have hconn : ∀ x ∈ Y, Relation.ReflTransGen (fun a b => a ∈ Y ∧ b ∈ Y ∧ F a b ≠ 0) e x :=
    connected_of_elationFull hnd halt hH Y hY0 hYinv hspanY heY (hfull e heP)
  have hirr : ∀ U : Submodule K V, (∀ g ∈ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hUX
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    have hgen : ∀ y ∈ Y, ∀ u ∈ U, F u y ≠ 0 → y ∈ U := by
      intro y hy u hu huy
      obtain ⟨g, hgX, hg⟩ := hYtr y hy (F u y)⁻¹
      have h1 : g u = u + y := by rw [hg u, inv_mul_cancel₀ huy, one_smul]
      have h2 : g u ∈ U := hUX g hgX u hu
      have h3 : y = g u - u := by rw [h1]; abel
      rw [h3]
      exact U.sub_mem h2 hu
    have hex : ∃ y ∈ Y, ∃ u ∈ U, F u y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hU0
      rw [Submodule.eq_bot_iff]
      intro u hu
      exact eq_zero_of_perp_span hnd hspanY (fun y hy => hcon y hy u hu)
    obtain ⟨y₀, hy₀Y, u₀, hu₀U, hFu₀⟩ := hex
    have hy₀U : y₀ ∈ U := hgen y₀ hy₀Y u₀ hu₀U hFu₀
    have key : ∀ x, Relation.ReflTransGen (fun a b => a ∈ Y ∧ b ∈ Y ∧ F a b ≠ 0) e x →
        (e ∈ U ↔ x ∈ U) := by
      intro x hx
      induction hx with
      | refl => exact Iff.rfl
      | tail _ hbc ih =>
        obtain ⟨hbY, hcY, hbc0⟩ := hbc
        rw [ih]
        exact ⟨fun hb => hgen _ hcY _ hb hbc0,
          fun hc => hgen _ hbY _ hc (by rw [form_comm halt]; exact hbc0)⟩
    have heU : e ∈ U := (key y₀ (hconn y₀ hy₀Y)).mpr hy₀U
    have hYU : Y ⊆ (U : Set V) := fun x hx => (key x (hconn x hx)).mp heU
    have hspanU : Submodule.span K Y ≤ U := Submodule.span_le.mpr hYU
    rw [hspanY] at hspanU
    exact top_le_iff.mp hspanU
  have hXeq : X = sympSubgroup F :=
    hbr hnd halt hq hdim X hXsymp Y hY0 hYtr hXdef hirr
  have hsymp_le : sympSubgroup F ≤ H := by
    rw [← hXeq]
    exact hXH
  exact le_antisymm hH hsymp_le

end CFSG.RankThree.GF2n.Stroth80.Classify
