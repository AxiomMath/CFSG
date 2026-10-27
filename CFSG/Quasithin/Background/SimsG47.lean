module

public import CFSG.Quasithin.Background.SimsG4Core
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

private theorem commutator_span_invariant (G₀ : Subgroup (V ≃ₗ[F] V)) (g₀ : V ≃ₗ[F] V)
    (hg₀ : g₀ ∈ G₀) (w : V)
    (hw : w ∈ Submodule.span F {x | ∃ g ∈ transvGen G₀, ∃ v, x = g v - v}) :
    g₀ w ∈ Submodule.span F {x | ∃ g ∈ transvGen G₀, ∃ v, x = g v - v} := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, v, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨g₀ * g * g₀⁻¹, conj_mem_transvGen hg₀ hg, g₀ v, ?_⟩
    simp only [map_sub, LinearEquiv.mul_apply, inv_mul_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem transvGen_irred_of_transitive (G₀ : Subgroup (V ≃ₗ[F] V)) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty)
    (htrans : ∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀, ∃ g ∈ transvGen G₀, g * a * g⁻¹ = b) :
    IsIrredOnV (transvGen G₀) := by
  obtain ⟨d₀, hd₀⟩ := hD
  intro U hU
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  have hmove : ∃ a ∈ transvSet G₀, ∃ u ∈ U, a u ≠ u := by
    by_contra hcon
    push Not at hcon
    let C : Submodule F V :=
      { carrier := {v | ∀ g ∈ transvGen G₀, g v = v}
        add_mem' := fun {x y} hx hy g hg => by rw [map_add, hx g hg, hy g hg]
        zero_mem' := fun g _ => map_zero g
        smul_mem' := fun c x hx g hg => by rw [map_smul, hx g hg] }
    have hfixU : ∀ g ∈ transvGen G₀, ∀ u ∈ U, g u = u := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem a ha => exact fun u hu => hcon a ha u hu
      | one => exact fun u _ => rfl
      | mul x y hx hy ihx ihy =>
        intro u hu
        rw [LinearEquiv.mul_apply, ihy u hu, ihx u hu]
      | inv x hx ihx =>
        intro u hu
        have h1 := ihx u hu
        calc x⁻¹ u = x⁻¹ (x u) := by rw [h1]
          _ = u := inv_mul_apply x u
    have hUC : U ≤ C := fun u hu g hg => hfixU g hg u hu
    have hCinv : ∀ g ∈ G₀, ∀ c ∈ C, g c ∈ C := by
      intro g hg c hc k hk
      have := hc (g⁻¹ * k * g⁻¹⁻¹) (conj_mem_transvGen (G₀.inv_mem hg) hk)
      rw [inv_inv] at this
      simp only [LinearEquiv.mul_apply] at this
      calc k (g c) = g (g⁻¹ (k (g c))) := (mul_inv_apply g _).symm
        _ = g c := by rw [this]
    rcases hirr C hCinv with hbot | htop
    · exact hU0 (eq_bot_iff.mpr (hbot ▸ hUC))
    · apply transv_ne_one d₀ hd₀.2
      apply LinearEquiv.ext
      intro v
      have hv : v ∈ C := by rw [htop]; exact Submodule.mem_top
      exact hv d₀ (Subgroup.subset_closure hd₀)
  obtain ⟨a, ha, u, hu, hau⟩ := hmove
  have hcentre : ∀ b ∈ transvSet G₀, ∀ v, b v - v ∈ U := by
    have hVa : commSpace a ≤ U := by
      have hx : a u - u ∈ U ⊓ commSpace a := by
        refine ⟨U.sub_mem (hU a (Subgroup.subset_closure ha) u hu) hu, ?_⟩
        exact ⟨u, by simp⟩
      have hne : U ⊓ commSpace a ≠ ⊥ := by
        intro h0
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hx
        exact hau hx
      have hrank : Module.finrank F (commSpace a) = 1 := ha.2.1
      have hx0 : (⟨a u - u, hx.2⟩ : commSpace a) ≠ 0 := by
        intro h0
        apply hau
        have := congrArg Subtype.val h0
        simpa [sub_eq_zero] using this
      have hall := (finrank_eq_one_iff_of_nonzero' _ hx0).mp hrank
      intro y hy
      obtain ⟨c, hc⟩ := hall ⟨y, hy⟩
      have hcy : c • (a u - u) = y := congrArg Subtype.val hc
      rw [← hcy]
      exact U.smul_mem c hx.1
    intro b hb v
    obtain ⟨g, hg, rfl⟩ := htrans a ha b hb
    have hw : a (g⁻¹ v) - g⁻¹ v ∈ commSpace a := ⟨g⁻¹ v, by simp⟩
    have hgU := hU g hg _ (hVa hw)
    simp only [map_sub, mul_inv_apply] at hgU
    simpa [LinearEquiv.mul_apply] using hgU
  have hGU : ∀ g ∈ transvGen G₀, ∀ v, g v - v ∈ U := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem b hb => exact hcentre b hb
    | one => intro v; simp
    | mul x y hx hy ihx ihy =>
      intro v
      have h1 := ihx (y v)
      have h2 := ihy v
      have : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [this]
      exact U.add_mem h1 h2
    | inv x hx ihx =>
      intro v
      have h1 := ihx (x⁻¹ v)
      rw [mul_inv_apply] at h1
      have : x⁻¹ v - v = -(v - x⁻¹ v) := by abel
      rw [this]
      exact U.neg_mem h1
  set S := Submodule.span F {x | ∃ g ∈ transvGen G₀, ∃ v, x = g v - v} with hS
  have hSU : S ≤ U := by
    rw [Submodule.span_le]
    rintro x ⟨g, hg, v, rfl⟩
    exact hGU g hg v
  rcases hirr S (fun g hg w hw => commutator_span_invariant G₀ g hg w hw) with hbot | htop
  · exfalso
    apply transv_ne_one d₀ hd₀.2
    apply LinearEquiv.ext
    intro v
    have hv : d₀ v - v ∈ S := by
      rw [hS]
      exact Submodule.subset_span ⟨d₀, Subgroup.subset_closure hd₀, v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
    exact hv
  · exact eq_top_iff.mpr (htop ▸ hSU)

theorem transvSet_transvGen (G₀ : Subgroup (V ≃ₗ[F] V)) :
    transvSet (transvGen G₀) = transvSet G₀ := by
  ext d
  exact ⟨fun hd => ⟨transvGen_le G₀ hd.1, hd.2⟩, fun hd => ⟨Subgroup.subset_closure hd, hd.2⟩⟩

theorem advGraph_transvGen_connected_iff (G₀ : Subgroup (V ≃ₗ[F] V)) :
    (advGraph (transvGen G₀)).Connected ↔ (advGraph G₀).Connected := by
  have h := transvSet_transvGen G₀
  let e : ↥(transvSet (transvGen G₀)) ≃ ↥(transvSet G₀) :=
    Equiv.subtypeEquivRight (fun x => by rw [h])
  let φ : advGraph (transvGen G₀) ≃g advGraph G₀ :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        simp only [advGraph, SimpleGraph.fromRel_adj]
        exact and_congr e.injective.ne_iff Iff.rfl }
  exact φ.connected_iff

end CFSG.Quasithin.SimsG4
