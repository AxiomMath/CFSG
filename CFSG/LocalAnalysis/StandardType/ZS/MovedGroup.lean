module

public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem exists_movedSpace_restrictHom_le_span {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : X} (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) :
    ∃ a : HardMathSupport.Kantor79.commutatorSpace X,
      HardMathSupport.Kantor79.movedSpace
        (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
          (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) t) ≤
        Submodule.span (ZMod p) {a} := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hfint : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.movedSpace (t : U ≃ₗ[ZMod p] U)) = 1 := ht.2
  have hne : HardMathSupport.Kantor79.movedSpace (t : U ≃ₗ[ZMod p] U) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfint
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : HardMathSupport.Kantor79.movedSpace (t : U ≃ₗ[ZMod p] U) =
      Submodule.span (ZMod p) {a} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfint ha ha0
  have haV : a ∈ V := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace t.2 ha
  refine ⟨⟨a, haV⟩, ?_⟩
  intro w hw
  obtain ⟨v, hv⟩ := hw
  have hwU : (w : U) ∈ HardMathSupport.Kantor79.movedSpace (t : U ≃ₗ[ZMod p] U) := by
    refine ⟨(v : U), ?_⟩
    have h := congrArg (fun z : V => (z : U)) hv
    simp only [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap] at h
    exact h
  rw [hspan] at hwU
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwU
  exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc⟩

theorem isRefl_restrictHom_or_eq_one {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : X} (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) :
    IsRefl p (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) t) ∨
      restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) t = 1 := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  change IsRefl p (φ t) ∨ φ t = 1
  have hsq : φ t * φ t = 1 := by
    rw [← map_mul, show t * t = 1 from Subtype.ext ht.1, map_one]
  by_cases hone : φ t = 1
  · exact Or.inr hone
  · refine Or.inl ⟨hsq, ?_⟩
    obtain ⟨a, hle⟩ := exists_movedSpace_restrictHom_le_span (X := X) (t := t) ht
    have hne : HardMathSupport.Kantor79.movedSpace (φ t) ≠ ⊥ := by
      intro hbot
      apply hone
      ext v
      have hv : ((φ t : V →ₗ[ZMod p] V) - 1) v ∈
          HardMathSupport.Kantor79.movedSpace (φ t) := ⟨v, rfl⟩
      rw [hbot] at hv
      have hv0 : ((φ t : V →ₗ[ZMod p] V) - 1) v = 0 := by simpa using hv
      simpa [LinearMap.sub_apply, sub_eq_zero] using hv0
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hwa : w ∈ Submodule.span (ZMod p) {a} := hle hw
    rw [Submodule.mem_span_singleton] at hwa
    obtain ⟨c, hc⟩ := hwa
    have hc0 : c ≠ 0 := by
      intro hc0
      exact hw0 (by rw [← hc, hc0, zero_smul])
    have hspanw : HardMathSupport.Kantor79.movedSpace (φ t) = Submodule.span (ZMod p) {w} := by
      refine le_antisymm ?_ ?_
      · intro x hx
        have hxa : x ∈ Submodule.span (ZMod p) {a} := hle hx
        rw [Submodule.mem_span_singleton] at hxa
        obtain ⟨d, hd⟩ := hxa
        exact Submodule.mem_span_singleton.mpr ⟨d * c⁻¹, by
          rw [← hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one, hd]⟩
      · rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ hw
    show Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace (φ t)) = 1
    rw [hspanw, finrank_span_singleton hw0]

theorem card_movedGroup_of_splitSupport {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) : Nat.card (movedGroup X) = Nat.card X := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hker : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro h hh
    have h1 : φ h = 1 := (MonoidHom.mem_ker).mp hh
    apply Subtype.ext
    ext v
    have hv : v ∈ V ⊔ C := by rw [hX.1.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    have ha' : (h : U ≃ₗ[ZMod p] U) a = a := by
      have hc := congrArg (fun e : V ≃ₗ[ZMod p] V => (e ⟨a, ha⟩ : U)) h1
      simpa [φ, restrictHom_apply] using hc
    have hb' : (h : U ≃ₗ[ZMod p] U) b = b := (mem_centralizerSpace.mp hb) h h.2
    rw [ha', hb']
    simp
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker, Subgroup.card_bot, one_mul] at hcard
  have hmg : movedGroup X = φ.range := rfl
  rw [hmg]
  exact hcard

theorem reflGen_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X) :
    ReflGen p (movedGroup X) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  let R : Set X := {t | IsRefl p (t : U ≃ₗ[ZMod p] U)}
  have hmemR : ∀ t : X, IsRefl p (t : U ≃ₗ[ZMod p] U) →
      φ t ∈ Subgroup.closure {g | g ∈ movedGroup X ∧ IsRefl p g} := by
    intro t ht
    rcases isRefl_restrictHom_or_eq_one (X := X) (t := t) ht with hrefl | hone
    · refine Subgroup.subset_closure ⟨?_, hrefl⟩
      exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
    · rw [hone]
      exact Subgroup.one_mem _
  have htop : (⊤ : Subgroup X) = Subgroup.closure R := by
    refine le_antisymm ?_ le_top
    intro x _
    have hxmap : X.subtype x ∈ (Subgroup.closure R).map X.subtype := by
      rw [MonoidHom.map_closure]
      have hSR : X.subtype '' R = {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t} := by
        ext t
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y.2, hy⟩
        · rintro ⟨htX, htR⟩
          exact ⟨⟨t, htX⟩, htR, rfl⟩
      rw [hSR, ← hX]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_map (f := X.subtype)).mp hxmap
    have hyx' : y = x := X.subtype_injective hyx
    rwa [hyx'] at hy
  have hclosure : movedGroup X = Subgroup.closure (φ '' R) := by
    have hmg : movedGroup X = φ.range := rfl
    rw [hmg, ← Subgroup.map_top φ, htop, MonoidHom.map_closure]
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [hclosure]
    rw [Subgroup.closure_le]
    rintro g ⟨t, htR, rfl⟩
    exact hmemR t htR
  · rw [Subgroup.closure_le]
    intro g hg
    exact hg.1

private theorem transvection_extension {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) {x : X}
    {u : HardMathSupport.Kantor79.commutatorSpace X}
    {ψ : Module.Dual (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    (hgv : ∀ w, (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x) w = w + ψ w • u) :
    ∀ v : U, (x : U ≃ₗ[ZMod p] U) v = v + (ψ.comp
      ((HardMathSupport.Kantor79.commutatorSpace X).projectionOnto
        (centralizerSpace X) hs.1)) v • (u : U) := by
  intro v
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let π := V.projectionOnto C hs.1
  let ψ' : Module.Dual (ZMod p) U := ψ.comp π
  change (x : U ≃ₗ[ZMod p] U) v = v + ψ' v • (u : U)
  have hv : v ∈ V ⊔ C := by rw [hs.1.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hxa : (x : U ≃ₗ[ZMod p] U) a = a + ψ ⟨a, ha⟩ • (u : U) := by
    have h := congrArg (fun z : V => (z : U)) (hgv ⟨a, ha⟩)
    simpa [restrictHom_apply] using h
  have hxb : (x : U ≃ₗ[ZMod p] U) b = b := (mem_centralizerSpace.mp hb) x x.2
  have hπ : π (a + b) = ⟨a, ha⟩ := by
    have h1 : π a = ⟨a, ha⟩ := by
      change V.projectionOnto C hs.1 a = ⟨a, ha⟩
      rw [Submodule.projectionOnto_apply_of_mem_left hs.1 ha]
    have h2 : π b = 0 := by
      change V.projectionOnto C hs.1 b = 0
      exact Submodule.projectionOnto_apply_of_mem_right hs.1 hb
    rw [map_add, h1, h2, add_zero]
  have hψ'a : ψ' (a + b) = ψ ⟨a, ha⟩ := by simp [ψ', hπ]
  rw [map_add, hxa, hxb, hψ'a]
  abel

theorem transvectionFree_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) (ht : QTwoLin.TransvectionFree X) :
    QTwoLin.TransvectionFree (movedGroup X) := by
  intro g hg htrans
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  change g ∈ φ.range at hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
  obtain ⟨u, ψ, hu, hψ, hψu, hgv⟩ := htrans
  let π := V.projectionOnto C hs.1
  let ψ' : Module.Dual (ZMod p) U := ψ.comp π
  apply ht (x : U ≃ₗ[ZMod p] U) x.2
  refine ⟨(u : U), ψ', ?_, ?_, ?_, ?_⟩
  · exact fun h => hu (Subtype.ext h)
  · intro h0
    apply hψ
    ext w
    have h1 := congrArg (fun f : Module.Dual (ZMod p) U => f (w : U)) h0
    have h2 : π (w : U) = w := by
      change V.projectionOnto C hs.1 (w : U) = w
      rw [Submodule.projectionOnto_apply_of_mem_left hs.1 w.2]
    simpa [ψ', h2] using h1
  · have hπu : π (u : U) = u := by
      change V.projectionOnto C hs.1 (u : U) = u
      rw [Submodule.projectionOnto_apply_of_mem_left hs.1 u.2]
    have hψu' : ψ' (u : U) = ψ u := by simp [ψ', hπu]
    rw [hψu', hψu]
  · exact transvection_extension hs hgv

end CFSG.StandardType.ZS
