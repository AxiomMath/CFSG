module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrUnit
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFixAlgC
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFixAlgD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def qtwoDCoordAct {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m)
    (r : MulAut ↥Bs) (v : DVec m) : DVec m :=
  β (Additive.ofMul (r (Additive.toMul (β.symm v))))

theorem qtwoDCoordAct_mul {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m)
    (r r' : MulAut ↥Bs) (v : DVec m) :
    qtwoDCoordAct β (r * r') v = qtwoDCoordAct β r (qtwoDCoordAct β r' v) := by
  simp [qtwoDCoordAct, MulAut.mul_apply]

theorem qtwoDCoordAct_one {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m) (v : DVec m) :
    qtwoDCoordAct β 1 v = v := by
  simp [qtwoDCoordAct]

theorem qtwoDCoordAct_injective {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m)
    {r r' : MulAut ↥Bs} (h : ∀ v, qtwoDCoordAct β r v = qtwoDCoordAct β r' v) : r = r' := by
  ext a
  have := h (β (Additive.ofMul a))
  simp only [qtwoDCoordAct, AddEquiv.symm_apply_apply, toMul_ofMul] at this
  exact congrArg (fun z : ↥Bs => (z : G)) (Additive.ofMul.injective (β.injective this))

theorem qtwoDNbr_coxRefl_dTau {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) {m : ℕ} (hm : 2 ≤ m) (e' : Fin m ≃ ι)
    (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥A) : MulAut ↥Bs)) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s))) :
    ∀ r ∈ ggCoxRefl M e, ∃ (s : Bool) (c d : Fin m), c ≠ d ∧
      ∀ v, qtwoDCoordAct β r v = dTau m s c d v := by
  classical
  let S : Set (DVec m ≃ₗ[ZMod 3] DVec m) :=
    {x | ∃ (ε : Bool) (a b : Fin m), a ≠ b ∧ x = dTau m ε a b}
  have hsimple : ∀ j : ι, ∃ (s : Bool) (c d : Fin m), c ≠ d ∧
      ∀ v, qtwoDCoordAct β ((e (M.simple j) : ↥A) : MulAut ↥Bs) v = dTau m s c d v := by
    intro j
    obtain ⟨t, rfl⟩ := e'.surjective j
    refine ⟨decide (t.val + 1 = m), OrthTorus.simpleLo t, OrthTorus.simpleHi t,
      OrthTorus.simpleLo_ne_simpleHi hm t, fun v => ?_⟩
    have h := hβ t (Additive.toMul (β.symm v))
    simpa [qtwoDCoordAct] using h
  have hW : ∀ w : M.Group, ∃ u ∈ Subgroup.closure S,
      ∀ v, qtwoDCoordAct β ((e w : ↥A) : MulAut ↥Bs) v = u v := by
    intro w
    have hw : w ∈ Subgroup.closure (Set.range M.simple) := by
      rw [show Set.range M.simple = Set.range M.toCoxeterSystem.simple from rfl,
        M.toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨s, c, d, hcd, h⟩ := hsimple j
      exact ⟨dTau m s c d, Subgroup.subset_closure ⟨s, c, d, hcd, rfl⟩, h⟩
    | one =>
      exact ⟨1, Subgroup.one_mem _, fun v => by simp [qtwoDCoordAct_one]⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨u, hu, hux⟩ := ihx
      obtain ⟨u', hu', huy⟩ := ihy
      refine ⟨u * u', Subgroup.mul_mem _ hu hu', fun v => ?_⟩
      have : ((e (x * y) : ↥A) : MulAut ↥Bs) =
          ((e x : ↥A) : MulAut ↥Bs) * ((e y : ↥A) : MulAut ↥Bs) := by
        rw [map_mul]
        rfl
      rw [this, qtwoDCoordAct_mul, huy, hux]
      rfl
    | inv x hx ihx =>
      obtain ⟨u, hu, hux⟩ := ihx
      refine ⟨u⁻¹, Subgroup.inv_mem _ hu, fun v => ?_⟩
      have h1 : ((e x⁻¹ : ↥A) : MulAut ↥Bs) = (((e x : ↥A) : MulAut ↥Bs))⁻¹ := by
        rw [map_inv]
        rfl
      have h2 : u (qtwoDCoordAct β ((e x⁻¹ : ↥A) : MulAut ↥Bs) v) = v := by
        rw [← hux, ← qtwoDCoordAct_mul, h1, mul_inv_cancel, qtwoDCoordAct_one]
      rw [LinearEquiv.coe_inv]
      exact (u.symm_apply_eq.mpr h2.symm).symm
  rintro r ⟨w, i, rfl⟩
  obtain ⟨u, hu, huw⟩ := hW w
  obtain ⟨s, c, d, hcd, hsi⟩ := hsimple i
  obtain ⟨s', a', b', hab', h⟩ := dTau_conj_mem_closure m hu s hcd
  refine ⟨s', a', b', hab', fun v => ?_⟩
  have h1 : ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) =
      ((e w : ↥A) : MulAut ↥Bs) * ((e (M.simple i) : ↥A) : MulAut ↥Bs) *
        (((e w : ↥A) : MulAut ↥Bs))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have h2 : ∀ v, qtwoDCoordAct β ((((e w : ↥A) : MulAut ↥Bs))⁻¹) v = u⁻¹ v := by
    intro v
    have h3 : u (qtwoDCoordAct β ((((e w : ↥A) : MulAut ↥Bs))⁻¹) v) = v := by
      rw [← huw, ← qtwoDCoordAct_mul, mul_inv_cancel, qtwoDCoordAct_one]
    rw [LinearEquiv.coe_inv]
    exact (u.symm_apply_eq.mpr h3.symm).symm
  rw [h1, qtwoDCoordAct_mul, qtwoDCoordAct_mul, h2, hsi, huw, ← h]
  rfl

variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
  {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}

theorem qtwoDNbr_fixBound (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} (hm : 2 ≤ m)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (e' : Fin m ≃ ι) (β : Additive ↥Bs ≃+ DVec m)
    (hβ : ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
        dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    {X : Subgroup G} (hA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    QTwoDFixBound Bs X m := by
  classical
  intro n ε hn5 hrefl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hdT : ∀ a b : Fin (k + 1), a ≠ b → ∃ (s : Bool) (c d : Fin m), c ≠ d ∧
      ∀ v, qtwoDCoordAct β ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) v =
        dTau m s c d v := by
    intro a b hab
    have hmem : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈
        ggAutomizerJoin L Bs 𝒦 := hA (ε (Equiv.swap a b)).2
    have hcox := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 hmem
      (hrefl a b hab)
    exact qtwoDNbr_coxRefl_dTau e hm e' β hβ _ hcox
  let act : Equiv.Perm (Fin (k + 1)) → DVec m → DVec m := fun σ v =>
    qtwoDCoordAct β ((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) v
  have hmul : ∀ σ τ v, act (σ * τ) v = act σ (act τ v) := by
    intro σ τ v
    change qtwoDCoordAct β ((ε (σ * τ) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) v = _
    rw [map_mul]
    exact qtwoDCoordAct_mul β _ _ v
  have hfaith : ∀ σ τ, (∀ v, act σ v = act τ v) → σ = τ := by
    intro σ τ h
    exact ε.injective (Subtype.ext (qtwoDCoordAct_injective β h))
  have hk : 4 ≤ k := by omega
  obtain ⟨hkm, hcard⟩ := qtwoDNbr_fix_card_le_of_act hk act hmul hfaith (fun j => by
    obtain ⟨s, c, d, hcd, h⟩ := hdT (Fin.castSucc j) (Fin.succ j)
      (ne_of_lt (Fin.castSucc_lt_succ (i := j)))
    exact ⟨s, c, d, hcd, h⟩)
  refine ⟨by omega, ?_⟩
  have hinj : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤
      Nat.card {v : DVec m // ∀ σ, act σ v = v} := by
    refine Nat.card_le_card_of_injective
      (fun b : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) =>
        (⟨β (Additive.ofMul ⟨(b : G), b.2.1⟩), fun σ => ?_⟩ :
          {v : DVec m // ∀ σ, act σ v = v})) ?_
    · have hφ : ((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggAutomizer X Bs := (ε σ).2
      obtain ⟨g, hgX, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
      have hfix : ((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ⟨(b : G), b.2.1⟩ =
          ⟨(b : G), b.2.1⟩ := by
        refine Subtype.ext ?_
        rw [hg ⟨(b : G), b.2.1⟩]
        have hcomm : g * (b : G) = (b : G) * g := Subgroup.mem_centralizer_iff.mp b.2.2 g hgX
        calc g * (b : G) * g⁻¹ = (b : G) * g * g⁻¹ := by rw [hcomm]
          _ = b := by group
      change qtwoDCoordAct β ((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
        (β (Additive.ofMul ⟨(b : G), b.2.1⟩)) = β (Additive.ofMul ⟨(b : G), b.2.1⟩)
      simp [qtwoDCoordAct, hfix]
    · intro b b' hbb'
      have h1 := congrArg Subtype.val hbb'
      have h2 : (⟨(b : G), b.2.1⟩ : ↥Bs) = ⟨(b' : G), b'.2.1⟩ :=
        Additive.ofMul.injective (β.injective h1)
      exact Subtype.ext (congrArg (fun z : ↥Bs => (z : G)) h2)
  have hexp : m - (k + 1) + 1 = m - k := by omega
  rw [hexp]
  exact hinj.trans hcard

end CFSG.StandardType.QTwo

end
