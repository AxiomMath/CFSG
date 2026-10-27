module

public import CFSG.CGT.PushingUpLit.SolKNA.SzRepAux
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.CGT.PushingUpLit.SolKNA

variable {G : Type*} [Group G] {W₀ : Type*} [AddCommGroup W₀] [Module (ZMod 2) W₀]

theorem exists_equivariant_of_cocycle (act : G →* AddMonoid.End W₀)
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (θ₁ : W₀ →+ V) (hθ₁ : Function.Injective θ₁) (hθ₁eq : ∀ g v, θ₁ (act g v) = ρ g (θ₁ v))
    (s : W₀ →+ V) (hs : ∀ g v, ρ g (s v) - s (act g v) ∈ θ₁.range) :
    ∃ θ : W₀ →+ V, (∀ g v, θ (act g v) = ρ g (θ v)) ∧ ∀ v, θ v - s v ∈ θ₁.range := by
  let hbij : Function.Bijective θ₁.rangeRestrict :=
    ⟨fun x y h => hθ₁ (by simpa using congrArg Subtype.val h),
      fun y => by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x, Subtype.ext hx⟩⟩
  let e : W₀ ≃+ θ₁.range := AddEquiv.ofBijective θ₁.rangeRestrict hbij
  let F : G → W₀ →+ θ₁.range := fun g =>
    ((ρ g).toAddMonoidHom.comp s - s.comp (act g)).codRestrict θ₁.range (fun v => hs g v)
  let Y : G → AddMonoid.End W₀ := fun g => (e.symm : θ₁.range →+ W₀).comp (F g)
  have hY : ∀ g v, θ₁ (Y g v) = ρ g (s v) - s (act g v) :=
    fun g v => congrArg Subtype.val (e.apply_symm_apply (F g v))
  have hcoc : ∀ g h, Y (g * h) = act g * Y h + Y g * act h := by
    intro g h
    ext v
    apply hθ₁
    rw [hY (g * h) v]
    change ρ (g * h) (s v) - s (act (g * h) v) =
      θ₁ (act g (Y h v) + Y g (act h v))
    rw [map_mul, map_mul]
    change (ρ g * ρ h) (s v) - s (act g (act h v)) = _
    rw [Module.End.mul_apply, map_add, hθ₁eq, hY h v, hY g (act h v), map_sub]
    abel
  obtain ⟨X, hX⟩ := hcob Y hcoc
  let X' : W₀ →+ W₀ := X
  let θX : W₀ →+ V := θ₁.comp X'
  refine ⟨s - θX, ?_, ?_⟩
  · intro g v
    have hρ : ρ g (s v) = s (act g v) + θ₁ (Y g v) := by
      rw [hY g v]
      abel
    have hX' : Y g v = act g (X' v) - X' (act g v) :=
      congrArg (fun f : AddMonoid.End W₀ => f v) (hX g)
    have hθX : θ₁ (Y g v) = θ₁ (act g (X' v)) - θ₁ (X' (act g v)) := by
      rw [hX', map_sub]
    show s (act g v) - θX (act g v) = ρ g (s v - θX v)
    rw [map_sub]
    change s (act g v) - θX (act g v) = ρ g (s v) - ρ g (θX v)
    rw [show θX (act g v) = θ₁ (X' (act g v)) from rfl,
      show θX v = θ₁ (X' v) from rfl,
      ← hθ₁eq g (X' v), hρ, hθX]
    abel
  · intro v
    exact ⟨-X' v, by simp [θX]⟩

section MinimalInvariant

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem exists_minimal_invariant [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod 2) G V) :
    ∃ U : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ U, ρ g w ∈ U) ∧ U ≠ ⊥ ∧
      ∀ U' : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ U', ρ g w ∈ U') → U' ≤ U →
        U' = ⊥ ∨ U' = U := by
  classical
  have hfin : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective
  let S : Set (Submodule (ZMod 2) V) := {U | (∀ g, ∀ w ∈ U, ρ g w ∈ U) ∧ U ≠ ⊥}
  have hne : S.Nonempty := ⟨⊤, fun g w _ => Submodule.mem_top, top_ne_bot⟩
  obtain ⟨U, hUS, hmin⟩ := Set.Finite.exists_minimalFor id S (Set.toFinite S) hne
  refine ⟨U, hUS.1, hUS.2, fun U' hU' hle => ?_⟩
  by_cases hbot : U' = ⊥
  · exact Or.inl hbot
  · exact Or.inr (le_antisymm hle (hmin ⟨hU', hbot⟩ hle))

private theorem irreducible_of_minimal (ρ : Representation (ZMod 2) G V)
    {U : Submodule (ZMod 2) V} (hUinv : ∀ g, ∀ w ∈ U, ρ g w ∈ U)
    (hUmin : ∀ U' : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ U', ρ g w ∈ U') → U' ≤ U →
      U' = ⊥ ∨ U' = U) :
    ∀ W : Submodule (ZMod 2) U, (∀ g, ∀ w ∈ W, restrictRep ρ U hUinv g w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hmapinv : ∀ g, ∀ y ∈ Submodule.map U.subtype W,
      ρ g y ∈ Submodule.map U.subtype W := by
    intro g y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact Submodule.mem_map.mpr ⟨restrictRep ρ U hUinv g w, hW g w hw,
      restrictRep_apply ρ U hUinv g w⟩
  rcases hUmin (Submodule.map U.subtype W) hmapinv (Submodule.map_subtype_le U W) with h | h
  · left
    apply le_antisymm _ bot_le
    intro w hw
    have : (w : V) ∈ Submodule.map U.subtype W := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · right
    apply eq_top_iff.mpr
    intro w _
    have hmem : (w : V) ∈ Submodule.map U.subtype W := by
      rw [h]
      exact w.2
    obtain ⟨w', hw', hw'eq⟩ := Submodule.mem_map.mp hmem
    have hww : w' = w := Subtype.ext hw'eq
    simpa [hww] using hw'

end MinimalInvariant

section LatticeBookkeeping

variable {V Q : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup Q] [Module (ZMod 2) Q]

private theorem sum_toRight_eq_zero
    {ι : Type*} {W : ι → Submodule (ZMod 2) Q} {C : ι → Submodule (ZMod 2) V}
    {f : V →ₗ[ZMod 2] Q}
    (hW : iSupIndep W) (hmap : ∀ i, Submodule.map f (C i) = W i)
    (hdisj : ∀ i, C i ⊓ LinearMap.ker f = ⊥)
    {t : Finset (Unit ⊕ ι)} {v : Unit ⊕ ι → V}
    (hv : ∀ x ∈ t, v x ∈ Sum.elim (fun _ => LinearMap.ker f) C x)
    (hsum : ∑ x ∈ t, v x = 0) :
    (∑ i ∈ t.toRight, v (Sum.inr i) = 0) ∧
      ∀ i ∈ t.toRight, f (v (Sum.inr i)) = 0 := by
  have hfsum : ∑ x ∈ t, f (v x) = 0 := by
    rw [← map_sum, hsum, map_zero]
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight] at hfsum
  have hleft : ∑ u ∈ t.toLeft, f (v (Sum.inl u)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hmem : v (Sum.inl u) ∈ LinearMap.ker f := by
      simpa using hv (Sum.inl u) (by simpa using hu)
    simpa using hmem
  have hright : ∑ i ∈ t.toRight, f (v (Sum.inr i)) = 0 := by
    rw [hleft, zero_add] at hfsum
    exact hfsum
  have hwmem : ∀ i ∈ t.toRight, f (v (Sum.inr i)) ∈ W i := by
    intro i hi
    have hmemC : v (Sum.inr i) ∈ C i := by
      simpa using hv (Sum.inr i) (by simpa using hi)
    have hmem : f (v (Sum.inr i)) ∈ Submodule.map f (C i) :=
      Submodule.mem_map.mpr ⟨_, hmemC, rfl⟩
    simpa [hmap i] using hmem
  have hwzero : ∀ i ∈ t.toRight, f (v (Sum.inr i)) = 0 := by
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hW
    exact hW t.toRight (fun i => f (v (Sum.inr i))) hwmem hright
  have hrightV : ∑ i ∈ t.toRight, v (Sum.inr i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hmemC : v (Sum.inr i) ∈ C i := by
      simpa using hv (Sum.inr i) (by simpa using hi)
    have hmemU : v (Sum.inr i) ∈ LinearMap.ker f := hwzero i hi
    have hmem : v (Sum.inr i) ∈ C i ⊓ LinearMap.ker f := ⟨hmemC, hmemU⟩
    rw [hdisj i] at hmem
    exact hmem
  exact ⟨hrightV, hwzero⟩

private theorem iSupIndep_sum_unit_ker {ι : Type*} {W : ι → Submodule (ZMod 2) Q}
    {C : ι → Submodule (ZMod 2) V} {f : V →ₗ[ZMod 2] Q}
    (hW : iSupIndep W) (hmap : ∀ i, Submodule.map f (C i) = W i)
    (hdisj : ∀ i, C i ⊓ LinearMap.ker f = ⊥) :
    iSupIndep (fun o : Unit ⊕ ι => Sum.elim (fun _ => LinearMap.ker f) C o) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro t v hv hsum
  obtain ⟨hrightV, hwzero⟩ := sum_toRight_eq_zero hW hmap hdisj hv hsum
  intro i hi
  cases i with
  | inl u =>
      have hu : u ∈ t.toLeft := by simpa using hi
      have hsplit : ∑ x ∈ t, v x =
          ∑ u' ∈ t.toLeft, v (Sum.inl u') + ∑ i ∈ t.toRight, v (Sum.inr i) :=
        Finset.sum_sum_eq_sum_toLeft_add_sum_toRight t v
      rw [hsplit, hrightV, add_zero] at hsum
      have hsub : t.toLeft ⊆ ({u} : Finset Unit) := by
        intro u' _
        exact Finset.mem_singleton.mpr (Subsingleton.elim u' u)
      have hsingle : ∑ u' ∈ t.toLeft, v (Sum.inl u') = v (Sum.inl u) := by
        rw [Finset.sum_subset hsub]
        · simp
        · intro x hx hxnot
          exact absurd (Finset.mem_singleton.mp hx ▸ hu) hxnot
      rw [hsingle] at hsum
      exact hsum
  | inr i =>
      have hmemC : v (Sum.inr i) ∈ C i := by
        simpa using hv (Sum.inr i) hi
      have hmemU : v (Sum.inr i) ∈ LinearMap.ker f := hwzero i (by simpa using hi)
      have hmem : v (Sum.inr i) ∈ C i ⊓ LinearMap.ker f := ⟨hmemC, hmemU⟩
      rw [hdisj i] at hmem
      exact hmem

private theorem sup_ker_sup_iSup_eq_top {ι : Type*} {W : ι → Submodule (ZMod 2) Q}
    {C : ι → Submodule (ZMod 2) V} {f : V →ₗ[ZMod 2] Q}
    (hW : ⨆ i, W i = ⊤) (hmap : ∀ i, Submodule.map f (C i) = W i) :
    LinearMap.ker f ⊔ ⨆ i, C i = ⊤ := by
  let S : Submodule (ZMod 2) V := LinearMap.ker f ⊔ ⨆ i, C i
  have hmem : ∀ i, C i ≤ S := fun i => le_sup_of_le_right (le_iSup C i)
  have hker : LinearMap.ker f ≤ S := le_sup_left
  have key : ∀ y ∈ (⨆ i, W i), ∃ x ∈ S, f x = y := by
    intro y hy
    refine Submodule.iSup_induction W hy (motive := fun z => ∃ x ∈ S, f x = z) ?_ ?_ ?_
    · intro i z hz
      rw [← hmap i] at hz
      obtain ⟨c, hc, hcz⟩ := hz
      exact ⟨c, hmem i hc, hcz⟩
    · exact ⟨0, S.zero_mem, map_zero f⟩
    · intro x y hx hy
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      exact ⟨a + b, S.add_mem ha hb, by rw [map_add, hax, hby]⟩
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨y, hyS, hfy⟩ := key (f x) (by rw [hW]; exact Submodule.mem_top)
  have hxmem : x - y ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hfy, sub_self]
  have hxeq : x = (x - y) + y := by abel
  rw [hxeq]
  exact S.add_mem (hker hxmem) hyS

end LatticeBookkeeping

private theorem exists_equivariant_lift
    (act : G →* AddMonoid.End W₀)
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g)
    {V Q : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [AddCommGroup Q] [Module (ZMod 2) Q]
    (ρ : Representation (ZMod 2) G V) (U : Submodule (ZMod 2) V)
    (f : V →ₗ[ZMod 2] Q) (hker : LinearMap.ker f = U)
    (ρQ : Representation (ZMod 2) G Q)
    (hquot : ∀ (g : G) (x : V), ρQ g (f x) = f (ρ g x))
    (θ₁ : W₀ →+ V) (hθ₁inj : Function.Injective θ₁)
    (hθ₁eq : ∀ g v, θ₁ (act g v) = ρ g (θ₁ v))
    (hθ₁range : θ₁.range = U.toAddSubgroup)
    (θ' : W₀ →+ Q) (hθ'eq : ∀ g v, θ' (act g v) = ρQ g (θ' v))
    (l : Q →ₗ[ZMod 2] V) (hl : ∀ x : Q, f (l x) = x) :
    ∃ θ : W₀ →+ V, (∀ g v, θ (act g v) = ρ g (θ v)) ∧
      (∀ v, f (θ v) = θ' v) ∧
      ∀ v, θ v - (l.toAddMonoidHom.comp θ') v ∈ θ₁.range := by
  let s : W₀ →+ V := l.toAddMonoidHom.comp θ'
  have hs : ∀ v, f (s v) = θ' v := fun v => hl (θ' v)
  have hs_mem : ∀ g v, ρ g (s v) - s (act g v) ∈ θ₁.range := by
    intro g v
    rw [hθ₁range]
    have hzero : f (ρ g (s v) - s (act g v)) = 0 := by
      rw [map_sub, ← hquot, hs, ← hθ'eq, hs, sub_self]
    have hmem : ρ g (s v) - s (act g v) ∈ LinearMap.ker f := hzero
    rwa [hker] at hmem
  obtain ⟨θ, hθeq, hθdiff⟩ :=
    exists_equivariant_of_cocycle act hcob ρ θ₁ hθ₁inj hθ₁eq s hs_mem
  have hcomp : ∀ v, f (θ v) = θ' v := by
    intro v
    have hmem := hθdiff v
    rw [hθ₁range] at hmem
    have hsub : f (θ v) - f (s v) = 0 := by
      rw [← map_sub]
      have hmemker : θ v - s v ∈ LinearMap.ker f := by
        rw [hker]
        exact hmem
      exact hmemker
    have heq : f (θ v) = f (s v) := sub_eq_zero.mp hsub
    rw [heq, hs]
  exact ⟨θ, hθeq, hcomp, hθdiff⟩

private theorem injective_and_disjoint
    {V Q : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [AddCommGroup Q] [Module (ZMod 2) Q]
    (U : Submodule (ZMod 2) V) (f : V →ₗ[ZMod 2] Q) (hker : LinearMap.ker f = U)
    (θ₁ : W₀ →+ V) (hθ₁range : θ₁.range = U.toAddSubgroup)
    (θ' : W₀ →+ Q) (hθ'inj : Function.Injective θ')
    (s : W₀ →+ V) (hs : ∀ v, f (s v) = θ' v)
    (θ : W₀ →+ V) (hcomp : ∀ v, f (θ v) = θ' v)
    (hθdiff : ∀ v, θ v - s v ∈ θ₁.range) :
    Function.Injective θ ∧ LinearMap.range (θ.toZModLinearMap 2) ⊓ U = ⊥ := by
  constructor
  · intro x y hxy
    have h0 : θ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hmem := hθdiff (x - y)
    rw [h0, zero_sub, hθ₁range] at hmem
    have hmemU : s (x - y) ∈ U := (Submodule.neg_mem_iff (p := U)).mp hmem
    have hq : θ' (x - y) = 0 := by
      rw [← hs (x - y)]
      have hmemker : s (x - y) ∈ LinearMap.ker f := by
        rw [hker]
        exact hmemU
      exact hmemker
    have hq0 : θ' (x - y) = θ' 0 := by rw [map_zero]; exact hq
    have hzero : x - y = 0 := hθ'inj hq0
    exact sub_eq_zero.mp hzero
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxU⟩ := hx
    rw [Submodule.mem_bot]
    obtain ⟨v, rfl⟩ := hxC
    have hq : θ' v = 0 := by
      rw [← hcomp v]
      have hmemker : θ v ∈ LinearMap.ker f := by
        rw [hker]
        exact hxU
      exact hmemker
    have hv : v = 0 := hθ'inj (by rw [map_zero]; exact hq)
    rw [hv, map_zero]

private theorem lift_map
    (act : G →* AddMonoid.End W₀)
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g)
    {V Q : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [AddCommGroup Q] [Module (ZMod 2) Q]
    (ρ : Representation (ZMod 2) G V) (U : Submodule (ZMod 2) V)
    (f : V →ₗ[ZMod 2] Q) (hker : LinearMap.ker f = U)
    (ρQ : Representation (ZMod 2) G Q)
    (hquot : ∀ (g : G) (x : V), ρQ g (f x) = f (ρ g x))
    (θ₁ : W₀ →+ V) (hθ₁inj : Function.Injective θ₁)
    (hθ₁eq : ∀ g v, θ₁ (act g v) = ρ g (θ₁ v))
    (hθ₁range : θ₁.range = U.toAddSubgroup)
    (θ' : W₀ →+ Q) (hθ'inj : Function.Injective θ')
    (hθ'eq : ∀ g v, θ' (act g v) = ρQ g (θ' v))
    (l : Q →ₗ[ZMod 2] V) (hl : ∀ x : Q, f (l x) = x) :
    ∃ θ : W₀ →+ V, Function.Injective θ ∧ (∀ g v, θ (act g v) = ρ g (θ v)) ∧
      (∀ v, f (θ v) = θ' v) ∧ LinearMap.range (θ.toZModLinearMap 2) ⊓ U = ⊥ := by
  obtain ⟨θ, hθeq, hcomp, hθdiff⟩ :=
    exists_equivariant_lift act hcob ρ U f hker ρQ hquot θ₁ hθ₁inj hθ₁eq hθ₁range
      θ' hθ'eq l hl
  obtain ⟨hθinj, hdisj⟩ :=
    injective_and_disjoint U f hker θ₁ hθ₁range θ' hθ'inj (l.toAddMonoidHom.comp θ')
      (fun v => hl (θ' v)) θ hcomp hθdiff
  exact ⟨θ, hθinj, hθeq, hcomp, hdisj⟩

private theorem supIndep_insert_ker
    {V Q : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [AddCommGroup Q] [Module (ZMod 2) Q]
    {f : V →ₗ[ZMod 2] Q} {U : Submodule (ZMod 2) V} (hker : LinearMap.ker f = U)
    {sq : Finset (Submodule (ZMod 2) Q)} (hsqInd : sq.SupIndep id)
    (hsqSup : sq.sup id = ⊤) {C : ↥sq → Submodule (ZMod 2) V}
    (hmapC : ∀ i, Submodule.map f (C i) = (i.1 : Submodule (ZMod 2) Q))
    (hdisjC : ∀ i, C i ⊓ U = ⊥) :
    (insert U (sq.attach.image C)).SupIndep id ∧
      (insert U (sq.attach.image C)).sup id = ⊤ := by
  let p : Unit ⊕ ↥sq → Submodule (ZMod 2) V := Sum.elim (fun _ => U) C
  have hW_ind : iSupIndep (fun i : ↥sq => (i.1 : Submodule (ZMod 2) Q)) := by
    simpa using hsqInd.independent
  have hWtop : (⨆ i : ↥sq, (i.1 : Submodule (ZMod 2) Q)) = ⊤ := by
    rw [iSup_subtype, ← Finset.sup_eq_iSup]
    exact hsqSup
  have hsupTop : U ⊔ ⨆ i : ↥sq, C i = ⊤ := by
    have h := sup_ker_sup_iSup_eq_top (W := fun i : ↥sq =>
        (i.1 : Submodule (ZMod 2) Q)) (C := C) (f := f) hWtop hmapC
    rwa [hker] at h
  have hindTop : iSupIndep p := by
    have h := iSupIndep_sum_unit_ker (W := fun i : ↥sq =>
        (i.1 : Submodule (ZMod 2) Q)) (C := C) (f := f) hW_ind hmapC
      (fun i => by
        rw [hker]
        exact hdisjC i)
    rwa [hker] at h
  have himage : (Finset.univ.image p) = insert U (sq.attach.image C) := by
    ext W
    simp [p, Finset.mem_image, Finset.mem_insert, eq_comm]
  constructor
  · rw [← himage]
    exact Finset.SupIndep.image (f := id) (g := p) hindTop.sup_indep_univ
  · rw [← himage, Finset.sup_image, Finset.sup_eq_iSup, iSup_sum]
    simpa [p] using hsupTop

private theorem lift_family
    (act : G →* AddMonoid.End W₀)
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g)
    {V Q : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [AddCommGroup Q] [Module (ZMod 2) Q]
    (ρ : Representation (ZMod 2) G V) (U : Submodule (ZMod 2) V)
    (f : V →ₗ[ZMod 2] Q) (hker : LinearMap.ker f = U) (hf : Function.Surjective f)
    (ρQ : Representation (ZMod 2) G Q)
    (hquot : ∀ (g : G) (x : V), ρQ g (f x) = f (ρ g x))
    (θ₁ : W₀ →+ V) (hθ₁inj : Function.Injective θ₁)
    (hθ₁eq : ∀ g v, θ₁ (act g v) = ρ g (θ₁ v))
    (hθ₁range : θ₁.range = U.toAddSubgroup)
    (sq : Finset (Submodule (ZMod 2) Q)) (hsqInd : sq.SupIndep id)
    (hsqSup : sq.sup id = ⊤)
    (hsqMem : ∀ W ∈ sq, ∃ θ : W₀ →+ Q, Function.Injective θ ∧
      θ.range = W.toAddSubgroup ∧ ∀ g v, θ (act g v) = ρQ g (θ v)) :
    ∃ (C : ↥sq → Submodule (ZMod 2) V) (θi : ↥sq → W₀ →+ V),
      (∀ i, Function.Injective (θi i)) ∧
      (∀ i, (θi i).range = (C i).toAddSubgroup) ∧
      (∀ i g v, θi i (act g v) = ρ g (θi i v)) ∧
      (∀ i, Submodule.map f (C i) = (i.1 : Submodule (ZMod 2) Q)) ∧
      (∀ i, C i ⊓ U = ⊥) := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective f
    (LinearMap.range_eq_top.mpr hf)
  have hl_apply : ∀ x : Q, f (l x) = x := by
    intro x
    simpa using LinearMap.congr_fun hl x
  let θ' : ↥sq → W₀ →+ Q := fun i => Classical.choose (hsqMem i.1 i.2)
  have hθ'inj : ∀ i, Function.Injective (θ' i) :=
    fun i => (Classical.choose_spec (hsqMem i.1 i.2)).1
  have hθ'range : ∀ i, (θ' i).range = (i.1).toAddSubgroup :=
    fun i => (Classical.choose_spec (hsqMem i.1 i.2)).2.1
  have hθ'eq : ∀ i g v, θ' i (act g v) = ρQ g (θ' i v) :=
    fun i => (Classical.choose_spec (hsqMem i.1 i.2)).2.2
  have hθi : ∀ i : ↥sq, ∃ θ : W₀ →+ V, Function.Injective θ ∧
      (∀ g v, θ (act g v) = ρ g (θ v)) ∧ (∀ v, f (θ v) = θ' i v) ∧
      LinearMap.range (θ.toZModLinearMap 2) ⊓ U = ⊥ :=
    fun i => lift_map act hcob ρ U f hker ρQ hquot θ₁ hθ₁inj hθ₁eq hθ₁range
      (θ' i) (hθ'inj i) (hθ'eq i) l hl_apply
  choose θi hθi_inj hθi_eq hcomp_apply hdisjC using hθi
  let C : ↥sq → Submodule (ZMod 2) V := fun i => LinearMap.range ((θi i).toZModLinearMap 2)
  have hCrange : ∀ i, (θi i).range = (C i).toAddSubgroup := fun i => rfl
  have hmapC : ∀ i, Submodule.map f (C i) = (i.1 : Submodule (ZMod 2) Q) := by
    intro i
    change Submodule.map f (LinearMap.range ((θi i).toZModLinearMap 2)) = (i.1)
    have hcomp : f.comp ((θi i).toZModLinearMap 2) = (θ' i).toZModLinearMap 2 := by
      ext v
      exact hcomp_apply i v
    rw [← LinearMap.range_comp, hcomp]
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hx
      have hxr : x ∈ (θ' i).range := ⟨v, hv⟩
      rwa [hθ'range i] at hxr
    · intro hx
      have hxr : x ∈ (θ' i).range := by rwa [hθ'range i]
      obtain ⟨v, hv⟩ := hxr
      exact LinearMap.mem_range.mpr ⟨v, hv⟩
  exact ⟨C, θi, hθi_inj, hCrange, hθi_eq, hmapC, hdisjC⟩

private theorem lift_decomp
    (act : G →* AddMonoid.End W₀)
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g)
    {V Q : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [AddCommGroup Q] [Module (ZMod 2) Q]
    (ρ : Representation (ZMod 2) G V) (U : Submodule (ZMod 2) V)
    (f : V →ₗ[ZMod 2] Q) (hker : LinearMap.ker f = U) (hf : Function.Surjective f)
    (ρQ : Representation (ZMod 2) G Q)
    (hquot : ∀ (g : G) (x : V), ρQ g (f x) = f (ρ g x))
    (θ₁ : W₀ →+ V) (hθ₁inj : Function.Injective θ₁)
    (hθ₁eq : ∀ g v, θ₁ (act g v) = ρ g (θ₁ v))
    (hθ₁range : θ₁.range = U.toAddSubgroup)
    (sq : Finset (Submodule (ZMod 2) Q)) (hsqInd : sq.SupIndep id)
    (hsqSup : sq.sup id = ⊤)
    (hsqMem : ∀ W ∈ sq, ∃ θ : W₀ →+ Q, Function.Injective θ ∧
      θ.range = W.toAddSubgroup ∧ ∀ g v, θ (act g v) = ρQ g (θ v)) :
    ∃ s : Finset (Submodule (ZMod 2) V), s.SupIndep id ∧ s.sup id = ⊤ ∧
      ∀ W ∈ s, ∃ θ : W₀ →+ V, Function.Injective θ ∧ θ.range = W.toAddSubgroup ∧
        ∀ g v, θ (act g v) = ρ g (θ v) := by
  classical
  obtain ⟨C, θi, hθi_inj, hCrange, hθi_eq, hmapC, hdisjC⟩ :=
    lift_family act hcob ρ U f hker hf ρQ hquot θ₁ hθ₁inj hθ₁eq hθ₁range sq hsqInd
      hsqSup hsqMem
  obtain ⟨hInd, hSup⟩ := supIndep_insert_ker hker hsqInd hsqSup hmapC hdisjC
  refine ⟨insert U (sq.attach.image C), hInd, hSup, ?_⟩
  intro W hW
  rw [Finset.mem_insert] at hW
  rcases hW with rfl | hW
  · exact ⟨θ₁, hθ₁inj, hθ₁range, hθ₁eq⟩
  · rw [Finset.mem_image] at hW
    obtain ⟨i, -, rfl⟩ := hW
    exact ⟨θi i, hθi_inj i, hCrange i, hθi_eq i⟩

private theorem exists_decomp_nontrivial
    (act : G →* AddMonoid.End W₀) {g₀ : G} (hg₀ : g₀ ^ 5 = 1)
    (hsimple : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), (∀ v, ρ g₀ v = v → v = 0) → Nontrivial V →
      (∀ W : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∃ θ : W₀ →+ V, Function.Bijective θ ∧ ∀ g v, θ (act g v) = ρ g (θ v))
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g)
    {n : ℕ}
    (ih : ∀ m < n, ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V],
      Nat.card V = m → ∀ (ρ : Representation (ZMod 2) G V),
      (∀ v, ρ g₀ v = v → v = 0) →
      ∃ s : Finset (Submodule (ZMod 2) V), s.SupIndep id ∧ s.sup id = ⊤ ∧
        ∀ W ∈ s, ∃ θ : W₀ →+ V, Function.Injective θ ∧ θ.range = W.toAddSubgroup ∧
          ∀ g v, θ (act g v) = ρ g (θ v))
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hcard : Nat.card V = n) (ρ : Representation (ZMod 2) G V)
    (hfpf : ∀ v, ρ g₀ v = v → v = 0) (hnt : Nontrivial V) :
    ∃ s : Finset (Submodule (ZMod 2) V), s.SupIndep id ∧ s.sup id = ⊤ ∧
      ∀ W ∈ s, ∃ θ : W₀ →+ V, Function.Injective θ ∧ θ.range = W.toAddSubgroup ∧
        ∀ g v, θ (act g v) = ρ g (θ v) := by
  obtain ⟨U, hUinv, hUne, hUmin⟩ := exists_minimal_invariant ρ
  haveI hUneN : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  let ρU : Representation (ZMod 2) G U := restrictRep ρ U hUinv
  have hfpfU : ∀ u : U, ρU g₀ u = u → u = 0 := fpf_restrict ρ U hUinv hfpf
  have hirr : ∀ W : Submodule (ZMod 2) U,
      (∀ g, ∀ w ∈ W, ρU g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    irreducible_of_minimal ρ hUinv hUmin
  obtain ⟨θU, hθUbij, hθUeq⟩ := hsimple U ρU hfpfU hUneN hirr
  let θ₁ : W₀ →+ V := U.subtype.toAddMonoidHom.comp θU
  have hθ₁inj : Function.Injective θ₁ := by
    intro x y h
    exact hθUbij.1 (Subtype.ext h)
  have hθ₁eq : ∀ g v, θ₁ (act g v) = ρ g (θ₁ v) := by
    intro g v
    have h := congrArg (fun x : U => (x : V)) (hθUeq g v)
    simpa [θ₁, ρU, restrictRep_apply] using h
  have hθ₁range : θ₁.range = U.toAddSubgroup := by
    apply le_antisymm
    · rintro x ⟨v, rfl⟩
      exact (θU v).2
    · intro x hx
      obtain ⟨v, hv⟩ := hθUbij.2 ⟨x, hx⟩
      exact ⟨v, congrArg Subtype.val hv⟩
  let Q := V ⧸ U
  let ρQ : Representation (ZMod 2) G Q := ρ.quotient U (fun g w hw => hUinv g w hw)
  have hfpfQ : ∀ q : Q, ρQ g₀ q = q → q = 0 :=
    fpf_quotient ρ U hUinv hg₀ hfpf
  haveI hfinQ : Finite Q :=
    Finite.of_surjective (Submodule.mkQ U) (Submodule.mkQ_surjective U)
  have hcardQ : Nat.card Q < Nat.card V := by
    have h : Nat.card V = Nat.card U * Nat.card Q :=
      Submodule.card_eq_card_quotient_mul_card U
    rw [h]
    exact lt_mul_of_one_lt_left Nat.card_pos Finite.one_lt_card
  have hcardQn : Nat.card Q < n := by rw [← hcard]; exact hcardQ
  obtain ⟨sq, hsqInd, hsqSup, hsqMem⟩ := ih (Nat.card Q) hcardQn Q rfl ρQ hfpfQ
  have hquot : ∀ (g : G) (x : V), ρQ g (U.mkQ x) = U.mkQ (ρ g x) := by
    intro g x
    change (Submodule.mapQ U U (ρ g) (fun w hw => hUinv g w hw)) (U.mkQ x) =
      U.mkQ (ρ g x)
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  obtain ⟨s, hsInd, hsSup, hsMem⟩ :=
    lift_decomp act hcob ρ U U.mkQ (Submodule.ker_mkQ U) (Submodule.mkQ_surjective U)
      ρQ hquot θ₁ hθ₁inj hθ₁eq hθ₁range sq hsqInd hsqSup hsqMem
  exact ⟨s, hsInd, hsSup, hsMem⟩

private theorem exists_decomp_aux (act : G →* AddMonoid.End W₀) {g₀ : G}
    (hg₀ : g₀ ^ 5 = 1)
    (hsimple : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), (∀ v, ρ g₀ v = v → v = 0) → Nontrivial V →
      (∀ W : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∃ θ : W₀ →+ V, Function.Bijective θ ∧ ∀ g v, θ (act g v) = ρ g (θ v))
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g) :
    ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V],
      Nat.card V = n → ∀ (ρ : Representation (ZMod 2) G V),
      (∀ v, ρ g₀ v = v → v = 0) →
      ∃ s : Finset (Submodule (ZMod 2) V), s.SupIndep id ∧ s.sup id = ⊤ ∧
        ∀ W ∈ s, ∃ θ : W₀ →+ V, Function.Injective θ ∧ θ.range = W.toAddSubgroup ∧
          ∀ g v, θ (act g v) = ρ g (θ v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V instACG instMod instFin hcard ρ hfpf
    classical
    by_cases hnt : Nontrivial V
    · exact exists_decomp_nontrivial act hg₀ hsimple hcob ih V hcard ρ hfpf hnt
    · haveI hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
      refine ⟨∅, by simp, ?_, by simp⟩
      have htop : (⊤ : Submodule (ZMod 2) V) = ⊥ := by
        rw [eq_bot_iff]
        intro x _
        exact Subsingleton.elim x 0
      rw [htop]
      rfl

theorem exists_decomp_of_simple_of_cocycle (act : G →* AddMonoid.End W₀) {g₀ : G}
    (hg₀ : g₀ ^ 5 = 1)
    (hsimple : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), (∀ v, ρ g₀ v = v → v = 0) → Nontrivial V →
      (∀ W : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∃ θ : W₀ →+ V, Function.Bijective θ ∧ ∀ g v, θ (act g v) = ρ g (θ v))
    (hcob : ∀ Y : G → AddMonoid.End W₀, (∀ g h, Y (g * h) = act g * Y h + Y g * act h) →
      ∃ X : AddMonoid.End W₀, ∀ g, Y g = act g * X - X * act g)
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hfpf : ∀ v, ρ g₀ v = v → v = 0) :
    ∃ s : Finset (Submodule (ZMod 2) V), s.SupIndep id ∧ s.sup id = ⊤ ∧
      ∀ W ∈ s, ∃ θ : W₀ →+ V, Function.Injective θ ∧ θ.range = W.toAddSubgroup ∧
        ∀ g v, θ (act g v) = ρ g (θ v) :=
  exists_decomp_aux act hg₀ hsimple hcob (Nat.card V) V rfl ρ hfpf

end CFSG.RepresentationTheory.SzMartineau
