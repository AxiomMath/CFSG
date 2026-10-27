module

public import CFSG.Quasithin.Background.F3Paths
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.Quasithin

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {Vh : Type u₁} {V : Type u₂} {Γh : SimpleGraph Vh} {Γ : SimpleGraph V}

structure GraphCovering (Γh : SimpleGraph Vh) (Γ : SimpleGraph V) (θ : Vh → V) : Prop where
  adj : ∀ a b, Γh.Adj a b → Γ.Adj (θ a) (θ b)
  surj : Function.Surjective θ
  loc_inj : ∀ v a b, Γh.Adj v a → Γh.Adj v b → θ a = θ b → a = b
  loc_surj : ∀ v w, Γ.Adj (θ v) w → ∃ a, Γh.Adj v a ∧ θ a = w

structure IsLocIso (Γh : SimpleGraph Vh) (Γ : SimpleGraph V) (θ : Vh → V) (v : Vh) : Prop where
  inj : ∀ a b, Γh.Adj v a → Γh.Adj v b → θ a = θ b → a = b
  surj : ∀ w, Γ.Adj (θ v) w → ∃ a, Γh.Adj v a ∧ θ a = w

theorem GraphCovering.of_isLocIso {θ : Vh → V} (hadj : ∀ a b, Γh.Adj a b → Γ.Adj (θ a) (θ b))
    (hsurj : Function.Surjective θ) (hloc : ∀ v, IsLocIso Γh Γ θ v) : GraphCovering Γh Γ θ where
  adj := hadj
  surj := hsurj
  loc_inj v := (hloc v).inj
  loc_surj v := (hloc v).surj

structure PermQuasiEquiv (A : Type*) (X : Type*) (B : Type*) (Y : Type*) [Group A] [Group B]
    [MulAction A X] [MulAction B Y] where
  grp : A ≃* B
  set : X ≃ Y
  map_smul : ∀ (a : A) (x : X), set (a • x) = grp a • set x

namespace PermQuasiEquiv

variable {A X B Y C Z : Type*} [Group A] [Group B] [Group C] [MulAction A X] [MulAction B Y]
  [MulAction C Z]

@[expose] def symm (q : PermQuasiEquiv A X B Y) : PermQuasiEquiv B Y A X where
  grp := q.grp.symm
  set := q.set.symm
  map_smul b y := by
    apply q.set.injective
    rw [q.set.apply_symm_apply, q.map_smul, q.grp.apply_symm_apply, q.set.apply_symm_apply]

@[expose] def trans (q₁ : PermQuasiEquiv A X B Y) (q₂ : PermQuasiEquiv B Y C Z) :
    PermQuasiEquiv A X C Z where
  grp := q₁.grp.trans q₂.grp
  set := q₁.set.trans q₂.set
  map_smul a x := by
    simp only [Equiv.trans_apply, MulEquiv.coe_trans, Function.comp_apply, q₁.map_smul, q₂.map_smul]

end PermQuasiEquiv

namespace GraphCovering

variable {θ : Vh → V} (hθ : GraphCovering Γh Γ θ)

@[expose] def pathMap {n : ℕ} (q : GPath Γh n) : GPath Γ n := q.map θ hθ.adj

@[simp] theorem pathMap_apply {n : ℕ} (q : GPath Γh n) (i : ℕ) : hθ.pathMap q i = θ (q i) := rfl

theorem GPath_eq_snoc_take {n : ℕ} (p : GPath Γ (n + 1)) :
    p = (p.take n (Nat.le_succ n)).snoc (p (n + 1)) (by
      simpa [GPath.take] using p.adj n (Nat.lt_succ_self n)) := by
  refine GPath.ext' fun i hi => ?_
  by_cases h : i ≤ n
  · rw [GPath.snoc_of_le _ _ _ h, GPath.take_apply_of_le _ _ _ h]
  · have : i = n + 1 := by omega
    subst this
    rw [GPath.snoc_last]

theorem pathMap_take {n : ℕ} (r : GPath Γh n) (k : ℕ) (hk : k ≤ n) :
    hθ.pathMap (r.take k hk) = (hθ.pathMap r).take k hk :=
  GPath.ext' fun i hi => by
    simp [GPath.take_apply_of_le _ _ _ hi]

theorem lift_path (vh : Vh) : ∀ (n : ℕ) (p : GPath Γ n), p 0 = θ vh →
    ∃! q : GPath Γh n, q 0 = vh ∧ hθ.pathMap q = p := by
  intro n
  induction n with
  | zero =>
    intro p hp
    refine ⟨⟨fun _ => vh, fun i hi => absurd hi (Nat.not_lt_zero i), fun _ _ => rfl⟩, ⟨rfl, ?_⟩, ?_⟩
    · exact GPath.ext' fun i hi => by
        have : i = 0 := by omega
        subst this
        simp [hp]
    · rintro q ⟨hq0, -⟩
      exact GPath.ext' fun i hi => by
        have : i = 0 := by omega
        subst this
        simpa using hq0
  | succ n ih =>
    intro p hp
    have hp' : (p.take n (Nat.le_succ n)) 0 = θ vh := by
      rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le n)]; exact hp
    obtain ⟨q', ⟨hq'0, hq'⟩, huniq⟩ := ih (p.take n (Nat.le_succ n)) hp'
    have hq'n : θ (q' n) = p n := by
      have := congrArg (fun r : GPath Γ n => r n) hq'
      simpa [GPath.take_apply_of_le] using this
    have hadj : Γ.Adj (θ (q' n)) (p (n + 1)) := by
      rw [hq'n]; exact p.adj n (Nat.lt_succ_self n)
    obtain ⟨a, haadj, haθ⟩ := hθ.loc_surj (q' n) (p (n + 1)) hadj
    refine ⟨q'.snoc a haadj, ⟨?_, ?_⟩, ?_⟩
    · rw [GPath.snoc_of_le _ _ _ (Nat.zero_le n)]; exact hq'0
    · refine GPath.ext' fun i hi => ?_
      by_cases h : i ≤ n
      · have e1 := congrArg (fun r : GPath Γ n => r i) hq'
        simp only [pathMap_apply, GPath.take_apply_of_le _ _ _ h] at e1 ⊢
        rw [GPath.snoc_of_le _ _ _ h]
        exact e1
      · have : i = n + 1 := by omega
        subst this
        simp [haθ]
    · rintro r ⟨hr0, hr⟩
      have hrt : r.take n (Nat.le_succ n) = q' := by
        refine huniq _ ⟨?_, ?_⟩
        · rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le n)]; exact hr0
        · rw [pathMap_take, hr]
      have hrn : r n = q' n := by
        have := congrArg (fun s : GPath Γh n => s n) hrt
        simpa [GPath.take_apply_of_le] using this
      have hra : r (n + 1) = a := by
        have h1 : Γh.Adj (q' n) (r (n + 1)) := by
          rw [← hrn]; exact r.adj n (Nat.lt_succ_self n)
        have h2 : θ (r (n + 1)) = θ a := by
          have := congrArg (fun s : GPath Γ (n + 1) => s (n + 1)) hr
          simp only [pathMap_apply] at this
          rw [this, haθ]
        exact hθ.loc_inj (q' n) _ _ h1 haadj h2
      refine GPath.ext' fun i hi => ?_
      by_cases h : i ≤ n
      · rw [GPath.snoc_of_le _ _ _ h, ← hrt, GPath.take_apply_of_le _ _ _ h]
      · have : i = n + 1 := by omega
        subst this
        rw [GPath.snoc_last, hra]

theorem noBack_pathMap_iff {n : ℕ} (q : GPath Γh n) : (hθ.pathMap q).NoBack ↔ q.NoBack := by
  constructor
  · intro h i hi heq
    exact h i hi (by simp [heq])
  · intro h i hi heq
    apply h i hi
    have h1 : Γh.Adj (q (i + 1)) (q i) := (q.adj i (by omega)).symm
    have h2 : Γh.Adj (q (i + 1)) (q (i + 2)) := q.adj (i + 1) (by omega)
    exact hθ.loc_inj (q (i + 1)) _ _ h1 h2 (by simpa using heq)

theorem bijOn_paths (vh : Vh) (n : ℕ) :
    Set.BijOn hθ.pathMap (GPath.paths Γh vh n) (GPath.paths Γ (θ vh) n) := by
  refine ⟨fun q hq => ?_, fun q₁ h₁ q₂ h₂ h => ?_, fun p hp => ?_⟩
  · show hθ.pathMap q 0 = θ vh
    simp [show q 0 = vh from hq]
  · obtain ⟨r, -, hr⟩ := hθ.lift_path vh n (hθ.pathMap q₁) (by
      show hθ.pathMap q₁ 0 = θ vh
      simp [show q₁ 0 = vh from h₁])
    exact (hr q₁ ⟨h₁, rfl⟩).trans (hr q₂ ⟨h₂, h.symm⟩).symm
  · obtain ⟨r, hr, -⟩ := hθ.lift_path vh n p hp
    exact ⟨r, hr.1, hr.2⟩

theorem bijOn_nbPaths (vh : Vh) (n : ℕ) :
    Set.BijOn hθ.pathMap (GPath.nbPaths Γh vh n) (GPath.nbPaths Γ (θ vh) n) := by
  have hb := hθ.bijOn_paths vh n
  refine ⟨fun q hq => ⟨hb.mapsTo hq.1, (hθ.noBack_pathMap_iff q).mpr hq.2⟩,
    hb.injOn.mono (fun q hq => hq.1), fun p hp => ?_⟩
  obtain ⟨q, hq, hqp⟩ := hb.surjOn hp.1
  exact ⟨q, ⟨hq, (hθ.noBack_pathMap_iff q).mp (hqp ▸ hp.2)⟩, hqp⟩

@[expose] def pathSetMap (vh : Vh) (p : PathSet Γh vh) : PathSet Γ (θ vh) :=
  ⟨p.1, hθ.pathMap p.2.1, by
    show hθ.pathMap p.2.1 0 = θ vh
    simp [p.2.2]⟩

@[simp] theorem pathSetMap_apply (vh : Vh) (p : PathSet Γh vh) (i : ℕ) :
    (hθ.pathSetMap vh p).2.1 i = θ (p.2.1 i) := rfl

theorem pathSetMap_length (vh : Vh) (p : PathSet Γh vh) : (hθ.pathSetMap vh p).1 = p.1 := rfl

theorem pathSetMap_bijective (vh : Vh) : Function.Bijective (hθ.pathSetMap vh) := by
  constructor
  · rintro ⟨n, p, hp⟩ ⟨n', p', hp'⟩ h
    have hn : n = n' := congrArg Sigma.fst h
    subst hn
    have h2 : hθ.pathMap p = hθ.pathMap p' := by
      have := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact congrArg Subtype.val this
    have := (hθ.bijOn_paths vh n).injOn (show p ∈ GPath.paths Γh vh n from hp)
      (show p' ∈ GPath.paths Γh vh n from hp') h2
    subst this
    rfl
  · rintro ⟨n, p, hp⟩
    obtain ⟨q, hq, hqp⟩ := (hθ.bijOn_paths vh n).surjOn (show p ∈ GPath.paths Γ (θ vh) n from hp)
    exact ⟨⟨n, q, hq⟩, Sigma.ext rfl (heq_of_eq (Subtype.ext hqp))⟩

@[expose] noncomputable def pathSetEquiv (vh : Vh) : PathSet Γh vh ≃ PathSet Γ (θ vh) :=
  Equiv.ofBijective _ (hθ.pathSetMap_bijective vh)

theorem pathSetMap_bijOn_noBack (vh : Vh) :
    Set.BijOn (hθ.pathSetMap vh) {p | p.NoBack} {p | p.NoBack} := by
  have hb := hθ.pathSetMap_bijective vh
  refine ⟨fun p hp => (hθ.noBack_pathMap_iff p.2.1).mpr hp, hb.1.injOn, fun p hp => ?_⟩
  obtain ⟨q, hq⟩ := hb.2 p
  refine ⟨q, ?_, hq⟩
  have h1 : (hθ.pathSetMap vh q).NoBack := by rw [hq]; exact hp
  exact (hθ.noBack_pathMap_iff q.2.1).mp h1

section Groups

variable {Gh : Type u₃} {G : Type u₄} [Group Gh] [Group G] [MulAction Gh Vh] [MulAction G V]
  [GraphAction Gh Γh] [GraphAction G Γ]

structure StabIso (θG : Gh →* G) (uh : Vh) : Prop where
  equivariant : ∀ (gh : Gh) (v : Vh), θ (gh • v) = θG gh • θ v
  inj : ∀ gh : Gh, gh • uh = uh → θG gh = 1 → gh = 1
  surj : ∀ g : G, g • θ uh = θ uh → ∃ gh : Gh, gh • uh = uh ∧ θG gh = g

variable {θG : Gh →* G}

theorem pathMap_smul (hs : ∀ (gh : Gh) (v : Vh), θ (gh • v) = θG gh • θ v) {n : ℕ} (gh : Gh)
    (q : GPath Γh n) : hθ.pathMap (gh • q) = θG gh • hθ.pathMap q :=
  GPath.ext' fun i _ => by simp [hs]

@[expose] def _root_.CFSG.Quasithin.GPath.stabPath {H : Type*} [Group H] [MulAction H V]
    {Γ : SimpleGraph V} {n : ℕ} (p : GPath Γ n) : Subgroup H where
  carrier := {g | ∀ i, i ≤ n → g • p i = p i}
  one_mem' := fun i _ => one_smul H _
  mul_mem' := fun {a b} ha hb i hi => by rw [mul_smul, hb i hi, ha i hi]
  inv_mem' := fun {a} ha i hi => by
    have := ha i hi
    rw [inv_smul_eq_iff]
    exact this.symm

theorem mem_stabPath {H : Type*} [Group H] [MulAction H V] {Γ : SimpleGraph V} {n : ℕ}
    {p : GPath Γ n} {g : H} : g ∈ p.stabPath ↔ ∀ i, i ≤ n → g • p i = p i := Iff.rfl

omit [GraphAction Gh Γh] [GraphAction G Γ] in
theorem map_stabPath_le (hs : ∀ (gh : Gh) (v : Vh), θ (gh • v) = θG gh • θ v) {n : ℕ}
    (q : GPath Γh n) {gh : Gh} (hg : gh ∈ q.stabPath) : θG gh ∈ (hθ.pathMap q).stabPath :=
  fun i hi => by
    show θG gh • θ (q i) = θ (q i)
    rw [← hs, hg i hi]

theorem stabPath_le_map (uh : Vh) (hsi : StabIso (θ := θ) (θG := θG) uh) {n : ℕ} (q : GPath Γh n)
    (hq : q 0 = uh) {g : G} (hg : g ∈ (hθ.pathMap q).stabPath) :
    ∃ gh : Gh, gh ∈ q.stabPath ∧ θG gh = g := by
  have hg0 : g • θ uh = θ uh := by
    have := hg 0 (Nat.zero_le n)
    simpa [hq] using this
  obtain ⟨gh, hgh, hθg⟩ := hsi.surj g hg0
  refine ⟨gh, ?_, hθg⟩
  have heq : hθ.pathMap (gh • q) = hθ.pathMap q := by
    rw [hθ.pathMap_smul hsi.equivariant, hθg]
    refine GPath.ext' fun i hi => ?_
    simpa using hg i hi
  have h0 : (gh • q) 0 = uh := by simp [hq, hgh]
  obtain ⟨r, -, hr⟩ := hθ.lift_path uh n (hθ.pathMap q) (by simp [hq])
  have e1 := hr (gh • q) ⟨h0, heq⟩
  have e2 := hr q ⟨hq, rfl⟩
  have : gh • q = q := e1.trans e2.symm
  intro i hi
  have := congrArg (fun s : GPath Γh n => s i) this
  simpa using this

omit [GraphAction Gh Γh] in
theorem injOn_stabPath (uh : Vh) (hsi : StabIso (θ := θ) (θG := θG) uh) {n : ℕ} (q : GPath Γh n)
    (hq : q 0 = uh) {g₁ g₂ : Gh} (h₁ : g₁ ∈ q.stabPath) (h₂ : g₂ ∈ q.stabPath)
    (h : θG g₁ = θG g₂) : g₁ = g₂ := by
  have hg1 : g₁ • uh = uh := by simpa [hq] using h₁ 0 (Nat.zero_le n)
  have hg2 : g₂ • uh = uh := by simpa [hq] using h₂ 0 (Nat.zero_le n)
  have : g₂⁻¹ * g₁ = 1 := by
    apply hsi.inj
    · rw [mul_smul, hg1, inv_smul_eq_iff]; exact hg2.symm
    · rw [map_mul, map_inv, h]; simp
  rw [inv_mul_eq_one] at this
  exact this.symm

include hθ in
theorem transitive_of_transitive (uh : Vh) (hsi : StabIso (θ := θ) (θG := θG) uh) (n : ℕ)
    (htrans : ∀ q₁ q₂ : GPath Γh n, q₁ ∈ GPath.nbPaths Γh uh n → q₂ ∈ GPath.nbPaths Γh uh n →
      ∃ gh : Gh, gh • uh = uh ∧ gh • q₁ = q₂)
    (p₁ p₂ : GPath Γ n) (h₁ : p₁ ∈ GPath.nbPaths Γ (θ uh) n)
    (h₂ : p₂ ∈ GPath.nbPaths Γ (θ uh) n) :
    ∃ g : G, g • θ uh = θ uh ∧ g • p₁ = p₂ := by
  have hb := hθ.bijOn_nbPaths uh n
  obtain ⟨q₁, hq₁, rfl⟩ := hb.surjOn h₁
  obtain ⟨q₂, hq₂, rfl⟩ := hb.surjOn h₂
  obtain ⟨gh, hgh, hq⟩ := htrans q₁ q₂ hq₁ hq₂
  refine ⟨θG gh, ?_, ?_⟩
  · rw [← hsi.equivariant, hgh]
  · rw [← hθ.pathMap_smul hsi.equivariant, hq]

omit [GraphAction G Γ] in
theorem isLocIso_smul' (hs : ∀ (gh : Gh) (v : Vh), θ (gh • v) = θG gh • θ v) {v : Vh}
    (h : IsLocIso Γh Γ θ v) (g : Gh) (hΓ : ∀ (g : G) (a b : V), Γ.Adj (g • a) (g • b) ↔ Γ.Adj a b) :
    IsLocIso Γh Γ θ (g • v) where
  inj a b ha hb hab := by
    have ha' : Γh.Adj v (g⁻¹ • a) := by
      have := (GraphAction.adj_smul g⁻¹ (g • v) a).mpr ha
      rwa [inv_smul_smul] at this
    have hb' : Γh.Adj v (g⁻¹ • b) := by
      have := (GraphAction.adj_smul g⁻¹ (g • v) b).mpr hb
      rwa [inv_smul_smul] at this
    have hab' : θ (g⁻¹ • a) = θ (g⁻¹ • b) := by rw [hs, hs, hab]
    exact smul_left_cancel g⁻¹ (h.inj _ _ ha' hb' hab')
  surj w hw := by
    rw [hs] at hw
    have hw' : Γ.Adj (θ v) ((θG g)⁻¹ • w) := by
      have := (hΓ (θG g)⁻¹ (θG g • θ v) w).mpr hw
      rwa [inv_smul_smul] at this
    obtain ⟨a, ha, haθ⟩ := h.surj _ hw'
    refine ⟨g • a, (GraphAction.adj_smul g v a).mpr ha, ?_⟩
    rw [hs, haθ, smul_inv_smul]

theorem isLocIso_smul (hs : ∀ (gh : Gh) (v : Vh), θ (gh • v) = θG gh • θ v) {v : Vh}
    (h : IsLocIso Γh Γ θ v) (g : Gh) : IsLocIso Γh Γ θ (g • v) :=
  isLocIso_smul' hs h g (fun g a b => GraphAction.adj_smul g a b)

omit [GraphAction Gh Γh] [GraphAction G Γ] in
theorem StabIso.smul {uh : Vh} (h : StabIso (θ := θ) (θG := θG) uh) (g : Gh) :
    StabIso (θ := θ) (θG := θG) (g • uh) where
  equivariant := h.equivariant
  inj gh hgh h1 := by
    have e1 : (g⁻¹ * gh * g) • uh = uh := by
      rw [mul_smul, mul_smul, hgh, inv_smul_smul]
    have e2 : θG (g⁻¹ * gh * g) = 1 := by
      rw [map_mul, map_mul, map_inv, h1]; simp
    have := h.inj _ e1 e2
    have h3 := congrArg (fun x => g * x * g⁻¹) this
    simpa [mul_assoc] using h3
  surj g' hg' := by
    rw [h.equivariant g uh] at hg'
    have e1 : ((θG g)⁻¹ * g' * θG g) • θ uh = θ uh := by
      rw [mul_smul, mul_smul, hg', inv_smul_smul]
    obtain ⟨gh', hgh', hθ'⟩ := h.surj _ e1
    refine ⟨g * gh' * g⁻¹, ?_, ?_⟩
    · rw [mul_smul, mul_smul, inv_smul_smul, hgh']
    · rw [map_mul, map_mul, map_inv, hθ']
      group

omit [GraphAction Gh Γh] [GraphAction G Γ] in
@[expose] def StabIso.restrict {uh : Vh} (h : StabIso (θ := θ) (θG := θG) uh) :
    MulAction.stabilizer Gh uh →* MulAction.stabilizer G (θ uh) where
  toFun g := ⟨θG g, by
    rw [MulAction.mem_stabilizer_iff, ← h.equivariant (g : Gh) uh]
    exact congrArg θ (MulAction.mem_stabilizer_iff.mp g.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

omit [GraphAction Gh Γh] [GraphAction G Γ] in
@[simp] theorem StabIso.coe_restrict {uh : Vh} (h : StabIso (θ := θ) (θG := θG) uh)
    (g : MulAction.stabilizer Gh uh) : ((h.restrict g : MulAction.stabilizer G (θ uh)) : G) = θG g :=
  rfl

omit [GraphAction Gh Γh] [GraphAction G Γ] in
theorem StabIso.restrict_bijective {uh : Vh} (h : StabIso (θ := θ) (θG := θG) uh) :
    Function.Bijective h.restrict := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun a ha => ?_, fun g => ?_⟩
  · have h1 : θG a = 1 := congrArg Subtype.val ha
    exact Subtype.ext (h.inj _ (MulAction.mem_stabilizer_iff.mp a.2) h1)
  · obtain ⟨gh, hgh, hθ⟩ := h.surj g.1 (MulAction.mem_stabilizer_iff.mp g.2)
    exact ⟨⟨gh, MulAction.mem_stabilizer_iff.mpr hgh⟩, Subtype.ext hθ⟩

omit [GraphAction Gh Γh] [GraphAction G Γ] in
@[expose] noncomputable def StabIso.equiv {uh : Vh} (h : StabIso (θ := θ) (θG := θG) uh) :
    MulAction.stabilizer Gh uh ≃* MulAction.stabilizer G (θ uh) :=
  MulEquiv.ofBijective h.restrict h.restrict_bijective

include hθ in
@[expose] noncomputable def StabIso.quasiEquiv {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh) :
    PermQuasiEquiv (MulAction.stabilizer Gh uh) (PathSet Γh uh) (MulAction.stabilizer G (θ uh))
      (PathSet Γ (θ uh)) where
  grp := hs.equiv
  set := hθ.pathSetEquiv uh
  map_smul g p := PathSet.ext rfl fun i => by
    show θ ((g : Gh) • p.2.1 i) = θG g • θ (p.2.1 i)
    exact hs.equivariant _ _

include hθ in
theorem map_stabPath_eq {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh) {n : ℕ} (q : GPath Γh n)
    (hq : q 0 = uh) : q.stabPath.map θG = (hθ.pathMap q).stabPath := by
  ext g
  constructor
  · rintro ⟨gh, hgh, rfl⟩
    exact hθ.map_stabPath_le hs.equivariant q hgh
  · intro hg
    obtain ⟨gh, hgh, hθg⟩ := hθ.stabPath_le_map uh hs q hq hg
    exact ⟨gh, hgh, hθg⟩

include hθ in
@[expose] noncomputable def stabPathEquiv {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh) {n : ℕ}
    (q : GPath Γh n) (hq : q 0 = uh) :
    ↥(q.stabPath : Subgroup Gh) ≃* ↥((hθ.pathMap q).stabPath : Subgroup G) :=
  MulEquiv.ofBijective
    ((θG.comp (q.stabPath : Subgroup Gh).subtype).codRestrict (hθ.pathMap q).stabPath
      (fun g => hθ.map_stabPath_le hs.equivariant q g.2))
    ⟨fun a b hab => Subtype.ext (injOn_stabPath uh hs q hq a.2 b.2 (congrArg Subtype.val hab)),
      fun g => by
        obtain ⟨gh, hgh, hθg⟩ := hθ.stabPath_le_map uh hs q hq g.2
        exact ⟨⟨gh, hgh⟩, Subtype.ext hθg⟩⟩

include hθ in
theorem transitive_of_transitive' (uh : Vh) (hsi : StabIso (θ := θ) (θG := θG) uh) (n : ℕ)
    (htrans : ∀ p₁ p₂ : GPath Γ n, p₁ ∈ GPath.nbPaths Γ (θ uh) n →
      p₂ ∈ GPath.nbPaths Γ (θ uh) n → ∃ g : G, g • θ uh = θ uh ∧ g • p₁ = p₂)
    (q₁ q₂ : GPath Γh n) (h₁ : q₁ ∈ GPath.nbPaths Γh uh n) (h₂ : q₂ ∈ GPath.nbPaths Γh uh n) :
    ∃ gh : Gh, gh • uh = uh ∧ gh • q₁ = q₂ := by
  have hb := hθ.bijOn_nbPaths uh n
  obtain ⟨g, hg, hgq⟩ := htrans _ _ (hb.mapsTo h₁) (hb.mapsTo h₂)
  obtain ⟨gh, hgh, hθg⟩ := hsi.surj g hg
  refine ⟨gh, hgh, ?_⟩
  have h3 : gh • q₁ ∈ GPath.nbPaths Γh uh n :=
    ⟨by rw [GPath.smul_apply, h₁.1, hgh], GPath.smul_noBack h₁.2⟩
  refine hb.injOn h3 h₂ ?_
  rw [hθ.pathMap_smul hsi.equivariant, hθg]
  exact hgq

include hθ in
theorem mem_stabPath_iff {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh) {n : ℕ} (q : GPath Γh n)
    (hq : q 0 = uh) {g : Gh} (hg : g • uh = uh) :
    g ∈ q.stabPath ↔ θG g ∈ (hθ.pathMap q).stabPath := by
  constructor
  · intro h
    exact hθ.map_stabPath_le hs.equivariant q h
  · intro h
    obtain ⟨g', hg', hθg'⟩ := hθ.stabPath_le_map uh hs q hq h
    have hg'u : g' • uh = uh := by simpa [hq] using hg' 0 (Nat.zero_le n)
    have h1 : g'⁻¹ * g = 1 := by
      apply hs.inj
      · rw [mul_smul, hg, inv_smul_eq_iff]
        exact hg'u.symm
      · rw [map_mul, map_inv, hθg']; simp
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hg'

end Groups

section Two

variable {V₂ : Type u₅} {Γ₂ : SimpleGraph V₂} {θ₂ : Vh → V₂} (hθ₂ : GraphCovering Γh Γ₂ θ₂)
  {Gh : Type u₃} {G : Type u₄} {G₂ : Type u₆} [Group Gh] [Group G] [Group G₂] [MulAction Gh Vh]
  [MulAction G V] [MulAction G₂ V₂] [GraphAction Gh Γh] [GraphAction G Γ] [GraphAction G₂ Γ₂]
  {θG : Gh →* G} {θG₂ : Gh →* G₂}

@[expose] noncomputable def psi (uh : Vh) : PathSet Γ (θ uh) ≃ PathSet Γ₂ (θ₂ uh) :=
  (hθ.pathSetEquiv uh).symm.trans (hθ₂.pathSetEquiv uh)

@[expose] noncomputable def StabIso.comp {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh)
    (hs₂ : StabIso (θ := θ₂) (θG := θG₂) uh) :
    MulAction.stabilizer G (θ uh) ≃* MulAction.stabilizer G₂ (θ₂ uh) :=
  hs.equiv.symm.trans hs₂.equiv

omit [GraphAction Gh Γh] [GraphAction G Γ] [GraphAction G₂ Γ₂] in
theorem StabIso.comp_spec {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh)
    (hs₂ : StabIso (θ := θ₂) (θG := θG₂) uh) (gq : MulAction.stabilizer Gh uh) :
    StabIso.comp hs hs₂ (hs.equiv gq) = hs₂.equiv gq := by
  simp [StabIso.comp]

include hθ hθ₂ in
@[expose] noncomputable def quasiEquivComp {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh)
    (hs₂ : StabIso (θ := θ₂) (θG := θG₂) uh) :
    PermQuasiEquiv (MulAction.stabilizer G (θ uh)) (PathSet Γ (θ uh))
      (MulAction.stabilizer G₂ (θ₂ uh)) (PathSet Γ₂ (θ₂ uh)) :=
  (StabIso.quasiEquiv hθ hs).symm.trans (StabIso.quasiEquiv hθ₂ hs₂)

include hθ hθ₂ in
theorem quasiEquivComp_grp {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh)
    (hs₂ : StabIso (θ := θ₂) (θG := θG₂) uh) :
    (quasiEquivComp hθ hθ₂ hs hs₂).grp = StabIso.comp hs hs₂ := rfl

include hθ hθ₂ in
theorem quasiEquivComp_set {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh)
    (hs₂ : StabIso (θ := θ₂) (θG := θG₂) uh) :
    (quasiEquivComp hθ hθ₂ hs hs₂).set = psi hθ hθ₂ uh := rfl

include hθ hθ₂ in
theorem mem_stabPath_comp_iff {uh : Vh} (hs : StabIso (θ := θ) (θG := θG) uh)
    (hs₂ : StabIso (θ := θ₂) (θG := θG₂) uh) (p : PathSet Γ (θ uh))
    (g : MulAction.stabilizer G (θ uh)) :
    (g : G) ∈ p.2.1.stabPath ↔
      ((StabIso.comp hs hs₂ g : MulAction.stabilizer G₂ (θ₂ uh)) : G₂) ∈
        (psi hθ hθ₂ uh p).2.1.stabPath := by
  obtain ⟨ph, rfl⟩ := (hθ.pathSetEquiv uh).surjective p
  obtain ⟨gq, rfl⟩ := hs.equiv.surjective g
  rw [StabIso.comp_spec hs hs₂ gq]
  have e : psi hθ hθ₂ uh (hθ.pathSetEquiv uh ph) = hθ₂.pathSetEquiv uh ph := by
    simp [psi]
  rw [e]
  have h1 : (hs.equiv gq : G) = θG gq := rfl
  have h2 : (hs₂.equiv gq : G₂) = θG₂ gq := rfl
  rw [h1, h2]
  have hgq : (gq : Gh) • uh = uh := MulAction.mem_stabilizer_iff.mp gq.2
  have hp0 : ph.2.1 0 = uh := ph.2.2
  exact (hθ.mem_stabPath_iff hs ph.2.1 hp0 hgq).symm.trans (hθ₂.mem_stabPath_iff hs₂ ph.2.1 hp0 hgq)

end Two

end GraphCovering

end CFSG.Quasithin
