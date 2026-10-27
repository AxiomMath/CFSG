module

public import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type*} [Group G] {D : Set G}

namespace OddLocal

@[expose] def conjSet (g : G) (S : Set G) : Set G := (fun x => g * x * g⁻¹) '' S

@[expose] def OrbitGen (S : Set G) (e : G) : Prop :=
  ∀ x ∈ S, ∃ k ∈ Subgroup.closure S, x = k * e * k⁻¹

theorem mem_conjSet {g x : G} {S : Set G} : x ∈ conjSet g S ↔ g⁻¹ * x * g ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by group⟩

theorem conj_mem_conjSet {g x : G} {S : Set G} (hx : x ∈ S) : g * x * g⁻¹ ∈ conjSet g S :=
  ⟨x, hx, rfl⟩

theorem ncard_conjSet [Finite G] (g : G) (S : Set G) : (conjSet g S).ncard = S.ncard :=
  Set.ncard_image_of_injective _ fun a b h => by simpa using h

theorem mem_normalizer_of_commute {S : Set G} {c : G} (h : ∀ x ∈ S, Commute c x) :
    c ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [(h y hy).eq, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := (h _ hy).eq
    have e : c * y * c⁻¹ = y := by
      have h2 : c * (c * y * c⁻¹) = c * y := by rw [h1]; group
      exact mul_left_cancel h2
    rw [← e]
    exact hy

theorem mem_normalizer_orbit {K : Subgroup G} {e k : G} (hk : k ∈ K) :
    k ∈ Subgroup.normalizer {f | ∃ g ∈ K, f = g * e * g⁻¹} := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨k * g, K.mul_mem hk hg, by group⟩
  · rintro ⟨g, hg, hgh⟩
    refine ⟨k⁻¹ * g, K.mul_mem (K.inv_mem hk) hg, ?_⟩
    calc h = k⁻¹ * (k * h * k⁻¹) * k := by group
      _ = k⁻¹ * g * e * (k⁻¹ * g)⁻¹ := by rw [hgh]; group

theorem orbit_eq_of_mem {K : Subgroup G} {e e' : G}
    (h : e' ∈ {f | ∃ g ∈ K, f = g * e * g⁻¹}) :
    {f | ∃ g ∈ K, f = g * e' * g⁻¹} = {f | ∃ g ∈ K, f = g * e * g⁻¹} := by
  obtain ⟨g₀, hg₀, rfl⟩ := h
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * g₀, K.mul_mem hg hg₀, by group⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * g₀⁻¹, K.mul_mem hg (K.inv_mem hg₀), by group⟩

theorem orbit_subset {K : Subgroup G} {S : Set G} (hK : K ≤ Subgroup.normalizer S) {e : G}
    (he : e ∈ S) : {f | ∃ g ∈ K, f = g * e * g⁻¹} ⊆ S := by
  rintro _ ⟨g, hg, rfl⟩
  exact (Subgroup.mem_set_normalizer_iff.mp (hK hg) e).mp he

theorem conj_mem_closure_conjSet {S : Set G} (g : G) {k : G} (hk : k ∈ Subgroup.closure S) :
    g * k * g⁻¹ ∈ Subgroup.closure (conjSet g S) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (conj_mem_conjSet hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem OrbitGen.conj {S : Set G} {e : G} (h : OrbitGen S e) (g : G) :
    OrbitGen (conjSet g S) (g * e * g⁻¹) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk, rfl⟩ := h y hy
  exact ⟨g * k * g⁻¹, conj_mem_closure_conjSet g hk, by group⟩

theorem mem_of_not_commute (hD : IsOddTransp D) {u v : G} (hu : u ∈ D) (hv : v ∈ D)
    (huv : ¬ Commute u v) {S : Set G} (huS : u ∈ S) (hnu : u ∈ Subgroup.normalizer S)
    (hnv : v ∈ Subgroup.normalizer S) : v ∈ S := by
  obtain ⟨g, hg, hgu⟩ := hD.exists_conj hu hv huv
  have hle : Subgroup.closure ({u, v} : Set G) ≤ Subgroup.normalizer S := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hnu
    · exact hnv
  rw [← hgu]
  exact (Subgroup.mem_set_normalizer_iff.mp (hle hg) u).mp huS

theorem isBlock_conj_iff {F : Set G} :
    MulAction.IsBlock (ConjAct G) F ↔
      ∀ g : G, ∀ a ∈ F, g * a * g⁻¹ ∈ F → g ∈ Subgroup.normalizer F := by
  have key : ∀ g : G, ConjAct.toConjAct g • F = F ↔ g ∈ Subgroup.normalizer F := by
    intro g
    rw [Subgroup.mem_normalizer_iff_conj_image_eq, ← Set.image_smul]
    rfl
  rw [MulAction.isBlock_iff_smul_eq_of_mem]
  constructor
  · intro h g a ha hga
    rw [← key]
    exact h ha (by rwa [ConjAct.toConjAct_smul])
  · intro h g a ha hga
    rw [← ConjAct.toConjAct_ofConjAct g, key]
    exact h _ a ha (by rwa [ConjAct.smul_def] at hga)

theorem closure_commSet_le_centralizer (d : G) :
    Subgroup.closure (commSet D d) ≤ Subgroup.centralizer {d} := by
  rw [Subgroup.closure_le]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr hx.2.1.eq

theorem commute_of_mem_closure_commSet {d k : G} (hk : k ∈ Subgroup.closure (commSet D d)) :
    Commute k d :=
  Subgroup.mem_centralizer_singleton_iff.mp (closure_commSet_le_centralizer d hk)

theorem self_mem_orbitIn (d e : G) : e ∈ orbitIn D d e :=
  ⟨1, Subgroup.one_mem _, by group⟩

theorem orbitIn_subset_commSet (hN : IsNormalSet D) {d e : G} (he : e ∈ commSet D d) :
    orbitIn D d e ⊆ commSet D d := by
  rintro _ ⟨g, hg, rfl⟩
  have hgd := commute_of_mem_closure_commSet hg
  refine ⟨hN g e he.1, (hgd.mul_left he.2.1).mul_left hgd.inv_left, fun h => he.2.2 ?_⟩
  calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
    _ = d := by rw [h, hgd.inv_left.eq, inv_mul_cancel_right]

theorem closure_commSet_le_normalizer_orbitIn (d e : G) :
    Subgroup.closure (commSet D d) ≤ Subgroup.normalizer (orbitIn D d e) :=
  fun _ hk => mem_normalizer_orbit hk

theorem orbitIn_eq_of_mem {d e e' : G} (h : e' ∈ orbitIn D d e) :
    orbitIn D d e' = orbitIn D d e :=
  orbit_eq_of_mem h

theorem conj_mem_closure_commSet (hN : IsNormalSet D) {c d k : G}
    (hk : k ∈ Subgroup.closure (commSet D (c * d * c⁻¹))) :
    c⁻¹ * k * c ∈ Subgroup.closure (commSet D d) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨by simpa using hN c⁻¹ x hx.1, ?_, fun h => hx.2.2 ?_⟩
    · have h1 := (hx.2.1.conj c⁻¹)
      simpa [mul_assoc] using h1
    · calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
        _ = c * d * c⁻¹ := by rw [h]
  | one => simp
  | mul x y _ _ hx hy =>
    have e : c⁻¹ * (x * y) * c = c⁻¹ * x * c * (c⁻¹ * y * c) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : c⁻¹ * x⁻¹ * c = (c⁻¹ * x * c)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem ncard_orbitIn_le [Finite G] (hS : Setup G D) {d : G} (hd : d ∈ D) {E : Set G}
    (hE : IsMaxOrbit D d E) {f e' : G} (hf : f ∈ D) (he' : e' ∈ commSet D f) :
    (orbitIn D f e').ncard ≤ E.ncard := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hd hf)
  obtain ⟨-, -, -, hmax⟩ := hE
  set e'' := c⁻¹ * e' * c with he''
  have he''d : e'' ∈ commSet D d := by
    refine ⟨by simpa using hS.normal c⁻¹ e' he'.1, ?_, fun h => he'.2.2 ?_⟩
    · have h1 := he'.2.1.conj c⁻¹
      simpa [he'', mul_assoc] using h1
    · calc e' = c * e'' * c⁻¹ := by rw [he'']; group
        _ = c * d * c⁻¹ := by rw [h]
  have hsub : orbitIn D (c * d * c⁻¹) e' ⊆ conjSet c (orbitIn D d e'') := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_conjSet]
    exact ⟨c⁻¹ * k * c, conj_mem_closure_commSet hS.normal hk, by rw [he'']; group⟩
  calc (orbitIn D (c * d * c⁻¹) e').ncard ≤ (conjSet c (orbitIn D d e'')).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (orbitIn D d e'').ncard := ncard_conjSet c _
    _ ≤ E.ncard := hmax e'' he''d

section Orbit

variable {d : G} {E : Set G}

theorem subset_commSet (hN : IsNormalSet D) (hE : IsMaxOrbit D d E) : E ⊆ commSet D d := by
  obtain ⟨e₀, he₀, rfl, -⟩ := hE
  exact orbitIn_subset_commSet hN he₀

theorem closure_commSet_le_normalizer (hE : IsMaxOrbit D d E) :
    Subgroup.closure (commSet D d) ≤ Subgroup.normalizer E := by
  obtain ⟨e₀, -, rfl, -⟩ := hE
  exact closure_commSet_le_normalizer_orbitIn d e₀

theorem mem_normalizer_of_mem_commSet (hE : IsMaxOrbit D d E) {c : G} (hc : c ∈ commSet D d) :
    c ∈ Subgroup.normalizer E :=
  closure_commSet_le_normalizer hE (Subgroup.subset_closure hc)

theorem self_mem_normalizer (hN : IsNormalSet D) (hE : IsMaxOrbit D d E) :
    d ∈ Subgroup.normalizer E :=
  mem_normalizer_of_commute fun _ hx => (subset_commSet hN hE hx).2.1.symm

theorem nonempty (hE : IsMaxOrbit D d E) : E.Nonempty := by
  obtain ⟨e₀, -, rfl, -⟩ := hE
  exact ⟨e₀, self_mem_orbitIn d e₀⟩

theorem commute_of_not_mem (hS : Setup G D) (hE : IsMaxOrbit D d E) {c : G}
    (hc : c ∈ commSet D d) (hcE : c ∉ E) {e : G} (he : e ∈ E) : Commute c e := by
  by_contra h
  have heD := subset_commSet hS.normal hE he
  exact hcE (mem_of_not_commute hS.oddT heD.1 hc.1 (fun h' => h h'.symm) he
    (mem_normalizer_of_mem_commSet hE heD) (mem_normalizer_of_mem_commSet hE hc))

theorem orbitGen (hS : Setup G D) (hE : IsMaxOrbit D d E) {e : G} (he : e ∈ E) :
    OrbitGen E e := by
  set P : Set G := {f | ∃ k ∈ Subgroup.closure E, f = k * e * k⁻¹} with hP
  have hle : Subgroup.closure (commSet D d) ≤ Subgroup.normalizer P := by
    rw [Subgroup.closure_le]
    intro c hc
    by_cases hcE : c ∈ E
    · exact mem_normalizer_orbit (Subgroup.subset_closure hcE)
    · apply mem_normalizer_of_commute
      rintro _ ⟨k, hk, rfl⟩
      have hck : Commute c k := by
        have h1 : Subgroup.closure E ≤ Subgroup.centralizer {c} := by
          rw [Subgroup.closure_le]
          intro x hx
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (commute_of_not_mem hS hE hc hcE hx).eq.symm
        exact (Subgroup.mem_centralizer_singleton_iff.mp (h1 hk)).symm
      exact (hck.mul_right (commute_of_not_mem hS hE hc hcE he)).mul_right hck.inv_right
  have hEe : E = orbitIn D d e := by
    obtain ⟨e₀, -, rfl, -⟩ := hE
    exact (orbitIn_eq_of_mem he).symm
  intro x hx
  rw [hEe] at hx
  exact orbit_subset hle ⟨1, Subgroup.one_mem _, by group⟩ hx

theorem one_lt_ncard [Finite G] (hS : Setup G D) (hd : d ∈ D) (hE : IsMaxOrbit D d E)
    (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b) : 1 < E.ncard := by
  by_contra hlt
  push Not at hlt
  have hcl : ∀ f ∈ D, ∀ c ∈ commSet D f, ∀ e ∈ commSet D f, Commute c e := by
    intro f hf c hc e he
    have h1 := ncard_orbitIn_le hS hd hE hf he
    have hsub : orbitIn D f e ⊆ {e} := by
      intro y hy
      have hle1 : (orbitIn D f e).ncard ≤ 1 := h1.trans hlt
      exact (Set.ncard_le_one (Set.toFinite _)).mp hle1 y hy e (self_mem_orbitIn f e)
    have hce : c * e * c⁻¹ = e := hsub ⟨c, Subgroup.subset_closure hc, rfl⟩
    show c * e = e * c
    calc c * e = c * e * c⁻¹ * c := by group
      _ = e * c := by rw [hce]
  have hsub : ∀ f ∈ D, ∀ e ∈ commSet D f, ∀ x ∈ D, Commute x f → Commute x e := by
    intro f hf e he x hx hxf
    by_cases hxf' : x = f
    · rw [hxf']
      exact he.2.1.symm
    · exact hcl f hf x ⟨hx, hxf, hxf'⟩ e he
  have hclosed : ∀ x ∈ {x | x ∈ D ∧ Commute x d}, ∀ y ∈ D, Commute x y →
      y ∈ {x | x ∈ D ∧ Commute x d} := by
    rintro x ⟨hx, hxd⟩ y hy hxy
    refine ⟨hy, ?_⟩
    by_cases hxd' : x = d
    · rw [← hxd']
      exact hxy.symm
    · exact hsub x hx d ⟨hd, hxd.symm, fun h => hxd' h.symm⟩ y hy hxy.symm
  have hall : ∀ y ∈ D, Commute y d := fun y hy =>
    (mem_of_reach hclosed ⟨hd, Commute.refl d⟩ (hconn d hd y hy)).2
  obtain ⟨e₀, he₀, -, -⟩ := hE
  have h1 : Subgroup.closure D ≤ Subgroup.centralizer {d} := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hall y hy).eq
  obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj hd he₀.1)
  have hcd := Subgroup.mem_centralizer_singleton_iff.mp (h1 (hS.gen ▸ Subgroup.mem_top c))
  apply he₀.2.2
  rw [← hc, hcd, mul_inv_cancel_right]

theorem exists_not_commute [Finite G] (hS : Setup G D) (hd : d ∈ D) (hE : IsMaxOrbit D d E)
    (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b) {e : G} (he : e ∈ E) :
    ∃ e' ∈ E, ¬ Commute e e' := by
  by_contra h
  push Not at h
  have hsub : E ⊆ {e} := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := orbitGen hS hE he x hx
    have h1 : Subgroup.closure E ≤ Subgroup.centralizer {e} := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h y hy).eq.symm
    have hke := Subgroup.mem_centralizer_singleton_iff.mp (h1 hk)
    show k * e * k⁻¹ = e
    rw [hke, mul_inv_cancel_right]
  have h1 := one_lt_ncard hS hd hE hconn
  have h2 : E.ncard ≤ 1 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    (Set.ncard_singleton e).le
  omega

theorem commute_of_mem_F (hS : Setup G D) (hE : IsMaxOrbit D d E) {f : G}
    (hf : f ∈ normSet D E \ E) {e : G} (he : e ∈ E) : Commute f e := by
  by_contra h
  have heD := subset_commSet hS.normal hE he
  exact hf.2 (mem_of_not_commute hS.oddT heD.1 hf.1.1 (fun h' => h h'.symm) he
    (mem_normalizer_of_mem_commSet hE heD) hf.1.2)

theorem mem_normSet_of_commute (hN : IsNormalSet D) (hE : IsMaxOrbit D d E) {c : G}
    (hc : c ∈ D) (hcd : Commute c d) : c ∈ normSet D E := by
  refine ⟨hc, ?_⟩
  by_cases h : c = d
  · rw [h]
    exact self_mem_normalizer hN hE
  · exact mem_normalizer_of_mem_commSet hE ⟨hc, hcd, h⟩

theorem self_mem_F (hN : IsNormalSet D) (hd : d ∈ D) (hE : IsMaxOrbit D d E) :
    d ∈ normSet D E \ E :=
  ⟨mem_normSet_of_commute hN hE hd (Commute.refl d), fun h => (subset_commSet hN hE h).2.2 rfl⟩

theorem mem_normSet_of_subset [Finite G] (hS : Setup G D) (hd : d ∈ D) (hE : IsMaxOrbit D d E)
    {f : G} (hf : f ∈ D) (hEf : E ⊆ commSet D f) {c : G} (hc : c ∈ D) (hcf : Commute c f) :
    c ∈ normSet D E := by
  obtain ⟨e₁, he₁⟩ := nonempty hE
  have hsub : E ⊆ orbitIn D f e₁ := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := orbitGen hS hE he₁ x hx
    exact ⟨k, Subgroup.closure_mono hEf hk, rfl⟩
  have heq : E = orbitIn D f e₁ :=
    Set.eq_of_subset_of_ncard_le hsub (ncard_orbitIn_le hS hd hE hf (hEf he₁)) (Set.toFinite _)
  refine ⟨hc, ?_⟩
  by_cases h : c = f
  · rw [h]
    exact mem_normalizer_of_commute fun x hx => (hEf hx).2.1.symm
  · rw [heq]
    exact closure_commSet_le_normalizer_orbitIn f e₁ (Subgroup.subset_closure ⟨hc, hcf, h⟩)

theorem mem_normSet_of_commute_F [Finite G] (hS : Setup G D) (hd : d ∈ D)
    (hE : IsMaxOrbit D d E) {f : G} (hf : f ∈ normSet D E \ E) {c : G} (hc : c ∈ D)
    (hcf : Commute c f) : c ∈ normSet D E :=
  mem_normSet_of_subset hS hd hE hf.1.1
    (fun _ he => ⟨(subset_commSet hS.normal hE he).1, (commute_of_mem_F hS hE hf he).symm,
      fun h => hf.2 (h ▸ he)⟩) hc hcf

theorem mem_normalizer_diff (hN : IsNormalSet D) {k : G} (hk : k ∈ Subgroup.normalizer E) :
    k ∈ Subgroup.normalizer (normSet D E \ E) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  have hD : y ∈ D ↔ k * y * k⁻¹ ∈ D := ⟨fun hy => hN k y hy, fun hy => by
    simpa [mul_assoc] using hN k⁻¹ _ hy⟩
  have hNy : y ∈ Subgroup.normalizer E ↔ k * y * k⁻¹ ∈ Subgroup.normalizer E := by
    constructor
    · intro hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hy) (Subgroup.inv_mem _ hk)
    · intro hy
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hk) hy) hk
      simpa [mul_assoc] using this
  have hEy := Subgroup.mem_set_normalizer_iff.mp hk y
  simp only [normSet, Set.mem_sdiff, Set.mem_ofPred_eq]
  rw [hD, hNy, hEy]

theorem subset_or_subset (hN : IsNormalSet D) {E' : Set G} {e' : G} (he' : e' ∈ E')
    (hE' : OrbitGen E' e') (hsub : E' ⊆ normSet D E) : E' ⊆ E ∨ E' ⊆ normSet D E \ E := by
  have hle : Subgroup.closure E' ≤ Subgroup.normalizer E := by
    rw [Subgroup.closure_le]
    exact fun k hk => (hsub hk).2
  by_cases h : e' ∈ E
  · left
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hE' x hx
    exact (Subgroup.mem_set_normalizer_iff.mp (hle hk) e').mp h
  · right
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hE' x hx
    exact (Subgroup.mem_set_normalizer_iff.mp (mem_normalizer_diff hN (hle hk)) e').mp
      ⟨hsub he', h⟩

end Orbit

section Block

variable [Finite G] (hS : Setup G D) {d : G} (hd : d ∈ D) {E : Set G} (hE : IsMaxOrbit D d E)
  (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b)
include hS hd hE

theorem conj_mem_F_of_not_mem {g : G} (hg : g ∉ Subgroup.normalizer (normSet D E \ E))
    {f : G} (hf : f ∈ normSet D E \ E) (hgf : g * f * g⁻¹ ∈ normSet D E \ E) {e : G}
    (he : e ∈ E) : g * e * g⁻¹ ∈ normSet D E \ E := by
  obtain ⟨e₀, he₀⟩ := nonempty hE
  have hsub : conjSet g E ⊆ normSet D E := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_normSet_of_commute_F hS hd hE hgf
      (hS.normal g y (subset_commSet hS.normal hE hy).1) ?_
    exact (commute_of_mem_F hS hE hf hy).symm.conj g
  rcases subset_or_subset hS.normal (conj_mem_conjSet he₀) ((orbitGen hS hE he₀).conj g)
    hsub with h | h
  ·
    exfalso
    apply hg
    have heq : conjSet g E = E :=
      Set.eq_of_subset_of_ncard_le h (ncard_conjSet g E).ge (Set.toFinite _)
    have hgE : g ∈ Subgroup.normalizer E := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← heq]
        exact conj_mem_conjSet hy
      · intro hy
        rw [← heq, mem_conjSet] at hy
        simpa [mul_assoc] using hy
    exact mem_normalizer_diff hS.normal hgE
  · exact h (conj_mem_conjSet he)

include hconn in
theorem mem_normalizer_F {g : G} {f : G} (hf : f ∈ normSet D E \ E)
    (hgf : g * f * g⁻¹ ∈ normSet D E \ E) : g ∈ Subgroup.normalizer (normSet D E \ E) := by
  by_contra hg
  have hg' : g⁻¹ ∉ Subgroup.normalizer (normSet D E \ E) := fun h =>
    hg (by simpa using Subgroup.inv_mem _ h)
  have hg'f : g⁻¹ * (g * f * g⁻¹) * g⁻¹⁻¹ ∈ normSet D E \ E := by simpa [mul_assoc] using hf
  have h1 : ∀ e ∈ E, g * e * g⁻¹ ∈ normSet D E \ E := fun e he =>
    conj_mem_F_of_not_mem hS hd hE hg hf hgf he
  have h2 : ∀ e ∈ E, g⁻¹ * e * g⁻¹⁻¹ ∈ normSet D E \ E := fun e he =>
    conj_mem_F_of_not_mem hS hd hE hg' hgf hg'f he
  obtain ⟨e₀, he₀⟩ := nonempty hE
  have hcover : ∀ (k : G), (∀ e ∈ E, k⁻¹ * e * k⁻¹⁻¹ ∈ normSet D E \ E) →
      ∀ x ∈ normSet D E, x ∈ normSet D E \ E ∨ k⁻¹ * x * k ∈ normSet D E \ E := by
    intro k hk x hx
    by_cases hxE : x ∈ E
    · right
      simpa using hk x hxE
    · exact Or.inl ⟨hx, hxE⟩
  have hFk : ∀ (k : G), (∀ e ∈ E, k * e * k⁻¹ ∈ normSet D E \ E) →
      ∀ y ∈ normSet D E \ E, k * y * k⁻¹ ∈ normSet D E := by
    intro k hk y hy
    exact mem_normSet_of_commute_F hS hd hE (hk e₀ he₀) (hS.normal k y hy.1.1)
      ((commute_of_mem_F hS hE hy he₀).conj k)
  have h1' : ∀ e ∈ E, g⁻¹⁻¹ * e * g⁻¹⁻¹⁻¹ ∈ normSet D E \ E := by simpa using h1
  have hinv : ∀ x ∈ normSet D E, g * x * g⁻¹ ∈ normSet D E := by
    intro x hx
    rcases hcover g⁻¹ h1' x hx with h | h
    · exact hFk g h1 x h
    · simpa using h.1
  have hclosed : ∀ a ∈ normSet D E, ∀ c ∈ D, Commute a c → c ∈ normSet D E := by
    intro a ha c hc hac
    rcases hcover g (by simpa using h2) a ha with h | h
    · exact mem_normSet_of_commute_F hS hd hE h hc hac.symm
    · have hc' : g⁻¹ * c * g ∈ normSet D E := by
        refine mem_normSet_of_commute_F hS hd hE h (by simpa using hS.normal g⁻¹ c hc) ?_
        simpa [mul_assoc] using (hac.symm.conj g⁻¹)
      have := hinv _ hc'
      simpa [mul_assoc] using this
  have hall : ∀ y ∈ D, y ∈ normSet D E := fun y hy =>
    mem_of_reach hclosed (self_mem_F hS.normal hd hE).1 (hconn d hd y hy)
  have htop : Subgroup.closure D ≤ Subgroup.normalizer E := by
    rw [Subgroup.closure_le]
    exact fun y hy => (hall y hy).2
  obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj (subset_commSet hS.normal hE he₀).1 hd)
  have hcN := htop (hS.gen ▸ Subgroup.mem_top c)
  have hdE : d ∈ E := by
    rw [← hc]
    exact (Subgroup.mem_set_normalizer_iff.mp hcN e₀).mp he₀
  exact (subset_commSet hS.normal hE hdE).2.2 rfl

end Block

end OddLocal

open OddLocal in
theorem isMaxBlock_normSet_diff [Finite G] (hS : Setup G D)
    (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b) {d : G} (hd : d ∈ D) {E : Set G}
    (hE : IsMaxOrbit D d E) : IsMaxBlock D (normSet D E \ E) := by
  obtain ⟨e₀, he₀⟩ := nonempty hE
  refine ⟨⟨d, self_mem_F hS.normal hd hE⟩, fun x hx => hx.1.1, fun h => ?_, ?_, ?_⟩
  · have : e₀ ∈ normSet D E \ E := by rw [h]; exact (subset_commSet hS.normal hE he₀).1
    exact this.2 he₀
  · rw [isBlock_conj_iff]
    intro g a ha hga
    exact mem_normalizer_F hS hd hE hconn ha hga
  · intro L hFL hLD hLne hL
    rw [isBlock_conj_iff] at hL
    have hdL : d ∈ L := hFL (self_mem_F hS.normal hd hE)
    have hnL : ∀ c ∈ commSet D d, c ∈ Subgroup.normalizer L := fun c hc =>
      hL c d hdL (by rw [hc.2.1.eq, mul_inv_cancel_right]; exact hdL)
    have hselfL : ∀ ℓ ∈ L, ℓ ∈ Subgroup.normalizer L := fun ℓ hℓ =>
      hL ℓ ℓ hℓ (by rw [mul_inv_cancel_right]; exact hℓ)
    have hEL : ∀ e ∈ E, e ∉ L := by
      intro e he heL
      have hEsub : E ⊆ L := by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := orbitGen hS hE he x hx
        have hle : Subgroup.closure E ≤ Subgroup.normalizer L := by
          rw [Subgroup.closure_le]
          exact fun y hy => hnL y (subset_commSet hS.normal hE hy)
        exact (Subgroup.mem_set_normalizer_iff.mp (hle hk) e).mp heL
      have hCd : ∀ c ∈ D, Commute c d → c ∈ L := by
        intro c hc hcd
        by_cases hcE : c ∈ E
        · exact hEsub hcE
        · exact hFL ⟨mem_normSet_of_commute hS.normal hE hc hcd, hcE⟩
      have hclosed : ∀ ℓ ∈ L, ∀ c ∈ D, Commute ℓ c → c ∈ L := by
        intro ℓ hℓ c hc hℓc
        obtain ⟨k, rfl⟩ := isConj_iff.mp (hS.isConj hd (hLD hℓ))
        have hkL : k ∈ Subgroup.normalizer L := hL k d hdL hℓ
        have hc' : k⁻¹ * c * k ∈ L := by
          apply hCd _ (by simpa using hS.normal k⁻¹ c hc)
          have := hℓc.symm.conj k⁻¹
          simpa [mul_assoc] using this
        have := (Subgroup.mem_set_normalizer_iff.mp hkL _).mp hc'
        simpa [mul_assoc] using this
      apply hLne
      apply Set.Subset.antisymm hLD
      intro y hy
      exact mem_of_reach hclosed hdL (hconn d hd y hy)
    apply Set.Subset.antisymm _ hFL
    intro ℓ hℓ
    have hcomm : ∀ e ∈ E, Commute ℓ e := by
      intro e he
      by_contra h
      exact hEL e he (mem_of_not_commute hS.oddT (hLD hℓ) (subset_commSet hS.normal hE he).1 h
        hℓ (hselfL ℓ hℓ) (hnL e (subset_commSet hS.normal hE he)))
    refine ⟨⟨hLD hℓ, mem_normalizer_of_commute hcomm⟩, fun hℓE => ?_⟩
    obtain ⟨e', he', h⟩ := exists_not_commute hS hd hE hconn hℓE
    exact h (hcomm e' he')

end CFSG.Timmesfeld.Bridge
