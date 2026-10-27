module

public import CFSG.Quasithin.Background.G12Rad
public import CFSG.ClassicalGroups.Alternating.Generation

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}

@[expose] def orbitSet (Γ : Subgroup (GLV V)) (v : V) : Set V := {w | ∃ g ∈ Γ, w = g v}

theorem mem_orbitSet_self {v : V} : v ∈ orbitSet Γ v := ⟨1, Γ.one_mem, rfl⟩

theorem orbitSet_apply_mem {v : V} {g : GLV V} (hg : g ∈ Γ) {w : V} (hw : w ∈ orbitSet Γ v) :
    g w ∈ orbitSet Γ v := by
  obtain ⟨h, hh, rfl⟩ := hw
  exact ⟨g * h, Γ.mul_mem hg hh, rfl⟩

theorem orbitSet_ne_zero {v : V} (hv : v ≠ 0) {w : V} (hw : w ∈ orbitSet Γ v) : w ≠ 0 := by
  obtain ⟨g, -, rfl⟩ := hw
  intro h
  apply hv
  simpa using h

section Fin

variable [Finite V]

theorem exists_fix_move (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {v : V} (hv : IsStarVec B Γ v)
    {y y' : V} (hy : B y v = 1) (hy' : B y' v = 1) :
    ∃ g ∈ Γ, g v = v ∧ (g y = y' ∨ g y = y' + v) := by
  have hv' := (isStarVec_iff_rad hB hΓ).1 hv
  have hva : B v (y + y') = 0 := by
    rw [map_add, hB.symm' v y, hB.symm' v y', hy, hy']; decide
  obtain ⟨c, hc⟩ := hv'.2 _ hva
  refine ⟨radE B v (y + y') c, hc, radE_apply_v hB hva, ?_⟩
  rw [radE_apply hB hva, hy, one_smul, mul_one]
  have e : y + (y + y') = y' := by
    rw [← add_assoc, g12_vadd_self, zero_add]
  rcases g12_eq_zero_or_one (B y (y + y') + c) with h0 | h1
  · left
    rw [h0, zero_smul, add_zero, e]
  · right
    rw [h1, one_smul, e]

theorem exists_move_perp (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {v : V} (hv : IsStarVec B Γ v)
    {w : V} (hw : B v w = 0) (hw0 : w ≠ 0) (hwv : w ≠ v) :
    ∃ g ∈ Γ, g v = v ∧ g w = w + v := by
  have hv' := (isStarVec_iff_rad hB hΓ).1 hv
  obtain ⟨a, hva, hwa⟩ := hB.exists_perp_one hw0 (Ne.symm hwv)
  obtain ⟨c, hc⟩ := hv'.2 a hva
  refine ⟨radE B v a c, hc, radE_apply_v hB hva, ?_⟩
  rw [radE_apply hB hva]
  have hwv' : B w v = 0 := by rw [hB.symm']; exact hw
  rw [hwv', hwa]
  simp

theorem exists_B_ne (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {u v : V} (hu : IsStarVec B Γ u)
    (huv : B u v = 1) (hd : 4 ≤ Module.finrank (ZMod 2) V) : ∃ g ∈ Γ, B (g v) v = 1 := by
  by_contra H
  simp only [not_exists, not_and] at H
  have hvu : B v u = 1 := by rw [hB.symm']; exact huv
  have H1 : ∀ a, B u a = 0 → ∀ c, radE B u a c ∈ Γ → c = 0 := by
    intro a hua c hc
    have h1 := H _ hc
    have e : B (radE B u a c v) v = c := by
      rw [radE_apply hB hua]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvu,
        huv, hB.1 v, one_mul, mul_one, zero_add]
      rw [hB.symm' a v]
      have h2 := g12_add_self (B v a)
      calc B v a + (B v a + c) = (B v a + B v a) + c := by rw [add_assoc]
        _ = c := by rw [h2, zero_add]
    rw [e] at h1
    rcases g12_eq_zero_or_one c with h0 | h0
    · exact h0
    · exact absurd h0 h1
  have hu0 : u ≠ 0 := fun h => by rw [h] at huv; simp at huv
  have hex : ∃ e, B u e = 0 ∧ e ≠ 0 ∧ e ≠ u := by
    by_contra hne
    simp only [not_exists, not_and, not_not] at hne
    have hle : perp B u ≤ Submodule.span (ZMod 2) {u} := by
      intro x hx
      rw [Submodule.mem_span_singleton]
      by_cases hx0 : x = 0
      · exact ⟨0, by simp [hx0]⟩
      · exact ⟨1, by rw [one_smul]; exact (hne x (mem_perp_iff.1 hx) hx0).symm⟩
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0] at h1
    have h2 := hB.finrank_perp hu0
    omega
  obtain ⟨e, hue, he0, heu⟩ := hex
  obtain ⟨a2, hua2, hea2⟩ := hB.exists_perp_one (v := u) (w := e) he0 (Ne.symm heu)
  have hu' := (isStarVec_iff_rad hB hΓ).1 hu
  obtain ⟨c1, hc1⟩ := hu'.2 e hue
  obtain ⟨c2, hc2⟩ := hu'.2 a2 hua2
  have h1 := H1 e hue c1 hc1
  have h2 := H1 a2 hua2 c2 hc2
  subst h1 h2
  have hprod := Γ.mul_mem hc1 hc2
  rw [radE_mul hB hue hua2] at hprod
  have hmem : B u (e + a2) = 0 := by rw [map_add, hue, hua2, add_zero]
  have := H1 (e + a2) hmem _ hprod
  rw [hea2] at this
  exact absurd this (by decide)

theorem span_orbit_eq_top (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {u v : V}
    (hv : IsStarVec B Γ v) (hu : IsStarVec B Γ u) (huv : B u v = 1)
    (hd : 4 ≤ Module.finrank (ZMod 2) V) : Submodule.span (ZMod 2) (orbitSet Γ v) = ⊤ := by
  obtain ⟨g0, hg0, hg0v⟩ := exists_B_ne hB hΓ hu huv hd
  obtain ⟨x0, hx0mem, hx0B⟩ : ∃ x0 ∈ orbitSet Γ v, B x0 v = 1 := ⟨g0 v, ⟨g0, hg0, rfl⟩, hg0v⟩
  have hv' := (isStarVec_iff_rad hB hΓ).1 hv
  have hS0 : ∀ w ∈ orbitSet Γ v, w ∈ Submodule.span (ZMod 2) (orbitSet Γ v) :=
    fun w hw => Submodule.subset_span hw
  have hperp : ∀ z, B v z = 0 → z ∈ Submodule.span (ZMod 2) (orbitSet Γ v) := by
    intro z hz
    obtain ⟨c, hc⟩ := hv'.2 z hz
    have h1 : radE B v z c x0 ∈ orbitSet Γ v := orbitSet_apply_mem hc hx0mem
    rw [radE_apply hB hz, hx0B, one_smul, mul_one] at h1
    have h2 := hS0 _ h1
    have h3 := hS0 _ hx0mem
    have h4 := hS0 _ (mem_orbitSet_self (Γ := Γ) (v := v))
    have h5 : z = (x0 + z + (B x0 z + c) • v) + x0 + (B x0 z + c) • v := by
      have e1 := g12_vadd_self x0
      have e2 := g12_vadd_self ((B x0 z + c) • v)
      calc z = (x0 + x0) + z + ((B x0 z + c) • v + (B x0 z + c) • v) := by rw [e1, e2]; abel
        _ = _ := by abel
    rw [h5]
    exact Submodule.add_mem _ (Submodule.add_mem _ h2 h3) (Submodule.smul_mem _ _ h4)
  rw [eq_top_iff]
  intro x _
  have hx0v : B v x0 = 1 := by rw [hB.symm']; exact hx0B
  rcases g12_eq_zero_or_one (B v x) with h0 | h1
  · exact hperp x h0
  · have : x + x0 ∈ Submodule.span (ZMod 2) (orbitSet Γ v) := by
      apply hperp
      rw [map_add, h1, hx0v]; decide
    have h3 := hS0 _ hx0mem
    have e : x = (x + x0) + x0 := by
      rw [add_assoc, g12_vadd_self, add_zero]
    rw [e]
    exact Submodule.add_mem _ this h3

omit [Finite V] in
theorem orbit_eq_of_far (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {v : V} (hv0 : v ≠ 0)
    (hfar : ∀ y, B y v = 1 → y ∈ orbitSet Γ v) : ∀ x, x ≠ 0 → x ∈ orbitSet Γ v := by
  intro x hx0
  rcases g12_eq_zero_or_one (B x v) with h0 | h1
  · by_cases hxv : x = v
    · rw [hxv]; exact mem_orbitSet_self
    · obtain ⟨y, hy1, hy2⟩ := hB.exists_B_eq_one_one hv0 hx0
      obtain ⟨h, hh, hyv⟩ := hfar y hy1
      have hiso : ∀ a b, B (h a) (h b) = B a b := fun a b => hΓ hh a b
      have hhx : B (h.symm x) v = 1 := by
        have := hiso (h.symm x) v
        rw [LinearEquiv.apply_symm_apply, ← hyv, hB.symm' x y, hy2] at this
        exact this.symm
      obtain ⟨k, hk, hkx⟩ := hfar _ hhx
      refine ⟨h * k, Γ.mul_mem hh hk, ?_⟩
      show x = h (k v)
      rw [← hkx, LinearEquiv.apply_symm_apply]
  · exact hfar x h1
open CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial in
theorem spSub_le_closure_tv (hB : IsSymplectic B) :
    spSub B ≤ Subgroup.closure {g | ∃ x, g = radE B x 0 1} := by
  have hAlt : B.IsAlt := hB.1
  let ψ := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  intro g hg
  have hg' : ψ.symm g ∈ bilinIsometryGroup B := by
    intro x y
    have h1 : ((ψ.symm g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = g := by
      have := LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (R := ZMod 2) (M := V)
        (ψ.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h1]
    exact hg x y
  rw [alternating_transvection_generation hAlt hB.nondegenerate] at hg'
  have hmem : g ∈ (Subgroup.closure {t : LinearMap.GeneralLinearGroup (ZMod 2) V |
      ∃ (a : V) (c : ZMod 2), t = symplecticTransvection B hAlt a c}).map ψ.toMonoidHom :=
    ⟨ψ.symm g, hg', by simp⟩
  rw [MonoidHom.map_closure] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨t, ⟨a, c, rfl⟩, rfl⟩
  have key : ψ (symplecticTransvection B hAlt a c) = radE B a 0 c := by
    refine LinearEquiv.ext fun x => ?_
    rw [radE_zero_apply hB]
    exact symplecticTransvection_apply hAlt a c x
  show ψ (symplecticTransvection B hAlt a c) ∈ {g | ∃ x, g = radE B x 0 1}
  rw [key]
  rcases g12_eq_zero_or_one c with h0 | h1
  · refine ⟨0, ?_⟩
    rw [h0, radE_zero_zero hB]
    refine LinearEquiv.ext fun x => ?_
    rw [radE_one_apply hB]
    simp
  · exact ⟨a, by rw [h1]⟩


theorem eq_spSub_of_tv_mem (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {u v : V}
    (hv : IsStarVec B Γ v) (hu : IsStarVec B Γ u) (huv : B u v = 1)
    (hd : 4 ≤ Module.finrank (ZMod 2) V) (htv : radE B v 0 1 ∈ Γ) : Γ = spSub B := by
  have hv0 : v ≠ 0 := ((isStarVec_iff_rad hB hΓ).1 hv).1
  obtain ⟨g0, hg0, hg0v⟩ := exists_B_ne hB hΓ hu huv hd
  have hfar : ∀ y, B y v = 1 → y ∈ orbitSet Γ v := by
    intro y hy
    obtain ⟨g, hg, hgv, hgy⟩ := exists_fix_move hB hΓ hv hg0v hy
    rcases hgy with h1 | h1
    · exact ⟨g * g0, Γ.mul_mem hg hg0, by show y = g (g0 v); rw [h1]⟩
    · refine ⟨radE B v 0 1 * g * g0, Γ.mul_mem (Γ.mul_mem htv hg) hg0, ?_⟩
      show y = radE B v 0 1 (g (g0 v))
      rw [h1, radE_one_apply hB]
      have hb : B (y + v) v = 1 := by
        rw [map_add, LinearMap.add_apply, hy, hB.1 v]; decide
      rw [hb, one_smul, add_assoc, g12_vadd_self, add_zero]
  have hall := orbit_eq_of_far hB hΓ hv0 hfar
  apply le_antisymm hΓ
  refine (spSub_le_closure_tv hB).trans ((Subgroup.closure_le Γ).2 ?_)
  rintro _ ⟨x, rfl⟩
  by_cases hx : x = 0
  · subst hx
    have h1 : radE B 0 0 1 = 1 := by
      refine LinearEquiv.ext fun z => ?_
      rw [radE_one_apply hB]
      simp
    rw [h1]
    exact Γ.one_mem
  · obtain ⟨g, hg, rfl⟩ := hall x hx
    have := radE_conj_mem hB hΓ hg (v := v) (a := 0) (c := 1) (by simp) htv
    rwa [map_zero] at this

theorem exists_quadratic_of_nontransitive (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {u v : V}
    (hv : IsStarVec B Γ v) (hu : IsStarVec B Γ u) (huv : B u v = 1)
    (hd : 4 ≤ Module.finrank (ZMod 2) V) (hnt : ∃ x, x ≠ 0 ∧ x ∉ orbitSet Γ v) :
    ∃ q : V → ZMod 2, (∀ x y, q (x + y) = q x + q y + B x y) ∧ Γ ≤ orthSub q ∧ q v = 0 ∧
      ∀ w, w ∈ orbitSet Γ v ↔ (w ≠ 0 ∧ q w = 0) := by
  classical
  have hv0 : v ≠ 0 := ((isStarVec_iff_rad hB hΓ).1 hv).1
  let q : V → ZMod 2 := fun y => if y = 0 ∨ y ∈ orbitSet Γ v then 0 else 1
  have hq0 : q 0 = 0 := by simp [q]
  have hqorb : ∀ y ∈ orbitSet Γ v, q y = 0 := fun y hy => by simp [q, hy]
  have hqn : ∀ y, y ≠ 0 → y ∉ orbitSet Γ v → q y = 1 := fun y h1 h2 => by simp [q, h1, h2]
  have hqz : ∀ y, y ≠ 0 → q y = 0 → y ∈ orbitSet Γ v := by
    intro y h1 h2
    by_contra h3
    have := hqn y h1 h3
    rw [h2] at this
    exact absurd this (by decide)
  have hinv : ∀ g ∈ Γ, ∀ y, q (g y) = q y := by
    intro g hg y
    have h1 : (g y = 0 ∨ g y ∈ orbitSet Γ v) ↔ (y = 0 ∨ y ∈ orbitSet Γ v) := by
      constructor
      · rintro (h | h)
        · left
          simpa using h
        · right
          have := orbitSet_apply_mem (Γ.inv_mem hg) h
          simpa using this
      · rintro (h | h)
        · left; rw [h]; exact map_zero g
        · right; exact orbitSet_apply_mem hg h
    simp only [q]
    exact if_congr h1 rfl rfl
  have hd1 : ∀ y, q (v + y) = q y + B v y := by
    intro y
    rcases g12_eq_zero_or_one (B v y) with h0 | h1
    · rw [h0, add_zero]
      by_cases hy0 : y = 0
      · rw [hy0, add_zero, hq0, hqorb v mem_orbitSet_self]
      · by_cases hyv : y = v
        · rw [hyv, g12_vadd_self, hq0, hqorb v mem_orbitSet_self]
        · obtain ⟨g, hg, hgv, hgy⟩ := exists_move_perp hB hΓ hv h0 hy0 hyv
          rw [add_comm, ← hgy]
          exact hinv g hg y
    · have hyv1 : B y v = 1 := by rw [hB.symm']; exact h1
      have hy0 : y ≠ 0 := fun h => by rw [h] at hyv1; simp at hyv1
      have hvy0 : v + y ≠ 0 := by
        intro h
        have : B v (v + y) = 1 := by rw [map_add, hB.1 v, h1]; simp
        rw [h] at this; simp at this
      obtain ⟨g0, hg0, hg0v⟩ := exists_B_ne hB hΓ hu huv hd
      have hone : y ∈ orbitSet Γ v ∨ y + v ∈ orbitSet Γ v := by
        obtain ⟨g, hg, hgv, hgy⟩ := exists_fix_move hB hΓ hv hyv1 hg0v
        rcases hgy with h2 | h2
        · left
          have := orbitSet_apply_mem (Γ.inv_mem hg) (⟨g0, hg0, rfl⟩ : g0 v ∈ orbitSet Γ v)
          rw [← h2] at this
          simpa using this
        · right
          have := orbitSet_apply_mem (Γ.inv_mem hg) (⟨g0, hg0, rfl⟩ : g0 v ∈ orbitSet Γ v)
          have e : g (y + v) = g0 v := by
            rw [map_add, h2, hgv, add_assoc, g12_vadd_self, add_zero]
          rw [← e] at this
          simpa using this
      have hnot : ¬ (y ∈ orbitSet Γ v ∧ y + v ∈ orbitSet Γ v) := by
        rintro ⟨hy1, hy2⟩
        obtain ⟨x, hx0, hxn⟩ := hnt
        apply hxn
        refine orbit_eq_of_far hB hΓ hv0 (fun z hz => ?_) x hx0
        obtain ⟨g, hg, hgv, hgy⟩ := exists_fix_move hB hΓ hv hyv1 hz
        rcases hgy with h2 | h2
        · rw [← h2]; exact orbitSet_apply_mem hg hy1
        · have e : z = g (y + v) := by
            rw [map_add, h2, hgv, add_assoc, g12_vadd_self, add_zero]
          rw [e]; exact orbitSet_apply_mem hg hy2
      rw [h1, add_comm v y]
      have hyv0 : y + v ≠ 0 := by rw [add_comm]; exact hvy0
      by_cases hmy : y ∈ orbitSet Γ v
      · have hn : y + v ∉ orbitSet Γ v := fun h => hnot ⟨hmy, h⟩
        rw [hqorb y hmy, hqn _ hyv0 hn]; decide
      · have hm2 : y + v ∈ orbitSet Γ v := hone.resolve_left hmy
        rw [hqn y hy0 hmy, hqorb _ hm2]; decide
  have he : ∀ x ∈ orbitSet Γ v, ∀ y, q (x + y) = q y + B x y := by
    rintro _ ⟨g, hg, rfl⟩ y
    have hgi : ∀ a b, B (g a) (g b) = B a b := fun a b => hΓ hg a b
    have e1 : g v + y = g (v + g.symm y) := by
      rw [map_add, LinearEquiv.apply_symm_apply]
    have h2 : q (g.symm y) = q y := hinv g⁻¹ (Γ.inv_mem hg) y
    rw [e1, hinv g hg, hd1, h2, ← hgi v (g.symm y), LinearEquiv.apply_symm_apply]
  have hspan := span_orbit_eq_top hB hΓ hv hu huv hd
  have hP : ∀ a ∈ Submodule.span (ZMod 2) (orbitSet Γ v), ∀ y, q (a + y) = q a + q y + B a y := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      intro y
      rw [he x hx y, hqorb x hx, zero_add]
    | zero =>
      intro y
      rw [zero_add, hq0, map_zero, LinearMap.zero_apply, zero_add, add_zero]
    | add a b _ _ ha hb =>
      intro y
      rw [add_assoc, ha (b + y), hb y, ha b]
      simp only [map_add, LinearMap.add_apply]
      ring
    | smul c a _ ha =>
      intro y
      rcases g12_eq_zero_or_one c with h0 | h1
      · rw [h0, zero_smul, zero_add, hq0, map_zero, LinearMap.zero_apply, zero_add, add_zero]
      · rw [h1, one_smul]; exact ha y
  refine ⟨q, fun x y => hP x (by rw [hspan]; trivial) y, fun g hg x => hinv g hg x,
    hqorb v mem_orbitSet_self, fun w => ⟨fun hw => ⟨orbitSet_ne_zero hv0 hw, hqorb w hw⟩,
      fun ⟨h1, h2⟩ => hqz w h1 h2⟩⟩


theorem g12_eq_zero_of_eq_add : ∀ a c : ZMod 2, a = a + c → c = 0 := by decide

theorem exists_orth_pair (hB : IsSymplectic B) (hd : 5 ≤ Module.finrank (ZMod 2) V) (z w : V) :
    ∃ x a, B z x = 0 ∧ B w x = 0 ∧ B z a = 0 ∧ B w a = 0 ∧ B x a = 1 := by
  classical
  let S : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {z, w}
  have hS : Module.finrank (ZMod 2) S ≤ 2 := by
    have h1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑({z, w} : Finset V) : Set V)) ≤
        ({z, w} : Finset V).card := finrank_span_finset_le_card _
    have h2 : ({z, w} : Finset V).card ≤ 2 := Finset.card_le_two
    have h3 : (↑({z, w} : Finset V) : Set V) = {z, w} := by simp
    rw [h3] at h1
    have e : Module.finrank (ZMod 2) S =
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {z, w}) := rfl
    omega
  have hU : Module.finrank (ZMod 2) (B.orthogonal S) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) S :=
    LinearMap.BilinForm.finrank_orthogonal hB.nondegenerate S
  have hnle : ¬ B.orthogonal S ≤ S := by
    intro hle
    have := Submodule.finrank_mono hle
    omega
  obtain ⟨x, hxU, hxS⟩ : ∃ x, x ∈ B.orthogonal S ∧ x ∉ S := by
    by_contra hcon
    apply hnle
    intro x hx
    by_contra hxS
    exact hcon ⟨x, hx, hxS⟩
  have hSS : B.orthogonal (B.orthogonal S) = S :=
    LinearMap.BilinForm.orthogonal_orthogonal hB.nondegenerate hB.isRefl S
  rw [← hSS, LinearMap.BilinForm.mem_orthogonal_iff] at hxS
  simp only [not_forall] at hxS
  obtain ⟨a, haU, ha⟩ := hxS
  have hzS : z ∈ S := Submodule.subset_span (by simp)
  have hwS : w ∈ S := Submodule.subset_span (by simp)
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxU haU
  refine ⟨x, a, hxU z hzS, hxU w hwS, haU z hzS, haU w hwS, ?_⟩
  rw [hB.symm']
  exact g12_eq_one_of_ne_zero _ ha

theorem big_zero_of_mem (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) (hd : 5 ≤ Module.finrank (ZMod 2) V)
    (hstar : ∀ w, w ≠ 0 → IsStarVec B Γ w) (htv : ∀ w, w ≠ 0 → radE B w 0 1 ∉ Γ)
    {w : V} (hw0 : w ≠ 0) {z : V} (hwz : B w z = 0) (hz0 : z ≠ 0)
    {c : ZMod 2} (hc : radE B w z c ∈ Γ) : c = 0 := by
  obtain ⟨x, a, hzx, hwx, hza, hwa, hxa⟩ := exists_orth_pair hB hd z w
  obtain ⟨cx, hcx⟩ := ((isStarVec_iff_rad hB hΓ).1 (hstar w hw0)).2 x hwx
  obtain ⟨c', hc'⟩ := ((isStarVec_iff_rad hB hΓ).1 (hstar z hz0)).2 a hza
  have hxz : B x z = 0 := by rw [hB.symm']; exact hzx
  have hgw : radE B z a c' w = w := by
    rw [radE_apply hB hza, hwz, hwa]
    simp
  have hgx : radE B z a c' x = x + z := by
    rw [radE_apply hB hza, hxz, hxa]
    simp
  have h1 := radE_conj_mem hB hΓ hc' hwx hcx
  rw [hgw, hgx] at h1
  have h2 := Γ.mul_mem hcx hc
  rw [radE_mul hB hwx hwz, hxz, add_zero] at h2
  have hmem : B w (x + z) = 0 := by rw [map_add, hwx, hwz, add_zero]
  have h3 := radE_unique hB hmem (htv w hw0) h1 h2
  exact g12_eq_zero_of_eq_add _ _ h3

theorem false_of_all_star_no_tv (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B)
    (hd : 5 ≤ Module.finrank (ZMod 2) V) (hstar : ∀ w, w ≠ 0 → IsStarVec B Γ w)
    (htv : ∀ w, w ≠ 0 → radE B w 0 1 ∉ Γ) {w : V} (hw0 : w ≠ 0) : False := by
  obtain ⟨x, a, hz0x, hwx, hz0a, hwa, hxa⟩ := exists_orth_pair hB hd w w
  obtain ⟨cx, hcx⟩ := ((isStarVec_iff_rad hB hΓ).1 (hstar w hw0)).2 x hwx
  obtain ⟨ca, hca⟩ := ((isStarVec_iff_rad hB hΓ).1 (hstar w hw0)).2 a hwa
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero, LinearMap.zero_apply] at hxa; exact absurd hxa (by decide)
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at hxa; exact absurd hxa (by decide)
  have hxa0 : x + a ≠ 0 := by
    intro h
    have : x = a := by
      calc x = x + (a + a) := by rw [g12_vadd_self, add_zero]
        _ = (x + a) + a := by rw [add_assoc]
        _ = a := by rw [h, zero_add]
    rw [this, hB.1 a] at hxa
    exact absurd hxa (by decide)
  have hcx0 := big_zero_of_mem hB hΓ hd hstar htv hw0 hwx hx0 hcx
  have hca0 := big_zero_of_mem hB hΓ hd hstar htv hw0 hwa ha0 hca
  have hprod := Γ.mul_mem hcx hca
  rw [radE_mul hB hwx hwa, hcx0, hca0, hxa] at hprod
  have hmem : B w (x + a) = 0 := by rw [map_add, hwx, hwa, add_zero]
  have := big_zero_of_mem hB hΓ hd hstar htv hw0 hmem hxa0 hprod
  exact absurd this (by decide)


end Fin

end NoInst

end CFSG.Quasithin.G11
