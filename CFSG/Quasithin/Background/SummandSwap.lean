module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

namespace SummandSwap

variable {V : Type*} [CommGroup V]

variable {A : Subgroup (MulAut V)} {I : Subgroup V} {a : MulAut V}

theorem aut_sq_apply (hAe : IsElemAbelian2 A) (haA : a ∈ A) (x : V) : a (a x) = x := by
  have h : a * a = 1 := by rw [← pow_two]; exact hAe.2 a haA
  exact congrArg (fun φ : MulAut V => φ x) h

theorem aut_comm_apply (hAe : IsElemAbelian2 A) {g h : MulAut V} (hg : g ∈ A)
    (hh : h ∈ A) (x : V) : g (h x) = h (g x) :=
  congrArg (fun φ : MulAut V => φ x) (hAe.1 g hg h hh)

theorem aut_inv_eq (hAe : IsElemAbelian2 A) (haA : a ∈ A) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hAe.2 a haA)

theorem diag_injOn (hdisj : Disjoint I (I.map a.toMonoidHom)) :
    Set.InjOn (fun x : V => x * a x) (I : Set V) := by
  intro x hx y hy hxy
  have hxy' : x * a x = y * a y := hxy
  have ht : x * y⁻¹ ∈ I := I.mul_mem hx (I.inv_mem hy)
  have h1 : (x * y⁻¹) * a (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_mul_mul_comm, ← mul_inv, hxy', mul_inv_cancel]
  have := (Subgroup.disjoint_iff_mul_eq_one.mp hdisj ht
    (Subgroup.mem_map_of_mem a.toMonoidHom ht) h1).1
  exact mul_inv_eq_one.mp this

theorem exists_diag_of_fixed (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (hdisj : Disjoint I (I.map a.toMonoidHom)) {u : V} (hu : u ∈ I ⊔ I.map a.toMonoidHom)
    (hau : a u = u) : ∃ y ∈ I, y * a y = u := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  have h1 : a y * w = y * a w := by
    have := hau
    rw [map_mul] at this
    have e : a (a w) = w := aut_sq_apply hAe haA w
    simpa [e] using this
  have ht : y * w⁻¹ ∈ I := I.mul_mem hy (I.inv_mem hw)
  have h2 : a (y * w⁻¹) = y * w⁻¹ := by
    rw [map_mul, map_inv]
    have := div_eq_div_iff_mul_eq_mul.mpr h1
    simpa only [div_eq_mul_inv] using this
  have h3 : y * w⁻¹ ∈ I.map a.toMonoidHom := by
    have := Subgroup.mem_map_of_mem a.toMonoidHom ht
    have e : a.toMonoidHom (y * w⁻¹) = y * w⁻¹ := h2
    rwa [e] at this
  have h4 : y * w⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj ht h3
  have h5 : y = w := mul_inv_eq_one.mp h4
  subst h5
  exact ⟨y, hy, rfl⟩

theorem diag_mem_fixV (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (hcos : ∀ g ∈ A, g ∈ stabSub I ∨ a⁻¹ * g ∈ stabSub I) {x : V}
    (hx : x ∈ fixV (A ⊓ stabSub I)) : x * a x ∈ fixV A := by
  have ha1 := aut_inv_eq hAe haA
  have h0 : ∀ g ∈ A, g ∈ stabSub I → g (x * a x) = x * a x := by
    intro g hg hgs
    have hgx : g x = x := mem_fixV.mp hx g ⟨hg, hgs⟩
    rw [map_mul, aut_comm_apply hAe hg haA, hgx]
  intro g hg
  rcases hcos g hg with h | h
  · exact h0 g hg h
  · rw [ha1] at h
    have h1 : (a * g) (x * a x) = x * a x := h0 (a * g) (A.mul_mem haA hg) h
    have h2 : g (x * a x) = a ((a * g) (x * a x)) := by
      show g (x * a x) = a (a (g (x * a x)))
      rw [aut_sq_apply hAe haA]
    rw [h2, h1, map_mul, aut_sq_apply hAe haA, mul_comm]

theorem diag_image_eq (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (hdisj : Disjoint I (I.map a.toMonoidHom))
    (hcos : ∀ g ∈ A, g ∈ stabSub I ∨ a⁻¹ * g ∈ stabSub I) :
    (fun x : V => x * a x) '' ((I ⊓ fixV (A ⊓ stabSub I) : Subgroup V) : Set V) =
      (((I ⊔ I.map a.toMonoidHom) ⊓ fixV A : Subgroup V) : Set V) := by
  ext u
  constructor
  · rintro ⟨x, ⟨hxI, hxB⟩, rfl⟩
    exact ⟨Subgroup.mem_sup.mpr ⟨x, hxI, a x, Subgroup.mem_map_of_mem a.toMonoidHom hxI, rfl⟩,
      diag_mem_fixV hAe haA hcos hxB⟩
  · rintro ⟨hu, hfix⟩
    obtain ⟨y, hy, rfl⟩ := exists_diag_of_fixed hAe haA hdisj hu (hfix a haA)
    refine ⟨y, ⟨hy, fun b hb => ?_⟩, rfl⟩
    have h1 := hfix b hb.1
    rw [map_mul, aut_comm_apply hAe hb.1 haA] at h1
    have hby : b y ∈ I := (mem_stabSub.mp hb.2 y).mpr hy
    exact diag_injOn hdisj hby hy h1

omit [CommGroup V] in
theorem relIndex_le_of_cover {G : Type*} [Group G] {H K : Subgroup G} {n : ℕ}
    (r : Fin n → G) (hr : ∀ m, r m ∈ K) (h : ∀ g ∈ K, ∃ m, (r m)⁻¹ * g ∈ H) :
    H.relIndex K ≤ n := by
  classical
  have hsurj : Function.Surjective
      (fun m : Fin n => (QuotientGroup.mk (⟨r m, hr m⟩ : K) : K ⧸ H.subgroupOf K)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨m, hm⟩ := h g g.2
      refine ⟨m, ?_⟩
      simpa [QuotientGroup.eq, Subgroup.mem_subgroupOf] using hm
  calc H.relIndex K = Nat.card (K ⧸ H.subgroupOf K) := rfl
    _ ≤ Nat.card (Fin n) := Nat.card_le_card_of_surjective _ hsurj
    _ = n := by simp

theorem rk_fix_sup (hAe : IsElemAbelian2 A) (haA : a ∈ A)
    (hdisj : Disjoint I (I.map a.toMonoidHom))
    (hcos : ∀ g ∈ A, g ∈ stabSub I ∨ a⁻¹ * g ∈ stabSub I) :
    rk ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) = rk ↥(I ⊓ fixV (A ⊓ stabSub I)) := by
  have hinj : Set.InjOn (fun x : V => x * a x) ((I ⊓ fixV (A ⊓ stabSub I) : Subgroup V) : Set V) :=
    (diag_injOn hdisj).mono (fun x hx => hx.1)
  have h := Nat.card_image_of_injOn hinj
  rw [diag_image_eq hAe haA hdisj hcos] at h
  unfold rk
  exact congrArg (padicValNat 2) h

end SummandSwap

end CFSG.Quasithin
