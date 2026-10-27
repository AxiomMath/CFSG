module

public import CFSG.Quasithin.Background.F7TwoInvAltInvol
public import CFSG.Quasithin.Background.F7TwoInvAutWrap

public section

namespace CFSG.Quasithin.F7Two

variable {G : Type*} [Group G]

theorem conjSub_le_of_mem {K X : Subgroup G} {n : G} (hn : n ∈ K) (hX : X ≤ K) :
    X.map (MulAut.conj n).toMonoidHom ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  exact K.mul_mem (K.mul_mem hn (hX hx)) (K.inv_mem hn)

theorem conjSub_mul (a b : G) (H : Subgroup G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b * y * b⁻¹, ⟨y, hy, rfl⟩, by group⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩

theorem conjSub_inv_of_eq {H H' : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H') : H'.map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [← h, Subgroup.map_map]
  have e : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  rw [e, Subgroup.map_id]

theorem conj_mem_invXi_of_le {Γ R : Subgroup G} (hRΓ : R ≤ Γ) {g u x : G} (hg : g ∈ Γ)
    (hx : x ∈ invXi R u) : g * x * g⁻¹ ∈ invXi Γ (g * u * g⁻¹) := by
  refine ⟨Γ.mul_mem (Γ.mul_mem hg (hRΓ hx.1)) (Γ.inv_mem hg), fun hP => hx.2 ?_⟩
  have e : g * u * g⁻¹ * (g * x * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ =
      (MulAut.conj g).toMonoidHom (u * x * u⁻¹ * x⁻¹) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e, isPGroup_zpowers_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at hP
  exact hP

theorem map_closure_invXi_le {Γ R : Subgroup G} (hRΓ : R ≤ Γ) {g : G} (u : G) (hg : g ∈ Γ) :
    (Subgroup.closure (invXi R u)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (invXi Γ (g * u * g⁻¹)) := by
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact conj_mem_invXi_of_le hRΓ hg hx

theorem le_closure_invXi_of_invAutGen {R : Subgroup G} {u : G} (hu : u ∈ R)
    (h : InvAutGen ↥R (MulAut.conj (⟨u, hu⟩ : ↥R))) : R ≤ Subgroup.closure (invXi R u) :=
  ((invGen_iff_invAutGen (L := R) (a := u) (φ := MulAut.conj (⟨u, hu⟩ : ↥R))
    (fun _ => rfl)).2 h).ge

theorem le_closure_invXi_of_forall_invAutGen {R : Subgroup G}
    (hR : ∀ φ : MulAut ↥R, φ * φ = 1 → φ ≠ 1 → InvAutGen ↥R φ) (hs : IsSimpleGroup ↥R)
    (hnab : ∃ x y : ↥R, x * y ≠ y * x) {u : G} (hu : u ∈ R) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    R ≤ Subgroup.closure (invXi R u) := by
  refine le_closure_invXi_of_invAutGen hu (hR _ ?_ ?_)
  · have h : (⟨u, hu⟩ : ↥R) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
    rw [← map_mul, h, map_one]
  · intro h1
    have hz : (⟨u, hu⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut ↥R => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * ⟨u, hu⟩ = ⟨u, hu⟩ * g * ⟨u, hu⟩⁻¹ * ⟨u, hu⟩ := by rw [h2]
        _ = ⟨u, hu⟩ * g := by group
    rw [center_eq_bot_of_isSimpleGroup hs hnab, Subgroup.mem_bot] at hz
    exact hu1 (congrArg Subtype.val hz)

theorem nonempty_invXi_of_le_closure {Γ R : Subgroup G} {u : G}
    (h : R ≤ Subgroup.closure (invXi Γ u)) (hR : R ≠ ⊥) : (invXi Γ u).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, Subgroup.closure_empty] at h
  exact hR (le_bot_iff.1 h)

theorem invAutGen_conj_of_le_closure {Γ : Subgroup G} {u : G} (hu : u ∈ Γ)
    (h : Γ ≤ Subgroup.closure (invXi Γ u)) : InvAutGen ↥Γ (MulAut.conj (⟨u, hu⟩ : ↥Γ)) :=
  (invGen_iff_invAutGen (L := Γ) (a := u) (φ := MulAut.conj (⟨u, hu⟩ : ↥Γ)) (fun _ => rfl)).1
    (le_antisymm closure_invXi_le h)

end CFSG.Quasithin.F7Two
