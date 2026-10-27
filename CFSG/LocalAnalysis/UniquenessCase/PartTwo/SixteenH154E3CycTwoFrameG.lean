module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X]

structure s16h_CycFrameG (q n : ℕ) (Mb : Subgroup (MulAut X)) (ψ z : MulAut X) (U : Subgroup X) :
    Prop where
  exp2 : ∀ x : X, x ^ 2 = 1
  card_u : Nat.card ↥U = 2 ^ n
  sup_top : U ⊔ U.map ψ.toMonoidHom = ⊤
  psi_mem : ψ ∈ Mb
  z_mem : z ∈ Mb
  one_lt : 1 < q
  z_ord : orderOf z = q
  z_fpf : ∀ u ∈ U, z u = u → u = 1
  z_triv : ∀ u ∈ U.map ψ.toMonoidHom, z u = u
  stab : s16h_CycN Mb z ≤ stabSub U
  idx : (s16h_CycN Mb z).relIndex Mb = 2

namespace s16h_CycFrameG

variable {q n : ℕ} {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}

theorem N_le (_F : s16h_CycFrameG q n Mb ψ z U) : s16h_CycN Mb z ≤ Mb := inf_le_left

theorem z_mem_N (F : s16h_CycFrameG q n Mb ψ z U) : z ∈ s16h_CycN Mb z :=
  ⟨F.z_mem, Subgroup.le_normalizer (Subgroup.mem_zpowers z)⟩

theorem N_normal (F : s16h_CycFrameG q n Mb ψ z U) : ((s16h_CycN Mb z).subgroupOf Mb).Normal :=
  Subgroup.normal_of_index_eq_two F.idx

theorem conj_mem (F : s16h_CycFrameG q n Mb ψ z U) {m n : MulAut X} (hm : m ∈ Mb)
    (hn : n ∈ s16h_CycN Mb z) : m * n * m⁻¹ ∈ s16h_CycN Mb z := by
  have h := F.N_normal.conj_mem ⟨n, hn.1⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem conj_inv_mem (F : s16h_CycFrameG q n Mb ψ z U) {m n : MulAut X} (hm : m ∈ Mb)
    (hn : n ∈ s16h_CycN Mb z) : m⁻¹ * n * m ∈ s16h_CycN Mb z := by
  simpa using F.conj_mem (Mb.inv_mem hm) hn

theorem psi_not_mem (F : s16h_CycFrameG q n Mb ψ z U) : ψ ∉ s16h_CycN Mb z := by
  intro hψ
  have hs : ψ ∈ stabSub U := F.stab hψ
  have hmap : U.map ψ.toMonoidHom = U := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (mem_stabSub.1 hs u).2 hu
    · intro hx
      refine ⟨ψ⁻¹ x, ?_, by simp⟩
      exact (mem_stabSub.1 ((stabSub U).inv_mem hs) x).2 hx
  have hz : z = 1 := by
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ U.map ψ.toMonoidHom := by
      rw [hmap]
      have h := F.sup_top
      rw [hmap, sup_idem] at h
      rw [h]
      exact Subgroup.mem_top x
    simpa using F.z_triv x hx
  have h3 := F.z_ord
  rw [hz, orderOf_one] at h3
  have h4 := F.one_lt
  omega

theorem mem_or (F : s16h_CycFrameG q n Mb ψ z U) {g : MulAut X} (hg : g ∈ Mb) :
    g ∈ s16h_CycN Mb z ∨ ψ⁻¹ * g ∈ s16h_CycN Mb z := by
  by_cases hgN : g ∈ s16h_CycN Mb z
  · exact Or.inl hgN
  · right
    obtain ⟨a, haMb, ha⟩ := Subgroup.relIndex_eq_two_iff'.1 F.idx
    have h1 : a * g ∈ s16h_CycN Mb z :=
      (ha g hg).elim (fun h => h.1) (fun h => absurd h.1 hgN)
    have h2 : a * ψ ∈ s16h_CycN Mb z :=
      (ha ψ F.psi_mem).elim (fun h => h.1) (fun h => absurd h.1 F.psi_not_mem)
    have h3 := (s16h_CycN Mb z).mul_mem ((s16h_CycN Mb z).inv_mem h2) h1
    simpa [mul_assoc] using h3

theorem psi_sq_mem (F : s16h_CycFrameG q n Mb ψ z U) : ψ * ψ ∈ s16h_CycN Mb z := by
  rcases F.mem_or (Mb.mul_mem F.psi_mem F.psi_mem) with h | h
  · exact h
  · exact absurd (by simpa using h) F.psi_not_mem

@[expose] noncomputable def rho (F : s16h_CycFrameG q n Mb ψ z U) :
    ↥(s16h_CycN Mb z) →* MulAut ↥U :=
  (resHom U).comp (Subgroup.inclusion F.stab)

theorem rho_apply (F : s16h_CycFrameG q n Mb ψ z U) (n : ↥(s16h_CycN Mb z)) (u : ↥U) :
    ((F.rho n u : ↥U) : X) = (n : MulAut X) (u : X) := rfl

theorem rho_range (F : s16h_CycFrameG q n Mb ψ z U) : F.rho.range = autSub (s16h_CycN Mb z) U := by
  change ((resHom U).comp (Subgroup.inclusion F.stab)).range = _
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem fix_of_rho_eq_one (F : s16h_CycFrameG q n Mb ψ z U) {n : ↥(s16h_CycN Mb z)}
    (h : F.rho n = 1) (u : X) (hu : u ∈ U) : (n : MulAut X) u = u := by
  have := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : X)) h
  exact (F.rho_apply n ⟨u, hu⟩).symm.trans (by simpa using this)

theorem eq_one_of_rho_eq_one (F : s16h_CycFrameG q n Mb ψ z U) {n : MulAut X}
    (hn : n ∈ s16h_CycN Mb z) (h₁ : F.rho ⟨n, hn⟩ = 1)
    (h₂ : F.rho ⟨ψ⁻¹ * n * ψ, F.conj_inv_mem F.psi_mem hn⟩ = 1) : n = 1 := by
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ U ⊔ U.map ψ.toMonoidHom := by rw [F.sup_top]; exact Subgroup.mem_top x
  obtain ⟨u₁, hu₁, y, hy, rfl⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨u₂, hu₂, rfl⟩ := Subgroup.mem_map.1 hy
  have e1 := F.fix_of_rho_eq_one h₁ u₁ hu₁
  have e2 := F.fix_of_rho_eq_one h₂ u₂ hu₂
  simp only [MulAut.mul_apply, MulAut.inv_apply] at e2
  have e3 : n (ψ u₂) = ψ u₂ := by
    have := congrArg ψ e2
    simpa using this
  simp only [MulEquiv.coe_toMonoidHom, map_mul, e1, e3, MulAut.one_apply]

@[expose] noncomputable def core (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U)) :
    Subgroup (MulAut X) where
  carrier := {n | n ∈ s16h_CycN Mb z ∧
    ∀ m ∈ Mb, ∀ h : m⁻¹ * n * m ∈ s16h_CycN Mb z, F.rho ⟨m⁻¹ * n * m, h⟩ ∈ D}
  one_mem' := by
    refine ⟨(s16h_CycN Mb z).one_mem, fun m _ h => ?_⟩
    have e : (⟨m⁻¹ * 1 * m, h⟩ : ↥(s16h_CycN Mb z)) = 1 := Subtype.ext (by simp)
    rw [e, map_one]
    exact D.one_mem
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨(s16h_CycN Mb z).mul_mem haN hbN, fun m hm h => ?_⟩
    have h₁ : m⁻¹ * a * m ∈ s16h_CycN Mb z := F.conj_inv_mem hm haN
    have h₂ : m⁻¹ * b * m ∈ s16h_CycN Mb z := F.conj_inv_mem hm hbN
    have e : (⟨m⁻¹ * (a * b) * m, h⟩ : ↥(s16h_CycN Mb z)) =
        ⟨m⁻¹ * a * m, h₁⟩ * ⟨m⁻¹ * b * m, h₂⟩ :=
      Subtype.ext (by show m⁻¹ * (a * b) * m = (m⁻¹ * a * m) * (m⁻¹ * b * m); group)
    rw [e, map_mul]
    exact D.mul_mem (ha m hm h₁) (hb m hm h₂)
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨(s16h_CycN Mb z).inv_mem haN, fun m hm h => ?_⟩
    have h₁ : m⁻¹ * a * m ∈ s16h_CycN Mb z := F.conj_inv_mem hm haN
    have e : (⟨m⁻¹ * a⁻¹ * m, h⟩ : ↥(s16h_CycN Mb z)) = (⟨m⁻¹ * a * m, h₁⟩)⁻¹ :=
      Subtype.ext (by show m⁻¹ * a⁻¹ * m = (m⁻¹ * a * m)⁻¹; group)
    rw [e, map_inv]
    exact D.inv_mem (ha m hm h₁)

theorem core_le_N (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U)) :
    F.core D ≤ s16h_CycN Mb z := fun _ hn => hn.1

theorem core_le (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U)) : F.core D ≤ Mb :=
  (F.core_le_N D).trans F.N_le

theorem rho_mem_of_mem_core (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U))
    {n : MulAut X} (hn : n ∈ F.core D) : F.rho ⟨n, hn.1⟩ ∈ D := by
  have h : (1 : MulAut X)⁻¹ * n * 1 ∈ s16h_CycN Mb z := by simpa using hn.1
  have := hn.2 1 Mb.one_mem h
  have e : (⟨(1 : MulAut X)⁻¹ * n * 1, h⟩ : ↥(s16h_CycN Mb z)) = ⟨n, hn.1⟩ :=
    Subtype.ext (by simp)
  rwa [e] at this

theorem conj_mem_core (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U))
    {g n : MulAut X} (hg : g ∈ Mb) (hn : n ∈ F.core D) : g * n * g⁻¹ ∈ F.core D := by
  refine ⟨F.conj_mem hg hn.1, fun m hm h => ?_⟩
  have hm' : g⁻¹ * m ∈ Mb := Mb.mul_mem (Mb.inv_mem hg) hm
  have h' : (g⁻¹ * m)⁻¹ * n * (g⁻¹ * m) ∈ s16h_CycN Mb z := F.conj_inv_mem hm' hn.1
  have e : (⟨m⁻¹ * (g * n * g⁻¹) * m, h⟩ : ↥(s16h_CycN Mb z)) =
      ⟨(g⁻¹ * m)⁻¹ * n * (g⁻¹ * m), h'⟩ :=
    Subtype.ext (by show m⁻¹ * (g * n * g⁻¹) * m = (g⁻¹ * m)⁻¹ * n * (g⁻¹ * m); group)
  rw [e]
  exact hn.2 _ hm' h'

theorem core_normalizes (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U)) :
    Mb ≤ Subgroup.normalizer (F.core D : Set (MulAut X)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => F.conj_mem_core D hg hn, fun hn => ?_⟩
  have := F.conj_mem_core D (Mb.inv_mem hg) hn
  simpa [mul_assoc] using this

theorem zp_fix (F : s16h_CycFrameG q n Mb ψ z U) (u : X) (hu : u ∈ U) : (ψ * z * ψ⁻¹) u = u := by
  have hsq : ψ * ψ ∈ stabSub U := F.stab F.psi_sq_mem
  have h1 : (ψ * ψ)⁻¹ u ∈ U := (mem_stabSub.1 ((stabSub U).inv_mem hsq) u).2 hu
  have h3 : ψ⁻¹ u ∈ U.map ψ.toMonoidHom := by
    refine ⟨(ψ * ψ)⁻¹ u, h1, ?_⟩
    simp [mul_inv_rev, MulAut.mul_apply]
  simp only [MulAut.mul_apply]
  rw [F.z_triv _ h3]
  simp

theorem conj_z_fix (F : s16h_CycFrameG q n Mb ψ z U) {n : MulAut X} (hn : n ∈ s16h_CycN Mb z)
    (u : X) (hu : u ∈ U) : ((ψ * n)⁻¹ * z * (ψ * n)) u = u := by
  have hnu : n u ∈ U := (mem_stabSub.1 (F.stab hn) u).2 hu
  have hψ : ψ (n u) ∈ U.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hnu
  have h := F.z_triv _ hψ
  simp only [mul_inv_rev, MulAut.mul_apply]
  rw [h]
  simp

theorem zp_mem_N (F : s16h_CycFrameG q n Mb ψ z U) : ψ * z * ψ⁻¹ ∈ s16h_CycN Mb z :=
  F.conj_mem F.psi_mem F.z_mem_N

theorem rho_conj_z_mem (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U))
    (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D) {g : MulAut X} (hg : g ∈ Mb)
    (h : g⁻¹ * z * g ∈ s16h_CycN Mb z) : F.rho ⟨g⁻¹ * z * g, h⟩ ∈ D := by
  rcases F.mem_or hg with hgN | hψg
  · have hmem : g⁻¹ * z * g ∈ Subgroup.zpowers z := by
      have := Subgroup.mem_normalizer_iff.1 ((s16h_CycN Mb z).inv_mem hgN).2 z
      simpa using this.1 (Subgroup.mem_zpowers z)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have e : (⟨g⁻¹ * z * g, h⟩ : ↥(s16h_CycN Mb z)) =
        (⟨z, F.z_mem_N⟩ : ↥(s16h_CycN Mb z)) ^ k :=
      Subtype.ext (by simpa using hk.symm)
    rw [e, map_zpow]
    exact D.zpow_mem hzD k
  · have e : F.rho ⟨g⁻¹ * z * g, h⟩ = 1 := by
      refine MulEquiv.ext fun u => Subtype.ext ?_
      rw [F.rho_apply]
      simpa using F.conj_z_fix hψg u u.2
    rw [e]
    exact D.one_mem

theorem z_mem_core (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U))
    (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D) : z ∈ F.core D :=
  ⟨F.z_mem_N, fun _ hm h => F.rho_conj_z_mem D hzD hm h⟩

theorem zp_mem_core (F : s16h_CycFrameG q n Mb ψ z U) (D : Subgroup (MulAut ↥U))
    (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D) : ψ * z * ψ⁻¹ ∈ F.core D := by
  refine ⟨F.zp_mem_N, fun m hm h => ?_⟩
  have hg : ψ⁻¹ * m ∈ Mb := Mb.mul_mem (Mb.inv_mem F.psi_mem) hm
  have h' : (ψ⁻¹ * m)⁻¹ * z * (ψ⁻¹ * m) ∈ s16h_CycN Mb z := by
    have e : (ψ⁻¹ * m)⁻¹ * z * (ψ⁻¹ * m) = m⁻¹ * (ψ * z * ψ⁻¹) * m := by group
    rw [e]
    exact h
  have e : (⟨m⁻¹ * (ψ * z * ψ⁻¹) * m, h⟩ : ↥(s16h_CycN Mb z)) =
      ⟨(ψ⁻¹ * m)⁻¹ * z * (ψ⁻¹ * m), h'⟩ :=
    Subtype.ext (by show m⁻¹ * (ψ * z * ψ⁻¹) * m = (ψ⁻¹ * m)⁻¹ * z * (ψ⁻¹ * m); group)
  rw [e]
  exact F.rho_conj_z_mem D hzD hg h'

end s16h_CycFrameG

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
