module

public import CFSG.Quasithin.Background.Harris.R1.J2VertSplit
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.QuasithinUnique

theorem isSylowTwoOf_of_card {K A : Subgroup (Equiv.Perm (Fin 64))} (hK : Nat.card K = 3840)
    (hA : Nat.card A = 256) (hAK : A ≤ K) : IsSylowTwoOf A K := by
  refine ⟨hAK, IsPGroup.of_card (n := 8) (by rw [hA]; norm_num), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := A) (K := K)
  rw [inf_of_le_left hAK, hA, hK] at h
  have h15 : A.relIndex K = 15 := by omega
  have h15' : (A.subgroupOf K).index = 15 := h15
  rw [h15']
  decide

theorem split_root_counts
    {H : Type} [Group H] [Finite H] (j : H →* Equiv.Perm (Fin 64)) (hj : Function.Injective j)
    (hrange : j.range = sHom.range) (S Q : Subgroup H) [Q.Normal] (hS : Nat.card S = 256)
    (hQ : Q.map j = Qs) {z v : H} (hz : ∀ h : H, h * z = z * h) (hjz : j z = zs)
    (hvQ : v ∈ Q) (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvz : v ≠ z)
    (hSv : ∀ s ∈ S, s * v * s⁻¹ = v ∨ s * v * s⁻¹ = z * v) :
    Nat.card {y : S // (y : H) * v = v * y ∧ (y : H) * y = z} = 28 ∧
    Nat.card {y : S // (y : H) * v = v * y ∧ (y : H) * y = v} = 12 := by
  classical
  have hKcard : Nat.card sHom.range = 3840 := card_range_sHom
  have hP : Nat.card (S.map j) = 256 := by
    rw [Subgroup.card_map_of_injective hj, hS]
  have hPK : S.map j ≤ sHom.range := by
    rw [← hrange]; exact Subgroup.map_le_range j S
  obtain ⟨c, hcK, hc⟩ := CFSG.Quasithin.A4.exists_conj_of_isSylowTwoOf
    (isSylowTwoOf_of_card hKcard hP hPK) (isSylowTwoOf_of_card hKcard card_Ts Ts_le)
  have hcj : c ∈ j.range := by rw [hrange]; exact hcK
  obtain ⟨h₀, rfl⟩ := hcj
  have hTs : ∀ x, x ∈ Ts ↔ ∃ s ∈ S, x = j h₀ * j s * (j h₀)⁻¹ := by
    intro x
    rw [hc, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, e⟩
      refine ⟨s, hs, ?_⟩
      rw [e]; group
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by group⟩
  set cj : Equiv.Perm (Fin 64) ≃* Equiv.Perm (Fin 64) := MulAut.conj (j h₀) with hcjdef
  have hcjapp : ∀ a, cj a = j h₀ * a * (j h₀)⁻¹ := fun a => MulAut.conj_apply _ _
  have e : ∀ a b : H, cj (j a) * cj (j b) = cj (j (a * b)) := fun a b => by simp only [map_mul]
  have hg : j h₀ * zs = zs * j h₀ := by rw [← hjz, ← map_mul, ← map_mul, hz]
  have hcz : cj (j z) = zs := by
    rw [hjz, hcjapp, hg, mul_inv_cancel_right]
  have hzy : ∀ y : Ts, (y : Equiv.Perm (Fin 64)) * zs = zs * y := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ := (hTs y).1 hy
    show cj (j s) * zs = zs * cj (j s)
    rw [← hcz, e, e, hz s]
  let f : S → Ts := fun s => ⟨cj (j s), (hTs _).2 ⟨s, s.2, (hcjapp _)⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : cj (j a) = cj (j b) := congrArg Subtype.val hab
      exact Subtype.ext (hj (cj.injective h1))
    · rintro ⟨x, hx⟩
      obtain ⟨s, hs, rfl⟩ := (hTs x).1 hx
      exact ⟨⟨s, hs⟩, Subtype.ext (hcjapp _).symm⟩
  have key : ∀ w : H, Nat.card {y : S // (y : H) * v = v * y ∧ (y : H) * y = w} =
      Nat.card {y : Ts // (y : Equiv.Perm (Fin 64)) * cj (j v) = cj (j v) * y ∧
        (y : Equiv.Perm (Fin 64)) * y = cj (j w)} := by
    intro w
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective f hf) ?_)
    intro y
    change _ ↔ cj (j y) * cj (j v) = cj (j v) * cj (j y) ∧ cj (j y) * cj (j y) = cj (j w)
    rw [e, e, e]
    simp only [EmbeddingLike.apply_eq_iff_eq, hj.eq_iff]
  have hu : cj (j v) = j (h₀ * v * h₀⁻¹) := by
    rw [hcjapp]; simp
  have hv'Q : h₀ * v * h₀⁻¹ ∈ Q := Subgroup.Normal.conj_mem inferInstance v hvQ h₀
  have huQs : cj (j v) ∈ Qs := by
    rw [hu, ← hQ]; exact Subgroup.mem_map_of_mem j hv'Q
  have hu2 : cj (j v) * cj (j v) = 1 := by
    rw [e, hv2]; simp
  have hu1 : cj (j v) ≠ 1 := by
    intro h
    apply hv1
    apply hj
    simpa using h
  have hu3 : cj (j v) ≠ zs := by
    intro h
    apply hvz
    apply hj
    exact cj.injective (h.trans hcz.symm)
  have hn : ∀ g ∈ Ts, g * cj (j v) * g⁻¹ = cj (j v) ∨ g * cj (j v) * g⁻¹ = zs * cj (j v) := by
    intro g hg'
    obtain ⟨s, hs, rfl⟩ := (hTs g).1 hg'
    have h1 : cj (j s) * cj (j v) * (cj (j s))⁻¹ = cj (j (s * v * s⁻¹)) := by
      simp only [map_mul, map_inv]
    have h2 : j h₀ * j s * (j h₀)⁻¹ = cj (j s) := (hcjapp _).symm
    rw [h2, h1]
    rcases hSv s hs with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, ← e z v, hcz])
  have hcomm : ∀ y : Ts, ((y : Equiv.Perm (Fin 64)) * (zs * x1s) = (zs * x1s) * y ↔
      (y : Equiv.Perm (Fin 64)) * x1s = x1s * y) := by
    intro y
    rw [← mul_assoc, hzy y, mul_assoc, mul_assoc, mul_right_inj]
  have h1 : ∀ w, Nat.card {y : Ts // (y : Equiv.Perm (Fin 64)) * (zs * x1s) = (zs * x1s) * y ∧
        (y : Equiv.Perm (Fin 64)) * y = w} =
      Nat.card {y : Ts // (y : Equiv.Perm (Fin 64)) * x1s = x1s * y ∧
        (y : Equiv.Perm (Fin 64)) * y = w} := fun w =>
    Nat.card_congr (Equiv.subtypeEquivRight fun y => and_congr_left' (hcomm y))
  rcases normalLine_Ts _ huQs hu2 hu1 hu3 hn with hx | hx
  · rw [key z, key v, hcz, hx]
    exact ⟨card_root_z_Ts, card_root_x_Ts⟩
  · rw [key z, key v, hcz, hx, h1 zs, h1 (zs * x1s)]
    exact ⟨card_root_z_Ts, card_root_zx_Ts⟩

end CFSG.Quasithin.Background.Harris.R1.J2Vert
