module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.CatB

theorem centralizer_conj_eq (g x : A8) :
    centralizer ({g * x * g⁻¹} : Set A8) =
      (centralizer ({x} : Set A8)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨g⁻¹ * y * g, ?_, by show g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · rintro ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff] at ha
    show g * a * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
      _ = g * (x * a) * g⁻¹ := by rw [ha]
      _ = g * x * g⁻¹ * (g * a * g⁻¹) := by group

theorem card_centralizer_conj (g x : A8) :
    Nat.card (centralizer ({g * x * g⁻¹} : Set A8)) = Nat.card (centralizer ({x} : Set A8)) := by
  rw [centralizer_conj_eq]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem P0_param {z : A8} (hz : z ∈ a8P0) : ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ z = a8c8 ^ i * a8d8 ^ j := by
  let g : Fin 3 × Fin 3 → A8 := fun a => a8c8 ^ (a.1 : ℕ) * a8d8 ^ (a.2 : ℕ)
  have hg : ∀ a, g a ∈ a8P0 := fun a =>
    mul_mem (pow_mem a8c8_mem_P0 _) (pow_mem a8d8_mem_P0 _)
  have hev : Function.Injective
      (fun a : Fin 3 × Fin 3 => (((a8c ^ (a.1 : ℕ) * a8d ^ (a.2 : ℕ)) 0,
        (a8c ^ (a.1 : ℕ) * a8d ^ (a.2 : ℕ)) 3) : Fin 8 × Fin 8)) := by decide
  have hinj : Function.Injective (fun a => (⟨g a, hg a⟩ : a8P0)) := by
    intro a b hab
    have h1 : g a = g b := congrArg Subtype.val hab
    apply hev
    exact congrArg (fun x : A8 => ((x : Perm (Fin 8)) 0, (x : Perm (Fin 8)) 3)) h1
  have hbij : Function.Bijective (fun a => (⟨g a, hg a⟩ : a8P0)) := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [a8P0_card]
    simp
  obtain ⟨a, ha⟩ := hbij.2 ⟨z, hz⟩
  refine ⟨a.1, a.2, a.1.isLt, a.2.isLt, ?_⟩
  exact (congrArg Subtype.val ha).symm

theorem P0_cases {z : A8} (hz : z ∈ a8P0) :
    z = 1 ∨ z = a8c8 ∨ z = a8c8 ^ 2 ∨ z = a8d8 ∨ z = a8d8 ^ 2 ∨ z = a8c8 * a8d8 ∨
      z = a8c8 * a8d8 ^ 2 ∨ z = a8c8 ^ 2 * a8d8 ∨ z = a8c8 ^ 2 * a8d8 ^ 2 := by
  obtain ⟨i, j, hi, hj, rfl⟩ := P0_param hz
  interval_cases i <;> interval_cases j <;> simp

private def t67 : Perm (Fin 8) := swap 6 7

private theorem sign_t67 : sign t67 = -1 := by
  rw [t67, sign_swap (by decide)]

private theorem card_cent_A8 (x : A8) (hx : (x : Perm (Fin 8)) * t67 = t67 * (x : Perm (Fin 8))) :
    Nat.card (centralizer ({x} : Set A8)) * 2 =
      Nat.card (centralizer ({(x : Perm (Fin 8))} : Set (Perm (Fin 8)))) := by
  have h := a8_card_alt_inf (centralizer ({(x : Perm (Fin 8))} : Set (Perm (Fin 8)))) t67
    (mem_centralizer_singleton_iff.2 hx.symm) sign_t67
  have hmap : (centralizer ({x} : Set A8)).map (alternatingGroup (Fin 8)).subtype =
      centralizer ({(x : Perm (Fin 8))} : Set (Perm (Fin 8))) ⊓ alternatingGroup (Fin 8) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [mem_centralizer_singleton_iff] at ha
      exact ⟨congrArg Subtype.val ha, a.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨y, h2⟩, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext h1
  rw [← h, ← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

private theorem isThreeCycle_a8c : a8c.IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

private theorem isThreeCycle_a8d : a8d.IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

private theorem isThreeCycle_a8d_sq : (a8d ^ 2).IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

private theorem disjoint_cd : a8c.Disjoint a8d := fun x => by revert x; decide

private theorem disjoint_cd_sq : a8c.Disjoint (a8d ^ 2) := fun x => by revert x; decide

theorem card_cent_c : Nat.card (centralizer ({a8c8} : Set A8)) = 180 := by
  have h := card_cent_A8 a8c8 (Equiv.ext (by decide))
  have h3 := a8_cent3 a8c isThreeCycle_a8c.cycleType
  have h4 : (a8c8 : Perm (Fin 8)) = a8c := rfl
  rw [h4] at h
  omega

theorem card_cent_d : Nat.card (centralizer ({a8d8} : Set A8)) = 180 := by
  have h := card_cent_A8 a8d8 (Equiv.ext (by decide))
  have h3 := a8_cent3 a8d isThreeCycle_a8d.cycleType
  have h4 : (a8d8 : Perm (Fin 8)) = a8d := rfl
  rw [h4] at h
  omega

theorem card_cent_cd : Nat.card (centralizer ({a8c8 * a8d8} : Set A8)) = 18 := by
  have h := card_cent_A8 (a8c8 * a8d8) (Equiv.ext (by decide))
  have hct : (a8c * a8d).cycleType = {3, 3} := by
    rw [disjoint_cd.cycleType_mul, isThreeCycle_a8c.cycleType, isThreeCycle_a8d.cycleType]
    rfl
  have h3 := a8_cent33 (a8c * a8d) hct
  have h4 : ((a8c8 * a8d8 : A8) : Perm (Fin 8)) = a8c * a8d := rfl
  rw [h4] at h
  omega

theorem card_cent_cd2 : Nat.card (centralizer ({a8c8 * a8d8 ^ 2} : Set A8)) = 18 := by
  have h := card_cent_A8 (a8c8 * a8d8 ^ 2) (Equiv.ext (by decide))
  have hct : (a8c * a8d ^ 2).cycleType = {3, 3} := by
    rw [disjoint_cd_sq.cycleType_mul, isThreeCycle_a8c.cycleType, isThreeCycle_a8d_sq.cycleType]
    rfl
  have h3 := a8_cent33 (a8c * a8d ^ 2) hct
  have h4 : ((a8c8 * a8d8 ^ 2 : A8) : Perm (Fin 8)) = a8c * a8d ^ 2 := rfl
  rw [h4] at h
  omega

private theorem sq_mem_zpowers {w : A8} (h3 : w ^ 3 = 1) : w ∈ zpowers (w ^ 2) := by
  have : w = (w ^ 2) ^ 2 := by
    rw [← pow_mul]
    calc w = w ^ 3 * w := by rw [h3, one_mul]
      _ = w ^ (2 * 2) := by rw [← pow_succ]
  have h2 : (w ^ 2) ^ 2 ∈ zpowers (w ^ 2) := Subgroup.pow_mem _ (mem_zpowers _) 2
  rwa [← this] at h2

theorem centralizer_sq_eq {x : A8} (h3 : x ^ 3 = 1) :
    centralizer ({x ^ 2} : Set A8) = centralizer ({x} : Set A8) := by
  have hx4 : x = (x ^ 2) ^ 2 := by
    rw [← pow_mul]
    calc x = x ^ 3 * x := by rw [h3, one_mul]
      _ = x ^ (2 * 2) := by rw [← pow_succ]
  ext y
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : Commute y (x ^ 2) := h
    have := (hc.pow_right 2).eq
    rw [← hx4] at this
    exact this
  · intro h
    have hc : Commute y x := h
    exact (hc.pow_right 2).eq

private theorem mem_zpowers_pair {w : A8} (h3 : w ^ 3 = 1) {x y : A8} (hx : x = w ∨ x = w ^ 2)
    (hy : y = w ∨ y = w ^ 2) : y ∈ zpowers x := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact mem_zpowers _
  · exact Subgroup.pow_mem _ (mem_zpowers _) 2
  · exact sq_mem_zpowers h3
  · exact mem_zpowers _

private theorem d_mem_Kb : a8d8 ∈ a8Kb :=
  (mem_a8Kb_iff _).2 ⟨by decide, by decide, by decide⟩

private theorem Dd_mem_Kb {y : A8} (hy : y = a8d8 ∨ y = a8d8 ^ 2) : y ∈ a8Kb := by
  rcases hy with rfl | rfl
  · exact d_mem_Kb
  · exact pow_mem d_mem_Kb 2

private def wPerm : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7

private theorem sign_wPerm : sign wPerm = 1 := by
  rw [wPerm, Perm.sign_mul, Perm.sign_mul, Perm.sign_mul, sign_swap (by decide),
    sign_swap (by decide), sign_swap (by decide), sign_swap (by decide)]
  decide

private def w8 : A8 := toA8 wPerm sign_wPerm

private theorem w8_c : w8 * a8c8 * w8⁻¹ = a8d8 := Subtype.ext (Equiv.ext (by decide))

private theorem w8_d : w8 * a8d8 * w8⁻¹ = a8c8 := Subtype.ext (Equiv.ext (by decide))

open scoped Pointwise in
theorem exists_conj_into_P0 {H : Subgroup A8} (hH : IsPGroup 3 H) :
    ∃ h : A8, ∀ m ∈ H, h * m * h⁻¹ ∈ a8P0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₁, hQ₁⟩ := hH.exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := a8P0_three.exists_le_sylow
  have hQ₂eq : (Q₂ : Subgroup A8) = a8P0 := by
    obtain ⟨n, hn⟩ := Q₂.isPGroup'.exists_card_eq
    have hd : 3 ^ n ∣ 20160 := by
      rw [← a8_card, ← hn]; exact Subgroup.card_subgroup_dvd_card _
    have hn2 := a8_three_part_perm n hd
    have hle : Nat.card (Q₂ : Subgroup A8) ≤ Nat.card a8P0 := by
      rw [a8P0_card, hn]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hn2) (by norm_num)
    exact (Subgroup.eq_of_le_of_card_ge hQ₂ hle).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A8 Q₂ Q₁
  refine ⟨g⁻¹, fun m hm => ?_⟩
  have hset : ((Q₁ : Subgroup A8) : Set A8) = MulAut.conj g • ((Q₂ : Subgroup A8) : Set A8) := by
    rw [← hg]; exact Sylow.coe_smul
  have hmQ : m ∈ ((Q₁ : Subgroup A8) : Set A8) := hQ₁ hm
  rw [hset] at hmQ
  have h := Set.smul_mem_smul_set_iff (a := MulAut.conj g) (s := ((Q₂ : Subgroup A8) : Set A8))
    (x := g⁻¹ * m * g)
  have hconj : MulAut.conj g • (g⁻¹ * m * g) = m := by
    show g * (g⁻¹ * m * g) * g⁻¹ = m
    group
  rw [hconj] at h
  have h2 : g⁻¹ * m * g ∈ ((Q₂ : Subgroup A8) : Set A8) := h.1 hmQ
  rw [hQ₂eq] at h2
  simpa using h2

private theorem zpowers_eq_of {w x : A8} (h3 : w ^ 3 = 1) (hx : x = w ∨ x = w ^ 2) :
    zpowers x = zpowers w := by
  rcases hx with rfl | rfl
  · rfl
  · exact le_antisymm (zpowers_le.2 (Subgroup.pow_mem _ (mem_zpowers _) 2))
      (zpowers_le.2 (sq_mem_zpowers h3))

private theorem centralizer_eq_of {w x : A8} (h3 : w ^ 3 = 1) (hx : x = w ∨ x = w ^ 2) :
    centralizer ({x} : Set A8) = centralizer ({w} : Set A8) := by
  rcases hx with rfl | rfl
  · rfl
  · exact centralizer_sq_eq h3

theorem exists_H_of_conj {x y g : A8} (hx : g * x * g⁻¹ = a8c8 ∨ g * x * g⁻¹ = a8c8 ^ 2)
    (hy : g * y * g⁻¹ ∈ a8Kb) :
    ∃ H : Subgroup A8, Nonempty (H ≃* alternatingGroup (Fin 5)) ∧ y ∈ H ∧
      H ≤ centralizer ({x} : Set A8) ∧ zpowers x ⊔ H = centralizer ({x} : Set A8) ∧
      zpowers x ⊓ H = ⊥ := by
  have hφinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hφapp : ∀ a, (MulAut.conj g⁻¹).toMonoidHom a = g⁻¹ * a * g := fun a => by
    simp [MulAut.conj_apply]
  have hxx : (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹) = x := by rw [hφapp]; group
  have hz : zpowers (g * x * g⁻¹) = zpowers a8c8 := zpowers_eq_of a8c8_cube hx
  have hcx : centralizer ({g * x * g⁻¹} : Set A8) = centralizer ({a8c8} : Set A8) :=
    centralizer_eq_of a8c8_cube hx
  have hC : centralizer ({x} : Set A8) =
      (centralizer ({g * x * g⁻¹} : Set A8)).map (MulAut.conj g⁻¹).toMonoidHom := by
    have h := centralizer_conj_eq g⁻¹ (g * x * g⁻¹)
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h
  have hzx : zpowers x = (zpowers a8c8).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hz, MonoidHom.map_zpowers, hxx]
  refine ⟨a8Kb.map (MulAut.conj g⁻¹).toMonoidHom, ⟨?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective a8Kb _ hφinj).symm.trans a8KbEquiv.symm
  · refine Subgroup.mem_map.2 ⟨g * y * g⁻¹, hy, ?_⟩
    rw [hφapp]; group
  · rw [hC, hcx, a8_centralizer, Subgroup.map_sup]
    exact le_sup_left
  · rw [hC, hcx, a8_centralizer, Subgroup.map_sup, hzx, sup_comm]
  · rw [hzx, ← Subgroup.map_inf _ _ _ hφinj, inf_comm, a8Kb_inf_zpowers, Subgroup.map_bot]

private theorem Cc_card {z : A8} (h : z = a8c8 ∨ z = a8c8 ^ 2) :
    Nat.card (centralizer ({z} : Set A8)) = 180 := by
  rw [centralizer_eq_of a8c8_cube h]; exact card_cent_c

private theorem Dd_card {z : A8} (h : z = a8d8 ∨ z = a8d8 ^ 2) :
    Nat.card (centralizer ({z} : Set A8)) = 180 := by
  rw [centralizer_eq_of a8d8_cube h]; exact card_cent_d

private theorem cd2_cube : (a8c8 * a8d8 ^ 2) ^ 3 = 1 := Subtype.ext (Equiv.ext (by decide))

private theorem cd_cube : (a8c8 * a8d8) ^ 3 = 1 := Subtype.ext (Equiv.ext (by decide))

private theorem c2d_eq : a8c8 ^ 2 * a8d8 = (a8c8 * a8d8 ^ 2) ^ 2 :=
  Subtype.ext (Equiv.ext (by decide))

private theorem c2d2_eq : a8c8 ^ 2 * a8d8 ^ 2 = (a8c8 * a8d8) ^ 2 :=
  Subtype.ext (Equiv.ext (by decide))

private theorem Mm_card {z : A8}
    (h : z = a8c8 * a8d8 ∨ z = a8c8 * a8d8 ^ 2 ∨ z = a8c8 ^ 2 * a8d8 ∨ z = a8c8 ^ 2 * a8d8 ^ 2) :
    Nat.card (centralizer ({z} : Set A8)) = 18 := by
  rcases h with rfl | rfl | rfl | rfl
  · exact card_cent_cd
  · exact card_cent_cd2
  · rw [c2d_eq, centralizer_sq_eq cd2_cube]; exact card_cent_cd2
  · rw [c2d2_eq, centralizer_sq_eq cd_cube]; exact card_cent_cd

private theorem conj_c_mem {z : A8} (hz : z = a8c8 ∨ z = a8c8 ^ 2) :
    w8 * z * w8⁻¹ = a8d8 ∨ w8 * z * w8⁻¹ = a8d8 ^ 2 := by
  rcases hz with rfl | rfl
  · exact Or.inl w8_c
  · exact Or.inr (by rw [← w8_c, conj_pow])

private theorem conj_d_mem {z : A8} (hz : z = a8d8 ∨ z = a8d8 ^ 2) :
    w8 * z * w8⁻¹ = a8c8 ∨ w8 * z * w8⁻¹ = a8c8 ^ 2 := by
  rcases hz with rfl | rfl
  · exact Or.inl w8_d
  · exact Or.inr (by rw [← w8_d, conj_pow])

private theorem P0_cls {z : A8} (hz : z ∈ a8P0) :
    z = 1 ∨ (z = a8c8 ∨ z = a8c8 ^ 2) ∨ (z = a8d8 ∨ z = a8d8 ^ 2) ∨
      (z = a8c8 * a8d8 ∨ z = a8c8 * a8d8 ^ 2 ∨ z = a8c8 ^ 2 * a8d8 ∨ z = a8c8 ^ 2 * a8d8 ^ 2) := by
  rcases P0_cases hz with h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem a8_pair {x y : A8} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hc : x * y = y * x)
    (hx1 : x ≠ 1) (hyx : y ∉ zpowers x)
    (hcard : Nat.card (centralizer ({x} : Set A8)) = Nat.card (centralizer ({y} : Set A8))) :
    Nat.card (centralizer ({x} : Set A8)) = 18 ∨
      ∃ H : Subgroup A8, Nonempty (H ≃* alternatingGroup (Fin 5)) ∧ y ∈ H ∧
        H ≤ centralizer ({x} : Set A8) ∧ zpowers x ⊔ H = centralizer ({x} : Set A8) ∧
        zpowers x ⊓ H = ⊥ := by
  have hP : IsPGroup 3 (closure ({x, y} : Set A8)) := by
    refine isPGroup_closure_three _ ?_ ?_
    · intro s hs
      rcases hs with h | h
      · rw [h]; exact hx3
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hy3
    · intro s hs u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hu
      rcases hs with h | h <;> rcases hu with h' | h' <;> rw [h, h'] <;>
        first | rfl | exact hc | exact hc.symm
  obtain ⟨h, hh⟩ := exists_conj_into_P0 hP
  have hxP : h * x * h⁻¹ ∈ a8P0 := hh x (subset_closure (by simp))
  have hyP : h * y * h⁻¹ ∈ a8P0 := hh y (subset_closure (by simp))
  have hx1' : h * x * h⁻¹ ≠ 1 := fun e => hx1 (by
    have e' : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [e'] at *; simp [e])
  have hyx' : h * y * h⁻¹ ∉ zpowers (h * x * h⁻¹) := by
    intro hm
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hm
    apply hyx
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [conj_zpow] at hn
    exact mul_left_cancel (mul_right_cancel hn)
  have hcard' : Nat.card (centralizer ({h * x * h⁻¹} : Set A8)) =
      Nat.card (centralizer ({h * y * h⁻¹} : Set A8)) := by
    rw [card_centralizer_conj, card_centralizer_conj]; exact hcard
  have hcx : Nat.card (centralizer ({x} : Set A8)) =
      Nat.card (centralizer ({h * x * h⁻¹} : Set A8)) := (card_centralizer_conj h x).symm
  have hone : h * y * h⁻¹ = 1 → False := fun h1 => hyx' (by rw [h1]; exact one_mem _)
  rcases P0_cls hxP with h1 | hC | hD | hM
  · exact absurd h1 hx1'
  · have hxc := Cc_card hC
    rcases P0_cls hyP with h1 | hC' | hD' | hM'
    · exact absurd h1 hone
    · exact absurd (mem_zpowers_pair a8c8_cube hC hC') hyx'
    · exact Or.inr (exists_H_of_conj hC (Dd_mem_Kb hD'))
    · have := Mm_card hM'
      exfalso; omega
  · have hxd := Dd_card hD
    rcases P0_cls hyP with h1 | hC' | hD' | hM'
    · exact absurd h1 hone
    · have e : (w8 * h) * x * (w8 * h)⁻¹ = w8 * (h * x * h⁻¹) * w8⁻¹ := by group
      have e' : (w8 * h) * y * (w8 * h)⁻¹ = w8 * (h * y * h⁻¹) * w8⁻¹ := by group
      refine Or.inr (exists_H_of_conj (g := w8 * h) ?_ ?_)
      · rw [e]; exact conj_d_mem hD
      · rw [e']; exact Dd_mem_Kb (conj_c_mem hC')
    · exact absurd (mem_zpowers_pair a8d8_cube hD hD') hyx'
    · have := Mm_card hM'
      exfalso; omega
  · have hxm := Mm_card hM
    rcases P0_cls hyP with h1 | hC' | hD' | hM'
    · exact absurd h1 hone
    · have := Cc_card hC'
      exfalso; omega
    · have := Dd_card hD'
      exfalso; omega
    · exact Or.inl (by omega)

end CFSG.RankThree.PartTwo.Sec21.FF84
