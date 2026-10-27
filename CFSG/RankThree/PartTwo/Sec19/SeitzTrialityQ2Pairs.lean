module

public import Certificates.Data.HuppertD4Q2.Checker

public section

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.AGLEmbedding.ChevOuter HuppertD4Q2

namespace CFSG.RankThree.PartTwo.Sec19.TrialityTwo

instance instFiniteMulAutLineGroup : Finite (MulAut lineGroup) :=
  Finite.of_injective (fun f : MulAut lineGroup => (f : lineGroup → lineGroup)) DFunLike.coe_injective

section Pairs

theorem phiT_sq_ne_conj (x : lineGroup) : phiT ^ 2 ≠ MulAut.conj x := by
  intro h
  apply phiT_ne_conj (x ^ 2)
  have h4 : phiT = phiT ^ 4 := by
    rw [show 4 = 1 + 3 by norm_num, pow_add, phiT_pow_three, mul_one, pow_one]
  rw [h4, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h, ← map_pow]

theorem exp_eq_of_conj_eq {a b : ℕ} (ha : a < 3) (hb : b < 3) {x : lineGroup}
    (h : phiT ^ a = MulAut.conj x * phiT ^ b) : a = b := by
  have h3 : phiT * phiT * phiT = 1 := by
    have := phiT_pow_three
    simpa [pow_succ, mul_assoc] using this
  interval_cases a <;> interval_cases b <;> first | rfl | skip
  ·
    exfalso
    apply phiT_ne_conj x⁻¹
    rw [map_inv]
    simp only [pow_zero, pow_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  ·
    exfalso
    apply phiT_sq_ne_conj x⁻¹
    rw [map_inv]
    simp only [pow_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  ·
    exfalso
    apply phiT_ne_conj x
    simpa using h
  ·
    exfalso
    apply phiT_sq_ne_conj x
    calc phiT ^ 2 = phiT * phiT := pow_two _
      _ = (MulAut.conj x * phiT ^ 2) * phiT := by simpa using congrArg (· * phiT) h
      _ = MulAut.conj x * (phiT * phiT * phiT) := by simp [pow_two, mul_assoc]
      _ = MulAut.conj x := by rw [h3, mul_one]
  ·
    exfalso
    apply phiT_sq_ne_conj x
    simpa using h
  ·
    exfalso
    apply phiT_ne_conj x
    calc phiT = phiT ^ 4 := by
          rw [show 4 = 1 + 3 by norm_num, pow_add, phiT_pow_three, mul_one, pow_one]
      _ = phiT ^ 2 * phiT ^ 2 := by rw [← pow_add]
      _ = (MulAut.conj x * phiT ^ 1) * phiT ^ 2 := by rw [← h]
      _ = MulAut.conj x * (phiT * phiT * phiT) := by simp [pow_two, mul_assoc]
      _ = MulAut.conj x := by rw [h3, mul_one]

theorem conj_injective_of_center (h : Subgroup.center lineGroup = ⊥) :
    Function.Injective (MulAut.conj : lineGroup →* MulAut lineGroup) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hmem : c ∈ Subgroup.center lineGroup := by
    rw [Subgroup.mem_center_iff]
    intro n
    have h1 := DFunLike.congr_fun hc n
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rwa [h, Subgroup.mem_bot] at hmem

theorem rep_inj (hZ : Subgroup.center lineGroup = ⊥) {p q : Pr} {α : MulAut lineGroup}
    (hp : Rep p α) (hq : Rep q α) : p = q := by
  obtain ⟨hps, hpj, g, hg, hα⟩ := hp
  obtain ⟨hqs, hqj, h, hh, hα'⟩ := hq
  have key : MulAut.conj g * phiT ^ p.2 = MulAut.conj h * phiT ^ q.2 := hα.symm.trans hα'
  have key2 : phiT ^ p.2 = MulAut.conj (g⁻¹ * h) * phiT ^ q.2 := by
    calc phiT ^ p.2 = (MulAut.conj g)⁻¹ * (MulAut.conj g * phiT ^ p.2) := by group
      _ = (MulAut.conj g)⁻¹ * (MulAut.conj h * phiT ^ q.2) := by rw [key]
      _ = MulAut.conj (g⁻¹ * h) * phiT ^ q.2 := by rw [map_mul, map_inv]; group
  have hj : p.2 = q.2 := exp_eq_of_conj_eq hpj hqj key2
  rw [hj] at key
  have hgh : MulAut.conj g = MulAut.conj h := mul_right_cancel key
  have hgh' : g = h := conj_injective_of_center hZ hgh
  exact Prod.ext (CFSG.AGLEmbedding.D4Two.eq_of_toMat_eq hps hqs (by rw [hg, hh, hgh'])) hj

theorem rep_eq_oneP_iff (hZ : Subgroup.center lineGroup = ⊥) {p : Pr} {α : MulAut lineGroup}
    (hp : Rep p α) : p = oneP ↔ α = 1 :=
  ⟨fun h => rep_ext hp rep_oneP h, fun h => rep_one hZ (h ▸ hp)⟩

theorem rep_inv_eq {p q : Pr} {α β : MulAut lineGroup} (hp : Rep p α) (hq : Rep q β)
    (h : mulP p q = oneP) : β = α⁻¹ :=
  eq_inv_of_mul_eq_one_right (rep_ext (rep_mul hp hq) rep_oneP h)

theorem rep_cube1P (hZ : Subgroup.center lineGroup = ⊥) {p : Pr} {α : MulAut lineGroup}
    (hp : Rep p α) : cube1P p = true ↔ α ^ 3 = 1 := by
  have hr := rep_mul hp (rep_mul hp hp)
  rw [cube1P, beq_iff_eq]
  constructor
  · intro h
    rw [pow_three]
    exact rep_ext hr rep_oneP h
  · intro h
    rw [pow_three] at h
    rw [h] at hr
    exact rep_inj hZ hr rep_oneP

theorem rep_commP (hZ : Subgroup.center lineGroup = ⊥) {p q : Pr} {α β : MulAut lineGroup}
    (hp : Rep p α) (hq : Rep q β) : commP p q = true ↔ α * β = β * α := by
  rw [commP, beq_iff_eq]
  constructor
  · intro h
    exact rep_ext (rep_mul hp hq) (rep_mul hq hp) h
  · intro h
    have hr := rep_mul hq hp
    rw [← h] at hr
    exact rep_inj hZ (rep_mul hp hq) hr

theorem rep_mem_powsP (hZ : Subgroup.center lineGroup = ⊥) {p q : Pr} {α β : MulAut lineGroup}
    (hp : Rep p α) (hq : Rep q β) :
    q ∈ powsP p ↔ β ∈ ({1, α, α * α} : Set (MulAut lineGroup)) := by
  simp only [powsP, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (rep_ext hq rep_oneP h)
    · exact Or.inr (Or.inl (rep_ext hq hp h))
    · exact Or.inr (Or.inr (rep_ext hq (rep_mul hp hp) h))
  · rintro (h | h | h)
    · exact Or.inl (rep_inj hZ hq (h ▸ rep_oneP))
    · exact Or.inr (Or.inl (rep_inj hZ hq (h ▸ hp)))
    · exact Or.inr (Or.inr (rep_inj hZ hq (h ▸ rep_mul hp hp)))

theorem rep_isPairP (hZ : Subgroup.center lineGroup = ⊥) {p q : Pr} {α β : MulAut lineGroup}
    (hp : Rep p α) (hq : Rep q β) :
    isPairP p q = true ↔ (α ≠ 1 ∧ α ^ 3 = 1 ∧ β ^ 3 = 1 ∧ α * β = β * α ∧
      β ∉ ({1, α, α * α} : Set (MulAut lineGroup))) := by
  have h1 := rep_eq_oneP_iff hZ hp
  have h2 := rep_cube1P hZ hp
  have h3 := rep_cube1P hZ hq
  have h4 := rep_commP hZ hp hq
  have h5 := rep_mem_powsP hZ hp hq
  simp only [isPairP, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  have h6 : (powsP p).contains q = false ↔ q ∉ powsP p := by
    rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
  rw [h6]
  constructor
  · rintro ⟨⟨⟨⟨hne, hc1⟩, hc2⟩, hcm⟩, hmem⟩
    exact ⟨fun h => hne (h1.mpr h), h2.mp hc1, h3.mp hc2, h4.mp hcm, fun hb => hmem (h5.mpr hb)⟩
  · rintro ⟨hne, hc1, hc2, hcm, hmem⟩
    exact ⟨⟨⟨⟨fun h => hne (h1.mp h), h2.mpr hc1⟩, h3.mpr hc2⟩, h4.mpr hcm⟩,
      fun hq' => hmem (h5.mp hq')⟩

theorem rep_powsP_elt {p : Pr} {α : MulAut lineGroup} (hp : Rep p α) :
    ∀ z ∈ powsP p, ∃ i : ℕ, i < 3 ∧ Rep z (α ^ i) := by
  intro z hz
  simp only [powsP, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨0, by norm_num, by simpa using rep_oneP⟩
  · exact ⟨1, by norm_num, by simpa using hp⟩
  · exact ⟨2, by norm_num, by simpa [pow_two] using rep_mul hp hp⟩

theorem exists_mem_powsP {p : Pr} {α : MulAut lineGroup}
    (hp : Rep p α) {i : ℕ} (hi : i < 3) : ∃ z ∈ powsP p, Rep z (α ^ i) := by
  interval_cases i
  · exact ⟨oneP, by simp [powsP], by simpa using rep_oneP⟩
  · exact ⟨p, by simp [powsP], by simpa using hp⟩
  · exact ⟨mulP p p, by simp [powsP], by simpa [pow_two] using rep_mul hp hp⟩

theorem rep_mem_planeP (hZ : Subgroup.center lineGroup = ⊥) {u v z : Pr}
    {a b c : MulAut lineGroup} (hu : Rep u a) (hv : Rep v b) (hz : Rep z c) :
    z ∈ planeP u v ↔ ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ c = a ^ i * b ^ j := by
  unfold planeP
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨i, hi, hxi⟩ := rep_powsP_elt hu x hx
    obtain ⟨j, hj, hyj⟩ := rep_powsP_elt hv y hy
    exact ⟨i, j, hi, hj, rep_ext hz (rep_mul hxi hyj) rfl⟩
  · rintro ⟨i, j, hi, hj, hc⟩
    obtain ⟨x, hx, hxi⟩ := exists_mem_powsP hu hi
    obtain ⟨y, hy, hyj⟩ := exists_mem_powsP hv hj
    refine ⟨x, hx, y, hy, ?_⟩
    have hr := rep_mul hxi hyj
    rw [← hc] at hr
    exact (rep_inj hZ hz hr).symm

end Pairs

section Lines

@[expose] noncomputable def repLine1 (i : ℕ) : MulAut lineGroup := wordAut (classR1.getD i [])

@[expose] noncomputable def repLine2 (i : ℕ) : MulAut lineGroup := wordAut (classR2.getD i [])

end Lines

end CFSG.RankThree.PartTwo.Sec19.TrialityTwo
